#!/usr/bin/env python3
"""Referee script (written from scratch, independent of lowrank_*/ext_*/proof_* scripts).

Checks, in exact integer arithmetic:
  (1)  n * #HC(G) = sum over 2-factors X of tau(X)
  (2)  tau(X) = det reduced Laplacian = Berezin integral of prod_{e in X} (1 + B_e),
       B_e = (pb_i - pb_j)(p_i - p_j), root generators set to 0
  (3)  blob decomposition: sum over crossing-edge labels of prod_a T_a(labels at a)
       * (-1)^{sum over interleaving disjoint bundle pairs N_ab N_cd}
  (4)  the same as a literal network (Definition 2 of the paper): node settings = own copies
       of incident bundle labels + parity-copy bits, W_a = T_a * (-1)^{P_ab * copy},
       Psi_{a,c} = equality tests.  Copy bits are genuinely summed over.
Two crossing-edge alphabets are tested: 6 states (unused, used/1, 4 bilinear terms) and the
5-state variant (unused, used/(1+loc_i)(1+loc_j), used/-loc_i loc_j, two cross terms).

Generators: (v, 0) = psibar_v, (v, 1) = psi_v.  Integral := coefficient of prod_{v != r} psibar_v psi_v.

Usage: python3 review_exact_count.py [seed] [trials]
"""
import itertools, math, random, sys

# ------------------------------------------------------------------ basic graph functions
def hc_count(n, edges):
    adj = [[] for _ in range(n)]
    for i, j in edges:
        adj[i].append(j); adj[j].append(i)
    cnt = 0
    def dfs(v, seen, d):
        nonlocal cnt
        if d == n:
            cnt += 0 in adj[v]
            return
        for w in adj[v]:
            if not (seen >> w) & 1:
                dfs(w, seen | (1 << w), d + 1)
    dfs(0, 1, 1)
    assert cnt % 2 == 0
    return cnt // 2

def two_factors(n, edges):
    m = len(edges); out = []; deg = [0] * n
    # remaining edge count per vertex for pruning
    rem = [0] * n
    for i, j in edges:
        rem[i] += 1; rem[j] += 1
    def rec(k, ch):
        if k == m:
            if all(d == 2 for d in deg):
                out.append(tuple(ch))
            return
        i, j = edges[k]
        rem[i] -= 1; rem[j] -= 1
        if deg[i] + rem[i] >= 2 and deg[j] + rem[j] >= 2:
            rec(k + 1, ch)
        if deg[i] < 2 and deg[j] < 2:
            deg[i] += 1; deg[j] += 1; ch.append(k)
            rec(k + 1, ch)
            ch.pop(); deg[i] -= 1; deg[j] -= 1
        rem[i] += 1; rem[j] += 1
    rec(0, [])
    return out

def det(M):
    M = [r[:] for r in M]; N = len(M)
    if N == 0:
        return 1
    s, prev = 1, 1
    for k in range(N - 1):
        if M[k][k] == 0:
            for r in range(k + 1, N):
                if M[r][k]:
                    M[k], M[r] = M[r], M[k]; s = -s; break
            else:
                return 0
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return s * M[N - 1][N - 1]

def tau(n, edges, X, r, u=None):
    L = [[0] * n for _ in range(n)]
    for k in X:
        i, j = edges[k]; x = u[k] if u else 1
        L[i][i] += x; L[j][j] += x; L[i][j] -= x; L[j][i] -= x
    idx = [v for v in range(n) if v != r]
    return det([[L[a][b] for b in idx] for a in idx])

def inv_parity(seq):
    p = 0
    for a in range(len(seq)):
        for b in range(a + 1, len(seq)):
            p ^= seq[a] > seq[b]
    return p

# ------------------------------------------------------------------ (2) global Berezin integral
def bterms(i, j):
    """the 4 bilinear terms of B_e as (gen1, gen2, coeff) meaning coeff * gen1 gen2."""
    return [((i, 0), (i, 1), 1), ((j, 0), (j, 1), 1), ((i, 0), (j, 1), -1), ((j, 0), (i, 1), -1)]

def berezin(n, edges, X, r):
    """coefficient of prod_{v != r} pb_v p_v (v ascending) in prod_{e in X} (1 + B_e)."""
    X = list(X); used = set(); total = 0
    need = 2 * (n - 1)
    def rec(k, seq, coef):
        nonlocal total
        if k == len(X):
            if len(seq) == need:
                total += coef * (-1) ** inv_parity(seq)
            return
        rec(k + 1, seq, coef)              # term 1
        i, j = edges[X[k]]
        for g1, g2, c in bterms(i, j):
            if g1[0] == r or g2[0] == r or g1 in used or g2 in used:
                continue
            used.add(g1); used.add(g2)
            rec(k + 1, seq + [g1, g2], coef * c)
            used.discard(g1); used.discard(g2)
    rec(0, [], 1)
    return total

# ------------------------------------------------------------------ (3) blob evaluation
NSTATES = {6: 6, 5: 5}

def side_options(alpha, label, e, v, i, j, lower_is_v, w=1, u=1):
    """weighted: multiply 'used' by w and each bilinear term by u (both put on the lower side).
    For the 5-state product label each side carries its own u."""
    opts = _side_options(alpha, label, e, v, i, j, lower_is_v)
    out = []
    for (used, lp, cg, c) in opts:
        f = 1
        if lower_is_v and used:
            f *= w
        if alpha == 5 and label == 1:
            if lp: f *= u
        elif alpha == 5 and label == 2:
            if lower_is_v: f *= u * u
        elif lower_is_v and label in ((2, 3, 4, 5) if alpha == 6 else (3, 4)):
            f *= u
        out.append((used, lp, cg, c * f))
    return out

def _side_options(alpha, label, e, v, i, j, lower_is_v):
    """options at endpoint v (in blob of v) for crossing edge e=(i,j) with given label.
    returns list of (used, local_pair or None, cross_gen or None, coeff)."""
    loc = ((v, 0), (v, 1))
    if alpha == 6:
        if label == 0:
            return [(0, None, None, 1)]
        if label == 1:
            return [(1, None, None, 1)]
        if label == 2:   # pb_i p_i
            return [(1, loc if v == i else None, None, 1)]
        if label == 3:   # pb_j p_j
            return [(1, loc if v == j else None, None, 1)]
        if label == 4:   # - pb_i p_j
            g = (i, 0) if v == i else (j, 1)
            return [(1, None, g, -1 if lower_is_v else 1)]
        if label == 5:   # - pb_j p_i
            g = (j, 0) if v == j else (i, 1)
            return [(1, None, g, -1 if lower_is_v else 1)]
    else:
        if label == 0:
            return [(0, None, None, 1)]
        if label == 1:   # (1 + loc_i)(1 + loc_j): each side independently
            return [(1, None, None, 1), (1, loc, None, 1)]
        if label == 2:   # - loc_i loc_j
            return [(1, loc, None, -1 if lower_is_v else 1)]
        if label == 3:
            g = (i, 0) if v == i else (j, 1)
            return [(1, None, g, -1 if lower_is_v else 1)]
        if label == 4:
            g = (j, 0) if v == j else (i, 1)
            return [(1, None, g, -1 if lower_is_v else 1)]
    raise ValueError

def is_cross_label(alpha, label):
    return label in ((4, 5) if alpha == 6 else (3, 4))

class Blobs:
    def __init__(self, n, edges, r, blob, pos, alpha=6, w=None, u=None):
        self.w = w or [1] * len(edges); self.u = u or [1] * len(edges)
        self.n, self.edges, self.r, self.blob, self.pos, self.alpha = n, edges, r, blob, pos, alpha
        self.g = max(blob) + 1
        self.cross = [k for k, (i, j) in enumerate(edges) if blob[i] != blob[j]]
        self.internal = [[k for k, (i, j) in enumerate(edges) if blob[i] == blob[j] == a]
                         for a in range(self.g)]
        self.inc = [[k for k in self.cross if a in (blob[edges[k][0]], blob[edges[k][1]])]
                    for a in range(self.g)]
        self.memo = {}

    def key(self, gen):
        v, t = gen
        return (self.blob[v], self.pos[v], t)

    def T(self, a, labs):
        """local table of blob a; labs: tuple of labels of self.inc[a] (same order)."""
        mk = (a, labs)
        if mk in self.memo:
            return self.memo[mk]
        blob, edges, r = self.blob, self.edges, self.r
        verts = [v for v in range(self.n) if blob[v] == a]
        # per crossing edge: option list at the a-side endpoint
        cross_opts = []
        for k, lab in zip(self.inc[a], labs):
            i, j = edges[k]
            v = i if blob[i] == a else j
            other = j if v == i else i
            lower_is_v = blob[v] < blob[other]
            cross_opts.append((k, v, other, side_options(self.alpha, lab, k, v, i, j, lower_is_v,
                                                                  self.w[k], self.u[k])))
        total = 0
        internal = self.internal[a]
        # enumerate crossing side options x internal edge states
        def finish(deg, used, local_pairs, cross_pairs, coef):
            # cross_pairs: list of (edge k, a-gen, other blob)
            for v in verts:
                if deg[v] != 2:
                    return 0
                if v != r and ((v, 0) not in used or (v, 1) not in used):
                    return 0
            par = 0
            # normalisation of local pairs
            for (g1, g2) in local_pairs:
                if self.key(g1) > self.key(g2):
                    par ^= 1
            # normalisation of cross pairs whose lower blob is a: the a-generator must come
            # first; in each term coeff*g1 g2 with g1 = psibar, g2 = psi.  a-gen is g1 iff a-gen
            # is a psibar.
            for (k, ga, ob) in cross_pairs:
                if a < ob and ga[1] == 1:      # a-gen is the psi (second factor) -> swap
                    par ^= 1
            # interleavings among pairs touching a (except same-bundle cross/cross)
            P = [('L', (self.key(g1), self.key(g2)) if self.key(g1) < self.key(g2)
                  else (self.key(g2), self.key(g1)), None) for (g1, g2) in local_pairs]
            for (k, ga, ob) in cross_pairs:
                ka = self.key(ga); kf = (ob, -1, 0)
                P.append(('C', (ka, kf) if ka < kf else (kf, ka), ob))
            for x in range(len(P)):
                for y in range(x + 1, len(P)):
                    tp, (x1, y1), o1 = P[x]
                    tq, (x2, y2), o2 = P[y]
                    if tp == 'C' and tq == 'C' and o1 == o2:
                        continue
                    if (x1 < x2 < y1 < y2) or (x2 < x1 < y2 < y1):
                        par ^= 1
            # same-bundle contributions
            byb = {}
            for (k, ga, ob) in cross_pairs:
                byb.setdefault(ob, []).append((k, self.key(ga)))
            for ob, lst in byb.items():
                lst.sort()
                N = len(lst)
                if a < ob:
                    par ^= (N * (N - 1) // 2) & 1
                for x in range(N):
                    for y in range(x + 1, N):
                        par ^= lst[x][1] < lst[y][1]
            return coef * (-1) ** par

        deg = {v: 0 for v in verts}
        used = set()
        def rec_cross(idx, local_pairs, cross_pairs, coef):
            nonlocal total
            if idx == len(cross_opts):
                rec_int(0, local_pairs, cross_pairs, coef)
                return
            k, v, other, opts = cross_opts[idx]
            for (u, lp, cg, c) in opts:
                if u and deg[v] >= 2:
                    continue
                gens = (list(lp) if lp else []) + ([cg] if cg else [])
                if any(gg[0] == r or gg in used for gg in gens):
                    continue
                deg[v] += u
                for gg in gens: used.add(gg)
                rec_cross(idx + 1, local_pairs + ([lp] if lp else []),
                          cross_pairs + ([(k, cg, blob[other])] if cg else []), coef * c)
                for gg in gens: used.discard(gg)
                deg[v] -= u
        def rec_int(idx, local_pairs, cross_pairs, coef):
            nonlocal total
            if idx == len(internal):
                total += finish(deg, used, local_pairs, cross_pairs, coef)
                return
            k = internal[idx]; i, j = edges[k]
            rec_int(idx + 1, local_pairs, cross_pairs, coef)       # unused
            if deg[i] >= 2 or deg[j] >= 2:
                return
            deg[i] += 1; deg[j] += 1
            W = self.w[k]; Uu = self.u[k]
            rec_int(idx + 1, local_pairs, cross_pairs, coef * W)   # used, term 1
            for g1, g2, c in bterms(i, j):
                if g1[0] == r or g2[0] == r or g1 in used or g2 in used:
                    continue
                used.add(g1); used.add(g2)
                rec_int(idx + 1, local_pairs + [(g1, g2)], cross_pairs, coef * c * W * Uu)
                used.discard(g1); used.discard(g2)
            deg[i] -= 1; deg[j] -= 1
        rec_cross(0, [], [], 1)
        self.memo[mk] = total
        return total

    def bundle_parities(self, lab):
        """lab: dict crossing edge -> label.  N_ab mod 2 per bundle (a<b)."""
        Pp = {}
        for k in self.cross:
            i, j = self.edges[k]
            a, b = sorted((self.blob[i], self.blob[j]))
            Pp[(a, b)] = Pp.get((a, b), 0) ^ is_cross_label(self.alpha, lab[k])
        return Pp

    def interleaving_bundle_pairs(self):
        g = self.g; out = []
        for a, c, b, d in itertools.combinations(range(g), 4):
            out.append(((a, b), (c, d)))  # a<c<b<d  (from combinations a<c<b<d sorted)
        return out

    def labels_iter(self):
        """crossing-label assignments, pruned only by per-vertex degree<=2 and generator reuse
        (both make some T_a vanish, so pruning does not change the sum)."""
        edges, blob, r = self.edges, self.blob, self.r
        C = self.cross
        deg = [0] * self.n; used = set(); lab = {}
        A = self.alpha
        def gens_of(k, l):
            i, j = edges[k]
            if A == 6:
                return {0: [], 1: [], 2: [(i, 0), (i, 1)], 3: [(j, 0), (j, 1)],
                        4: [(i, 0), (j, 1)], 5: [(j, 0), (i, 1)]}[l]
            return {0: [], 1: [], 2: [(i, 0), (i, 1), (j, 0), (j, 1)],
                    3: [(i, 0), (j, 1)], 4: [(j, 0), (i, 1)]}[l]
        def rec(idx):
            if idx == len(C):
                yield dict(lab); return
            k = C[idx]; i, j = edges[k]
            for l in range(A):
                u = l != 0
                if u and (deg[i] >= 2 or deg[j] >= 2):
                    continue
                gs = gens_of(k, l)
                if any(gg[0] == r or gg in used for gg in gs):
                    continue
                deg[i] += u; deg[j] += u
                for gg in gs: used.add(gg)
                lab[k] = l
                yield from rec(idx + 1)
                for gg in gs: used.discard(gg)
                deg[i] -= u; deg[j] -= u
        yield from rec(0)

    def value(self):
        tot = 0
        ib = self.interleaving_bundle_pairs()
        for lab in self.labels_iter():
            prod = 1
            for a in range(self.g):
                prod *= self.T(a, tuple(lab[k] for k in self.inc[a]))
                if prod == 0:
                    break
            if prod == 0:
                continue
            Pp = self.bundle_parities(lab)
            s = sum(Pp.get(p, 0) * Pp.get(q, 0) for p, q in ib) & 1
            tot += prod * (-1) ** s
        return tot

    # ---------------------------------------------------------- (4) literal network
    def network_value(self, sum_copies=True):
        """Network on [g]: node a's setting = (its copy of every incident bundle string,
        copy bits p[a,(c,d)] for each bundle (c,d) with a<c<b<d for some b).
        W_a = T_a(own copies) * (-1)^{sum_b P_ab(own) * p[a,(c,d)]}.
        Psi_{a,b} = [a's copy of bundle ab == b's copy] * prod [p[a,(b,d)] == P_bd(b's copy)]
                    * prod [p[b,(a,d)] == P_ad(a's copy)].
        Because bundle copies are tested for equality we enumerate one common string per
        bundle (that is exactly the sum over theta in Definition 1(b)); copy bits are summed
        genuinely over {0,1} with their Psi indicator when sum_copies is True."""
        g = self.g
        copies = []  # (holder a, bundle (c,d), list of b)
        for a in range(g):
            for c in range(a + 1, g):
                for d in range(c + 1, g):
                    bs = [b for b in range(c + 1, d)]
                    if bs:
                        copies.append((a, (c, d), bs))
        tot = 0
        for lab in self.labels_iter():
            Tprod = 1
            for a in range(g):
                Tprod *= self.T(a, tuple(lab[k] for k in self.inc[a]))
                if Tprod == 0:
                    break
            if Tprod == 0:
                continue
            Pp = self.bundle_parities(lab)
            if sum_copies:
                inner = 0
                for bits in itertools.product((0, 1), repeat=len(copies)):
                    w = 1
                    for (a, cd, bs), p in zip(copies, bits):
                        # Psi_{a,c}: copy bit must equal c's parity of bundle cd
                        if p != Pp.get(cd, 0):
                            w = 0; break
                        w *= (-1) ** (p * (sum(Pp.get((a, b), 0) for b in bs) & 1))
                    inner += w
            else:
                inner = 1
                for (a, cd, bs) in copies:
                    p = Pp.get(cd, 0)
                    inner *= (-1) ** (p * (sum(Pp.get((a, b), 0) for b in bs) & 1))
            tot += Tprod * inner
        return tot

    def bit_accounting(self):
        g = self.g
        e = {}
        for k in self.cross:
            i, j = self.edges[k]
            a, b = sorted((self.blob[i], self.blob[j]))
            e[(a, b)] = e.get((a, b), 0) + 1
        c = {}
        for (a, b), m in e.items():
            c[(a, b)] = math.ceil(m * math.log2(self.alpha))
        ncopy = 0
        for a in range(g):
            for cc in range(a + 1, g):
                for d in range(cc + 1, g):
                    if d - cc >= 2:
                        c[(a, cc)] = c.get((a, cc), 0) + 1; ncopy += 1
        U = 2 * sum(c.values())
        P = max(sum(v for (x, y), v in c.items() if a in (x, y)) for a in range(g))
        return U, P, ncopy

# ------------------------------------------------------------------ random instances
def random_graph(n, p, rng, kind=None):
    while True:
        if kind == 'cubicish':
            edges = set()
            # union of a Hamiltonian-ish cycle or disjoint triangles plus random chords
            perm = list(range(n)); rng.shuffle(perm)
            if rng.random() < 0.5 and n % 3 == 0:
                for t in range(0, n, 3):
                    for x, y in ((0, 1), (1, 2), (0, 2)):
                        edges.add(tuple(sorted((perm[t + x], perm[t + y]))))
            else:
                for t in range(n):
                    edges.add(tuple(sorted((perm[t], perm[(t + 1) % n]))))
            for _ in range(rng.randint(1, n)):
                x, y = rng.sample(range(n), 2)
                edges.add(tuple(sorted((x, y))))
        else:
            edges = {(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p}
        edges = sorted(edges)
        deg = [0] * n
        for i, j in edges:
            deg[i] += 1; deg[j] += 1
        if min(deg) >= 2:
            rng.shuffle(edges)
            edges = [(i, j) if rng.random() < 0.5 else (j, i) for i, j in edges]
            return edges

def special_graphs():
    out = []
    # Petersen graph: no HC, has 2-factors (two 5-cycles)
    pet = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + \
          [(i, i + 5) for i in range(5)]
    out.append(('petersen', 10, pet))
    # prism C3 x K2 and C4 x K2
    for m in (3, 4):
        e = [(i, (i + 1) % m) for i in range(m)] + [(m + i, m + (i + 1) % m) for i in range(m)] + \
            [(i, m + i) for i in range(m)]
        out.append(('prism%d' % m, 2 * m, e))
    out.append(('K4', 4, list(itertools.combinations(range(4), 2))))
    out.append(('K5', 5, list(itertools.combinations(range(5), 2))))
    out.append(('K33', 6, [(i, 3 + j) for i in range(3) for j in range(3)]))
    # two disjoint triangles joined by one edge pair (no HC: bridge-ish), and 3 triangles in a ring
    out.append(('2tri+2', 6, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4)]))
    out.append(('3tri', 9, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (6, 7), (7, 8), (6, 8),
                            (2, 3), (5, 6), (8, 0)]))
    out.append(('K34', 7, [(i, 3 + j) for i in range(3) for j in range(4)]))   # 0 HC, n odd bip
    return out

def random_partition(n, rng, g):
    mode = rng.random()
    if mode < 0.3:
        blob = [rng.randrange(g) for _ in range(n)]
    elif mode < 0.6:   # very unequal: most in one blob
        big = rng.randrange(g)
        blob = [big if rng.random() < 0.7 else rng.randrange(g) for _ in range(n)]
    else:              # round robin of a random permutation (balanced), maybe with empty blobs
        perm = list(range(n)); rng.shuffle(perm)
        gg = max(1, g - rng.randint(0, 2))
        blob = [0] * n
        for t, v in enumerate(perm):
            blob[v] = t % gg
        # relabel blobs randomly in [g] so empty ones land anywhere
        relab = list(range(g)); rng.shuffle(relab)
        blob = [relab[b] for b in blob]
    # force max label g-1 present so that g is as intended (an empty blob may still exist)
    pos = list(range(n)); rng.shuffle(pos)
    return blob, pos

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(seed)
    stats = dict(identity1=0, berezin=0, berezin_random_subgraph=0, blob6=0, blob5=0, network=0,
                 nonzero_hc=0, zero_hc_with_2factors=0, fail=0)
    # (a) Berezin = det on random subgraphs (not only 2-factors), all roots
    for t in range(trials):
        n = rng.randint(2, 7)
        edges = random_graph(n, rng.uniform(0.3, 0.9), rng) if n >= 3 else [(0, 1)]
        X = [k for k in range(len(edges)) if rng.random() < 0.6]
        for r in range(n):
            b = berezin(n, edges, X, r); d = tau(n, edges, X, r)
            if b != d:
                print('BEREZIN FAIL', n, edges, X, r, b, d); stats['fail'] += 1
            stats['berezin_random_subgraph'] += 1
    insts = [(nm, n, e) for nm, n, e in special_graphs()]
    for t in range(trials):
        n = rng.randint(3, 9)
        kind = 'cubicish' if rng.random() < 0.5 else None
        insts.append(('rand', n, random_graph(n, rng.uniform(0.25, 0.7), rng, kind)))
    for nm, n, edges in insts:
        if len(edges) > 18:
            continue
        hc = hc_count(n, edges)
        tfs = two_factors(n, edges)
        r = rng.randrange(n)
        s = sum(tau(n, edges, X, r) for X in tfs)
        ok1 = s == n * hc
        stats['identity1'] += 1
        if hc: stats['nonzero_hc'] += 1
        elif tfs: stats['zero_hc_with_2factors'] += 1
        if len(tfs) <= 30 and n <= 8:
            sb = sum(berezin(n, edges, X, r) for X in tfs)
            ok1 &= sb == s; stats['berezin'] += 1
        if not ok1:
            print('ID1 FAIL', nm, n, edges, hc, s); stats['fail'] += 1
        for rep in range(2):
            g = rng.randint(2, 6)
            blob, pos = random_partition(n, rng, g)
            g_eff = max(blob) + 1
            weighted = rep == 1
            if weighted:
                w = [rng.randint(1, 3) for _ in edges]; u = [rng.choice([-3, -2, -1, 1, 2, 3]) for _ in edges]
                target = 0
                for X in tfs:
                    pw = 1
                    for k in X: pw *= w[k]
                    target += pw * tau(n, edges, X, r, u)
            else:
                w = u = None; target = n * hc
            for alpha in (6, 5):
                B = Blobs(n, edges, r, blob, pos, alpha, w, u)
                if len(B.cross) > 14:
                    continue
                v = B.value()
                stats['blob%d' % alpha] += 1; stats['weighted'] = stats.get('weighted', 0) + weighted
                if v != target:
                    print('BLOB FAIL', alpha, weighted, nm, n, edges, r, blob, pos, v, target)
                    stats['fail'] += 1
                if alpha == 6 and g_eff <= 6 and len(B.cross) <= 10:
                    nv = B.network_value(sum_copies=(g_eff <= 5))
                    stats['network'] += 1
                    if nv != target:
                        print('NETWORK FAIL', nm, n, edges, r, blob, nv, n * hc)
                        stats['fail'] += 1
    print(stats)

if __name__ == '__main__':
    main()
