#!/usr/bin/env python3
"""Referee check (independent): n*#HC = sum_{2-factors X} tau(X), its Berezin form,
and the blob (network) factorisation with the interleaving sign rule.

Everything is exact integer arithmetic.  Run: python3 review_hc_blobs.py [seed] [trials]
"""
import itertools, random, sys
from functools import lru_cache

# ---------------------------------------------------------------- basics
def hc_count(n, edges):
    """number of undirected Hamiltonian cycles (n>=3), brute force DFS."""
    adj = [set() for _ in range(n)]
    for i, j in edges:
        adj[i].add(j); adj[j].add(i)
    cnt = 0
    def dfs(v, seen, depth):
        nonlocal cnt
        if depth == n:
            if 0 in adj[v]:
                cnt += 1
            return
        for w in adj[v]:
            if not seen >> w & 1:
                dfs(w, seen | 1 << w, depth + 1)
    dfs(0, 1, 1)
    return cnt // 2 if n >= 3 else None

def two_factors(n, edges):
    m = len(edges)
    out = []
    deg = [0] * n
    def rec(k, chosen):
        if k == m:
            if all(d == 2 for d in deg):
                out.append(list(chosen))
            return
        i, j = edges[k]
        # remaining capacity pruning
        rec(k + 1, chosen)
        if deg[i] < 2 and deg[j] < 2:
            deg[i] += 1; deg[j] += 1; chosen.append(k)
            rec(k + 1, chosen)
            chosen.pop(); deg[i] -= 1; deg[j] -= 1
    rec(0, [])
    return out

def det_int(M):
    """Bareiss fraction-free determinant (exact)."""
    M = [row[:] for row in M]
    N = len(M)
    if N == 0:
        return 1
    sign, prev = 1, 1
    for k in range(N - 1):
        if M[k][k] == 0:
            for r in range(k + 1, N):
                if M[r][k] != 0:
                    M[k], M[r] = M[r], M[k]; sign = -sign; break
            else:
                return 0
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[N - 1][N - 1]

def tau(n, edges, X, r):
    L = [[0] * n for _ in range(n)]
    for k in X:
        i, j = edges[k]
        L[i][i] += 1; L[j][j] += 1; L[i][j] -= 1; L[j][i] -= 1
    idx = [v for v in range(n) if v != r]
    return det_int([[L[a][b] for b in idx] for a in idx])

# ---------------------------------------------------------------- Grassmann (global check)
# generator id: psibar_v -> 2v, psi_v -> 2v+1.  Canonical top monomial T = prod_{v!=r} psibar_v psi_v (v ascending)
def gmul_mono(m1, m2):
    """product of two sorted-tuple monomials; returns (sign, mono) or None."""
    s = set(m1)
    for g in m2:
        if g in s:
            return None
    # sign = parity of inversions in concatenation m1+m2 (both sorted)
    inv = 0
    for g in m2:
        inv += sum(1 for h in m1 if h > g)
    return (-1 if inv & 1 else 1), tuple(sorted(m1 + m2))

def gmul(A, B):
    C = {}
    for ma, ca in A.items():
        for mb, cb in B.items():
            r = gmul_mono(ma, mb)
            if r is None:
                continue
            s, mm = r
            C[mm] = C.get(mm, 0) + s * ca * cb
    return {k: v for k, v in C.items() if v}

def berezin_global(n, edges, X, r):
    def gen(kind, v):  # kind 0 = psibar, 1 = psi
        return None if v == r else 2 * v + kind
    F = {(): 1}
    for k in X:
        i, j = edges[k]
        f = {(): 1}
        for (a, ca) in ((i, 1), (j, -1)):
            for (b, cb) in ((i, 1), (j, -1)):
                ga, gb = gen(0, a), gen(1, b)
                if ga is None or gb is None:
                    continue
                r2 = gmul_mono((ga,), (gb,))
                s, mm = r2
                f[mm] = f.get(mm, 0) + s * ca * cb
        F = gmul(F, f)
    top = tuple(sorted(g for v in range(n) if v != r for g in (2 * v, 2 * v + 1)))
    # canonical order psibar_v psi_v ascending v == sorted order, so coefficient directly
    return F.get(top, 0)

# ---------------------------------------------------------------- blob network
def perm_sign_to_canonical(word, canon_pos):
    """sign of sorting the letter list `word` into canonical order; 0 if not a permutation of canon."""
    if len(word) != len(canon_pos) or len(set(word)) != len(word):
        return 0
    try:
        p = [canon_pos[x] for x in word]
    except KeyError:
        return 0
    inv = 0
    for a in range(len(p)):
        for b in range(a + 1, len(p)):
            if p[a] > p[b]:
                inv += 1
    return -1 if inv & 1 else 1

# crossing-edge states (edge e=(i in blob a, j in blob b), a<b):
# 6-state:  0 out | 1 in,'1' | 2 in,A=psibar_i psi_i | 3 in,B=psibar_j psi_j | 4 in,C1=-psibar_i psi_j | 5 in,C2=-psibar_j psi_i
# naive5:   states {0,2,3,4,5} (drops 'in with 1')  -- expected to FAIL
# trick5:   0 out | 1 in,(1+A)(1+B) summed locally | 2 in, -A*B | 4 C1 | 5 C2
VERBOSE = False
STATESETS = {'six': [0, 1, 2, 3, 4, 5], 'naive5': [0, 2, 3, 4, 5], 'trick5': [0, 1, 2, 4, 5]}

def network_value(n, edges, blob, K, r, mode='six', quad_sign=True, copy_bits=False):
    """sum over crossing-edge labels of prod_a W_a(labels at a) * quadruple sign.
    If copy_bits: the quadruple sign is realised by explicit extra edge variables z[(a,c,b)]
    on node pair {a,c} (a<c<b), forced at c to equal XOR_{d>b} P_cd, multiplied at a as (-1)^{P_ab z}."""
    m = len(edges)
    cross = [k for k in range(m) if blob[edges[k][0]] != blob[edges[k][1]]]
    # orient crossing edges so first endpoint is in the lower blob
    orient = {}
    for k in cross:
        i, j = edges[k]
        if blob[i] > blob[j]:
            i, j = j, i
        orient[k] = (i, j)
    pair_of = {k: (blob[orient[k][0]], blob[orient[k][1]]) for k in cross}
    # global order of cross terms: by (pair, edge index)
    cross_sorted = sorted(cross, key=lambda k: (pair_of[k], k))
    internal = {a: [k for k in range(m) if blob[edges[k][0]] == a and blob[edges[k][1]] == a] for a in range(K)}
    incident = {a: [k for k in cross_sorted if a in pair_of[k]] for a in range(K)}
    verts = {a: [v for v in range(n) if blob[v] == a] for a in range(K)}
    canon = {}
    for a in range(K):
        lst = [g for v in verts[a] if v != r for g in (('b', v), ('p', v))]
        canon[a] = {x: t for t, x in enumerate(lst)}

    def gen(kind, v):
        return None if v == r else (kind, v)

    def letters_internal_state(k, s):
        """returns list of (coef, letters) for internal edge state s (s in 1..5)."""
        i, j = edges[k]
        if s == 1: return (1, [])
        if s == 2: g = [gen('b', i), gen('p', i)]; c = 1
        if s == 3: g = [gen('b', j), gen('p', j)]; c = 1
        if s == 4: g = [gen('b', i), gen('p', j)]; c = -1
        if s == 5: g = [gen('b', j), gen('p', i)]; c = -1
        if None in g: return None
        return (c, g)

    @lru_cache(maxsize=None)
    def W(a, lab, zin, zout):
        """lab: tuple of states for incident[a] edges (same order); zin/zout copy bits (see below)."""
        labd = dict(zip(incident[a], lab))
        # per-vertex crossing degree
        deg = {v: 0 for v in verts[a]}
        for k, s in labd.items():
            if s != 0:
                i, j = orient[k]
                v = i if blob[i] == a else j
                deg[v] += 1
        if any(d > 2 for d in deg.values()):
            return 0
        # cross letters of a, in global order, + coefficients + local-term options from crossing edges
        cross_letters = []
        coef = 1
        local_opts = []  # list of option-lists [(c, letters), ...] that must be multiplied (summed per option)
        for k in incident[a]:
            s = labd[k]
            i, j = orient[k]
            lower = (blob[i] == a)
            if s in (0,):
                continue
            if mode == 'trick5' and s == 1:
                v = i if lower else j
                g = [gen('b', v), gen('p', v)]
                opts = [(1, [])] + ([(1, g)] if None not in g else [])
                local_opts.append(opts)
                continue
            if mode == 'trick5' and s == 2:
                v = i if lower else j
                g = [gen('b', v), gen('p', v)]
                if None in g: return 0
                if lower: coef *= -1
                local_opts.append([(1, g)])
                continue
            if s == 1:
                continue
            if s == 2:
                if lower:
                    g = [gen('b', i), gen('p', i)]
                    if None in g: return 0
                    local_opts.append([(1, g)])
                continue
            if s == 3:
                if not lower:
                    g = [gen('b', j), gen('p', j)]
                    if None in g: return 0
                    local_opts.append([(1, g)])
                continue
            # s in (4,5): odd crossing term
            if s == 4:   # -psibar_i psi_j : letters (psibar_i @lower, psi_j @upper), coef -1
                lw, up = gen('b', i), gen('p', j); c = -1
            else:        # -psibar_j psi_i = + psi_i psibar_j : letters (psi_i @lower, psibar_j @upper), coef +1
                lw, up = gen('p', i), gen('b', j); c = 1
            # if either side vanishes the whole term is zero; both nodes see this
            if lw is None or up is None:
                return 0
            if lower:
                coef *= c
                cross_letters.append(lw)
            else:
                cross_letters.append(up)
        # local sign factors from pair parities
        npar = {}
        for k in incident[a]:
            if labd[k] in (4, 5):
                pr = pair_of[k]
                npar[pr] = npar.get(pr, 0) + 1
        sgn = 0
        for pr, c in npar.items():
            if pr[0] == a:
                sgn += c * (c - 1) // 2
        lowpairs = [(pr, c) for pr, c in npar.items() if pr[0] == a]
        for (p1, c1), (p2, c2) in itertools.combinations(lowpairs, 2):
            sgn += c1 * c2
        uppairs = [(pr, c) for pr, c in npar.items() if pr[1] == a]
        for (p1, c1), (p2, c2) in itertools.combinations(uppairs, 2):
            sgn += c1 * c2
        # copy bits
        if copy_bits:
            # zout: dict (a',b)->bit for a'<a<b : must equal XOR_{d>b} P_{a d}
            for (ap, b), bit in zout:
                val = sum(npar.get((a, d), 0) for d in range(b + 1, K)) & 1
                if val != bit:
                    return 0
            # zin: dict (c,b)->bit for a<c<b : multiply (-1)^{P_ab * bit}
            for (c, b), bit in zin:
                sgn += (npar.get((a, b), 0) & 1) * bit
        coef *= -1 if sgn & 1 else 1
        # sum over internal-edge states
        total = 0
        ints = internal[a]
        # recursive enumeration of internal-edge states with degree pruning
        remaining = {v: 0 for v in verts[a]}
        for k in ints:
            i, j = edges[k]; remaining[i] += 1; remaining[j] += 1
        d2 = dict(deg)
        acc = []
        def irec(t, wc, letters):
            nonlocal total
            if t == len(ints):
                if any(d != 2 for d in d2.values()):
                    return
                for choice in itertools.product(*local_opts):
                    cc = wc
                    lw = list(letters)
                    for c, g in choice:
                        cc *= c; lw += g
                    sg = perm_sign_to_canonical(lw + cross_letters, canon[a])
                    total += cc * sg
                return
            k = ints[t]
            i, j = edges[k]
            remaining[i] -= 1; remaining[j] -= 1
            # state 0
            if d2[i] + remaining[i] >= 2 and d2[j] + remaining[j] >= 2:
                irec(t + 1, wc, letters)
            if d2[i] < 2 and d2[j] < 2:
                d2[i] += 1; d2[j] += 1
                for s in range(1, 6):
                    res = letters_internal_state(k, s)
                    if res is None: continue
                    c, g = res
                    irec(t + 1, wc * c, letters + g)
                d2[i] -= 1; d2[j] -= 1
            remaining[i] += 1; remaining[j] += 1
        if all(deg[v] + remaining[v] >= 2 for v in verts[a]):
            irec(0, coef, [])
        return total

    states = STATESETS[mode]
    # copy-bit variables
    zvars = []
    if copy_bits:
        for a in range(K):
            for c in range(a + 1, K):
                for b in range(c + 1, K - 1):  # need some d > b
                    zvars.append((a, c, b))
    value = 0
    vcount = {v: 0 for v in range(n)}
    lab = {}
    order = cross_sorted                      # decide crossing edges pair by pair
    last = {a: -1 for a in range(K)}
    for t, k in enumerate(order):
        for a in pair_of[k]:
            last[a] = t
    done_at = {}
    for a in range(K):
        done_at.setdefault(last[a], []).append(a)
    quads = list(itertools.combinations(range(K), 4))

    def finish(partial):
        nonlocal value
        npar = {}
        for k in cross:
            if lab[k] in (4, 5):
                npar[pair_of[k]] = npar.get(pair_of[k], 0) + 1
        if not copy_bits:
            qs = 0
            if quad_sign:
                for a, c, b, d in quads:
                    qs += npar.get((a, b), 0) * npar.get((c, d), 0)
            value += partial * (-1 if qs & 1 else 1)
            return
        for zb in itertools.product((0, 1), repeat=len(zvars)):
            zd = dict(zip(zvars, zb))
            prod = 1
            for a in range(K):
                tt = tuple(lab[k] for k in incident[a])
                zin = tuple(sorted(((c, b), bit) for (aa, c, b), bit in zd.items() if aa == a))
                zout = tuple(sorted(((aa, b), bit) for (aa, c, b), bit in zd.items() if c == a))
                w = W(a, tt, zin, zout)
                if w == 0:
                    prod = 0; break
                prod *= w
            value += prod

    rem = {v: 0 for v in range(n)}
    for (i, j) in edges:
        rem[i] += 1; rem[j] += 1
    def node_factor(t, partial):
        for a in done_at.get(t, []):
            w = W(a, tuple(lab[k] for k in incident[a]), (), ())   # zero here => zero for every copy-bit setting
            partial *= w
            if partial == 0:
                return 0
        return partial
    def rec(t, partial):
        if t == len(order):
            finish(partial); return
        k = order[t]
        i, j = edges[k]
        rem[i] -= 1; rem[j] -= 1
        for s in states:
            if s == 0 and (vcount[i] + rem[i] < 2 or vcount[j] + rem[j] < 2):
                continue
            if s != 0:
                if vcount[i] >= 2 or vcount[j] >= 2:
                    continue
                vcount[i] += 1; vcount[j] += 1
            lab[k] = s
            p2 = node_factor(t, partial)
            if p2 != 0:
                rec(t + 1, p2)
            if s != 0:
                vcount[i] -= 1; vcount[j] -= 1
        rem[i] += 1; rem[j] += 1
    p0 = node_factor(-1, 1)    # nodes with no crossing edges
    if p0 != 0:
        rec(0, p0)
    return value

# ---------------------------------------------------------------- driver
def rand_graph(rng, n, p):
    return [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p]

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(seed)
    stats = dict(identity=0, berezin=0, net6=0, trick5=0, naive5_fail=0, noquad_fail=0, copy=0,
                 nonzero=0, quad_relevant=0)
    # ---- (a) identity + berezin on many graphs, all roots
    fams = []
    for _ in range(trials):
        n = rng.randint(3, 9)
        fams.append((n, rand_graph(rng, n, rng.choice([0.4, 0.6, 0.8, 1.0]))))
    # structured: disjoint triangles + bridges (many-cycle 2-factors), K_n, prism, Petersen
    fams.append((6, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]))
    fams.append((9, [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(6,7),(7,8),(6,8),(0,3),(3,6),(6,0),(1,4),(4,7),(7,1),(2,5),(5,8),(8,2)]))
    pet = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
    fams.append((10, [tuple(sorted(e)) for e in pet]))
    for nn in (3, 4, 5, 6, 7):
        fams.append((nn, [(i, j) for i in range(nn) for j in range(i + 1, nn)]))
    for n, E in fams:
        h = hc_count(n, E)
        tf = two_factors(n, E)
        for r in range(n):
            s = sum(tau(n, E, X, r) for X in tf)
            assert s == n * h, (n, E, r, s, h)
            stats['identity'] += 1
        for X in tf[:20]:
            for r in (0, n - 1):
                assert berezin_global(n, E, X, r) == tau(n, E, X, r), (n, E, X, r)
                stats['berezin'] += 1
    # Berezin = det on arbitrary edge subsets (not just 2-factors)
    for _ in range(100):
        n = rng.randint(2, 7)
        E = rand_graph(rng, n, 0.6)
        X = [k for k in range(len(E)) if rng.random() < 0.7]
        r = rng.randrange(n)
        assert berezin_global(n, E, X, r) == tau(n, E, X, r)
        stats['berezin'] += 1
    # ---- (b) blob network
    netcases = []
    for _ in range(trials):
        n = rng.randint(4, 9)
        if rng.random() < 0.75:      # sparse Hamiltonian-ish: random cycle + chords
            perm = list(range(n)); rng.shuffle(perm)
            Es = {tuple(sorted((perm[t], perm[(t + 1) % n]))) for t in range(n)}
            for _ in range(rng.randint(1, n // 2 + 2)):
                i, j = rng.sample(range(n), 2); Es.add(tuple(sorted((i, j))))
            E = sorted(Es)
        else:
            E = rand_graph(rng, n, rng.choice([0.4, 0.55]))
        K = rng.randint(2, 6) if n > 6 else rng.randint(2, 5)
        if n >= 8: K = max(K, 3)
        mode = rng.choice(['balanced', 'random', 'singletons', 'withempty'])
        if mode == 'singletons' and n <= 6:
            K = n; blob = list(range(n)); rng.shuffle(blob)
        elif mode == 'withempty':
            blob = [rng.randrange(K + 1) for _ in range(n)]; K = K + 1
        else:
            blob = [rng.randrange(K) for _ in range(n)]
        netcases.append((n, E, blob, K, rng.randrange(n)))
    netcases.append((6, [(i, j) for i in range(6) for j in range(i + 1, 6)], [0, 2, 1, 3, 0, 2], 4, 3))
    if len(sys.argv) > 3:
        netcases.append((6, [(i, j) for i in range(6) for j in range(i + 1, 6)], [0, 1, 2, 3, 4, 5], 6, 0))
    netcases.append((8, [(i, (i + 1) % 8) for i in range(8)] + [(i, i + 4) for i in range(4)], [0, 2, 4, 1, 3, 5, 0, 1], 6, 2))
    import time
    for ci, (n, E, blob, K, r) in enumerate(netcases):
        t0 = time.time()
        h = hc_count(n, E)
        target = n * h
        v6 = network_value(n, E, blob, K, r, 'six')
        assert v6 == target, ('six', n, E, blob, K, r, v6, target)
        stats['net6'] += 1
        if target: stats['nonzero'] += 1
        vt = network_value(n, E, blob, K, r, 'trick5')
        assert vt == target, ('trick5', n, E, blob, K, r, vt, target)
        stats['trick5'] += 1
        vn = network_value(n, E, blob, K, r, 'naive5')
        if vn != target: stats['naive5_fail'] += 1
        vq = network_value(n, E, blob, K, r, 'six', quad_sign=False)
        if vq != target: stats['noquad_fail'] += 1
        if K >= 4: stats['quad_relevant'] += 1
        if K <= 5:
            vc = network_value(n, E, blob, K, r, 'six', copy_bits=True)
            assert vc == target, ('copy', n, E, blob, K, r, vc, target)
            stats['copy'] += 1
        if VERBOSE:
            print(ci, n, len(E), K, 'blob', blob, 'r', r, 'n#HC', target, 'naive5', vn, 'noquad', vq, '%.1fs' % (time.time() - t0), flush=True)
    print('seed', seed, stats, flush=True)

if __name__ == '__main__':
    main()
