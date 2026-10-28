"""Shared exact-integer library for the checks of research/tsp-theorem.md.

Builds on proof_lib.py (the literal implementation of exact-hc-theorem.md):
  * WInstance   : the weighted undirected instance of tsp-theorem.md Section 2 (TSP-1).  The
                  weight z^{w_e} of an edge in the 2-factor sits on the internal factor, or on the
                  low-end piece alpha of a crossing edge; z is an integer Y (Kronecker, z = 2^b).
  * DInstance   : the directed instance of Section 3 (TSP-2): labels {N, 0, 2}, three per arc.
  * LabelNetwork: the network of exact-hc-theorem.md Definition 5.1 for an arbitrary label
                  alphabet (base-|L| blocks, copy bits, W_a, Psi_ab, c_ab, f_ab via pi_ab), so that
                  proof_lib.eval_network_brute / eval_network_grouped apply unchanged.
  * polynomial helpers (dict exponent -> coefficient), tours, cycle covers, arborescences.
No floating point anywhere.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from proof_lib import (gmul, gadd, gscale, gprod, ONE, ZERO, parity_of, Gens, pieces, pi_, c_kl,
                       Instance, two_factors, hc_count, det_bareiss, reduced_laplacian,
                       is_spanning_tree, count_spanning_trees_brute, random_graph, to_bits,
                       from_bits, eval_network_brute, eval_network_grouped)


# ----------------------------------------------------------------------------------------------
# polynomials in one variable: dict {exponent: coefficient}
# ----------------------------------------------------------------------------------------------
def padd(P, Q, c=1):
    out = dict(P)
    for e, v in Q.items():
        out[e] = out.get(e, 0) + c * v
    return {e: v for e, v in out.items() if v}


def pscale(P, c):
    return {e: c * v for e, v in P.items() if c * v}


def plowest(P):
    """lowest exponent with nonzero coefficient, or None."""
    return min(P) if P else None


def kron_eval(P, Y):
    return sum(c * Y ** e for e, c in P.items())


def kron_decode_nonneg(val, b, nterms):
    """base-2^b digits of a nonnegative integer; all coefficients are known to be >= 0 and < 2^b."""
    assert val >= 0
    out = []
    mask = (1 << b) - 1
    for _ in range(nterms):
        out.append(val & mask)
        val >>= b
    assert val == 0, "Kronecker overflow"
    return {e: c for e, c in enumerate(out) if c}


# ----------------------------------------------------------------------------------------------
# tours and 2-factors with weights (undirected)
# ----------------------------------------------------------------------------------------------
def ham_cycles(n, edges):
    """Hamiltonian cycles as frozensets of edge indices (n >= 3), each once."""
    if n < 3:
        return []
    adj = [[] for _ in range(n)]
    for k, (i, j) in enumerate(edges):
        adj[i].append((j, k)); adj[j].append((i, k))
    out = set()
    def dfs(v, seen, path):
        if len(path) == n - 1:
            for (u, k) in adj[v]:
                if u == 0:
                    out.add(frozenset(path + [k]))
            return
        for (u, k) in adj[v]:
            if not (seen >> u) & 1:
                dfs(u, seen | (1 << u), path + [k])
    dfs(0, 1, [])
    return sorted(out, key=sorted)


def tour_poly(n, edges, w):
    """sum_H z^{w(H)} over Hamiltonian cycles H (edge-index weights w)."""
    P = {}
    for H in ham_cycles(n, edges):
        t = sum(w[k] for k in H)
        P[t] = P.get(t, 0) + 1
    return P


def tau_brute(n, edge_list):
    return count_spanning_trees_brute(n, edge_list)


def twofactor_poly(n, edges, w, tau=None):
    """sum_{2-factors X} z^{w(X)} tau(V,X), tau by brute force unless given."""
    tau = tau or (lambda X: tau_brute(n, [edges[k] for k in X]))
    P = {}
    for X in two_factors(n, edges):
        t = sum(w[k] for k in X)
        c = tau(X)
        if c:
            P[t] = P.get(t, 0) + c
    return P


# ----------------------------------------------------------------------------------------------
# directed: cycle covers, directed Hamiltonian cycles, in-arborescences, L_out
# ----------------------------------------------------------------------------------------------
def dham_cycles(n, arcs):
    """directed Hamiltonian cycles as frozensets of arc indices (n >= 2)."""
    out_ = [[] for _ in range(n)]
    for k, (i, j) in enumerate(arcs):
        out_[i].append((j, k))
    res = []
    def dfs(v, seen, path):
        if len(path) == n - 1:
            for (u, k) in out_[v]:
                if u == 0:
                    res.append(frozenset(path + [k]))
            return
        for (u, k) in out_[v]:
            if not (seen >> u) & 1:
                dfs(u, seen | (1 << u), path + [k])
    dfs(0, 1, [])
    return res


def cycle_covers(n, arcs):
    """arc subsets with out-degree = in-degree = 1 everywhere, as sorted index tuples."""
    m = len(arcs)
    res = []
    outd = [0] * n; ind = [0] * n
    def rec(k, ch):
        if k == m:
            if all(o == 1 for o in outd) and all(i == 1 for i in ind):
                res.append(tuple(ch))
            return
        rec(k + 1, ch)
        i, j = arcs[k]
        if outd[i] < 1 and ind[j] < 1:
            outd[i] += 1; ind[j] += 1; ch.append(k)
            rec(k + 1, ch)
            ch.pop(); outd[i] -= 1; ind[j] -= 1
    rec(0, [])
    return res


def in_arborescences_brute(n, arc_list, r):
    """number of spanning in-arborescences towards r: n-1 arcs, every v != r has out-degree 1,
    r has out-degree 0, and every vertex reaches r."""
    cnt = 0
    for F in itertools.combinations(arc_list, n - 1):
        outd = [0] * n
        nxt = [None] * n
        ok = True
        for (i, j) in F:
            outd[i] += 1; nxt[i] = j
        if outd[r] != 0 or any(outd[v] != 1 for v in range(n) if v != r):
            continue
        for v in range(n):
            x = v; steps = 0
            while x != r and steps <= n:
                x = nxt[x]; steps += 1
            if x != r:
                ok = False; break
        cnt += ok
    return cnt


def reduced_Lout(n, arc_list, r):
    L = [[0] * n for _ in range(n)]
    for i, j in arc_list:
        L[i][i] += 1; L[i][j] -= 1
    keep = [v for v in range(n) if v != r]
    return [[L[u][v] for v in keep] for u in keep]


def dtour_poly(n, arcs, w):
    P = {}
    for H in dham_cycles(n, arcs):
        t = sum(w[k] for k in H)
        P[t] = P.get(t, 0) + 1
    return P


def cyclecover_poly(n, arcs, w, r=0):
    P = {}
    for X in cycle_covers(n, arcs):
        c = det_bareiss(reduced_Lout(n, [arcs[k] for k in X], r))
        if c:
            t = sum(w[k] for k in X)
            P[t] = P.get(t, 0) + c
    return P


def random_digraph(n, m, rng):
    allp = [(i, j) for i in range(n) for j in range(n) if i != j]
    return sorted(rng.sample(allp, min(m, len(allp))))


# ----------------------------------------------------------------------------------------------
# weighted undirected instance (Section 2 of tsp-theorem.md)
# ----------------------------------------------------------------------------------------------
class WInstance(Instance):
    """proof_lib.Instance with integer edge weights.  wdict: {(u,v) with u<v: weight}; Y: the
    integer substituted for z.  Internal edge e in X contributes Y^{w_e}(1+q_e); a crossing edge
    with label != N carries Y^{w_e} on its low-end piece alpha."""
    def __init__(self, n, edges, blob, r, wdict, Y, g=None, rng=None, gen_rng=None):
        super().__init__(n, edges, blob, r, g=g, rng=rng, gen_rng=gen_rng)
        self.wd = {(min(u, v), max(u, v)): w for (u, v), w in wdict.items()}
        self.Y = Y

    def wt(self, u, v):
        return self.wd[(min(u, v), max(u, v))]

    def internal_choices(self, a):
        if not hasattr(self, "_ic"):
            self._ic = {}
        if a in self._ic:
            return self._ic[a]
        ints = self.internal[a]
        out = []
        for xs in itertools.product((0, 1), repeat=len(ints)):
            dg = {v: 0 for v in self.V[a]}
            for x, (u, v) in zip(xs, ints):
                if x:
                    dg[u] += 1; dg[v] += 1
            if any(d > 2 for d in dg.values()):
                continue
            F = gprod([gscale(self.Gn.one_plus_q(u, v), self.Y ** self.wt(u, v))
                       for x, (u, v) in zip(xs, ints) if x])
            out.append((xs, dg, F))
        self._ic[a] = out
        return out

    def Gamma(self, a, lab_at):
        seq = []
        for k in self.delta[a]:
            s, t = self.cross[k]
            al, be = pieces(self.Gn, s, t, lab_at[k])
            if self.ak[k] == a:
                if lab_at[k] != "N":
                    al = gscale(al, self.Y ** self.wt(s, t))
                seq.append(al)
            else:
                seq.append(be)
        return gprod(seq)

    def mu(self):
        deg = [0] * self.n
        for i, j in self.edges:
            deg[i] += 1; deg[j] += 1
        return max(sum(deg[v] for v in self.V[a]) for a in range(self.g))


# ----------------------------------------------------------------------------------------------
# directed instance (Section 3 of tsp-theorem.md): labels N (arc not in X), 0 (even term), 2 (odd)
# ----------------------------------------------------------------------------------------------
DLABELS = ("N", 0, 2)


def dpieces(Gn, i, j, s, t, l, Yw=1):
    """pieces (alpha at low end s, beta at high end t) of label l for the arc i->j in X, whose
    factor is Yw * (1 + psibar_i (psi_i - psi_j)).  {s,t} = {i,j}."""
    if l == "N":
        return ONE, ONE
    if s == i:   # tail is the low end
        if l == 0:
            return gscale(gadd(ONE, gmul(Gn.pb(s), Gn.ps(s))), Yw), ONE
        return gscale(Gn.pb(s), Yw), gscale(Gn.ps(t), -1)
    # head is the low end: -psibar_i psi_j = psi_j psibar_i
    if l == 0:
        return gscale(ONE, Yw), gadd(ONE, gmul(Gn.pb(t), Gn.ps(t)))
    return gscale(Gn.ps(s), Yw), Gn.pb(t)


class DInstance:
    """digraph, partition, root, crossing order; arcs are (tail, head)."""
    def __init__(self, n, arcs, blob, r, wlist, Y, g=None, rng=None, gen_rng=None):
        self.n, self.arcs, self.blob, self.r = n, list(arcs), list(blob), r
        self.g = g if g is not None else max(blob) + 1
        self.Gn = Gens(n, r, gen_rng)
        self.Y = Y
        self.w = {a: wlist[k] for k, a in enumerate(self.arcs)}
        cross = []
        self.internal = {a: [] for a in range(self.g)}
        for (i, j) in self.arcs:
            if blob[i] == blob[j]:
                self.internal[blob[i]].append((i, j))
            else:
                cross.append((i, j))
        if rng is not None:
            rng.shuffle(cross)
        self.cross = cross
        self.m = len(cross)
        self.low = [(i, j) if blob[i] < blob[j] else (j, i) for (i, j) in cross]   # (s, t)
        self.ak = [blob[s] for s, t in self.low]
        self.bk = [blob[t] for s, t in self.low]
        self.delta = {a: [k for k in range(self.m) if self.ak[k] == a or self.bk[k] == a]
                      for a in range(self.g)}
        self.Eab = {}
        for a in range(self.g):
            for b in range(a + 1, self.g):
                self.Eab[(a, b)] = [k for k in range(self.m) if (self.ak[k], self.bk[k]) == (a, b)]
        self.V = {a: [v for v in range(n) if blob[v] == a] for a in range(self.g)}

    # signs: identical to proof_lib.Instance (they only use parities and chord positions)
    eps = Instance.eps
    sigma = Instance.sigma
    P = Instance.P

    def Gamma(self, a, lab_at):
        seq = []
        for k in self.delta[a]:
            i, j = self.cross[k]
            s, t = self.low[k]
            al, be = dpieces(self.Gn, i, j, s, t, lab_at[k], self.Y ** self.w[(i, j)])
            seq.append(al if self.ak[k] == a else be)
        return gprod(seq)

    def arc_factor(self, i, j):
        return gscale(gadd(ONE, gmul(self.Gn.pb(i), gadd(self.Gn.ps(i), self.Gn.ps(j), -1))),
                      self.Y ** self.w[(i, j)])

    def internal_choices(self, a):
        if not hasattr(self, "_ic"):
            self._ic = {}
        if a in self._ic:
            return self._ic[a]
        ints = self.internal[a]
        out = []
        for xs in itertools.product((0, 1), repeat=len(ints)):
            od = {v: 0 for v in self.V[a]}; idg = {v: 0 for v in self.V[a]}
            for x, (i, j) in zip(xs, ints):
                if x:
                    od[i] += 1; idg[j] += 1
            if any(d > 1 for d in od.values()) or any(d > 1 for d in idg.values()):
                continue
            F = gprod([self.arc_factor(i, j) for x, (i, j) in zip(xs, ints) if x])
            out.append((xs, od, idg, F))
        self._ic[a] = out
        return out

    def I(self, a, lab_at):
        od = {v: 0 for v in self.V[a]}; idg = {v: 0 for v in self.V[a]}
        for k in self.delta[a]:
            if lab_at[k] != "N":
                i, j = self.cross[k]
                if self.blob[i] == a:
                    od[i] += 1
                else:
                    idg[j] += 1
        if any(d > 1 for d in od.values()) or any(d > 1 for d in idg.values()):
            return 0
        Gam = self.Gamma(a, lab_at)
        if not Gam:
            return 0
        tot = 0
        for xs, od2, idg2, F in self.internal_choices(a):
            if all(od[v] + od2[v] == 1 and idg[v] + idg2[v] == 1 for v in self.V[a]):
                tot += self.Gn.top(gmul(F, Gam), self.V[a])
        return tot

    def mu(self):
        deg = [0] * self.n
        for i, j in self.arcs:
            deg[i] += 1; deg[j] += 1
        return max(sum(deg[v] for v in self.V[a]) for a in range(self.g))


# ----------------------------------------------------------------------------------------------
# the network of Definition 5.1 for an arbitrary label alphabet
# ----------------------------------------------------------------------------------------------
def width_base(base, e):
    w = 0
    while (1 << w) < base ** e:
        w += 1
    return w


class LabelNetwork:
    """Settings of node a: blocks (base-|labels| code of the labels on E(a,b), b != a, increasing
    b, w_ab bits each, lowest bit first) followed by the copy bits y_cd, (c,d) in Q_a.  Node
    function W_a = sigma_a chi_a I_a; edge function Psi_ab tests equal labels on E(a,b) and
    correct copies; c_ab = w_ab + (g - max(a,b) - 1) (0-based blob indices), f_ab = [pi_ab = theta]."""
    def __init__(self, inst, labels):
        self.inst = inst
        self.labels = tuple(labels)
        self.base = len(labels)
        self.kappa = {l: i for i, l in enumerate(self.labels)}
        self.g = g = inst.g
        self.e = {}; self.w = {}
        for a in range(g):
            for b in range(g):
                if a != b:
                    self.e[(a, b)] = len(inst.Eab[(min(a, b), max(a, b))])
                    self.w[(a, b)] = width_base(self.base, self.e[(a, b)])
        self.Q = {a: [(c, d) for c in range(a + 1, g) for d in range(c + 1, g)] for a in range(g)}
        self.layout = {}
        for a in range(g):
            pos = 0; lay = {}
            for b in range(g):
                if b != a:
                    lay[b] = (pos, self.w[(a, b)]); pos += self.w[(a, b)]
            lay["Q"] = (pos, len(self.Q[a]))
            self.layout[a] = lay
        self.Plen = {a: sum(w for (p, w) in self.layout[a].values()) for a in range(g)}
        self.c = {(a, b): self.w[(a, b)] + (g - 1 - max(a, b))
                  for a in range(g) for b in range(g) if a != b}
        self._Wcache = {}

    def encode(self, a, lab_at, y):
        bits = [0] * self.Plen[a]
        for b in range(self.g):
            if b == a:
                continue
            p, w = self.layout[a][b]
            ks = self.inst.Eab[(min(a, b), max(a, b))]
            val = sum(self.kappa[lab_at[k]] * self.base ** t for t, k in enumerate(ks))
            bits[p:p + w] = to_bits(val, w)
        p, w = self.layout[a]["Q"]
        bits[p:p + w] = [y[cd] for cd in self.Q[a]]
        return tuple(bits)

    def decode(self, a, z):
        if len(z) != self.Plen[a]:
            return None
        lab_at = {}
        for b in range(self.g):
            if b == a:
                continue
            p, w = self.layout[a][b]
            val = from_bits(z[p:p + w])
            ks = self.inst.Eab[(min(a, b), max(a, b))]
            if val >= self.base ** len(ks):
                return None
            for k in ks:
                lab_at[k] = self.labels[val % self.base]
                val //= self.base
        p, w = self.layout[a]["Q"]
        y = {cd: z[p + i] for i, cd in enumerate(self.Q[a])}
        return lab_at, y

    def settings(self, a):
        ks = self.inst.delta[a]
        for labs in itertools.product(self.labels, repeat=len(ks)):
            lab_at = dict(zip(ks, labs))
            for ys in itertools.product((0, 1), repeat=len(self.Q[a])):
                yield self.encode(a, lab_at, dict(zip(self.Q[a], ys)))

    def in_S(self, a, z):
        return self.decode(a, z) is not None

    def chi(self, a, lab_at, y):
        tot = 0
        for (c, d) in self.Q[a]:
            if y[(c, d)]:
                tot += sum(self.inst.P(a, b, lab_at) for b in range(c + 1, d))
        return -1 if tot & 1 else 1

    def W(self, a, z):
        if (a, z) in self._Wcache:
            return self._Wcache[(a, z)]
        lab_at, y = self.decode(a, z)
        val = self.inst.I(a, lab_at)
        if val:
            val *= self.inst.sigma(a, lab_at) * self.chi(a, lab_at, y)
        self._Wcache[(a, z)] = val
        return val

    def proj(self, a, b, z):
        lab_at, y = self.decode(a, z)
        p, w = self.layout[a][b]
        out = list(z[p:p + w])
        if a < b:
            out += [y[(b, d)] for d in range(b + 1, self.g)]
        else:
            out += [self.inst.P(a, d, lab_at) for d in range(a + 1, self.g)]
        return tuple(out)

    def f(self, a, b, z, theta):
        return 1 if self.proj(a, b, z) == tuple(theta) else 0

    def Psi(self, a, b, za, zb):
        if a > b:
            return self.Psi(b, a, zb, za)
        la, ya = self.decode(a, za)
        lb, yb = self.decode(b, zb)
        for k in self.inst.Eab[(a, b)]:
            if la[k] != lb[k]:
                return 0
        for d in range(b + 1, self.g):
            if ya[(b, d)] != self.inst.P(b, d, lb):
                return 0
        return 1

    def U(self):
        return sum(self.c.values())

    def max_table_bits(self):
        """max over nodes and settings of bit-length of |W_a|, and the bound mu."""
        mx = 0
        for a in range(self.g):
            for z in self.settings(a):
                mx = max(mx, abs(self.W(a, z)).bit_length())
        return mx


def random_groups(g, K, rng):
    """a random grouping of the g nodes into K nonempty groups (for eval_network_grouped)."""
    while True:
        gid = [rng.randrange(K) for _ in range(g)]
        if len(set(gid)) == K:
            break
    return [[a for a in range(g) if gid[a] == x] for x in range(K)]
