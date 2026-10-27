"""Generic blob-network engine for "local constraints x one Berezin (determinant) factor".

A *spec* describes a sum

    Z = sum_{s, sigma} prod_v C_v(s_v, sigma|delta(v)) * Berezin[ prod_v M_v(s_v) * prod_e F_e(s_u, s_v, sigma_e) ]

* s_v      : a local state of vertex v (e.g. y_v in S or not, a colour, a domination flag),
* sigma_e  : an edge state *visible to the constraints C* at both ends (e.g. x_e for degree tests),
* M_v      : an even Grassmann element in the generators of v (mass term, psibar_v psi_v for v
             outside S, ...),
* F_e      : an even Grassmann element in the generators of u and v; may contain scalar weights,
             including pairwise 0/1 constraints such as [y_u or y_v],
* Berezin  : coefficient of the top monomial prod_v psibar_v psi_v (ascending order), with
             generators deleted at "root" vertices (gens(v) False).

Blob decomposition (the network): every crossing edge e = (i in lower blob, j in higher blob) is
decomposed, for each sigma and each parity p, by an exact rank factorisation of the matrix
  rows (s_i, monomial of i of parity p)  x  cols (s_j, monomial of j of parity p)
into sum_t alpha_t(s_i) beta_t(s_j).  A crossing-edge label is (sigma, p, t); log2(#labels) is the
number of bits this edge costs on its blob pair.  Each blob table W_a sums its own states and
internal edges; the global value is
  Z = sum_labels eps(labels) prod_a W_a(labels at a),
with eps = sign of the permutation of odd pieces from edge order into blob order (computed
directly).  Everything is exact (int / Fraction).
"""
from fractions import Fraction
import itertools, math

# ------------------------------------------------------------------ Grassmann algebra
def gmul_mono(m1, m2):
    if m1 & m2:
        return None, 0
    s = 0
    x = m2
    while x:
        q = (x & -x).bit_length() - 1
        x &= x - 1
        s += bin(m1 >> (q + 1)).count("1")
    return m1 | m2, -1 if s & 1 else 1

def gmul(A, B):
    out = {}
    for m1, c1 in A.items():
        for m2, c2 in B.items():
            m, s = gmul_mono(m1, m2)
            if m is None:
                continue
            out[m] = out.get(m, 0) + s * c1 * c2
    return {m: c for m, c in out.items() if c}

def gadd(A, B, cb=1):
    out = dict(A)
    for m, c in B.items():
        out[m] = out.get(m, 0) + cb * c
    return {m: c for m, c in out.items() if c}

def gscale(A, c):
    return {m: v * c for m, v in A.items() if v * c}

def gexp(X):
    """exp of an even nilpotent element."""
    res = {0: 1}; term = {0: 1}; k = 1
    while True:
        term = gscale(gmul(term, X), Fraction(1, k))
        if not term:
            break
        res = gadd(res, term); k += 1
    return {m: (int(c) if Fraction(c).denominator == 1 else c) for m, c in res.items()}

ONE = {0: 1}
ZERO = {}

def popcount(x):
    return bin(x).count("1")

# ------------------------------------------------------------------ spec helpers
class Spec:
    """Subclass / fill: n, edges, vstates(v), estates(k), C(v,s,sig), M(v,s), F(k,su,sv,sig),
    gens(v)."""
    n = 0
    edges = []
    def vstates(self, v): return [0]
    def estates(self, k): return [0]
    def C(self, v, s, sig): return 1
    def M(self, v, s): return ONE
    def F(self, k, su, sv, sig): return ONE
    def gens(self, v): return True
    # generators
    def pb(self, v): return {1 << (2 * v): 1} if self.gens(v) else {}
    def ps(self, v): return {1 << (2 * v + 1): 1} if self.gens(v) else {}
    def pbps(self, v): return gmul(self.pb(v), self.ps(v)) if self.gens(v) else ONE
    def q_undirected(self, u, v):
        d1 = gadd(self.pb(u), self.pb(v), -1); d2 = gadd(self.ps(u), self.ps(v), -1)
        return gmul(d1, d2)
    def q_arc(self, u, v):  # arc u->v: psibar_u (psi_u - psi_v)  (L = D_out - A)
        return gmul(self.pb(u), gadd(self.ps(u), self.ps(v), -1))
    def incident(self, v):
        return [k for k, e in enumerate(self.edges) if v in e]

def monos(spec, v):
    if not spec.gens(v):
        return [0]
    a, b = 1 << (2 * v), 1 << (2 * v + 1)
    return [0, a, b, a | b]

# ------------------------------------------------------------------ exact rank factorisation
def rank_factor(M):
    """M (list of rows, Fractions/ints) = U V with U = columns of M at pivots, V = RREF rows."""
    R = [[Fraction(x) for x in row] for row in M]
    nr = len(R); nc = len(R[0]) if nr else 0
    piv = []; r = 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if R[i][c] != 0), None)
        if p is None:
            continue
        R[r], R[p] = R[p], R[r]
        pv = R[r][c]
        R[r] = [x / pv for x in R[r]]
        for i in range(nr):
            if i != r and R[i][c] != 0:
                f = R[i][c]
                R[i] = [x - f * y for x, y in zip(R[i], R[r])]
        piv.append(c); r += 1
        if r == nr:
            break
    U = [[M[i][c] for c in piv] for i in range(nr)]
    V = R[:len(piv)]
    return U, V

def decompose_edge(spec, k, i, j):
    """Labels for crossing edge k with i the lower-blob endpoint. Returns list of
    (sig, parity, alpha: s_i -> grassmann, beta: s_j -> grassmann)."""
    u, v = spec.edges[k]
    labels = []
    for sig in spec.estates(k):
        for p in (0, 1):
            rows = [(si, mL) for si in spec.vstates(i) for mL in monos(spec, i) if popcount(mL) % 2 == p]
            cols = [(sj, mR) for sj in spec.vstates(j) for mR in monos(spec, j) if popcount(mR) % 2 == p]
            if not rows or not cols:
                continue
            cache = {}
            def Fval(si, sj):
                key = (si, sj)
                if key not in cache:
                    su, sv = (si, sj) if i == u else (sj, si)
                    cache[key] = spec.F(k, su, sv, sig)
                return cache[key]
            M = []
            for (si, mL) in rows:
                row = []
                for (sj, mR) in cols:
                    m, sgn = gmul_mono(mL, mR)
                    row.append(Fval(si, sj).get(m, 0) * sgn)
                M.append(row)
            if all(x == 0 for row in M for x in row):
                continue
            U, V = rank_factor(M)
            for t in range(len(V)):
                al = {}
                for ri, (si, mL) in enumerate(rows):
                    if U[ri][t] != 0:
                        al.setdefault(si, {})[mL] = U[ri][t]
                be = {}
                for ci, (sj, mR) in enumerate(cols):
                    if V[t][ci] != 0:
                        be.setdefault(sj, {})[mR] = V[t][ci]
                labels.append((sig, p, al, be))
    return labels

# ------------------------------------------------------------------ the network
def build_network(spec, blob):
    K = max(blob) + 1
    n = spec.n
    cross, internal = [], {a: [] for a in range(K)}
    for k, (u, v) in enumerate(spec.edges):
        if blob[u] == blob[v]:
            internal[blob[u]].append(k)
        else:
            cross.append(k)
    lab = {}; low = {}
    for k in cross:
        u, v = spec.edges[k]
        i, j = (u, v) if blob[u] < blob[v] else (v, u)
        low[k] = (i, j)
        lab[k] = decompose_edge(spec, k, i, j)
    tables = {}
    for a in range(K):
        va = [v for v in range(n) if blob[v] == a]
        top = 0
        for v in va:
            if spec.gens(v):
                top |= (1 << (2 * v)) | (1 << (2 * v + 1))
        inc = [k for k in cross if a in (blob[spec.edges[k][0]], blob[spec.edges[k][1]])]
        ints = internal[a]
        tab = {}
        # enumerate local states and internal edge states once, then labels
        local_cfgs = []
        for ss in itertools.product(*[spec.vstates(v) for v in va]):
            sd = dict(zip(va, ss))
            Mprod = ONE
            for v in va:
                Mprod = gmul(Mprod, spec.M(v, sd[v]))
                if not Mprod:
                    break
            if not Mprod:
                continue
            for sigs in itertools.product(*[spec.estates(k) for k in ints]):
                sigd = dict(zip(ints, sigs))
                P = Mprod
                for k in ints:
                    u, v = spec.edges[k]
                    P = gmul(P, spec.F(k, sd[u], sd[v], sigd[k]))
                    if not P:
                        break
                if not P:
                    continue
                local_cfgs.append((sd, sigd, P))
        for labs in itertools.product(*[range(len(lab[k])) for k in inc]):
            ld = dict(zip(inc, labs))
            val = 0
            for sd, sigd, P in local_cfgs:
                sig_all = dict(sigd)
                for k in inc:
                    sig_all[k] = lab[k][ld[k]][0]
                w = 1
                for v in va:
                    w *= spec.C(v, sd[v], {k: sig_all[k] for k in spec.incident(v)})
                    if w == 0:
                        break
                if w == 0:
                    continue
                X = P
                for k in inc:
                    sig, p, al, be = lab[k][ld[k]]
                    i, j = low[k]
                    piece = al.get(sd[i], {}) if blob[i] == a else be.get(sd[j], {})
                    X = gmul(X, piece)
                    if not X:
                        break
                c = X.get(top, 0) if X else 0
                val += w * c
            if val != 0:
                tab[labs] = val
        tables[a] = (inc, tab)
    return dict(K=K, cross=cross, lab=lab, low=low, tables=tables, blob=blob)

def contract(net):
    K, cross, lab, tables, blob, low = (net[x] for x in ("K", "cross", "lab", "tables", "blob", "low"))
    pos = {k: t for t, k in enumerate(cross)}
    # pieces: position 2t (alpha, lower blob), 2t+1 (beta, higher blob)
    pb_ = []
    for k in cross:
        i, j = low[k]
        pb_ += [blob[i], blob[j]]
    npc = len(pb_)
    inv = [[1 if (p < q and pb_[p] > pb_[q]) else 0 for q in range(npc)] for p in range(npc)]
    # join tables
    partial = {(): 1}  # key: tuple of (k,label) sorted
    assigned = set()
    for a in range(K):
        inc, tab = tables[a]
        new = {}
        for key, val in partial.items():
            kd = dict(key)
            for labs, w in tab.items():
                ok = True
                for k, l in zip(inc, labs):
                    if k in kd and kd[k] != l:
                        ok = False; break
                if not ok:
                    continue
                nd = dict(kd); nd.update(zip(inc, labs))
                nk = tuple(sorted(nd.items()))
                new[nk] = new.get(nk, 0) + val * w
        partial = {k: v for k, v in new.items() if v != 0}
        assigned |= set(inc)
    Z = 0
    for key, val in partial.items():
        kd = dict(key)
        if len(kd) != len(cross):
            continue
        odd = []
        for k in cross:
            if lab[k][kd[k]][1] == 1:
                t = pos[k]; odd += [2 * t, 2 * t + 1]
        s = sum(inv[p][q] for p in odd for q in odd)
        Z += -val if s & 1 else val
    return Z

def network_value(spec, blob):
    net = build_network(spec, blob)
    Z = contract(net)
    bits = {k: len(net["lab"][k]) for k in net["cross"]}
    return Z, bits, net

# ------------------------------------------------------------------ exact utilities
def det_exact(M):
    N = len(M)
    if N == 0:
        return 1
    A = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for c in range(N):
        p = next((r for r in range(c, N) if A[r][c] != 0), None)
        if p is None:
            return 0
        if p != c:
            A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, N):
            if A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return d

def kron_decode(val, b, nterms):
    """balanced base-2^b digits of an integer (or Fraction with denominator 1)."""
    val = Fraction(val)
    assert val.denominator == 1, val
    val = int(val)
    B = 1 << b
    out = []
    for _ in range(nterms):
        d = val % B
        if d >= B // 2:
            d -= B
        out.append(d)
        val = (val - d) // B
    assert val == 0, "kronecker overflow"
    return out

def random_blobs(n, K, rng):
    while True:
        bl = [rng.randrange(K) for _ in range(n)]
        if len(set(bl)) == K:
            return bl

def crossing_ok(edges, blob, max_cross, max_inc):
    cr = [e for e in edges if blob[e[0]] != blob[e[1]]]
    K = max(blob) + 1
    inc = max(sum(1 for e in cr if blob[e[0]] == a or blob[e[1]] == a) for a in range(K))
    return len(cr) <= max_cross and inc <= max_inc
