# Library: OpenAI D.1 (quantitative-contraction.tex) construction specialised to the K_4 clique sum.
# Dictionary (P3 of engine3-openai-route.md):
#   * the four tables a,b,c,d are the vertices of D.1's network (non-bipartite version: every table
#     holds row ports and column ports; A(Y)B(X) is replaced by prod_u W_u(ports of u));
#   * label coordinates = the three perfect matchings of K_4 (r = 2 symbols per coordinate):
#       coord 0: {a,b}|{c,d} (rows), coord 1: {a,c}|{b,d} (columns), coord 2: {a,d}|{b,c} (diagonals);
#     coordinates 3..A-1 (if A > 3) carry the same symbol 0 on every vertex (pure "copy" bits);
#   * one wire = one bit of an edge string; a packet = L = 2^A slots of ONE K_4 edge (each K_4 edge is
#     its own pair-label class); bit i of a slot = row symbol in coord i if the edge's endpoints differ
#     in coord i (orientation), copy bit otherwise (Lemma tensor-packets (2));
#   * Cauchy kernel W_xy(T) = C(T)/(C'(0)(T-(y-x))), S = [-L, L) (eq. tensor-cauchy), alpha = 2^(A+1);
#   * a node t != 0 with v2(t) = i < 3 is a merge along matching i.
from fractions import Fraction
import itertools

LABEL = {'a': (0, 0, 0), 'b': (0, 1, 1), 'c': (1, 0, 1), 'd': (1, 1, 0)}
EDGES = [('a', 'b'), ('a', 'c'), ('a', 'd'), ('b', 'c'), ('b', 'd'), ('c', 'd')]
CUTS = {0: ({'a', 'b'}, {'c', 'd'}), 1: ({'a', 'c'}, {'b', 'd'}), 2: ({'a', 'd'}, {'b', 'c'})}

def v2(n):
    n = int(n)
    if n == 0: return 10**9
    n = abs(n); c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

def v2q(q):
    q = Fraction(q)
    if q == 0: return 10**9
    return v2(q.numerator) - v2(q.denominator)

def lab(u, A):
    return LABEL[u] + (0,) * (A - 3)

def bit(x, i): return (x >> i) & 1

def edge_slots(e, A):
    """valid slots of a packet of edge e=(u,v): list of (slot, row_vertex, col_vertex)."""
    u, v = e; L = 2 ** A
    lu, lv = lab(u, A), lab(v, A)
    diff = [i for i in range(A) if lu[i] != lv[i]]
    out = []
    for x in range(L):
        for (r, c) in ((u, v), (v, u)):
            if all(bit(x, i) == lab(r, A)[i] for i in diff):
                out.append((x, r, c))
    return out

def real_slots(e, A, lam):
    """choose lam real slots, alternating orientation (u->v, v->u, ...)."""
    sl = edge_slots(e, A)
    f = [s for s in sl if s[1] == e[0]]; g = [s for s in sl if s[1] == e[1]]
    inter = [s for pair in itertools.zip_longest(f, g) for s in pair if s is not None]
    assert lam <= len(inter), (lam, len(inter))
    return inter[:lam]

class Kernel:
    def __init__(self, A):
        self.A = A; self.L = 2 ** A; self.alpha = 2 ** (A + 1)
        self.S = list(range(-self.L, self.L))
        c = Fraction(1)
        for s in self.S:
            if s != 0: c *= (0 - s)
        self.Cp0 = c
    def W(self, x, y, T):
        d = y - x; num = Fraction(1)
        for s in self.S:
            if s != d: num *= (T - s)
        return num / self.Cp0

def to_mod(q, P):
    q = Fraction(q); M = 1 << P
    assert v2q(q) >= 0 or q == 0, q
    num, den = q.numerator, q.denominator
    k = v2(den) if den != 1 else 0
    # q = num / (2^k * odd), v2(num) >= k
    num >>= k; odd = den >> k
    return (num * pow(odd, -1, M)) % M

def edge_matrix(e, A, lam, T, K=None, P=None):
    """G_e(T)[zu, zv]: deformed equality of edge e=(u,v) with lam wires in one packet.
    zu, zv in {0,1}^lam (bit s = that endpoint's port on real slot s). Entries Fractions (P None) or mod 2^P."""
    K = K or Kernel(A)
    rs = real_slots(e, A, lam)
    u, v = e
    Wm = [[K.W(x, y, T) for (y, _, _) in rs] for (x, _, _) in rs]
    if P is not None:
        Wm = [[to_mod(w, P) for w in row] for row in Wm]
        MOD = 1 << P
    n = 2 ** lam
    G = [[None] * n for _ in range(n)]
    for zu in range(n):
        for zv in range(n):
            Y = []; X = []
            for s, (x, r, c) in enumerate(rs):
                bu, bv = (zu >> s) & 1, (zv >> s) & 1
                Y.append(bu if r == u else bv)   # row port bit held by row vertex
                X.append(bv if r == u else bu)   # column port bit held by column vertex
            prod = 1 if P is not None else Fraction(1)
            for s in range(lam):
                z = sum(Wm[s][k] * X[k] for k in range(lam))
                f = z if Y[s] == 1 else 1 - z
                prod = prod * f
                if P is not None: prod %= MOD
            G[zu][zv] = prod
    return G

def smith_vals_mod(Mat, P):
    """2-adic Smith valuations of an integer matrix mod 2^P (entries ints in [0,2^P)). Invariants that are
    0 mod 2^P are reported as P (meaning >= P)."""
    MOD = 1 << P
    A = [list(r) for r in Mat]
    nr, nc = len(A), len(A[0])
    rows = list(range(nr)); cols = list(range(nc)); out = []
    while rows and cols:
        best = None
        for i in rows:
            Ai = A[i]
            for j in cols:
                x = Ai[j]
                if x:
                    vv = (x & -x).bit_length() - 1
                    if best is None or vv < best[0]:
                        best = (vv, i, j)
                        if vv == 0: break
            if best and best[0] == 0: break
        if best is None: break
        vv, pi, pj = best; out.append(vv)
        piv = A[pi][pj]; oinv = pow(piv >> vv, -1, MOD)
        prow = [(x * oinv) % MOD for x in A[pi]]
        rows.remove(pi); cols.remove(pj)
        for i in rows:
            f = A[i][pj]
            if f:
                f >>= vv
                Ai = A[i]
                for j in cols:
                    if prow[j]: Ai[j] = (Ai[j] - f * prow[j]) % MOD
                Ai[pj] = 0
    out += [P] * (min(nr, nc) - len(out))
    return sorted(out)

def hermite_precisions(A, qlev, p):
    """D.1 Lemma tapered-hermite with multiplicities q_t = qlev[v2(t)] (0 if missing).
    Returns dict t -> (level, q_t, v2(E_t(0)), exact precision p_t = p - min_{j<q_t} v2(E_t(0) (t/alpha)^j))."""
    L = 2 ** A; S = [t for t in range(-L, L) if t != 0]
    q = {t: qlev.get(v2(t), 0) for t in S}
    out = {}
    for t in S:
        if q[t] == 0: continue
        vE = sum(q[s] * (v2(s) - v2(t - s)) for s in S if s != t)
        i = v2(t)
        pt = p - vE + (q[t] - 1) * (A + 1 - i)
        out[t] = (i, q[t], vE, pt)
    return out, sum(q.values())
