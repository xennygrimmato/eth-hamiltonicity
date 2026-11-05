# Brute-force validation of the whole D.1-style pipeline for K_4 at N = 2, 4 (lam = 1, 2), A = 3, L = 8:
#  (i)  F(T) = clique sum with deformed edge matrices G_e(T); F(0) = Z (direct clique sum);
#  (ii) tapered Hermite recovery of F(0) mod 2^p from jets [F(t+alpha z)]_{<q_t} known only mod 2^{p_t}
#       (exact p_t of k4lib.hermite_precisions), with random perturbations by multiples of 2^{p_t};
#  (iii) at a node t, F(t+alpha*zeta) mod 2^{p} evaluated as a SIGNED NETWORK SUM with the two groups of
#       matching i merged: crossing edges replaced by their truncated 2-adic Smith pieces, merged tables
#       T_0[k], T_1[k] (k = 4-tuple of piece names with total valuation < p), pairing sum_k T_0[k]T_1[k].
import sys, random, math, itertools
from fractions import Fraction
import numpy as np
from k4lib import *

A = 3; K = Kernel(A); L = K.L; alpha = K.alpha
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
lam = int(sys.argv[1]) if len(sys.argv) > 1 else 1
N = 2 ** lam; M = 6 * lam; DEG = M * (2 * L - 1)
NODE_ORDER = ['a', 'b', 'c', 'd']
tabs = {u: np.array([random.randrange(4) for _ in range(N ** 3)], dtype=object).reshape(N, N, N) for u in NODE_ORDER}
# leg order of each table: its three edges in EDGES order
legs = {u: [e for e in EDGES if u in e] for u in NODE_ORDER}

def clique(Gs):
    """sum over copies: Z = sum prod_u W_u(x_u) prod_e G_e[x_e^u, x_e^v]; G_e indexed [u-copy, v-copy] for e=(u,v)"""
    # absorb each G_e into the table of its first endpoint u: W~_u(.., z_e, ..) = sum_x W_u(.., x, ..) G_e[x, z_e]
    Wt = {u: tabs[u] for u in NODE_ORDER}
    for e in EDGES:
        u = e[0]; ax = legs[u].index(e)
        G = np.array(Gs[e], dtype=object)
        Wt[u] = np.moveaxis(np.tensordot(Wt[u], G, axes=([ax], [0])), -1, ax)
    sub = {e: chr(ord('i') + k) for k, e in enumerate(EDGES)}
    spec = ','.join(''.join(sub[e] for e in legs[u]) for u in NODE_ORDER) + '->'
    return np.einsum(spec, *[Wt[u] for u in NODE_ORDER], optimize=False)

Z = clique({e: [[1 if x == y else 0 for y in range(N)] for x in range(N)] for e in EDGES})
print(f"lam={lam} N={N}: direct clique sum Z = {Z}")
# (i) F at integer points, scaled to integers: W * C'(0) is an integer polynomial
pts = list(range(1, DEG + 2))
vals = []
for T in pts:
    Gs = {e: edge_matrix(e, A, lam, Fraction(T), K) for e in EDGES}
    vals.append(Fraction(clique(Gs)))
assert clique({e: edge_matrix(e, A, lam, Fraction(0), K) for e in EDGES}) == Z
# Newton interpolation -> coefficients of F(T)
n = len(pts); dd = vals[:]
coef_newton = [dd[0]]
for k in range(1, n):
    dd = [(dd[j + 1] - dd[j]) / (pts[j + k] - pts[j]) for j in range(n - k)]
    coef_newton.append(dd[0])
# expand Newton form to monomial coefficients
poly = [Fraction(0)]
for k in reversed(range(n)):
    # poly = poly * (T - pts[k]) + coef_newton[k]
    newp = [Fraction(0)] * (len(poly) + 1)
    for j, c in enumerate(poly):
        newp[j + 1] += c; newp[j] -= c * pts[k]
    newp[0] += coef_newton[k]; poly = newp
while len(poly) > 1 and poly[-1] == 0: poly.pop()
print(f" F(T) recovered: degree {len(poly)-1} (bound M(2L-1) = {DEG}); F(0) == Z: {poly[0] == Z}")

def shift_jets(t, q):
    """coefficients of F(t + alpha z) in z, up to z^{q-1} (exact)"""
    out = []
    # F(t+alpha z) = sum_k poly_k (t + alpha z)^k
    for j in range(q):
        s = Fraction(0)
        for k in range(j, len(poly)):
            s += poly[k] * math.comb(k, j) * Fraction(t) ** (k - j)
        out.append(s * alpha ** j)
    return out

def hermite_recover(qlev, p, perturb=True):
    hp, Q = hermite_precisions(A, qlev, p)
    S = [t for t in range(-L, L) if t != 0]
    qq = {t: qlev.get(v2(t), 0) for t in S}
    total = Fraction(0)
    for t, (i, qt, vE, pt) in hp.items():
        jets = shift_jets(t, qt)
        assert all(v2q(c) >= 0 for c in jets)   # Lemma tensor-integrality
        if perturb:
            jets = [c + random.randrange(-50, 50) * Fraction(2) ** pt for c in jets]
        # E_t(t + alpha z) as power series, truncated at q_t
        E = [Fraction(1)] + [Fraction(0)] * (qt - 1)
        for s in S:
            if s == t or qq[s] == 0: continue
            fac = [Fraction(1), Fraction(alpha, t - s)]   # (t + alpha z - s)/(t - s) = 1 + alpha z/(t-s)
            for _ in range(qq[s]):
                E = [sum(E[j - k] * fac[k] for k in range(2) if j - k >= 0) for j in range(qt)]
        # 1/E truncated
        inv = [Fraction(1)] + [Fraction(0)] * (qt - 1)
        for j in range(1, qt):
            inv[j] = -sum(E[k] * inv[j - k] for k in range(1, j + 1))
        quo = [sum(jets[k] * inv[j - k] for k in range(j + 1)) for j in range(qt)]
        Et0 = Fraction(1)
        for s in S:
            if s == t or qq[s] == 0: continue
            Et0 *= Fraction(0 - s, t - s) ** qq[s]
        assert v2q(Et0) == vE
        total += Et0 * sum(quo[j] * Fraction(-t, alpha) ** j for j in range(qt))
    return total, Q

for name, qlev in [("D.1 taper q(i)=M(3-i)", {0: 3 * M, 1: 2 * M, 2: M}),
                   ("near-minimal uniform", {0: -(-(DEG + 1) // 14), 1: -(-(DEG + 1) // 14), 2: -(-(DEG + 1) // 14)})]:
    for p in (1, 8):
        exact, Q = hermite_recover(qlev, p, perturb=False)
        pert, _ = hermite_recover(qlev, p, perturb=True)
        ok = (exact == Z) and v2q(pert - Z) >= p
        print(f" Hermite [{name}] Sum q_t = {Q} > {len(poly)-1}: exact recovery {exact == Z}; with jets perturbed mod 2^p_t, "
              f"result = Z mod 2^{p}: {v2q(pert - Z) >= p}")

# (iii) signed-network-sum evaluation of F(t + alpha*zeta) at a node via truncated Smith pieces
def smith_pieces(Gm, P):
    MOD = 1 << P; Am = [list(r) for r in Gm]; nr = len(Am); nc = len(Am[0]); pcs = []
    while True:
        best = None
        for i in range(nr):
            for j in range(nc):
                x = Am[i][j] % MOD
                if x:
                    vv = (x & -x).bit_length() - 1
                    if best is None or vv < best[0]: best = (vv, i, j)
        if best is None: break
        vv, pi, pj = best; piv = Am[pi][pj]; oinv = pow(piv >> vv, -1, MOD)
        col = [Am[i][pj] >> vv for i in range(nr)]                         # integral
        row = [(Am[pi][j] * oinv) % MOD >> vv for j in range(nc)]           # integral (vals >= vv)
        # term = 2^vv * col (x) row
        pcs.append((vv, col, row))
        for i in range(nr):
            for j in range(nc):
                Am[i][j] = (Am[i][j] - (col[i] * row[j] << vv)) % MOD
    return pcs

P = 60
for t in (1, 2, 4):
    i = v2(t); g0, g1 = CUTS[i]; T = Fraction(t + alpha)
    Gs = {e: edge_matrix(e, A, lam, T, K, P=P) for e in EDGES}
    direct = clique(Gs) % (1 << P)
    cr = [e for e in EDGES if (e[0] in g0) != (e[1] in g0)]
    pcs = {e: smith_pieces(Gs[e], P) for e in cr}
    for p in (4, 8, 12, 16, 24):
        names = [k for k in itertools.product(*[range(len(pcs[e])) for e in cr]) if sum(pcs[e][kk][0] for e, kk in zip(cr, k)) < p]
        # merged tables: side g: sum over ports of its two tables, internal edge matrix, and its factor of each crossing piece
        def side_value(g, k, side_is_first):
            tot = 0
            inner = [e for e in EDGES if e[0] in g and e[1] in g][0]
            us = [u for u in NODE_ORDER if u in g]
            # enumerate all strings held by g's two tables: each table has 3 legs
            for xs in itertools.product(range(N), repeat=6):
                xu = dict(zip(us, [xs[0:3], xs[3:6]]))
                val = 1
                for u in us: val *= tabs[u][xu[u]]
                if val == 0: continue
                # internal edge e=(u,v): G_e[x_e^u, x_e^v]
                uu, vv_ = inner
                val *= Gs[inner][xu[uu][legs[uu].index(inner)]][xu[vv_][legs[vv_].index(inner)]]
                for e, kk in zip(cr, k):
                    w = e[0] if e[0] in g else e[1]
                    x = xu[w][legs[w].index(e)]
                    vvk, col, row = pcs[e][kk]
                    val *= (col[x] if w == e[0] else row[x])
                tot += val
            return tot
        s = 0
        for k in names:
            w = sum(pcs[e][kk][0] for e, kk in zip(cr, k))
            s += (side_value(g0, k, True) * side_value(g1, k, False)) << w
        ok = (s - direct) % (1 << p) == 0
        print(f" node t={t} (merge {sorted(g0)}|{sorted(g1)}), p={p:2d}: {len(names):5d} names (N^4={N**4}) ; "
              f"signed-network-sum value == F(t+alpha) mod 2^p: {ok}")
