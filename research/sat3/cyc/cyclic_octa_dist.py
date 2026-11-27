"""End-to-end check of Proposition 4.1 on sample edges: savings computed from the definition of the metric of the
filtration space (q1-notes section 1: d^2 = sum_{j,l} m(j,l) (s_j - s'_l)^2, m = second difference of
dim(V_j ^ V'_l)), with all dimensions by exact rank computations over F_q.  No use of Lemma 3.1 or of section 4.3."""
import sys, math, itertools
from cyclic_octa import setup, rho, rank_mod

def dim_int(U, V, q):  # dim(U ^ V) for row-spanned subspaces
    if not U or not V: return 0
    return rank_mod(U, q) + rank_mod(V, q) - rank_mod(U + V, q)
def dist2(F, G, q):
    # F, G: lists of (rows spanning V_j, level), increasing chains ending with the whole space
    d2 = 0.0
    for j in range(len(F)):
        for l in range(len(G)):
            m = dim_int(F[j][0], G[l][0], q)
            if j: m -= dim_int(F[j-1][0], G[l][0], q)
            if l: m -= dim_int(F[j][0], G[l-1][0], q)
            if j and l: m += dim_int(F[j-1][0], G[l-1][0], q)
            d2 += m*(F[j][1] - G[l][1])**2
    return d2
def complement(U, n, q):
    C = []; cur = [r[:] for r in U]; rk = rank_mod(cur, q)
    for i in range(n):
        e = [0]*n; e[i] = 1
        if rank_mod(cur + [e], q) > rk: cur.append(e); C.append(e); rk += 1
    return C
def basis(U, q):
    B = []
    for r in U:
        if rank_mod(B + [r], q) > len(B): B.append(r)
    return B

g = int(sys.argv[1]); par = tuple(map(int, sys.argv[2:6])) if len(sys.argv) > 5 else (1, 1, 2, 3)
q, w, pts, M = setup(g, *par)
n = 12; full = [[int(i == j) for j in range(n)] for i in range(n)]
VR0, VC0, VD0 = M[0:2], M[2:4], M[4:6]
hubR = lambda r: rho(VR0, (r % g, 0), pts, w, q)
hubC = lambda c: rho(VC0, (0, c % g), pts, w, q)
hubD = lambda d: rho(VD0, (d % g, 0), pts, w, q)
node = lambda r, c: (hubR(r), hubC(c), hubD(r + c))
W = lambda r, c: basis(sum(node(r, c), []), q)
hubF = lambda V: [(V, 1.0), (full, 0.0)]
T = 1e4
print("g = %d, F_%d; delta = %.6f (same-class hubs R_0, R_1)" % (g, q, math.sqrt(dist2(hubF(hubR(0)), hubF(hubR(1)), q))))
# non-collinear edges
for (t1, t2) in [(1, 1), (1, 2), (2, g-1) if g > 3 else (1, 1)]:
    if t1 % g == 0 or t2 % g == 0 or (t1+t2) % g == 0: continue
    Wn, Wm = W(0, 0), W(t1, t2)
    C = complement(Wn + Wm, n, q); a = 1/math.sqrt(10)
    x = [(Wn, T*a), (Wn + C, 0.0), (full, -T*a)]; y = [(Wm, T*a), (Wm + C, 0.0), (full, -T*a)]
    xy = math.sqrt(dist2(x, y, q))
    s = [xy - math.sqrt(dist2(x, hubF(h), q)) - math.sqrt(dist2(y, hubF(h2), q)) for h, h2 in zip(node(0, 0), node(t1, t2))]
    print("non-collinear edge (0,0)-(%d,%d): |xy| = %.4f (2T = %.0f), s/delta = %s  (sqrt(2/5) = %.6f)"
          % (t1, t2, xy, 2*T, [round(v/2, 5) for v in s], math.sqrt(0.4)))
# collinear edge sharing R_0: nodes (0,0), (0,t); k1 = class C
for t in (1, 2):
    V, V2 = hubC(0), hubC(t)
    Wn, Wm = W(0, 0), W(0, t)
    inner = basis(Wn + Wm, q)                       # V0 + V + V' + L + L'
    Mc = []
    for r in inner + full:                          # complement of V + V' containing a complement inside W_n + W_n'
        if rank_mod(V + V2 + Mc + [r], q) > 4 + len(Mc): Mc.append(r)
    # make sure M contains V_0 + L + L' modulo V + V': replace by a complement that contains the hub R_0
    Mc = []
    for r in hubR(0) + inner + full:
        if rank_mod(V + V2 + Mc + [r], q) > 4 + len(Mc): Mc.append(r)
    x = [(V, T/2), (V + Mc, 0.0), (full, -T/2)]; y = [(V2, T/2), (V2 + Mc, 0.0), (full, -T/2)]
    xy = math.sqrt(dist2(x, y, q))
    s = [xy - math.sqrt(dist2(x, hubF(h), q)) - math.sqrt(dist2(y, hubF(h2), q)) for h, h2 in zip(node(0, 0), node(0, t))]
    print("collinear edge (0,0)-(0,%d) (common hub R_0, k1 = C): s/delta for (R, C, D) = %s   (expected 0, 1, 0)" % (t, [round(v/2, 5) for v in s]))
