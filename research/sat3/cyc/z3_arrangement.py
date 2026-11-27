"""An explicit subspace arrangement for Delta_3 with k = 2, w = 5, N = 10 (attains the Shannon bound w/k = 5/2).

Hubs A_i, B_j, C_k (i,j,k in Z_3), nodes (i,j,k) with i+j+k = 0, edges (i,j,k) -> (i+1,j+1,k+1).
Construction (cyclic-cap.md, section 3): K^10 = X + Y, X = W_(000), Y = W_(111), dim 5 each.
In X: V_A0 = <a,a'>, V_B0 = <b,b'>, V_C0 = <c,c'> with the single relation (a+a') + (b+b') + (c+c') = 0;
the same in Y with A1, B1, C1.  Then
   V_C2 = <a0 + b1', a1 + b0'>,  V_A2 = <b0 + c1, b1 + c0>,  V_B2 = <a0' + c1', a1' + c0'>.
Exact arithmetic over the rationals (fractions) -- ranks by Gaussian elimination.
"""
from fractions import Fraction as F
import itertools, random
random.seed(3)

def rank(rows):
    M = [list(map(F, r)) for r in rows]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        p = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        pv = M[rk][c]; M[rk] = [x/pv for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f*y for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk

def e(i, n=10): v = [0]*n; v[i] = 1; return v
add = lambda *vs: [sum(x) for x in zip(*vs)]
neg = lambda v: [-x for x in v]
scal = lambda s, v: [s*x for x in v]
# X = span(e0..e4): a0=e0, a0'=e1, b0=e2, b0'=e3, c0=e4, c0' = -(a0+a0'+b0+b0'+c0)
def block(off):
    a, a2, b, b2, c = (e(off+i) for i in range(5))
    c2 = neg(add(a, a2, b, b2, c))
    return a, a2, b, b2, c, c2
a0, a0p, b0, b0p, c0, c0p = block(0)
a1, a1p, b1, b1p, c1, c1p = block(5)
V = {('A', 0): [a0, a0p], ('B', 0): [b0, b0p], ('C', 0): [c0, c0p],
     ('A', 1): [a1, a1p], ('B', 1): [b1, b1p], ('C', 1): [c1, c1p],
     ('C', 2): [add(a0, b1p), add(a1, b0p)],
     ('A', 2): [add(b0, c1), add(b1, c0)],
     ('B', 2): [add(a0p, c1p), add(a1p, c0p)]}
nodes = [(i, j, (-i-j) % 3) for i in range(3) for j in range(3)]
W = {n: V[('A', n[0])] + V[('B', n[1])] + V[('C', n[2])] for n in nodes}
print("hub dims:", sorted(set(rank(v) for v in V.values())))
print("node dims:", [rank(W[n]) for n in nodes])
ok = True
for n in nodes:
    n2 = tuple((x+1) % 3 for x in n)
    r = rank(W[n] + W[n2]); ok &= (r == rank(W[n]) + rank(W[n2]))
    print("edge", n, "->", n2, " dim(W+W') =", r)
print("all nine edges have independent node spaces:", ok)
print("same-class hubs independent:", all(rank(V[(c, i)] + V[(c, j)]) == 4 for c in 'ABC' for i in range(3) for j in range(i)))
print("value sqrt(k/w) = sqrt(2/5) =", (2/5)**.5, " Gamma = 81 k/w =", 81*2/5)
