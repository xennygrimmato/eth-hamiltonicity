"""Exact (mod p) optimum of the S_lambda-symmetric Bell/Pauli class, compared with the generic-flag formula.
Per qubit: E-basis Bell projectors (rank 1), G-basis sigma_a (x) sigma_a (OSR 1); F = (II+XX+YY+ZZ)/2."""
import sys, math
from flint import nmod_mat
from collections import defaultdict
sys.path.insert(0, '.')
from pieces_bell_generic import comps, lmult, value
P = (1<<61)-1
S = [[1,1,1,1],[1,-1,1,-1],[-1,1,1,-1],[1,1,-1,-1]]   # S[a][b] = eigenvalue of sigma_a(x)sigma_a on Bell b

def polymul(p, q):
    r = defaultdict(int)
    for a,x in p.items():
        for b,y in q.items():
            r[tuple(i+j for i,j in zip(a,b))] = (r[tuple(i+j for i,j in zip(a,b))] + x*y) % P
    return r
def polypow(p, n):
    r = {(0,0,0,0):1}
    for _ in range(n): r = polymul(r, p)
    return r

def setup(l):
    types = list(comps(l,4)); idx = {t:i for i,t in enumerate(types)}
    n = len(types)
    # g_j (sum of Pauli strings of type j) = sum_k Wt[k][j] E_k ; Wt[k][j] = sum_{a of type j} prod s(a_t,b_t), b fixed of type k
    # = coeff of y^j in prod_t (sum_a s(a,b_t) y_a)
    lin = [{tuple(1 if i==a else 0 for i in range(4)): S[a][b] % P for a in range(4)} for b in range(4)]
    pw = [[polypow(lin[b], e) for e in range(l+1)] for b in range(4)]
    W = [[0]*n for _ in range(n)]
    for k in types:
        poly = {(0,0,0,0):1}
        for b in range(4): poly = polymul(poly, pw[b][k[b]])
        for j, c in poly.items():
            W[idx[k]][idx[j]] = c % P
    f = [lmult(t) for t in types]
    Fv = [(-1)**t[3] % P for t in types]
    return types, f, W, Fv

def feasible(B, f, W, Fv, tol=1e-9):
    n = len(f); rows = []
    for th in sorted(set(f)):
        Sset = set(i for i in range(n) if f[i] <= th+tol)
        J = [j for j in range(n) if f[j] <= B-th+tol]
        if not J: continue
        Sc = [k for k in range(n) if k not in Sset]
        if Sc:
            K, nul = nmod_mat([[W[k][j] for j in J] for k in Sc], P).nullspace()
            if nul == 0: continue
            U = nmod_mat([[W[k][j] for j in J] for k in range(n)], P) * K
            rows += [[int(U[k,c]) for k in range(n)] for c in range(nul)]
        else:
            rows += [[W[k][j] for k in range(n)] for j in J]
    if not rows: return False
    r1 = nmod_mat(rows, P).rank()
    return nmod_mat(rows+[Fv], P).rank() == r1

if __name__ == "__main__":
    for l in [int(a) for a in sys.argv[1:]]:
        types, f, W, Fv = setup(l)
        lo, hi = 0.0, 4.0*l
        for _ in range(25):
            mid = (lo+hi)/2
            if feasible(mid, f, W, Fv): hi = mid
            else: lo = mid
        print(l, "exact:", round(hi/(4*l),5), " generic formula:", round(value(l,[1]*4,[1]*4),5), flush=True)
