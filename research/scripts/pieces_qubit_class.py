"""Exact optimum of rho within the 'qubit-symmetric' class of pieces.

Class: pieces T in the algebra  Sym^lambda( span{I, F_2} )  (operators on (C^2 (x) C^2)^{(x) lambda}
invariant under U(x)U conjugation on every bit, and under permutations of the bits).
Such T <-> binary form p(X,Y) of degree lambda:
   E-basis (P_sym, P_anti):   monomial X^{l-k} Y^k   <-> k antisym (dim 1), l-k sym (dim 3)
   realigned basis (Q, G):    monomial X'^{l-j}Y'^j  <-> j copies G (rank 3), l-j copies Q (rank 1)
   with X' = X+Y, Y' = X-3Y (up to scalars).  F = (X-Y)^l.
rank(T) = sum_{k in suppE} C(l,k) 3^{l-k},  OSR(T) = sum_{j in suppG} C(l,j) 3^j.
We find min B such that F in sum_theta ( V_{S_theta} cap W_{J_{B-theta}} ), and report rho = B/(4 l)
(B measured by log2 of the max-weight element of each support, i.e. up to an additive O(log l)).
"""
import sys, math
from flint import nmod_mat
P = (1 << 61) - 1

def lgC(n, k):
    return (math.lgamma(n+1)-math.lgamma(k+1)-math.lgamma(n-k+1))/math.log(2)

def setup(l):
    f1 = [lgC(l,k) + (l-k)*math.log2(3) for k in range(l+1)]   # rank cost of E_k
    f2 = [lgC(l,j) + j*math.log2(3) for j in range(l+1)]       # OSR cost of g_j
    # W columns: X'^{l-j} Y'^j expanded in X^{l-k}Y^k, X'=X+Y, Y'=X-3Y
    def polypow(a, b, n):  # (aX + bY)^n as list coeff of X^{n-k}Y^k
        c = [0]*(n+1)
        for k in range(n+1):
            c[k] = math.comb(n,k) * a**(n-k) * b**k
        return c
    def mul(p, q):
        r = [0]*(len(p)+len(q)-1)
        for i,x in enumerate(p):
            if x:
                for j,y in enumerate(q):
                    r[i+j] += x*y
        return r
    W = []
    for j in range(l+1):
        W.append(mul(polypow(1,1,l-j), polypow(1,-3,j)))
    Fv = [math.comb(l,k)*(-1)**k for k in range(l+1)]
    return f1, f2, W, Fv

def kernel_basis(M, rows, cols):
    # M: list of rows (python ints), return kernel vectors (length cols) mod P
    if rows == 0:
        return [[1 if i==j else 0 for i in range(cols)] for j in range(cols)]
    A = nmod_mat(rows, cols, [x % P for r in M for x in r], P)
    X, nullity = A.nullspace()
    return [[int(X[i,c]) for i in range(cols)] for c in range(nullity)]

def feasible(l, B, f1, f2, W, Fv, tol=1e-9):
    thetas = sorted(set(f1))
    vecs = []
    for th in thetas:
        S = [k for k in range(l+1) if f1[k] <= th + tol]
        J = [j for j in range(l+1) if f2[j] <= B - th + tol]
        if not S or not J: continue
        Sc = [k for k in range(l+1) if k not in set(S)]
        M = [[W[j][k] for j in J] for k in Sc]
        K = kernel_basis(M, len(Sc), len(J))
        for c in K:
            v = [0]*(l+1)
            for idx, j in enumerate(J):
                if c[idx]:
                    for k in range(l+1):
                        v[k] = (v[k] + c[idx]*W[j][k]) % P
            vecs.append(v)
    if not vecs: return False
    A = nmod_mat(len(vecs), l+1, [x for r in vecs for x in r], P)
    r1 = A.rank()
    A2 = nmod_mat(len(vecs)+1, l+1, [x for r in vecs for x in r] + [x % P for x in Fv], P)
    return A2.rank() == r1

def best(l):
    f1, f2, W, Fv = setup(l)
    lo, hi = 2.0*l, 4.0*l
    assert feasible(l, hi, f1, f2, W, Fv)
    for _ in range(40):
        mid = (lo+hi)/2
        if feasible(l, mid, f1, f2, W, Fv): hi = mid
        else: lo = mid
    return hi/(4*l)

if __name__ == "__main__":
    for l in [int(a) for a in sys.argv[1:]]:
        print(l, best(l), "  log12/4=", math.log2(12)/4, flush=True)
