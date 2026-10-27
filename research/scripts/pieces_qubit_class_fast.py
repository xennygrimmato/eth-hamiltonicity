"""Faster version of pieces_qubit_class.py (same model), everything mod a 61-bit prime via flint."""
import sys, math
from flint import nmod_mat, nmod
P = (1 << 61) - 1
def lgC(n, k):
    return (math.lgamma(n+1)-math.lgamma(k+1)-math.lgamma(n-k+1))/math.log(2)

def setup(l, a1=1, b1=1, a2=1, b2=-3, dimE=(3,1), dimG=(1,3)):
    # E monomial X^{l-k}Y^k has weight C(l,k) dimE[0]^{l-k} dimE[1]^k ; G monomial X'^{l-j}Y'^j similarly
    f1 = [lgC(l,k) + (l-k)*math.log2(dimE[0]) + k*math.log2(dimE[1]) for k in range(l+1)]
    f2 = [lgC(l,j) + (l-j)*math.log2(dimG[0]) + j*math.log2(dimG[1]) for j in range(l+1)]
    # W[k][j] coefficient of X^{l-k}Y^k in (a1X+b1Y)^{l-j}(a2X+b2Y)^j  mod P
    W = [[0]*(l+1) for _ in range(l+1)]
    for j in range(l+1):
        p = [math.comb(l-j,i)*a1**(l-j-i)*b1**i for i in range(l-j+1)]
        q = [math.comb(j,i)*a2**(j-i)*b2**i for i in range(j+1)]
        for i,x in enumerate(p):
            for i2,y in enumerate(q):
                W[i+i2][j] = (W[i+i2][j] + x*y) % P
    return f1, f2, W

def feasible(l, B, f1, f2, W, Fv, tol=1e-9):
    thetas = sorted(set(f1))
    rows = []
    for th in thetas:
        S = set(k for k in range(l+1) if f1[k] <= th + tol)
        J = [j for j in range(l+1) if f2[j] <= B - th + tol]
        if not S or not J: continue
        Sc = [k for k in range(l+1) if k not in S]
        WJ = nmod_mat([[W[k][j] for j in J] for k in range(l+1)], P)
        if Sc:
            M = nmod_mat([[W[k][j] for j in J] for k in Sc], P)
            K, nul = M.nullspace()
            if nul == 0: continue
            U = WJ * K   # columns (first nul) span intersection
            for c in range(nul):
                rows.append([int(U[k,c]) for k in range(l+1)])
        else:
            for c in range(len(J)):
                rows.append([W[k][J[c]] for k in range(l+1)])
    if not rows: return False
    A = nmod_mat(rows, P)
    r1 = A.rank()
    A2 = nmod_mat(rows + [[x % P for x in Fv]], P)
    return A2.rank() == r1

def best(l, Fv=None, **kw):
    f1, f2, W = setup(l, **kw)
    if Fv is None: Fv = [math.comb(l,k)*(-1)**k for k in range(l+1)]
    lo, hi = 0.0, 4.0*l
    if not feasible(l, hi, f1, f2, W, Fv): return None
    for _ in range(30):
        mid = (lo+hi)/2
        if feasible(l, mid, f1, f2, W, Fv): hi = mid
        else: lo = mid
    return hi/(4*l)

if __name__ == "__main__":
    for l in [int(a) for a in sys.argv[1:]]:
        print(l, best(l), "  log12/4=", math.log2(12)/4, flush=True)
