"""Bell/Pauli S_lambda-symmetric class reduced by the global S_3 (WLOG pieces S_3-invariant, since the
cost = max over types is S_3-invariant and averaging over 6 group elements keeps it).
Compares the exact optimum (mod p) with the generic-flag formula computed over S_3-orbits."""
import sys, math
from flint import nmod_mat
sys.path.insert(0, '.')
from pieces_bell_exact import setup, P
from pieces_bell_generic import lmult
def reduce(l):
    types, f, W, Fv = setup(l)
    idx = {t:i for i,t in enumerate(types)}
    Eorb = {}; Gorb = {}
    for t in types:
        Eorb.setdefault(tuple(sorted(t[:3]))+(t[3],), []).append(t)
        Gorb.setdefault((t[0],)+tuple(sorted(t[1:])), []).append(t)
    EO = list(Eorb); GO = list(Gorb)
    Wr = [[sum(W[idx[Eorb[o][0]]][idx[j]] for j in Gorb[q]) % P for q in GO] for o in EO]
    fE = [lmult(Eorb[o][0]) for o in EO]; fG = [lmult(Gorb[q][0]) for q in GO]
    Fr = [Fv[idx[Eorb[o][0]]] for o in EO]
    return fE, fG, Wr, Fr
def feasible(B, fE, fG, W, Fv, tol=1e-9):
    n = len(fE); rows = []
    for th in sorted(set(fE)):
        S = set(i for i in range(n) if fE[i] <= th+tol)
        J = [j for j in range(len(fG)) if fG[j] <= B-th+tol]
        if not J: continue
        Sc = [k for k in range(n) if k not in S]
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
def solve(l):
    fE, fG, W, Fv = reduce(l)
    lo, hi = 0.0, 4.0*l
    for _ in range(25):
        mid = (lo+hi)/2
        if feasible(mid, fE, fG, W, Fv): hi = mid
        else: lo = mid
    q1 = sorted(fE); q2 = sorted(fG); n = len(q1)
    gen = max(q1[i]+q2[n-1-i] for i in range(n))/(4*l)
    return hi/(4*l), gen, n
if __name__ == "__main__":
    for l in [int(a) for a in sys.argv[1:]]:
        ex, gen, n = solve(l)
        print(l, "orbits", n, "exact", round(ex,5), "generic-over-orbits", round(gen,5), flush=True)
