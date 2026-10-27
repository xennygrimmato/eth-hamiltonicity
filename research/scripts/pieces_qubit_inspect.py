import sys, math
sys.path.insert(0, '.')
from pieces_qubit_class_fast import *
l = int(sys.argv[1]); rho = float(sys.argv[2]); B = 4*rho*l
f1, f2, W = setup(l)
tol=1e-9
for th in sorted(set(f1)):
    S = set(k for k in range(l+1) if f1[k] <= th + tol)
    J = [j for j in range(l+1) if f2[j] <= B - th + tol]
    if not S or not J: continue
    Sc = [k for k in range(l+1) if k not in S]
    M = nmod_mat([[W[k][j] for j in J] for k in Sc], P) if Sc else None
    nul = len(J) if not Sc else M.nullspace()[1]
    if nul:
        Ss = sorted(S); 
        # describe S as intervals
        iv=[]; st=Ss[0]; pr=Ss[0]
        for k in Ss[1:]:
            if k!=pr+1: iv.append((st,pr)); st=k
            pr=k
        iv.append((st,pr))
        print(f"theta/l={th/l:.3f} S={iv} J=[{min(J)},{max(J)}] |J|={len(J)} dim={nul}")
