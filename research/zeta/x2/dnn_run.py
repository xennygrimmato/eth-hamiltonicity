import numpy as np, sys
from dnn_lp import solve
A=float(sys.argv[1]); hx=float(sys.argv[2]); c=float(sys.argv[3]) if len(sys.argv)>3 else 1.0
k,r,al,unk = solve(c=c, A=A, hx=hx)
print('c=%g A=%g hx=%g kappa*=%.5f simple>=%.5f'%(c,A,hx,k,2-k), flush=True)
S = np.where(al<=c, np.minimum(al,1), 0.0); S[unk]=r.x[1:]
np.savez('dnn_sol_A%g_c%g.npz'%(A,c), al=al, S=S, kappa=k)
