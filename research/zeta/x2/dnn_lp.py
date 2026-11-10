"""Idea 1 / DNN relaxation.
Stationary point process on R, density 1 counted with multiplicity.
kappa = E sum_{x_j in [0,1]} m_j^2 (atom of reduced 2nd moment at 0).
S(alpha) = kappa + FT(R2-1)(alpha), R2 = off-diagonal pair density >= 0.
Known: S(alpha)=|alpha| on [0,c] (Montgomery F with support c; GUE for 1<|alpha|<=c means min(|a|,1)).
Maximise kappa subject to S>=0, R2>=0.  simple fraction >= 2-kappa (sharp when only m in {1,2}).
"""
import numpy as np, sys
from scipy.optimize import linprog
def solve(c=1.0, A=8.0, h=0.01, X=25.0, hx=0.01, target=lambda a: np.minimum(np.abs(a),1.0)):
    al = np.arange(0, A+h/2, h); w = np.full(al.size, h); w[0]=w[-1]=h/2
    known = al <= c+1e-12; unk = ~known
    xs = np.arange(0, X+hx/2, hx)
    C = 2*np.cos(2*np.pi*np.outer(xs, al))*w   # R2(x) = 1 + C@(S-kappa)
    # variables: [kappa, S_unk...]
    nu = unk.sum()
    # R2 = 1 + C[:,known]@T_known + C[:,unk]@S_unk - kappa*C.sum(1) >= 0
    Tk = target(al[known])
    A_ub = np.hstack([ (C.sum(1))[:,None], -C[:,unk] ])
    b_ub = 1 + C[:,known]@Tk
    cost = np.zeros(1+nu); cost[0] = -1
    bounds = [(0,None)]+[(0,None)]*nu
    r = linprog(cost, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    return r.x[0], r, al, unk
if __name__=='__main__':
    for A in [4,8,12]:
        k,r,al,unk = solve(c=1.0, A=A)
        print('c=1 A=%g kappa*=%.5f simple>=%.5f'%(A,k,2-k))
