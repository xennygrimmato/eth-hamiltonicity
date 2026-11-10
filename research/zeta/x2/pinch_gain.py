"""Lead task (3): rigorous coupling via h1's Theorem A.1 + pinching (Lemma A.2):
N0s >= (2-R(psi))N + sum_{spec Gamma} phi(lam-1) - o(N), and a block of two simple on-line zeros at distance d contributes
phi(k)+phi(-k) = 2 k^2, k = kappa_psi(d) = int psi(u) cos(2 pi d u) du / int psi  (u in [-1/2,1/2], d in mean spacings).
If c*N consecutive gaps between simple on-line zeros are <= lam (positive length), choose every other one: >= cN/2 disjoint pairs
=> gain >= c * min_{0<d<=lam} kappa(d)^2.  Optimise psi jointly: maximise 2 - R(psi) + c*min_{d<=lam} kappa(d)^2."""
import numpy as np
from scipy.optimize import minimize
u=np.linspace(-0.5,0.5,401); du=u[1]-u[0]
def R(psi):
    I=psi.sum()*du; A=(psi**2).sum()*du; B=(np.abs(u[:,None]-u[None,:])*np.outer(psi,psi)).sum()*du*du
    return (A+B)/I**2
def kap(psi,d): return (psi*np.cos(2*np.pi*d*u)).sum()/psi.sum()
psiMT=np.cos(np.sqrt(2)*u*1.0)  # test; find best c0 for cos(c0 u)
best=min(((R(np.cos(c0*u)),c0) for c0 in np.linspace(0.1,6,600)))
print('best cos(c u): R=%.6f at c=%.3f  -> 2-R=%.6f'%(best[0],best[1],2-best[0]))
psi=np.cos(best[1]*u)
for d in [0.3,0.5,0.7,0.9]: print('kappa_MT(%.1f)=%.4f  kappa^2=%.4f'%(d,kap(psi,d),kap(psi,d)**2))
# joint optimisation with even cosine-series psi >= 0 parametrisation
def obj(c,lam,coef):
    p=np.cos(best[1]*u)+sum(a*np.cos(2*np.pi*(j+1)*u) for j,a in enumerate(coef))
    if p.min()<0: return 10
    ds=np.linspace(1e-3,lam,30); m=min(kap(p,d)**2 for d in ds)
    return -(2-R(p)+c*m)
print('rigorous bound 2-R+c*min kappa^2 (MT window | optimised window):')
for lam in [0.3,0.5,0.7,0.9]:
    row=[]
    for c in [0.01,0.02,0.05,0.10]:
        mt=-obj(c,lam,[]); r=minimize(lambda x:obj(c,lam,x),np.zeros(4),method='Nelder-Mead',options={'maxiter':2000,'xatol':1e-6,'fatol':1e-9})
        row.append('c=%.2f: %.4f | %.4f'%(c,mt,-r.fun))
    print('lam=%.1f  '%lam+'   '.join(row))
