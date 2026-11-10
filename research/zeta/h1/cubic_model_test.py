#!/usr/bin/env python3
"""Cubic rank-trace certificate in the N-periodic model (h3's model): G_jk = sqrt(psi_j psi_k) S(j-k), 0<=j,k<N, sum psi = 1.
Data (Diaconis-Shahshahani / Montgomery + Rudnick-Sarnak): E tr G = N, E tr G^2 = N^2 sum psi^2 + sum_{j!=k} psi_j psi_k |j-k|,
E tr G^3 = N^3 sum psi^3 + 3 N sum_{j!=l} psi_j^2 psi_l |j-l|.
Certificate f(x)=c1 x+c2 x^2+c3 x^3 from the scalar LP (cubic_scalar_lp.solve):  claim  s1 >= tr f(G) - c' N  for EVERY configuration.
Adversarial test: minimise  s1 - tr f(G) + c' N  over configurations with marks: simple, double, triple (on-line), off-line pairs (depth y).
Usage: cubic_model_test.py N a tries [mode]   (window psi_j ~ cos(a (j-(N-1)/2)/N))
"""
import sys, numpy as np
from scipy.optimize import minimize
sys.path.insert(0,'.')
from cubic_scalar_lp import solve
rng=np.random.default_rng(int(__import__('os').environ.get('SEED',3)))
def setup(N,a):
    j=np.arange(N); psi=np.cos(a*(j-(N-1)/2)/N); psi/=psi.sum()
    D=np.abs(j[:,None]-j[None,:])
    m2=(N*N*(psi**2).sum()+psi@D@psi)/N
    m3=(N**3*(psi**3).sum()+3*N*(psi**2)@D@psi)/N
    return psi,m2,m3
def G_of(N,psi,t,kind,y):
    l=np.arange(-(N-1),N)
    W=np.where((kind==3)[:,None],2*np.cosh(2*np.pi*np.outer(y,l)/N),kind[:,None].astype(float)*np.ones((1,len(l))))
    W=np.where((kind==4)[:,None],3.0,W)
    S=(W*np.exp(2j*np.pi*np.outer(t,l)/N)).sum(0)      # S(l), l=-(N-1)..N-1
    j=np.arange(N); sq=np.sqrt(psi)
    return sq[:,None]*sq[None,:]*S[(j[:,None]-j[None,:])+N-1]
def defect(N,psi,coef,cp,t,kind,y):
    lam=np.linalg.eigvalsh(G_of(N,psi,t,kind,y))
    return (kind==1).sum()-(coef[0]*lam+coef[1]*lam**2+coef[2]*lam**3).sum()+cp*N
if __name__=='__main__':
    N=int(sys.argv[1]); a=float(sys.argv[2]); tries=int(sys.argv[3]); mode=sys.argv[4] if len(sys.argv)>4 else 'unc'
    psi,m2,m3=setup(N,a); val,x=solve(m2,m3,'unc',True); coef=x[:3]; cp=x[4]
    print(f"N={N} a={a}: m2={m2:.5f} m3={m3:.5f} certificate value {val:.5f}; f coeffs {np.round(coef,4)} t={x[3]:.4f} c'={cp:.4f}")
    # sanity: CUE-like lattice and the extremal 2pt-type configs
    worst=(1e9,None)
    for it in range(tries):
        k2=rng.integers(0,N//2+1); k3=rng.integers(0,(N-2*k2)//2+1) if mode=='unc' else 0; rem=N-2*k2-2*k3
        k4=rng.integers(0,rem//3+1) if rng.random()<0.2 else 0; k1=rem-3*k4
        kind=np.array([1]*k1+[2]*k2+[3]*k3+[4]*k4); n=len(kind); isp=kind==3
        def fun(z):
            y=np.zeros(n); y[isp]=np.abs(z[n:]); return defect(N,psi,coef,cp,z[:n],kind,y)
        z0=np.concatenate([rng.uniform(0,N,n) if rng.random()<0.7 else (np.sort(rng.uniform(0,N,n))),np.abs(rng.exponential(0.15,k3))])
        r=minimize(fun,z0,method='L-BFGS-B',options={'maxiter':150})
        if r.fun<worst[0]:
            worst=(r.fun,(k1,k2,k3,k4,np.round(np.abs(r.x[n:]),3)))
            print(f"  try {it}: min defect {r.fun:.5f} (per N: {r.fun/N:.5f}) comp (k1,k2,k3pairs,k4triples,depths)={worst[1]}",flush=True)
    print("RESULT worst defect per N:",worst[0]/N,worst[1])
