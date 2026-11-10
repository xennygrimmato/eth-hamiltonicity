#!/usr/bin/env python3
"""Targeted adversarial test of the cubic certificate  s1 >= 2 tr G^2 - tr G^3  (x0=1 form) in the periodic model:
many off-line pairs, deep and clustered starts, depths kept >= ymin (so they cannot collapse to on-line doubles).
defect := s1 - 2 tr G^2 + tr G^3  must be >= 0.   Usage: N a tries ymin"""
import sys, numpy as np
from scipy.optimize import minimize
from cubic_model_test import setup, G_of
rng=np.random.default_rng(int(__import__('os').environ.get('SEED',11)))
N=int(sys.argv[1]); a=float(sys.argv[2]); tries=int(sys.argv[3]); ymin=float(sys.argv[4])
psi,m2,m3=setup(N,a)
print(f"N={N} a={a} value 2m2-m3 = {2*m2-m3:.5f}; ymin={ymin}")
def defect(t,kind,y):
    lam=np.linalg.eigvalsh(G_of(N,psi,t,kind,y)); return (kind==1).sum()-2*(lam**2).sum()+(lam**3).sum()
worst=1e9
for it in range(tries):
    k3=rng.integers(1,N//2+1); k2=rng.integers(0,(N-2*k3)//2+1) if rng.random()<0.5 else 0; k1=N-2*k3-2*k2
    kind=np.array([1]*k1+[2]*k2+[3]*k3); n=len(kind); isp=kind==3
    def fun(z):
        y=np.zeros(n); y[isp]=ymin+np.abs(z[n:]); return defect(z[:n],kind,y)
    style=rng.integers(0,3)
    t0=rng.uniform(0,N,n) if style==0 else (rng.uniform(0,N)+rng.normal(0,0.5,n) if style==1 else np.sort(rng.uniform(0,N,n)))
    z0=np.concatenate([t0,np.abs(rng.exponential(rng.choice([0.05,0.3,1.0]),k3))])
    r=minimize(fun,z0,method='L-BFGS-B',options={'maxiter':200})
    if r.fun<worst:
        worst=r.fun; print(f" try {it}: defect {r.fun:.5f} ({r.fun/N:.5f}/N) k1,k2,pairs={k1,k2,k3} depths-ymin={np.round(np.abs(r.x[n:]),3)}",flush=True)
print("RESULT worst defect/N",worst/N)
