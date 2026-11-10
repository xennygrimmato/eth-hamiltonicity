#!/usr/bin/env python3
"""Rank-trace certificate 2 - R as a function of bandwidth c.
R(psi) = [ int psi^2 + iint Fhat(u-v) psi(u)psi(v) ] / (int psi)^2, psi even >=0 on [-c/2,c/2],
Fhat(a) = form-factor datum: |a| for |a|<=1; for 1<|a|<=c either 1 (truth / GRH family asymptotics)
or kappa*|a| (large-sieve upper bound).  Flat window closed forms and optimal window (discretised QP).
"""
import numpy as np
def Rflat(c,mode,kappa=1.0):
    if c<=1: return 1/c+c/3
    if mode=='truth': return 1+1/(3*c*c)
    return kappa*c/3+(2-kappa)/c-(2/3)*(1-kappa)/c**2
def Ropt(c,mode,kappa=1.0,n=1200):
    h=c/n; u=(np.arange(n)+.5)*h-c/2
    D=np.abs(u[:,None]-u[None,:])
    if mode=='truth': K=np.minimum(D,1.0)
    else: K=np.where(D<=1,D,kappa*D)
    A=np.eye(n)/h+K            # quadratic form  h^2 * psi^T A psi  (delta part: h*sum psi^2)
    x=np.linalg.solve(A,np.ones(n)); 
    R=1.0/(h*h*np.ones(n)@x)/ (1/h**2) if False else 1.0/(np.ones(n)@x)   # min psi^T A psi h^2 s.t. h*sum psi=1  -> 1/(1^T A^-1 1)
    return R, x.min()>=-1e-9
if __name__=='__main__':
    print("check c=1: flat",Rflat(1,'truth'),"opt",Ropt(1,'truth')[0],"MT exact",0.5+np.sqrt(.5)/np.tan(np.sqrt(.5)))
    print(" c    truth:flat  opt  simple(opt) distinct(opt) | LS k=1: flat opt simple | LS k=1.263: flat opt simple  (psi>=0?)")
    for c in [1,1.1,1.2,1.3,1.4,1.5,1.6,1.7321,1.8,1.9,2.0]:
        a=Rflat(c,'truth');b,p1=Ropt(c,'truth');d=Rflat(c,'ls',1);e,p2=Ropt(c,'ls',1);f=Rflat(c,'ls',1.263);g,p3=Ropt(c,'ls',1.263)
        print(f"{c:5.3f} {a:.4f} {b:.4f} {2-b:.4f} {(3-b)/2:.4f} | {d:.4f} {e:.4f} {2-e:.4f} | {f:.4f} {g:.4f} {2-g:.4f}  {p1,p2,p3}")
    for kap in [1.0,1.1,1.263,1.5]:
        best=max((2-Ropt(c,'ls',kap,600)[0],c) for c in np.linspace(1,2,41))
        print("kappa",kap,"best simple, c:",best, " distinct:",(1+best[0])/2)
