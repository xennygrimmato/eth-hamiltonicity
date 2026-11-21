#!/usr/bin/env python3
"""Zeta zeros 0<gamma<=TMAX: locate by Riemann-Siegel Z(t) (numpy, C0 term) sign changes on a grid,
bisect, then polish with mpmath.siegelz (secant). Check count against N(T) (Backlund). Output zeros.npy."""
import numpy as np, mpmath, sys, time
from multiprocessing import Pool
TMAX=float(sys.argv[1]) if len(sys.argv)>1 else 12000.0
def theta(t):
    return t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)+7/(5760*t**3)
def Z(t):
    t=np.asarray(t,float); a=np.sqrt(t/(2*np.pi)); N=np.floor(a).astype(int); p=a-N
    out=np.zeros_like(t); th=theta(t)
    for n in range(1,int(N.max())+1):
        m=N>=n
        out[m]+=2*np.cos(th[m]-t[m]*np.log(n))/np.sqrt(n)
    d=np.cos(2*np.pi*p); d=np.where(np.abs(d)<1e-9,1e-9,d)
    C0=np.cos(2*np.pi*(p*p-p-1/16))/d
    return out+(-1.0)**(N-1)*a**-0.5*C0
def polish(t0):
    mpmath.mp.dps=20
    try:
        r=mpmath.findroot(mpmath.siegelz,(t0-2e-3,t0+2e-3),solver='secant',tol=1e-12,maxsteps=20)
        r=float(r)
        return r if abs(r-t0)<0.05 else float('nan')
    except Exception: return float('nan')
if __name__=="__main__":
    t0=time.time()
    lo_list=[]
    for a in np.arange(14.0,TMAX,500.0):
        g=np.arange(a,min(a+500.0,TMAX)+0.004,0.004); z=Z(g)
        i=np.nonzero(z[:-1]*z[1:]<0)[0]
        lo,hi=g[i].copy(),g[i+1].copy(); zl=z[i]
        for _ in range(12):
            mid=(lo+hi)/2; zm=Z(mid); s=zl*zm>0
            lo=np.where(s,mid,lo); hi=np.where(s,hi,mid); zl=np.where(s,zm,zl)
        lo_list.append((lo+hi)/2)
    cand=np.concatenate(lo_list)
    print("candidates",len(cand),time.time()-t0,flush=True)
    with Pool(4) as P: zs=np.array(P.map(polish,cand,chunksize=64))
    bad=np.isnan(zs); print("polish failures",bad.sum())
    zs=np.where(bad,cand,zs); zs=np.unique(np.round(zs,10))
    T=zs[-1]+1e-6
    NT=T/(2*np.pi)*np.log(T/(2*np.pi*np.e))+7/8
    print("zeros",len(zs),"last",zs[-1],"N(T) smooth",NT,"time",time.time()-t0)
    print("first",zs[:3],"min gap",np.diff(zs).min())
    np.save("zeros.npy",zs)
