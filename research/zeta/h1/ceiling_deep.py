#!/usr/bin/env python3
"""h1: three-point ceiling with off-line pairs of depth <= YMAX, numerically stable version.
Same model/rows as ceiling_npoint.py (level 2: 2-pt rows; level 3: + bispectrum rows a+b<=N-1).
Stabilisation: every column is rescaled by s = max(1, ||f/scale||_inf); LP variable is w*s, so a deep column has
cost c/s, mass 1/s and O(1) features: as s -> infinity it becomes a RAY (zero cost, zero mass) of the feature cone.
Pairs are parametrised by y = YMAX * sin^2(z) (bounded).  Pricing minimises (reduced cost)/s.
Usage: ceiling_deep.py N level YMAX iters tries        env SEED"""
import sys, os, numpy as np
from scipy.optimize import linprog, minimize
rng=np.random.default_rng(int(os.environ.get('SEED',7)))
N=int(sys.argv[1]); level=int(sys.argv[2]); YMAX=float(sys.argv[3]); iters=int(sys.argv[4]); tries=int(sys.argv[5])
R=[('2',l) for l in range(1,N)]
if level>=3: R+=[('3',a,b) for a in range(1,N) for b in range(a,N) if a+b<=N-1]
tg=np.array([float(r[1]) if r[0]=='2' else 0.0 for r in R]); scale=np.array([max(float(r[1]),1.0) if r[0]=='2' else float(N) for r in R])
i2=np.array([r[1] for r in R if r[0]=='2']); A3=np.array([r[1] for r in R if r[0]=='3'],int); B3=np.array([r[2] for r in R if r[0]=='3'],int)
l=np.arange(0,N)
def feats(t,m,y):
    W=np.where((y>0)[:,None],2*np.cosh(2*np.pi*np.outer(y,l)/N),m[:,None]*np.ones((1,N)))
    S=(W*np.exp(2j*np.pi*np.outer(t,l)/N)).sum(0)
    f2=np.abs(S[i2])**2
    if level>=3: return np.concatenate([f2,(S[A3]*S[B3]*np.conj(S[A3+B3])).real])/scale
    return f2/scale
def cue():
    Z=(rng.normal(size=(N,N))+1j*rng.normal(size=(N,N)))/np.sqrt(2); Q,Rr=np.linalg.qr(Z); Q=Q*(np.diag(Rr)/abs(np.diag(Rr)))
    return np.angle(np.linalg.eigvals(Q))*N/(2*np.pi)
cols=[]   # (cost, f, s, info)
def add(cost,f,info):
    s=max(1.0,np.abs(f).max()); cols.append((cost/s,f/s,1.0/s,info))
for _ in range(3000): add(1.0,feats(cue(),np.ones(N),np.zeros(N)),(N,0,0,0.0))
for _ in range(400):
    k2=rng.integers(0,N//2+1); k1=N-2*k2; m=np.array([1.0]*k1+[2.0]*k2); add(k1/N,feats(rng.uniform(0,N,len(m)),m,np.zeros(len(m))),(k1,k2,0,0.0))
nr=len(R); BIG=50.0; tgs=tg/scale
for it in range(iters):
    C=np.array([c[0] for c in cols]); F=np.array([c[1] for c in cols]).T; M=np.array([c[2] for c in cols]); mc=len(cols)
    Aeq=np.zeros((nr+1,mc+2*nr)); Aeq[0,:mc]=M; Aeq[1:,:mc]=F; Aeq[1:,mc:mc+nr]=np.eye(nr); Aeq[1:,mc+nr:]=-np.eye(nr)
    res=linprog(np.concatenate([C,BIG*np.ones(2*nr)]),A_eq=Aeq,b_eq=np.concatenate([[1.0],tgs]),bounds=(0,None),method='highs')
    if res.x is None: print("LP failed:",res.message); break
    c0,lam=res.eqlin.marginals[0],res.eqlin.marginals[1:]; slack=res.x[mc:].sum(); new=[]
    for _ in range(tries):
        u=rng.random()
        k3=0 if u<0.2 else rng.integers(1,N//2+1); k2=rng.integers(0,(N-2*k3)//2+1) if rng.random()<0.6 else 0; k1=N-2*k2-2*k3
        m=np.array([1.0]*k1+[2.0]*(k2+k3)); n=len(m); isp=np.arange(n)>=k1+k2
        def f(z):
            y=np.zeros(n); y[isp]=YMAX*np.sin(z[n:])**2; ft=feats(z[:n],m,y); s=max(1.0,np.abs(ft).max()); return (k1/N-c0-lam@ft)/s
        st=rng.integers(0,3); t0=rng.uniform(0,N,n) if st==0 else (rng.uniform(0,N)+rng.normal(0,rng.choice([0.3,1.0]),n) if st==1 else np.arange(n)*N/n+rng.normal(0,0.1,n))
        z0=np.concatenate([t0,rng.uniform(0,np.pi/2,k3)])
        r=minimize(f,z0,method='L-BFGS-B',options={'maxiter':80})
        if r.fun<-1e-8:
            y=np.zeros(n); y[isp]=YMAX*np.sin(r.x[n:])**2; new.append((r.fun,k1,k2,k3,r.x[:n],m,y))
    new.sort(key=lambda z:z[0])
    print(f"it {it:3d} obj {res.fun:.6f} slack {slack:.1e} ncols {mc} newneg {len(new)} best {new[0][0] if new else 0:.1e}",flush=True)
    if not new and slack<1e-9: break
    for (_,k1,k2,k3,t,m,y) in new[:40]: add(k1/N,feats(t,m,y),(k1,k2,k3,round(float(y.max()),2),np.round(np.sort(t%N),2).tolist(),np.round(y,2).tolist()))
x=res.x[:len(cols)]
print("support columns with pairs (mass weight w = x/s, scaled weight x, info):")
tot=0
for i in np.argsort(-x):
    if x[i]>1e-9 and cols[i][3][2]>0:
        w=x[i]*cols[i][2]; tot+=w; print(f"   mass {w:.3e} scaled {x[i]:.3e} cost*N {cols[i][0]/cols[i][2]*N:.0f} {cols[i][3]}")
print(f"total mass on pair configs {tot:.4e}")
print(f"RESULT N={N} level={level} YMAX={YMAX}: value {res.fun:.6f} slack {slack:.1e}")
np.save(f"dual_N{N}_L{level}_Y{YMAX}.npy",np.concatenate([[c0],lam]))
