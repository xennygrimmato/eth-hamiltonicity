#!/usr/bin/env python3
"""m4: zeta'-weighted ("TW") two-point rows in the N-periodic certificate LP, with depth-robust column scaling.
Model (h3/h4): N-periodic configurations, total multiplicity N: k1 simple on-line, k2 double on-line, k3 off-line pairs t+-iy.
Rows (expectations over the law):
  pair  P_l = |S(l)|^2, S(l)=sum_rho m_rho e(l tau_rho/N), 1<=l<=N-1      target l (CUE exact)  [bandwidth-one data]
  TW    V_j = |sum_rho a_rho e(j tau_rho/N)|^2 , j in JSET                target: CUE Monte Carlo
     WT=z : a_rho = Z'(tau_rho)/c_N, Z(t)=prod 2 sin(pi(t-tau)/N)  (Hardy-Z frame; easy range |j|<=N/2 <-> x in [1,T])
     WT=m : a_rho = zeta'B analogue g_rho*B(z_rho), B=sum_{k<=K} c_k h_k z^-k (h4/tw_moll.py; c = RH-optimal mollifier)
All rows are analytic in the zeros AND Hermitian squares (both for on-line and conjugation-symmetric configurations).
SIDE=eq : rows = targets (pair rows exact, TW rows +-TOL relative);  SIDE=le : every row <= (1+DELTA)*target (one-sided).
Depth: y = YMAX*sin^2(z); every column is rescaled by s=max(1,||f/scale||_inf) (h1/ceiling_deep.py), so deep columns become rays.
Value = E[#simple]/N of the best law found = upper estimate of the ceiling (pricing heuristic).
Usage: tw_lp.py N mode(rh|unc) WT(z|m|none) [iters tries]   env: JMIN JMAX K YMAX SIDE TOL DELTA SEED
"""
import sys, os, numpy as np
from scipy.optimize import linprog, minimize
from scipy.stats import unitary_group
E=os.environ.get
N=int(sys.argv[1]); MODE=sys.argv[2]; WT=sys.argv[3]
iters=int(sys.argv[4]) if len(sys.argv)>4 else 80; tries=int(sys.argv[5]) if len(sys.argv)>5 else 12
YMAX=float(E('YMAX',1.0)); SIDE=E('SIDE','eq'); TOL=float(E('TOL',0.02)); DELTA=float(E('DELTA',0.0)); K=int(E('K',max(1,N//2-1)))
rng=np.random.default_rng(int(E('SEED',7)))
JSET=np.arange(int(E('JMIN',-(N//2) if WT=='z' else 0)),int(E('JMAX',N//2 if WT=='z' else N))+1)
lp=np.arange(1,int(E("LPMAX",N-1))+1)   # pair rows l=1..LPMAX (default N-1 = bandwidth one; LPMAX=N adds the alpha=1 row)

def weights_z(taus,mult,cN):
    d=taus[:,None]-taus[None,:]; s=2*np.sin(np.pi*d/N); np.fill_diagonal(s,1.0); s=s**mult[None,:]
    a=(2*np.pi/N)*np.prod(s,axis=1)/cN; return np.where(mult==1,a,0.0)
def Fmat(taus,mult):
    z=np.exp(2j*np.pi*taus/N); zz=np.repeat(z,mult.astype(int)); e=np.poly(zz)
    h=np.zeros(K+1,complex); h[0]=1
    for k in range(1,K+1): h[k]=-sum(e[j]*h[k-j] for j in range(1,min(k,len(e)-1)+1))
    r=1-z[None,:]/z[:,None]; np.fill_diagonal(r,1.0); r=r**mult[None,:]
    g=np.where(mult==1,np.prod(r,axis=1),0.0)
    return g[None,:]*h[:,None]*z[None,:]**(-np.arange(K+1)[:,None])
CM=None; cN=1.0
def feats(taus,mult):
    S=(mult[:,None]*np.exp(2j*np.pi*np.outer(taus,lp)/N)).sum(0); out=[np.abs(S)**2]
    if WT!='none':
        a=weights_z(taus,mult,cN) if WT=='z' else CM.conj()@Fmat(taus,mult)
        T=(a[:,None]*np.exp(2j*np.pi*np.outer(taus,JSET)/N)).sum(0); out.append(np.abs(T)**2)
    return np.concatenate(out)
def build(k1,k2,k3,t,y):
    taus=np.concatenate([t[:k1+k2].astype(complex),t[k1+k2:]+1j*y,t[k1+k2:]-1j*y])
    mult=np.concatenate([np.ones(k1),2*np.ones(k2),np.ones(2*k3)]); return taus,mult
# CUE targets
M=int(E('MC',40000)); ts=np.angle(np.linalg.eigvals(unitary_group.rvs(N,size=M,random_state=3)))*N/(2*np.pi); one=np.ones(N)
if WT=='z':
    U2=np.mean([np.sum(weights_z(t.astype(complex),one,1.0)**2) for t in ts[:10000]]); cN=np.sqrt(U2/N)
if WT=='m':
    v=np.zeros(K+1,complex); A=np.zeros((K+1,K+1),complex)
    for t in ts[:20000]:
        F=Fmat(t.astype(complex),one); v+=F.sum(1); A+=F@F.conj().T
    v/=20000; A/=20000; CM=np.linalg.solve(A,v); CM=CM/np.sqrt((CM.conj()@A@CM).real/N)
    print(f"mollifier K={K}: RH Cauchy-Schwarz bound {abs(CM.conj()@v)**2/N**2:.4f}",flush=True)
FT=np.array([feats(t.astype(complex),one) for t in ts]); tg=FT.mean(0); se=FT.std(0)/np.sqrt(M)
tg[:len(lp)]=lp
npair=len(lp); R=len(tg); scale=np.maximum(np.abs(tg),1.0)
if WT!='none': print(f"N={N} {MODE} WT={WT} J={JSET[0]}..{JSET[-1]} SIDE={SIDE} YMAX={YMAX}: TW targets {np.array2string(tg[npair:],precision=3)} (max rel MC se {np.max(se[npair:]/tg[npair:]):.4f})",flush=True)
lo=tg.copy(); hi=tg.copy()
if SIDE=='eq': lo[npair:]=tg[npair:]*(1-TOL); hi[npair:]=tg[npair:]*(1+TOL)
else: lo[:]=-np.inf; hi=tg*(1+DELTA); hi[:npair]=lp*(1+float(E('DELTAP',0.0)))
cols=[]
def add(cost,f,info):
    s=max(1.0,np.max(np.abs(f)/scale)); cols.append((cost/s,f/s,1.0/s,info))
for t in ts[:1500]: add(1.0,feats(t.astype(complex),one),(N,0,0,0.0))
comps=[(N-2*k2-2*k3,k2,k3) for k2 in range(N//2+1) for k3 in range((N//2-k2+1) if MODE=='unc' else 1)]
for _ in range(300):
    k1,k2,k3=comps[rng.integers(len(comps))]
    add(k1/N,feats(*build(k1,k2,k3,rng.uniform(0,N,k1+k2+k3),YMAX*rng.random(k3)**2)),(k1,k2,k3,0.0))
BIG=50.0
for it in range(iters):
    C=np.array([c[0] for c in cols]); F=np.array([c[1] for c in cols]).T/scale[:,None]; Ms=np.array([c[2] for c in cols]); m=len(cols)
    # variables: w (m), slack+ (R), slack- (R).  lo <= F w + sp - sm <= hi ; sum Ms w = 1
    fin=np.isfinite(lo)
    Aub=np.vstack([np.hstack([F,np.eye(R),-np.eye(R)]),np.hstack([-F,-np.eye(R),np.eye(R)])[fin]])
    bub=np.concatenate([hi/scale,-(lo/scale)[fin]])
    Aeq=np.zeros((1,m+2*R)); Aeq[0,:m]=Ms
    res=linprog(np.concatenate([C,BIG*np.ones(2*R)]),A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=[1.0],bounds=(0,None),method='highs')
    if res.x is None: print("LP failed",res.message); break
    c0=res.eqlin.marginals[0]; mu=res.ineqlin.marginals; lam=mu[:R].copy(); lam[fin]-=mu[R:]
    lam=lam/scale; slack=res.x[m:].sum(); w=res.x[:m]; val=C@w
    new=[]
    for _ in range(tries):
        k1,k2,k3=comps[rng.integers(len(comps))]; n=k1+k2+k3
        def fo(x):
            f=feats(*build(k1,k2,k3,x[:n],YMAX*np.sin(x[n:])**2)); s=max(1.0,np.max(np.abs(f)/scale)); return (k1/N-c0-lam@f)/s
        st=rng.integers(0,3)
        t0=rng.uniform(0,N,n) if st==0 else (np.arange(n)*N/n+rng.normal(0,0.1,n) if st==1 else rng.uniform(0,N)+rng.normal(0,1.0,n))
        x0=np.concatenate([t0,rng.uniform(0,np.pi/2,k3)*rng.choice([0.2,1.0])])
        r=minimize(fo,x0,method='L-BFGS-B',options={'maxiter':120})
        if r.fun<-1e-7: new.append((r.fun,k1,k2,k3,r.x))
    print(f"it {it:3d} E[s1]/N {val:.5f} slack {slack:.1e} ncols {m} newneg {len(new)} best {min([q[0] for q in new],default=0):.1e}",flush=True)
    if not new and it>3: break
    for (_,k1,k2,k3,x) in new:
        n=k1+k2+k3; y=YMAX*np.sin(x[n:])**2
        add(k1/N,feats(*build(k1,k2,k3,x[:n],y)),(k1,k2,k3,round(float(y.max()),3) if k3 else 0.0))
mass=w*Ms; wp=sum(mass[i] for i in range(m) if cols[i][3][2]>0); wd=sum(mass[i] for i in range(m) if cols[i][3][1]>0)
deep=[cols[i][3][3] for i in range(m) if w[i]>1e-9 and cols[i][3][2]>0]
print(f"RESULT N={N} {MODE} WT={WT} J={JSET[0]}..{JSET[-1]} SIDE={SIDE} DELTA={DELTA} YMAX={YMAX}: value {val:.5f} slack {slack:.1e} | mass on doubles {wd:.3f}, pairs {wp:.3f}; pair depths in support {sorted(deep)[-6:]}")
