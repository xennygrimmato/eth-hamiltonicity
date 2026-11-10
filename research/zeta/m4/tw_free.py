#!/usr/bin/env python3
"""m4: FREE-WEIGHT version of the mollified TW test.  What a Cauchy-Schwarz/certificate proof can actually use:
the values f(rho)=zeta'B(rho) are NOT functions of the local configuration; one knows only
  (a) f = 0 at multiple zeros,  (b) the linear moment  sum f = M1 (BHB S1, unconditional),
  (c) one-sided upper bounds for the Hermitian squares  |sum_rho f_rho e(j tau_rho/N)|^2 <= W_j (Hypothesis TW, j in JSET),
  (d) the pair rows |S(l)|^2 = l (bandwidth one), (e) optionally  sum|f|^2 <= N (BHB S2, on-line only: M2=1).
Law over (configuration, weight vector f).  Pricing over f is explicit: f* = (nu/2) Q^{-1} 1, Q = sum_j |mu_j| e_j e_j^* (+|mu_M2| I).
Targets (M1, W_j) = CUE expectations of the DETERMINED weights (h4/tw_moll.py analogue, RH-optimal mollifier of length K), so the
CUE law is feasible.  MODE rh: f on simple on-line zeros; unc: also on both members of off-line pairs (depth<=YMAX, rescaled columns).
Usage: tw_free.py N mode [iters tries]  env: K JMIN JMAX DELTA M2 YMAX SEED
"""
import sys, os, numpy as np
from scipy.optimize import linprog, minimize
from scipy.stats import unitary_group
E=os.environ.get
N=int(sys.argv[1]); MODE=sys.argv[2]; iters=int(sys.argv[3]) if len(sys.argv)>3 else 80; tries=int(sys.argv[4]) if len(sys.argv)>4 else 12
OFFCAP=float(E('OFFCAP','-1')); K=int(E('K',max(1,N//2-1))); YMAX=float(E('YMAX',1.0)); DELTA=float(E('DELTA',0.0)); USEM2=E('M2','0')=='1'
rng=np.random.default_rng(int(E('SEED',7)))
JSET=np.arange(int(E('JMIN',0)),int(E('JMAX',N))+1); lp=np.arange(1,N)
def Fmat(taus,mult):
    z=np.exp(2j*np.pi*taus/N); zz=np.repeat(z,mult.astype(int)); e=np.poly(zz)
    h=np.zeros(K+1,complex); h[0]=1
    for k in range(1,K+1): h[k]=-sum(e[j]*h[k-j] for j in range(1,min(k,len(e)-1)+1))
    r=1-z[None,:]/z[:,None]; np.fill_diagonal(r,1.0); r=r**mult[None,:]
    g=np.where(mult==1,np.prod(r,axis=1),0.0)
    return g[None,:]*h[:,None]*z[None,:]**(-np.arange(K+1)[:,None])
def feats(taus,mult,f):
    S=(mult[:,None]*np.exp(2j*np.pi*np.outer(taus,lp)/N)).sum(0)
    T=(f[:,None]*np.exp(2j*np.pi*np.outer(taus,JSET)/N)).sum(0)
    out=[np.abs(S)**2,[f.sum().real,f.sum().imag],np.abs(T)**2]
    if USEM2: out.append([np.sum(np.abs(f)**2)])
    if OFFCAP>=0: out.append([np.sum(np.abs(f[np.abs(taus.imag)>0])**2)])
    return np.concatenate(out)
def build(k1,k2,k3,t,y):
    taus=np.concatenate([t[:k1+k2].astype(complex),t[k1+k2:]+1j*y,t[k1+k2:]-1j*y])
    mult=np.concatenate([np.ones(k1),2*np.ones(k2),np.ones(2*k3)]); return taus,mult
M=int(E('MC',30000)); ts=np.angle(np.linalg.eigvals(unitary_group.rvs(N,size=M,random_state=3)))*N/(2*np.pi); one=np.ones(N)
v=np.zeros(K+1,complex); A=np.zeros((K+1,K+1),complex)
for t in ts[:20000]:
    F=Fmat(t.astype(complex),one); v+=F.sum(1); A+=F@F.conj().T
v/=20000; A/=20000; CM=np.linalg.solve(A,v); CM=CM/np.sqrt((CM.conj()@A@CM).real/N)
fdet=lambda taus,mult: CM.conj()@Fmat(taus,mult)
FT=np.array([feats(t.astype(complex),one,fdet(t.astype(complex),one)) for t in ts]); tg=FT.mean(0)
np0=N-1; tg[:np0]=lp; tg[np0+1]=0.0; m1=tg[np0]
R=len(tg); nW=len(JSET); iW=np.arange(np0+2,np0+2+nW)
print(f"N={N} {MODE} K={K} J={JSET[0]}..{JSET[-1]} DELTA={DELTA} M2={USEM2} YMAX={YMAX}: M1={m1:.4f} (RH C-S bound {m1**2/N**2:.4f}); W targets {np.array2string(tg[iW],precision=3)}",flush=True)
eqmask=np.zeros(R,bool); eqmask[:np0+2]=True
hi=tg*(1+DELTA); hi[:np0+2]=tg[:np0+2]
if OFFCAP>=0: hi[-1]=OFFCAP*N; tg[-1]=OFFCAP*N   # m4: one-sided bound sum_{off-line rho}|f|^2 <= OFFCAP*N (the missing 'Lemma O1')
scale=np.maximum(np.abs(tg),1.0)
cols=[]
def add(cost,f,info):
    s=max(1.0,np.max(np.abs(f)/scale)); cols.append((cost/s,f/s,1.0/s,info))
for t in ts[:1500]:
    tc=t.astype(complex); add(1.0,feats(tc,one,fdet(tc,one)),(N,0,0,0.0))
comps=[(N-2*k2-2*k3,k2,k3) for k2 in range(N//2+1) for k3 in range((N//2-k2+1) if MODE=='unc' else 1)]
def bestf(taus,mult,nu,muW,muM2,muOff=0.0):
    supp=(mult==1); idx=np.where(supp)[0]; f=np.zeros(len(taus),complex)
    if len(idx)==0: return f
    Ej=np.exp(2j*np.pi*np.outer(taus[idx],JSET)/N)            # n x J
    Q=(Ej*muW[None,:])@Ej.conj().T + (muM2+1e-9*max(1e-12,muW.sum()+muM2)+1e-12)*np.eye(len(idx))
    # we need conj: T_f(j) = sum f e_j  => |T|^2 = f^T E E^* conj f ; write g = conj f? use f^* (conj E)(E^T) f
    Qh=(Ej.conj()*muW[None,:])@Ej.T + (Q-(Ej*muW[None,:])@Ej.conj().T)
    Qh=Qh+np.diag(muOff*(np.abs(taus[idx].imag)>0))
    f[idx]=(nu/2)*np.linalg.lstsq(Qh,np.ones(len(idx)).astype(complex),rcond=1e-13)[0]
    return f
BIG=50.0
for it in range(iters):
    C=np.array([c[0] for c in cols]); F=np.array([c[1] for c in cols]).T/scale[:,None]; Ms=np.array([c[2] for c in cols]); m=len(cols)
    ub=~eqmask
    Aeq=np.zeros((1+eqmask.sum(),m+2*R)); Aeq[0,:m]=Ms
    Aeq[1:,:m]=F[eqmask]; Aeq[1:,m:m+R]=np.eye(R)[eqmask]; Aeq[1:,m+R:]=-np.eye(R)[eqmask]
    Aub=np.hstack([F[ub],np.eye(R)[ub]*0,-np.eye(R)[ub]])
    res=linprog(np.concatenate([C,BIG*np.ones(2*R)]),A_ub=Aub,b_ub=(hi/scale)[ub],A_eq=Aeq,b_eq=np.concatenate([[1.0],(tg/scale)[eqmask]]),bounds=(0,None),method='highs')
    if res.x is None: print("LP failed",res.message); break
    c0=res.eqlin.marginals[0]; lam=np.zeros(R); lam[eqmask]=res.eqlin.marginals[1:]; lam[ub]=res.ineqlin.marginals; lam=lam/scale
    slack=res.x[m:].sum(); w=res.x[:m]; val=C@w
    nu=lam[np0]+1j*lam[np0+1]; muW=-lam[iW]; muW=np.maximum(muW,0); muM2=max(-lam[np0+2+nW],0) if USEM2 else 0.0; muOff=max(-lam[-1],0) if OFFCAP>=0 else 0.0
    new=[]
    for _ in range(tries):
        k1,k2,k3=comps[rng.integers(len(comps))]; n=k1+k2+k3
        def conf(x):
            taus,mult=build(k1,k2,k3,x[:n],YMAX*np.sin(x[n:])**2)
            if MODE=='rh' or k3==0: fm=mult.copy(); fm[k1+k2:]=1
            return taus,mult
        def fo(x):
            taus,mult=conf(x); f=bestf(taus,mult,nu,muW,muM2,muOff); ft=feats(taus,mult,f); s=max(1.0,np.max(np.abs(ft)/scale)); return (k1/N-c0-lam@ft)/s
        st=rng.integers(0,3)
        t0=rng.uniform(0,N,n) if st==0 else (np.arange(n)*N/n+rng.normal(0,0.1,n) if st==1 else rng.uniform(0,N)+rng.normal(0,1.0,n))
        x0=np.concatenate([t0,rng.uniform(0,np.pi/2,k3)*rng.choice([0.2,1.0])])
        r=minimize(fo,x0,method='L-BFGS-B',options={'maxiter':100})
        if r.fun<-1e-7: new.append((r.fun,k1,k2,k3,r.x))
    print(f"it {it:3d} E[s1]/N {val:.5f} slack {slack:.1e} ncols {m} newneg {len(new)} best {min([q[0] for q in new],default=0):.1e}",flush=True)
    if not new and it>3: break
    for (_,k1,k2,k3,x) in new:
        n=k1+k2+k3; y=YMAX*np.sin(x[n:])**2; taus,mult=build(k1,k2,k3,x[:n],y)
        add(k1/N,feats(taus,mult,bestf(taus,mult,nu,muW,muM2,muOff)),(k1,k2,k3,round(float(y.max()),3) if k3 else 0.0))
mass=w*Ms; wp=sum(mass[i] for i in range(m) if cols[i][3][2]>0); wd=sum(mass[i] for i in range(m) if cols[i][3][1]>0)
deep=[cols[i][3][3] for i in range(m) if w[i]>1e-9 and cols[i][3][2]>0]
print(f"RESULT N={N} {MODE} free-f K={K} J={JSET[0]}..{JSET[-1]} DELTA={DELTA} M2={USEM2} YMAX={YMAX}: value {val:.5f} slack {slack:.1e} | mass doubles {wd:.3f}, pairs {wp:.3f}; depths {sorted(deep)[-6:]}")
