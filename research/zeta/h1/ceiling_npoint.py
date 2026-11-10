#!/usr/bin/env python3
"""h1: does the bandwidth-one ceiling survive when the UNCONDITIONAL 3- and 4-point data (Rudnick-Sarnak range,
= Diaconis-Shahshahani moments of CUE(N) in the periodic model) are added to the two-point rows?
Model as in h3/t1_ceiling_cg.py (RH side: on-line simple / on-line double marks; N-periodic, total multiplicity N).
S(l) = sum_j m_j e(l t_j / N).  Rows (expectations over the law; mirror-symmetrised so only real parts):
  2pt : E|S(l)|^2 = l,                      1<=l<=N-1
  3pt : E Re[S(a)S(b)conj S(a+b)] = 0,      1<=a<=b, a+b<=N-1
  4pt : E|S(a)|^2|S(b)|^2 = ab(1+[a=b]),    1<=a<=b, a+b<=N-1
        E Re[S(a)S(b)conj(S(c)S(d))] = 0,   a<=b, c<=d, a<c, a+b=c+d<=N-1
Objective: min E[#simple]/N.   Usage: ceiling_npoint.py N level(2|3|4) iters tries
A feasible law (slack 0) is an upper bound for every certificate using these rows.
"""
import sys, numpy as np, itertools
from scipy.optimize import linprog, minimize
import os
rng=np.random.default_rng(int(os.environ.get("SEED",7)))
def rows_def(N,level):
    R=[('2',l) for l in range(1,N)]
    if level>=3: R+=[('3',a,b) for a in range(1,N) for b in range(a,N) if a+b<=N-1]
    if level>=4:
        R+=[('4',a,b) for a in range(1,N) for b in range(a,N) if a+b<=N-1]
        for s in range(2,N):
            ps=[(a,s-a) for a in range(1,s//2+1)]
            R+=[('4x',p[0],p[1],q[0],q[1]) for p,q in itertools.combinations(ps,2)]
    return R
def target(R):
    out=[]
    for r in R:
        if r[0]=='2': out.append(float(r[1]))
        elif r[0]=='3': out.append(0.0)
        elif r[0]=='4': out.append(r[1]*r[2]*(2.0 if r[1]==r[2] else 1.0))
        else: out.append(0.0)
    return np.array(out)
def feats(N,R,t,m,y=None):
    l=np.arange(0,N)
    W=m[:,None]*np.ones((1,N)) if y is None else np.where((y>0)[:,None],2*np.cosh(2*np.pi*np.outer(y,l)/N),m[:,None]*np.ones((1,N)))
    S=(W*np.exp(2j*np.pi*np.outer(t,l)/N)).sum(0)
    out=np.empty(len(R))
    for i,r in enumerate(R):
        if r[0]=='2': out[i]=abs(S[r[1]])**2
        elif r[0]=='3': out[i]=(S[r[1]]*S[r[2]]*np.conj(S[r[1]+r[2]])).real
        elif r[0]=='4': out[i]=abs(S[r[1]])**2*abs(S[r[2]])**2
        else: out[i]=(S[r[1]]*S[r[2]]*np.conj(S[r[3]]*S[r[4]])).real
    return out
def cue(N):
    Z=(rng.normal(size=(N,N))+1j*rng.normal(size=(N,N)))/np.sqrt(2); Q,Rr=np.linalg.qr(Z); Q=Q*(np.diag(Rr)/abs(np.diag(Rr)))
    return np.angle(np.linalg.eigvals(Q))*N/(2*np.pi)
def run(N,level,iters,tries,ncue=4000):
    R=rows_def(N,level); tg=target(R); scale=np.maximum(np.abs(tg),1.0)*np.array([1.0 if r[0]=='2' else N for r in R])
    cols=[]
    for _ in range(ncue): cols.append((1.0,feats(N,R,cue(N),np.ones(N)),(N,0)))
    for _ in range(400):
        k2=rng.integers(0,N//2+1); k1=N-2*k2; m=np.array([1.0]*k1+[2.0]*k2)
        cols.append((k1/N,feats(N,R,rng.uniform(0,N,len(m)),m),(k1,k2)))
    BIG=50.0; nr=len(R)
    for it in range(iters):
        C=np.array([c[0] for c in cols]); F=np.array([c[1] for c in cols]).T/scale[:,None]; mcol=len(cols)
        cobj=np.concatenate([C,BIG*np.ones(2*nr)])
        Aeq=np.zeros((nr+1,mcol+2*nr)); Aeq[0,:mcol]=1; Aeq[1:,:mcol]=F; Aeq[1:,mcol:mcol+nr]=np.eye(nr); Aeq[1:,mcol+nr:]=-np.eye(nr)
        res=linprog(cobj,A_eq=Aeq,b_eq=np.concatenate([[1.0],tg/scale]),bounds=(0,None),method='highs')
        c0,lam=res.eqlin.marginals[0],res.eqlin.marginals[1:]; slack=res.x[mcol:].sum()
        new=[]
        for _ in range(tries):
            if rng.random()<0.25:
                t0=cue(N); k2=0
            else:
                k2=rng.integers(0,N//2+1); t0=None
            k3=rng.integers(0,(N-2*k2)//2+1) if (UNC and t0 is None) else 0
            k1=N-2*k2-2*k3; m=np.array([1.0]*k1+[2.0]*(k2+k3)); n=len(m); isp=np.arange(n)>=k1+k2
            if t0 is None: t0=rng.uniform(0,N,n)
            def f(z):
                y=np.zeros(n); y[isp]=np.minimum(np.abs(z[n:]),YMAX); return k1/N-c0-lam@(feats(N,R,z[:n],m,y)/scale)
            z0=np.concatenate([t0,np.abs(rng.exponential(rng.choice([0.05,0.2,0.6]),k3))])
            r=minimize(f,z0,method='L-BFGS-B',options={'maxiter':60})
            if r.fun<-1e-7:
                y=np.zeros(n); y[isp]=np.minimum(np.abs(r.x[n:]),YMAX); new.append((r.fun,k1,k2,r.x[:n],m,y,k3))
        new.sort(key=lambda z:z[0])
        print(f"it {it:3d} obj {res.fun:.6f} slack {slack:.2e} ncols {mcol} newneg {len(new)} best {new[0][0] if new else 0:.2e}",flush=True)
        if not new and slack<1e-9: break
        for (_,k1,k2,t,m,y,k3) in new[:40]: cols.append((k1/N,feats(N,R,t,m,y),(k1,k2,k3,round(float(y.max()),2))))
    w=res.x[:len(cols)]; supp={}
    for i,c in enumerate(cols):
        if w[i]>1e-7: supp[c[2]]=supp.get(c[2],0)+w[i]
    print("law weight by (k1,k2[,pairs,maxdepth]):",{str(k):round(v,4) for k,v in sorted(supp.items(),key=str)})
    print('weight on pair configs:',sum(v for k,v in supp.items() if len(k)>2 and k[2]>0))
    print(f"RESULT N={N} level={level}: value {res.fun:.6f} slack {slack:.1e} rows {nr}")
UNC=os.environ.get('UNC','0')=='1'; YMAX=float(os.environ.get('YMAX',1.5))
if __name__=='__main__':
    run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]))
