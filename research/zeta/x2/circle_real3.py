"""Vectorised, CUE-seeded version of circle_real2 (same problem; see notebook Idea 1/2).
features: pair |p_k|^2 (k<=K); tri Re p_a p_b conj p_{a+b} (a<=b, a+b<=N); quad |p_a|^2|p_b|^2 (a<=b, a+b<=N);
mom E_phi |Lambda(e(phi))|^{2k} (k in mom).  CUE targets.  maximise kappa or minimise simple fraction."""
import numpy as np, argparse, pickle
from scipy.optimize import linprog, minimize
from scipy.stats import unitary_group
rng=np.random.default_rng(0)
def partitions(n, maxpart):
    if n==0: yield (); return
    for p in range(min(n,maxpart),0,-1):
        for rest in partitions(n-p, p): yield (p,)+rest
class Feat:
    def __init__(s,N,K,tri,quad,mom):
        s.N=N; T=[]; s.pk=np.arange(1,K+1); T+= [min(k,N) for k in s.pk]
        tr=[(a,b) for a in range(1,N+1) for b in range(a,N+1-a)] if tri else []
        qu=[(a,b) for a in range(1,N+1) for b in range(a,N+1-a)] if quad else []
        s.ta=np.array([a for a,b in tr],int); s.tb=np.array([b for a,b in tr],int); T+=[0.0]*len(tr)
        s.qa=np.array([a for a,b in qu],int); s.qb=np.array([b for a,b in qu],int); T+=[a*b*(2 if a==b else 1) for a,b in qu]
        s.mom=list(mom); T+=[{1:N+1,2:(N+1)*(N+2)**2*(N+3)/12}[k] for k in s.mom]
        s.target=np.array(T,float); s.nf=len(T)
        s.kmax=max(K,N); G=4*N+3; s.phi=(np.arange(G)+0.5)/G
    def eval(s,th,m,y=None):
        ks=np.arange(1,s.kmax+1); E=np.exp(2j*np.pi*np.outer(ks,th)); p=E@m
        v=[np.abs(p[s.pk-1])**2]
        if s.ta.size: X=p[s.ta-1]*p[s.tb-1]*np.conj(p[s.ta+s.tb-1]); v.append(X.real)
        if s.qa.size: A2=np.abs(p[s.qa-1])**2; B2=np.abs(p[s.qb-1])**2; v.append(A2*B2)
        if s.mom:
            d=s.phi[:,None]-th[None,:]; base=2-2*np.cos(2*np.pi*d); lb=np.log(np.maximum(base,1e-300))
            for k in s.mom: v.append(np.array([np.exp(lb@(k*m)).mean()]))
        vals=np.concatenate(v)
        if y is None: return vals
        i=0; dp=np.zeros(s.kmax,complex)
        yy=y[i:i+s.pk.size]; i+=s.pk.size; np.add.at(dp,s.pk-1,yy*np.conj(p[s.pk-1]))
        if s.ta.size:
            yy=y[i:i+s.ta.size]; i+=s.ta.size; pa=p[s.ta-1]; pb=p[s.tb-1]; pc=p[s.ta+s.tb-1]
            np.add.at(dp,s.ta-1,0.5*yy*pb*np.conj(pc)); np.add.at(dp,s.tb-1,0.5*yy*pa*np.conj(pc)); np.add.at(dp,s.ta+s.tb-1,0.5*yy*np.conj(pa*pb))
        if s.qa.size:
            yy=y[i:i+s.qa.size]; i+=s.qa.size
            np.add.at(dp,s.qa-1,yy*np.conj(p[s.qa-1])*B2); np.add.at(dp,s.qb-1,yy*A2*np.conj(p[s.qb-1]))
        g=2*np.real((dp[:,None]*2j*np.pi*ks[:,None]*m[None,:]*E).sum(0))
        if s.mom:
            for k in s.mom:
                yy=y[i]; i+=1
                L=np.exp(lb@(k*m))  # |Lambda|^{2k} on grid
                # d/dth_j log base_j = (-4pi sin(2pi d))/base ; use L*k*m_j*that (L vanishes where base small)
                with np.errstate(divide='ignore',invalid='ignore'):
                    r=np.where(base>1e-12,(-4*np.pi*np.sin(2*np.pi*d))/base,0.0)
                g=g+yy*(L[:,None]*k*m[None,:]*r).mean(0)
        return vals,g
def run(N,K,tri,quad,mom,maxpart,obj,restarts,iters=400,ncue=3000,verbose=True,tag=''):
    F=Feat(N,K,tri,quad,mom); nf=F.nf
    pats=[np.array(p,float) for p in partitions(N,maxpart)]
    gval=lambda p:(-(p==1).sum() if obj=='simple' else (p**2).sum())
    cols=[];G=[];confs=[]
    for _ in range(ncue):
        U=unitary_group.rvs(N,random_state=rng); th=(np.angle(np.linalg.eigvals(U))/(2*np.pi))%1; m=np.ones(N)
        cols.append(F.eval(th,m)); G.append(gval(m)); confs.append((th,m))
    best={}
    for it in range(iters):
        A=np.array(cols).T; g=np.array(G,float); nc=A.shape[1]
        BIG=1e2
        A_eq=np.vstack([np.hstack([A,np.eye(nf),-np.eye(nf)]),np.hstack([np.ones((1,nc)),np.zeros((1,2*nf))])])
        b_eq=np.concatenate([F.target,[1.0]]); scale=np.maximum(1,np.abs(F.target))
        cost=np.concatenate([-g,BIG*np.concatenate([1/scale,1/scale])])
        r=linprog(cost,A_eq=A_eq,b_eq=b_eq,bounds=[(0,None)]*(nc+2*nf),method='highs')
        du=r.eqlin.marginals; y=-du[:nf]; y0=-du[nf]
        art=(r.x[nc:]).sum(); val=(g*r.x[:nc]).sum()
        added=0; bestred=-np.inf
        for pi,p in enumerate(pats):
            D=len(p)
            def f(t):
                th=np.concatenate([[0.0],t]); v,gr=F.eval(th,p,y); return (y*v).sum(),gr[1:]
            starts=[rng.random(D-1) for _ in range(restarts)]
            if pi in best: starts.append((best[pi][1:]+0.02*rng.standard_normal(D-1))%1)
            bb=(np.inf,None)
            for t0 in starts:
                rr=minimize(f,t0,jac=True,method='L-BFGS-B')
                if rr.fun<bb[0]: bb=(rr.fun,np.concatenate([[0.0],rr.x%1]))
            best[pi]=bb[1]; red=gval(p)-bb[0]-y0; bestred=max(bestred,red)
            if red>1e-7: cols.append(F.eval(bb[1],p)); G.append(gval(p)); confs.append((bb[1],p)); added+=1
        if verbose and it%5==0: print(it,'obj=%.6f art=%.2e cols=%d add=%d red=%.1e'%(val/N,art,len(cols),added,bestred),flush=True)
        if added==0: break
    lam=r.x[:nc]; sel=[(lam[i],confs[i]) for i in range(nc) if lam[i]>1e-7]
    pickle.dump(sel,open('ens3_%s.pkl'%tag,'wb'))
    return val/N,art
if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('N',type=int); ap.add_argument('--K',type=int,default=0)
    ap.add_argument('--tri',action='store_true'); ap.add_argument('--quad',action='store_true'); ap.add_argument('--mom',default='')
    ap.add_argument('--maxpart',type=int,default=2); ap.add_argument('--obj',default='simple'); ap.add_argument('--restarts',type=int,default=6)
    ap.add_argument('--ncue',type=int,default=3000)
    a=ap.parse_args(); K=a.K or a.N; mom=[int(c) for c in a.mom]
    tag='N%d_K%d_%s%s%s%s'%(a.N,K,a.obj,'_tri' if a.tri else '','_quad' if a.quad else '',('_mom'+a.mom) if a.mom else '')
    v,art=run(a.N,K,a.tri,a.quad,mom,a.maxpart,a.obj,a.restarts,ncue=a.ncue,tag=tag)
    s=-v if a.obj=='simple' else 2-v
    print('RESULT %s value=%.6f simple_fraction=%.6f art=%.2e'%(tag,v,s,art),flush=True)
