"""Lead task (1), realizable side.  Finite model (E|p_k|^2=k, k<=N), mixtures of actual marked configurations
(marks 1,2), extra row  E G(C) >= c*N  with G one of
  any : ordered pairs of DISTINCT points at circular distance < lam (weights m_j m_k)       [implied by 'c of zeros have a distinct zero within lam']
  sc  : ordered pairs of distinct SIMPLE points (= sign changes of Z) within lam (weight 1)
  cons: 2 * #consecutive distinct-point gaps < lam   (ordered count of consecutive close distinct pairs)
Smoothed from below: phi(d)=1 for d<=lam-w, linear to 0 at lam (so feasibility for the smoothed row implies the true row).
min simple fraction by column generation (CUE seeds + multistart L-BFGS pricing)."""
import numpy as np, argparse
from scipy.optimize import linprog, minimize
from scipy.stats import unitary_group
rng=np.random.default_rng(1)
ap=argparse.ArgumentParser(); ap.add_argument('N',type=int); ap.add_argument('--lam',type=float,default=0.5)
ap.add_argument('--c',type=float,default=0.05); ap.add_argument('--kind',default='any'); ap.add_argument('--w',type=float,default=0.03)
ap.add_argument('--iters',type=int,default=60); ap.add_argument('--restarts',type=int,default=6)
a=ap.parse_args(); N=a.N; ks=np.arange(1,N+1); lam=a.lam; w=a.w
def phi(d):  # d in mean-spacing units
    return np.clip((lam-d)/w,0,1)
def dphi(d): return np.where((d>lam-w)&(d<lam),-1/w,0.0)
def G(th,m,grad=False):
    D=len(th); dd=(th[:,None]-th[None,:]+0.5)%1-0.5; d=np.abs(dd)*N; np.fill_diagonal(d,99)
    if a.kind=='any': W=np.outer(m,m)
    elif a.kind=='sc': s=(m%2==1).astype(float); W=np.outer(s,s)
    if a.kind in ('any','sc'):
        val=(W*phi(d)).sum()
        if not grad: return val
        g=(W*dphi(d)*np.sign(dd)*N).sum(1)*2
        return val,g
    # consecutive
    o=np.argsort(th); ts=th[o]; gaps=(np.roll(ts,-1)-ts)%1*N
    val=2*phi(gaps).sum()
    if not grad: return val
    gg=2*dphi(gaps); g=np.zeros(D); g[o]+= -gg; g[np.roll(o,-1)]+= gg
    return val,g
def feats(th,m):
    p=np.exp(2j*np.pi*np.outer(ks,th))@m; return np.concatenate([np.abs(p)**2,[G(th,m)]])
def partitions(n,mp):
    if n==0: yield (); return
    for q in range(min(n,mp),0,-1):
        for r in partitions(n-q,q): yield (q,)+r
pats=[np.array(p,float) for p in partitions(N,2)]
target=np.concatenate([ks.astype(float),[a.c*N]])
cols=[];gv=[];confs=[]
for _ in range(1500):
    U=unitary_group.rvs(N,random_state=rng); th=(np.angle(np.linalg.eigvals(U))/(2*np.pi))%1; m=np.ones(N)
    cols.append(feats(th,m)); gv.append(-N); confs.append((th,m))
nf=N+1; best={}
for it in range(a.iters):
    A=np.array(cols).T; nc=A.shape[1]; g=np.array(gv,float)
    # equality for pair rows, >= for G row: G - s = cN with s>=0 slack
    A_eq=np.vstack([np.hstack([A,np.eye(nf),-np.eye(nf),np.zeros((nf,1))]),np.hstack([np.ones((1,nc)),np.zeros((1,2*nf+1))])])
    A_eq[N,-1]=-1.0
    b_eq=np.concatenate([target,[1.0]])
    sc_=1e2/np.maximum(1,target); cost=np.concatenate([-g,sc_,sc_,[0.0]])
    r=linprog(cost,A_eq=A_eq,b_eq=b_eq,bounds=[(0,None)]*(nc+2*nf+1),method='highs')
    du=r.eqlin.marginals; y=-du[:nf]; y0=-du[nf]; art=r.x[nc:nc+2*nf].sum(); val=(g*r.x[:nc]).sum()
    added=0; bestred=-np.inf
    for pi,p in enumerate(pats):
        Dn=len(p)
        def f(t):
            th=np.concatenate([[0.0],t]); E=np.exp(2j*np.pi*np.outer(ks,th)); pk=E@p
            v=(y[:N]*np.abs(pk)**2).sum(); gr=2*np.real((y[:N]*np.conj(pk))[:,None]*2j*np.pi*ks[:,None]*p[None,:]*E).sum(0)
            gval,ggr=G(th,p,grad=True); v+=y[N]*gval; gr=gr+y[N]*ggr
            return v,gr[1:]
        starts=[rng.random(Dn-1) for _ in range(a.restarts)]
        if pi in best: starts.append((best[pi][1:]+0.01*rng.standard_normal(Dn-1))%1)
        bb=(np.inf,None)
        for t0 in starts:
            rr=minimize(f,t0,jac=True,method='L-BFGS-B')
            if rr.fun<bb[0]: bb=(rr.fun,np.concatenate([[0.0],rr.x%1]))
        best[pi]=bb[1]; red=-(p==1).sum()-bb[0]-y0; bestred=max(bestred,red)
        if red>1e-7: cols.append(feats(bb[1],p)); gv.append(-(p==1).sum()); confs.append((bb[1],p)); added+=1
    if it%5==0: print(it,'simple=%.5f art=%.1e cols=%d add=%d red=%.1e'%(-val/N,art,len(cols),added,bestred),flush=True)
    if added==0: break
print('RESULT N=%d kind=%s lam=%.2f c=%.3f simple=%.5f art=%.1e'%(N,a.kind,lam,a.c,-val/N,art),flush=True)
