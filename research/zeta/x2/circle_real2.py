"""Finite CUE-model realizability LP with optional higher-moment (Rudnick-Sarnak-range) constraints.
Ensemble = mixture of configurations (D distinct points theta_j on R/Z, multiplicities m_j, sum m_j = N).
Constraints (CUE values, Diaconis-Shahshahani range):
  pair : E|p_k|^2 = min(k,N), 1<=k<=K
  tri  : E Re p_a p_b conj(p_{a+b}) = 0, 1<=a<=b, a+b<=N
  quad : E |p_a|^2|p_b|^2 = ab(1+[a==b]), 1<=a<=b, a+b<=N
Objective: 'simple' -> minimise E #{j: m_j=1}/N ; 'kappa' -> maximise E sum m_j^2/N.
Column generation, pricing by multistart L-BFGS over positions for each multiplicity pattern."""
import numpy as np, sys, argparse
from scipy.optimize import linprog, minimize
rng = np.random.default_rng(0)
def partitions(n, maxpart):
    if n==0: yield (); return
    for p in range(min(n,maxpart),0,-1):
        for rest in partitions(n-p, p): yield (p,)+rest
class Feat:
    def __init__(s, N, K, tri, quad, mom=()):
        s.N=N; s.list=[]; s.target=[]; s.mom=list(mom)
        from math import comb
        for k in range(1,K+1): s.list.append(('p',k,0)); s.target.append(min(k,N))
        if tri:
            for a in range(1,N+1):
                for b in range(a,N+1-a): s.list.append(('t',a,b)); s.target.append(0.0)
        if quad:
            for a in range(1,N+1):
                for b in range(a,N+1-a): s.list.append(('q',a,b)); s.target.append(a*b*(2 if a==b else 1))
        for k in s.mom:   # E |Lambda(1)|^{2k} for CUE: k=1: N+1 ; k=2: (N+1)(N+2)^2(N+3)/12
            s.list.append(('m',k,0)); s.target.append({1:N+1, 2:(N+1)*(N+2)**2*(N+3)/12}[k])
        s.target=np.array(s.target,float)
        G = 4*N+3; s.phi = (np.arange(G)+0.5)/G
        s.kmax = max(K, 2*N if (tri or quad) else K)
    def eval(s, th, m, grad=False, y=None):
        ks = np.arange(1, s.kmax+1)
        E = np.exp(2j*np.pi*np.outer(ks, th)); p = (m[None,:]*E).sum(1)
        P = lambda k: p[k-1]
        vals = np.empty(len(s.list)); dp = np.zeros(s.kmax, complex)  # dF/dp (holomorphic), weighted by y
        for i,(t,a,b) in enumerate(s.list):
            if t=='p':
                vals[i]=abs(P(a))**2
                if grad: dp[a-1]+= y[i]*np.conj(P(a))
            elif t=='t':
                X = P(a)*P(b)*np.conj(P(a+b)); vals[i]=X.real
                if grad:
                    dp[a-1]+= y[i]*0.5*P(b)*np.conj(P(a+b)); dp[b-1]+= y[i]*0.5*P(a)*np.conj(P(a+b))
                    dp[a+b-1]+= y[i]*0.5*np.conj(P(a)*P(b))
            elif t=='m':
                k=a; d = s.phi[:,None]-th[None,:]; base = 2-2*np.cos(2*np.pi*d)   # |1-e(phi-th)|^2
                fac = base**(k*m[None,:]); L = np.prod(fac,axis=1); vals[i]=L.mean()
                if grad:
                    # d/dth_j: prod_{l!=j} fac_l * k m_j base_j^{k m_j -1} * (-4 pi sin(2pi d_j))
                    others = np.empty_like(fac)
                    for j in range(len(th)): others[:,j]=np.prod(np.delete(fac,j,axis=1),axis=1)
                    dfac = k*m[None,:]*base**(k*m[None,:]-1)*(-4*np.pi*np.sin(2*np.pi*d))
                    gm = (others*dfac).mean(0); mg = y[i]*gm
                    s._extra = mg if not hasattr(s,'_extra') or s._extra is None else s._extra+mg
            else:
                A2=abs(P(a))**2; B2=abs(P(b))**2; vals[i]=A2*B2
                if grad:
                    dp[a-1]+= y[i]*np.conj(P(a))*B2; dp[b-1]+= y[i]*A2*np.conj(P(b))
        if not grad: return vals
        extra = getattr(s,'_extra',None); s._extra=None
        # d/dtheta_j F = 2 Re sum_k dF/dp_k * dp_k/dtheta_j, dp_k/dth_j = 2 pi i k m_j E_kj
        g = 2*np.real((dp[:,None]*2j*np.pi*ks[:,None]*m[None,:]*E).sum(0))
        if extra is not None: g = g + extra
        return vals, g
def run(N, K, tri=False, quad=False, maxpart=2, obj='simple', iters=300, restarts=10, verbose=True, mom=()):
    F = Feat(N,K,tri,quad,mom); nf=len(F.list)
    pats=[np.array(p,float) for p in partitions(N,maxpart)]
    gval = lambda p: (-(p==1).sum() if obj=='simple' else (p**2).sum())
    cols=[]; G=[]; best_th={}; confs=[]
    for pi,p in enumerate(pats):
        for _ in range(3):
            th=rng.random(len(p)); cols.append(F.eval(th,p)); G.append(gval(p)); confs.append((th,p))
    BIG=1e3*N
    for it in range(iters):
        A=np.array(cols).T; g=np.array(G,float); nc=A.shape[1]
        A_eq=np.vstack([np.hstack([A,np.eye(nf),-np.eye(nf)]), np.hstack([np.ones((1,nc)),np.zeros((1,2*nf))])])
        b_eq=np.concatenate([F.target,[1.0]])
        cost=np.concatenate([-g, BIG*np.ones(2*nf)])
        r=linprog(cost,A_eq=A_eq,b_eq=b_eq,bounds=[(0,None)]*(nc+2*nf),method='highs')
        du=r.eqlin.marginals; y=-du[:nf]; y0=-du[nf]
        art=r.x[nc:].sum(); val=(g*r.x[:nc]).sum()
        added=0; bestred=-np.inf
        for pi,p in enumerate(pats):
            D=len(p)
            def f(t):
                th=np.concatenate([[0.0],t]); v,gr=F.eval(th,p,grad=True,y=y); return (y*v).sum(), gr[1:]
            starts=[rng.random(D-1) for _ in range(restarts)]
            if pi in best_th: starts.append(best_th[pi][1:]+0.01*rng.standard_normal(D-1))
            bb=(np.inf,None)
            for t0 in starts:
                rr=minimize(f,t0,jac=True,method='L-BFGS-B')
                if rr.fun<bb[0]: bb=(rr.fun, np.concatenate([[0.0],rr.x%1]))
            best_th[pi]=bb[1]
            red=gval(p)-bb[0]-y0; bestred=max(bestred,red)
            if red>1e-7: cols.append(F.eval(bb[1],p)); G.append(gval(p)); confs.append((bb[1],p)); added+=1
        if verbose and it%5==0: print(it,'obj=%.6f art=%.1e cols=%d add=%d red=%.1e'%(val/N,art,len(cols),added,bestred),flush=True)
        if added==0: break
    lam=r.x[:nc]
    return val/N, art, lam, cols, G, pats, confs
if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('N',type=int); ap.add_argument('--K',type=int,default=0)
    ap.add_argument('--tri',action='store_true'); ap.add_argument('--quad',action='store_true')
    ap.add_argument('--maxpart',type=int,default=2); ap.add_argument('--obj',default='simple'); ap.add_argument('--restarts',type=int,default=10); ap.add_argument('--mom',default='')
    a=ap.parse_args(); K=a.K or a.N
    v,art,lam,cols,G,pats,confs=run(a.N,K,a.tri,a.quad,a.maxpart,a.obj,restarts=a.restarts,mom=[int(c) for c in a.mom if c.isdigit()])
    s = -v if a.obj=='simple' else 2-v
    import pickle
    sel=[(lam[i],confs[i]) for i in range(len(lam)) if lam[i]>1e-6]
    pickle.dump(sel, open('ens_N%d_K%d_%s%s%s.pkl'%(a.N,K,a.obj,'_tri' if a.tri else '','_quad' if a.quad else '')+('_mom'+a.mom if a.mom else ''),'wb'))
    for w,(th,p) in sorted(sel,key=lambda z:-z[0])[:12]:
        o=np.argsort(th); print('w=%.4f m=%s th=%s'%(w, p[o].astype(int).tolist(), np.round(th[o],3).tolist()))
    print('RESULT N=%d K=%d tri=%s quad=%s mom=%s maxpart=%d obj=%s value=%.6f simple_fraction=%.6f art=%.1e'%(a.N,K,a.tri,a.quad,a.mom,a.maxpart,a.obj,v,s,art),flush=True)
