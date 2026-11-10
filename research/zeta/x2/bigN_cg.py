"""Large-N realizable ensembles for the pair-only problem (Idea 1) + diagnostics of higher RS-range moments
(Idea 3).  Columns: CUE samples + 'compressed crystal with defects' generator; pricing = scoring many
generator samples + L-BFGS polishing of the best.  Objective: minimise E #simple / N  s.t. E|p_k|^2 = k (k<=N)."""
import numpy as np, sys, time
from scipy.optimize import linprog, minimize
from scipy.stats import unitary_group
rng=np.random.default_rng(int(sys.argv[3]) if len(sys.argv)>3 else 0)
N=int(sys.argv[1]); iters=int(sys.argv[2]) if len(sys.argv)>2 else 40
ks=np.arange(1,N+1); target=ks.astype(float)
def feats(th,m): p=np.exp(2j*np.pi*np.outer(ks,th))@m; return np.abs(p)**2
def gen():
    s=rng.uniform(0.8,1.0); M=int(round(N/s)); n2=rng.integers(0,N//3+1); n0=M-N+n2
    if n0<0 or n0+n2>M: return None
    m=np.ones(M); idx=rng.permutation(M)
    if rng.random()<0.6 and n2>0:   # dipoles: vacancy right after a double where possible
        dbl=idx[:n2]; m[dbl]=2; vac=[]
        for d in dbl:
            j=(d+1)%M
            if m[j]==1 and len(vac)<n0: m[j]=0; vac.append(j)
        rest=[j for j in rng.permutation(M) if m[j]==1]
        for j in rest[:n0-len(vac)]: m[j]=0
    else:
        m[idx[:n2]]=2; m[idx[n2:n2+n0]]=0
    if m.sum()!=N: return None
    th=(np.arange(M)+rng.normal(0,rng.uniform(0,0.12),M))/M
    keep=m>0; return th[keep]%1, m[keep]
def polish(th,m,y):
    def f(t):
        tt=np.concatenate([[th[0]],t]); E=np.exp(2j*np.pi*np.outer(ks,tt)); p=E@m
        v=(y*np.abs(p)**2).sum(); g=2*np.real((y*np.conj(p))[:,None]*2j*np.pi*ks[:,None]*m[None,:]*E).sum(0)
        return v,g[1:]
    r=minimize(f,th[1:],jac=True,method='L-BFGS-B',options={'maxiter':300})
    return np.concatenate([[th[0]],r.x%1]), r.fun
cols=[];g=[];confs=[]
for _ in range(1500):
    U=unitary_group.rvs(N,random_state=rng); th=(np.angle(np.linalg.eigvals(U))/(2*np.pi))%1; m=np.ones(N)
    cols.append(feats(th,m)); g.append(-N*1.0); confs.append((th,m))
t0=time.time()
for it in range(iters):
    A=np.array(cols).T; nc=A.shape[1]; G=np.array(g)
    A_eq=np.vstack([np.hstack([A,np.eye(N),-np.eye(N)]),np.hstack([np.ones((1,nc)),np.zeros((1,2*N))])])
    r=linprog(np.concatenate([-G,1e3*np.ones(2*N)/np.maximum(1,target).repeat(1).tolist()*0+np.concatenate([1e2/target,1e2/target])])[:nc+2*N] if False else np.concatenate([-G,np.concatenate([1e2/target,1e2/target])]),
              A_eq=A_eq,b_eq=np.concatenate([target,[1]]),bounds=[(0,None)]*(nc+2*N),method='highs')
    du=r.eqlin.marginals; y=-du[:N]; y0=-du[N]; lam=r.x[:nc]; art=r.x[nc:].sum()
    simple=-(G*lam).sum()/N
    # pricing
    cand=[]
    for _ in range(3000):
        c=gen()
        if c is None: continue
        th,m=c; red=-(m==1).sum()-(y*feats(th,m)).sum()-y0; cand.append((red,th,m))
    cand.sort(key=lambda z:-z[0]); added=0; best=-1e9
    for red,th,m in cand[:12]:
        th2,val=polish(th,m,y); red2=-(m==1).sum()-val-y0; best=max(best,red2)
        if red2>1e-7: cols.append(feats(th2,m)); g.append(-(m==1).sum()); confs.append((th2,m)); added+=1
    print(it,'simple=%.5f art=%.1e cols=%d added=%d bestred=%.2e t=%.0fs'%(simple,art,len(cols),added,best,time.time()-t0),flush=True)
    if added==0: break
sel=[(lam[i],confs[i]) for i in range(nc) if lam[i]>1e-8]
import pickle; pickle.dump(sel,open('bigN_ens_N%d.pkl'%N,'wb'))
# diagnostics: higher RS-range moments of the final mixture vs CUE
def P(th,m,k): return (m*np.exp(2j*np.pi*k*th)).sum()
print('RESULT N=%d simple=%.5f art=%.1e  (#configs %d)'%(N,simple,art,len(sel)))
worst_q=0; worst_t=0
for a in range(1,N+1):
    for b in range(a,N+1-a):
        q=sum(w*abs(P(th,m,a))**2*abs(P(th,m,b))**2 for w,(th,m) in sel); qt=a*b*(2 if a==b else 1)
        t=sum(w*(P(th,m,a)*P(th,m,b)*np.conj(P(th,m,a+b))).real for w,(th,m) in sel)
        worst_q=max(worst_q,abs(q/qt-1)); worst_t=max(worst_t,abs(t)/np.sqrt(a*b*(a+b)))
print('max rel. error 4-level E|pa|^2|pb|^2/CUE-1 = %.3f ; max |3-level|/sqrt(ab(a+b)) = %.3f'%(worst_q,worst_t))
