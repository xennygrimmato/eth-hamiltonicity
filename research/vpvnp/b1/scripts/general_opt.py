# [N] Joint optimisation of a Euclidean configuration (ends + two hubs per balanced split)
# maximising R = min_S saving_S/|o_S o'_S|, to test whether finite (nonlinear) configurations
# beat the linear-regime optimum c_k = sqrt(k s0 (k-s0)/2).
# Usage: python3 general_opt.py k d restarts eps seed
import sys, itertools, numpy as np
from scipy.optimize import minimize
k=int(sys.argv[1]); d=int(sys.argv[2]); R=int(sys.argv[3]); eps=float(sys.argv[4]); seed=int(sys.argv[5])
rng=np.random.default_rng(seed)
edges=[(a,b) for a in range(k) for b in range(a+1,k)]; N=len(edges)
# end index: 2*e (end (a,b) at a) and 2*e+1 (end (b,a) at b)
node_of=np.array([x for (a,b) in edges for x in (a,b)])
splits=[]
for s in range(1,k):
    if k<=3*s<=2*k:
        for S in itertools.combinations(range(k),s):
            Sc=tuple(x for x in range(k) if x not in S)
            if (s<k-s) or (s==k-s and S<Sc): splits.append(set(S))
M=len(splits)
side=np.array([[0 if node_of[i] in S else 1 for i in range(2*N)] for S in splits])  # 0 -> o, 1 -> o'
nP=2*N*d; nH=2*M*d
def unpack(x):
    t=x[0]; P=x[1:1+nP].reshape(2*N,d); H=x[1+nP:].reshape(M,2,d); return t,P,H
TINY=1e-12
def nrm(v): return np.sqrt((v*v).sum(-1)+TINY)
def cons(x):
    t,P,H=unpack(x)
    W=P[0::2]-P[1::2]; wl=nrm(W)
    hubs=H[np.arange(M)[:,None],side]            # M x 2N x d
    dv=P[None]-hubs; dl=nrm(dv)                     # M x 2N
    hd=H[:,0]-H[:,1]; hl=nrm(hd)
    sav=wl.sum()-dl.sum(1)
    c1=sav-t*hl
    c2=(hd*hd).sum(1)-eps**2
    c3=1-(W*W).sum(1)
    return np.concatenate([c1,c2,c3])
def jac(x):
    t,P,H=unpack(x)
    W=P[0::2]-P[1::2]; wl=nrm(W)
    hubs=H[np.arange(M)[:,None],side]; dv=P[None]-hubs; dl=nrm(dv)
    hd=H[:,0]-H[:,1]; hl=nrm(hd)
    J=np.zeros((2*M+N,len(x)))
    # c1
    J[:M,0]=-hl
    gW=W/wl[:,None]                                  # N x d
    gP=np.zeros((2*N,d)); gP[0::2]=gW; gP[1::2]=-gW
    U=dv/dl[...,None]                                # M x 2N x d
    GP=gP[None]-U                                    # M x 2N x d
    J[:M,1:1+nP]=GP.reshape(M,-1)
    GH=np.zeros((M,2,d))
    for j in (0,1):
        GH[:,j]=(U*(side==j)[...,None]).sum(1)
    uh=hd/hl[:,None]
    GH[:,0]-=t[...,None]*uh if np.ndim(t) else t*uh
    GH[:,1]+=t*uh
    for m in range(M):
        J[m,1+nP+m*2*d:1+nP+(m+1)*2*d]=GH[m].ravel()
    for m in range(M):
        J[M+m,1+nP+m*2*d:1+nP+m*2*d+d]=2*hd[m]
        J[M+m,1+nP+m*2*d+d:1+nP+(m+1)*2*d]=-2*hd[m]
    for e in range(N):
        J[2*M+e,1+2*e*d:1+(2*e+1)*d]=-2*W[e]
        J[2*M+e,1+(2*e+1)*d:1+(2*e+2)*d]=2*W[e]
    return J
s0=-(-k//3); ck=np.sqrt(k*s0*(k-s0)/2)
best=-1
for r in range(R):
    if r==0:   # simplex start (E.5), hubs at +-eps/2 along w_S
        P=np.zeros((2*N,d))
        for e,(a,b) in enumerate(edges):
            u=np.zeros(d); u[a%d]+=1; u[b%d]-=1; u/=np.linalg.norm(u)
            P[2*e]=u/2; P[2*e+1]=-u/2
    else:
        P=rng.normal(size=(2*N,d))*rng.uniform(0.2,2)
        for e in range(N):
            w=P[2*e]-P[2*e+1]; L=np.linalg.norm(w)
            if L>1: c=(P[2*e]+P[2*e+1])/2; P[2*e]=c+w/L/2; P[2*e+1]=c-w/L/2
    H=np.zeros((M,2,d))
    for m,S in enumerate(splits):
        g=sum((P[i] if side[m,i]==0 else -P[i]) for i in range(2*N))
        c=P.mean(0); u=g/ (np.linalg.norm(g)+1e-9)
        H[m,0]=c+u*eps; H[m,1]=c-u*eps
    x0=np.concatenate([[0.0],P.ravel(),H.ravel()])
    # feasible t start
    c=cons(x0)
    res=minimize(lambda x:-x[0],x0,jac=lambda x:np.eye(1,len(x),0).ravel()*-1,
                 constraints=[{'type':'ineq','fun':cons,'jac':jac}],method='SLSQP',
                 options={'maxiter':3000,'ftol':1e-10})
    t,P,H=unpack(res.x); cc=cons(res.x)
    viol=-min(0,cc.min())
    # recompute true ratio
    hubs=H[np.arange(M)[:,None],side]; dl=np.linalg.norm(P[None]-hubs,axis=-1)
    wl=np.linalg.norm(P[0::2]-P[1::2],axis=1); hl=np.linalg.norm(H[:,0]-H[:,1],axis=1)
    ratio=((wl.sum()-dl.sum(1))/hl).min()
    print(f"k={k} restart={r} t={t:.4f} trueR={ratio:.4f} viol={viol:.1e} hubsep[min,max]=[{hl.min():.3g},{hl.max():.3g}] status={res.status}",flush=True)
    if viol<1e-6: best=max(best,ratio)
print(f"RESULT k={k} d={d} eps={eps} best R={best:.4f} c_k={ck:.4f} trivial C_min={s0*(k-s0)}")
