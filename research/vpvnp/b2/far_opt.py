# Far-leg (linear) regime of the flat-case hub bound: legs of edge e at x_e +- M u_e, M -> infinity.
# Then sum_k delta_k b_k = sum_e < u_e, sum_k (h^k_{G_k(v)} - h^k_{G_k(u)}) >.  With delta_k <= 1 we maximise
# F(h) = sum_e | sum_{k in ks} Delta^k_e |  subject to |h^k_g - h^k_g'| <= 1.
import sys, itertools, numpy as np
from scipy.optimize import minimize
nodes=[(r,c) for r in range(3) for c in range(3)]
tri={v:(v[0]+v[1])%3 for v in nodes}
E=[(u,v) for u in nodes for v in nodes if u<v and tri[u]==tri[v]]
mf=[lambda v:v[0],lambda v:v[1],lambda v:(v[0]-v[1])%3]
def F(h,ks,eps=0.0):
    tot=0
    for (u,v) in E:
        s=sum(h[j,mf[k](u)]-h[j,mf[k](v)] for j,k in enumerate(ks))
        tot+=np.sqrt((s*s).sum()+eps)
    return tot
def run(m,ks,trials,seed):
    rng=np.random.default_rng(seed); best=(0,None)
    K=len(ks)
    cons=[]
    for j in range(K):
        for g,g2 in itertools.combinations(range(3),2):
            cons.append({'type':'ineq','fun':(lambda z,j=j,g=g,g2=g2: 1-((z.reshape(K,3,m)[j,g]-z.reshape(K,3,m)[j,g2])**2).sum())})
    for t in range(trials):
        z=rng.normal(size=K*3*m)*0.5
        r=minimize(lambda z:-F(z.reshape(K,3,m),ks,1e-9),z,constraints=cons,method='SLSQP',options={'maxiter':1000})
        h=r.x.reshape(K,3,m)
        dmax=max(np.sqrt(((h[j,g]-h[j,g2])**2).sum()) for j in range(K) for g,g2 in itertools.combinations(range(3),2))
        val=F(h,ks)/dmax
        if val>best[0]: best=(val,h)
    return best
if __name__=='__main__':
    for ks in ([0],[0,1],[0,1,2]):
        for m in (2,4,6):
            v,h=run(m,ks,60,1)
            print(ks,m,round(v,5),flush=True)
