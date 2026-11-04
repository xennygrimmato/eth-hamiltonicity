# Certificate: the "fake profile" P* (three single-bond row nets of cost 2, one column net of cost 2, units lambda)
# satisfies every min-cut inequality obtainable from node-local maps + one flattening (any leg cut X|Y).
import numpy as np, itertools
row=lambda i:i%3; col=lambda i:i%2
def struct(kind,bonds):
    # returns (n_internal, edges list (u,v,cap)) with node vertices 0..5, extra vertices 6..
    E=[]
    if kind=='H':
        for i in range(6): E.append((i,(i+1)%6,1))
        n=6
    elif kind=='row':
        for i in range(6): E.append((i,6+row(i),2))
        for (r,s),c in bonds.items(): E.append((6+r,6+s,c))
        n=9
    else:
        for i in range(6): E.append((i,6+col(i),2))
        E.append((6,7,bonds)); n=8
    return n,E
def cutvals(n,E):
    # for each subset S (X side) of internal vertices: const + sum over nodes of (i in S)*y_i + (i notin S)*x_i
    subs=np.arange(1<<n); inS=((subs[:,None]>>np.arange(n))&1).astype(np.int64)
    const=np.zeros(1<<n,dtype=np.int64)
    for u,v,c in E: const+=c*(inS[:,u]!=inS[:,v])
    return const,inS[:,:6]
pats=np.array(list(itertools.product(range(3),repeat=12)),dtype=np.int64)  # x0..x5,y0..y5
X=pats[:,:6]; Y=pats[:,6:]
def mincut(n,E):
    const,inS=cutvals(n,E)
    best=np.full(len(pats),10**9,dtype=np.int64)
    for s in range(len(const)):
        v=const[s]+(Y*inS[s]).sum(1)+(X*(1-inS[s])).sum(1)
        np.minimum(best,v,out=best)
    return best
mH=mincut(*struct('H',None))
P=[('row',{(0,1):2}),('row',{(0,2):2}),('row',{(1,2):2}),('col',2)]
mP=np.max([mincut(*struct(k,b)) for k,b in P],axis=0)
print('patterns',len(pats),'max target mincut',mH.max())
print('violations (max_t m_t < m_H):',int((mP<mH).sum()))
# what does the method give at best? largest m_H over patterns where every row/col term of cost<=c is capped
# sanity: diagonal patterns (one node per row, cut = parity) give m_H=2 at most
diag=[(1 if (i in S and col(i)==0) else 0) for S in [(0,1,2)] for i in range(6)]
# also: profile with max cost < 2 must fail somewhere
for c2 in [1]:
    Q=[('row',{(0,1):c2,(0,2):0,(1,2):0}),('row',{(0,2):c2}),('row',{(1,2):c2}),('col',c2)]
    mQ=np.max([mincut(*struct(k,b)) for k,b in Q],axis=0); print('cost-1 profile violations',int((mQ<mH).sum()))
