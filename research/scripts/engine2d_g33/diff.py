"""Maximum certified exponent of the multi-contraction single-flattening method on the g x g level.
For a keep/fix/pair contraction M (edge-disjoint X->Y paths in the grid graph), a row-network with bonds
e=(e_rs) is bounded by |alpha|^{s_R(sigma)+e(sigma)} for every row labelling sigma; M is "handled" by it iff
|n_r| <= e(r|rest) for all rows r, n_r = #paths (X-end in row r, Y-end outside) - #paths (Y-end in row r, X-end outside).
Cheapest row term handling M: d_R(M) = max(max_r |n_r|, ceil(sum_r |n_r| / 2)); same for columns.
The method proves cost >= min(d_R, d_C) for every M, and no more: the profile {tailored terms} satisfies every
contraction inequality.  This script maximises min(d_R(M), d_C(M)) over realisable M by ILP."""
import sys, itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
g=int(sys.argv[1]) if len(sys.argv)>1 else 3
nodes=[(r,c) for r in range(g) for c in range(g)]; nid={v:i for i,v in enumerate(nodes)}
edges=[(nid[(r,c)],nid[(s,d)]) for (r,c) in nodes for (s,d) in nodes if r<s and c!=d]
nE=len(edges); nv=len(nodes); deg=2*(g-1)**2
idx={}; n=0
def var(name,k=1):
    global n; idx[name]=list(range(n,n+k)); n+=k
var('fp',nE);var('fm',nE);var('a',nv);var('b',nv);var('nR',g);var('nC',g);var('vR',g);var('vC',g)
var('zR',g);var('zC',g);var('yR',g+1);var('yC',g+1);var('t',1)
A=[];lo=[];hi=[]
def add(coefs,l,h):
    r=np.zeros(n)
    for k,v in coefs: r[k]+=v
    A.append(r);lo.append(l);hi.append(h)
for e in range(nE): add([(idx['fp'][e],1),(idx['fm'][e],1)],0,1)
for v in range(nv):
    out=[];inn=[]
    for ei,(p,q) in enumerate(edges):
        if p==v: out.append(idx['fp'][ei]); inn.append(idx['fm'][ei])
        if q==v: out.append(idx['fm'][ei]); inn.append(idx['fp'][ei])
    add([(k,1) for k in out]+[(k,-1) for k in inn]+[(idx['a'][v],-1),(idx['b'][v],1)],0,0)
    add([(k,1) for k in out]+[(idx['a'][v],-1)],0,np.inf)
    add([(k,1) for k in inn]+[(idx['b'][v],-1)],0,np.inf)
    add([(k,1) for k in out+inn],0,deg)
for r in range(g):
    add([(idx['a'][v],1) for v in range(nv) if nodes[v][0]==r]+[(idx['b'][v],-1) for v in range(nv) if nodes[v][0]==r]+[(idx['nR'][r],-1)],0,0)
    add([(idx['a'][v],1) for v in range(nv) if nodes[v][1]==r]+[(idx['b'][v],-1) for v in range(nv) if nodes[v][1]==r]+[(idx['nC'][r],-1)],0,0)
BIG=200
for nm,vn,zn,yn in (('nR','vR','zR','yR'),('nC','vC','zC','yC')):
    for r in range(g):
        add([(idx[vn][r],1),(idx[nm][r],-1),(idx[zn][r],-BIG)],-np.inf,0)
        add([(idx[vn][r],1),(idx[nm][r],1),(idx[zn][r],BIG)],-np.inf,BIG)
    for r in range(g): add([(idx['t'][0],1),(idx[vn][r],-1),(idx[yn][r],BIG)],-np.inf,BIG)
    add([(idx['t'][0],2)]+[(idx[vn][r],-1) for r in range(g)]+[(idx[yn][g],BIG)],-np.inf,BIG+1)
    add([(idx[yn][r],1) for r in range(g+1)],1,np.inf)
lb=np.zeros(n); ub=np.full(n,np.inf)
for nm in ('fp','fm','zR','zC','yR','yC'):
    for k in idx[nm]: ub[k]=1
for nm in ('a','b'):
    for k in idx[nm]: ub[k]=deg
for nm in ('nR','nC'):
    for k in idx[nm]: lb[k]=-nE
c=np.zeros(n); c[idx['t'][0]]=-1
res=milp(c,constraints=LinearConstraint(np.array(A),lo,hi),integrality=np.ones(n),bounds=Bounds(lb,ub),options={"time_limit":900})
x=np.round(res.x).astype(int)
print("g",g,"Q",(g*(g-1)//2)**2,"max min(d_R,d_C) =",x[idx['t'][0]],"status",res.status)
print(" a",[int(x[k]) for k in idx['a']]," b",[int(x[k]) for k in idx['b']])
print(" n_R",[int(x[k]) for k in idx['nR']]," n_C",[int(x[k]) for k in idx['nC']]," |E|",sum(int(x[k]) for k in idx['a']))
print(" flow edges:",[(nodes[edges[e][0]],nodes[edges[e][1]],"+" if x[idx["fp"][e]] else "-") for e in range(nE) if x[idx["fp"][e]] or x[idx["fm"][e]]], flush=True)
