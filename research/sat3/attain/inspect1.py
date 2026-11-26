import sys, numpy as np, math
from game1 import *
name=sys.argv[1]; mode=sys.argv[2]; w=tuple(float(x) for x in sys.argv[3].split(',')); nt=int(sys.argv[4]) if len(sys.argv)>4 else 19
g,nodes,lab=net(name); edges=all_edges(nodes)
if mode=='generic': edges=[(a,c) for (a,c) in edges if all(lab[a,k]!=lab[c,k] for k in range(3))]
tgrid=[i/(nt+1) for i in range(1,nt+1)]
v,y,act=solve(lab,edges,w,tgrid,want_primal=True)
print("value",v,v/len(edges)); print("y",np.round(y,4))
from collections import Counter
cnt=Counter()
for mu,i,j,t,pats in act:
    cnt[(pats,round(t,4))]+=mu
for (pats,t),mu in sorted(cnt.items(),key=lambda kv:-kv[1])[:12]:
    m,th,per=mval(pats,t,1-t,w,detail=True)
    print("x=%.4f t=%.3f pats=%s  m=%.5f theta=%.4f costs=%s"%(mu,t,pats,m,th,np.round(per,4)))
