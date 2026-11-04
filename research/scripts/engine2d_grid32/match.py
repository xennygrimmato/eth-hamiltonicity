import numpy as np, itertools, sys
# hexagon nodes 0..5 (=1..6 in notes); row = i%3 (a=0: nodes0,3; b=1: nodes1,4; c=2: nodes 2,5); col = i%2
row=lambda i:i%3; col=lambda i:i%2
# legs: 2*i (L), 2*i+1 (R)
NL=12
node=lambda l:l//2
def matchings(ls):
    if not ls: yield []; return
    a=ls[0]
    for k in range(1,len(ls)):
        b=ls[k]; rest=ls[1:k]+ls[k+1:]
        for m in matchings(rest): yield [(a,b)]+m
Ms=list(matchings(list(range(NL))))
print(len(Ms))
def cost(m):
    r=sum(row(node(a))!=row(node(b)) for a,b in m); c=sum(col(node(a))!=col(node(b)) for a,b in m)
    return r,c
# vector: index bits b_l in {0,1}; eps(x,y)= x-y nonzero when differ: eps(0,1)=1,eps(1,0)=-1
idx=np.arange(1<<NL)
bits=[(idx>>l)&1 for l in range(NL)]
def vec(m):
    v=np.ones(1<<NL)
    for a,b in m:
        v=v*(bits[a]-bits[b])
    return v
H=[(2*i+1,(2*((i+1)%6))) for i in range(6)]
H=[tuple(sorted(p)) for p in H]
print('H cost',cost(H))
np.save('dummy.npy',np.zeros(1))
