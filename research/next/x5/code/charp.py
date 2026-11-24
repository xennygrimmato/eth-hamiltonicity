import sys, itertools
from crossing import *
n1,e1,n2,e2=map(int,sys.argv[1:5])
Q1,Q2,Th,res,co=compute(n1,e1,n2,e2,verbose=False)
S1,S2=symbols(n1,e1),symbols(n2,e2)
def flat(N,rp,cp,p):
    idx={'a':S1,'b':S2,'c':S1,'d':S2}; rows=[]
    for r in itertools.product(idx[rp[0]],idx[rp[1]]):
        row=[]
        for c in itertools.product(idx[cp[0]],idx[cp[1]]):
            s={rp[0]:r[0],rp[1]:r[1],cp[0]:c[0],cp[1]:c[1]}; row.append(co[(s['a'],s['b'],s['c'],s['d'])][N])
        rows.append(row)
    return rank_modp(rows,p) if p else rank_Q(rows)
print(f"({n1},{e1})x({n2},{e2}) Q={Q1}x{Q2}: N: rk_ad|bc [Q,F2,F3,F5] ; rk_ab|cd [Q,F2,F3,F5]")
for N in range(Th+1):
    if all(co[k][N]==0 for k in co): continue
    a=[flat(N,'ad','bc',p) for p in (0,2,3,5)]; b=[flat(N,'ab','cd',p) for p in (0,2,3,5)]
    print(N,a,b)
