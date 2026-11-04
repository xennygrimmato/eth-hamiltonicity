"""engine2d_lossy.py -- research/engine2-decorrelated.md §7 (lossy diagonal contractions).
(a) numeric check of Theorem 4 (3x2 grid): rank M(H) = N^4, rank M(T) <= N*rank_{b|ac}(T), <= N*rank_col(T)  (N = 2, 3)
(b) the lossy-diagonal bound e - max(s_R, s_C) for full g x g levels (no merges) and the 3x2 grid
Run: python3 engine2d_lossy.py   (about 1 minute)
"""
print("(a) Theorem 4 check")
# numeric check of Theorem 4 (lossy contraction) for the 3x2 grid, N=2 and N=3
import numpy as np
rng=np.random.default_rng(5)
# leg order: x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3  (ab, ac, bc)
B=[2,3,8,9]               # row b legs: u1 v1 x3 y3
AC=[0,1,4,5,6,7,10,11]
ODD=[0,2,4,6,8,10]; EVEN=[1,3,5,7,9,11]
def flat(T,L,R,N): return T.transpose(L+R).reshape(N**len(L),N**len(R))
def H(N):
    T=np.zeros([N]*12)
    for x1,y1,x2,y2,x3,y3 in np.ndindex(*[N]*6): T[x1,y1,y1,x1,x2,y2,y2,x2,x3,y3,y3,x3]=1
    return T
def M(T,N,o=0):
    # rows (y1,y2,v2,v3), cols (u1,x3,u2,v1); sum over z = x1 = x2 ; y3=u3=o
    S=np.zeros([N]*8)
    for z in range(N): S+=T[z,:,:,:,z,:,:,:,:,o,o,:]   # remaining axes: y1 u1 v1 y2 u2 v2 x3 v3
    # axes: 0 y1,1 u1,2 v1,3 y2,4 u2,5 v2,6 x3,7 v3
    return S.transpose([0,3,5,7,1,6,4,2]).reshape(N**4,N**4)
rk=lambda A: np.linalg.matrix_rank(A)
for N in [2,3]:
    h=H(N); print('N',N,'rank M(H)',rk(M(h,N)),'=N^4',N**4)
    for trial in range(4):
        r=rng.integers(1,4)
        # tensor with b|ac rank r
        T=sum(np.multiply.outer(rng.standard_normal([N]*4),rng.standard_normal([N]*8)) for _ in range(r))
        perm=np.argsort(B+AC); T=T.transpose(perm)
        # tensor with col rank r
        U=sum(np.multiply.outer(rng.standard_normal([N]*6),rng.standard_normal([N]*6)) for _ in range(r))
        U=U.transpose(np.argsort(ODD+EVEN))
        print(' rkB',rk(flat(T,B,AC,N)),'rkM',rk(M(T,N)),'<=',N*r,'| rkCol',rk(flat(U,ODD,EVEN,N)),'rkM',rk(M(U,N)),'<=',N*r)
print("(b) level counts")
# lossy-diagonal lemma, no merges: given 2-labellings sR (rows), sC (cols), each crossing edge of each
# rectangle is (free | (1,0) | (0,1) | (1,1) | (2,0)/(0,2)); maximise e - max(sR,sC) over the subset.
import itertools
from fractions import Fraction
def edge_costs(sR,sC,r1,c1,r2,c2):
    # legs l1 at (r1,c1), l2 at (r2,c2); orientation l1 in X(=0), l2 in Y(=1) or reversed
    best=[]
    for (a,b) in [((r1,c1),(r2,c2)),((r2,c2),(r1,c1))]:
        rl=(sR[a[0]]!=0)+(sR[b[0]]!=1); cl=(sC[a[1]]!=0)+(sC[b[1]]!=1)
        best.append((rl,cl))
    return best
def optimum(g_r,g_c,rects,sR,sC):
    # count edges by available cost options, then optimise via small enumeration
    from collections import Counter
    cnt=Counter()
    for (r1,r2,c1,c2) in rects:
        for (p,q) in [((r1,c1),(r2,c2)),((r1,c2),(r2,c1))]:
            opts=frozenset(edge_costs(sR,sC,p[0],p[1],q[0],q[1]))
            cnt[opts]+=1
    free=sum(v for k,v in cnt.items() if (0,0) in k)
    n10=sum(v for k,v in cnt.items() if (1,0) in k and (0,0) not in k)
    n01=sum(v for k,v in cnt.items() if (0,1) in k and (0,0) not in k and (1,0) not in k)
    n20=sum(v for k,v in cnt.items() if k=={(2,0),(0,2)})
    best=None
    for a in range(n10+1):
        for b in range(n01+1):
            for c in range(n20+1):
                for d in range(n20-c+1):
                    e=free+a+b+c+d; v=e-max(a+2*c,b+2*d)
                    if best is None or v>best[0]: best=(v,a,b,c,d)
    return best,free,n10,n01,n20
def grid(g):
    return [(r1,r2,c1,c2) for r1,r2 in itertools.combinations(range(g),2) for c1,c2 in itertools.combinations(range(g),2)]
for g in [3,4,5,6]:
    rects=grid(g); Q=len(rects); bestall=None
    labs=list(itertools.product([0,1],repeat=g))
    if g<=5:
        for sR in labs:
            for sC in labs:
                o=optimum(g,g,rects,sR,sC)[0][0]
                if bestall is None or o>bestall[0]: bestall=(o,sR,sC)
    h=g//2
    bal=tuple([0]*h+[1]*(g-h))
    ob=optimum(g,g,rects,bal,bal)
    print('g',g,'Q',Q,'balanced: e-s =',ob[0][0],'ratio',Fraction(ob[0][0],Q),'(free,n10,n01,n20)',ob[1:],
          '| best over all labellings',bestall[0] if bestall else None)
    if g%2==0: print('   closed form 3h^4-2h^3 =',3*h**4-2*h**3)
# 3x2 grid without merges
rects=[(0,1,0,1),(0,2,0,1),(1,2,0,1)]
b=max(optimum(3,2,rects,sR,sC)[0][0] for sR in itertools.product([0,1],repeat=3) for sC in itertools.product([0,1],repeat=2))
print('3x2 no-merge best',b)
