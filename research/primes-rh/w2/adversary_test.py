# Sanity test of the generalized adversary (Prop. G): for q arbitrary parity queries Q_j on [x,2x],
# there is R with |R|<=q+#forced such that S = P xor R has all queried parities even and excludes forced points.
import numpy as np, random
from sieve import seg_isprime
def gf2_small_solution(A,b):
    # A: q x U (uint8), solve A r = b over GF(2); return basic solution (support <= rank)
    A=A.copy()%2; b=b.copy()%2; q,U=A.shape; piv=[]; r=0
    for c in range(U):
        rows=np.nonzero(A[r:,c])[0]
        if len(rows)==0: continue
        i=r+rows[0]; A[[r,i]]=A[[i,r]]; b[[r,i]]=b[[i,r]]
        for k in range(q):
            if k!=r and A[k,c]: A[k]^=A[r]; b[k]^=b[r]
        piv.append(c); r+=1
        if r==q: break
    if np.any(b[r:]): return None
    sol=np.zeros(U,dtype=np.uint8)
    for k,c in enumerate(piv): sol[c]=b[k]
    return sol
random.seed(1)
for trial in range(20):
    x=random.randint(10**5,10**6); U=x+1; P=seg_isprime(x,2*x+1).astype(np.uint8)
    q=random.randint(5,60)
    Q=np.zeros((q,U),dtype=np.uint8)
    for j in range(q):
        kind=random.choice(['interval','ap','random'])
        if kind=='interval':
            a=random.randint(0,U-1); bb=random.randint(a,U-1); Q[j,a:bb+1]=1
        elif kind=='ap':
            m=random.randint(2,50); r0=random.randint(0,m-1); Q[j,r0::m]=1
        else: Q[j]=np.random.randint(0,2,U)
    forced=[random.randint(0,U-1) for _ in range(3)]  # output y + membership points must be absent
    # constraints: <S,Q_j>=0 where S=P^R  ->  <R,Q_j> = <P,Q_j>;  S_u=0 -> R_u=P_u
    F=np.zeros((len(forced),U),dtype=np.uint8)
    for i,u in enumerate(forced): F[i,u]=1
    A=np.vstack([Q,F]); b=np.concatenate([(Q.astype(np.int64)@P)%2, P[forced]]).astype(np.uint8)
    R=gf2_small_solution(A,b); S=P^R
    ok=np.all((Q.astype(np.int64)@S)%2==0) and np.all(S[forced]==0)
    gaps=np.diff(np.nonzero(S)[0]).max(); gp=np.diff(np.nonzero(P)[0]).max()
    print(f"x={x} q={q} |R|={R.sum()} ok={ok} maxgap S={gaps} P={gp}")
