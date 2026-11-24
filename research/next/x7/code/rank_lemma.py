"""Numerical test of two flattening-rank inequalities for 4-party tensors T[a,b,c,d]:
 (L1) rank(a|bcd) <= rank(ab|cd) * rank(ac|bd)
 (L2) rank(ad|bc) <= rank(ab|cd) * rank(ac|bd)   ('pairing triangle inequality')
Search: alternating projections onto {rank(ab|cd)<=r1} and {rank(ac|bd)<=r2} from random starts,
then report the numerical ranks of a|bcd and ad|bc of the limit point."""
import numpy as np, sys
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def trunc(M,r):
    U,s,Vh=np.linalg.svd(M,full_matrices=False); s[r:]=0; return (U*s)@Vh
def rk(M,tol=1e-7):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*s[0]).sum())
def test(da,db,dc,dd,r1,r2,iters=3000):
    T=rng.normal(size=(da,db,dc,dd))
    for it in range(iters):
        T=trunc(T.reshape(da*db,dc*dd),r1).reshape(da,db,dc,dd)
        P=T.transpose(0,2,1,3).reshape(da*dc,db*dd)
        T=trunc(P,r2).reshape(da,dc,db,dd).transpose(0,2,1,3)
        T/=np.linalg.norm(T)
    s1=np.linalg.svd(T.reshape(da*db,-1),compute_uv=False)
    res=s1[r1:].sum()/s1.sum()
    ra=rk(T.reshape(da,-1)); rad=rk(T.transpose(0,3,1,2).reshape(da*dd,-1))
    return res,ra,rad
worst1=worst2=0
for (da,db,dc,dd,r1,r2) in [(6,2,2,2,2,2),(8,2,2,3,2,2),(4,2,2,4,2,3),(9,3,3,1,3,3),(6,3,3,2,2,3),(5,5,5,5,3,3),(4,4,4,4,2,2),(4,4,4,4,4,2)]:
    for rep in range(4):
        res,ra,rad=test(da,db,dc,dd,r1,r2)
        if res<1e-9:
            worst1=max(worst1,ra/(r1*r2)); worst2=max(worst2,rad/(r1*r2))
        print((da,db,dc,dd,r1,r2),"resid %.1e"%res,"rank(a)",ra,"rank(ad|bc)",rad,"bound",r1*r2)
print("max ratio L1",worst1,"L2",worst2)
