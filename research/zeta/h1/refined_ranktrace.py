#!/usr/bin/env python3
"""(1) Random test of the exact identity [R]
   rank P = 2 tr P + 4 tr Q - 4 b_+ - ||P+Q||^2 + D,
   D = ||P - Q_- - Pi||^2 + ||Q_+ - 2 Pi_+||^2 + 2 tr(P Q_+) + 4 tr Q_- - 2 tr(Pi Q_-),
   and of D >= sum_i phi(p_i - 1)  (phi(a)=a^2 for a<=1, 2a-1 for a>1; p_i nonzero eigenvalues of P),
   and of pinching: sum phi(eig(Gamma)-1) >= sum over diagonal blocks.
(2) Energy constants for the Montgomery-Taylor kernel kappa(x)=psihat(2 pi x)/psihat(0), psi=cos(a s) on [-1/2,1/2],
   x in units of the mean zero spacing.  mu3(U) = min over 3 points of diameter <= U of sum phi(eig-1).
"""
import numpy as np
rng=np.random.default_rng(1)
phi=lambda a: np.where(a<=1,a*a,2*a-1)
def test(n=12,r=5,trials=2000):
    worst=0;w2=1e9;w3=1e9
    for _ in range(trials):
        V=rng.normal(size=(n,r))*rng.uniform(.2,1.5); P=V@V.T
        A=rng.normal(size=(n,n)); Q=(A+A.T)/2*rng.uniform(.1,2)
        w,U=np.linalg.eigh(Q); Qp=(U*np.maximum(w,0))@U.T; Qm=(U*np.maximum(-w,0))@U.T
        bp=(w>1e-12).sum(); Pip=(U[:,w>1e-12])@(U[:,w>1e-12]).T
        p,W=np.linalg.eigh(P); Wr=W[:,p>1e-10]; Pi=Wr@Wr.T; rk=Wr.shape[1]
        D=np.sum((P-Qm-Pi)**2)+np.sum((Qp-2*Pip)**2)+2*np.trace(P@Qp)+4*np.trace(Qm)-2*np.trace(Pi@Qm)
        rhs=2*np.trace(P)+4*np.trace(Q)-4*bp-np.sum((P+Q)**2)+D
        worst=max(worst,abs(rk-rhs)); w2=min(w2,D-phi(p[p>1e-10]-1).sum())
        # pinching
        m=6; X=rng.normal(size=(m,3)); X/=np.linalg.norm(X,axis=1)[:,None]*rng.uniform(.8,1.0); G=X@X.T; np.fill_diagonal(G,1.0)
        G=(G+G.T)/2
        if np.linalg.eigvalsh(G).min()<-1e-12: continue
        full=phi(np.linalg.eigvalsh(G)-1).sum(); blk=sum(phi(np.linalg.eigvalsh(G[i:i+2,i:i+2])-1).sum() for i in (0,2,4))
        w3=min(w3,full-blk)
    print("identity max err",worst,"; min(D - sum phi)=",w2,"; min(pinch full-block)=",w3)
def kappa(x,a=np.sqrt(2)):
    u=2*np.pi*np.asarray(x,float)
    f=lambda v: np.where(np.abs(v)<1e-9,0.5,np.sin(v/2)/np.where(np.abs(v)<1e-9,1,v))
    return (f(u-a)+f(u+a))/(2*np.sin(a/2)/a)
def e3(g1,g2,a):
    k1,k2,k12=kappa(g1,a),kappa(g2,a),kappa(g1+g2,a)
    G=np.array([[1,k1,k12],[k1,1,k2],[k12,k2,1]]); return phi(np.linalg.eigvalsh(G)-1).sum()
def R(a): return 0.5+ (a/2)/np.tan(a/2)*0+ ( (0.5+np.sin(a)/(2*a)) + None ) if False else None
def Rnum(a,n=2000):
    h=1/n; s=(np.arange(n)+.5)*h-.5; p=np.cos(a*s); D=np.abs(s[:,None]-s[None,:])
    return (h*(p*p).sum()+h*h*p@D@p)/(h*p.sum())**2
if __name__=='__main__':
    test()
    a=np.sqrt(2); xs=np.linspace(0.3,6,57001); k=kappa(xs,a); z=xs[:-1][np.sign(k[:-1])!=np.sign(k[1:])]
    print("MT kernel zeros (spacing units):",np.round(z,4)); print("R(MT) num",Rnum(a))
    x0=2-Rnum(a)
    for U in [3.2,3.5,4,5,6,8]:
        best=1e9;arg=None
        gs=np.linspace(0.02,U,int(U*150))
        for g1 in gs:
            g2=gs[gs<=U-g1+1e-12]
            if len(g2)==0: continue
            k1=kappa(g1,a);k2=kappa(g2,a);k12=kappa(g1+g2,a)
            v=2*(k1**2+k2**2+k12**2)   # = sum phi when eigenvalues<=2 ; near-min region has small kappas
            i=v.argmin()
            if v[i]<best: best=v[i];arg=(g1,g2[i])
        ex=e3(arg[0],arg[1],a)
        nblk=(x0-2/U)/3
        print(f"U={U}: mu3~{best:.3e} at gaps {arg} exact phi-sum {ex:.3e}; blocks/N >= {nblk:.4f}; delta >= {nblk*ex:.3e}")
