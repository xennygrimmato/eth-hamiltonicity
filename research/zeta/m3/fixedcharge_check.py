"""m3: Fabbian barriers Lemma 4.3 necessary conditions (fixed-charge two-point class, Def 4.1) with K = 0,
for MT, h3's k5 and the 50/50 mixture.  (4.1): sum_{k!=0} max(s_k,u_k) <= self_t ;  (4.2) comb row: sum_{k!=0}(s_k + W_t(k)) <= eps_c.
s_k = sup_{J_k} (-W_t)_+ , u_k = 8 sup_{J_k} (-V_t)_+ , J_k=(k-1/2,k+1/2]. K=0 is only ONE member of the class (Fabbian's LP also
optimises a PD K with spectrum in [-3,3]); so a pass here is not feasibility of the class, a failure with K=0 is not infeasibility. [N]"""
import numpy as np
from fabbian_tests import make, A
def kernels(q,y,t,rs):
    g=np.where(A<=1,q,0); ob=q-g
    C=np.cos(2*np.pi*np.outer(rs,A))
    Rf=2*np.trapezoid(q*C,A,axis=1); OB=2*np.trapezoid(ob*C,A,axis=1)
    psi=2*np.trapezoid(g*(np.cosh(2*np.pi*y*A)-1)*C,A,axis=1)
    phi=4*2*np.trapezoid(g*(np.cosh(2*np.pi*y*A)**2-1)*C,A,axis=1)
    W=4*Rf+phi+(4-t*t)*OB; V=Rf+psi+(1-t/2)*OB
    U=2*np.trapezoid(ob,A)*(-1)  # int|q| off [-1,1] (q<=0 there)
    self_=4*2*np.trapezoid(g*(np.cosh(2*np.pi*y*A)**2-1),A)+(4-t*t)*U
    return W,V,self_
for name,e in [('MT',None),('k5',None),('mix',0.5)]:
    q=make(name,e); g0=q[0]; epsc=4*(g0-1)
    print("==",name, "eps_c=%.4f"%epsc)
    for y in [0.1,0.165,0.2,0.24,0.27,0.3,0.5]:
        best=None
        for t in np.linspace(0,2,11):
            rs=np.linspace(0.5,30.5,15001)
            W,V,self_=kernels(q,y,t,rs)
            k=np.clip(np.round(rs).astype(int),1,30)
            s=np.zeros(31); u=np.zeros(31)
            for kk in range(1,31):
                m=(k==kk); s[kk]=max(0,(-W[m]).max()); u[kk]=8*max(0,(-V[m]).max())
            lhs=2*np.maximum(s,u)[1:].sum()
            Wk=kernels(q,y,t,np.arange(1,31).astype(float))[0]
            comb=2*(s[1:]+Wk).sum()
            r=(lhs/self_, comb, t)
            if best is None or r[0]<best[0]: best=r
        print(f"  y={y}: best t={best[2]:.1f}: (4.1) ratio sum max(s,u)/self = {best[0]:.3f}  comb row lhs = {best[1]:+.4f} (needs <= eps_c={epsc:.4f})")
