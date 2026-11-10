"""m3: apply Fabbian's necessary conditions / barrier witnesses (Zenodo 23198631) to OUR kernels.
Kernels (normalisation of Fabbian [20, Def 3.4]: q even, int q = 1, g = q 1_[-1,1], V(g)=g(0)+2 int_0^1 a g):
  k5  : h3's explicit kernel r = f*f~ on [-3/2,3/2] (h3/T1f_lemmaZ.md sec 5)
  MT  : Montgomery-Taylor r = psi*psi/(int psi)^2, psi = cos(sqrt2 s) on [-1/2,1/2]
  mix : (1-e) MT + e k5
Tests:
 (1) comb deficit eps_c = 4(g(0)-1)  [barriers Lemma 2.2(a)]: Phi(C_N)/(2N+1) -> eps_c for pairs k+-iy, ANY y>0.
     So (C) at any depth needs g(0) >= 1; block-sum (pair-by-pair) proofs need one-pair cost <= eps_c.
 (2) fractional chain (barriers Prop 3.3, period-2 limit): D(eps,y) = g(0)/2 (1+2eps)^2 + g(1/2)(1-2 eps cosh(pi y))^2 - 1 - 4eps^2;
     D<0 => homogeneous two-point (LP / Delsarte) certificates cannot prove (C) at common depth y (Thm 3.4 mechanism).
 (3) integer-triple chain (Remark 3.5): limit 25/2 g(0) - 13 at y*=arccosh(3/2)/pi (HOM fails if g(0) < 26/25).
 (4) one-pair-with-real-doubles F_2(X) (Thm 4.13 mechanism): min over X of 8 V_2(r_j) + 4 sum R_full(r_j-r_k), X = {+-r} or {+-r1,+-r2};
     compare with -eps_c (block sums excluded if min F < -eps_c).
 (5) removal witness (Prop 6.1): By(u) = 2 Re R_g(u+iy) < 0 somewhere -> deep pair next to M-fold real point.
"""
import numpy as np
from numpy.polynomial.legendre import leggauss
X,W = leggauss(400)
def quad(fun,a,b):
    x=(b-a)/2*X+(a+b)/2; return (b-a)/2*np.sum(W*fun(x))
c=[0.66666667,0.53044,-0.136227748726,0.347412,-0.178443]
def f5(u):
    u=np.asarray(u,float); w=np.pi*4*u/3
    v=c[0]+c[1]*np.cos(w)+c[2]*np.cos(2*w)+c[3]*np.sin(w)+c[4]*np.sin(2*w)
    return np.where(np.abs(u)<=0.75,v,0.0)
I5=quad(f5,-0.75,0.75)
def q_k5(a):  # autocorrelation int f(u) f(u+a) du, normalised so int q = 1
    a=np.atleast_1d(a); out=[]
    for aa in a:
        lo=max(-0.75,-0.75-aa); hi=min(0.75,0.75-aa)
        out.append(quad(lambda u: f5(u)*f5(u+aa),lo,hi) if hi>lo else 0.0)
    return np.array(out)/I5**2
psiI=quad(lambda s: np.cos(np.sqrt(2)*s),-.5,.5)
def q_MT(a):
    a=np.atleast_1d(a); out=[]
    for aa in a:
        lo=max(-.5,-.5-aa); hi=min(.5,.5-aa)
        out.append(quad(lambda s: np.cos(np.sqrt(2)*s)*np.cos(np.sqrt(2)*(s+aa)),lo,hi) if hi>lo else 0.0)
    return np.array(out)/psiI**2
# tabulate q on grid for transforms
A=np.linspace(0,1.5,3001)
tab={'k5':q_k5(A),'MT':q_MT(A)}
def make(name,e=None):
    if name=='mix': return (1-e)*tab['MT']+e*tab['k5']
    return tab[name]
def V(q): g=np.where(A<=1,q,0); return q[0]+2*np.trapezoid(A*g,A)
def Rg(q,z):  # R_g(z) = int_{-1}^1 g(a) e(z a) da, g even: 2 int_0^1 g cos(2 pi z a)
    g=np.where(A<=1,q,0); return 2*np.trapezoid(g*np.cos(2*np.pi*np.outer(np.atleast_1d(z),A)),A,axis=1)
def Rfull(q,x): return 2*np.trapezoid(q*np.cos(2*np.pi*np.outer(np.atleast_1d(x),A)),A,axis=1)
def g_at(q,a): return np.interp(a,A,q)
if __name__=='__main__':
    for name,e in [('MT',None),('k5',None),('mix',0.5)]:
        q=make(name,e); g0=q[0]; gh=g_at(q,0.5)
        print(f"== {name}{'' if e is None else ' eps='+str(e)}: int q={2*np.trapezoid(q,A):.6f}  value 2-V={2-V(q):.6f}  g(0)={g0:.6f}  g(1/2)={gh:.6f}  q(1)={g_at(q,1.0):.2e}")
        print(f"   (1) comb deficit eps_c=4(g0-1) = {4*(g0-1):+.5f}" + ("   <0 => (C) FALSE at every depth y>0!" if g0<1 else ""))
        # (2) fractional chain
        worst=[]
        for y in [0.02,0.04,0.055,0.06,0.1,0.2,0.3,0.4,0.5,0.6,0.8,1.0]:
            ch=np.cosh(np.pi*y); 
            # D = A2 e^2 + A1 e + A0
            A2=2*g0+4*gh*ch**2-4; A1=2*g0-4*gh*ch; A0=g0/2+gh-1
            es=np.linspace(0,3,30001); D=A0+A1*es+A2*es**2; i=np.argmin(D)
            worst.append((y,D[i],es[i]))
        print("   (2) fractional chain min_eps D(eps,y):", "  ".join(f"y={y}:{d:+.4f}(eps={ee:.2f})" for y,d,ee in worst))
        print(f"   (3) triple chain limit 25/2 g0 - 13 = {12.5*g0-13:+.4f}")
        # (4) one pair + real doubles, Fabbian V_t with t=2: V_2 = Rfull + psi_y = Re R_g(r+iy) - OB(r)... V_t=Rfull+psi_y+(1-t/2)OB
        g=np.where(A<=1,q,0)
        def ReRg_shift(r,y): return 2*np.trapezoid(g*np.cosh(2*np.pi*y*A)*np.cos(2*np.pi*np.outer(np.atleast_1d(r),A)),A,axis=1)
        rs=np.linspace(0.05,6,1200); Rf=Rfull(q,rs)
        out=[]
        for y in [0.032,0.05,0.1,0.2,0.3,0.5,1.0]:
            psi=ReRg_shift(rs,y)-Rg(q,rs)
            V2=Rf+psi   # t=2
            F1=16*V2+4*Rfull(q,2*rs)  # X={+r,-r}: 8V(r)+8V(-r)+4Rf(2r)*2
            F1=16*V2+8*Rfull(q,2*rs)
            i=np.argmin(F1); selfy=2*(Rg(q,[2j*y]).real if False else 2*np.trapezoid(g*np.cosh(4*np.pi*y*A),A)-Rg(q,[0])[0])
            out.append((y,F1[i],rs[i],selfy))
        print("   (4) min_X F_2(X), X={+-r} (vs -eps_c; self_2(y) for scale):", "  ".join(f"y={y}:{F:+.4f}@r={r:.2f}(self {s:.3f})" for y,F,r,s in out))
        # (5) removal witness
        mins=[]
        for y in [0.2,0.5,1.0]:
            By=2*ReRg_shift(rs,y); i=np.argmin(By); mins.append((y,By[i],rs[i]))
        print("   (5) min_u B_y(u):", "  ".join(f"y={y}:{b:+.4f}@u={u:.2f}" for y,b,u in mins))
