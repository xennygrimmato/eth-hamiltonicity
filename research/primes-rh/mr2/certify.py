# Verify the numerical constants used in Theorem A (notebook.md).
import numpy as np, json, mpmath as mp
mp.mp.dps=30
print("== (1) Gamma kernel K(s)=Gamma(s+1/2), Ktilde(u)=sqrt(u)e^{-u} (LLS 6.3) ==")
Cg=mp.quad(lambda t: mp.sqrt(mp.pi/mp.cosh(mp.pi*t)),[-mp.inf,0,mp.inf])/(2*mp.pi)   # |Gamma(1/2+it)|^2=pi/cosh(pi t)
print("C_Gamma=(1/2pi)int|Gamma(1/2+it)|dt =",Cg)
# in LLS normalisation: A=1-e^{-lam}, B=1 ; sqrt(X)(h A - B) <= sqrt(lam) C * Sigma
def alpha(h,lam): return lam*Cg**2*(h-1)**2/(h*(1-mp.e**(-lam))-1)**2
for h,l0 in [(2,2.452),(3,2.025),(4,1.825)]:
    lam=mp.findroot(lambda l: mp.diff(lambda x: alpha(h,x),l),l0)
    print(f"alpha_Gamma({h}) = {mp.nstr(alpha(h,lam),8)} at lambda={mp.nstr(lam,6)}  (LLS: 0.794,0.7,0.66)")
f4=lambda lam: 4*lam*Cg**2/(4*(1-mp.e**(-lam))-1)**2     # Carmichael-3: Sigma=2 log n, h=4
lam=mp.findroot(lambda l: mp.diff(f4,l),1.8); print("Carm3 constant (Gamma) = 4 lam C^2/(4(1-e^-lam)-1)^2 =",mp.nstr(f4(lam),8),"at lambda",mp.nstr(lam,6))
finf=lambda lam: lam*Cg**2/(1-mp.e**(-lam))**2
lam=mp.findroot(lambda l: mp.diff(finf,l),1.26); print("alpha_Gamma(inf) =",mp.nstr(finf(lam),8),"at lambda",mp.nstr(lam,6)," ; x 4/9 =",mp.nstr(finf(lam)*4/9,8))
print("alpha_Gamma(2)/4 =",mp.nstr(alpha(2,mp.mpf('2.452'))/4,8),"  e^-2 =",mp.nstr(mp.e**-2,8))
print("== (2) triangle kernel (LLS 6.2), h=inf: alpha = (alpha/(2(alpha-1+e^-alpha)))^2 ==")
for a in [5,10,20,40]: print(a, mp.nstr((a/(2*(a-1+mp.e**(-a))))**2,6), " x4/9:",mp.nstr((a/(2*(a-1+mp.e**(-a))))**2*4/9,6))
print("== (3) spline kernels from kernels.json (g piecewise linear, compact support) ==")
from kernel_opt import PQ_weights
K=json.load(open('kernels.json'))
def cert(name):
    d=K[name]; knots=np.array(d['knots']); g=np.array(d['g']); dt=knots[1]-knots[0]
    assert g.min()>=0 and g[0]==0 and g[-1]==0
    wP,wQ=PQ_weights(knots); P=wP@g; Q=wQ@g
    gp=np.concatenate([[0],g,[0]]); ds=(gp[2:]-2*gp[1:-1]+gp[:-2])/dt; S1=np.abs(ds).sum()
    Tm=4000.0; step=0.002; tot=0.0
    # small tau: direct formula is ill-conditioned; use tau>=0.01 with formula, [0,0.01] bounded by |ghat|<=int g
    intg=np.trapezoid(g,knots)
    tot+=0.01*intg
    t0=0.01
    while t0<Tm:
        taus=np.arange(t0,min(t0+50,Tm)+step/2,step)
        gh=-(np.exp(1j*np.outer(taus,knots))@ds)/taus**2
        tot+=np.trapezoid(np.abs(gh),taus); t0+=50
    Cup=(2*tot+2*S1/Tm)/(2*np.pi)
    return P,Q,Cup
for name in K:
    h=float(name.split('_')[0]); P,Q,C=cert(name)
    if h==2: print(name,"P,Q,C=",P,Q,C," alpha(2)=(C/(P-Q))^2=",(C/(P-Q))**2,"  /4 =",(C/(P-Q))**2/4)
    elif h==4: print(name,"P,Q,C=",P,Q,C," R_4=",(3*P-Q)/C," Carm3 const 4/R_4^2=",4*C*C/(3*P-Q)**2, " alpha(2) with this kernel:",(C/(P-Q))**2 if P>Q else None)
    else: print(name,"P,Q,C=",P,Q,C," alpha(inf)=(C/P)^2=",(C/P)**2," x4/9=",(C/P)**2*4/9, " h0 for 1% loss: Q/(0.005P)=",Q/(0.005*P))
