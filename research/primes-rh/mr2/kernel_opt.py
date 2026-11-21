# Optimise LLS-type kernels.  g(t)=Ktilde(lambda e^t) >= 0, piecewise linear, compact support.
# P=int_{t<=0} g e^{t/2}, Q=int_{t>0} g e^{t/2}, C=(1/2pi) int |ghat|.
# Inequality (GRH): ((h-1)P - Q) sqrt(X) <= (1+o(1)) C * sum_{chi != 1} log cond(chi).
# R_h = ((h-1)P-Q)/C ; maximise.
import numpy as np, sys, json
from scipy.optimize import minimize
def setup(tl,tr,dt):
    knots=np.arange(tl,tr+1e-9,dt)   # must contain 0
    return knots
def PQ_weights(knots):
    # exact integrals of hat functions times e^{t/2} on t<=0 and t>0 (0 is a knot)
    n=len(knots); wP=np.zeros(n); wQ=np.zeros(n)
    # integral over [a,b] of (linear from ga at a to gb at b) e^{t/2}
    def seg(a,b):
        # returns coefficients (ca,cb): int = ca*ga+cb*gb
        L=b-a
        # int_a^b e^{t/2} (b-t)/L dt , int_a^b e^{t/2}(t-a)/L dt
        E=lambda t:2*np.exp(t/2)
        I0=E(b)-E(a)
        # int t e^{t/2} = 2 t e^{t/2} - 4 e^{t/2}
        F=lambda t:2*t*np.exp(t/2)-4*np.exp(t/2)
        I1=F(b)-F(a)
        return (b*I0-I1)/L,(I1-a*I0)/L
    for j in range(n-1):
        a,b=knots[j],knots[j+1]; ca,cb=seg(a,b)
        if b<=1e-12: wP[j]+=ca; wP[j+1]+=cb
        else: wQ[j]+=ca; wQ[j+1]+=cb
    return wP,wQ
def Cmat(knots,taus):
    # ghat(tau) = -(1/tau^2) sum_j ds_j e^{i tau t_j}; ds = second difference of g /dt
    return np.exp(1j*np.outer(taus,knots))
def run(h,tl=-14,tr=5,dt=0.25,init=None,quiet=False):
    knots=setup(tl,tr,dt); n=len(knots)
    wP,wQ=PQ_weights(knots)
    taus=np.concatenate([np.arange(0.005,60,0.01)]); dtau=0.01
    E=Cmat(knots,taus)
    D=np.zeros((n,n))  # slope change operator, with g=0 outside
    for j in range(n):
        D[j,j]=-2/dt
        if j>0: D[j,j-1]=1/dt
        if j<n-1: D[j,j+1]=1/dt
    M=-(E@D)/(taus[:,None]**2)   # ghat = M g
    def obj(v):
        g=v*v
        gh=M@g
        a=np.abs(gh)+1e-300
        S1=np.sum(np.abs(D@g))
        C=(2*np.sum(a)*dtau + 2*S1/60.0)/(2*np.pi)   # tail bound: int_{60}^inf S1/tau^2 = S1/60 (both sides)
        num=(h-1)*(wP@g)-(wQ@g) if h<1e8 else wP@g
        return -num/C
    if init is None:
        lam=1.8
        g0=np.exp(knots/2-lam*np.exp(knots)); g0[0]=0; g0[-1]=0
    else: g0=init
    v0=np.sqrt(g0)+1e-3
    best=None
    res=minimize(obj,v0,method='L-BFGS-B',options={'maxiter':4000,'maxfun':400000})
    g=res.x**2
    if not quiet: print('h=',h,'R_h=',-res.fun, 'const ((h-1)/R)^2=',((h-1)/(-res.fun))**2 if h<1e8 else (1/(-res.fun))**2)
    return knots,g,-res.fun
if __name__=='__main__':
    out={}
    for h in [2,3,4,8,1e9]:
        knots,g,R=run(h)
        # normalise and round to 6 digits for a reproducible certificate
        g=g/g.max(); g=np.round(g,5); g[0]=0; g[-1]=0
        out[str(int(h))]={'knots':knots.tolist(),'g':g.tolist(),'R_float':R}
    json.dump(out,open('kernels.json','w'))
