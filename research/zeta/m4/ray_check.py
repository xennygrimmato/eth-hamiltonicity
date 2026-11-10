#!/usr/bin/env python3
"""m4: explicit deep-cluster rays against a saved 3-point dual certificate (h1/ceiling_deep.py model, N=8).
Configuration: k=N/2 off-line pairs, no on-line zeros (cost 0). Outer points v_i = R w_i (R = e^{2 pi Y/N}),
w chosen so that the power sums q_l = sum w_i^l vanish for s0 < l <= N-1 and q_{s0} = eta*e^{i phi} (eta ~ 1/R).
Then the leading features are the 3-point rows with a+b = s0, of either sign (phi), all else lower order.
Prints min over phi of (cost - c0 - lam.f): negative => the certificate is violated (the LP value at finite depth is not the depth->inf ceiling)."""
import sys, numpy as np
from scipy.optimize import least_squares
N=8; dual=np.load(sys.argv[1]); SMIN=int(sys.argv[2]) if len(sys.argv)>2 else 2
R=[('2',l) for l in range(1,N)]+[('3',a,b) for a in range(1,N) for b in range(a,N) if SMIN<=a+b<=N-1]
assert len(dual)==1+len(R), (len(dual),len(R))
c0=dual[0]; lam=dual[1:]
scale=np.array([max(float(r[1]),1.0) if r[0]=='2' else float(N) for r in R]); l=np.arange(0,N)
i2=np.array([r[1] for r in R if r[0]=='2']); A3=np.array([r[1] for r in R if r[0]=='3'],int); B3=np.array([r[2] for r in R if r[0]=='3'],int)
def feats(t,y):
    W=2*np.cosh(2*np.pi*np.outer(y,l)/N); S=(W*np.exp(2j*np.pi*np.outer(t,l)/N)).sum(0)
    return np.concatenate([np.abs(S[i2])**2,(S[A3]*S[B3]*np.conj(S[A3+B3])).real])/scale
print("3-pt multipliers by a+b:",{s:np.round(lam[len(i2):][(A3+B3)==s],4).tolist() for s in sorted(set(A3+B3))})
rng=np.random.default_rng(1); k=N//2
for s0 in range(N-1,1,-1):
    best=np.inf
    for trial in range(40):
        def eqs(x, tgt):
            w=x[:k]+1j*x[k:]; q=np.array([np.sum(w**L) for L in range(s0,N)]); q=q-np.concatenate([[tgt],np.zeros(N-1-s0)])
            return np.concatenate([q.real,q.imag])
        x0=rng.normal(size=2*k)
        sol=least_squares(eqs,x0,args=(0.0,),xtol=1e-15,ftol=1e-15,gtol=1e-15)
        if np.max(np.abs(sol.fun))>1e-9: continue
        w0=sol.x[:k]+1j*sol.x[k:]
        if np.min(np.abs(w0))<0.3: continue
        for Y in (5.0,10.0,20.0):
            Rr=np.exp(2*np.pi*Y/N)
            for phi in np.linspace(0,2*np.pi,16,endpoint=False):
                eta=np.exp(1j*phi)/Rr
                s2=least_squares(eqs,np.concatenate([w0.real,w0.imag]),args=(eta,),xtol=1e-15,ftol=1e-15,gtol=1e-15)
                w=s2.x[:k]+1j*s2.x[k:]; v=Rr*w
                if np.min(np.abs(v))<=1: continue
                y=N*np.log(np.abs(v))/(2*np.pi); t=N*np.angle(v)/(2*np.pi)
                f=feats(t,y); rc=(0-c0-lam@f)/max(1.0,np.abs(f).max())
                best=min(best,rc)
    print(f"s0={s0}: min scaled reduced cost over explicit rays = {best:.3e}  ({'VIOLATED' if best<-1e-6 else 'ok'})")
