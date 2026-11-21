#!/usr/bin/env python3
"""How many zeta zeros does a truncated (Gaussian-smoothed) explicit formula need to
 (A) detect primes in a soft window of relative width sigma at x,
 (B) get the EXACT weighted prime-power count Q = sum_{x1<n<=x2} Lambda(n)/sqrt(n) (zone-corrected, Lagarias-Odlyzko style),
     and how the requirement changes if the count is only needed up to a tolerance M/2 (i.e. we already know it mod M).
Exact identity used (Weil explicit formula, g(u)=phi_s(u-L)+phi_s(u+L), h(r)=2cos(rL)exp(-s^2 r^2/2)):
 S(L) := sum_n Lambda(n) n^-1/2 phi_s(log n - L)
       = cosh(L/2)*2*exp(s^2/8)/... (see code)  - 2 sum_{gamma>0} cos(gamma L) exp(-s^2 gamma^2/2) + Gamma-term + O(tiny)
 E(L) := sum_n Lambda(n) n^-1/2 Phi_s(L - log n),  E' = S.
"""
import numpy as np, sys
from scipy.special import digamma, ndtr
zs=np.load("zeros.npy")
def sieve_lambda(a,b):
    """return arrays (n, Lambda(n)) for prime powers n in [a,b]"""
    import math
    r=int(math.isqrt(b))+1
    small=np.ones(r+1,bool); small[:2]=False
    for i in range(2,int(r**0.5)+1):
        if small[i]: small[i*i::i]=False
    ps=np.nonzero(small)[0]
    seg=np.ones(b-a+1,bool)
    for p in ps:
        s=max(p*p,(a+p-1)//p*p); seg[s-a::p]=False
    n=[np.nonzero(seg)[0]+a]; lam=[np.log(n[0].astype(float))]
    for p in ps:               # prime powers p^k, k>=2
        q=p*p
        while q<=b:
            if q>=a: n.append(np.array([q])); lam.append(np.array([np.log(p)]))
            q*=p
    n=np.concatenate(n); lam=np.concatenate(lam); o=np.argsort(n); return n[o],lam[o]
def gamma_term_S(L,s):
    # (1/2)*(1/2pi) int h(r) Re psi(1/4+ir/2) dr - (1/2) g(0) log pi ; h(r)=2cos(rL)exp(-s^2r^2/2)
    R=8.0/s; r=np.linspace(0,R,int(R*L*8)+1)
    f=2*np.cos(r*L)*np.exp(-s*s*r*r/2)*digamma(0.25+0.5j*r).real
    return 0.5*(2*np.trapezoid(f,r)/(2*np.pi))      # even integrand; g(0)~0
def S_zero_side(L,s,T,gt=None):
    g=zs[zs<=T]
    main=0.5*(2*2*np.cosh(L/2)*np.exp(s*s/8))       # (1/2)(h(i/2)+h(-i/2))
    zsum=0.5*(2*np.sum(2*np.cos(g*L)*np.exp(-s*s*g*g/2)))
    return main-zsum+(gt if gt is not None else 0.0)
def E_diff_zero_side(L1,L2,s,T):
    g=zs[zs<=T]
    main=4*(np.sinh(L2/2)-np.sinh(L1/2))*np.exp(s*s/8)
    zsum=2*np.sum(np.exp(-s*s*g*g/2)*(np.sin(g*L2)-np.sin(g*L1))/g)
    return main-zsum
if __name__=="__main__":
    x=float(sys.argv[1]) if len(sys.argv)>1 else 1e8
    print(f"zeros loaded: {len(zs)} up to {zs[-1]:.1f};  x={x:.3g}")
    # ---------- (A) soft window detection
    print("\n(A) soft window  S(L)=sum Lambda(n)/sqrt(n) phi_sigma(log n-L); unit = contribution of one prime at centre")
    for s in (2e-3,1e-3,6e-4):
        L=np.log(x); h=s*x; a=int(x*np.exp(-9*s)); b=int(x*np.exp(9*s))+1
        n,lam=sieve_lambda(a,b); ln=np.log(n.astype(float))
        exact=np.sum(lam/np.sqrt(n)*np.exp(-(ln-L)**2/(2*s*s))/(s*np.sqrt(2*np.pi)))
        unit=np.log(x)/np.sqrt(x)/(s*np.sqrt(2*np.pi))
        gt=gamma_term_S(L,s)
        print(f" sigma={s:g} (h=sigma*x={h:.3g}), exact S={exact:.6f} = {exact/unit:.2f} primes-equivalents, gamma-term={gt:.2e}")
        for k in (1,2,3,4,5,6,7):
            T=k/s
            if T>zs[-1]: break
            err=S_zero_side(L,s,T,gt)-exact
            print(f"   T={T:8.0f} (T*sigma={k}, #zeros={np.sum(zs<=T):6d})  err={err:+.3e} = {err/unit:+.3e} primes")
    # ---------- (B) exact count with zone correction; tolerance M/2
    print("\n(B) exact Q=sum_{x1<n<=x2} Lambda(n)/sqrt n via zeros<=T + sieved transition zones of half-width K*sigma*x")
    x1=x; x2=x*1.02
    K=8.0
    for s in (2e-3,1e-3,7e-4):
        L1,L2=np.log(x1),np.log(x2)
        # exact soft count E(L2)-E(L1) needs all n; get it from sharp count + zone corrections (what the algorithm does in reverse)
        za=[(int(xx*np.exp(-K*s)),int(xx*np.exp(K*s))+1) for xx in (x1,x2)]
        zone_cost=sum(b-a for a,b in za)
        corr=0.0
        for (a,b),Le,xe,sign in ((za[0],L1,x1,-1),(za[1],L2,x2,+1)):
            n,lam=sieve_lambda(a,b); w=lam/np.sqrt(n); ln=np.log(n.astype(float))
            soft=ndtr((Le-ln)/s); sharp=(n<=xe).astype(float)
            corr+=sign*np.sum(w*(soft-sharp))        # soft - sharp, edge by edge
        n,lam=sieve_lambda(int(x1)+1,int(x2)); Q=np.sum(lam/np.sqrt(n)); cnt=len(n)
        unit=np.log(x)/np.sqrt(x)
        print(f" sigma={s:g}: zone candidates sieved={zone_cost:.3g}; true Q={Q:.6f}; #prime powers in (x1,x2]={cnt}; one prime = {unit:.3e}")
        Ts=[k/s for k in (0.5,1,1.5,2,2.5,3,3.5,4,4.5,5,5.5,6,7,8) if k/s<=zs[-1]]
        errs=[]
        for T in Ts:
            est=E_diff_zero_side(L1,L2,s,T)-corr
            e=abs(est-Q)/unit; errs.append(e)
            print(f"   T={T:8.0f} (T*sigma={T*s:4.1f}, #zeros={np.sum(zs<=T):6d}): |error| = {e:10.3e} primes")
        for M in (1,2,4,16,256,int(np.sqrt(x)/np.log(x)),int(np.sqrt(x))):
            ok=[T for T,e in zip(Ts,errs) if e<M/2 and all(e2<M/2 for T2,e2 in zip(Ts,errs) if T2>=T)]
            print(f"   tolerance M/2 with M={M:6d}: smallest tested T that suffices = {ok[0] if ok else None}"
                  +(f"  -> T*zone/x = {ok[0]*zone_cost/x:.1f}" if ok else ""))
    # ---------- (C) does 'structure' on zeros substitute for their exact positions?
    print("\n(C) replace exact zeros by smooth-density approximants (Gram-like: N(g_n)=n-1/2) : error of S(L)")
    s=1e-3; L=np.log(x); T=6/s
    a=int(x*np.exp(-9*s)); b=int(x*np.exp(9*s))+1
    n,lam=sieve_lambda(a,b); ln=np.log(n.astype(float))
    exact=np.sum(lam/np.sqrt(n)*np.exp(-(ln-L)**2/(2*s*s))/(s*np.sqrt(2*np.pi)))
    unit=np.log(x)/np.sqrt(x)/(s*np.sqrt(2*np.pi))
    g=zs[zs<=T]
    Nsm=lambda t: t/(2*np.pi)*np.log(t/(2*np.pi*np.e))+7/8
    lo=np.full(len(g),10.0); hi=np.full(len(g),T+50.0); tgt=np.arange(1,len(g)+1)-0.5
    for _ in range(60):
        mid=(lo+hi)/2; m=Nsm(mid)<tgt; lo=np.where(m,mid,lo); hi=np.where(m,hi,mid)
    gs=(lo+hi)/2
    main=2*np.cosh(L/2)*np.exp(s*s/8)
    for name,gg in (("exact zeros",g),("smooth approximants",gs),("exact zeros + N(0,0.01^2) noise",g+0.01*np.random.default_rng(1).standard_normal(len(g))),
                    ("exact zeros + N(0,0.1^2) noise",g+0.1*np.random.default_rng(1).standard_normal(len(g))),("every 2nd zero x2",None)):
        if gg is None: zsum=2*2*np.sum(np.cos(g[::2]*L)*np.exp(-s*s*g[::2]**2/2))
        else: zsum=2*np.sum(np.cos(gg*L)*np.exp(-s*s*gg*gg/2))
        err=(main-zsum-exact)/unit
        print(f"   {name:34s}: error = {err:+10.3f} primes   (window holds {exact/unit:.1f} prime-equivalents; mean rms displacement {np.sqrt(np.mean((g-(gg if gg is not None else g))**2)):.3f})")
