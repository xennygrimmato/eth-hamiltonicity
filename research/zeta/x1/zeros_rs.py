# fast zeros of Z(t) by Riemann-Siegel (C0,C1 corrections) + vectorised bisection; check vs mpmath.
import numpy as np, mpmath
def theta(t): return t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)+7/(5760*t**3)
def C0(p): 
    p=np.where(np.abs(np.cos(2*np.pi*p))<1e-7,p+1e-7,p)
    return np.cos(2*np.pi*(p*p-p-1/16))/np.cos(2*np.pi*p)
def C1(p,h=1e-3):
    d3=(C0(p+2*h)-2*C0(p+h)+2*C0(p-h)-C0(p-2*h))/(2*h**3)
    return -d3/(96*np.pi**2)
def Z(t):
    t=np.asarray(t,float); a=np.sqrt(t/(2*np.pi)); N=np.floor(a).astype(int); p=a-N
    th=theta(t); s=np.zeros_like(t)
    for n in range(1,N.max()+1):
        s+=np.where(n<=N, np.cos(th-t*np.log(n))/np.sqrt(n),0)
    R=(-1.0)**(N-1)*(t/(2*np.pi))**-0.25*(C0(p)+C1(p)*(t/(2*np.pi))**-0.5)
    return 2*s+R
if __name__=="__main__":
    t=np.arange(700.0,4000.0,0.004); z=Z(t)
    i=np.nonzero(z[:-1]*z[1:]<0)[0]; lo=t[i]; hi=t[i+1]; flo=z[i]
    for _ in range(40):
        mid=(lo+hi)/2; fm=Z(mid); left=fm*flo>0
        lo=np.where(left,mid,lo); flo=np.where(left,fm,flo); hi=np.where(left,hi,mid)
    g=(lo+hi)/2
    Nt=lambda T: T/(2*np.pi)*np.log(T/(2*np.pi*np.e))+7/8
    print("found",len(g),"expected N(4000)-N(700)=",Nt(4000)-Nt(700))
    mpmath.mp.dps=20
    # index check: zetazero(1000)=1419.42248...
    for n in [1000,2000]:
        ex=float(mpmath.zetazero(n).imag); j=np.argmin(abs(g-ex)); print(n,ex,g[j],g[j]-ex)
    np.save("zeros.npy",g)
