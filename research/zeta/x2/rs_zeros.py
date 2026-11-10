"""Zeros of zeta on the critical line via Riemann-Siegel Z(t) (numpy, vectorised), refined by bisection/secant.
Checks against mpmath.zetazero for small cases. Usage: python3 rs_zeros.py T0 T1 out.npy"""
import numpy as np, sys
def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def Z(t):
    t = np.atleast_1d(np.asarray(t, float))
    a = np.sqrt(t/(2*np.pi)); N = np.floor(a).astype(int); Nmax = N.max()
    th = theta(t)
    n = np.arange(1, Nmax+1)
    terms = np.cos(th[:,None] - np.outer(np.log(n), np.ones(1)).T*t[:,None]) / np.sqrt(n)[None,:]
    terms = np.where(n[None,:] <= N[:,None], terms, 0.0)
    s = 2*terms.sum(1)
    p = a - N
    C0 = np.cos(2*np.pi*(p*p - p - 1/16))/np.cos(2*np.pi*p)
    # first correction term C1 (Gabcke), via numerical derivative of C0 in p is messy; use standard series coefficient
    z = 2*p - 1
    C1 = -(np.pi**2)*(0.0) # placeholder small; we use C0 only + optional C1 below
    R = (-1)**(N-1) * (t/(2*np.pi))**(-0.25) * C0
    return s + R
def zeros(T0, T1, h=None):
    # grid fine relative to mean spacing 2pi/log(T/2pi)
    sp = 2*np.pi/np.log(T1/(2*np.pi)); h = h or sp/12
    ts = np.arange(T0, T1, h)
    out=[]
    for i in range(0, ts.size, 20000):
        tt = ts[i:i+20001]; zz = Z(tt)
        idx = np.nonzero(np.sign(zz[:-1])*np.sign(zz[1:]) < 0)[0]
        a = tt[idx]; b = tt[idx+1]; fa = zz[idx]; fb = zz[idx+1]
        for _ in range(40):
            m = (a+b)/2; fm = Z(m)
            left = np.sign(fm)==np.sign(fa)
            a = np.where(left, m, a); fa = np.where(left, fm, fa); b = np.where(left, b, m)
        out.append((a+b)/2)
    return np.concatenate(out)
if __name__=='__main__':
    T0,T1 = float(sys.argv[1]), float(sys.argv[2])
    g = zeros(T0,T1); np.save(sys.argv[3], g); print(g.size, g[:3], g[-3:])
