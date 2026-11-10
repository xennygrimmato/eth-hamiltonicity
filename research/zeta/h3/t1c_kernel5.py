#!/usr/bin/env python3
"""T1c: the explicit 5-parameter kernel (h3).  f(u) = a0 + a1 cos(2 pi u/c) + a2 cos(4 pi u/c) + b1 sin(2 pi u/c) + b2 sin(4 pi u/c)
on [-c/2,c/2], c = 3/2, r = f*f (autocorrelation), K = r^ = |f^|^2 >= 0.  Computes: value (accurate quadrature), sign of r on [0,1] and
[1,c], tail tau, periodic certificate files for t1b_check_cert.py, and the cell criterion R4(y) for the one-body inequality (*)."""
import numpy as np, sys
c = 1.5; co = np.array([0.6667, 0.5327, -0.1389, 0.3432, -0.1766]) if len(sys.argv) < 6 else np.array([float(v) for v in sys.argv[1:6]])
def f(u): return (co[0]+co[1]*np.cos(2*np.pi*u/c)+co[2]*np.cos(4*np.pi*u/c)+co[3]*np.sin(2*np.pi*u/c)+co[4]*np.sin(4*np.pi*u/c))*(np.abs(u) <= c/2)
# Gauss-Legendre autocorrelation r(a) = int f(u) f(u+a) du over overlap
gx, gw = np.polynomial.legendre.leggauss(80)
def r(a):
    a = np.atleast_1d(np.abs(a)); out = np.zeros_like(a, dtype=float)
    for i, al in enumerate(a):
        lo, hi = -c/2, c/2-al
        if hi > lo:
            u = (hi-lo)/2*gx+(hi+lo)/2; out[i] = (hi-lo)/2*np.sum(gw*f(u)*f(u+al))
    return out
I1 = np.sum(gw*0.5*f(0.5*gx+0.5)*1)  # unused
intf = c/2*np.sum(gw*f(c/2*gx))
r0 = r(0)[0]
ga = 0.5*gx+0.5; m1 = 0.5*np.sum(gw*ga*r(ga))
val = 2-(r0+2*m1)/intf**2
al = np.linspace(0, c, 1501); ra = r(al)
print(f"coef {co}; int f = {intf:.6f}; value 2-[r(0)+2 int_0^1 a r]/(int f)^2 = {val:.6f}")
print(f"min r on [0,1] = {ra[al<=1].min():+.3e};  max r on [1,c] = {ra[al>=1].max():+.3e} (must be <=0);  tau = {-2*np.trapezoid(ra[al>=1], al[al>=1])/intf**2:.5f}")
# periodic certificate (exact on real configs by Poisson): r_l = r(l/N)/(N (int f)^2), c0 = 2 - N r_0, a_l = 2 r_l/N
SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"
for N in (16, 32):
    rl = r(np.arange(N)/N)/(N*intf**2)
    np.savez(SP+f"k5_{N}.npz", c0=2-N*rl[0], a=2*rl[1:]/N)
    print(f"  periodic N={N}: certificate value {2-N*rl[0]-(2/N)*np.sum(rl[1:]*np.arange(1,N)):.6f}  -> {SP}k5_{N}.npz")
