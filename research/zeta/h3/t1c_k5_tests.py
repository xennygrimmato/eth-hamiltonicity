#!/usr/bin/env python3
"""Tests for an explicit kernel f (5 trig coefficients, c): rounding check, periodic certificate files, cell criterion R4(y)."""
import numpy as np, sys
c = 1.5; co = np.array([float(v) for v in sys.argv[1:6]])
SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"
gx, gw = np.polynomial.legendre.leggauss(80)
f = lambda u: co[0]+co[1]*np.cos(2*np.pi*u/c)+co[2]*np.cos(4*np.pi*u/c)+co[3]*np.sin(2*np.pi*u/c)+co[4]*np.sin(4*np.pi*u/c)
def r(a):
    a = np.abs(np.atleast_1d(a)); lo = -c/2; hi = c/2-a
    U = (hi-lo)[:, None]/2*gx[None, :]+(hi+lo)[:, None]/2
    return np.where(hi > lo, (hi-lo)/2*(gw[None, :]*f(U)*f(U+a[:, None])).sum(1), 0.0)
intf = co[0]*c; ga = 0.5*gx+0.5
val = 2-(r(0)[0]+2*0.5*np.sum(gw*ga*r(ga)))/intf**2
A1 = np.linspace(1, c, 2001); A0 = np.linspace(0, 1, 2001)
print(f"value {val:.6f}; max r on [1,c] {r(A1).max():+.3e}; min r on [0,1] {r(A0).min():+.3e}")
for N in (16, 32):
    rl = r(np.arange(N)/N)/(N*intf**2); np.savez(SP+f"k5r_{N}.npz", c0=2-N*rl[0], a=2*rl[1:]/N)
# continuum kernels by quadrature in alpha (normalised so K(0)=int r=1)
na = 1200; aa = np.linspace(-c, c, na+1); wa = np.full(na+1, aa[1]-aa[0]); wa[0] = wa[-1] = wa[0]/2
ra = r(aa)/intf**2; in1 = np.abs(aa) <= 1
xs = np.linspace(-15.5, 15.5, 12401)
CS = np.cos(2*np.pi*np.outer(xs, aa))
Kt = CS @ (wa*ra); K1t = CS @ (wa*ra*in1); K10 = np.sum(wa*ra*in1)
print(f"K(0)={np.interp(0,xs,Kt):.5f} min K = {Kt.min():+.3e} at {xs[Kt.argmin()]:.3f};  K1(0)={K10:.5f}")
def R4(y):
    Gt = CS @ (wa*ra*in1*np.cosh(2*np.pi*aa*y)) - K1t + Kt
    selfy = 2*(np.sum(wa*ra*in1*np.cosh(4*np.pi*aa*y))-K10)
    neg = Gt < 0; idx = np.where(neg)[0]; H = 0.0; groups = []
    if len(idx):
        s = idx[0]; p = idx[0]
        for i in idx[1:]:
            if i != p+1: groups.append((s, p)); s = i
            p = i
        groups.append((s, p))
    for s, e in groups:
        g = -Gt[s:e+1].min(); kap = min(1.0, np.interp(xs[e]-xs[s], xs, Kt)); Ms = np.arange(2, 2000)
        H += -min(-8*g, (kap*(Ms**2-2*Ms)-4*g*Ms).min())
    return H/selfy, len(groups), selfy
for y in [0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.5, 2.0, 3.0]:
    v, ng, se = R4(y); print(f"  y={y:5.3f} self={se:.3e} cells={ng:3d} R4={v:.4f}", flush=True)
