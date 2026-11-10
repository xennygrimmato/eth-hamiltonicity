#!/usr/bin/env python3
"""Pin r(1)=0 exactly for the explicit 5-term kernel by solving for a2 (others fixed); report value and r(1)."""
import numpy as np
from scipy.optimize import brentq
c = 1.5; gx, gw = np.polynomial.legendre.leggauss(120)
def r_of(co, a):
    f = lambda u: co[0]+co[1]*np.cos(2*np.pi*u/c)+co[2]*np.cos(4*np.pi*u/c)+co[3]*np.sin(2*np.pi*u/c)+co[4]*np.sin(4*np.pi*u/c)
    a = np.abs(np.atleast_1d(a)); lo = -c/2; hi = c/2-a
    U = (hi-lo)[:, None]/2*gx[None, :]+(hi+lo)[:, None]/2
    return np.where(hi > lo, (hi-lo)/2*(gw[None, :]*f(U)*f(U+a[:, None])).sum(1), 0.0)
base = [2/3, 0.53044, None, 0.347412, -0.178443]
g = lambda a2: r_of([base[0], base[1], a2, base[3], base[4]], 1.0)[0]
a2 = brentq(g, -0.14, -0.13, xtol=1e-15)
co = np.array([base[0], base[1], a2, base[3], base[4]])
ga = 0.5*gx+0.5
val = 2-(r_of(co, 0)[0]+2*0.5*np.sum(gw*ga*r_of(co, ga)))/(co[0]*c)**2
A1 = np.linspace(1, c, 4001); A0 = np.linspace(0, 1, 4001)
print(f"a2 = {a2:.12f}; r(1) = {g(a2):+.2e}; value {val:.6f}; max r on [1,c] {r_of(co,A1).max():+.2e}; min r on [0,1] {r_of(co,A0).min():+.2e}")
SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"
np.save(SP+"k5_final_coef.npy", co)
for N in (16, 32):
    rl = r_of(co, np.arange(N)/N)/(N*(co[0]*c)**2); np.savez(SP+f"k5f_{N}.npz", c0=2-N*rl[0], a=2*rl[1:]/N)
