#!/usr/bin/env python3
"""Continuum-ish study of the CGdL data kernel K1(z) = sum_{|l|<N} r_l e^{i 2 pi l z/N} (alpha = l/N, mean spacing 1)
from the periodic CGdL LP at N (default 64): K1 >= 0 on R?  min_x Re K1(x+i eta) vs eta;  self terms."""
import sys, numpy as np
from scipy.optimize import linprog
N = int(sys.argv[1]) if len(sys.argv) > 1 else 64; M = 4*N; G = 30*M
th = np.linspace(0, np.pi, G); l = np.arange(M+1)
Cm = np.cos(np.outer(th, l)); Cm[:, 1:] *= 2
c = np.zeros(M+1); c[0] = N; c[1:N] = 2*np.arange(1, N)/N
bounds = [(None, None)]*(M+1)
for k in range(N, M+1): bounds[k] = (None, 0)
Aeq = np.ones((1, M+1)); Aeq[0, 1:] = 2
res = linprog(c, A_ub=-Cm, b_ub=np.zeros(G), A_eq=Aeq, b_eq=[1.0], bounds=bounds, method='highs')
r = res.x; val = 2-res.fun; tau = -2*r[N:].sum()
np.savez(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/cgdl_r_{N}.npz", r=r, N=N, val=val)
print(f"N={N}: CGdL value {val:.6f}; tau = int_{{|a|>1}}|r| = {tau:.5f}; K(0)=1, K1(0)=1+tau")
print("continuum r(alpha)=N*r_l at alpha=0,.1,..,1.5:", np.round([N*r[int(round(a*N))] for a in np.arange(0, 1.51, 0.1)], 4))
ll = np.arange(-(N-1), N); rr = r[np.abs(ll)]
def K1(z): return (rr*np.exp(2j*np.pi*np.outer(np.atleast_1d(z), ll)/N)).sum(1)
x = np.linspace(0, N/2, 8001)
k1 = K1(x).real
print(f"min_x K1(x) on R = {k1.min():+.5f} at x={x[k1.argmin()]:.3f}   (K(x)>=0 by LP; K1 = K + tail part)")
print(" eta    min_x ReK1(x+i eta)  at x     K1(i eta)   K1(2i eta)  ratio min/K1(2i eta)")
for eta in [0.02, 0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0, 1.5]:
    v = K1(x+1j*eta).real; j = v.argmin()
    print(f" {eta:4.2f}  {v[j]:+.5f}          {x[j]:6.3f}  {K1(1j*eta)[0].real:9.4f}  {K1(2j*eta)[0].real:9.4f}  {v[j]/K1(2j*eta)[0].real:+.4f}")
