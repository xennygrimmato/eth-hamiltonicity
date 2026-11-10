#!/usr/bin/env python3
"""Periodic-model analogue of the Chirre-Goncalves-de Laat (RH) certificate.
Kernel K(theta)=sum_{|l|<=M} r(l) e^{il theta} >= 0, r(l)<=0 for N<=|l|<=M, K(0)=sum r = 1.
Real configs:  N* <= sum_l r(l)|S_l|^2/K(0) <= r(0)N^2 + 2 sum_{0<l<N} r(l)|S_l|^2  (drop |l|>=N terms, <=0),
so  s1/N >= 2 - N r(0) - (2/N) sum_{0<l<N} r(l)|S_l|^2  [data form: c0 = 2-N r(0), a_l = 2 r(l)/N].
LP: minimise N r(0) + (2/N) sum_{0<l<N} l r(l). Usage: t1b_cgdl_periodic.py N M"""
import sys, numpy as np
from scipy.optimize import linprog
N = int(sys.argv[1]); M = int(sys.argv[2]); G = 40*M
th = np.linspace(0, np.pi, G)
l = np.arange(M+1)
Cm = np.cos(np.outer(th, l)); Cm[:, 1:] *= 2           # K(theta) = r0 + 2 sum r_l cos
c = np.zeros(M+1); c[0] = N; c[1:N] = 2*np.arange(1, N)/N
bounds = [(None, None)]*(M+1)
for k in range(N, M+1): bounds[k] = (None, 0)
Aeq = np.ones((1, M+1)); Aeq[0, 1:] = 2
res = linprog(c, A_ub=-Cm, b_ub=np.zeros(G), A_eq=Aeq, b_eq=[1.0], bounds=bounds, method='highs')
r = res.x
print(f"N={N} M={M}: periodic CGdL certificate value 2 - obj = {2-res.fun:.6f}")
print("r(0..N-1) >= 0 ?", bool((r[:N] >= -1e-12).all()), " min r on [0,N):", r[:N].min())
print("r:", np.array2string(r[:min(M+1, 3*N)]*N, precision=4, max_line_width=250))
np.savez(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/cgdl_{N}.npz", c0=2-N*r[0], a=2*r[1:N]/N, val=2-res.fun)
# also: same LP but forcing r(l)=0 for l>=N (bandwidth-one, = MT-type / CCLM class)
bounds2 = [(None, None)]*N + [(0, 0)]*(M+1-N)
res2 = linprog(c, A_ub=-Cm, b_ub=np.zeros(G), A_eq=Aeq, b_eq=[1.0], bounds=bounds2, method='highs')
print(f"   same with support <N (CCLM/MT class): {2-res2.fun:.6f}")
