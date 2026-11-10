#!/usr/bin/env python3
"""Stress-test a dual certificate  s1/N >= c0 + sum_l lam_l |Shat(l)|^2  (from t1_ceiling_cg.py, RH run)
against configurations WITH off-line pairs: min over configs of  s1/N - c0 - sum lam |S|^2  per composition (k1,k2,k3).
Usage: t1_dual_check.py N restarts ymax"""
import sys, numpy as np
from scipy.optimize import minimize
N = int(sys.argv[1]); R = int(sys.argv[2]); YM = float(sys.argv[3]); YMIN = float(sys.argv[4]) if len(sys.argv) > 4 else 0.0; ONLYPAIRS = YMIN > 0
d = np.load(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/cg_{N}_rh.npy"); c0, lam = d[0], d[1:]
rng = np.random.default_rng(7); l = np.arange(1, N); om = 2*np.pi*l/N
print(f"N={N} c0={c0:.6f} dual value c0+sum lam*l = {c0+lam@l:.6f}")
worst_on, worst_off = (1e9, None), (1e9, None)
for k2 in range(N//2+1):
    for k3 in range(1 if ONLYPAIRS else 0, N//2-k2+1):
        k1 = N-2*k2-2*k3; n = k1+k2+k3
        isp = np.r_[np.zeros(k1+k2, bool), np.ones(k3, bool)]; base = np.r_[np.ones(k1), 2*np.ones(k2), 2*np.ones(k3)]
        def f(z):
            t = z[:n]; yy = np.zeros(n); yy[isp] = z[n:]
            W = np.where(isp[:, None], 2*np.cosh(np.outer(yy, om)), base[:, None]); E = np.exp(1j*np.outer(t, om)); S = (W*E).sum(0)
            val = k1/N - c0 - lam @ np.abs(S)**2
            gt = -(lam*2*np.real(np.conj(S)*W*1j*om*E)).sum(1)
            gy = -(lam*2*np.real(np.conj(S)*(2*np.sinh(np.outer(yy, om))*om)*E)).sum(1)[isp]
            return val, np.r_[gt, gy]
        best = 1e9
        for _ in range(R):
            z0 = np.r_[rng.uniform(0, N, n), rng.uniform(YMIN, YM, k3)]
            r = minimize(f, z0, jac=True, method='L-BFGS-B', bounds=[(None, None)]*n+[(YMIN, YM)]*k3)
            if r.fun < best: best, bz = r.fun, r.x
        tag = (k1, k2, k3)
        if k3 == 0 and best < worst_on[0]: worst_on = (best, tag)
        if k3 > 0 and best < worst_off[0]: worst_off = (best, tag, np.round(bz[n:], 3))
        print(f"  comp {tag}: min reduced cost {best:+.6f}", flush=True)
print("WORST on-line :", worst_on)
print("WORST with off-line pairs:", worst_off)
