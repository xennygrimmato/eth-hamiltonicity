#!/usr/bin/env python3
"""Local depth criterion [R-identity, numerics]: replacing a double at t (in on-line config mu) by a pair t+-iy changes
F = sum_l a_l |S_l|^2 by  2 y^2 * D2(t) + O(y^4),  D2(t) = sum_l a_l w_l^2 (2 + Re H_l) = -(mu*k'')(t),
k(x) = sum_l a_l cos(w_l x), w_l = 2 pi l/N.  D2<0 at some double  =>  that double prefers to go off-line (D fails locally).
Here: (1) verify the expansion by finite differences, (2) evaluate D2 at the on-line minimiser of the N=8 counterexample."""
import numpy as np
a = np.load("/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/randcert_a_8_6.npy"); N = 8
L = np.arange(1, N); W = 2*np.pi*L/N
def F(ts, ms, pair_idx=None, y=0.0):
    w = np.array([np.full(N-1, float(m)) for m in ms])
    if pair_idx is not None: w[pair_idx] = 2*np.cosh(W*y)
    S = (w*np.exp(1j*np.outer(ts, W))).sum(0); return np.abs(S)**2 @ a
def D2(ts, ms, i):
    H = sum(ms[b]*np.exp(1j*W*(ts[i]-ts[b])) for b in range(len(ts)) if b != i)
    return float((a*W**2*(2+np.real(H))).sum())
ts = np.array([0., 1.0039, 7.0139, 6.0101]); ms = [2, 2, 2, 2]
for i in range(4):
    y = 1e-3; fd = (F(ts, ms, i, y)-F(ts, ms))/(2*y*y)
    print(f"double at t={ts[i]:.4f}: D2 = {D2(ts, ms, i):+.5f}   finite-difference check {fd:+.5f}")
