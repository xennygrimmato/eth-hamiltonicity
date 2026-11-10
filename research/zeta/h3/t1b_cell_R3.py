#!/usr/bin/env python3
"""Refined cell criterion R3 for the single-pair inequality (*), CGdL kernel (cgdl_r_64), |x|<=XMAX:
split {G_y<0} into sub-cells of diameter <= DELTA; in a sub-cell with worst depth g and kappa = min_{|D|<=diam} K(D),
mass M (points of mass <=2) contributes >= -h := min( -8g [M<=2 single double],  min_{M>=2} kappa(M^2-2M) - 4gM ).
Different sub-cells interact through K>=0 (dropped). Criterion: R3(y) = sum h / self(y) < 1  ==> (*) holds at this y."""
import numpy as np
exec(open('t1b_onebody2.py').read().split("rng = np.random")[0])
XMAX = 15.5; DELTA = 0.12
mask = np.abs(xs) <= XMAX
def R3(y):
    Gt = tab(rr[inb]*np.cosh(w[inb]*y), w[inb])[0]-K1t+Kt
    selfy = 2*((rr[inb]*np.cosh(2*w[inb]*y)).sum()-K10)
    neg = (Gt < 0) & mask; idx = np.where(neg)[0]
    H = 0.0
    if len(idx):
        # group consecutive indices into sub-cells of diameter <= DELTA
        start = idx[0]; prev = idx[0]
        groups = []
        for i in idx[1:]:
            if i != prev+1 or xs[i]-xs[start] > DELTA: groups.append((start, prev)); start = i
            prev = i
        groups.append((start, prev))
        for s, e in groups:
            g = -Gt[s:e+1].min(); kap = np.interp(xs[e]-xs[s], xs, Kt)
            Ms = np.arange(2, 400)
            best_multi = (kap*(Ms**2-2*Ms)-4*g*Ms).min()
            H += -min(-8*g, best_multi)
    return H/selfy, selfy
for y in [0.003, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 1.0, 1.2, 1.5, 2.0, 2.5, 3.0]:
    v, se = R3(y); print(f"y={y:5.3f}  self={se:.4e}  R3={v:.4f}", flush=True)
