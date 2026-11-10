#!/usr/bin/env python3
"""T1c (h5): TARGETED adversarial attack on a data-form certificate  s1/N >= c0 - sum_l a_l |S_l|^2
in the N-periodic model with off-line pairs (weight 2cosh(w_l y), w_l = 2 pi l/N).
Strategy (different from h3's random batched Adam):
 1. build a pool of on-line local minima of the reduced cost (all compositions, structured starts incl. clusters);
 2. for every pool member, every double, and every pair of doubles: compute h3's exact local criterion
    D2(t) = sum a_l w_l^2 (2 + Re H_l), then convert the double(s) to pairs at depth y0 in {0.02,0.1,0.3,0.6}
    and re-optimise ALL positions and depths (L-BFGS-B, analytic gradient);
 3. 'cluster' starts: k doubles packed at spacing s in {0.3,0.6,1.0}, with pairs inserted inside/next to the cluster.
Reduced cost rc = s1/N - c0 + sum a_l |S_l|^2  (rc < 0  <=> certificate violated).
Usage: attack.py cert.npz [n_starts_per_comp]"""
import sys, numpy as np
from scipy.optimize import minimize
d = np.load(sys.argv[1]); c0 = float(d['c0']); a = np.asarray(d['a'], float); N = len(a) + 1
R = int(sys.argv[2]) if len(sys.argv) > 2 else 30
l = np.arange(1, N); w = 2 * np.pi * l / N; rng = np.random.default_rng(2026)

def rc_and_grad(t, y, m, isp):
    W = np.where(isp[:, None], 2 * np.cosh(np.outer(y, w)), m[:, None] * np.ones(N - 1))
    E = np.exp(1j * np.outer(t, w)); S = (W * E).sum(0)
    s1 = np.sum((m == 1) & ~isp)
    f = s1 / N - c0 + a @ np.abs(S) ** 2
    gS = 2 * a * np.conj(S)
    gt = np.real(gS * W * 1j * w * E).sum(1)
    gy = np.real(gS * 2 * np.sinh(np.outer(y, w)) * w * E).sum(1) * isp
    return f, gt, gy

def local_opt(t, y, m, isp, ymax=2.0):
    n = len(t)
    def fun(z):
        f, gt, gy = rc_and_grad(z[:n], z[n:], m, isp); return f, np.r_[gt, gy]
    bnds = [(None, None)] * n + [((0.0, ymax) if p else (0.0, 0.0)) for p in isp]
    r = minimize(fun, np.r_[t, y], jac=True, method='L-BFGS-B', bounds=bnds, options={'maxiter': 3000, 'ftol': 1e-15, 'gtol': 1e-12})
    return r.fun, r.x[:n], r.x[n:]

def D2(t, m, isp, y, idx):
    """h3's local criterion for the double at index idx (others = background incl. pairs)"""
    others = np.arange(len(t)) != idx
    Wb = np.where(isp[others][:, None], 2 * np.cosh(np.outer(y[others], w)), m[others][:, None] * np.ones(N - 1))
    H = (Wb * np.exp(1j * np.outer(t[idx] - t[others], w))).sum(0)
    return float(np.sum(a * w ** 2 * (2 + np.real(H))))

comps = [(N - 2 * k2, k2) for k2 in range(N // 2 + 1)]
pool = []
for k1, k2 in comps:
    m = np.r_[np.ones(k1), 2 * np.ones(k2)]; isp = np.zeros(len(m), bool); n = len(m)
    for r_ in range(R):
        mode = r_ % 3
        if mode == 0: t = np.sort(rng.uniform(0, N, n))
        elif mode == 1: t = (np.cumsum(m) - m / 2) * (N / m.sum()) + rng.normal(0, 0.15, n)
        else:  # clustered doubles
            s = rng.choice([0.3, 0.6, 1.0]); t = np.r_[rng.uniform(0, N, k1), rng.uniform(0, 1) + s * np.arange(k2)]
        f, tt, yy = local_opt(t, np.zeros(n), m, isp)
        pool.append((f, k1, k2, tt))
pool.sort(key=lambda z: z[0])
print(f"N={N} c0={c0:.6f} cert value={c0 - a @ l:.6f}  on-line min rc={pool[0][0]:+.3e} comp={pool[0][1:3]}")
best_pair = (1e9, None); minD2 = (1e9, None); tried = 0
for f0, k1, k2, t0 in pool[:max(40, len(pool) // 3)]:
    if k2 == 0: continue
    m = np.r_[np.ones(k1), 2 * np.ones(k2)]; n = len(m); dbl = np.arange(k1, n)
    for i in dbl:
        dd = D2(t0, m, np.zeros(n, bool), np.zeros(n), i)
        if f0 < 2e-3 and dd < minD2[0]: minD2 = (dd, (k1, k2), f0)
    sets = [[i] for i in dbl] + [[i, j] for i in dbl for j in dbl if i < j] + ([list(dbl)] if len(dbl) > 2 else [])
    for S_ in sets:
        for y0 in (0.02, 0.1, 0.3, 0.6):
            isp = np.zeros(n, bool); isp[S_] = True; y = np.where(isp, y0, 0.0)
            f, tt, yy = local_opt(t0.copy(), y, m, isp); tried += 1
            if f < best_pair[0]: best_pair = (f, (k1, k2 - len(S_), len(S_)), np.round(np.sort(yy[isp]), 4), f0)
print(f"  pair conversions tried: {tried}")
print(f"  min local criterion D2 over near-extremal (rc<2e-3) on-line doubles: {minD2}")
print(f"  BEST with pairs: rc={best_pair[0]:+.3e} comp(k1,k2,k3)={best_pair[1]} depths={best_pair[2]} (start rc {best_pair[3]:+.3e})")
