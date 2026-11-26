"""Minimise R = Sigma_S / (Sigma_vv + w*D) over m-page books (K_{2,m}, weight w on u1u2).
Book: spine u1=(0,0), u2=(0,D); page i holds v_i=(rho_i,a_i), rho_i>=0.
d_ij = min_{y in [0,D]} f_i(y)+f_j(y),  f_i(y)=|(rho_i,a_i-y)|.
Usage: python3 books.py m w [starts] [seed]
"""
import sys, numpy as np
from scipy.optimize import minimize

def book_ratio(x, m, w, D=1.0):
    rho = np.abs(x[:m]); a = x[m:2*m]
    A = np.hypot(rho, a); B = np.hypot(rho, a - D)
    S = A.sum() + B.sum()
    T = w * D
    for i in range(m):
        for j in range(i + 1, m):
            den = rho[i] + rho[j]
            if den > 1e-300:
                y = (a[i] * rho[j] + a[j] * rho[i]) / den
            else:
                y = 0.5 * (a[i] + a[j])
            y = min(max(y, 0.0), D)
            T += np.hypot(rho[i], a[i] - y) + np.hypot(rho[j], a[j] - y)
    return S / T

def Rm(m, w):
    return 2 * m / np.sqrt(m * m * (m - 1) ** 2 + 4 * w * w)

def run(m, w, starts=200, seed=0, verbose=True):
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    vals = []
    for s in range(starts):
        scale = 10 ** rng.uniform(-1.5, 1.5)
        x0 = np.concatenate([scale * rng.uniform(0, 2, m), 0.5 + scale * rng.normal(0, 1, m)])
        r = minimize(book_ratio, x0, args=(m, w), method='Nelder-Mead',
                     options=dict(xatol=1e-11, fatol=1e-14, maxiter=40000, maxfev=40000))
        r = minimize(book_ratio, r.x, args=(m, w), method='Powell', options=dict(xtol=1e-12, ftol=1e-15))
        vals.append(r.fun)
        if r.fun < best[0]:
            best = (r.fun, r.x.copy())
    vals = np.array(vals)
    if verbose:
        x = best[1]
        print(f"m={m} w={w}: best book R = {best[0]:.12f}   W-formula R_m(w) = {Rm(m,w):.12f}   "
              f"cut2/(m-1) = {2/(m-1):.6f}  flow = {2*m/(m*(m-1)+2*w):.6f}")
        print("   rho =", np.round(np.abs(x[:m]), 5), " a =", np.round(x[m:], 5))
        print("   fraction of starts within 1e-7 of best:", np.mean(vals < best[0] + 1e-7),
              " distinct local values:", np.unique(np.round(vals, 5))[:8])
    return best

if __name__ == "__main__":
    m = int(sys.argv[1]); w = float(sys.argv[2])
    starts = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    run(m, w, starts, seed)
