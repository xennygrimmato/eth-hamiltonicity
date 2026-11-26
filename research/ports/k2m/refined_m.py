"""[N] Refined m-page bracket Br_ref on books and on the cube, for (lam, eta) on the boundary of the
conjectured valid region: lam = R_m(w), eta = lam*w for w <= w_c(m); m = 4, 5."""
import numpy as np, sys
from scipy.optimize import minimize
from calib_check import book_data, random_book
from refined import br_ref
rng = np.random.default_rng(5)
def Rm(m, w): return 2*m/np.sqrt(m*m*(m-1)**2 + 4*w*w)
def wc(m):
    b = (m*m)//4
    return (m*m*(m-1)**2 - 4*b*b)/(8*b)
def cube_min(m, lam, eta, starts):
    idx = [(i, j) for i in range(m) for j in range(m) if i != j]
    def f(x):
        x = np.clip(x, -np.pi/2, np.pi/2)
        psi = np.zeros((m, m))
        for k, (i, j) in enumerate(idx): psi[i, j] = x[k]
        E = np.stack([np.cos(psi), np.sin(psi)], -1)
        return br_ref(E, m, lam, eta)
    best = (np.inf, None)
    for t in range(starts):
        n = len(idx)
        if t % 3 == 0: x0 = rng.uniform(-np.pi/2, np.pi/2, n)
        elif t % 3 == 1: x0 = rng.choice([-1, 1], n)*np.pi/2*(1 - 0.05*rng.random(n))
        else: x0 = 0.3*rng.normal(size=n)
        r = minimize(f, x0, method='Powell', options=dict(xtol=1e-9, ftol=1e-13, maxiter=20000))
        if r.fun < best[0]: best = (r.fun, np.clip(r.x, -np.pi/2, np.pi/2))
    return best
for m in (4, 5):
    for w in (1.0, m*(m-1)/6, 5*m*(m-1)/24, 0.5*(5*m*(m-1)/24 + wc(m)), wc(m)):
        lam = Rm(m, w); eta = lam*w
        gap = np.inf; mb = np.inf
        for _ in range(8000):
            D, rho, a = random_book(m)
            A, B, dZ, E, _ = book_data(D, rho, a)
            true = A.sum() + B.sum() - lam*np.triu(dZ, 1).sum() - eta*D
            b = br_ref(E, m, lam, eta)
            gap = min(gap, true/D - b); mb = min(mb, b)
        mc, arg = cube_min(m, lam, eta, 45 if m == 4 else 24)
        print(f"m={m} w={w:6.3f} (w_c={wc(m):.3f}) lam={lam:.5f}: books min(true/D-Br_ref)={gap:+.2e} min Br_ref={mb:+.2e} | cube min Br_ref={mc:+.3e}", flush=True)
        if mc < -1e-6: print("    at psi/(pi/2) =", np.round(arg/(np.pi/2), 2), flush=True)
