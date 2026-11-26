"""[N] The hard region F' of notes §5.4: frustrated at v1 (Q1 <= 0 <= Q2,Q3), v1 curved, and v2 or v3 curved.
Minimum of Br'(sigma; lam, eta) over the closure of F', for (lam, eta) on the cut line and on the arc."""
import numpy as np, sys
from scipy.optimize import minimize
rng = np.random.default_rng(4)
def vertex(psi, psp, lam):
    mu, de = (psi+psp)/2, (psi-psp)/2
    kap = np.arcsin(min(1.0, lam*np.cos(de)))
    N = np.cos(max(kap-abs(mu), 0.0))
    Q = np.sin(psi) + np.sin(psp)
    return N, Q, kap - abs(mu)          # third > 0: curved
def brp(psi, lam, eta, pen=0.0):
    p12, p13, p21, p23, p31, p32 = psi
    N1, Q1, g1 = vertex(p12, p13, lam); N2, Q2, g2 = vertex(p21, p23, lam); N3, Q3, g3 = vertex(p31, p32, lam)
    s = np.sin(psi)
    E = abs(s[0]+s[2]) + abs(s[1]+s[4]) + abs(s[3]+s[5])
    X = abs(Q1) + abs(Q2) + abs(Q3) - E
    val = N1 + N2 + N3 - lam/2*X - eta
    viol = max(Q1, 0) + max(-Q2, 0) + max(-Q3, 0) + max(-g1, 0) + max(-max(g2, g3), 0)
    return val + pen*viol, viol
def run(lam, eta, starts=400):
    best = (np.inf, None)
    for t in range(starts):
        x0 = rng.uniform(-np.pi/2, np.pi/2, 6) if t % 2 else 0.4*rng.normal(size=6)
        f = lambda x: brp(np.clip(x, -np.pi/2, np.pi/2), lam, eta, pen=50.0)[0]
        r = minimize(f, x0, method='Nelder-Mead', options=dict(xatol=1e-9, fatol=1e-12, maxiter=8000))
        x = np.clip(r.x, -np.pi/2, np.pi/2)
        v, viol = brp(x, lam, eta)
        if viol < 1e-7 and v < best[0]: best = (v, x)
    return best
if __name__ == "__main__":
    for lam, eta, name in ((12/13, 15/13, "corner (w=5/4)"), (0.9, 1.2, "cut line w=4/3"), (6/7, 9/7, "cut line w=3/2"),
                           (0.8, 1.4, "cut line w=7/4"), (3/np.sqrt(9+1.1**2), 3.3/np.sqrt(9+1.1**2), "arc w=1.1"),
                           (3/np.sqrt(9+1.2**2), 3.6/np.sqrt(9+1.2**2), "arc w=1.2")):
        v, x = run(lam, eta)
        print(f"{name}: lam={lam:.5f} eta={eta:.5f}: min Br' over closure(F') = {v:+.6f} at psi/(pi/2) = {np.round(x/(np.pi/2), 3)}", flush=True)
