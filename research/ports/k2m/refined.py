"""Refined calibration (notes Prop. C'): uses rho_i >= 0, so only  cos(alpha_i)+cos(beta_i) >= lam*P_i  is needed.
   M_ref(V; lam) = (P/|V|) sqrt(1 - lam^2 |V|^2/4)   if lam |V|^2 >= 2|Q|,
                 = 1 - lam |Q| / 2                    otherwise.
   Br_ref = Sum_i M_ref(V_i) - eta + (lam/2) Sum |eps_ij|,   eta = lam*w.
Checks [N] for m = 3: (a) true slack >= D*Br_ref on random books; (b) min of Br_ref over the cube [-pi/2,pi/2]^6
for (lam, eta) on the ellipse arc  lam = 3/sqrt(9+w^2), eta = lam*w.
Usage: python3 refined.py
"""
import numpy as np
from scipy.optimize import minimize
from calib_check import book_data, random_book
rng = np.random.default_rng(11)

def Mref(V, lam):
    P, Q = V; n2 = P*P + Q*Q
    if lam*n2 >= 2*abs(Q):
        if n2 < 1e-300: return 1.0
        return P/np.sqrt(n2)*np.sqrt(max(0.0, 1 - lam*lam*n2/4))
    return 1 - lam*abs(Q)/2

def br_ref(E, m, lam, eta):
    tot = -eta
    for i in range(m):
        V = sum(E[i, j] for j in range(m) if j != i)
        tot += Mref(V, lam)
    for i in range(m):
        for j in range(i+1, m):
            tot += lam/2*abs(E[i, j, 1] + E[j, i, 1])
    return tot

def br_cube(psi6, lam, eta):
    m = 3
    psi = np.zeros((3, 3)); k = 0
    for i in range(3):
        for j in range(3):
            if i != j: psi[i, j] = psi6[k]; k += 1
    E = np.stack([np.cos(psi), np.sin(psi)], -1)
    return br_ref(E, m, lam, eta)

if __name__ == "__main__":
    for w in (1.0, 1.1, 1.2, 1.25, 1.3):
        lam = 3/np.sqrt(9 + w*w); eta = lam*w
        gap = np.inf; mb = np.inf
        for _ in range(20000):
            D, rho, a = random_book(3)
            A, B, dZ, E, _ = book_data(D, rho, a)
            true = A.sum() + B.sum() - lam*np.triu(dZ, 1).sum() - eta*D
            b = br_ref(E, 3, lam, eta)
            gap = min(gap, true/D - b); mb = min(mb, b)
        # cube: random + local minimisation from random and corner starts
        mc = np.inf; arg = None
        for t in range(300):
            if t % 3 == 0: x0 = rng.uniform(-np.pi/2, np.pi/2, 6)
            elif t % 3 == 1: x0 = rng.choice([-1, 1], 6)*np.pi/2*(1 - 0.05*rng.random(6))
            else: x0 = 0.3*rng.normal(size=6)
            f = lambda x: br_cube(np.clip(x, -np.pi/2, np.pi/2), lam, eta)
            r = minimize(f, x0, method='Nelder-Mead', options=dict(xatol=1e-9, fatol=1e-13, maxiter=6000))
            if r.fun < mc: mc = r.fun; arg = np.clip(r.x, -np.pi/2, np.pi/2)
        print(f"w={w:5.2f} lam={lam:.6f}: books: min(true/D - Br_ref)={gap:+.3e}  min Br_ref={mb:+.3e} | cube: min Br_ref={mc:+.3e} at psi/(pi/2)={np.round(arg/(np.pi/2),3)}")
