"""Numerical checks [N] of
 (1) the weighted m-page calibration (notes Prop. C):  Sigma_S - lam*(w*D + Sum d^Z) >= D * Br,
     Br = Sum_i M_i - lam*w + (lam/2) Sum_{i<j}|eps_ij|,  M_i = (P_i/|V_i|) sqrt(1 - lam^2 |V_i|^2/4),
     V_i = (P_i,Q_i) = Sum_{j != i} e_ij,  lam = R_m(w) = 2m/sqrt(m^2(m-1)^2+4w^2);
 (2) sign of Br on random books and on random points of the cube (relaxation), for several (m,w);
 (3) the averaging identity (triples) on random books.
Usage: python3 calib_check.py
"""
import numpy as np, itertools
rng = np.random.default_rng(7)

def Rm(m, w): return 2*m/np.sqrt(m*m*(m-1)**2 + 4*w*w)

def random_book(m):
    mode = rng.integers(0, 4)
    D = 1.0
    if mode == 0:
        rho = rng.uniform(0, 3, m); a = rng.uniform(-2, 3, m)
    elif mode == 1:   # near W
        rho = m*(m-1)/4 * (1 + 0.3*rng.normal(size=m)); a = 0.5 + 0.5*rng.normal(size=m)
    elif mode == 2:   # thin, near the spine
        rho = 10**rng.uniform(-3, 0, m); a = rng.uniform(-1, 2, m)
    else:
        rho = 10**rng.uniform(-2, 1.5, m); a = rng.normal(0.5, 3, m)
    return D, np.abs(rho), a

def book_data(D, rho, a):
    m = len(rho)
    A = np.hypot(rho, a); B = np.hypot(rho, a - D)
    dZ = np.zeros((m, m)); E = np.zeros((m, m, 2)); hubtype = np.zeros((m, m), int)
    for i in range(m):
        for j in range(i+1, m):
            y = (a[i]*rho[j] + a[j]*rho[i])/(rho[i]+rho[j])
            if y <= 0: y = 0.0; hubtype[i, j] = 1
            elif y >= D: y = D; hubtype[i, j] = 2
            fi = np.hypot(rho[i], a[i]-y); fj = np.hypot(rho[j], a[j]-y)
            dZ[i, j] = dZ[j, i] = fi + fj
            E[i, j] = (rho[i]/fi, (a[i]-y)/fi); E[j, i] = (rho[j]/fj, (a[j]-y)/fj)
    return A, B, dZ, E, hubtype

def bracket(E, m, w, lam):
    """E[i,j] = unit vectors (c, s); returns Br."""
    tot = -lam*w
    for i in range(m):
        V = sum(E[i, j] for j in range(m) if j != i)
        nV = np.hypot(*V)
        if nV < 1e-14: continue
        tot += V[0]/nV*np.sqrt(max(0.0, 1 - lam*lam*nV*nV/4))
    for i in range(m):
        for j in range(i+1, m):
            tot += lam/2*abs(E[i, j, 1] + E[j, i, 1])
    return tot

def main():
    print("(1),(2) books:  m  w  #books  min(true slack/D - Br)  min Br  min true slack/D")
    for m, ws in ((3, (0.2, 0.5, 1.0)), (4, (0.5, 1.0, 2.0)), (5, (1.0, 3.3)), (6, (1.0, 5.0))):
        for w in ws:
            lam = Rm(m, w); mn_gap = np.inf; mn_br = np.inf; mn_true = np.inf
            N = 20000
            for _ in range(N):
                D, rho, a = random_book(m)
                A, B, dZ, E, _ = book_data(D, rho, a)
                true = A.sum() + B.sum() - lam*(w*D + np.triu(dZ, 1).sum())
                br = bracket(E, m, w, lam)
                mn_gap = min(mn_gap, true/D - br); mn_br = min(mn_br, br); mn_true = min(mn_true, true/D)
            print(f"   {m}  {w:4.1f}  {N}  {mn_gap:+.3e}  {mn_br:+.3e}  {mn_true:+.3e}")
    
    print("(2') relaxation on the cube (independent angles):  m  w  min Br over random + corner points")
    for m, ws in ((3, (0.5, 1.0, 1.05)), (4, (1.0, 2.0)), (5, (1.0, 10/3)), (6, (1.0,))):
        for w in ws:
            lam = Rm(m, w); mn = np.inf
            for t in range(40000):
                if t % 2 == 0: psi = rng.uniform(-np.pi/2, np.pi/2, (m, m))
                else: psi = rng.choice([-np.pi/2, np.pi/2], (m, m)) + (rng.random((m, m)) < 0.3)*rng.normal(0, 0.2, (m, m))
                psi = np.clip(psi, -np.pi/2, np.pi/2)
                E = np.stack([np.cos(psi), np.sin(psi)], -1)
                mn = min(mn, bracket(E, m, w, lam))
            print(f"   {m}  {w:5.2f}  {mn:+.4e}")
    
    print("(3) averaging over triples: max |C(m-1,2)*Sigma_S - sum_triples Sigma_S(triple)| etc.")
    for m in (4, 5, 6):
        D, rho, a = random_book(m)
        A, B, dZ, E, _ = book_data(D, rho, a)
        S = A.sum() + B.sum(); VV = np.triu(dZ, 1).sum()
        s3 = 0; vv3 = 0; n3 = 0
        for tr in itertools.combinations(range(m), 3):
            s3 += sum(A[i]+B[i] for i in tr); vv3 += sum(dZ[i, j] for i, j in itertools.combinations(tr, 2)); n3 += 1
        print(f"   m={m}: {abs(s3 - (m-1)*(m-2)/2*S):.2e} {abs(vv3 - (m-2)*VV):.2e} triples={n3} (= C(m,3) = {m*(m-1)*(m-2)//6})")

if __name__ == '__main__':
    main()
