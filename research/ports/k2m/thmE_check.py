"""[N] sanity checks for Theorem E (notes §5.3): cut regime of K_{2,3}(w).
 N(s,s') = cos((kappa-|mu|)_+), sin kappa = lam cos delta;  M_ref = N - (lam/2)|Q|;  Br = sum N_i - (lam/2) X - eta,
 X = sum|Q_i| - E.
 (V1) 1 - N <= (1-tau)(1 - |Q|/2)                       all (s,s'), all lam
 (V2) 1 - N <= lam^2 (1 - max(s,s'))  if s+s' >= 0      all lam
 (X1) all Q_i of one sign  =>  X <= 0
 (X2) Q_1 <= 0 <= Q_2,Q_3  =>  X <= 2 min(-s12, s21) + 2 min(-s13, s31)
 (E)  lam <= lam_1  =>  Br(lam, 3-2lam) >= 0;   also compares M_ref formula with refined.Mref."""
import numpy as np
from refined import Mref
rng = np.random.default_rng(2)
def N_of(s, sp, lam):
    psi, psp = np.arcsin(s), np.arcsin(sp)
    mu, de = (psi+psp)/2, (psi-psp)/2
    kap = np.arcsin(min(1.0, lam*np.cos(de)))
    return np.cos(max(kap-abs(mu), 0.0))
lam1 = np.roots([4, -8, 9, -4]); lam1 = float(lam1[np.isreal(lam1)].real[0])
print("lam_1 =", lam1, " w_1 = (3-2 lam_1)/lam_1 =", (3-2*lam1)/lam1)
worst = dict(V1=np.inf, V2=np.inf, X1=np.inf, X2=np.inf, E=np.inf, formula=0.0)
for t in range(300000):
    lam = rng.uniform(0.05, 0.999) if t % 2 else rng.uniform(0.05, lam1)
    tau = np.sqrt(1-lam*lam)
    k = t % 5
    if k == 0: s = rng.uniform(-1, 1, 6)
    elif k == 1: s = np.sin(rng.uniform(-np.pi/2, np.pi/2, 6))
    elif k == 2: s = np.clip(rng.choice([-1, 1], 6) + 0.05*rng.normal(size=6)*rng.integers(0, 2, 6), -1, 1)
    elif k == 3: s = np.clip(0.1*rng.normal(size=6), -1, 1)
    else: s = np.clip(rng.choice([-1, 0, 1], 6) + 0.02*rng.normal(size=6), -1, 1)
    s12, s13, s21, s23, s31, s32 = s
    verts = [(s12, s13), (s21, s23), (s31, s32)]
    Ns = [N_of(a, b, lam) for a, b in verts]; Q = [a+b for a, b in verts]
    E = abs(s12+s21) + abs(s13+s31) + abs(s23+s32); X = sum(abs(q) for q in Q) - E
    for (a, b), n, q in zip(verts, Ns, Q):
        worst['V1'] = min(worst['V1'], (1-tau)*(1-abs(q)/2) - (1-n))
        if q >= 0: worst['V2'] = min(worst['V2'], lam*lam*(1-max(a, b)) - (1-n))
        else: worst['V2'] = min(worst['V2'], lam*lam*(1+min(a, b)) - (1-n))
        c, cp = np.sqrt(1-a*a), np.sqrt(1-b*b)
        worst['formula'] = max(worst['formula'], abs(Mref((c+cp, a+b), lam) - (n - lam*abs(q)/2)))
    if min(Q) >= 0 or max(Q) <= 0: worst['X1'] = min(worst['X1'], -X)
    if Q[0] <= 0 <= min(Q[1], Q[2]): worst['X2'] = min(worst['X2'], 2*min(-s12, s21) + 2*min(-s13, s31) - X)
    if lam <= lam1: worst['E'] = min(worst['E'], sum(Ns) - lam/2*X - (3-2*lam))
print({k: float('%.3e' % v) for k, v in worst.items()})
