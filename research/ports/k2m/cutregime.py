"""[N] Per-vertex lemmas for the cut regime (notes §6).  N(s,s') = M_ref + (lam/2)|s+s'| = cos((kappa-|mu|)_+),
 sin(kappa) = lam*cos(delta), mu,delta = half sum / half difference of arcsin s, arcsin s'.
 (V1') s+s' <= 0 :  1 - N <= lam*alpha*(2 + s + s')
 (V2') s+s' >= 0 :  1 - N <= lam*(1-alpha)*(1 - max(s,s'))
Scan lam on the cut line; report feasibility of some alpha."""
import numpy as np
def Nfun(s, sp, lam):
    psi = np.arcsin(s); psp = np.arcsin(sp)
    mu = (psi + psp)/2; de = (psi - psp)/2
    kap = np.arcsin(np.clip(lam*np.cos(de), -1, 1))
    return np.cos(np.maximum(kap - np.abs(mu), 0.0))
n = 1201
g = np.sin(np.linspace(-np.pi/2, np.pi/2, n))
S, SP = np.meshgrid(g, g, indexing='ij')
for lam in (0.5, 0.6, 0.7, 0.72, 0.74, 0.75, 0.76, 0.78, 0.8, 12/13):
    tau = np.sqrt(1 - lam*lam)
    N = Nfun(S, SP, lam)
    neg = (S + SP) <= 0; pos = (S + SP) >= 0
    # smallest alpha for V1':  alpha >= (1-N)/(lam (2+s+s'))
    with np.errstate(divide='ignore', invalid='ignore'):
        r1 = np.where(neg & (2 + S + SP > 1e-12), (1 - N)/(lam*(2 + S + SP)), 0.0)
        r2 = np.where(pos & (1 - np.maximum(S, SP) > 1e-12), (1 - N)/(lam*(1 - np.maximum(S, SP))), 0.0)
    a_min = r1.max(); one_minus_a_min = r2.max()
    print(f"lam={lam:.4f} w={(3-2*lam)/lam:.3f}: V1' needs alpha >= {a_min:.5f} (centre value {(1-tau)/(2*lam):.5f});"
          f" V2' needs 1-alpha >= {one_minus_a_min:.5f} (centre {(1-tau)/lam:.5f}, lam={lam:.4f});  feasible: {a_min + one_minus_a_min <= 1}  (sum {a_min+one_minus_a_min:.5f})")
