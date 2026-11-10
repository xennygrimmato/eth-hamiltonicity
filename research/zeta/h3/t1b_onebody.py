#!/usr/bin/env python3
"""Single-pair one-body inequality (*) for the CGdL data kernel, near-continuum (periodic kernel at N=64, |x|<<N/2):
  LHS(B,y) = 2(K1(2iy) - K1(0)) + 4 sum_b m_b G_y(x_b) + sum_{b!=b'} m_b m_b' K(x_b - x_b'),
  G_y(x) = Re K1(x+iy) - K1(x) + K(x)  [= beta_y + K].
(*) LHS >= 0 for all real backgrounds B (masses 1/2) and y>=0  ==>  replacing a double by a pair never breaks CGdL
(proof: Slack(X_y) = Slack(X_0) + [self(y)-self(0)] + 4 sum m_b beta_y(x_b), and Slack(X_0) >= 4 sum m_b K(x_b) + sum_{b!=b'} m m' K).
Also prints zeros/minima of K and K1'' there (stiff-well mechanism)."""
import numpy as np, sys
d = np.load("/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/cgdl_r_64.npz"); r = d['r']; N = int(d['N'])
M = len(r)-1; ll = np.arange(-M, M+1); rr = r[np.abs(ll)]; inb = np.abs(ll) < N
w = 2*np.pi*ll/N
def K(x):  return (rr[None, :]*np.cos(np.outer(x, w))).sum(1)
def K1(x, y=0.0): return (rr[inb][None, :]*np.cosh(w[inb]*y)*np.cos(np.outer(x, w[inb]))).sum(1)
def K1pp(x): return -(rr[inb]*w[inb]**2*np.cos(np.outer(x, w[inb]))).sum(1)
x = np.linspace(0, 8, 16001); kx = K(x)
mins = [i for i in range(1, len(x)-1) if kx[i] < kx[i-1] and kx[i] <= kx[i+1]]
print("local minima of K on (0,8):  x, K(x), K1''(x)/|K1''(0)|")
k1pp0 = abs(K1pp(np.array([0.0]))[0])
for i in mins: print(f"   {x[i]:.3f}  {kx[i]:.2e}  {K1pp(np.array([x[i]]))[0]/k1pp0:+.4f}")
print(f"K1''(0) = {-k1pp0:.4f};  K(0)={K(np.array([0.]))[0]:.4f}")
# one-body minimisation
rng = np.random.default_rng(5)
def lhs_batch(X, m, y):   # X: (B,k) positions, m: (B,k) masses
    B, k = X.shape
    g = (Re := None)
    Kxy = lambda z: (rr[inb]*np.cosh(w[inb]*y)*np.cos(z[..., None]*w[inb])).sum(-1)
    Kfull = lambda z: (rr*np.cos(z[..., None]*w)).sum(-1)
    K1r = lambda z: (rr[inb]*np.cos(z[..., None]*w[inb])).sum(-1)
    G = Kxy(X) - K1r(X) + Kfull(X)
    D = X[:, :, None]-X[:, None, :]
    KD = Kfull(D); idx = np.arange(k); KD[:, idx, idx] = 0
    selfy = 2*(K1(np.array([0.0]), 2*y)[0]-K1(np.array([0.0]))[0])
    return selfy + 4*(m*G).sum(1) + np.einsum('bi,bij,bj->b', m, KD, m)
def minimise(y, k, B=256, steps=300, lr=0.02):
    X = rng.uniform(-3, 3, (B, k)); m = rng.choice([1.0, 2.0], (B, k))
    mt = np.zeros_like(X); vt = np.zeros_like(X); h = 1e-4
    for s in range(1, steps+1):
        f0 = lhs_batch(X, m, y)
        g = np.zeros_like(X)
        for j in range(k):
            Xp = X.copy(); Xp[:, j] += h; g[:, j] = (lhs_batch(Xp, m, y)-f0)/h
        mt = 0.9*mt+0.1*g; vt = 0.999*vt+0.001*g*g
        X -= lr*(mt/(1-0.9**s))/(np.sqrt(vt/(1-0.999**s))+1e-12)
    f = lhs_batch(X, m, y); b = f.argmin()
    return f[b], np.round(np.sort(X[b]), 3), m[b][np.argsort(X[b])]
if __name__ == '__main__':
    print(" y     self(y)-self(0)   min LHS over backgrounds (k=1..6 points)   argmin")
    for y in [0.01, 0.03, 0.05, 0.1, 0.2, 0.3, 0.5, 0.8]:
        selfy = 2*(K1(np.array([0.0]), 2*y)[0]-K1(np.array([0.0]))[0])
        best = min((minimise(y, k) for k in (1, 2, 4, 6)), key=lambda z: z[0])
        print(f" {y:4.2f}  {selfy:.5f}   {best[0]:+.5f}   x={best[1]} m={best[2]}", flush=True)
