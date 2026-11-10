#!/usr/bin/env python3
"""T1g (h5): mixture kernel r_mix = (1-eps) r_MT + eps r_CGdL in h3's near-continuum periodic model (N=64, M=256, mean spacing 1).
r_MT = psi*psi (psi_j ~ cos(sqrt2 s), s = (j+1/2)/N - 1/2), normalised K_MT(0)=1; r_CGdL from h3's cgdl_r_64.npz.
For the single-pair inequality (Lemma C, h3 sec 7):  LHS(B,y) = self(y) + 4 sum_b m_b G_y(t-t_b) + E_B,
G_y(x) = Re K1(x+iy) - K1(x) + K(x),  self(y) = 2(K1(2iy) - K1(0)),  E_B >= 0.
Prints: values; min_x G_y(x) (pointwise route); h3's cell criterion R4(y) for the mixture."""
import numpy as np, sys
SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"
d = np.load(SP + "cgdl_r_64.npz"); rC = d['r']; N = int(d['N']); M = len(rC) - 1
j = np.arange(N); s = (j + 0.5) / N - 0.5; psi = np.cos(np.sqrt(2) * s); psi /= psi.sum()
rMT = np.zeros(M + 1); rMT[:N] = [np.sum(psi[:N - l] * psi[l:]) for l in range(N)]
norm = rMT[0] + 2 * rMT[1:].sum(); rMT /= norm                     # K_MT(0) = 1
def value(r):  # data-form value 2 - N r0 - (2/N) sum_{0<l<N} r_l l  (normalised K(0)=1)
    return 2 - N * r[0] - (2 / N) * np.sum(r[1:N] * np.arange(1, N))
ll = np.arange(-M, M + 1); inb = np.abs(ll) < N; w = 2 * np.pi * ll / N
xs = np.linspace(-32, 32, 64001)
def tab(coef, freqs, x=xs): return (coef[None, :] * np.cos(np.outer(x, freqs))).sum(1)
def setup(eps):
    r = (1 - eps) * rMT + eps * rC; rr = r[np.abs(ll)]
    return r, rr, tab(rr, w), tab(rr[inb], w[inb]), rr[inb].sum()
def G_self(rr, Kt, K1t, K10, y):
    Gt = tab(rr[inb] * np.cosh(w[inb] * y), w[inb]) - K1t + Kt
    return Gt, 2 * ((rr[inb] * np.cosh(2 * w[inb] * y)).sum() - K10)
def R4(Gt, Kt, selfy, XMAX=31.5):
    neg = (Gt < 0) & (np.abs(xs) <= XMAX); idx = np.where(neg)[0]; H = 0.0; worstdiam = 0
    if len(idx) == 0: return 0.0, 0.0
    groups = []; st = idx[0]; pv = idx[0]
    for i in idx[1:]:
        if i != pv + 1: groups.append((st, pv)); st = i
        pv = i
    groups.append((st, pv)); Ms = np.arange(2, 400)
    for a_, b_ in groups:
        g = -Gt[a_:b_ + 1].min(); diam = xs[b_] - xs[a_]; worstdiam = max(worstdiam, diam)
        kap = np.interp(diam, xs[xs >= 0] - 0, Kt[xs >= 0])
        H += -min(-8 * g, (kap * (Ms ** 2 - 2 * Ms) - 4 * g * Ms).min())
    return H / selfy, worstdiam
if __name__ == '__main__':
    print(f"values (N=64): MT {value(rMT):.6f}  CGdL {value(rC):.6f}")
    print(f"zeros check: K_MT min on R = {tab(rMT[np.abs(ll)], w).min():.2e} (>=0, Gram)")
    ys = [0.001, 0.003, 0.01, 0.03, 0.1, 0.2, 0.3, 0.5, 0.8, 1.0, 1.5, 2.0, 3.0]
    for eps in [float(e) for e in (sys.argv[1:] or ['1.0', '0.5', '0.3', '0.2'])]:
        r, rr, Kt, K1t, K10 = setup(eps)
        print(f"\n== eps={eps}  (tau=(1-eps)/eps={(1-eps)/eps if eps>0 else np.inf:.3f})  value={value(r):.6f}  min K={Kt.min():.2e}")
        for y in ys:
            Gt, se = G_self(rr, Kt, K1t, K10, y); R, dm = R4(Gt, Kt, se)
            print(f"  y={y:6.3f} self={se:.3e}  min_x G_y={Gt.min():+.3e} at x={xs[Gt.argmin()]:+.3f}   min G/self={Gt.min()/se:+.3e}  R4={R:.4f} (max cell diam {dm:.3f})", flush=True)
