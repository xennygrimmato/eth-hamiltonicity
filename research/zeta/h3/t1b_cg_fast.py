#!/usr/bin/env python3
"""T1b (h3): faster column generation for the bandwidth-one ceiling, N-periodic model (same object as
Zeta23/PairCeiling/LawN256.lean and Knausgard Thm 7.7 at N=256): min E[#simple]/N s.t. E|Shat(l)|^2 = l, 0<l<N.
Batched Adam pricer over positions (and depths for off-line pairs if --unc), warm starts from the current law.
Usage: t1b_cg_fast.py N iters [unc] ; saves duals/law to scratchpad cgfast_N_mode.npz"""
import sys, numpy as np
from scipy.optimize import linprog
N = int(sys.argv[1]); ITERS = int(sys.argv[2]); UNC = len(sys.argv) > 3 and sys.argv[3] == 'unc'
rng = np.random.default_rng(3); L = np.arange(1, N); OM = 2*np.pi*L/N; YMAX = 1.0; TOL = 1e-7
SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"

def S2(t, base, isp, y):
    """t,base,isp,y: (B,n). returns |Shat|^2 (B,N-1), S (B,N-1), W, E"""
    W = np.where(isp[..., None], 2*np.cosh(y[..., None]*OM), base[..., None])
    E = np.exp(1j*t[..., None]*OM)
    S = (W*E).sum(1)
    return np.abs(S)**2, S, W, E

def random_batch(B):
    n = N  # slots; unused slots have base 0
    base = np.zeros((B, n)); isp = np.zeros((B, n), bool); k1 = np.zeros(B)
    for b in range(B):
        k2 = rng.integers(0, N//2+1); k3 = rng.integers(0, N//2-k2+1) if UNC else 0
        kk1 = N-2*k2-2*k3; k1[b] = kk1
        base[b, :kk1] = 1; base[b, kk1:kk1+k2] = 2; base[b, kk1+k2:kk1+k2+k3] = 2; isp[b, kk1+k2:kk1+k2+k3] = True
    return rng.uniform(0, N, (B, n)), base, isp, rng.uniform(0, 0.3, (B, n))*isp, k1

def price(a, c0, warm, B=384, steps=400, lr=0.05):
    t, base, isp, y, k1 = random_batch(B)
    for i, (wt, wb, wi, wy, wk) in enumerate(warm[:B//2]):          # warm starts: perturbed support configs
        t[i] = wt + rng.normal(0, 0.15, N); base[i] = wb; isp[i] = wi; y[i] = np.abs(wy + rng.normal(0, 0.05, N)*wi); k1[i] = wk
    mt = np.zeros_like(t); vt = np.zeros_like(t); my = np.zeros_like(y); vy = np.zeros_like(y)
    for s in range(1, steps+1):
        P, S, W, E = S2(t, base, isp, y)
        gS = 2*a*np.conj(S)                                          # d f / d S  (f = k1/N - c0 + sum a |S|^2)
        gt = np.real(gS[:, None, :]*W*1j*OM*E).sum(2)
        gy = np.real(gS[:, None, :]*2*np.sinh(y[..., None]*OM)*OM*E).sum(2)*isp
        for (x, g, m, v) in ((t, gt, mt, vt), (y, gy, my, vy)):
            m[:] = 0.9*m+0.1*g; v[:] = 0.999*v+0.001*g*g
            x -= lr*(m/(1-0.9**s))/(np.sqrt(v/(1-0.999**s))+1e-12)
        np.clip(y, 0, YMAX, out=y)
    P = S2(t, base, isp, y)[0]
    f = k1/N - c0 + P @ a
    return f, t, base, isp, y, k1, P

def lp(C, Smat):
    m = len(C); target = L.astype(float)
    Aeq = np.zeros((N, m+2*(N-1))); Aeq[0, :m] = 1; Aeq[1:, :m] = Smat.T
    Aeq[1:, m:m+N-1] = np.eye(N-1); Aeq[1:, m+N-1:] = -np.eye(N-1)
    res = linprog(np.r_[C, 10*np.ones(2*(N-1))/N], A_eq=Aeq, b_eq=np.r_[1.0, target], bounds=(0, None), method='highs')
    res.slack_used = res.x[m:].sum(); res.x = res.x[:m]
    return res

# seed: random on-line configs + doubled lattice + lattice
cols = []
t, base, isp, y, k1 = random_batch(600)
P = S2(t, base, isp, y)[0]
for b in range(600): cols.append((k1[b]/N, P[b], (t[b], base[b], isp[b], y[b], k1[b])))
for k in range(N):   # lattice (Shat=0 for 0<l<N) and shifted copies
    tt = np.arange(N)+0.0; cols.append((1.0, np.zeros(N-1), (tt, np.ones(N), np.zeros(N, bool), np.zeros(N), N)))
    break
res = None
for it in range(ITERS):
    C = np.array([c[0] for c in cols]); Smat = np.array([c[1] for c in cols])
    res = lp(C, Smat)
    if res.status != 0:   # infeasible seed: add more random columns
        t, base, isp, y, k1 = random_batch(600); P = S2(t, base, isp, y)[0]
        for b in range(600): cols.append((k1[b]/N, P[b], (t[b], base[b], isp[b], y[b], k1[b])))
        print("it", it, "LP status", res.status, "adding random cols", flush=True); continue
    du = res.eqlin.marginals; c0, lam = du[0], du[1:]; a = -lam
    w = res.x; supp = [cols[i][2] for i in np.argsort(-w) if w[i] > 1e-9]
    f, t, base, isp, y, k1, P = price(a, c0, supp)
    order = np.argsort(f); added = 0
    for b in order[:24]:
        if f[b] < -TOL:
            cols.append((k1[b]/N, P[b], (t[b].copy(), base[b].copy(), isp[b].copy(), y[b].copy(), k1[b]))); added += 1
    print(f"it {it:3d} slack {res.slack_used:.1e} obj {res.fun:.7f} minRC {f.min():+.2e} added {added} ncols {len(cols)} min(a) {a.min():+.2e}", flush=True)
    # drop columns with large reduced cost to keep LP small
    if len(cols) > 3000:
        rc = C - c0 - Smat @ lam
        keep = np.argsort(rc)[:1500]; cols = [cols[i] for i in keep]
    if added == 0 and res.slack_used < 1e-9: break
    if it % 25 == 24: np.savez(SP+f"cgfast_{N}_{'unc' if UNC else 'rh'}.npz", c0=c0, a=a, val=res.fun)
w = res.x; supp = [(w[i], cols[i]) for i in range(len(w)) if w[i] > 1e-9]
pw = sum(x for x, c in supp if c[2][2].any() and (c[2][3] > 1e-6).any())
print(f"RESULT N={N} unc={UNC} ceiling-law value {res.fun:.7f}; c0={c0:.6f}; weight on configs with pairs of depth>1e-6: {pw:.4f}")
print("a_l = -lambda_l:", np.array2string(a, precision=5, max_line_width=250))
np.savez(SP+f"cgfast_{N}_{'unc' if UNC else 'rh'}.npz", c0=c0, a=a, val=res.fun)
