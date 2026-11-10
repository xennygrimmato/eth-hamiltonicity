#!/usr/bin/env python3
"""T8 (h4), part 2b: MOLLIFIED one-point data (finite analogue of Bui--Heath-Brown's S1, S2) added to the pair rows.

Model as in tw_model.py.  z_rho = e(tau_rho/N);  Lambda(z) = prod_rho (1 - z_rho/z)^{m_rho}  (analogue of zeta),
g_rho = prod_{rho' != rho} (1 - z_rho'/z_rho)  (= z Lambda'(z) at a simple zero; 0 at doubles)      [analogue of zeta'(rho)]
1/Lambda(z) = sum_k h_k z^{-k}  (h_k complete homogeneous symmetric functions of the zeros)          [analogue of sum mu(n) n^{-s}]
mollifier  B(z) = sum_{k=0}^{K} c_k h_k z^{-k},  K < N/2  (analogue of length T^theta, theta < 1/2);  f_rho = g_rho B(z_rho).
  M1 = sum_rho f_rho                         (BHB S1)        rows Re, Im
  M2 = sum_rho f_rho * conj(f_{rho*})         (BHB S2 = sum f(rho) f(1-rho); = sum |f|^2 on the line; pairs give 2 Re(f conj f*))
Targets: CUE Monte Carlo.  c is chosen to maximise (E M1)^2/(N E M2) (the RH Cauchy-Schwarz bound for E s1/N).
Usage: tw_moll.py N K mode(rh|unc) [iters] [tries]
"""
import sys, numpy as np
from scipy.optimize import linprog, minimize
from scipy.stats import unitary_group
rng = np.random.default_rng(9)
YMAX = 1.0

def fvec(N, K, taus, mult, partner):
    """returns F[k, rho] = g_rho h_k z_rho^{-k} for simple rho (0 for doubles), and pair-row stats"""
    z = np.exp(2j*np.pi*taus/N)
    zz = np.repeat(z, mult.astype(int))
    e = np.poly(zz)                      # prod (x - z) = sum e-coeffs; e[j] = (-1)^j e_j
    h = np.zeros(K+1, complex); h[0] = 1
    for k in range(1, K+1):
        h[k] = -sum(e[j]*h[k-j] for j in range(1, min(k, len(e)-1)+1))
    r = 1 - z[None, :]/z[:, None]; np.fill_diagonal(r, 1.0); r = r**mult[None, :]
    g = np.where(mult == 1, np.prod(r, axis=1), 0.0)
    F = g[None, :]*h[:, None]*z[None, :]**(-np.arange(K+1)[:, None])
    l = np.arange(1, N)
    S = (mult[:, None]*np.exp(2j*np.pi*np.outer(taus, l)/N)).sum(0)
    return F, np.abs(S)**2

def build(N, k1, k2, k3, x):
    n = k1+k2+k3; t = x[:n]; y = x[n:]
    taus = np.concatenate([t[:k1+k2].astype(complex), t[k1+k2:]+1j*y, t[k1+k2:]-1j*y])
    mult = np.concatenate([np.ones(k1), 2*np.ones(k2), np.ones(2*k3)])
    partner = np.concatenate([np.arange(k1+k2), k1+k2+k3+np.arange(k3), k1+k2+np.arange(k3)])
    return taus, mult, partner

def main():
    N = int(sys.argv[1]); K = int(sys.argv[2]); mode = sys.argv[3]
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 40; tries = int(sys.argv[5]) if len(sys.argv) > 5 else 12
    M = 40000
    v = np.zeros(K+1, complex); A = np.zeros((K+1, K+1), complex)
    ts = np.angle(np.linalg.eigvals(unitary_group.rvs(N, size=M, random_state=3)))*N/(2*np.pi)
    one = np.ones(N); idn = np.arange(N)
    for t in ts:
        F, _ = fvec(N, K, t.astype(complex), one, idn)
        v += F.sum(1); A += F @ F.conj().T
    v /= M; A /= M
    c = np.linalg.solve(A, v); ratio = (v.conj() @ c).real/N        # sup over c of |c^* v|^2/(N c^* A c) = v^* A^{-1} v / N
    for KK in range(K+1):
        cc = np.linalg.solve(A[:KK+1, :KK+1], v[:KK+1]); print(f"  mollifier length K={KK}: RH Cauchy-Schwarz bound (E M1)^2/(N E M2) = {(v[:KK+1].conj()@cc).real/N:.4f}")
    c = c/np.sqrt((c.conj() @ A @ c).real/N)          # normalise E M2 = N
    m1 = c.conj() @ v; m2 = float(N)
    print(f"N={N} K={K} mode={mode}: optimal mollifier c={np.array2string(c,precision=3)}  E M1={m1:.4f}  E M2={m2}  RH C-S bound {abs(m1)**2/(N*m2):.4f}", flush=True)
    JMAX = int(__import__("os").environ.get("JMAX", -1)); JS = np.arange(0, JMAX+1)
    CROSS = int(__import__("os").environ.get("CROSS", 0)); NOW = int(__import__("os").environ.get("NOW", 0))
    def rowvec(k1, k2, k3, x):
        taus, mult, partner = build(N, k1, k2, k3, x)
        F, pair = fvec(N, K, taus, mult, partner)
        f = c.conj() @ F
        M1 = f.sum(); M2 = np.sum(f*np.conj(f[partner])).real
        if JMAX < 0: return np.concatenate([pair, [M1.real, M1.imag, M2]])
        E = np.exp(2j*np.pi*np.outer(taus, JS)/N)
        Tf = (f[:, None]*E).sum(0); Sj = (mult[:, None]*E).sum(0)
        Wj = np.abs(Tf)**2 if not NOW else np.zeros(0)
        Xj = (Sj*np.conj(Tf)).real[1:] if CROSS else np.zeros(0)       # single-weighted pair rows  Re S(j) conj T_f(j), j>=1
        return np.concatenate([pair, [M1.real, M1.imag, M2], Wj, Xj])
    TOL = float(__import__("os").environ.get("TOL", 0.02))
    Wt = np.mean([rowvec(N, 0, 0, t)[N+2:] for t in ts[:20000]], axis=0) if JMAX >= 0 else np.zeros(0)
    if JMAX >= 0: print("two-point mollified targets W_j, j=0..JMAX:", np.array2string(Wt, precision=3), flush=True)
    target = np.concatenate([np.arange(1, N).astype(float), [m1.real, m1.imag, m2], Wt])
    tol = np.concatenate([np.zeros(N-1), [TOL*abs(m1)]*2, [TOL*m2], np.maximum(TOL, 0.02)*np.abs(Wt)+0.02]); R = len(target)
    comps = [(N-2*k2-2*k3, k2, k3) for k2 in range(N//2+1) for k3 in range((N//2-k2+1) if mode == 'unc' else 1)]
    cols = []
    def addcol(k1, k2, k3, x): cols.append((k1/N, rowvec(k1, k2, k3, x), (k1, k2, k3, float(np.max(x[k1+k2+k3:])) if k3 else 0.0)))
    for t in ts[:1500]: addcol(N, 0, 0, t)
    for _ in range(300):
        k1, k2, k3 = comps[rng.integers(len(comps))]
        addcol(k1, k2, k3, np.concatenate([rng.uniform(0, N, k1+k2+k3), rng.exponential(0.2, k3)]))
    BIG = 50.0
    for it in range(iters):
        C = np.array([q[0] for q in cols]); S = np.array([q[1] for q in cols]).T; m = len(cols)
        cobj = np.concatenate([C, BIG*np.ones(2*R)/np.maximum(np.abs(target), 1)[np.r_[0:R, 0:R]]])
        Aeq = np.zeros((1, m+2*R)); Aeq[0, :m] = 1
        Aub = np.zeros((2*R, m+2*R)); Aub[:R, :m] = S; Aub[:R, m:m+R] = -np.eye(R); Aub[R:, :m] = -S; Aub[R:, m+R:] = -np.eye(R)
        res = linprog(cobj, A_ub=Aub, b_ub=np.concatenate([target+tol, -(target-tol)]), A_eq=Aeq, b_eq=[1.0], bounds=(0, None), method='highs')
        c0 = res.eqlin.marginals[0]; lam = res.ineqlin.marginals[:R]-res.ineqlin.marginals[R:]
        slack = res.x[m:].sum(); w = res.x[:m]; val = C @ w
        new = []
        for _ in range(tries):
            k1, k2, k3 = comps[rng.integers(len(comps))]; n = k1+k2+k3
            fobj = lambda x: k1/N - c0 - lam @ rowvec(k1, k2, k3, x)
            x0 = np.concatenate([rng.uniform(0, N, n), np.minimum(rng.exponential(0.2, k3), YMAX)])
            r = minimize(fobj, x0, method='L-BFGS-B', bounds=[(None, None)]*n+[(0, YMAX)]*k3, options={'maxiter': 150})
            if r.fun < -1e-7: new.append((r.fun, k1, k2, k3, r.x))
        print(f"it {it:3d} E[s1]/N {val:.5f} slack {slack:.2e} ncols {m} newneg {len(new)} best {min([a[0] for a in new], default=0):.2e}", flush=True)
        if not new and it > 3: break
        for (_, k1, k2, k3, x) in new: addcol(k1, k2, k3, x)
    supp = sorted([(float(w[i]), cols[i][2]) for i in range(m) if w[i] > 1e-6], key=lambda q: -q[0])
    wp = sum(a for a, k in supp if k[2] > 0); wd = sum(a for a, k in supp if k[1] > 0)
    dep = [k[3] for a, k in supp if k[2] > 0]
    print(f"RESULT N={N} K={K} mode={mode}: ceiling estimate E[s1]/N = {val:.5f} (slack {slack:.1e}); weight on configs with doubles {wd:.3f}, with pairs {wp:.3f}; pair depths in support: {np.round(dep,3)}")
if __name__ == '__main__': main()
