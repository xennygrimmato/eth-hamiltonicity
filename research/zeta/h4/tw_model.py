#!/usr/bin/env python3
"""T8 (h4): does zeta'-weighted data raise the bandwidth-one ceiling?  Finite periodic model (h3's model + weights).

Configuration: N-periodic, total multiplicity N: simple on-line t (kind 1), double on-line (kind 2), off-line pair t+-iy (kind 3).
Z(t) := prod_rho 2 sin(pi (t - tau_rho)/N)   (real on R; analogue of Hardy's Z),  a_rho := Z'(tau_rho) (0 at doubles).
Statistics of a configuration (all analytic in the zeros, invariant under rotation):
  pair rows   |Shat(l)|^2, 0<l<N,  Shat(l)=sum_rho m_rho e(l tau_rho/N)                    target l       (CUE exact)
  U2   = sum_rho a_rho^2            (analogue of sum zeta'(rho) zeta'(1-rho), Gonek / BHB S2 with B=1)       target: CUE (MC)
  G1   = sum_rho prod_{rho'!=rho} (1 - z_rho'/z_rho), z=e(tau/N)  (analogue of Gonek's sum zeta'(rho)); Re, Im   target: CUE (MC)
  V_l  = |T(l)|^2, T(l)=sum_rho a_rho e(l tau_rho/N), l in LSET  (analogue of |sum zeta'(rho) x^{i gamma}|^2 = Hypothesis TW)   target: CUE (MC)
Weights are normalised by c_N := sqrt(E_CUE U2 / N) so that E U2 = N.
ceiling = min over laws of E[s1]/N subject to the chosen rows (targets within +-TOL relative, to absorb MC error).
Usage: tw_model.py N mode(rh|unc) rows(base|U2|U2G1|all) [iters] [tries]
"""
import sys, numpy as np
from scipy.optimize import linprog, minimize
rng = np.random.default_rng(7)
YMAX = 1.0

def stats(N, taus, mult, LSET, cN):
    """taus: complex array of DISTINCT points (pair members listed separately), mult: multiplicities (1 or 2)."""
    l = np.arange(1, N)
    E = np.exp(2j*np.pi*np.outer(taus, l)/N)
    S = (mult[:, None]*E).sum(0)
    pair = np.abs(S)**2
    d = taus[:, None]-taus[None, :]
    s = 2*np.sin(np.pi*d/N); np.fill_diagonal(s, 1.0)
    s = s**mult[None, :]
    a = (2*np.pi/N)*np.prod(s, axis=1)/cN
    a = np.where(mult == 1, a, 0.0)
    U2 = np.sum(a*a).real
    z = np.exp(2j*np.pi*taus/N)
    r = 1 - z[None, :]/z[:, None]; np.fill_diagonal(r, 1.0); r = r**mult[None, :]
    g = np.where(mult == 1, np.prod(r, axis=1), 0.0)
    G1 = np.sum(g)/N**2
    T = (a[:, None]*np.exp(2j*np.pi*np.outer(taus, LSET)/N)).sum(0)
    V = np.abs(T)**2
    return pair, U2, G1, V

def cue_targets(N, LSET, M=60000):
    from scipy.stats import unitary_group
    U2s = []; G1s = []; Vs = []
    Us = unitary_group.rvs(N, size=M, random_state=11)
    ev = np.linalg.eigvals(Us)
    ts = np.angle(ev)*N/(2*np.pi)
    one = np.ones(N)
    for t in ts:
        p, U2, G1, V = stats(N, t.astype(complex), one, LSET, 1.0)
        U2s.append(U2); G1s.append(G1); Vs.append(V)
    U2s = np.array(U2s); G1s = np.array(G1s); Vs = np.array(Vs)
    cN = np.sqrt(U2s.mean()/N)
    se = lambda x: x.std(0)/np.sqrt(M)
    return dict(cN=cN, U2=N, U2se=se(U2s)/cN**2, G1=G1s.mean(), G1se=se(G1s.real)+1j*se(G1s.imag),
                V=Vs.mean(0)/cN**2, Vse=se(Vs)/cN**2)

def build(N, k1, k2, k3, x):
    n = k1+k2+k3
    t = x[:n]; y = x[n:]
    taus = np.concatenate([t[:k1+k2].astype(complex), t[k1+k2:]+1j*y, t[k1+k2:]-1j*y])
    mult = np.concatenate([np.ones(k1), 2*np.ones(k2), np.ones(2*k3)])
    return taus, mult

def rowvec(N, k1, k2, k3, x, LSET, cN, rows):
    p, U2, G1, V = stats(N, *build(N, k1, k2, k3, x), LSET, cN)
    v = [p]
    if rows in ('U2', 'U2G1', 'all'): v.append([U2])
    if rows in ('U2G1', 'all'): v.append([G1.real, G1.imag])
    if rows == 'all': v.append(V)
    return np.concatenate(v)

def main():
    N = int(sys.argv[1]); mode = sys.argv[2]; rows = sys.argv[3]
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 60; tries = int(sys.argv[5]) if len(sys.argv) > 5 else 12
    TOL = 0.03
    LSET = np.arange(int(__import__("os").environ.get("LMIN", 0)), int(__import__("os").environ.get("LMAX", 3*N//2))+1)
    tg = cue_targets(N, LSET)
    cN = tg['cN']
    target = [np.arange(1, N).astype(float)]; tol = [np.zeros(N-1)]
    if rows in ('U2', 'U2G1', 'all'): target.append([tg['U2']]); tol.append([TOL*N])
    if rows in ('U2G1', 'all'): target.append([tg['G1'].real, tg['G1'].imag]); tol.append([TOL*abs(tg['G1'])]*2)
    if rows == 'all': target.append(tg['V']); tol.append(TOL*tg['V']+1e-9)
    target = np.concatenate(target); tol = np.concatenate(tol); R = len(target)
    print(f"N={N} mode={mode} rows={rows}: CUE targets: G1={tg['G1']:.4f} (se {abs(tg['G1se']):.4f}), V_l={np.array2string(tg['V'],precision=3)} rel se max {np.max(tg['Vse']/tg['V']):.4f}; U2 rel se {tg['U2se']/N:.4f}", flush=True)
    comps = [(N-2*k2-2*k3, k2, k3) for k2 in range(N//2+1) for k3 in range((N//2-k2+1) if mode == 'unc' else 1)]
    cols = []
    def addcol(k1, k2, k3, x): cols.append((k1/N, rowvec(N, k1, k2, k3, x, LSET, cN, rows), (k1, k2, k3, float(np.max(x[k1+k2+k3:])) if k3 else 0.0)))
    # seed with CUE samples (feasible in expectation) and random configs
    from scipy.stats import unitary_group
    for U in unitary_group.rvs(N, size=1500, random_state=5):
        addcol(N, 0, 0, np.angle(np.linalg.eigvals(U))*N/(2*np.pi))
    for _ in range(300):
        k1, k2, k3 = comps[rng.integers(len(comps))]
        addcol(k1, k2, k3, np.concatenate([rng.uniform(0, N, k1+k2+k3), rng.exponential(0.2, k3)]))
    BIG = 50.0
    for it in range(iters):
        C = np.array([c[0] for c in cols]); S = np.array([c[1] for c in cols]).T; m = len(cols)
        # rows: target - tol <= S w <= target + tol ; slack variables with penalty
        cobj = np.concatenate([C, BIG*np.ones(2*R)/np.maximum(np.abs(target), 1)[np.r_[0:R, 0:R]]])
        Aeq = np.zeros((1, m+2*R)); Aeq[0, :m] = 1
        Aub = np.zeros((2*R, m+2*R)); Aub[:R, :m] = S; Aub[:R, m:m+R] = -np.eye(R); Aub[R:, :m] = -S; Aub[R:, m+R:] = -np.eye(R)
        bub = np.concatenate([target+tol, -(target-tol)])
        res = linprog(cobj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=[1.0], bounds=(0, None), method='highs')
        c0 = res.eqlin.marginals[0]; lam = res.ineqlin.marginals[:R]-res.ineqlin.marginals[R:]   # reduced cost: C - c0 - lam.S
        slack = res.x[m:].sum(); w = res.x[:m]
        val = C @ w
        new = []
        for _ in range(tries):
            k1, k2, k3 = comps[rng.integers(len(comps))]
            n = k1+k2+k3
            f = lambda x: k1/N - c0 - lam @ rowvec(N, k1, k2, k3, x, LSET, cN, rows)
            x0 = np.concatenate([rng.uniform(0, N, n), np.minimum(rng.exponential(0.2, k3), YMAX)])
            r = minimize(f, x0, method='L-BFGS-B', bounds=[(None, None)]*n+[(0, YMAX)]*k3, options={'maxiter': 150})
            if r.fun < -1e-7: new.append((r.fun, k1, k2, k3, r.x))
        print(f"it {it:3d} E[s1]/N {val:.5f} slack {slack:.2e} ncols {m} newneg {len(new)} best {min([a[0] for a in new], default=0):.2e}", flush=True)
        if not new and it > 3: break
        for (_, k1, k2, k3, x) in new: addcol(k1, k2, k3, x)
    supp = sorted([(w[i], cols[i][2]) for i in range(m) if w[i] > 1e-6], key=lambda z: -z[0])
    wp = sum(a for a, k in supp if k[2] > 0); wd = sum(a for a, k in supp if k[1] > 0)
    print(f"RESULT N={N} mode={mode} rows={rows}: ceiling estimate E[s1]/N = {val:.5f} (slack {slack:.1e}); law weight on configs with doubles {wd:.3f}, with pairs {wp:.3f}; top support {supp[:6]}")
if __name__ == '__main__': main()
