#!/usr/bin/env python3
"""T1 (h3): bandwidth-one ceiling for N-periodic configurations, RH vs unconditional.

Model (exact finite analogue of the paper's setting, cf. Zeta23/PairCeiling/LawN256.lean):
 a configuration = N-periodic multiset of points with total multiplicity N per period;
 kinds: simple on-line (weight 1), double on-line (weight 2), off-line pair at (t, +-y) (weight 2cosh(2 pi l y/N)).
 Shat(l) = sum_a w_a(l) exp(2 pi i l t_a / N);   data rows: E|Shat(l)|^2 = l,  0 < l < N   (CUE / F(alpha)=alpha on (0,1)).
 ceiling p(N) = min over laws of E[#simple]/N subject to the rows.
Any law found is feasible => upper bound on the ceiling (no certificate using these rows can exceed it).
Lower bound: the paper's rank-trace certificate (exactly valid in this model, incl. off-line pairs):
 s1/N >= 2 - N r(0) - (2/N) sum_{l>=1} r(l) |Shat(l)|^2,  r = psi * psi, psi>=0 on J<=N frequencies, sum psi = 1.
Usage: t1_ceiling_cg.py N [rh|unc] [iters]
"""
import sys, numpy as np
from scipy.optimize import linprog, minimize
rng = np.random.default_rng(1)
YMAX = 1.5   # cap on normalised depth (cosh(2 pi YMAX) ~ 6e3)
TRIES = int(__import__("os").environ.get("TRIES", 20))

def shat2(N, t, w):            # t: (n,), w: (n, N-1) weights per frequency
    l = np.arange(1, N)
    E = np.exp(2j*np.pi*np.outer(t, l)/N)
    return np.abs((w*E).sum(0))**2

def weights(N, kinds, y):
    l = np.arange(1, N)
    W = []
    for k, yy in zip(kinds, y):
        if k == 1: W.append(np.ones(N-1))
        elif k == 2: W.append(2*np.ones(N-1))
        else: W.append(2*np.cosh(2*np.pi*l*yy/N))
    return np.array(W)

def mt_cert(N):
    # maximise 2 - N sum psi^2 - (2/N) sum_l l r(l) over psi>=0 (J=N), sum psi = 1
    J = N
    l = np.arange(J)
    D = np.abs(l[:, None]-l[None, :])
    A = N*np.eye(J) + (1.0/N)*D*(D > 0)      # sum_l>=1 l r(l)*2 = sum_{j!=k} |j-k| psi_j psi_k
    x = np.linalg.solve(A, np.ones(J)); x /= x.sum()
    assert x.min() > 0
    return 2 - x @ A @ x

def price(N, lam, c0, unc, tries):
    """search configurations with negative reduced cost  s1/N - c0 - sum lam_l |S(l)|^2"""
    best = []
    l = np.arange(1, N)
    for _ in range(tries):
        # random composition
        kmax = N//2
        k2 = rng.integers(0, kmax+1)
        k3 = rng.integers(0, kmax-k2+1) if unc else 0
        k1 = N-2*k2-2*k3
        kinds = [1]*k1+[2]*k2+[3]*k3
        n = len(kinds)
        isp = np.array([k == 3 for k in kinds]); base = np.array([1.0 if k == 1 else 2.0 for k in kinds])
        om = 2*np.pi*l/N
        def f(z):
            t = z[:n]; yy = np.zeros(n); yy[isp] = z[n:]
            W = np.where(isp[:, None], 2*np.cosh(np.outer(yy, om)), base[:, None])
            E = np.exp(1j*np.outer(t, om))
            S = (W*E).sum(0)
            val = k1/N - c0 - lam @ np.abs(S)**2
            # gradients
            gt = -(lam[None, :]*2*np.real(np.conj(S)[None, :]*W*1j*om[None, :]*E)).sum(1)
            gy = -(lam[None, :]*2*np.real(np.conj(S)[None, :]*(2*np.sinh(np.outer(yy, om))*om[None, :])*E)).sum(1)[isp]
            return val, np.concatenate([gt, gy])
        z0 = np.concatenate([rng.uniform(0, N, n), np.minimum(rng.exponential(0.3, k3), 1.5)])
        bnds = [(None, None)]*n + [(0.0, YMAX)]*k3
        res = minimize(f, z0, jac=True, method='L-BFGS-B', bounds=bnds, options={'maxiter': 200})
        if res.fun < -1e-9:
            t = res.x[:n]; yy = np.zeros(n); yy[isp] = res.x[n:]
            best.append((res.fun, k1, kinds, t, yy))
    best.sort(key=lambda b: b[0])
    return best[:8]

def column(N, k1, kinds, t, yy):
    return k1/N, shat2(N, t, weights(N, kinds, yy)), (k1, kinds.count(2), kinds.count(3), float(np.max(yy)) if len(yy) else 0.0)

def run(N, unc, iters):
    cols = []
    # seed: random configurations of all kinds (on-line only for RH)
    for _ in range(200):
        k2 = rng.integers(0, N//2+1); k1 = N-2*k2
        kinds = [1]*k1+[2]*k2
        cols.append(column(N, k1, kinds, rng.uniform(0, N, len(kinds)), np.zeros(len(kinds))))
    # lattice (S=0 for 0<l<N) and Poisson-like
    cols.append(column(N, N, [1]*N, np.arange(N)+0.0, np.zeros(N)))
    target = np.arange(1, N).astype(float)
    BIG = 10.0
    hist = []
    for it in range(iters):
        C = np.array([c[0] for c in cols]); S = np.array([c[1] for c in cols]).T  # (N-1, ncols)
        m = len(cols)
        # variables: w (m), slack+ (N-1), slack- (N-1)
        cobj = np.concatenate([C, BIG*np.ones(2*(N-1))])
        Aeq = np.zeros((N, m+2*(N-1)))
        Aeq[0, :m] = 1
        Aeq[1:, :m] = S; Aeq[1:, m:m+N-1] = np.eye(N-1); Aeq[1:, m+N-1:] = -np.eye(N-1)
        beq = np.concatenate([[1.0], target])
        res = linprog(cobj, A_eq=Aeq, b_eq=beq, bounds=(0, None), method='highs')
        duals = res.eqlin.marginals
        c0, lam = duals[0], duals[1:]
        slack = res.x[m:].sum()
        hist.append((res.fun, slack))
        newc = price(N, lam, c0, unc, tries=TRIES)
        if True:
            print(f"it {it:3d}  obj {res.fun:.6f}  slack {slack:.2e}  ncols {m}  dual-bound {c0+lam@target:.6f}  newneg {len(newc)}", flush=True)
        if not newc and slack < 1e-9:
            # try harder before stopping
            newc = price(N, lam, c0, unc, tries=10*TRIES)
            if not newc: break
        for (_, k1, kinds, t, yy) in newc:
            cols.append(column(N, k1, kinds, t, yy))
    w = res.x[:len(cols)]
    supp = [(w[i], cols[i][2]) for i in range(len(cols)) if w[i] > 1e-7]
    wp = sum(a for a, k in supp if k[2] > 0)
    print("law support (weight, (k1,k2,k3,maxdepth)):")
    for a, k in sorted(supp, key=lambda z: -z[0]): print("   %.5f  %s" % (a, k))
    print("total weight on configurations containing off-line pairs: %.5f" % wp)
    return res.fun, slack, lam, c0, supp

if __name__ == '__main__':
    N = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else 'rh'; iters = int(sys.argv[3]) if len(sys.argv) > 3 else 150
    print(f"N={N} mode={mode}  rank-trace (MT-type) certificate lower bound p_MT(N) = {mt_cert(N):.6f}")
    val, slack, lam, c0, supp = run(N, mode == 'unc', iters)
    print(f"RESULT N={N} mode={mode}: law value (upper bound on ceiling) = {val:.6f}, slack={slack:.1e}, support size {len(supp)}")
    print("dual lambda_l:", np.array2string(lam, precision=4, max_line_width=200))
    np.save(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/cg_{N}_{mode}.npy", np.concatenate([[c0], lam]))
