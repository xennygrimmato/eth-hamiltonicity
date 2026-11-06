"""floor_finite.py -- the exact finite test for the three-merge piece-type criterion on Delta_3, all shapes, all real bond
dimensions, T types [C over every field for the flattening part; CVZ part over C, R].
Criterion (engine3-open-door.md 1.7, p = 3 merges, r = 3 groups each, nu_3 = 3/2):
   V_tot(tau_1..tau_T) = max_x min_k sum_j x_j c_k(tau_j) + 1.5 log2 T;  rho < 1/2 iff V_tot < 4.5 m0;  any trade iff < 9 m0.
Lower bound: for each orientation o, sum_j rank_o(tau_j) >= 2^{|o|}, and rank_o(tau_j) <= 2^{min_k Phi_{o,k}(c_k(tau_j))},
so some type has c_k >= g_k(o,T) := Phi_{o,k}^{-1}(|o| - log2 T) for ALL k (a box corner).  CVZ (uniform quantum functional on
merge k's three groups): some type has c_k >= 9 m0 - 1.5 log2 T.  The adversary mixes these types:
   V_tot >= LB(T) := max_{p in Delta(S_T)} min_k sum_s p_s s_k + 1.5 log2 T.
Computed for m0 = 1 (3^9 orientations) and m0 = 2 (6^9 bit orientations), T = 1..64; with and without the CVZ points."""
import numpy as np, itertools, sys
from scipy.optimize import linprog
from lib3m import *

def check_ginv():
    rng = np.random.default_rng(0); bad = 0
    for _ in range(400):
        L8 = rng.integers(0, 10, size=8).astype(float); L8[0] = L8[7] = 12
        t = rng.uniform(0, 12)
        M = Mg(L8[None, :])[0]
        # LP: min sum x s.t. L_s + cut_s.x >= t for all s
        r = linprog(np.ones(3), A_ub=-CUT, b_ub=L8 - t, bounds=[(0, None)] * 3, method='highs')
        g = ginv(M[None, :], np.array([t]))[0]
        if abs(r.fun - g) > 1e-7: bad += 1
    print(f'closed-form inverse vs LP on 400 random instances: {bad} mismatches', flush=True)

def pareto(V):
    V = np.unique(np.round(V, 9), axis=0)
    keep = []
    order = np.argsort(-V.sum(1))
    for i in order:
        v = V[i]
        if not any(np.all(V[j] >= v - 1e-12) and np.any(V[j] > v + 1e-12) for j in keep): keep.append(i)
    return V[keep]

def game(S):
    S = np.asarray(S, float); n = len(S)
    A = np.hstack([-S.T, np.ones((3, 1))])
    r = linprog(np.r_[np.zeros(n), -1], A_ub=A, b_ub=np.zeros(3), A_eq=[np.r_[np.ones(n), 0]], b_eq=[1],
                bounds=[(0, None)] * n + [(None, None)], method='highs')
    p = r.x[:n]
    return -r.fun, [(tuple(np.round(S[i], 3)), round(p[i], 3)) for i in np.argsort(-p)[:4] if p[i] > 1e-9]

if __name__ == '__main__':
    check_ginv()
    for m0 in (1, 2):
        idx, X, Y, rk = enumerate_orients(m0)
        Ms = {k: Mg(legs8(X[k], Y[k])).astype(float) for k in 'rcd'}
        print(f'\nN0 = {2**m0}: {idx.shape[0]} bit orientations; thresholds: rho<1/2 iff V_tot < {4.5*m0}, any trade iff < {9*m0}', flush=True)
        for T in (1, 2, 3, 4, 5, 6, 8, 12, 16, 32, 64):
            lt = np.log2(T); t = rk - lt
            ok = t > 0
            G = np.stack([ginv(Ms[k][ok], t[ok]) for k in 'rcd'], 1)
            G = G[G.min(1) > 0] if (G.min(1) > 0).any() else G
            # keep a manageable candidate set: the top by min and by every weighted sum
            cand = np.unique(np.round(G, 9), axis=0)
            if len(cand) > 3000:
                sc = [cand.min(1)] + [cand @ w for w in itertools.product((0, 1, 2, 3), repeat=3) if sum(w) > 0]
                sel = set()
                for s in sc: sel.update(np.argsort(-s)[:40].tolist())
                cand = cand[sorted(sel)]
            cand = pareto(cand)
            cvz = np.array([[9 * m0 - 1.5 * lt, 0, 0], [0, 9 * m0 - 1.5 * lt, 0], [0, 0, 9 * m0 - 1.5 * lt]])
            vf, sf = game(cand); vc, sc_ = game(np.vstack([cand, cvz]))
            minfl = cand.min(1).max()
            print(f'  T = {T:3d}: max_o min_k g_k = {minfl:.4f};  game floor flattening-only {vf:.4f} -> LB {vf+1.5*lt:.4f} ;'
                  f'  with CVZ {vc:.4f} -> LB {vc+1.5*lt:.4f}  [rho<1/2 {"REFUTED" if vc+1.5*lt >= 4.5*m0 else "open"}; '
                  f'trade {"REFUTED" if vc+1.5*lt >= 9*m0 else "open"}]  mix {sc_[:3]}', flush=True)
