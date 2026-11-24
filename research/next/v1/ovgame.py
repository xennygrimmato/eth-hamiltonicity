"""Sparse exact embeddings of the disjointness matrix R_d = [[1,1],[1,0]]^{(x)d}.

A gadget is a factorisation R_{d0} = P Q (over some field).  r[a] = nnz of row a of P,
c[b] = nnz of column b of Q.  Tensoring gadgets over blocks of coordinates gives
OV in time ~ n * 2^{tau d}, where for vectors of relative weight alpha (rows) and beta (columns)
  cost_rows = sum_g lam_g * E_{x~Bern(alpha)^d0} log2 r_g(x) / d0   (same for columns with c, beta)
and tau = max_{alpha,beta} min_lam max(cost_rows, cost_cols).
"""
import itertools, math, numpy as np

def profile_costs(r, c, d0, alphas):
    # returns rho(alpha) array, kappa(beta) array (per coordinate)
    lr = np.log2(np.array(r, float)); lc = np.log2(np.array(c, float))
    w = np.array([bin(x).count("1") for x in range(2**d0)])
    out_r = []; out_c = []
    for a in alphas:
        p = a**w * (1-a)**(d0-w)
        out_r.append((p*lr).sum()/d0); out_c.append((p*lc).sum()/d0)
    return np.array(out_r), np.array(out_c)

def game_value(rhos, kappas):
    # min over mixtures of max(rho, kappa) = max_theta min_g theta*rho+(1-theta)*kappa
    th = np.linspace(0, 1, 2001)[:, None]
    return (th*rhos[None, :] + (1-th)*kappas[None, :]).min(axis=1).max()

def tau_star(gadgets, grid=61, verbose=False):
    alphas = np.linspace(0.005, 0.995, grid)
    R = []; C = []
    for (r, c, d0) in gadgets:
        a, b = profile_costs(r, c, d0, alphas); R.append(a); C.append(b)
    R = np.array(R); C = np.array(C)       # gadgets x grid
    best = (-1, None)
    for i, al in enumerate(alphas):
        for j, be in enumerate(alphas):
            if al + be > 1.0: continue
            v = game_value(R[:, i], C[:, j])
            if v > best[0]: best = (v, (al, be))
    return best

if __name__ == "__main__":
    F1 = ([1, 1], [2, 1], 1); F2 = ([2, 1], [1, 1], 1); F3 = ([1, 2], [1, 2], 1)
    print("d0=1 gadgets:", tau_star([F1, F2, F3]))
    print("walls: gamma2 log2(2/sqrt3) =", math.log2(2/math.sqrt(3)), " Ye 2026 degree 0.3199")
