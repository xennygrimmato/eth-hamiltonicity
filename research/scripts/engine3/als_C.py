"""Heuristic [C]: real ALS for f_C = sum_t T_t with T_t a triangle network on the groups of merge k_t with given bonds.
Block-coordinate least squares: for term t and group g, T_t[legs_g, rest] = W_g[legs_g, bonds_g] M[bonds_g, rest] is
linear in W_g; we fit W_g to (f_C - other terms).  Reports best relative residual over restarts.
Usage: python3 als_C.py N   (runs the profile list for that N)."""
import numpy as np, sys, itertools, math
from lib import *
PAIRS = [(0, 1), (0, 2), (1, 2)]
def setup(N):
    cfg = config_C(N); G = graph_tensor(cfg).astype(float)
    perms = []
    for k in range(3):
        gl = group_legs(cfg, cfg['merges'][k]); order = gl[0] + gl[1] + gl[2]
        perms.append(order)
    return cfg, G, perms
def term_tensor(W, d, N):  # W[g]: (N^4, bonds of g in PAIRS order)
    A, B, C = W  # A: (N4, d01, d02), B: (N4, d01, d12), C: (N4, d02, d12)
    return np.einsum('xab,yac,zbc->xyz', A, B, C)
def fit(N, terms, iters=300, restarts=4, seed=0, ridge=1e-10):
    cfg, G, perms = setup(N); n4 = N ** 4
    Gk = [np.transpose(G, perms[k]).reshape(n4, n4, n4) for k in range(3)]
    # each term lives in its own leg order; convert between orders through the 12-leg form
    def to12(T3, k):
        T = T3.reshape((N,) * 12); inv = np.argsort(perms[k]); return np.transpose(T, inv)
    def from12(T, k): return np.transpose(T, perms[k]).reshape(n4, n4, n4)
    rng = np.random.default_rng(seed); best = 9e9; nrm = np.linalg.norm(G)
    for r in range(restarts):
        Ws = []
        for k, d in terms:
            Ws.append([rng.standard_normal((n4, d[(0, 1)], d[(0, 2)])) * .3, rng.standard_normal((n4, d[(0, 1)], d[(1, 2)])) * .3,
                       rng.standard_normal((n4, d[(0, 2)], d[(1, 2)])) * .3])
        Ts = [to12(term_tensor(W, d, N), k) for W, (k, d) in zip(Ws, terms)]
        for it in range(iters):
            for t, (k, d) in enumerate(terms):
                Rt = from12(G - sum(Ts[s] for s in range(len(terms)) if s != t), k)
                A, B, C = Ws[t]
                M = np.einsum('yac,zbc->abyz', B, C).reshape(-1, n4 * n4)
                A = np.linalg.solve(M @ M.T + ridge * np.eye(len(M)), M @ Rt.reshape(n4, -1).T).T.reshape(A.shape)
                M = np.einsum('xab,zbc->acxz', A, C).reshape(-1, n4 * n4)
                B = np.linalg.solve(M @ M.T + ridge * np.eye(len(M)), M @ Rt.transpose(1, 0, 2).reshape(n4, -1).T).T.reshape(B.shape)
                M = np.einsum('xab,yac->bcxy', A, B).reshape(-1, n4 * n4)
                C = np.linalg.solve(M @ M.T + ridge * np.eye(len(M)), M @ Rt.transpose(2, 0, 1).reshape(n4, -1).T).T.reshape(C.shape)
                Ws[t] = [A, B, C]; Ts[t] = to12(term_tensor(Ws[t], d, N), k)
        res = np.linalg.norm(sum(Ts) - G) / nrm; best = min(best, res)
        if best < 1e-6: break
    return best
if __name__ == '__main__':
    N = int(sys.argv[1]); Bd = lambda a, b, c: {(0, 1): a, (0, 2): b, (1, 2): c}
    if N == 2:
        profs = [[(0, Bd(2, 8, 2)), (1, Bd(1, 4, 4))],  # known S=48
                 [(0, Bd(2, 2, 4)), (1, Bd(2, 2, 4))], [(0, Bd(4, 2, 2)), (1, Bd(2, 4, 2))], [(0, Bd(2, 4, 2)), (1, Bd(2, 2, 4))],
                 [(0, Bd(2, 2, 4)), (2, Bd(2, 2, 4))], [(0, Bd(2, 2, 2)), (1, Bd(2, 2, 2)), (2, Bd(2, 2, 2))],
                 [(0, Bd(2, 2, 4)), (1, Bd(2, 2, 4)), (2, Bd(2, 2, 4))], [(0, Bd(2, 4, 4)), (1, Bd(2, 2, 4))],
                 [(0, Bd(4, 4, 2)), (1, Bd(2, 2, 2))], [(0, Bd(2, 4, 2)), (1, Bd(1, 4, 4))]]
    else:
        profs = [[(0, Bd(3, 27, 3)), (1, Bd(3, 9, 9))],      # analogue of the known decomposition (S = 486 < 729)
                 [(0, Bd(3, 9, 9)), (1, Bd(3, 9, 9))], [(0, Bd(3, 9, 3)), (1, Bd(3, 9, 9))], [(0, Bd(3, 27, 3)), (1, Bd(3, 3, 9))],
                 [(0, Bd(3, 9, 3)), (1, Bd(3, 3, 9)), (2, Bd(3, 9, 3))]]
    for pr in profs:
        S = sum(d[(0, 1)] * d[(0, 2)] * d[(1, 2)] for _, d in pr)
        r = fit(N, pr, iters=150 if N == 2 else 40, restarts=4 if N == 2 else 2)
        print(f"N={N} profile {[(k, (d[(0,1)], d[(0,2)], d[(1,2)])) for k, d in pr]}  S={S} (N^6={N**6}, max cost {max(math.log2(d[(0,1)]*d[(0,2)]*d[(1,2)]) for _, d in pr):.2f} bits): residual {r:.3e}", flush=True)
