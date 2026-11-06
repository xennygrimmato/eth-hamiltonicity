"""q2_sym_als.py -- Q2 (engine3-open-door.md 3.2): f_Delta = R + tau(R), tau = transpose (r,c)->(c,r), R a row network
with bonds (2,2,2) and (optionally) R simultaneously close to a column network S with bonds pc ((8,2,2): column ranks
16,16,4; or (4,4,2): 16,8,8).  Objective  ||f - R - tau R||^2 + mu ||R - S||^2, block-exact LS (lsqr) on R's factors,
exact LS on S's factors, mu ramped.  Reports the residual of f - R - tauR and the mismatch ||R - S||/||R||.
Usage: python3 q2_sym_als.py restarts sweeps seed pc(e.g. 822) [mu_max]"""
from d3lib import *
import numpy as np, sys
from scipy.sparse.linalg import LinearOperator, lsqr
restarts, sweeps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
pc = tuple(int(ch) for ch in sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != 'none' else None
mu_max = float(sys.argv[5]) if len(sys.argv) > 5 else 10.0
cfg = delta3(); f = cfg.to3_row(cfg.target()); nf = np.linalg.norm(f)
tau = cfg.apply_transpose
rng = np.random.default_rng(seed)
def update_R(W, i, tgt_f, S_full, mu):
    M = env(W, i); g = W[i].shape[0]; k = M.shape[0]
    other = [a for a in range(3) if a != i]; inv = np.argsort([i] + other)
    def L(w):   # factor -> full tensor (row order)
        X = w.reshape(g, k) @ M
        return np.transpose(X.reshape([W[i].shape[0]] + [W[a].shape[0] for a in other]), inv)
    def Lt(T):
        return (unfold(T, i) @ M.T).reshape(-1)
    sq = np.sqrt(mu)
    n = f.size
    def mv(w):
        R = L(w); return np.concatenate([(R + tau(R)).reshape(-1), sq * R.reshape(-1)])
    def rmv(y):
        a = y[:n].reshape(f.shape); b = y[n:].reshape(f.shape)
        return Lt(a + tau(a)) + sq * Lt(b)
    A = LinearOperator((2 * n, g * k), matvec=mv, rmatvec=rmv)
    rhs = np.concatenate([tgt_f.reshape(-1), sq * S_full.reshape(-1)])
    w = lsqr(A, rhs, atol=1e-12, btol=1e-12, iter_lim=2000, x0=W[i].reshape(-1))[0]
    W[i] = w.reshape(W[i].shape)
out = []
for r in range(restarts):
    W = rand_net(rng, cfg.gdims_row, (2, 2, 2), [0.1, 0.3, 1.0][r % 3])
    V = rand_net(rng, cfg.gdims_col, pc, 0.3) if pc else None
    best = (np.inf, np.inf)
    for it in range(sweeps):
        mu = 0.0 if pc is None else mu_max * min(1.0, it / (0.6 * sweeps))
        R = tri_net(W)
        if pc:
            Rc = cfg.to3_col(R)
            for i in range(3): ls_update(Rc, V, i)
            S = cfg.from3_col(tri_net(V))
        else:
            S = np.zeros_like(f)
        for i in range(3): update_R(W, i, f, S, mu)
        R = tri_net(W)
        res = np.linalg.norm(f - R - tau(R)) / nf
        mis = np.linalg.norm(R - S) / max(np.linalg.norm(R), 1e-30) if pc else 0.0
        if it >= 0.6 * sweeps or pc is None:
            if max(res, mis) < max(*best): best = (res, mis)
    out.append(best)
    print(f'restart {r}: residual ||f - R - tauR||/||f|| = {best[0]:.6f}, mismatch ||R - S||/||R|| = {best[1]:.4f}', flush=True)
out = np.array(out)
print(f'Q2 pc={pc}: {restarts} restarts x {sweeps} sweeps: min residual {out[:,0].min():.6f}, min max(res, mismatch) {out.max(axis=1).min():.6f}')
