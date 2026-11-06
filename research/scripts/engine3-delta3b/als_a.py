"""als_a.py -- task (a): N0 = 2, f_Delta (2^18 entries) = R1 + R2 + C1 + C2, R_i row networks with bonds (2,2,2) that are
also column triangle networks with bonds eR, C_j column networks (2,2,2) that are also row networks with bonds eC.
Penalty ALS (block-exact least squares): objective ||f - sum pieces||^2 + mu sum_i ||P_i - Q_i||^2, P_i the primary
(cost-3) network, Q_i the other-merge network; mu ramped 0 -> mu_max over the first 60% of sweeps, then held.
Reported: residual ||f - sum P||/||f||, mismatch max_i ||P_i - Q_i||/||P_i||, and the 'both-sides' residual
||f - sum Q||/||f|| (a genuine solution needs all three ~ 0).  [N]
Usage: python3 als_a.py restarts sweeps seed eR eC mu_max [planted]
  eR, eC like 887 (bonds (8,8,7)) or 'none' (no coupling).  planted: replace f by a planted sum of four pieces, each a
  sum of two node-product tensors (in row (2,2,1) and column (2,2,1), hence in every family here) - recovery control."""
import sys, numpy as np
from d3lib import delta3, rand_net, tri_net, ls_update
restarts, sweeps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
parse = lambda s: None if s == 'none' else tuple(int(c) for c in s)
eR, eC = parse(sys.argv[4]), parse(sys.argv[5]); mu_max = float(sys.argv[6]); planted = len(sys.argv) > 7
cfg = delta3(); rng = np.random.default_rng(seed)
f = cfg.to3_row(cfg.target())
if planted:
    def ghz_piece():
        # sum_{k=1,2} of products over the 9 nodes (each node vector on its 2 strings, 4 values)
        T = 0
        for k in range(2):
            vs = [rng.standard_normal(4) for _ in range(9)]
            t = vs[0]
            for v in vs[1:]: t = np.multiply.outer(t, v)
            T = T + t
        return T.reshape(cfg.gdims_row)   # node-major order = row order, 2 strings per node consecutive
    f = sum(ghz_piece() for _ in range(4))
nf = np.linalg.norm(f)
rowc = lambda T: T                    # row order 3-tensor
toC = cfg.to3_col; fromC = cfg.from3_col
results = []
for rs in range(restarts):
    sc = [0.1, 0.3, 1.0][rs % 3]
    P = [rand_net(rng, cfg.gdims_row, (2, 2, 2), sc), rand_net(rng, cfg.gdims_row, (2, 2, 2), sc),
         rand_net(rng, cfg.gdims_col, (2, 2, 2), sc), rand_net(rng, cfg.gdims_col, (2, 2, 2), sc)]
    kinds = ['row', 'row', 'col', 'col']
    Q = [rand_net(rng, cfg.gdims_col, eR, sc) if eR else None, rand_net(rng, cfg.gdims_col, eR, sc) if eR else None,
         rand_net(rng, cfg.gdims_row, eC, sc) if eC else None, rand_net(rng, cfg.gdims_row, eC, sc) if eC else None]
    full = lambda W, kind: tri_net(W) if kind == 'row' else fromC(tri_net(W))
    other = lambda kind: 'col' if kind == 'row' else 'row'
    parts = [full(P[i], kinds[i]) for i in range(4)]
    qparts = [full(Q[i], other(kinds[i])) if Q[i] is not None else None for i in range(4)]
    best = None; hist = []
    for it in range(sweeps):
        mu = mu_max * min(1.0, it / (0.6 * sweeps))
        for i in range(4):
            tgt = f - (sum(parts) - parts[i])
            if Q[i] is not None and mu > 0:
                tgt = (tgt + mu * qparts[i]) / (1 + mu)
            t3 = tgt if kinds[i] == 'row' else toC(tgt)
            for g in range(3): ls_update(t3, P[i], g)
            parts[i] = full(P[i], kinds[i])
            if Q[i] is not None:
                q3 = parts[i] if other(kinds[i]) == 'row' else toC(parts[i])
                for g in range(3): ls_update(q3, Q[i], g)
                qparts[i] = full(Q[i], other(kinds[i]))
        res = np.linalg.norm(f - sum(parts)) / nf
        mis = max((np.linalg.norm(parts[i] - qparts[i]) / max(np.linalg.norm(parts[i]), 1e-30)) if Q[i] is not None else 0.0 for i in range(4))
        resQ = np.linalg.norm(f - sum(qparts[i] if Q[i] is not None else parts[i] for i in range(4))) / nf
        hist.append(res)
        if it >= 0.6 * sweeps or mu_max == 0:
            score = max(res, mis, resQ)
            if best is None or score < best[0]: best = (score, res, mis, resQ, it)
        if mu_max == 0 and it > 60 and hist[-40] - res < 1e-7 * hist[-40]: break
    results.append(best)
    print(f'restart {rs}: residual {best[1]:.6f}, mismatch {best[2]:.6f}, both-sides residual {best[3]:.6f} (sweep {best[4]})', flush=True)
R = np.array([b[:4] for b in results])
print(f'SUMMARY eR={eR} eC={eC} mu_max={mu_max} planted={planted}: {restarts} restarts x {sweeps} sweeps; '
      f'min max(res,mis,resQ) = {R[:,0].min():.6f}, median {np.median(R[:,0]):.6f}; min residual {R[:,1].min():.6f}')
