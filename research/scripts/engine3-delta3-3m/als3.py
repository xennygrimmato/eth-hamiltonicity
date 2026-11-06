"""als3.py -- three-merge ALS on Delta_3 at N0 = 2 (2^18 entries) [N].
Usage: python3 als3.py SPEC restarts sweeps seed mu_max [planted|plantedgen]
  SPEC: pieces joined by '+'; a piece is 'k abc' (k in r,c,d = row / column / diagonal network with bonds (a,b,c) on the
  group pairs (01,02,12)), optionally coupled to other-merge networks with '/': e.g. 'r224/c448/d448' = a row (2,2,4) network
  that must also be a column (4,4,8) and a diagonal (4,4,8) network.
  Penalty ALS (block-exact least squares, as engine3-delta3b/als_a.py): ||f - sum P_i||^2 + mu sum_{i,k} ||P_i - Q_ik||^2,
  mu ramped 0 -> mu_max over the first 60% of the sweeps.  Score = max(residual, mismatch, both-sides residuals).
  planted: f replaced by a random sum of networks with exactly the primary shapes of SPEC (recovery control, no coupling);
  plantedgen: f replaced by a sum, one per piece, of 2 node-product tensors (in every coupled family; coupled control)."""
import sys, numpy as np, time
from d3lib import delta3, rand_net, tri_net, ls_update
from d3lib import to3, from3, gdims
KIND = {'r': 'row', 'c': 'col', 'd': 'diag'}
spec, restarts, sweeps, seed, mu_max = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
mode = sys.argv[6] if len(sys.argv) > 6 else ''
pieces = []
for p in spec.split('+'):
    parts = p.split('/')
    pieces.append([(KIND[q[0]], tuple(int(ch) for ch in q[1:])) for q in parts])
cfg = delta3(); rng = np.random.default_rng(seed)
f = cfg.target().reshape(cfg.gdims_row)
full = lambda W, kind: from3(cfg, tri_net(W), kind)
if mode == 'planted':
    f = sum(full(rand_net(rng, gdims(cfg, k), b, 1.0), k) for (k, b) in [pc[0] for pc in pieces])
elif mode == 'plantedgen':
    def ghz():
        T = 0
        for _ in range(2):
            t = rng.standard_normal(4)
            for _ in range(8): t = np.multiply.outer(t, rng.standard_normal(4))
            T = T + t
        return T.reshape(cfg.gdims_row)
    f = sum(ghz() for _ in pieces)
nf = np.linalg.norm(f); t0 = time.time(); results = []
for rs in range(restarts):
    sc = [0.1, 0.3, 1.0][rs % 3]
    P = [rand_net(rng, gdims(cfg, pc[0][0]), pc[0][1], sc) for pc in pieces]
    Q = [[rand_net(rng, gdims(cfg, k), b, sc) for (k, b) in pc[1:]] for pc in pieces]
    parts = [full(P[i], pieces[i][0][0]) for i in range(len(pieces))]
    qp = [[full(Q[i][j], pieces[i][1 + j][0]) for j in range(len(Q[i]))] for i in range(len(pieces))]
    best = None; hist = []
    for it in range(sweeps):
        mu = mu_max * min(1.0, it / (0.6 * sweeps)) if mu_max > 0 else 0.0
        for i, pc in enumerate(pieces):
            tgt = f - (sum(parts) - parts[i])
            nq = len(Q[i])
            if nq and mu > 0: tgt = (tgt + mu * sum(qp[i])) / (1 + mu * nq)
            t3 = to3(cfg, tgt, pc[0][0])
            for g in range(3): ls_update(t3, P[i], g)
            parts[i] = full(P[i], pc[0][0])
            for j in range(nq):
                k = pc[1 + j][0]; q3 = to3(cfg, parts[i], k)
                for g in range(3): ls_update(q3, Q[i][j], g)
                qp[i][j] = full(Q[i][j], k)
        res = np.linalg.norm(f - sum(parts)) / nf
        mis = max([np.linalg.norm(parts[i] - q) / max(np.linalg.norm(parts[i]), 1e-30) for i in range(len(pieces)) for q in qp[i]] or [0.0])
        hist.append(res)
        if mu_max == 0 or it >= 0.6 * sweeps:
            score = max(res, mis)
            if best is None or score < best[0]: best = (score, res, mis, it)
        if mu_max == 0 and it > 60 and hist[-40] - res < 1e-7 * hist[-40]: break
        if best is not None and best[0] < 1e-10: break
    results.append(best)
    print(f'restart {rs}: score {best[0]:.6f} residual {best[1]:.6f} mismatch {best[2]:.6f} (sweep {best[3]})', flush=True)
    if best[0] < 1e-7:
        np.savez(f'sol_{spec.replace("/", "_")}_{mode}_s{seed}_r{rs}.npz', *[p for p in parts])
R = np.array([b[:3] for b in results])
print(f'SUMMARY {spec} mu_max={mu_max} mode={mode or "f_Delta"}: {restarts} restarts x {sweeps} sweeps ({time.time()-t0:.0f}s): '
      f'min score {R[:,0].min():.6f}, median {np.median(R[:,0]):.6f}; min residual {R[:,1].min():.6f}', flush=True)
