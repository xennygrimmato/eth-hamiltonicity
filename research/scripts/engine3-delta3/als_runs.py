"""als_runs.py -- Q1: f_Delta ~ sum of row / column triangle networks at N0 = 2, ALS with random restarts.
Usage: python3 als_runs.py SPEC restarts sweeps seed [config]
  SPEC like 'r222+c222' or 'r224+c224' or 'r222+c222+r222'; bonds listed as (d01,d02,d12).
  config: delta3 (default) | two (restriction to two triangles)."""
from d3lib import *
import numpy as np, sys, time
spec, restarts, sweeps, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
which = sys.argv[5] if len(sys.argv) > 5 else 'delta3'
cfg = delta3() if which == 'delta3' else two_triangles()
f = cfg.to3_row(cfg.target())
terms = [('row' if t[0] == 'r' else 'col', tuple(int(ch) for ch in t[1:])) for t in spec.split('+')]
rng = np.random.default_rng(seed)
res = []; t0 = time.time()
for r in range(restarts):
    sc = [0.1, 0.3, 1.0][r % 3]
    b, W, h = als_sum(cfg, f, terms, rng, sweeps=sweeps, init_scale=sc)
    res.append(b)
    if b < 1e-8:
        print(f'restart {r}: EXACT candidate residual {b:.2e}', flush=True)
        np.savez(f'sol_{which}_{spec}_s{seed}_r{r}.npz', *[w for Wk in W for w in Wk])
res = np.array(res)
print(f'{which} {spec}: {restarts} restarts x <= {sweeps} sweeps (seed {seed}, {time.time()-t0:.0f}s): min residual {res.min():.6f}, '
      f'median {np.median(res):.6f}, max {res.max():.6f}; min captured norm^2 fraction 1-res^2 = {1-res.min()**2:.6f}')
u, c = np.unique(res.round(4), return_counts=True)
print('  histogram (4 d.p.):', dict(zip(u.tolist(), c.tolist())), flush=True)
