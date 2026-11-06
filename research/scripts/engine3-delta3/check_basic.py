"""check_basic.py -- conventions: ranks of f_Delta, transpose invariance, f as a row net (8,8,8) and col net, planted recovery."""
from d3lib import *
import numpy as np, sys
from d3lib import *
cfg = delta3(); f = cfg.to3_row(cfg.target())
print('Delta_3: strings', cfg.S, 'norm^2', f.sum(), 'row ranks', [flat_rank(f, i) for i in range(3)],
      'col ranks', [flat_rank(cfg.to3_col(f), i) for i in range(3)])
print('transpose invariant:', np.array_equal(cfg.apply_transpose(f), f))
rng = np.random.default_rng(0)
for kind in ('row', 'col'):
    b, W, h = als_sum(cfg, f, [(kind, (8, 8, 8))], rng, sweeps=50)
    print(f'f alone as {kind} net (8,8,8): residual {b:.2e}')
    b, W, h = als_sum(cfg, f, [(kind, (4, 8, 8))], rng, sweeps=200)
    print(f'f alone as {kind} net (4,8,8): residual {b:.4f}')
# planted: f' = R0 + C0 with bonds (2,2,2) random; ALS must recover
for trial in range(5):
    R0 = tri_net(rand_net(rng, cfg.gdims_row, (2, 2, 2), 1.0)); C0 = cfg.from3_col(tri_net(rand_net(rng, cfg.gdims_col, (2, 2, 2), 1.0)))
    P = R0 + C0
    bests = []
    for r in range(5):
        b, W, h = als_sum(cfg, P, [('row', (2, 2, 2)), ('col', (2, 2, 2))], rng, sweeps=500)
        bests.append(b)
        if b < 1e-8: break
    print(f'planted R0+C0 (2,2,2)+(2,2,2), trial {trial}: restarts used {len(bests)}, residuals {[f"{x:.1e}" for x in bests]}')
