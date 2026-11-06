"""check_sym.py -- [C] sigma'(r,c) = (c-r, -r) is an order-3 automorphism of Delta_3 fixing every triangle and cycling
rows -> columns -> diagonals; f_Delta is invariant; the transpose (r,c)->(c,r) swaps rows/cols and fixes the diagonal class.
Also: under each merge every edge crosses groups; f_Delta is <8,8,8> (cost 9) under each merge (ranks 64)."""
import numpy as np, itertools
from d3lib import *
cfg = delta3(); f = cfg.target().reshape(cfg.gdims_row)
s = SIGMA
print('order 3:', all(s(s(s(v))) == v for v in cfg.nodes))
print('triangle class fixed setwise (each triangle r+c=t maps to itself):', all((s(v)[0] + s(v)[1]) % 3 == (v[0] + v[1]) % 3 for v in cfg.nodes))
fn = {k: (lambda kk: (lambda v: {'row': v[0], 'col': v[1], 'diag': (v[0] - v[1]) % 3}[kk]))(k) for k in ('row', 'col', 'diag')}
for a, b in (('row', 'col'), ('col', 'diag'), ('diag', 'row')):
    ok = all(len({fn[b](s(v)) for v in cfg.nodes if fn[a](v) == g}) == 1 for g in range(3))
    print(f'sigma maps {a} groups onto {b} groups:', ok)
P = node_perm(cfg, s)
print('f invariant under sigma:', np.array_equal(apply_perm(cfg, f, P), f))
tr = lambda v: (v[1], v[0])
print('transpose preserves triangles:', all((tr(v)[0] + tr(v)[1]) % 3 == (v[0] + v[1]) % 3 for v in cfg.nodes),
      ' maps diag classes to diag classes:', all(len({(tr(v)[0] - tr(v)[1]) % 3 for v in cfg.nodes if (v[0] - v[1]) % 3 == g}) == 1 for g in range(3)))
for k in ('row', 'col', 'diag'):
    print(f'{k}: edges crossing = {sum(1 for (u, v) in cfg.edges if fn[k](u) != fn[k](v))} of 9; flattening ranks of f:',
          [flat_rank(to3(cfg, f, k), i) for i in range(3)])
