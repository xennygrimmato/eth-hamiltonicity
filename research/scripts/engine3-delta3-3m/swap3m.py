"""swap3m.py -- 'two-edge swap' variant of the straightened-edge family, charged under three merges [C exact ranks at N0 = 2; R]:
take two edges e1 = (r1,c)-(r2,c'), e2 = (r2,c)-(r3,c') of one column pair {c,c'} (r2 = sigma(r1), r3 = sigma(r2)) and swap their
c'-ends: R = graph tensor with edges (r1,c)-(r3,c') and (r2,c)-(r2,c') (the latter horizontal), C = f - R = (Pi_tau - I) (x) I^7,
rank(Pi_tau - I) = N(N-1)/2.  Asymptotically R = (8,9,9) lambda exactly, c_col(C) = 7 lambda + log2(N(N-1)/2) = 9 lambda - 1 + log2(1-1/N)."""
import numpy as np, itertools
from straight3m import cfg, f, orig, graph_tensor, costs, game
fn = {'row': lambda v: v[0], 'col': lambda v: v[1], 'diag': lambda v: (v[0] - v[1]) % 3}
for kind, pair in (('col', (0, 1)), ('row', (0, 1)), ('diag', (0, 1))):
    sel = [i for i, (u, v) in enumerate(cfg.edges) if {fn[kind](u), fn[kind](v)} == set(pair)]
    best = None
    for i1, i2 in itertools.permutations(sel, 2):
        (a1, b1), (a2, b2) = orig[i1], orig[i2]
        # strings: make a_j the end in group pair[0]
        def ends(i):
            u, v = cfg.edges[i]; return (u, v) if fn[kind](u) == pair[0] else (v, u)
        u1, v1 = ends(i1); u2, v2 = ends(i2)
        m = [orig[i] for i in range(9) if i not in (i1, i2)] + [(cfg.sidx[(u1, i1)], cfg.sidx[(v2, i2)]), (cfg.sidx[(u2, i2)], cfg.sidx[(v1, i1)])]
        R = graph_tensor(m); C = f - R; cR, cC = costs(R), costs(C)
        lo = [[cR[k][1] for k in cR], [cC[k][1] for k in cC]]
        v, q = game(lo)
        if best is None or v < best[0]: best = (v, q, cR, cC, (i1, i2))
    v, q, cR, cC, pr = best
    print(f'swap two {kind}-pair {pair} edges {pr}:')
    for nm, cc in (('R', cR), ('C = f - R', cC)):
        print(f'  {nm:10s} ' + '  '.join(f'{k}: ranks {cc[k][0]} cut>= {cc[k][1]:.3f}' for k in cc))
    print(f'  game value (cut lower bounds) {v:.4f} at q = {np.round(q, 3)}; V_tot (T = 2) >= {v + 1.5:.4f} (trade needs < 9)')
