"""flat_coupled.py -- exact flattening test [C, every field] at N0 = 2 for coupled three-merge families, each piece given by
an exact bond shape under EVERY merge (own + the two others); bound at an orientation = min over the three merges of the
network min-cut bound; all placements of every shape tried (stops at the first passing placement combination).
Each family is listed with its uniform-q criterion value V_tot = (sum of the three costs)/3 + 1.5 log2 T (trade iff < 9)."""
import numpy as np, itertools, sys
from lib3m import *
from ansatz_shape import keys, placements
rk, L, M = keys(1)
lg = lambda sh: tuple(np.log2(sh))
cache = {}
def B(k, sh):
    if (k, sh) not in cache: cache[(k, sh)] = logbound(L[k], sh)
    return cache[(k, sh)]
def test(family, label):
    """family: list of pieces; piece = dict merge -> dims shape."""
    opts = []
    for pc in family:
        per = [[(k, p) for p in placements(lg(pc[k]))] for k in 'rcd']
        opts.append([min_combo for min_combo in itertools.product(*per)])
    # relaxation first: per piece, the best placement at each orientation separately (valid for refutation)
    tot = np.zeros_like(rk)
    for op in opts:
        tot += np.max([2.0 ** np.minimum(np.minimum(B(*c[0]), B(*c[1])), B(*c[2])) for c in op], axis=0)
    relax = (np.log2(tot) - rk).min()
    best = None; n = 0
    ncomb = int(np.prod([len(op) for op in opts]))
    if relax < -1e-9 or ncomb > 30000:
        T = len(family); cost = max(sum(np.log2(pc[k]).sum() for k in 'rcd') for pc in family)
        Vt = cost / 3 + 1.5 * np.log2(T)
        print(f'{label}: V_tot(uniform q) = {Vt:.3f}; per-piece-best-placement relaxation slack {relax:+.4f} -> '
              f'{"REFUTED exactly (all placements)" if relax < -1e-9 else "relaxation passes (" + str(ncomb) + " combos, not enumerated)"}', flush=True)
        return
    for combo in itertools.product(*opts):
        n += 1
        tot = np.zeros_like(rk)
        for pcp in combo:
            tot += 2.0 ** np.minimum(np.minimum(B(*pcp[0]), B(*pcp[1])), B(*pcp[2]))
        sl = (np.log2(tot) - rk).min()
        if best is None or sl > best: best = sl
        if sl >= -1e-9: break
    T = len(family); cost = max(sum(np.log2(pc[k]).sum() for k in 'rcd') for pc in family)
    Vt = cost / 3 + 1.5 * np.log2(T)
    print(f'{label}: V_tot(uniform q) = {Vt:.3f}; best slack {best:+.4f} over {n} placement combos -> '
          f'{"PASSES (go to ALS)" if best >= -1e-9 else "REFUTED exactly"}', flush=True)
cyc = lambda own, oth: [dict(r=own, c=oth, d=oth), dict(c=own, d=oth, r=oth), dict(d=own, r=oth, c=oth)]
FULL = (8, 8, 8)
if __name__ == "__main__":
  for own, oth in (((2, 2, 4), (4, 4, 8)), ((2, 2, 4), (4, 4, 4)), ((2, 2, 4), (2, 4, 8)), ((2, 2, 4), (4, 8, 8)),
                 ((4, 4, 4), (4, 4, 4)), ((4, 4, 4), (4, 4, 8)), ((2, 4, 4), (4, 4, 4)), ((2, 4, 4), (4, 4, 8)),
                 ((2, 2, 2), (8, 8, 8)), ((2, 2, 4), (8, 8, 8))):
      test(cyc(own, oth), f'T=3  R+C+D own {own} others {oth}')
if __name__ == "__main__":
  for own, oth in (((2, 2, 2), (4, 4, 4)), ((2, 2, 2), (2, 4, 4)), ((2, 2, 2), (4, 4, 8)), ((2, 2, 2), (2, 4, 8))):
      test(cyc(own, oth) * 2, f'T=6  2x(R+C+D) own {own} others {oth}')
