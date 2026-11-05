"""Best certificate of the whole flattening method (lossy keep/fix/pair contractions, engine2-decorrelated §8.2)
for a configuration with several merges: D = max_M min_k d_k(M), where for a contraction M with net group
outflows n_g (g a group of merge k), d_k(M) = LP min sum e s.t. e(S|rest) >= sum_{g in S} n_g for all S
(= |n_1| for 2 groups, max(max|n_g|, sum|n_g|/2) for 3 groups).  d_k depends only on the oriented edge set of
M (pairings/ends only fix a_v - b_v = out_v - in_v), so we enumerate all 3^|E| orientations exactly.
The bound applies to every term whose cost is >= c_flat (in particular to every network term, local or not):
every decomposition has a term of cost >= D*lam - O(log T), and no flattening argument certifies more."""
import itertools, sys
from lib import *
def dk(ns):
    a = [abs(x) for x in ns]
    return a[0] if len(a) == 2 else max(max(a), sum(a) / 2)
def D(cfg):
    ed = cfg['edges']; best = (-1, None)
    for st in itertools.product((0, 1, -1), repeat=len(ed)):
        net = {v: 0 for v in cfg['nodes']}
        for (p, q), s in zip(ed, st):
            if s: net[p] += s; net[q] -= s
        val = min(dk([sum(net[v] for v in G) for G in mg]) for mg in cfg['merges'])
        if val > best[0]: best = (val, st)
    return best
if __name__ == "__main__":
  for name, cfg in (('crossing', config_crossing(2)), ('hexagon (3x2 grid)', config_hexagon(2)), ("Majdoddin's C", config_C(2))):
      v, st = D(cfg); print(f"{name}: D = {v}   (|E| = {len(cfg['edges'])}; optimal orientation {st})")
  # C with only two of its three merges, for comparison
  c = config_C(2)
  for ks in ((0, 1), (0,), (1,)):
      c2 = dict(c); c2['merges'] = [c['merges'][k] for k in ks]; print(f"C restricted to merges {ks}: D = {D(c2)[0]}")
