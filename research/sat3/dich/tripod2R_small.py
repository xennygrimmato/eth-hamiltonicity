"""Smaller version of tripod2R.py (n <= 12): K in the spine book T' x R of the T-book, flat (two rays of T')
against non-flat (three rays).  Same model: T x T' x R, flats R^3, exact mean widths."""
import math, time
from tripod2R import P3, run, tips
for R in (0.22, 0.2747, 0.32):
    for ang, name in (([0.0], "1 point per ray"), ([-math.pi / 4, math.pi / 4], "2 points per ray"), ([-math.pi / 3, 0.0, math.pi / 3], "3 points per ray")):
        for rays in ((0, 1), (0, 1, 2)):
            K = [P3(None, 0, None, 0, R), P3(None, 0, None, 0, -R)] + [P3(None, 0, k, R * math.cos(f), R * math.sin(f)) for k in rays for f in ang]
            if 3 + len(K) > 12: continue
            t0 = time.time(); v = run(tips + K, 0b111)
            print(f"R={R:.4f} {name:17s} rays of T' used: {len(rays)}  n={3 + len(K):2d}  max delta(tips) = {v:.5f}  [{time.time() - t0:.0f}s]", flush=True)
