"""Task B (sizes): exact size of phi(G, r, order) on large sparse graphs.

Checks the exact formulas of linear-encoding.md, Section 5:
  primary variables      5m - 2 d_r                     edge clauses   10m - 6 d_r
  cardinality variables  8m - 2 d_r - 4n + 2            card. clauses  32m - 8 d_r - 15n + 6
  local (mixed + rotation) variables <= 11 (m - d_r)
  crossing variables     <= 2 m' ceil(log2 n) + 2 m' + 4 n + 1,  m' = m - d_r,
and prints the measured growth  crossing_vars / (m log2 n)  (it does not tend to 0: the
encoding is Theta(m log n), not O(m)).  Width <= 3.  Prints PASS/FAIL.
"""
import math
import random
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc_lib import build_cnf  # noqa


def random_regular(n, d, rng):
    while True:
        stubs = [v for v in range(n) for _ in range(d)]
        rng.shuffle(stubs)
        E = set()
        ok = True
        for i in range(0, len(stubs), 2):
            a, b = stubs[i], stubs[i + 1]
            if a == b or (min(a, b), max(a, b)) in E:
                ok = False; break
            E.add((min(a, b), max(a, b)))
        if ok:
            return sorted(E)


rng = random.Random(1)
fails = 0
print(f"{'n':>6} {'m':>6} {'d':>2} {'vars':>8} {'clauses':>9} {'vars/m':>7} {'cross/(m lg n)':>15}")
for d in (3, 4):
    for n in (16, 64, 256, 1024, 4096):
        E = random_regular(n, d, rng) if d == 3 or n <= 1024 else random_regular(n, d, rng)
        m = len(E)
        r = rng.randrange(n)
        perm = list(range(n)); rng.shuffle(perm)
        pos = {v: perm[v] for v in range(n)}
        B, z, prim, info = build_cnf(n, E, r, pos, 'full')
        dr = sum(1 for e in E if r in e)
        mp = m - dr
        tag = B.kind_count
        ok = (info['nprim'] == 5 * m - 2 * dr
              and tag.get('edge', 0) == 10 * m - 6 * dr
              and info['ncard'] == 8 * m - 2 * dr - 4 * n + 2
              and tag.get('card', 0) == 32 * m - 8 * dr - 15 * n + 6
              and info['nlocal'] <= 11 * mp
              and info['ncross'] <= 2 * mp * math.ceil(math.log2(n)) + 2 * mp + 4 * n + 1
              and max(len(c) for c in B.clauses) <= 3)
        fails += not ok
        print(f"{n:>6} {m:>6} {d:>2} {B.nv:>8} {len(B.clauses):>9} {B.nv / m:>7.2f} "
              f"{info['ncross'] / (m * math.log2(n)):>15.3f}  local={info['nlocal']} "
              f"cross={info['ncross']} {'ok' if ok else 'MISMATCH'}")
print("PASS" if fails == 0 else f"FAIL ({fails})")
