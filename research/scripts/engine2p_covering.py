#!/usr/bin/env python3
"""engine2p_covering.py -- the covering bound for arbitrary grouping families (mechanism 7 in
research/engine2-probabilistic.md).

Model (one level of Theorem A on a g x g grid, per-rectangle pieces).  A rectangle q = (i<i', j<j')
has corner nodes (i,j),(i,j'),(i',j),(i',j').  A grouping pi (partition of the g^2 nodes into
blocks) induces a TYPE on q:
   'row'  : (i,j)~(i,j') and (i',j)~(i',j') and the two blocks differ
   'col'  : (i,j)~(i',j) and (i,j')~(i',j') and the two blocks differ
   'free' : (i,j)~(i',j') and (i,j')~(i',j), blocks differ      (F has rank 1 across this cut)
   'int'  : all four corners in one block                        (costs nothing, no recursion)
   'other': anything else (>= 3 blocks touched)
Adversary pieces: s_r (row rank 2^{2 lam}, col rank ~1), s_c (col rank 2^{2 lam}, row rank ~1).
One-ended cost of rectangle q in term iota under grouping pi (in units of 2 lam):
   s_r : 1 on 'row' and 'other', 0 on 'col' and 'free'   (row cut is refined by 'other')
   s_c : 1 on 'col' and 'other', 0 on 'row' and 'free'
   'int': 0 for both.
(Full bits of a rectangle = 2 in these units, so cost/|R| ... ratio rho_eff = cost/(2|R|)... we
report agree = cost in units of 2lam and the ratio agree/|R| = rho_eff.)
Level value V = max_iota min_pi cost(iota, pi) / |R|  (= rho_eff of the level, for these pieces).
Two groupings (rows, cols): V = ceil(|R|/2)/|R| -> 1/2.
Claim (covering bound): for ANY family of groupings into blocks of size <= s, with s = o(g^2)...
   V >= 1/2 - O(sqrt(log M / |R|)) - (internal fraction),  M = #groupings.

Exact computation for g = 3 over all partitions of the 9 nodes into blocks of size <= 3 (the
sub-network must then have >= 3 = g nodes), and for g = 4 over all partitions into 4 blocks of 4
with the adversary's iota sampled (lower bound on V by sampling; exact max needs 2^36 iotas).
"""
import itertools, random, sys
from math import comb, ceil
import numpy as np

def rectangles(g):
    R = []
    for i, ip in itertools.combinations(range(g), 2):
        for j, jp in itertools.combinations(range(g), 2):
            R.append((i*g+j, i*g+jp, ip*g+j, ip*g+jp))   # x=(i,j) y=(i,j') u=(i',j) v=(i',j')
    return R

def rect_type(block, q):
    x, y, u, v = (block[c] for c in q)
    if x == y == u == v: return 'int'
    if x == y and u == v and x != u: return 'row'
    if x == u and y == v and x != y: return 'col'
    if x == v and y == u and x != y: return 'free'
    return 'other'

def set_partitions_bounded(n, s):
    """all set partitions of range(n) with blocks of size <= s, as block-label lists"""
    def rec(i, labels, sizes):
        if i == n:
            yield list(labels); return
        for b in range(len(sizes)):
            if sizes[b] < s:
                labels.append(b); sizes[b] += 1
                yield from rec(i+1, labels, sizes)
                labels.pop(); sizes[b] -= 1
        labels.append(len(sizes)); sizes.append(1)
        yield from rec(i+1, labels, sizes)
        labels.pop(); sizes.pop()
    yield from rec(0, [], [])

def masks_for(g, parts, R):
    """for each partition: (rowmask, colmask, othermask) over rectangles; also stats"""
    rows, cols, oth, free, inte = [], [], [], 0, 0
    for block in parts:
        rm = cm = om = 0
        for k, q in enumerate(R):
            t = rect_type(block, q)
            if t == 'row': rm |= 1 << k
            elif t == 'col': cm |= 1 << k
            elif t == 'other': om |= 1 << k
            elif t == 'free': free += 1
            else: inte += 1
        rows.append(rm); cols.append(cm); oth.append(om)
    return (np.array(rows, dtype=np.uint64), np.array(cols, dtype=np.uint64),
            np.array(oth, dtype=np.uint64), free, inte)

def cost_min(iota_r, nR, rows, cols, oth):
    """iota_r = bitmask of rectangles carrying s_r; min over partitions of agreements"""
    full = (1 << nR) - 1
    ir = np.uint64(iota_r); ic = np.uint64(full ^ iota_r)
    agree = np.bitwise_count((rows & ir) | (cols & ic) | oth)
    return int(agree.min()), int(agree.argmin())

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL "), name); ok = ok and cond

# ---- g = 3 exact ----
g = 3; R = rectangles(g); nR = len(R)
parts = list(set_partitions_bounded(g*g, g))
rows, cols, oth, free, inte = masks_for(g, parts, R)
print("g=3: %d rectangles, %d partitions with blocks <= 3; free rects total %d, internal %d"
      % (nR, len(parts), free, inte))
best = -1; best_iota = None
for iota in range(1 << nR):
    m, arg = cost_min(iota, nR, rows, cols, oth)
    if m > best: best, best_iota = m, iota
print("   V(all partitions, blocks<=3) = %d/%d = %.4f ; two-grouping value = %d/%d" %
      (best, nR, best/nR, ceil(nR/2), nR))
# worst-case partition for the best iota: how many groupings are 'needed'?
# restrict to partitions into exactly g blocks of size g (balanced, the recursion's shape)
bal = [p for p in parts if max(p)+1 == g]
rows_b, cols_b, oth_b, free_b, inte_b = masks_for(g, bal, R)
best_b = max(cost_min(iota, nR, rows_b, cols_b, oth_b)[0] for iota in range(1 << nR))
print("   balanced (3 blocks of 3): %d partitions, V = %d/%d = %.4f" % (len(bal), best_b, nR, best_b/nR))
check("g=3: no grouping family pushes the level below 1/3 of |R| (covering bound regime)", best >= nR/3)

# ---- g = 4: all balanced partitions into 4 blocks of 4, sampled iota ----
g = 4; R = rectangles(g); nR = len(R)
def balanced_partitions(n, k):
    # partitions of range(n) into k blocks of size n//k, canonical (block labels by min element)
    s = n // k
    def rec(remaining, blocks):
        if not remaining:
            yield blocks; return
        first = remaining[0]; rest = remaining[1:]
        for others in itertools.combinations(rest, s-1):
            blk = (first,) + others
            rem2 = [x for x in rest if x not in others]
            yield from rec(rem2, blocks + [blk])
    for bl in rec(list(range(n)), []):
        lab = [0]*n
        for b, blk in enumerate(bl):
            for x in blk: lab[x] = b
        yield lab
bal4 = list(balanced_partitions(16, 4))
print("g=4: %d rectangles, %d balanced partitions into 4 blocks of 4" % (nR, len(bal4)))
rows4, cols4, oth4, free4, inte4 = masks_for(g, bal4, R)
print("   per partition: avg free rects %.3f, avg internal %.3f (bound 2|R|/g = %.1f free)" %
      (free4/len(bal4), inte4/len(bal4), 2*nR/g))
rng = random.Random(1)
vals = []
full = (1 << nR) - 1
for _ in range(300):
    iota = rng.getrandbits(nR)
    vals.append(cost_min(iota, nR, rows4, cols4, oth4)[0])
# also the structured adversary: s_r on rectangles with i+j even-ish patterns, plus local search
cur = rng.getrandbits(nR); curv = cost_min(cur, nR, rows4, cols4, oth4)[0]
for it in range(3000):
    cand = cur ^ (1 << rng.randrange(nR))
    v = cost_min(cand, nR, rows4, cols4, oth4)[0]
    if v >= curv: cur, curv = cand, v
print("   random iota: min over partitions of agreements: mean %.2f, max %d (of |R|=%d, |R|/2=%d)" %
      (sum(vals)/len(vals), max(vals), nR, nR//2))
print("   local-search adversary: V >= %d/%d = %.4f (two groupings give %d/%d = 0.5)" %
      (curv, nR, curv/nR, nR//2, nR))
check("g=4: adversary keeps every balanced grouping at >= 0.4 |R|", curv >= 0.4*nR)
print("ALL PASS" if ok else "SOME FAIL")
