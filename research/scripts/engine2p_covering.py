#!/usr/bin/env python3
"""engine2p_covering.py -- the covering bound for arbitrary grouping families (mechanism 7 in
research/engine2-probabilistic.md).

Model (one level of Theorem A on a g x g grid, per-rectangle pieces).  A rectangle q = (i<i', j<j')
has corner nodes (i,j),(i,j'),(i',j),(i',j').  A grouping pi (partition of the g^2 nodes into
blocks) induces a TYPE on q (repaired classification, 5 Nov 2026):
   'diag' : a diagonal pair, (i,j)~(i',j') or (i,j')~(i',j), lies in one block.  This covers
            the old 'free' and 'int' types and every 3+1 or 2+1+1 split with a diagonal pair in
            one block; the cost is bounded below only by 0.  Each pair of nodes in one block in
            distinct rows and columns is a diagonal of exactly one rectangle, so
            #diag <= sum_B C(|B|,2) <= g^2(g-1)/2 = 2|R|/(g-1).
   'row'  : not diag, and (i,j)~(i,j') or (i',j)~(i',j')   (the row cut is a union of blocks)
   'col'  : not diag, and (i,j)~(i',j) or (i,j')~(i',j')   (the column cut is a union of blocks)
   'four' : the four corners lie in four distinct blocks    (every cut is a union of blocks)
   (A non-diag rectangle cannot be both 'row' and 'col': x~y and x~u would give y~u, etc.)
The first version of this script typed every rectangle meeting >= 3 blocks as 'other' and charged
it both costs; that is right only for 'four'.  With three blocks only one of the row and column cuts
is a union of blocks, and a 3+1 split (two blocks) was typed 'other' too.
Adversary pieces: s_r (row rank 2^{2 lam}, col rank ~1), s_c (col rank 2^{2 lam}, row rank ~1).
One-ended cost of rectangle q in term iota under grouping pi (in units of 2 lam):
   s_r : 1 on 'row' and 'four', 0 on 'col' and 'diag'
   s_c : 1 on 'col' and 'four', 0 on 'row' and 'diag'.
(Full bits of a rectangle = 2 in these units, so cost/|R| ... ratio rho_eff = cost/(2|R|)... we
report agree = cost in units of 2lam and the ratio agree/|R| = rho_eff.)
Level value V = max_iota min_pi cost(iota, pi) / |R|  (= rho_eff of the level, for these pieces).
Two groupings (rows, cols): V = ceil(|R|/2)/|R| -> 1/2.
Claim (covering bound): for ANY family of groupings into blocks of size <= s, with s = o(g^2)...
   V >= 1/2 - 1/(g-1) - sqrt(ln(2M)/(2|R|)),  M = #groupings.

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
    if x == v or y == u: return 'diag'
    if x == y or u == v: return 'row'
    if x == u or y == v: return 'col'
    return 'four'

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
    global MAXDIAG
    MAXDIAG = 0
    rows, cols, oth, free, inte = [], [], [], 0, 0
    for block in parts:
        rm = cm = om = 0
        nd = 0
        for k, q in enumerate(R):
            t = rect_type(block, q)
            if t == 'row': rm |= 1 << k
            elif t == 'col': cm |= 1 << k
            elif t == 'four': om |= 1 << k
            else:
                free += 1; nd += 1
                if block[q[0]] == block[q[1]] == block[q[2]] == block[q[3]]: inte += 1
        rows.append(rm); cols.append(cm); oth.append(om)
        MAXDIAG = max(MAXDIAG, nd)
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
maxdiag3 = MAXDIAG
print("g=3: %d rectangles, %d partitions with blocks <= 3; diag rects total %d, internal %d"
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
print("   max diag rectangles in one partition: %d (bound 2|R|/(g-1) = %d)" % (maxdiag3, 2*nR//(g-1)))
check("g=3: diag count per partition <= 2|R|/(g-1)", maxdiag3 <= 2*nR/(g-1))
check("g=3: V >= (1/2 - 1/(g-1))|R| = 0 (bound vacuous at g = 3; reported for the record)", best >= 0)

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
print("   max diag rectangles in one partition: %d (bound 2|R|/(g-1) = %d)" % (MAXDIAG, 2*nR//(g-1)))
check("g=4: diag count per partition <= 2|R|/(g-1)", MAXDIAG <= 2*nR/(g-1))
print("   per partition: avg diag rects %.3f, avg internal %.3f (bound 2|R|/(g-1) = %.1f diag)" %
      (free4/len(bal4), inte4/len(bal4), 2*nR/(g-1)))
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
# The proved bound (diag rectangles charged 0) is (1/2 - 1/(g-1))|R| - O(sqrt(|R| log M)); at g = 4 the
# main term is 6 of 36.  (The first version, which charged every rectangle meeting >= 3 blocks both
# costs, reported 18/36 here; that value rested on the flawed charge.)
check("g=4: adversary keeps every balanced grouping at >= (1/2 - 1/(g-1))|R| = 6", curv >= (0.5 - 1/(g-1))*nR)
print("ALL PASS" if ok else "SOME FAIL")
