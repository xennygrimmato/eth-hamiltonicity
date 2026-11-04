"""engine2 M5: best contraction-tree exponent for the (K,lam)-clique as a function of omega.
A merge of node sets S1,S2 (sizes s1,s2; r = K-s1-s2 outside) is the matrix product
(D^{s1 r} x D^{s1 s2})(D^{s1 s2} x D^{s2 r}), cost D^{omega(s1 r, s1 s2, s2 r)}.  Bounds used, exact in Fractions:
  UB: omega(a,b,c) <= a+b+c-(3-omega)min(a,b,c)    (square blocking)
  LB: omega(a,b,c) >= max(a+b,b+c,a+c, omega(a+b+c)/3)   (input/output size; symmetrisation  <a,b,c>(x)<b,c,a>(x)<c,a,b>)
Leaves cost K-1 (reading a table).  Only sizes matter (K_K is symmetric).  e = f(K)/K^2."""
from fractions import Fraction as Fr
import sys

def ub(a, b, c, w): return a + b + c - (3 - w) * min(a, b, c)
def lb(a, b, c, w): return max(a + b, b + c, a + c, w * (a + b + c) / 3)

# rectangular bound (current constants, ADVWXXZ 2024): omega=2.371339, alpha=0.321334, omega(1,1,2)=3.250035;
# omega(1,1,k) convex in k (Lotti-Romani) -> piecewise-linear upper bound; omega(a,b,c) <= |a-b| + min(a,b)*omega(1,1,c/min(a,b)).
W0, ALPHA, W2 = 2.371339, 0.321334, 3.250035
def w11(k):
    if k <= ALPHA: return 2.0
    if k <= 1: return 2 + (W0 - 2) * (k - ALPHA) / (1 - ALPHA)
    if k <= 2: return W0 + (W2 - W0) * (k - 1)
    return W2 + (k - 2)
def ub_rect(a, b, c, w=None):
    best = a + b + c
    for (p, q, r) in [(a, b, c), (b, c, a), (a, c, b)]:
        m = min(p, q)
        if m == 0: best = min(best, max(p, q) + r if r else max(p, q)); continue
        best = min(best, abs(p - q) + m * w11(r / m))
    return max(best, a + b, b + c, a + c)

def best_tree(K, w, bound):
    f = [None] * (K + 1); arg = [None] * (K + 1)
    f[1] = K - 1
    for s in range(2, K + 1):
        r = K - s; best = None
        for s1 in range(1, s // 2 + 1):
            s2 = s - s1
            c = bound(s1 * r, s1 * s2, s2 * r, w)
            v = max(f[s1], f[s2], c)
            if best is None or v < best: best, arg[s] = v, s1
        f[s] = best
    return f[K] / K ** 2, arg

def shape(arg, K):
    # list the split sizes along the root path
    out = []; s = K
    while s > 1 and len(out) < 6:
        s1 = arg[s]; out.append((s1, s - s1)); s = max(s1, s - s1)
    return out

print("omega   K    e_tree_UB   e_tree_LB    1/4+1/(2K)   omega/9   root-path splits (UB tree)")
ok = True
for w in [Fr(2), Fr(21, 10), Fr(22, 10), Fr(9, 4), Fr(23, 10), Fr(2371339, 1000000), Fr(25, 10), Fr(3)]:
    for K in [30, 90, 240]:
        eu, argu = best_tree(K, w, ub); el, _ = best_tree(K, w, lb)
        print(f"{float(w):.4f} {K:4d}  {float(eu):.5f}    {float(el):.5f}     {1/4+1/(2*K):.5f}    {float(w)/9:.5f}   {shape(argu, K)}")
        ok &= el <= eu
        ok &= el >= Fr(2, 9) - Fr(1, K)
print("\ncurrent rectangular-MM constants (omega=2.371339, alpha=0.321334, omega(1,1,2)=3.250035):")
for K in [30, 90, 240]:
    er, argr = best_tree(K, None, ub_rect)
    print(f"  K={K}: e_tree_rect_UB = {er:.5f}   (1/4 + 1/(2K) = {1/4+1/(2*K):.5f}, omega/9 = {W0/9:.5f})")
print(f"[{'PASS' if ok else 'FAIL'}] LB-tree <= UB-tree and LB-tree >= 2/9 - 1/K for all rows")
