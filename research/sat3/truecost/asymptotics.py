#!/usr/bin/env python3
"""Refined count against the certificate of Prop. B.2(b), exact integers.
   refined(k) = sum_{m<=k} (k-m+1) p(m)   (= true rank of Psi_2k across ad|bc in the stable range, n1 = n2 >= 2)
   cert(k)    = (2k+1) sum_{m<=k} p(m)
and the entropy bookkeeping for classes of size n = c sqrt(e/2) at the middle term (p = q).
"""
import math, numpy as np
from entropy import s, k0, cs
K = 200000
p = [0] * (K + 1); p[0] = 1
# pentagonal recurrence
for n in range(1, K + 1):
    t = 0; j = 1
    while True:
        g1 = j * (3 * j - 1) // 2; g2 = j * (3 * j + 1) // 2
        if g1 > n: break
        sg = 1 if j % 2 else -1
        t += sg * p[n - g1]
        if g2 <= n: t += sg * p[n - g2]
        j += 1
    p[n] = t
cum = 0; cum2 = 0
print("     k   ln refined   ln cert    ratio   ln p(k)/ln cert")
marks = {10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000, 200000}
for k in range(K + 1):
    cum += p[k]            # sum_{m<=k} p(m)
    cum2 += cum            # sum_{m<=k} (k-m+1) p(m)
    if k in marks:
        lr = math.log(cum2); lc = math.log((2 * k + 1) * cum)
        print(f"{k:6d}  {lr:10.3f} {lc:10.3f}  {lr/lc:.4f}   {math.log(p[k])/lc:.4f}")
print()
print("middle term, p = q, classes of size n = c sqrt(e/2):  exponent of #{T at level e, |T| <= 2n} / exponent of d1 d2")
print("   c      s(c)/kappa0   ratio rho(c) = sbar(sqrt2 c) / (sqrt2 s(c))      (1/sqrt2 = 0.70711)")
for c in [0.05, 0.1, 0.2, 0.3, cs / math.sqrt(2), 0.45, 0.5, cs, 0.6, 0.65, 0.7]:
    sb = s(min(math.sqrt(2) * c, cs))
    print(f"  {c:.4f}   {s(c)/k0:.4f}       {sb/(math.sqrt(2)*s(c)):.5f}")
