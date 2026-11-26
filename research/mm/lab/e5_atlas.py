"""Derived-exponent atlas under the claimed exact rectangular formula
  w(x,y,z) = x + y + max(0,(x+y)z - xy)^2/(4xyz)   for x>=y>=z>0 (symmetric in its arguments),
versus the 'ideal' omega=2 world  w2(x,y,z) = max of the pairwise sums (= sum of the two largest).
"""
from math import isclose

def w(*a):
    x, y, z = sorted(a, reverse=True)
    if z <= 0:
        return x + y
    t = max(0.0, (x + y) * z - x * y)
    return x + y + t * t / (4 * x * y * z)

def w2(*a):
    x, y, z = sorted(a, reverse=True)
    return x + y

def bisect(f, lo, hi, it=200):
    flo = f(lo)
    for _ in range(it):
        mid = (lo + hi) / 2
        if (f(mid) > 0) == (flo > 0):
            lo, flo = mid, f(mid)
        else:
            hi = mid
    return (lo + hi) / 2

rows = []
W = 2.25
# 1. square / rectangular products
rows.append(("n x n x n product (omega)", w(1, 1, 1), w2(1, 1, 1)))
for k in [0.25, 0.5, 0.6, 0.75, 1.5, 2.0]:
    rows.append((f"<n, n^{k}, n> product", w(1, k, 1), w2(1, k, 1)))
# alpha: largest k with w(1,1,k)=2
alpha = bisect(lambda k: w(1, 1, k) - 2 - 1e-12, 0.3, 0.9)
rows.append(("alpha (dual exponent)", alpha, 1.0))
# 2. Zwick APSP (integer weights, directed, small M): n^{2+mu}, mu solves w(1,mu,1) = 1+2mu
mu = bisect(lambda m: w(1, m, 1) - (1 + 2 * m), 0.01, 0.99)
mu2 = bisect(lambda m: w2(1, m, 1) - (1 + 2 * m), 0.01, 0.99)
rows.append(("Zwick APSP / unweighted directed APSP n^{2+mu}", 2 + mu, 2 + mu2))
# 3. Fully sparse product (ABFK): m_in = m, m_out = m^r, time m^sigma, w(sigma-1, 2-sigma, 1+r-sigma) = sigma
for r in [0.5, 1.0, 1.25, 1.5]:
    f = lambda s, r=r: w(s - 1, 2 - s, 1 + r - s) - s
    f2 = lambda s, r=r: w2(s - 1, 2 - s, 1 + r - s) - s
    try:
        s1 = bisect(f, 1.0001, min(2, 1 + r) - 1e-4)
    except Exception:
        s1 = float('nan')
    s2 = bisect(f2, 1.0001, min(2, 1 + r) - 1e-4)
    rows.append((f"fully sparse product, m_out=m^{r} (ABFK eq.)", s1, s2))
# 4. square-omega-only formulas (not re-optimised with rectangular formula)
rows.append(("triangle detection AYZ m^{2w/(w+1)} [square omega only]", 2 * W / (W + 1), 4 / 3))
rows.append(("k-clique, k=3t: n^{t*omega}  (per t)", W, 2.0))
rows.append(("bounded-difference (min,+) n^{(3+w)/2} [square omega only]", (3 + W) / 2, 2.5))
rows.append(("det / inverse / rank / solve: n^omega", W, 2.0))

print(f"{'quantity':62s} {'omega=9/4':>10s} {'omega=2':>9s}  ideal?")
for name, v, v2 in rows:
    print(f"{name:62s} {v:10.5f} {v2:9.5f}  {'YES' if isclose(v, v2, abs_tol=1e-6) else 'no'}")
