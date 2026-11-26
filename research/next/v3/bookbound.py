"""Upper bound on the shared-label rate of the three tips of a book whose spine is R^k, and the resulting bound on omega.

Tips at distance 1 from the spine, on three pages that are pairwise flat.  With S a finite set on the spine,
  delta(tips) <= delta({p,q} u S) + delta({q,r} u S) - delta({q} u S)             (monotone + submodular)
             =  sqrt(2 pi) E[ 2 max(|g0|, M) - max(g0, M) ],   M = max_{s in S} <g', s>   (flat law = mean width)
For S a sphere of radius rho in R^k, M = rho |g'| with |g'| chi_k distributed.  k -> infinity: M -> constant m.
Any spectral point has perimeter <= omega * delta(tips), perimeter = 6.
"""
import math, numpy as np
from scipy import integrate, optimize, stats

def F(m):                      # E[ 2 max(|g|, m) - max(g, m) ] * sqrt(2 pi), g standard normal, m >= 0
    phi, Phi = stats.norm.pdf(m), stats.norm.cdf(m)
    tail = phi - m*(1 - Phi)   # E (g - m)_+
    return math.sqrt(2*math.pi)*(m + 3*tail)

def U(k, rho):
    if k == 0: return F(0.0)
    f = lambda x: F(rho*x)*stats.chi.pdf(x, k)
    return integrate.quad(f, 0, np.inf, limit=200)[0]

if __name__ == "__main__":
    print("%4s %10s %10s %10s" % ("k", "rho*", "U_k", "omega >="))
    for k in (0, 1, 2, 3, 5, 10, 30, 100):
        if k == 0: print("%4d %10s %10.5f %10.5f" % (0, "-", F(0), 6/F(0))); continue
        res = optimize.minimize_scalar(lambda r: U(k, r), bounds=(1e-4, 2), method="bounded")
        print("%4d %10.5f %10.5f %10.5f" % (k, res.x, res.fun, 6/res.fun))
    z = stats.norm.ppf(2/3)
    print(" inf   m = %.6f %10.5f %10.5f   (= 2 exp(z^2/2), z = Phi^{-1}(2/3))" % (z, F(z), 2*math.exp(z*z/2)))
    print("two-point spine set {+-t} (k = 1): 3 sqrt(1+t^2) - t, minimum 2 sqrt 2 = %.5f at t = 1/sqrt 8; omega >= 3/sqrt 2 = %.5f" % (2*math.sqrt(2), 3/math.sqrt(2)))
    print("thresholds: 6/U < 9/4 needs U > %.5f;  OpenAI's extremal tripod has delta = 8/3 = %.5f" % (6/2.25, 8/3))
