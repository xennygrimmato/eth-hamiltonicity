"""H-configurations in T_4 x R^M: A,B = tips (arm h/2) over the spine point 0, C,D' = tips (arm h/2) over m e_1.
Within-pair distance h, all four cross distances L = sqrt(h^2 + m^2).  Bound (4.1) with
K = segment [lo, hi] e_1  +  ball of Gaussian radius r (orthogonal directions, M -> infinity):
   delta_4 <= sqrt(2 pi) E[ S + 2 (a g - S)_+ + 2 (a g + m g1 - S)_+ ],  S = max(hi g1, lo g1) + r,  a = h/2.
The decoder inequality (K-MM 8.2) with the tripod inequality needs delta_4 >= L + h/2 - o(h) for h/L -> 0."""
import math, numpy as np
from scipy import optimize, integrate, stats
SQ = math.sqrt(2 * math.pi); phi = stats.norm.pdf; Phi = stats.norm.cdf
def Epos(a, s):                       # E (a g - s)_+ , vectorised in s
    t = s / a
    return a * (phi(t) - t * (1 - Phi(t)))
x = np.linspace(-9, 9, 36001); w = phi(x) * (x[1] - x[0])      # trapezoid rule for E over g1
def bound(h, m, lo, hi, r):
    a = h / 2
    S = np.maximum(hi * x, lo * x) + r
    return SQ * float(np.sum(w * (S + 2 * Epos(a, S) + 2 * Epos(a, S - m * x))))
for h, m in [(0.2, 1.0), (0.1, 1.0), (0.05, 1.0), (0.02, 1.0)]:
    L = math.hypot(h, m)
    f = lambda p: bound(h, m, p[0], p[1], abs(p[2]))
    best = min((optimize.minimize(f, x0, method="Nelder-Mead", options={"xatol": 1e-9, "fatol": 1e-12, "maxiter": 4000})
                for x0 in ([0.0, m, 0.0], [-0.1, m + 0.1, 0.05], [0.05, m - 0.05, 0.02])), key=lambda z: z.fun)
    print(f"h={h:5.2f} L={L:.5f}: K=[0,m]: {bound(h, m, 0, m, 0):.6f}   optimised: {best.fun:.6f} at lo,hi,r = "
          f"{best.x[0]:+.4f},{best.x[1]:.4f},{abs(best.x[2]):.4f}   slope (delta4 - L)/h = {(best.fun - L)/h:.4f}   (threshold 0.5; flat and tree: 1)")
