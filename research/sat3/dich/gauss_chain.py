"""Upper bounds on common-label rates of pod tips in  T_k x R^M  (inside the filtration space C_{M+1}),
from the flat law + submodularity chain (dichotomy-attack.md, Theorem L), against the tripod bound D*.

Chain value for tips at radii a_i over the spine point 0 and a convex body K in the spine R^M with support
function S = s_K(G) (G standard Gaussian in R^M, g an independent standard Gaussian):
      U = sqrt(2 pi) * E[ S + sum_i (a_i g - S)_+ ].
K = ball of radius R in R^M: S = R |G|.  M -> infinity with R sqrt(M) = r fixed: S = r (deterministic).
"""
import math
from scipy import integrate, optimize, stats
SQ = math.sqrt(2 * math.pi)
phi = stats.norm.pdf; Phi = stats.norm.cdf

def Epos(a, s):
    """E (a g - s)_+ for a > 0, s real"""
    t = s / a
    return a * (phi(t) - t * (1 - Phi(t)))

def U_const(arms, r):
    return SQ * (r + sum(Epos(a, r) for a in arms))

def U_inf(arms):
    res = optimize.minimize_scalar(lambda r: U_const(arms, r), bounds=(0, 5 * max(arms)), method="bounded",
                                   options={"xatol": 1e-12})
    return res.fun, res.x

def U_ball(arms, M, R):
    """K = ball of radius R in R^M:  S = R * chi_M"""
    chi = stats.chi(M)
    f = lambda x: (R * x + sum(Epos(a, R * x) for a in arms)) * chi.pdf(x)
    v, _ = integrate.quad(f, 0, 12 + 3 * math.sqrt(M), limit=400)
    return SQ * v

def U_M(arms, M):
    res = optimize.minimize_scalar(lambda R: U_ball(arms, M, R), bounds=(0, 5 * max(arms)), method="bounded",
                                   options={"xatol": 1e-10})
    return res.fun, res.x

def dstar(arms):
    if min(arms) <= 0: return sum(arms)
    return sum(arms) - 1 / sum(1 / a for a in arms)

if __name__ == "__main__":
    print("k tips, arms 1: c_k(M=1) = 2 sqrt(k-1); c_k(inf) = k exp(-t_k^2/2), P(g>t_k) = 1/k; lower bounds")
    print(" k  M=1      M=2      M=3      M=8      M=64     M=inf    closed   | 4(k-1)/k (K_k rank = k^2/4)  Steiner")
    for k in range(2, 9):
        arms = [1.0] * k
        t = stats.norm.isf(1 / k)
        row = [U_M(arms, M)[0] for M in (1, 2, 3, 8, 64)]
        print(f"{k:2d}  " + "  ".join(f"{v:.5f}" for v in row) + f"  {U_inf(arms)[0]:.5f}  {k*math.exp(-t*t/2):.5f}  | {4*(k-1)/k:.5f}   {k}")
    u3 = U_inf([1, 1, 1])[0]
    print(f"\nthree tips: U = {u3:.6f} a,  D* = {8/3:.6f} a,  hub = 3a;  D/hp in [{8/9:.5f}, {u3/3:.5f}]")
    print(f"consequence: not contracting => omega >= 6/U = {6/u3:.5f}   (M=1: {6/(2*math.sqrt(2)):.5f})")
    print("\nscan of arm ratios (a1,a2,a3), sum = 3: min over the simplex of U_inf - D*  and of U_inf / D*")
    best = (9, None); bestr = (9, None)
    n = 60
    for i in range(1, n):
        for j in range(i, n):
            l = 3 * n / n  # dummy
            a1 = 3 * i / (3 * n); a2 = 3 * j / (3 * n)
            a1 = i / n * 3; a2 = j / n * 3; a3 = 3 - a1 - a2
            if a3 < a2 or a3 <= 0: continue
            u = U_inf([a1, a2, a3])[0]; d = dstar([a1, a2, a3])
            if u - d < best[0]: best = (u - d, (a1, a2, a3))
            if u / d < bestr[0]: bestr = (u / d, (a1, a2, a3))
    print("  min (U - D*) =", best, "\n  min U/D* =", bestr)
    print("\nlong arm: arms (1,1,b):  U - b  ->", [round(U_inf([1, 1, b])[0] - b, 5) for b in (10, 100, 1000)],
          "  D* - b ->", [round(dstar([1, 1, b]) - b, 5) for b in (10, 100, 1000)])
    print("degenerate arm: arms (1,1,eps):", [(e, round(U_inf([1, 1, e])[0], 5), round(dstar([1, 1, e]), 5)) for e in (0.5, 0.1, 0.01)])
