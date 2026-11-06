"""cu_numbers.py -- the arithmetic of Cohn-Umans / CKSU families as piece families on Delta_3 (whole-string view).

Facts used (all [K]): a TPP realisation of <n,n,n> in G has |G| >= n^2 (CU03 Lemma 3.1), sum_rho d_rho^2 = |G|,
hence Sigma(G) := sum_rho d_rho >= max(d_max, |G|/d_max).  A Fourier block B is a row network with bonds D(B) = sum_{B} d_rho.
With T blocks, max_B D(B) >= Sigma(G)/T.
 (P) product route: one TPP <N,N,N> per triangle; a block of Irr(G)^3 costs c_row = c_col <= 3 log2 D(B); the trade needs
     D(B) < N^3 for every block, rho<1/2 needs D(B) < N^{3/2}; and sum_B D(B) = Sigma(G)^3.
 (R) single-group route: TPP <N^3,N^3,N^3> under rows; |G| >= N^6; heaviest block D >= N^3/T: construction row cost >= 9 lambda - 3 log2 T.
Tables: CKSU Sec. 2 groups (Cyc_n^3)^2 x| Cyc_2 (N = 2n(n-1), |G| = 2n^6, degrees <= 2);
        CU03 Thm 3.3 / CKSU Thm 1.7 triangle groups Sym(Delta_n) (N = 1!2!...n!, |G| = (n(n+1)/2)!, degrees by hook lengths);
        S_3 (N = 2)."""
import math, itertools
from fractions import Fraction

def partitions(n, I=1):
    yield (n,)
    for i in range(I, n // 2 + 1):
        for p in partitions(n - i, i):
            yield (i,) + p

def hook_degree(lam):
    lam = sorted(lam, reverse=True); n = sum(lam)
    conj = [sum(1 for r in lam if r > c) for c in range(lam[0])]
    H = 1
    for r, row in enumerate(lam):
        for c in range(row):
            H *= (row - c - 1) + (conj[c] - r - 1) + 1
    return math.factorial(n) // H

def sym_degrees(m):
    return sorted((hook_degree(p) for p in partitions(m)), reverse=True)

def line(name, N, order, degs=None, k=None, dmax=None, Sigma=None):
    if degs is not None:
        k = len(degs); dmax = max(degs); Sigma = sum(degs); assert sum(d * d for d in degs) == order
    lam = math.log2(N)
    print(f"{name:34s} N={N:<6d} lambda={lam:6.2f} |G|={order:<12.3g} k(G)={k:<9d} d_max={dmax:<6d} Sigma={Sigma:<12.3g} "
          f"| per-triangle raw 3lam={3*lam:6.2f}; heaviest-block cost 3log2(Sigma/T): T=2 {3*math.log2(Sigma/2):6.2f}  "
          f"T=16 {3*math.log2(Sigma/16):6.2f}  T=1000 {3*math.log2(Sigma/1000):6.2f}; 3log2 d_max={3*math.log2(dmax):6.2f}; "
          f"Delta_3 product route: sum_B D = Sigma^3 = N^{3*math.log2(Sigma)/lam:.2f}, trade needs every D<N^3, rho<1/2 every D<N^1.5")

print("== per-triangle TPP realisations <N,N,N> (product route (P)); the single-group route (R) uses G^3 or any G with <N^3,N^3,N^3>\n")
line("S_3 (CU03 Sec.3)", 2, 6, degs=[1, 1, 2])
for n in (3, 5, 9, 17):
    N = 2 * n * (n - 1); order = 2 * n ** 6
    k = 2 * n ** 3 + (n ** 6 - n ** 3) // 2; Sigma = 2 * n ** 3 + 2 * (n ** 6 - n ** 3) // 2
    line(f"CKSU Sec.2 (Cyc_{n}^3)^2 x| Cyc_2", N, order, k=k, dmax=2, Sigma=Sigma)
for n in (2, 3, 4, 5):
    m = n * (n + 1) // 2; N = math.prod(math.factorial(i) for i in range(1, n + 1))
    degs = sym_degrees(m)
    line(f"Sym(Delta_{n}) = S_{m} (CKSU Thm 1.7)", N, math.factorial(m), degs=degs)

print("\n== the naming charge of a Fourier type family (fixed-alphabet view, Sec. 1.7 of engine3-open-door.md):")
print("   T = k(G) >= |G|/d_max^2 >= N^6/d_max^2 for a TPP <N^3,N^3,N^3>  =>  1.5 log2 T + 3 log2 d_max >= 9 lambda = raw.")
for name, N, order, dmax in [("S_3^3", 2, 216, 8), ("(Cyc_3^3)^2x|Cyc_2 (<12,12,12> >= <8,8,8>)", 2, 1458, 2), ("S_6 (<12,12,12> >= <8,8,8>)", 2, 720, 16)]:
    k = {216: 27, 1458: 405, 720: 11}[order]
    print(f"   {name:44s}: k(G)={k:4d}, 1.5 log2 k = {1.5*math.log2(k):6.2f}, 3 log2 d_max = {3*math.log2(dmax):5.2f}, sum = {1.5*math.log2(k)+3*math.log2(dmax):6.2f} vs raw 9 (trade needs game value + 1.5 log2 T < 9)")

print("\n== network vs rank for one block <d,d,d>: network 3 log2 d; rank-one terms via nu_3: 1.5 log2 R(<d,d,d>) (R >= d^2, border/asymptotic ~ d^omega)")
for d, R in [(2, 7), (3, 23), (4, 49)]:
    print(f"   d={d}: network {3*math.log2(d):.2f} bits; rank-one with R={R} (known rank / best known): {1.5*math.log2(R):.2f} bits")
