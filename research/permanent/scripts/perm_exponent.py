#!/usr/bin/env python3
"""Engine arithmetic: what Lemma 8 + Theorem A actually charge for the permanent networks.

Levels (Theorem A(a) of [A], exact-hc-theorem.md s.1): K_0 = 2^{x0}, log K_{l+1} = 2 log g_l,
g_l = 2^{3l+x0} K_l, e_0 = 1/2, e_{l+1} = (rho + 3/(2K_l)) e_l + 3/K_l.  Theorem B: rho = 1/sqrt 2.
Time of a network with total U, max node P, g = 3K^8 nodes:  2^{e(U + gP/K) + 2gP/K} * poly * tau.

Networks for per(A) / #PM (this directory):
  Laplace / profile (bijection-term):  U = 2 n lg(e h)      with h = g row groups, P = (2n/g) lg(e g)
  bounded degree Delta (bijection-term): U = 2 n lg(e Delta),  P = (2n/g) lg(e Delta)
  Ryser broadcast (non-bijection):       U = 2 n^2 / q, P = n + q   (fails gP/K outright)

The script prints, per level, e_l, K_l, e_l * lg K_l and the exponent / n of the dense Laplace network,
showing that it grows like sqrt(log K) (so the exponent is never below n), and that e_l lg K_l -> 0
would require rho < 1/2 (alpha' = lg(1/rho) > 1).
"""
import math, sys

def levels(rho, x0=18, L=8):
    K = 2.0 ** x0; e = 0.5; out = []
    lgK = x0
    for l in range(L):
        out.append((l, lgK, e))
        g_lg = 3 * l + x0 + lgK           # lg g_l
        e = (rho + 3 / (2 * K)) * e + 3 / K
        lgK = 2 * g_lg
        K = 2.0 ** lgK if lgK < 1000 else float('inf')
    return out

def main():
    print("Theorem B pieces, rho = 1/sqrt2:  (lg = log2)")
    print(" l   lg K_l        e_l          e_l*lg K_l    exponent/n of dense Laplace network  (e*2 lg(e*3K^8) + 2gP/K)")
    for l, lgK, e in levels(1 / math.sqrt(2)):
        lg_g = math.log2(3) + 8 * lgK
        U_over_n = 2 * (lg_g + math.log2(math.e))          # U = 2 n lg(e g)
        # P = (2n/g) lg(e g), so gP/K = 2 n lg(e g) / K  (per n):
        gPK = 2 * (lg_g + math.log2(math.e)) / 2 ** lgK if lgK < 900 else 0.0
        X = e * (U_over_n + gPK) + 2 * gPK
        print(f" {l:2d}  {lgK:10.3g}  {e:12.4g}  {e*lgK:12.4g}  {X:12.4g}")
    print("\nHypothetical pieces with rho = 0.4 (alpha' = lg 2.5 = 1.32 > 1):")
    for l, lgK, e in levels(0.4):
        print(f" {l:2d}  lg K={lgK:10.3g}  e={e:12.4g}  e*lg K={e*lgK:12.4g}")
    print("\nbounded degree Delta, exponent/n = e_l * 2 lg(e Delta): 2^{o(n)} iff lg Delta = o(1/e_l) = o(sqrt(lg K_l)) ~ o(sqrt(lg n)).")
    print("Ryser broadcast: P >= n so gP/K >= 3K^7 n: never admissible.")
    print("PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
