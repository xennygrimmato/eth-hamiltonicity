#!/usr/bin/env python3
"""Exact-arithmetic sanity checks for research/permanent/clique-evaluation.md.

Normalisation: a (K,lam)-clique has K nodes, lam bits per unordered pair, U = K(K-1)lam
(both ends), cost 2^{e_K K^2 lam}.  Brute force over the 2^{K(K-1)lam/2} labellings is
e = (K-1)/(2K) -> 1/2.  Query lower bound e >= (K-1)/K^2.

(1) upper bounds for direct methods, as exact fractions in units of K^2 lam:
    seq   : sequential contraction, max_j [(j+1)(K-j-1)+j]
    mm3   : split into 3 groups (sizes s1,s2,s3), form the three group tensors by sequential
            contraction inside the group, then trace(M1 M2 M3) by FMM: omega * max(s_i s_j)
            (the MM is rectangular when the groups are unequal; we charge omega * largest side,
            an upper bound).  Reported with omega = 2.371339 and omega = 2.
(2) contraction-tree lower bound: min over binary trees of max_{internal node S} |S|(K-|S|),
    computed by DP; compared with 2K^2/9.
(3) Anthropic's schedule (Theorem A(a)): K_0 = 2^{x0}, K_{l+1} = (2^{3l+x0} K_l)^2,
    e_{l+1} = (rho + 3*2^{-l-5}) e_l + 3/K_l, with e_0 = 1/2 (paper) or e_0 = omega/9 (MM base).
    Prints e_l, e_l * lg K_l, and the ratio.
(4) the fixed point of a level recursion e' = rho e + t/4 for pieces with 2^{t lam} terms.
"""
from fractions import Fraction as Fr
from math import log2, sqrt

OMEGA = Fr(2371339, 1000000)

def seq_bound(K):
    return max(Fr((j+1)*(K-j-1) + j, K*K) for j in range(K-1))

def mm3_bound(K, omega):
    best = None
    for s1 in range(1, K-1):
        for s2 in range(1, K-s1):
            s3 = K-s1-s2
            if s3 < 1: continue
            # forming group tensor of size s with open edges to the other K-s nodes
            form = max(Fr((j+1)*(K-j-1) + j, K*K) for s in (s1,s2,s3) for j in range(s))
            mm = omega * Fr(max(s1*s2, s1*s3, s2*s3), K*K)
            val = max(form, mm)
            if best is None or val < best: best = val
    return best

def tree_lb(K):
    # f(n) = min over binary trees with n leaves of max over internal nodes S of |S|(K-|S|)
    f = {1: 0}
    for n in range(2, K+1):
        f[n] = min(max(n*(K-n) if n < K else 0, f[a], f[n-a]) for a in range(1, n//2+1))
    return Fr(f[K], K*K)

def schedule(rho, e0, x0=18, levels=6):
    K = 2**x0; e = e0; out = []
    for l in range(levels):
        lgK = K.bit_length() - 1
        out.append((l, lgK, e, e*lgK))
        e = (rho + 3*2.0**(-l-5))*e + (3.0/K if K < 2**1000 else 0.0)
        K = (2**(3*l+x0)*K)**2
    return out

if __name__ == "__main__":
    print("(1)+(2) exponents in units of K^2 lam")
    print(" K  query-LB  brute   seq      mm3(w=2.3713) mm3(w=2)  tree-LB  2/9")
    for K in list(range(3, 13)) + [15, 20, 30, 40]:
        q = Fr(K-1, K*K); b = Fr(K-1, 2*K)
        print(f"{K:3d} {float(q):.4f}   {float(b):.4f} {float(seq_bound(K)):.4f}   "
              f"{float(mm3_bound(K, OMEGA)):.4f}        {float(mm3_bound(K, Fr(2))):.4f}   "
              f"{float(tree_lb(K)):.4f}   {2/9:.4f}")
    ok = all(tree_lb(K) >= Fr(2,9) - Fr(1, K) for K in range(3, 60))
    print("tree lower bound >= 2/9 - 1/K for K<60:", "PASS" if ok else "FAIL")
    # exact: min over s of s(K-s) with s in [K/3, 2K/3] is >= 2K^2/9 - O(1)
    print()
    print("(3) Anthropic schedule, rho = 1/sqrt2, x0 = 18")
    rho = 1/sqrt(2)
    A = schedule(rho, 0.5); B = schedule(rho, float(OMEGA)/9)
    print(" l    lgK      e(1/2 base)  e*lgK     e(w/9 base)  e*lgK    ratio")
    for (l, lgK, e, el), (_, _, e2, el2) in zip(A, B):
        print(f"{l:2d} {lgK:9d}  {e:.5f}      {el:8.2f}  {e2:.5f}      {el2:8.2f}  {e2/e:.3f}")
    print("min over levels of e*lgK (1/2 base):", round(min(x[3] for x in A), 2),
          " (w/9 base):", round(min(x[3] for x in B), 2))
    print()
    print("(4) fixed point e* = t/(4(1-rho)) of e' = rho e + t/4 (pieces with 2^{t lam} terms)")
    for t, rho_ in [(0, 1/sqrt(2)), (0, 0.5), (2, 0), (float(OMEGA), 0), (0.5, 0.5), (0.1, 0.5)]:
        print(f"  t={t:.3f} rho={rho_:.3f}  e* = {t/(4*(1-rho_)):.4f}")
