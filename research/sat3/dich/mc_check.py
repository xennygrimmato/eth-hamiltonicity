"""Independent Monte-Carlo check of the chain value in T_3 x R^M (M = 3, 6): mean widths of explicit finite point
sets in the flats R^(M+1), W = sqrt(2 pi) E max <G, z>, against the closed form of gauss_chain.py."""
import math, numpy as np
from gauss_chain import U_ball, U_M
rng = np.random.default_rng(5)
SQ = math.sqrt(2 * math.pi)
for M in (3, 6):
    val, R = U_M([1, 1, 1], M)
    K = rng.standard_normal((4000, M)); K = R * K / np.linalg.norm(K, axis=1, keepdims=True)   # points of the sphere
    n = 400000
    G = rng.standard_normal((n, M)); g = rng.standard_normal(n)
    S = np.zeros(n)
    for i in range(0, len(K), 200): S = np.maximum(S, (G @ K[i:i+200].T).max(axis=1))
    # flat F_1j: tip p1 = (+1, 0), tip pj = (-1, 0), K in {0} x R^M
    W_K1j = SQ * np.maximum(S, np.abs(g)).mean()        # W(K u p1 u pj)
    W_K1 = SQ * np.maximum(S, g).mean()                 # W(K u p1)
    chain = 2 * W_K1j - W_K1
    print(f"M={M}: R*={R:.4f}  MC chain value = {chain:.4f}   closed form (ball) = {val:.4f}   [finite K of 4000 points: slightly larger]")
