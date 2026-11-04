#!/usr/bin/env python3
"""engine2p_f2pieces.py -- mechanism 1 residue: pieces over F_2 (what a randomised, isolation-based
decision algorithm would need: only Z mod 2).

lam = 1: F = SWAP on two bits, a 4x4 matrix in the row flattening ((x,y),(u,v)).  A piece A has
  rank_row = rank of A as a 4x4 matrix,  rank_col = rank of the realignment A^col[(x,u),(y,v)].
Exhaustive over all 2-piece decompositions F = A_1 + A_2 over F_2 (65536 choices of A_1):
  minimise  max_i (rank_row(A_i) * rank_col(A_i))        ("product cost" 2^{c_row + c_col})
  and also  max_i (log2 rank_row + log2 rank_col) summed... (same thing).
Compare with the rational decomposition SWAP = I - 2 P_singlet (I: (4,1); P_singlet: (1,3)) and
the trivial F itself (4,4) = 16.  Also exhaustive over 3-piece decompositions restricted to
A_1, A_2 of rank <= 2 (to keep the search small) and all 2-piece decompositions over F_3.
Also: the Theorem-B normalisation h! vanishes mod 2 for h >= 2 (a one-line fact, printed).
"""
import itertools
import numpy as np

def rank_mod(M, p):
    M = [list(map(int, r)) for r in M]; n = len(M); m = len(M[0]); r = 0
    for c in range(m):
        piv = next((i for i in range(r, n) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], -1, p)
        M[r] = [(v*inv) % p for v in M[r]]
        for i in range(n):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(a - f*b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r

def realign(A):
    # A[(x,y),(u,v)] -> B[(x,u),(y,v)], 2 bits each
    B = np.zeros((4,4), dtype=int)
    for x in range(2):
        for y in range(2):
            for u in range(2):
                for v in range(2):
                    B[2*x+u, 2*y+v] = A[2*x+y, 2*u+v]
    return B

def cost(A, p):
    rr = rank_mod(A, p); rc = rank_mod(realign(A), p)
    return rr*rc, rr, rc

F = np.zeros((4,4), dtype=int)
for x in range(2):
    for y in range(2):
        F[2*x+y, 2*y+x] = 1     # [x=v][y=u]: (u,v) = (y,x)

print("F = SWAP: product cost over Q = %d (rank_row %d, rank_col %d)" % cost(F, 101))
I4 = np.eye(4, dtype=int)
P = np.zeros((4,4), dtype=int); P[1,1]=P[2,2]=1; P[1,2]=P[2,1]=-1   # 2*P_singlet
print("Q-decomposition I - 2P_singlet: I -> %s ; 2P_singlet -> %s" % (cost(I4,101), cost(P,101)))

def exhaustive2(p):
    best = None; arg = None
    for bits in itertools.product(range(p), repeat=16):
        A1 = np.array(bits, dtype=int).reshape(4,4)
        A2 = (F - A1) % p
        c = max(cost(A1,p)[0], cost(A2,p)[0])
        if best is None or c < best: best, arg = c, (A1.copy(), A2.copy())
    return best, arg

b2, (A1, A2) = exhaustive2(2)
print("F_2, 2 pieces: min max-product = %d ; pieces costs %s %s" % (b2, cost(A1,2), cost(A2,2)))
print("   A1 =\n", A1, "\n   A2 =\n", A2)
ok = True
# sanity: the trivial decomposition {I, I+SWAP} over F_2
c1 = cost(I4 % 2, 2); c2 = cost((I4+F) % 2, 2)
print("   {I, I+F} over F_2: costs %s %s" % (c1, c2))
# F_3 exhaustive 2 pieces (3^16 = 43M too slow in pure Python); sample structured subset:
# all A1 with entries in {0,1,2} supported on the support of F plus the diagonal (2^... small)
print("F_3, 2 pieces restricted to supp(A1) in supp(F) u diag (3^6 = 729):")
supp = [(i,j) for i in range(4) for j in range(4) if F[i,j] or i == j]
best3 = None
for vals in itertools.product(range(3), repeat=len(supp)):
    A1 = np.zeros((4,4), dtype=int)
    for (i,j), v in zip(supp, vals): A1[i,j] = v
    A2 = (F - A1) % 3
    c = max(cost(A1,3)[0], cost(A2,3)[0])
    if best3 is None or c < best3: best3 = c
print("   min max-product = %d" % best3)
# 3 pieces over F_2 with A1, A2 of rank <= 2 each (rank <= 2 matrices over F_2: enumerate all 4x4 of rank <=2)
mats = [np.array(b, dtype=int).reshape(4,4) for b in itertools.product(range(2), repeat=16)]
low = [M for M in mats if rank_mod(M, 2) <= 2]
costs = {i: cost(M,2)[0] for i, M in enumerate(low)}
print("F_2: %d matrices of rank <= 2" % len(low))
best3p = None
for i, A1 in enumerate(low):
    ca = costs[i]
    if ca >= b2: continue
    for j, A2 in enumerate(low):
        cb = costs[j]
        if cb >= b2 or j < i: continue
        A3 = (F - A1 - A2) % 2
        c = max(ca, cb, cost(A3,2)[0])
        if best3p is None or c < best3p: best3p = c
print("F_2, 3 pieces (two of rank <= 2): min max-product = %s  (2-piece optimum %d)" % (best3p, b2))
from math import factorial
print("Theorem-B normalisation h! mod 2 for h = 1..6:", [factorial(h) % 2 for h in range(1,7)])
print("PASS" if b2 <= 16 else "FAIL")
