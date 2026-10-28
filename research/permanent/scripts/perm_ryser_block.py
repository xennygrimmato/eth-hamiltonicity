#!/usr/bin/env python3
"""Ryser network with row->block labels (exact integers).

per(A) = sum_{x in {0,1}^n} (-1)^{n-|x|} prod_i (A x)_i.   Columns are split into blocks C_b of size q,
rows into groups R_a of size p.  Expanding prod_i sum_b s_ib(x_b), s_ib = sum_{j in C_b} A_ij x_j,
every row chooses a block.  Network:

  * column node b: private x_b (q bits); shared with row node a the set L_ab = {i in R_a : row i
    chose block b} (p bits);  W_b = (-1)^{|C_b|-|x_b|} prod_{i in U_a L_ab} s_ib(x_b), summed over x_b.
  * row node a: W_a = [the L_ab, b = 1..h_c, partition R_a].

Bits: c_ab = p  ->  U = 2 (n/p)(n/q) p = 2 n^2 / q, and every column node sees
sum_a c_ab = (n/p) p = n label bits (the "broadcast law": some node must see all n Ryser bits).
Restricting to patterns (|L_ab| = N_ab) gives c_ab = log2 C(p, N_ab) and U -> 2 n log2(n/q),
i.e. the Laplace count again.

The script checks the identity on random dense 0/1 matrices, n <= 7, and prints U, P.
"""
import itertools, math, random, sys
from math import log2

def permanent(A):
    n = len(A); tot = 0
    for p in itertools.permutations(range(n)):
        t = 1
        for i in range(n):
            t *= A[i][p[i]]
            if not t: break
        tot += t
    return tot

def network_value(A, R, C):
    n = len(A); hr, hc = len(R), len(C)
    # labels: for each (a,b) a subset L_ab of R[a]
    keys = [(a, b) for a in range(hr) for b in range(hc)]
    alph = {k: [frozenset(s) for r in range(len(R[k[0]]) + 1) for s in itertools.combinations(R[k[0]], r)] for k in keys}
    # column node tables, summed over private x_b: Wt_b[(L_0b,...,L_{hr-1,b})]
    def coltable(b):
        tab = {}
        q = len(C[b])
        for Ls in itertools.product(*[alph[(a, b)] for a in range(hr)]):
            rows = sorted(frozenset().union(*Ls))
            val = 0
            for xb in itertools.product((0, 1), repeat=q):
                w = (-1) ** (q - sum(xb))
                for i in rows:
                    w *= sum(A[i][j] * xb[t] for t, j in enumerate(C[b]))
                    if not w: break
                val += w
            tab[Ls] = val
        return tab
    ctab = [coltable(b) for b in range(hc)]
    total = 0
    for choice in itertools.product(*[alph[k] for k in keys]):
        L = dict(zip(keys, choice))
        w = 1
        for a in range(hr):  # row nodes: partition of R_a
            parts = [L[(a, b)] for b in range(hc)]
            if sum(len(x) for x in parts) != len(R[a]) or frozenset().union(*parts) != frozenset(R[a]):
                w = 0; break
        if not w: continue
        for b in range(hc):
            w *= ctab[b][tuple(L[(a, b)] for a in range(hr))]
            if not w: break
        total += w
    return total

def main():
    rng = random.Random(7)
    ok = True
    for n, hr, hc in [(4, 2, 2), (5, 2, 2), (6, 2, 3), (6, 3, 2), (7, 2, 2)]:
        A = [[1 if rng.random() < 0.8 else 0 for _ in range(n)] for _ in range(n)]
        R = [list(range(a * n // hr, (a + 1) * n // hr)) for a in range(hr)]
        C = [list(range(b * n // hc, (b + 1) * n // hc)) for b in range(hc)]
        v = network_value(A, R, C); p = permanent(A)
        good = v == p; ok &= good
        U = 2 * sum(len(R[a]) for a in range(hr) for b in range(hc))
        Pcol = max(len(C[b]) + sum(len(R[a]) for a in range(hr)) for b in range(hc))
        Prow = max(sum(len(R[a]) for b in range(hc)) for a in range(hr))
        print(f"n={n} h_r={hr} h_c={hc}: per={p} network={v} {'ok' if good else 'MISMATCH'}; U={U} (=2 n h_c), "
              f"P_col={Pcol} (= q + n: broadcast), P_row={Prow}")
    print("asymptotics: U = 2 n^2 / q ; the column node sees q + n bits for every p, q  ->  U * P >= n^2.")
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
