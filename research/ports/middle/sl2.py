#!/usr/bin/env python3
"""Cayley graphs of SL_2(F_{2^k}) with generators e12(1), e21(1), e12(x), e21(x).
Placement g -> g.W0, W0 = U^2, U = polynomials of degree < j (F_2-subspace of F_q).
Checks: (a) edge distances d_J(g s W0, g W0) = d_J(s W0, W0) <= 1,
        (b) mean pair distance d_J(g W0, W0) over g,
        (c) lambda_2 of the Cayley graph and the kernel inequality
            E_edges 2^{-d} <= lam + (1-lam) E_pairs 2^{-d}.
d_J(A,B) = dim A - dim(A cap B) for subspaces of equal dimension."""
import sys, itertools
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla

IRRED = {2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011, 7: 0b10000011}

def make_field(k):
    mod = IRRED[k]; q = 1 << k
    def mul(a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a & q: a ^= mod
        return r
    tab = [[mul(a, b) for b in range(q)] for a in range(q)]
    return q, tab

def rank_f2(rows):
    rows = list(rows); r = 0
    piv = {}
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv: v ^= piv[h]
            else:
                piv[h] = v; r += 1; break
    return r

def main(k):
    q, T = make_field(k)
    j = k // 2
    Ub = [1 << i for i in range(j)]            # basis of U = polys of degree < j
    # basis of W0 = U^2 as vectors (a,b) in F_q^2, encoded a | b<<k
    W0 = [(u, 0) for u in Ub] + [(0, u) for u in Ub]
    enc = lambda v: v[0] | (v[1] << k)
    def act(g, v):
        a, b, c, d = g
        return (T[a][v[0]] ^ T[b][v[1]], T[c][v[0]] ^ T[d][v[1]])
    def dJ(g):
        img = [enc(act(g, w)) for w in W0]
        rk = rank_f2(img + [enc(w) for w in W0])   # dim(gW0 + W0)
        return rk - 2 * j                          # = dim W0 - dim(gW0 cap W0)
    def mulm(g, h):
        a, b, c, d = g; e, f, gg, hh = h
        return (T[a][e] ^ T[b][gg], T[a][f] ^ T[b][hh], T[c][e] ^ T[d][gg], T[c][f] ^ T[d][hh])
    x = 2
    gens = [(1, 1, 0, 1), (1, 0, 1, 1), (1, x, 0, 1), (1, 0, x, 1)]
    # enumerate the group generated
    idx = {(1, 0, 0, 1): 0}; elems = [(1, 0, 0, 1)]
    frontier = [(1, 0, 0, 1)]
    while frontier:
        nf = []
        for g in frontier:
            for s in gens:
                h = mulm(g, s)
                if h not in idx:
                    idx[h] = len(elems); elems.append(h); nf.append(h)
        frontier = nf
    n = len(elems)
    print(f"k={k} q={q} j={j} |group|={n} (|SL2|={q*(q*q-1)})  dim W0={2*j} in F_2^{2*k}")
    edge_d = [dJ(s) for s in gens]
    print("  edge distances d_J(sW0,W0):", edge_d)
    dist = np.array([dJ(g) for g in elems])
    # right Cayley graph g ~ g s ; f(g) = g W0 ; d(f(g), f(h)) = dJ(g^{-1} h) -> pair average = mean over group
    Epairs = dist.mean(); Eedges = np.mean(edge_d)
    K_pairs = np.mean(2.0 ** (-dist)); K_edges = np.mean([2.0 ** (-e) for e in edge_d])
    print(f"  E_edges d={Eedges:.3f}  E_pairs d={Epairs:.3f}  ratio={Epairs/Eedges:.2f}   log2 n={np.log2(n):.1f}")
    print(f"  E_edges 2^-d={K_edges:.4f}  E_pairs 2^-d={K_pairs:.5f}  => lambda_2 >= {(K_edges-K_pairs)/(1-K_pairs):.4f}")
    hist = np.bincount(dist); print("  histogram of d_J(gW0,W0):", hist.tolist())
    if n <= 300000:
        rows = []; cols = []
        for g in elems:
            i = idx[g]
            for s in gens:
                rows.append(i); cols.append(idx[mulm(g, s)])
        A = sp.csr_matrix((np.ones(len(rows)) / len(gens), (rows, cols)), shape=(n, n))
        A = (A + A.T) / 2
        vals = sla.eigsh(A, k=3, which='LA', return_eigenvectors=False, tol=1e-6)
        vals = sorted(vals, reverse=True)
        print("  top eigenvalues of normalized adjacency:", [round(v, 5) for v in vals])

if __name__ == "__main__":
    for k in [int(a) for a in sys.argv[1:]] or [2, 3, 4, 5, 6]:
        main(k)
