#!/usr/bin/env python3
"""dense_lowrank_hc.py -- Theorem 1 of dense-structured.md: HC(L + D), rank L <= r, D sparse.

Checks, exactly, on random instances (n <= 8, r <= 3, integer U, V in [-2,2], signed sparse D):
 (I1) expansion over directed linear forests:
        HC(L+D) = HC(D) + sum_{F acyclic, indeg,outdeg<=1, F subset supp D} D^F * N_L(F),
        N_L(F) = sum over cyclic orders of the units of F of prod L[head_i][tail_{i+1}]   (brute force);
 (I2) labelled-Eulerian (BEST) form:  N-sum  sum_N ec(N) [z^N] prod_units l_unit(z),
        l_unit(z) = sum_{a,b} V[tail][a] U[head][b] z_ab,   ec = t_w(N) prod_a (d_a - 1)!;
 (I3) the n^{O(r)}-evaluation form actually used by the algorithm:
        HC(L+D) = HC(D) + sum_{R subset [r]} sum_{T in-arborescence on R rooted at min R}
                   sum_d prod_{a in R}(d_a-1)! [w^d x^0 t_T^1] Q_{R,T}(w,x,t),
        Q_{R,T} = sum_F D^F prod_units ( alpha_R(u) beta_R(w) + sum_{(a->b) in T} t_ab V_ua w_a x_a U_wb / x_b ),
        alpha_R(u) = sum_{a in R} V_ua w_a x_a,  beta_R(w) = sum_{b in R} U_wb / x_b.
 (E2) r = 1, L = J, D = -adjacency of a sparse graph: (I3)/2 equals #HC(K_n - D) (the earlier E2).
Prints PASS/FAIL per instance and the number of (R,T) pairs (= outer terms) per r.
"""
import itertools, random, sys
from math import factorial
sys.path.insert(0, __import__('os').path.dirname(__file__))
from dense_lib import *


def N_L_brute(F, n, L):
    us = units(F, n)
    k = len(us)
    tot = 0
    for p in itertools.permutations(range(1, k)):
        seq = (0,) + p
        pr = 1
        for i in range(k):
            pr *= L[us[seq[i]][1]][us[seq[(i + 1) % k]][0]]
        tot += pr
    return tot


def I1(n, L, D):
    arcs = arcs_of(D)
    tot = 0
    for F in dir_subsets(arcs, n):
        if is_ham_dicycle(F, n):
            tot += wprod(D, F)
            continue
        if units(F, n) is None:
            continue
        tot += wprod(D, F) * N_L_brute(F, n, L)
    return tot


def I2(n, r, U, V, D):
    arcs = arcs_of(D)
    tot = 0
    for F in dir_subsets(arcs, n):
        if is_ham_dicycle(F, n):
            tot += wprod(D, F); continue
        us = units(F, n)
        if us is None:
            continue
        P = {tuple([0] * (r * r)): 1}
        for (u, w) in us:
            lu = {}
            for a in range(r):
                for b in range(r):
                    c = V[u][a] * U[w][b]
                    if c:
                        e = [0] * (r * r); e[a * r + b] = 1
                        lu[tuple(e)] = lu.get(tuple(e), 0) + c
            P = pmul(P, lu)
        s = 0
        for e, c in P.items():
            N = [[e[a * r + b] for b in range(r)] for a in range(r)]
            s += c * best_ec(N, r)
        tot += wprod(D, F) * s
    return tot


def I3(n, r, U, V, D, count=None):
    arcs = arcs_of(D)
    Fs = []
    base = 0
    for F in dir_subsets(arcs, n):
        if is_ham_dicycle(F, n):
            base += wprod(D, F); continue
        us = units(F, n)
        if us is not None:
            Fs.append((wprod(D, F), us))
    tot = base
    pairs = 0
    for s in range(1, r + 1):
        for R in itertools.combinations(range(r), s):
            for par in in_arborescences(list(R)):
                pairs += 1
                T = sorted(par.items())             # arcs (a -> par a)
                nv = 2 * r + len(T)
                trunc = lambda e: all(e[2 * r + i] <= 1 for i in range(len(T)))
                def ell(u, w):
                    P = {}
                    for a in R:
                        for b in R:
                            c = V[u][a] * U[w][b]
                            if not c: continue
                            e = [0] * nv; e[a] += 1; e[r + a] += 1; e[r + b] -= 1
                            P[tuple(e)] = P.get(tuple(e), 0) + c
                            if (a, b) in T:
                                e2 = list(e); e2[2 * r + T.index((a, b))] = 1
                                P[tuple(e2)] = P.get(tuple(e2), 0) + c
                    return P
                Q = {}
                for (dF, us) in Fs:
                    P = {tuple([0] * nv): dF}
                    for (u, w) in us:
                        P = pmul(P, ell(u, w), trunc)
                    Q = padd(Q, P)
                for e, c in Q.items():
                    if any(e[r + a] for a in range(r)): continue
                    if any(e[2 * r + i] != 1 for i in range(len(T))): continue
                    pr = 1
                    for a in R:
                        assert e[a] >= 1
                        pr *= factorial(e[a] - 1)
                    tot += c * pr
    if count is not None:
        count.append(pairs)
    return tot


def rand_inst(rng, n, r, m, vals=(-2, -1, 1, 2)):
    U = [[rng.randint(-2, 2) for _ in range(r)] for _ in range(n)]
    V = [[rng.randint(-2, 2) for _ in range(r)] for _ in range(n)]
    L = [[sum(U[i][k] * V[j][k] for k in range(r)) for j in range(n)] for i in range(n)]
    offd = [(i, j) for i in range(n) for j in range(n) if i != j]
    D = [[0] * n for _ in range(n)]
    for (i, j) in rng.sample(offd, m):
        D[i][j] = rng.choice(vals)
    return U, V, L, D


def main():
    rng = random.Random(20261029)
    allok = True
    cases = [(4, 1, 4), (5, 1, 6), (5, 2, 5), (6, 2, 6), (6, 3, 5), (7, 2, 7), (7, 3, 6), (6, 3, 8), (7, 1, 9), (5, 3, 7)]
    for (n, r, m) in cases:
        U, V, L, D = rand_inst(rng, n, r, m)
        A = [[L[i][j] + D[i][j] for j in range(n)] for i in range(n)]
        truth = hc_dir_brute(A)
        a1 = I1(n, L, D); a2 = I2(n, r, U, V, D); cnt = []; a3 = I3(n, r, U, V, D, cnt)
        ok = truth == a1 == a2 == a3
        allok &= ok
        print(f"n={n} r={r} m={m}: brute={truth} I1={a1} I2={a2} I3={a3} (R,T)-pairs={cnt[0]}  {'PASS' if ok else 'FAIL'}")
    # E2 consistency: K_n - D with D a sparse undirected graph
    for (n, m) in [(6, 5), (7, 6), (8, 6)]:
        offd = [(i, j) for i in range(n) for j in range(i + 1, n)]
        E = rng.sample(offd, m)
        Dm = [[0] * n for _ in range(n)]
        for i, j in E:
            Dm[i][j] = Dm[j][i] = -1
        U = [[1] for _ in range(n)]; V = [[1] for _ in range(n)]
        G = [[0 if i == j else 1 + Dm[i][j] for j in range(n)] for i in range(n)]
        truth = hc_dir_brute(G) // 2
        a3 = I3(n, 1, U, V, Dm)
        ok = (a3 % 2 == 0) and a3 // 2 == truth
        allok &= ok
        print(f"E2 check K_{n} - D, |D|={m}: #HC={truth} I3/2={a3/2}  {'PASS' if ok else 'FAIL'}")
    print("ALL PASS" if allok else "SOME FAIL")


if __name__ == "__main__":
    main()
