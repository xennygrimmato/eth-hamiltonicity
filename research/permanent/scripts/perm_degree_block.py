#!/usr/bin/env python3
"""Bounded-degree block/profile network for #PM of a bipartite graph (exact integers).

Bipartite graph G on rows R and columns C (A = biadjacency 0/1 matrix, max degree Delta).
g blocks; block a owns rows R_a and columns C_a.  E(a,b) = edges between R_a and C_b.
Profile mu = (mu_ab): number of rows of R_a matched into C_b (g x g contingency table with row sums
|R_a|, column sums |C_b|).  For a fixed profile the network is

  * node a: setting = (M_ab)_{b != a}, M_ab a subset of E(a,b) of size mu_ab (the cross edges a's rows
            use into C_b), plus (M_ba)_{b != a} (the cross edges b's rows use into C_a), plus a private
            matching of the remaining rows of R_a into the remaining columns of C_a.
            W_a = [all M_ab, b != a, have distinct rows]
                  * [all M_ba, b != a, have distinct columns, disjoint from the private part]
                  * #{perfect matchings of the leftover rows/columns of block a}.
  * edge {a,b}: both nodes hold M_ab and M_ba, equality-tested, so
            c_ab = ceil(log2 C(|E(a,b)|, mu_ab)) + ceil(log2 C(|E(b,a)|, mu_ba)).

#PM = sum over profiles of the network value.  Every nonzero term is a perfect matching
("bijection-term" network).  U(mu) = 2 sum_{a != b} [lg C(e_ab, mu_ab)] <= 2 lg C(|E|, n) <= 2 n lg(e Delta),
and P_a = sum_{b} (...) <= 2 lg C(Delta n/g, n/g) ~ (2n/g) lg(e Delta).  So the engine gives
#PM in 2^{O(n log Delta / sqrt(log n))}: 2^{o(n)} iff log Delta = o(sqrt(log n)).  For dense A
(Delta = n) this is 2^{Theta(n log n / sqrt(log n))} - worse than Ryser.

Run: python3 perm_degree_block.py  -> PASS/FAIL, U per profile, and the bound 2 lg C(|E|, n).
"""
import itertools, math, random, sys
from math import comb, log2

def lg_choose(a, b):
    c = comb(a, b)
    return math.ceil(log2(c)) if c > 1 else 0

def count_pm(A, rows, cols):
    rows, cols = list(rows), list(cols)
    if len(rows) != len(cols):
        return 0
    if not rows:
        return 1
    i = rows[0]
    return sum(count_pm(A, rows[1:], [c for c in cols if c != j]) for j in cols if A[i][j])

def profiles(rsum, csum):
    g = len(rsum)
    def rec(a, colleft):
        if a == g:
            if all(c == 0 for c in colleft):
                yield []
            return
        def comp(b, left):
            if b == g:
                if left == 0:
                    yield []
                return
            for v in range(min(left, colleft[b]) + 1):
                for rest in comp(b + 1, left - v):
                    yield [v] + rest
        for row in comp(0, rsum[a]):
            for rest in rec(a + 1, [c - v for c, v in zip(colleft, row)]):
                yield [row] + rest
    yield from rec(0, list(csum))

def network_value(A, R, C, mu):
    g = len(R)
    E = {(a, b): [(i, j) for i in R[a] for j in C[b] if A[i][j]] for a in range(g) for b in range(g) if a != b}
    keys = list(E)
    alph = {k: [frozenset(s) for s in itertools.combinations(E[k], mu[k[0]][k[1]])] for k in keys}
    total = 0
    for choice in itertools.product(*[alph[k] for k in keys]):
        M = dict(zip(keys, choice))
        w = 1
        for a in range(g):
            out_rows = [i for b in range(g) if b != a for (i, j) in M[(a, b)]]
            in_cols = [j for b in range(g) if b != a for (i, j) in M[(b, a)]]
            if len(set(out_rows)) != len(out_rows) or len(set(in_cols)) != len(in_cols):
                w = 0; break
            rows_left = [i for i in R[a] if i not in out_rows]
            cols_left = [j for j in C[a] if j not in in_cols]
            w *= count_pm(A, rows_left, cols_left)
            if w == 0:
                break
        total += w
    return total

def bits(A, R, C, mu):
    g = len(R)
    e = {(a, b): sum(1 for i in R[a] for j in C[b] if A[i][j]) for a in range(g) for b in range(g) if a != b}
    c = {(a, b): lg_choose(e[(a, b)], mu[a][b]) + lg_choose(e[(b, a)], mu[b][a]) for (a, b) in e}
    U = sum(c.values())                      # every ordered pair counted: U = sum_{a != b} c_ab
    P = max(sum(c[(a, b)] for b in range(g) if b != a) for a in range(g))
    return U, P

def random_bipartite(n, Delta, rng):
    """0/1 n x n matrix with every row and column degree <= Delta (random regular-ish)."""
    while True:
        A = [[0] * n for _ in range(n)]
        cols = list(range(n)) * Delta
        rng.shuffle(cols)
        ok = True
        for i in range(n):
            mine = cols[i * Delta:(i + 1) * Delta]
            if len(set(mine)) < Delta:
                ok = False; break
            for j in mine:
                A[i][j] = 1
        if ok:
            return A

def main():
    rng = random.Random(3)
    ok = True
    for n, g, Delta in [(4, 2, 2), (6, 2, 2), (6, 3, 2), (6, 2, 3), (6, 3, 3), (6, 2, 6), (7, 2, 3)]:
        A = random_bipartite(n, Delta, rng) if Delta < n else [[1] * n for _ in range(n)]
        R = [list(range(a * n // g, (a + 1) * n // g)) for a in range(g)]
        C = [list(range(a * n // g, (a + 1) * n // g)) for a in range(g)]
        rs = [len(r) for r in R]
        tot = 0; Umax = 0; Pmax = 0; npr = 0
        for mu in profiles(rs, rs):
            # mu_aa is implicit (rows matched inside the block); only a != b entries are labels
            npr += 1
            tot += network_value(A, R, C, mu)
            U, P = bits(A, R, C, mu)
            Umax = max(Umax, U); Pmax = max(Pmax, P)
        pm = count_pm(A, range(n), range(n))
        good = tot == pm; ok &= good
        nE = sum(map(sum, A))
        print(f"n={n} g={g} Delta={Delta} |E|={nE}: #PM={pm} sum over {npr} profiles={tot} {'ok' if good else 'MISMATCH'}; "
              f"max U={Umax}, bound 2 lg C(|E|,n)={2*lg_choose(nE, n)}, 2n lg(e Delta)={2*n*log2(math.e*Delta):.1f}; max P={Pmax}")
    print("bijection-term network: U <= 2 lg C(|E|, n) <= 2 n lg(e Delta); dense Delta=n gives Theta(n log n).")
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
