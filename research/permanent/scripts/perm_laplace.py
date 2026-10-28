#!/usr/bin/env python3
"""Laplace / column-partition network for the permanent (exact integers).

Rows are split into h groups R_a, columns into h blocks C_b.  For a *pattern* N (an h x h
contingency table with row sums |R_a| and column sums |C_b|) the network N_N has

  * row nodes a:  setting = (T_ab)_b, T_ab a subset of C_b of size N_ab (the columns of block b that
                  group a uses);  W_a = per(A[R_a, union_b T_ab]).
  * column nodes b: setting = (T_ab)_a;  W_b = [the T_ab, a=1..h, partition C_b].
  * edge {a,b}: the label T_ab is shared, c_ab = ceil(log2 C(|C_b|, N_ab)) bits.

Then per(A) = sum_N value(N_N).  (This is also exactly the "surjection network": private maps
j : R_a -> [n] at the row nodes, private Ryser variables x_b at the column nodes, shared hit sets
im(j_a) & C_b.  The Ryser sum at a column node collapses to the covering test, and the covering
test forces the hit sets to be a partition, so the two networks coincide.)

Bit accounting: U(N) = 2 sum_ab log2 C(|C_b|, N_ab) <= 2 n (log2 h + log2 e), attained near the
uniform pattern.  Max node load P_a = sum_b c_ab <= log2 C(n, n/h) ~ (n/h) log2(h e).

Run: python3 perm_laplace.py     -> prints PASS/FAIL and the bit counts.
"""
import itertools, math, random, sys
from math import comb, log2

def permanent(A, rows, cols):
    rows, cols = list(rows), list(cols)
    if len(rows) != len(cols):
        return 0
    tot = 0
    for p in itertools.permutations(cols):
        t = 1
        for i, j in zip(rows, p):
            t *= A[i][j]
            if t == 0:
                break
        tot += t
    return tot

def patterns(rsum, csum):
    """all nonneg integer h x h matrices with given row and column sums."""
    h = len(rsum)
    def rec(a, colleft):
        if a == h:
            if all(c == 0 for c in colleft):
                yield []
            return
        # compositions of rsum[a] into h parts bounded by colleft
        def comp(b, left):
            if b == h:
                if left == 0:
                    yield []
                return
            for v in range(min(left, colleft[b]) + 1):
                for rest in comp(b + 1, left - v):
                    yield [v] + rest
        for row in comp(0, rsum[a]):
            newleft = [c - v for c, v in zip(colleft, row)]
            for rest in rec(a + 1, newleft):
                yield [row] + rest
    yield from rec(0, list(csum))

def network_value(A, R, C, N):
    """brute-force sum over all labellings of the product of node tables."""
    h = len(R)
    # label alphabet for edge (a,b): subsets of C[b] of size N[a][b]
    alph = {(a, b): [frozenset(s) for s in itertools.combinations(C[b], N[a][b])] for a in range(h) for b in range(h)}
    keys = list(alph)
    total = 0
    for choice in itertools.product(*[alph[k] for k in keys]):
        T = dict(zip(keys, choice))
        w = 1
        for b in range(h):  # column nodes: partition test
            parts = [T[(a, b)] for a in range(h)]
            if sum(len(p) for p in parts) != len(C[b]) or frozenset().union(*parts) != frozenset(C[b]):
                w = 0
                break
        if w == 0:
            continue
        for a in range(h):  # row nodes: block permanent
            cols = sorted(frozenset().union(*[T[(a, b)] for b in range(h)]))
            w *= permanent(A, R[a], cols)
            if w == 0:
                break
        total += w
    return total

def bits(C, N):
    h = len(N)
    c = [[math.ceil(log2(comb(len(C[b]), N[a][b]))) if comb(len(C[b]), N[a][b]) > 1 else 0 for b in range(h)] for a in range(h)]
    U = 2 * sum(sum(r) for r in c)
    Prow = max(sum(c[a]) for a in range(h))
    Pcol = max(sum(c[a][b] for a in range(h)) for b in range(h))
    return U, Prow, Pcol

def main():
    rng = random.Random(1)
    ok = True
    for n, h in [(4, 2), (5, 2), (6, 2), (6, 3), (7, 2), (7, 3)]:
        A = [[rng.randint(0, 1) if rng.random() < 0.9 else 0 for _ in range(n)] for _ in range(n)]
        R = [list(range(a * n // h, (a + 1) * n // h)) for a in range(h)]
        C = [list(range(b * n // h, (b + 1) * n // h)) for b in range(h)]
        rs = [len(r) for r in R]; cs = [len(c) for c in C]
        tot = 0; Umax = 0; Pmax = 0; npat = 0
        for N in patterns(rs, cs):
            npat += 1
            tot += network_value(A, R, C, N)
            U, Pr, Pc = bits(C, N)
            Umax = max(Umax, U); Pmax = max(Pmax, Pr, Pc)
        p = permanent(A, range(n), range(n))
        good = (tot == p)
        ok &= good
        print(f"n={n} h={h}: per={p} sum over {npat} patterns={tot} {'ok' if good else 'MISMATCH'}; "
              f"max_N U(N)={Umax}  (2n log2 h = {2*n*log2(h):.1f}, 2n(log2 h+log2 e) = {2*n*(log2(h)+log2(math.e)):.1f}), max node load P={Pmax}")
    print("asymptotics: U = 2 sum_ab log2 C(n/h, N_ab) <= 2n(log2 h + 1.44); P ~ (n/h) log2(h e);")
    print("             number of patterns <= (n/h+1)^(h^2) = 2^{O(h^2 log n)}.")
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
