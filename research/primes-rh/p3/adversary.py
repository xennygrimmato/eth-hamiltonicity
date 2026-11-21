"""Block adversary for parity-query prime finding (p3, subtask 3).

Given ANY k query sets a_1..a_k subset of [0,n) (answers mod 2) and ANY output point x,
build v in {0,1}^n with  <a_i,v> = 0 mod 2 for all i,  v_x = 0,  max gap <= (k+1)(log N+2)-ish,
and prefix counts within k+1 of the target density 1/logN.
Construction (notebook Thm 1): any k+1 columns of the k x n parity-check matrix are dependent,
so every block of k+1 coordinates carries a nonzero codeword; take a greedy disjoint sum.
Usage: python3 adversary.py
"""
import numpy as np, math, random

def nullvec(Hsub):
    """nonzero x with Hsub x = 0 over GF(2); Hsub is k x (k+1) uint8."""
    A = Hsub.copy() % 2
    k, m = A.shape
    piv_cols, r = [], 0
    for c in range(m):
        p = next((i for i in range(r, k) if A[i, c]), None)
        if p is None:
            continue
        A[[r, p]] = A[[p, r]]
        for i in range(k):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        piv_cols.append(c); r += 1
        if r == k:
            break
    free = [c for c in range(m) if c not in piv_cols][0]
    x = np.zeros(m, np.uint8); x[free] = 1
    for i, c in enumerate(piv_cols):
        x[c] = A[i, free]
    return x

def adversary(H, x, logN):
    k, n = H.shape
    coords = [i for i in range(n) if i != x]
    blocks = [coords[i:i + k + 1] for i in range(0, len(coords) - k, k + 1)]
    v = np.zeros(n, np.uint8)
    for b in blocks:
        target = (b[-1] + 1) / logN           # want prefix count ~ position/logN
        if v[:b[0]].sum() < target:
            v[b] ^= nullvec(H[:, b])
    return v

def check(H, v, x, logN):
    syn = (H.astype(int) @ v.astype(int)) % 2
    ones = np.flatnonzero(v)
    gaps = np.diff(np.concatenate(([-1], ones, [len(v)])))
    pref = np.cumsum(v) - np.arange(1, len(v) + 1) / logN
    return syn.any(), v[x], gaps.max(), np.abs(pref).max()

if __name__ == "__main__":
    rng = np.random.default_rng(1)
    n, logN = 6000, math.log(10**12)   # think of [N,N+n) with N=10^12
    for fam in ["random sets", "intervals", "intervals x APs (q<=50)"]:
        for k in [10, 40, 120]:
            H = np.zeros((k, n), np.uint8)
            for i in range(k):
                if fam == "random sets":
                    H[i] = rng.integers(0, 2, n)
                else:
                    a, b = sorted(rng.integers(0, n, 2))
                    H[i, a:b + 1] = 1
                    if fam.startswith("intervals x"):
                        q = int(rng.integers(1, 51)); r = int(rng.integers(0, q))
                        mask = (np.arange(n) % q) == r
                        H[i] &= mask
            x = int(rng.integers(0, n))
            v = adversary(H, x, logN)
            bad, vx, g, e = check(H, v, x, logN)
            print(f"{fam:24s} k={k:4d}: syndrome!=0:{bad} v_x={vx} maxgap={g:5d} "
                  f"(bound {(k+1)*(int(logN)+3)}) max prefix err={e:6.1f} (bound {k+2}) |v|={v.sum()} target={n/logN:.0f}")
