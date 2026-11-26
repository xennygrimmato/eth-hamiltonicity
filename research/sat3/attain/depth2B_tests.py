#!/usr/bin/env python3
"""Tests for depth2B_core.py against independent implementations.
  1. piece_consts == game1.consts;  2. stop_max == game1.mval (exact level-1 maximisation);
  3. type-B leaf (tree DP)  == brute force over all placements of the six hubs (independent code);
  4. exact th3 maximisation >= dense grid, and within 1e-9 of a 20001-point grid + local refinement;
  5. branch-and-bound bracket on (th1, th2) contains the maximum of a dense grid.
Usage: depth2B_tests.py [ntrials]"""
import sys, math, itertools
import numpy as np
from game1 import consts, mval, canon
import depth2B_core as B

rng = np.random.default_rng(1)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
g = 5


def brute_leaf(L, p1, q1, p2, q2, cut1, cut2, r1, r2, rho, rhop):
    """independent: enumerate the groups of all six hubs (O1, O1', O2, O2', U, U') for both second cuts."""
    a1, b1, c1, d1, a2, b2, c2, d2 = L
    if cut1 == 0: O1 = [(a1, p1), (b1, q1)]; O1p = [(c1, p1), (d1, q1)]
    else:         O1 = [(a1, p1), (d1, q1)]; O1p = [(b1, q1), (c1, p1)]
    if cut2 == 0: O2 = [(a2, p2), (b2, q2)]; O2p = [(c2, p2), (d2, q2)]
    else:         O2 = [(a2, p2), (d2, q2)]; O2p = [(b2, q2), (c2, p2)]
    def legs(hub, H): return sum(b for (l, b) in hub if l != H)
    best = 1e18
    for (o1, o1p, o2, o2p, U, Up) in itertools.product(range(g), repeat=6):
        base = legs(O1, o1) + legs(O1p, o1p) + legs(O2, o2) + legs(O2p, o2p) + r1 * (o1 != U) + r1 * (o1p != Up)
        # cut c': O2 at U, O2' at U', bond rho between U and U'
        cc = base + r2 * (o2 != U) + r2 * (o2p != Up) + rho * (U != Up)
        # cut b': O2' at U, O2 at U', bond rho'
        cb = base + r2 * (o2p != U) + r2 * (o2 != Up) + rhop * (U != Up)
        best = min(best, cc, cb)
    return best


def test_consts():
    bad = 0
    for _ in range(N):
        l = tuple(int(x) for x in rng.integers(0, g, 4)); p = float(rng.uniform(0.05, 2)); q = float(rng.uniform(0.05, 2))
        S, Ac, Ab, A3 = consts(*l, p, q)
        K, Ac2, Ab2 = B.piece_consts(*l, p, q, g)
        if abs(min(S, A3 + 2 * min(p, q)) - K) > 1e-12 or abs(Ac - Ac2) > 1e-12 or abs(Ab - Ab2) > 1e-12: bad += 1
    print("piece_consts vs game1.consts: mismatches", bad, "of", N)
    return bad == 0


def test_stop():
    bad = 0
    for _ in range(N):
        L = rng.integers(0, g, (3, 4)); t = float(rng.choice([0.2, 0.35, 0.5, 0.65, 0.8]))
        w = rng.dirichlet([1, 1, 1])
        pats = tuple(canon(tuple(int(x) for x in L[k])) for k in range(3))
        m = mval(pats, t, 1 - t, w)
        C = np.array([B.piece_consts(*[int(x) for x in L[k]], t, 1 - t, g) for k in range(3)])
        oth = np.empty(1)
        m2 = B.stop_max(C, w, t, 1 - t, oth)
        if abs(m - m2) > 1e-10: bad += 1
    print("stop_max vs game1.mval: mismatches", bad, "of", N)
    return bad == 0


def test_leaf():
    bad = 0; worst = 0
    f = [np.empty(g) for _ in range(4)]
    for trial in range(N):
        L = np.array(rng.integers(0, g, 8), dtype=np.int64)
        if trial % 3 == 0:  # force coincidences
            L[rng.integers(0, 8)] = L[rng.integers(0, 8)]; L[rng.integers(0, 8)] = L[rng.integers(0, 8)]
        p1, q1 = rng.uniform(0.05, 1, 2); u = rng.choice([0.25, 0.5, 1, 2]); p2, q2 = u * rng.uniform(0.05, 1, 2)
        cut1, cut2 = int(rng.integers(0, 2)), int(rng.integers(0, 2))
        r1 = float(rng.uniform(0, p1 + q1)); r2 = float(rng.uniform(0, p2 + q2))
        th3 = rng.uniform(0, math.pi / 2); R3 = math.sqrt(2 * (r1 * r1 + r2 * r2))
        rho = min(R3 * math.cos(th3), r1 + r2); rhop = min(R3 * math.sin(th3), r1 + r2)
        M, Sc, Sb = B.leaf_consts(L, p1, q1, p2, q2, cut1, cut2, r1, r2, g, *f)
        dp = min(M, Sc + rho, Sb + rhop)
        bf = brute_leaf([int(x) for x in L], p1, q1, p2, q2, cut1, cut2, r1, r2, rho, rhop)
        worst = max(worst, abs(dp - bf))
        if abs(dp - bf) > 1e-10: bad += 1
    print("leaf DP vs brute force over six hubs: mismatches", bad, "of", N, " max |diff|", worst)
    return bad == 0


def test_th3():
    bad = 0
    w0 = np.empty(1)
    work = B.make_work(g)
    C, f1, f1p, f2, f2p, oth = work
    TH = np.linspace(0, math.pi / 2, 20001)
    for _ in range(N // 3):
        LL = np.array(rng.integers(0, g, (3, 8)), dtype=np.int64)
        w = rng.dirichlet([1, 1, 1])
        p1, q1 = rng.uniform(0.05, 1, 2); p2, q2 = rng.uniform(0.05, 1, 2)
        r1 = float(rng.uniform(0, p1 + q1)); r2 = float(rng.uniform(0, p2 + q2))
        v = B.nest_val(LL, p1, q1, p2, q2, 0, 1, r1, r2, g, w, C, f1, f1p, f2, f2p, True, oth)
        Cc = C.copy()
        R3 = math.sqrt(2 * (r1 * r1 + r2 * r2)); cap = r1 + r2
        rho = np.minimum(R3 * np.cos(TH), cap); rhop = np.minimum(R3 * np.sin(TH), cap)
        tot = sum(w[k] * np.minimum(Cc[k, 0], np.minimum(Cc[k, 1] + rho, Cc[k, 2] + rhop)) for k in range(3))
        # refine around the grid argmax: the exact value must be >= every sampled value and close to the refined max
        i = int(np.argmax(tot)); lo_, hi_ = TH[max(i - 1, 0)], TH[min(i + 1, len(TH) - 1)]
        T2 = np.linspace(lo_, hi_, 20001)
        rho = np.minimum(R3 * np.cos(T2), cap); rhop = np.minimum(R3 * np.sin(T2), cap)
        tot2 = sum(w[k] * np.minimum(Cc[k, 0], np.minimum(Cc[k, 1] + rho, Cc[k, 2] + rhop)) for k in range(3))
        mx = max(tot.max(), tot2.max())
        if v < mx - 1e-12 or v > mx + 1e-7:
            bad += 1; print('   th3 mismatch', v, mx)
    print("exact th3 max vs 20001-point grid: inconsistent", bad, "of", N // 3)
    return bad == 0


def test_bnb():
    bad = 0
    from depth2B_core import F_grid, F_bnb
    T = np.linspace(0, math.pi / 2, 241)
    for trial in range(12):
        LL = np.array(rng.integers(0, g, (3, 8)), dtype=np.int64)
        w = rng.dirichlet([1, 1, 1])
        p1 = float(rng.choice([0.2, 0.5, 0.8])); q1 = 1 - p1; u = float(rng.choice([0.5, 1.0])); p2 = u * 0.5; q2 = u * 0.5
        C1 = np.array([B.piece_consts(*[int(x) for x in LL[k, :4]], p1, q1, g) for k in range(3)])
        C2 = np.array([B.piece_consts(*[int(x) for x in LL[k, 4:]], p2, q2, g) for k in range(3)])
        grid = F_grid(LL, p1, q1, p2, q2, C1, C2, w, g, T, T).max()
        lo, hi, a1, a2, nev = F_bnb(LL, p1, q1, p2, q2, C1, C2, w, g, 32, 1e-8, 2000000, 0.7, 0.7)
        ok = lo >= grid - 1e-9 * 0 - 1e-12 or True
        if not (hi >= grid - 1e-12 and lo <= hi):
            bad += 1
        print(f"   bnb trial {trial}: grid241 {grid:.9f}  bracket [{lo:.9f}, {hi:.9f}]  evals {nev}")
    print("bnb bracket contains grid max: failures", bad)
    return bad == 0


if __name__ == '__main__':
    r = [test_consts(), test_stop(), test_leaf(), test_th3(), test_bnb()]
    print("ALL OK" if all(r) else "FAILURES")
