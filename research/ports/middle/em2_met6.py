#!/usr/bin/env python3
"""E-M2 (notes §9): which extreme rays of the metric cone MET_6 are rank metrics D_f, f: [6] -> Mat_mu(F_2)?

Step 1. Extreme rays of MET_6 = vertices of {d >= 0, triangle inequalities, sum d = 1}; found as LP optima for
many random objectives (scipy HiGHS), scaled to primitive integer vectors, reduced to S_6-orbits.
Step 2. For each orbit representative delta and c in {1,2,3,4}: search f with D_f = c*delta exactly
(simulated annealing on sum |D_f - c delta|, f(0) = 0, mu from max(c delta) to 8). Exact hits are certified
by recomputation. A miss is "not found", not a proof of non-membership.
Usage: python3 em2_met6.py [objectives] [restarts]"""
import itertools, math, random, sys, time
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

N = 6
PAIRS = list(itertools.combinations(range(N), 2))
PIDX = {p: i for i, p in enumerate(PAIRS)}

def pidx(i, j):
    return PIDX[(min(i, j), max(i, j))]

def triangle_rows():
    rows = []
    for i, j, k in itertools.permutations(range(N), 3):
        if i < j:  # d_ij - d_ik - d_kj <= 0
            r = np.zeros(len(PAIRS)); r[pidx(i, j)] += 1; r[pidx(i, k)] -= 1; r[pidx(k, j)] -= 1
            rows.append(r)
    return np.array(rows)

PERMS = list(itertools.permutations(range(N)))

def canon(v):
    best = None
    for p in PERMS:
        w = tuple(v[pidx(p[i], p[j])] for (i, j) in PAIRS)
        if best is None or w < best:
            best = w
    return best

def to_int(x):
    x = np.where(np.abs(x) < 1e-9, 0, x)
    m = min(t for t in x if t > 0)
    fr = [Fraction(t / m).limit_denominator(24) for t in x]
    l = 1
    for f in fr:
        l = l * f.denominator // math.gcd(l, f.denominator)
    v = [int(f * l) for f in fr]
    g = 0
    for t in v:
        g = math.gcd(g, t)
    return tuple(t // g for t in v)

def is_cut(v):
    vals = set(v) - {0}
    if len(vals) != 1:
        return False
    # cut metric: d_ij = [i,j separated] for some S
    for S in range(1, 1 << (N - 1)):
        if all((v[pidx(i, j)] > 0) == (((S >> i) & 1) != ((S >> j) & 1)) for (i, j) in PAIRS):
            return True
    return False

def rays(nobj, seed=3):
    A = triangle_rows()
    rng = np.random.default_rng(seed)
    found = {}
    for it in range(nobj):
        c = rng.normal(size=len(PAIRS))
        if it % 2 == 1:  # sparse "reward a random pattern" objectives reach the rare non-cut orbits
            c = np.where(rng.random(len(PAIRS)) < 0.3, 3.0, -1.0) + 0.3 * rng.normal(size=len(PAIRS))
        r = linprog(-c, A_ub=A, b_ub=np.zeros(len(A)), A_eq=np.ones((1, len(PAIRS))), b_eq=[1], bounds=(0, None), method="highs")
        v = to_int(r.x)
        k = canon(v)
        found[k] = found.get(k, 0) + 1
    return found

# ---------- F_2 matrices as ints (row i = byte i) ----------
RK = {}
def rank(x):
    r = RK.get(x)
    if r is not None:
        return r
    rows = [(x >> (8 * i)) & 0xFF for i in range(8)]
    basis = {}
    rr = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v; rr += 1; break
    RK[x] = rr
    return rr

def rand_rank_one(rng, mu):
    x = rng.randrange(1, 1 << mu); y = rng.randrange(1, 1 << mu)
    return sum(y << (8 * i) for i in range(mu) if (x >> i) & 1)

def search(target, mu, iters, restarts, rng):
    """min over f of sum |D_f - target| (target: list over PAIRS)."""
    mask = sum(((1 << mu) - 1) << (8 * i) for i in range(mu))
    best = (10 ** 9, None)
    for _ in range(restarts):
        f = [0] + [rng.getrandbits(64) & mask for _ in range(N - 1)]
        err = sum(abs(rank(f[i] ^ f[j]) - target[pidx(i, j)]) for (i, j) in PAIRS)
        for it in range(iters):
            T = 2.0 * (0.01 / 2.0) ** (it / iters)
            v = rng.randrange(1, N)
            u = rng.random()
            if u < 0.5:
                b = f[v] ^ rand_rank_one(rng, mu)
            elif u < 0.8:
                b = f[v] ^ (1 << (8 * rng.randrange(mu) + rng.randrange(mu)))
            else:
                w = rng.randrange(N)
                b = f[w] ^ rand_rank_one(rng, mu)
            de = sum(abs(rank(b ^ f[w]) - target[pidx(v, w)]) - abs(rank(f[v] ^ f[w]) - target[pidx(v, w)]) for w in range(N) if w != v)
            if de <= 0 or rng.random() < math.exp(-de / T):
                f[v] = b; err += de
                if err < best[0]:
                    best = (err, list(f))
                if err == 0:
                    return best
    return best

def main():
    nobj = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    t0 = time.time()
    found = rays(nobj)
    print(f"# MET_6: {len(found)} orbits of extreme rays found from {nobj} random LP objectives ({time.time()-t0:.1f}s)")
    rng = random.Random(7)
    print("| orbit rep (d over pairs 01,02,..,45) | hits | cut? | orbit size | in rank cone? (c, mu, f) | best L1 error per c |")
    print("|---|---|---|---|---|---|")
    for k, hits in sorted(found.items(), key=lambda kv: (max(kv[0]), kv[0])):
        orbit = len({canon_perm for canon_perm in (tuple(k[pidx(p[i], p[j])] for (i, j) in PAIRS) for p in PERMS)})
        cut = is_cut(k)
        res = "cut (diagonal placement)" if cut else None
        errs = []
        if not cut:
            for c in (1, 2, 3, 4):
                tgt = [c * t for t in k]
                lo = max(tgt)
                hit = None
                beste = 10 ** 9
                for mu in range(lo, 9):
                    e, f = search(tgt, mu, 6000, restarts, rng)
                    beste = min(beste, e)
                    if e == 0:
                        # certify
                        assert all(rank(f[i] ^ f[j]) == tgt[pidx(i, j)] for (i, j) in PAIRS)
                        hit = (c, mu, [format(x, "x") for x in f])
                        break
                errs.append(beste)
                if hit:
                    res = f"YES c={hit[0]} mu={hit[1]} f={hit[2]}"
                    break
            if res is None:
                res = "not found (c <= 4, mu <= 8)"
        print(f"| {list(k)} | {hits} | {cut} | {orbit} | {res} | {errs} |", flush=True)
    print(f"# total {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
