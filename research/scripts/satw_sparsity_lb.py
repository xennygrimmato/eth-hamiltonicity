"""satw_sparsity_lb.py -- research/sat-width.md, Section 3.3 (Theorem S: a density lower bound for sparsification).

Run: python3 -I satw_sparsity_lb.py

Theorem S. Let k >= 3, k' >= 1, n >= 2, 0 < alpha <= 1, m = ceil(alpha 2^k n), 0 < sigma < 1, D > 0 with
    (*)  Dn (k' log2(2n) + 2) + log2(e) alpha n 2^{k sigma} ... see the text; concretely
         2^{Dn(k' log2(2n)+2)} * exp(-m 2^{-k(1-sigma)}) < (1 - 2^-k)^m / 2.
Then some k-CNF phi with m clauses on n variables has |sol phi| >= 2^n (1-2^-k)^m / 2 and no CNF G of
width <= k' with <= Dn clauses has 2^{sigma n} <= |sol G| and sol G subset sol phi. Hence any cover
sol phi = U_{i<=N} sol G_i by such G_i needs N >= 2^{n(1-sigma)} (1-2^-k)^m / 2.

S1  Shearer step: Pr_C[S meets the falsifying subcube of a uniform random k-clause C] = E_V |S_V| / 2^k
    >= 2^{-k(1-sigma)} for |S| = 2^{sigma n}: exact over all k-sets V, for random sets, subcubes,
    affine subspaces and Hamming balls (n = 12, k = 3..5).
S2  Monte Carlo: Pr_phi[S subset sol phi] <= exp(-m 2^{-k(1-sigma)}) for a few fixed S (n = 10).
S3  Parameters: with alpha = (1-2^-k)/(k log2 e) and sigma = 1 - eps - 1/k - 3/n (so that N <= 2^{eps n}
    is impossible), the least D violating (*) satisfies log2 D >= k(1-eps) - log2(k' log2(2n)+2) - log2 k - 3
    whenever k(1-eps) >= 3;
    checked for k = 3..200, n = 2^10..2^4096 (as log2 n), eps in {1/2, 1/4, 1/100}.
S4  Consequence in the regime of Theorem D (eps ~ 1/sqrt(log n)): a sparsification with outputs of density
    (k/eps)^c (any c) on the same variables is impossible as soon as k >= C_c log log n; prints the crossover k.
"""
import random
from itertools import combinations
from math import comb, exp, log, log2, sqrt, ceil

FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def hit_prob(S, n, k):
    tot = 0
    cnt = 0
    for V in combinations(range(n), k):
        proj = set(tuple((x >> v) & 1 for v in V) for x in S)
        tot += len(proj)
        cnt += 1
    return tot / cnt / 2 ** k


rng = random.Random(11)
n = 12
print("S1  hit probability vs Shearer bound 2^{-k(1-sigma)}")
worst = 10.0
for k in [3, 4, 5]:
    fams = []
    for size_exp in [3, 6, 9]:
        fams.append(("random", rng.sample(range(1 << n), 1 << size_exp)))
        fams.append(("subcube", [x << (n - size_exp) for x in range(1 << size_exp)]))
        # random affine subspace of dimension size_exp
        basis = [rng.randrange(1, 1 << n) for _ in range(size_exp)]
        shift = rng.randrange(1 << n)
        sub = set()
        for c in range(1 << size_exp):
            v = shift
            for i in range(size_exp):
                if c >> i & 1:
                    v ^= basis[i]
            sub.add(v)
        fams.append(("affine", list(sub)))
    for r in [1, 2, 3]:
        fams.append(("ball", [x for x in range(1 << n) if bin(x).count("1") <= r]))
    for name, S in fams:
        sigma = log2(len(S)) / n
        p = hit_prob(S, n, k)
        lb = 2 ** (-k * (1 - sigma))
        check(p >= lb - 1e-12, f"S1 {name} k={k} |S|={len(S)}: {p} < {lb}")
        worst = min(worst, p / lb)
print(f"    all families: min ratio hit/bound = {worst:.3f} (>= 1)")


# S2
def rand_clause(n, k):
    V = rng.sample(range(n), k)
    return [(v, rng.random() < 0.5) for v in V]


def sat(C, x):
    return any(((x >> v) & 1) == pos for v, pos in C)


n2 = 10
for k, m, S in [(3, 20, list(range(64))), (3, 10, rng.sample(range(1 << n2), 32)), (4, 40, [x << 5 for x in range(32)])]:
    sigma = log2(len(S)) / n2
    trials = 20000
    good = 0
    for _ in range(trials):
        ok = True
        for _ in range(m):
            C = rand_clause(n2, k)
            if not all(sat(C, x) for x in S):
                ok = False
                break
        good += ok
    bound = exp(-m * 2 ** (-k * (1 - sigma)))
    est = good / trials
    check(est <= bound + 3 * sqrt(bound / trials) + 1e-3, f"S2 k={k} m={m}: {est} > {bound}")
    print(f"S2  k={k} m={m} |S|={len(S)}: Pr[S in sol phi] ~ {est:.4f} <= exp(-m 2^-k(1-sigma)) = {bound:.4f}")


# S3
def log2_union(D, n_log2, kp):
    # log2 of 2^{Dn(k' log2(2n)+2)} divided by n: D (k' (n_log2+1) + 2)
    return D * (kp * (n_log2 + 1) + 2)


def holds_log(lD, k, kp, n_log2, alpha, sigma):
    # (*) per variable in log2:  2^lD (k'log2 2n + 2) - log2(e) alpha 2^{k sigma} < alpha 2^k log2(1-2^-k) - 1/n
    # i.e. 2^lD * A + R < a * 2^{k sigma} with A = k'log2 2n + 2, a = log2(e) alpha, R = 1/n - alpha 2^k log2(1-2^-k) > 0
    A = kp * (n_log2 + 1) + 2
    a = log2(exp(1)) * alpha
    R = 2.0 ** (-min(n_log2, 1000)) - alpha * 2 ** k * log2(1 - 2 ** -k) if k < 1000 else alpha * log2(exp(1)) * (1 + 2.0 ** -k)
    t = k * sigma + log2(a)  # log2 of a 2^{k sigma}
    if t < 1020 and 2 ** t <= R:
        return False
    rest = log2(1 - R / 2 ** t) if t < 1020 else 0.0
    return lD + log2(A) < t + rest


def Dstar(k, kp, n_log2, eps):
    alpha = (1 - 2.0 ** -k) / (k * log2(exp(1)))
    sigma = 1 - eps - 1 / k - 3 * 2.0 ** (-min(n_log2, 1000))
    lo, hi = -60.0, 4.0 * k + 10
    if not holds_log(lo, k, kp, n_log2, alpha, sigma):
        return None, alpha, sigma
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds_log(mid, k, kp, n_log2, alpha, sigma):
            lo = mid
        else:
            hi = mid
    return lo, alpha, sigma


print("S3  log2 D* (least density forced) vs the claimed bound k(1-eps) - log2(k'log2(2n)+2) - log2 k - 3")
for eps in [0.5, 0.25, 0.01]:
    for n_log2 in [10, 64, 1024, 4096]:
        row = []
        for k in [3, 8, 16, 32, 64, 128, 200]:
            kp = k
            lD, alpha, sigma = Dstar(k, kp, n_log2, eps)
            claim = k * (1 - eps) - log2(kp * (n_log2 + 1) + 2) - log2(k) - 3 if k * (1 - eps) >= 3 else -1e9
            if lD is None:
                check(claim <= 0, f"S3 no D but claim positive k={k}")
                row.append("   -  ")
                continue
            # number of outputs forced: N >= 2^{n(1-sigma)} (1-2^-k)^m / 2 = 2^{n(1 - sigma + alpha 2^k log2(1-2^-k)) - 1}
            forced = 1 - sigma + alpha * 2.0 ** k * log2(1 - 2.0 ** -k)
            check(forced > eps, f"S3 forced exponent {forced} <= eps {eps} (k={k})")
            check(lD >= claim - 1e-9, f"S3 k={k} n=2^{n_log2} eps={eps}: log2 D* {lD} < claim {claim}")
            row.append(f"{lD:6.1f}")
        print(f"    eps={eps:<5} log2 n={n_log2:5d}: " + " ".join(row) + "   (k = 3,8,16,32,64,128,200)")

# S4
print("S4  crossover: least k with log2 D*(k) > c log2(k/eps), eps = 1/sqrt(log2 n), k' = k")
for n_log2 in [2 ** 10, 2 ** 20, 2 ** 40, 2 ** 80]:
    eps = 1 / sqrt(n_log2)
    out = []
    for c in [3, 10]:
        kc = None
        for k in range(3, 5000):
            lD, _, _ = Dstar(k, k, n_log2, eps)
            if lD is not None and lD > c * log2(k / eps):
                kc = k
                break
        out.append(kc)
        check(kc is not None and kc <= 6 * c * log2(n_log2) + 40, f"S4 crossover too large n=2^{n_log2} c={c}: {kc}")
    print(f"    log2 n = 2^{int(log2(n_log2))}: loglog n = {log2(n_log2):.0f}, crossover k for c=3: {out[0]}, c=10: {out[1]};"
          f" Theorem D's range k <= (log n)^(1/4) = {n_log2 ** 0.25:.0f}")
print("PASS" if FAILS == 0 else f"FAIL ({FAILS})")
