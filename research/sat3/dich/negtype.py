"""Is sqrt(rank) on Mat_mu(F_2) of negative type (a necessary condition for l1-embeddability)?  And the
five-point set W5 = {0, V, p1, p2, p3} of the diamond K_2(2) (already known not to be l1: hull notes)?

Translation-invariant d(a,b) = f(rk(a-b)) is of negative type iff the Walsh-Hadamard transform of a -> f(rk a)
is <= 0 at every nontrivial character.  The transform depends only on the rank of the character matrix.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

def rank_f2(rows):
    rows = list(rows); r = 0
    for bit in range(max(rows).bit_length() if rows and max(rows) else 0):
        piv = None
        for i in range(r, len(rows)):
            if rows[i] >> bit & 1: piv = i; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1: rows[i] ^= rows[r]
        r += 1
    return r

def wht(v):
    v = v.astype(float).copy(); h = 1; n = len(v)
    while h < n:
        v = v.reshape(-1, 2, h); a = v[:, 0, :] + v[:, 1, :]; b = v[:, 0, :] - v[:, 1, :]
        v = np.stack([a, b], axis=1).reshape(-1); h *= 2
    return v

for mu in (2, 3, 4):
    n = mu * mu
    rk = np.array([rank_f2([(x >> (mu * i)) & ((1 << mu) - 1) for i in range(mu)]) for x in range(1 << n)])
    for name, f in (("sqrt(rank)", np.sqrt), ("rank", lambda r: r.astype(float)), ("rank^(1/4)", lambda r: r ** 0.25)):
        F = wht(f(rk))
        by = {}
        for x in range(1, 1 << n): by.setdefault(int(rk[x]), set()).add(round(float(F[x]), 6))
        ok = all(max(s) <= 1e-9 for s in by.values())
        print(f"mu={mu} f={name:10s} transform by character rank: " + ", ".join(f"{r}: {sorted(s)}" for r, s in sorted(by.items())) + f"   negative type: {ok}")

# W5: pentagonal / hypermetric and cut-cone membership by LP
P = ["0", "V", "p1", "p2", "p3"]
def d(x, y):
    if x == y: return 0.0
    if {x, y} == {"0", "V"}: return math.sqrt(2)
    if x[0] == "p" and y[0] == "p": return math.sqrt(2)
    return 1.0
pairs = list(itertools.combinations(range(5), 2))
cuts = [m for m in range(1, 16)]
A = np.array([[1.0 if ((m >> i) & 1) != ((m >> j) & 1) else 0.0 for m in cuts] for i, j in pairs])
b = np.array([d(P[i], P[j]) for i, j in pairs])
res = linprog(np.zeros(len(cuts)), A_eq=A, b_eq=b, bounds=[(0, None)] * len(cuts), method="highs")
print("W5 in the cut cone (l1-embeddable):", res.status == 0)
res2 = linprog(np.ones(len(cuts)), A_ub=-A, b_ub=-b, bounds=[(0, None)] * len(cuts), method="highs")
print("W5: least total weight of cuts dominating d:", res2.fun, "  (label upper bound of the diamond: 3 - 1/sqrt2 =", 3 - 1/math.sqrt(2), ")")
