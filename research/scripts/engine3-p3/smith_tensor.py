# 2-adic Smith invariants (mod 2^P) of the flattening of the deformed packet tensor
#   P_g(Y_g, X_g ; X_g') = prod_{x in g} l_{Y_x}( (W(T) X)_x ),  l_0(z)=1-z, l_1(z)=z,
# across the split ((Y_g, X_g) | X_g'), for D.1's Cauchy kernel at T = t + alpha*zeta, v_2(t)=i.
# g = row/column slots with bit_i = 0 (these are the crossing pairs at node t), g' = the rest.
# Output: number of invariants with valuation < p, for p = 1..P, versus the D.1 mode-monomial count
# (monomials in the kernel-block Smith modes of total weight < p, degree <= |g|).
import sys, itertools
import numpy as np
from fractions import Fraction

P = 30; MOD = 1 << P
def v2(n):
    n = abs(int(n))
    if n == 0: return 10**9
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c
def inv_odd(o):
    return pow(int(o) % MOD, -1, MOD)
def frac_mod(q):  # q Fraction with odd denominator -> residue mod 2^P
    assert q.denominator % 2 == 1
    return (q.numerator % MOD) * inv_odd(q.denominator) % MOD

a = int(sys.argv[1]) if len(sys.argv) > 1 else 3
i = int(sys.argv[2]) if len(sys.argv) > 2 else 0
zeta = 1
L = 2**a; alpha = 2**(a+1); t = 2**i; T = Fraction(t + alpha*zeta)
S = list(range(-L, L))
Cp0 = Fraction(1)
for s in S:
    if s != 0: Cp0 *= (0 - s)
def W(x, y):
    d = y - x; num = Fraction(1)
    for s in S:
        if s != d: num *= (T - s)
    return num / Cp0
g  = [x for x in range(L) if (x >> i) & 1 == 0]   # row slots of the group
gl = [y for y in range(L) if (y >> i) & 1 == 1]   # column slots in the SAME group (bits differ)
gp = [y for y in range(L) if (y >> i) & 1 == 0]   # crossing column slots (bits equal)
m = len(g)
Wm = [[frac_mod(W(x, y)) for y in range(L)] for x in range(L)]  # all entries 2-adic integers (Lemma tensor-integrality)
# local part loc[x][Xg], cross part cr[x][Xg']
Xg_all  = np.array(list(itertools.product([0,1], repeat=m)), dtype=np.int64)   # 2^m x m
loc = np.zeros((m, 2**m), dtype=np.int64); cr = np.zeros((m, 2**m), dtype=np.int64)
for r, x in enumerate(g):
    wl = np.array([Wm[x][y] for y in gl], dtype=np.int64); wc = np.array([Wm[x][y] for y in gp], dtype=np.int64)
    # sums of up to m terms each < 2^30: fits in int64
    loc[r] = (Xg_all @ wl) % MOD
    cr[r]  = (Xg_all @ wc) % MOD
# Build A[(Yg, Xg), Xg'] = prod_r l_{Y_r}(loc[r][Xg] + cr[r][Xg'])
rows = []
for Y in itertools.product([0,1], repeat=m):
    prod = np.ones((2**m, 2**m), dtype=np.int64)
    for r in range(m):
        z = (loc[r][:, None] + cr[r][None, :]) % MOD
        f = z if Y[r] == 1 else (1 - z) % MOD
        prod = (prod * f) % MOD   # both < 2^30 -> product < 2^60 OK
    rows.append(prod)
A = np.concatenate(rows, axis=0)  # (2^m * 2^m) x 2^m
A = A.T.copy()                    # 2^m x 2^{2m}: fewer rows, many columns
nr, nc = A.shape
print(f"L={L} a={a} node t={t} (i={i}) zeta={zeta}: |g|={m}, flattening {nc} x {nr} (transposed to {nr} x {nc}), mod 2^{P}")
# 2-adic Smith elimination
invariants = []
active_r = list(range(nr)); active_c = np.ones(nc, dtype=bool)
Awork = A.copy()
while active_r and active_c.any():
    sub = Awork[np.ix_(active_r, np.where(active_c)[0])]
    if not sub.any(): break
    # minimal valuation entry
    nz = sub != 0
    vals = np.full(sub.shape, 10**9, dtype=np.int64)
    # compute valuations vectorised: trailing zeros
    s = sub[nz].astype(np.int64)
    tz = np.log2((s & -s).astype(np.float64)).astype(np.int64)
    vals[nz] = tz
    k = np.unravel_index(np.argmin(vals), vals.shape)
    v = int(vals[k]); pr = active_r[k[0]]; pc = np.where(active_c)[0][k[1]]
    invariants.append(v)
    piv = int(Awork[pr, pc]); o = piv >> v; oinv = inv_odd(o)
    rowv = (Awork[pr, :] * oinv) % MOD            # pivot row scaled: pivot entry becomes 2^v
    colv = (Awork[:, pc] >> v)                    # exact: all entries have valuation >= v
    # A <- A - colv (x) rowv   (mod 2^P); products: colv < 2^(P-v), rowv < 2^P -> < 2^(2P-v) fits int64 for P=30
    Awork = (Awork - (colv[:, None] * rowv[None, :]) % MOD) % MOD
    active_r.remove(pr); active_c[pc] = False
invariants.sort()
print("tensor Smith valuations (< P only):", [v for v in invariants if v < P], " count:", len(invariants), "of max rank", min(nr, nc))
# D.1-style monomial count from the kernel block's Smith modes (computed as in smith_kernel.py)
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
from math import lcm
B = [[W(x, y) for y in gp] for x in g]
den = 1
for row in B:
    for e in row: den = lcm(den, e.denominator)
kk = v2(den)
snf = smith_normal_form(Matrix([[int(e*den) for e in row] for row in B]), domain=ZZ)
wk = sorted(v2(snf[j, j]) - kk for j in range(m) if snf[j, j] != 0)
print("kernel cross-block Smith valuations (mode weights):", wk)
def count_monomials(ws, p, maxdeg):
    # number of exponent tuples beta with sum w_k beta_k < p and sum beta_k <= maxdeg
    from functools import lru_cache
    @lru_cache(None)
    def f(idx, budget, deg):
        if idx == len(ws): return 1
        tot = 0; b = 0
        while b * ws[idx] < budget and b <= deg:
            tot += f(idx+1, budget - b*ws[idx], deg - b); b += 1
        return tot
    return f(0, p, maxdeg)
print(" p : #tensor invariants with val<p | #mode monomials (D.1 bookkeeping, deg<=|g|) | 2^{|g'|} brute force")
for p in list(range(2, P+1, 2)):
    nt = sum(1 for v in invariants if v < p)
    print(f"{p:3d}: {nt:5d} | {count_monomials(wk, p, m):6d} | {2**len(gp)}")
