"""Exact implementation of Prop. B.2 (crossing identity) of the VP != VNP paper, App. B.3.

Psi(X; s_a,s_b,s_c,s_d) = det M(X), M as in App. B.3. Coefficients obtained by exact evaluation at
X = 0..Theta (integer Bareiss determinants) and exact Newton interpolation.
Checks: deg <= Theta, Psi(1) = eps * matching, flattening ranks of Psi_N vs (N+1)P(N) bounds.
Usage: python3 crossing.py n1 e1 n2 e2
"""
import sys, itertools
from fractions import Fraction
from math import comb

def symbols(n, e):
    """all (I,J), |I|=|J|=n, sum_{I}(2i+1)+sum_J(2j+1) = e"""
    out = []
    maxl = e // 2 + 1
    def subsets(k, maxsum):
        # k-subsets of N with sum(2i+1) <= maxsum, returned with their energies
        res = []
        for S in itertools.combinations(range(maxl), k):
            en = sum(2 * i + 1 for i in S)
            if en <= maxsum:
                res.append((S, en))
        return res
    subs = subsets(n, e)
    for I, ei in subs:
        for J, ej in subs:
            if ei + ej == e:
                out.append((I, J))
    return out

def Bv(r, n, y):  # coefficient of t^n in (1+t)^r/(1+y t)^{r+1}
    return sum(comb(r, k) * comb(r + n - k, n - k) * (-y) ** (n - k) for k in range(0, min(r, n) + 1))

def Cv(r, n, y):  # coefficient of t^n in (1+y t)^r/(1+t)^{r+1}
    return sum(comb(r, k) * y ** k * comb(r + n - k, n - k) * (-1) ** (n - k) for k in range(0, min(r, n) + 1))

def det_int(M):
    """Bareiss fraction-free determinant of integer matrix (list of lists)"""
    M = [row[:] for row in M]
    n = len(M)
    if n == 0:
        return 1
    sign = 1
    prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if M[i][k] != 0), None)
            if sw is None:
                return 0
            M[k], M[sw] = M[sw], M[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]

def matrix(X, sa, sb, sc, sd):
    y = X * X
    Ia, Ja = sa; Ib, Jb = sb; Ic, Jc = sc; Id, Jd = sd
    rows = [('a', i) for i in Ia] + [('d', i) for i in Id] + [('c', i) for i in Ic] + [('b', i) for i in Ib]
    cols = [('a', j) for j in Ja] + [('d', j) for j in Jd] + [('c', j) for j in Jc] + [('b', j) for j in Jb]
    def ent(p, i, q, j):
        d = 1 if i == j else 0
        if p == 'a':
            return {'a': 0, 'd': Cv(i, j, y), 'c': d * X ** (2 * i + 1), 'b': (y - 1) * X ** (2 * i + 1) * Bv(i, j, y)}[q]
        if p == 'd':
            return {'a': -Cv(j, i, y), 'd': 0, 'c': X ** (2 * j + 1) * Bv(j, i, y), 'b': -d * X ** (2 * i + 1)}[q]
        if p == 'c':
            return {'a': -d * X ** (2 * i + 1), 'd': -X ** (2 * i + 1) * Bv(i, j, y), 'c': 0, 'b': -(y - 1) * Cv(i, j, y)}[q]
        if p == 'b':
            return {'a': -(y - 1) * X ** (2 * j + 1) * Bv(j, i, y), 'd': d * X ** (2 * i + 1), 'c': (y - 1) * Cv(j, i, y), 'b': 0}[q]
    return [[ent(p, i, q, j) for (q, j) in cols] for (p, i) in rows]

def interpolate(vals):
    """values at X=0..D -> integer coefficient list (exact, Newton)"""
    D = len(vals) - 1
    dd = [Fraction(v) for v in vals]
    coef_newton = [dd[0]]
    for k in range(1, D + 1):
        dd = [(dd[i + 1] - dd[i]) / k for i in range(len(dd) - 1)]
        coef_newton.append(dd[0])
    # convert Newton basis prod_{m<k}(X-m) to monomials
    poly = [Fraction(0)] * (D + 1)
    basis = [Fraction(1)]
    for k in range(D + 1):
        for i, b in enumerate(basis):
            poly[i] += coef_newton[k] * b
        nb = [Fraction(0)] * (len(basis) + 1)
        for i, b in enumerate(basis):
            nb[i + 1] += b
            nb[i] -= k * b
        basis = nb
    assert all(p.denominator == 1 for p in poly)
    return [int(p) for p in poly]

def rank_modp(rows, p=(1 << 61) - 1):
    M = [[x % p for x in r] for r in rows]
    if not M:
        return 0
    n, m = len(M), len(M[0])
    r = 0
    for c in range(m):
        piv = next((i for i in range(r, n) if M[i][c]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(n):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
        if r == n:
            break
    return r

def rank_Q(rows):
    return max(rank_modp(rows, (1 << 61) - 1), rank_modp(rows, (1 << 31) - 1))

def P_count(E):
    """number of symbols (any size) with energy <= E"""
    # count pairs of subsets (I,J), |I|=|J|, by DP over levels: f[k][en] = #subsets size k energy en
    L = E // 2 + 1
    f = {}
    f = [[0] * (E + 1) for _ in range(L + 2)]
    f[0][0] = 1
    for i in range(L):
        w = 2 * i + 1
        for k in range(L, -1, -1):
            for en in range(E, w - 1, -1):
                f[k + 1][en] += f[k][en - w]
    tot = 0
    for k in range(L + 1):
        for e1 in range(E + 1):
            if f[k][e1]:
                for e2 in range(E + 1 - e1):
                    tot += f[k][e1] * f[k][e2]
    return tot

def compute(n1, e1, n2, e2, verbose=True):
    S1, S2 = symbols(n1, e1), symbols(n2, e2)
    Th = 2 * (e1 + e2)
    Q1, Q2 = len(S1), len(S2)
    coeffs = {}
    for sa in S1:
        for sc in S1:
            for sb in S2:
                for sd in S2:
                    vals = [det_int(matrix(X, sa, sb, sc, sd)) for X in range(Th + 1)]
                    co = interpolate(vals)
                    coeffs[(sa, sb, sc, sd)] = co
    # degree check via X = Theta+1 extra evaluation
    import random
    for key in random.sample(list(coeffs), min(20, len(coeffs))):
        X = Th + 3
        v = det_int(matrix(X, *key))
        assert v == sum(c * X ** k for k, c in enumerate(coeffs[key])), "degree > Theta"
    # value at X=1: matching (with c,d renamed by swapping I,J)
    eps = None
    for (sa, sb, sc, sd), co in coeffs.items():
        v = sum(co)
        match = (sc == (sa[1], sa[0])) and (sd == (sb[1], sb[0]))
        if match:
            if eps is None:
                eps = v
            assert v == eps and abs(v) == 1
        else:
            assert v == 0
    # flattening ranks
    res = []
    for N in range(Th + 1):
        def flat(rowp, colp):
            idx = {'a': S1, 'b': S2, 'c': S1, 'd': S2}
            R = list(itertools.product(idx[rowp[0]], idx[rowp[1]]))
            C = list(itertools.product(idx[colp[0]], idx[colp[1]]))
            rows = []
            for r in R:
                row = []
                for c in C:
                    s = {rowp[0]: r[0], rowp[1]: r[1], colp[0]: c[0], colp[1]: c[1]}
                    row.append(coeffs[(s['a'], s['b'], s['c'], s['d'])][N])
                rows.append(row)
            return rank_Q(rows)
        if all(coeffs[k][N] == 0 for k in coeffs):
            res.append((N, 0, 0, 0))
            continue
        r_adbc = flat('ad', 'bc'); r_abcd = flat('ab', 'cd'); r_acbd = flat('ac', 'bd')
        res.append((N, r_adbc, r_abcd, r_acbd))
    if verbose:
        print(f"n1={n1} e1={e1} n2={n2} e2={e2}  |S1|={Q1} |S2|={Q2} Theta={Th} eps={eps}")
        print(" N  rk(ad|bc) bound(N+1)P(N) | rk(ab|cd) bound | rk(ac|bd)")
        for N, r1, r2, r3 in res:
            if r1 or r2:
                b1 = (N + 1) * P_count(N); b2 = (Th - N + 1) * P_count(Th - N)
                assert r1 <= b1 and r2 <= b2
                print(f"{N:3d} {r1:6d} {b1:10d} | {r2:6d} {b2:10d} | {r3:6d}")
    return Q1, Q2, Th, res, coeffs

if __name__ == '__main__':
    a = list(map(int, sys.argv[1:5]))
    compute(*a)
