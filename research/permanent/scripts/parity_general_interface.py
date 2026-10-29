#!/usr/bin/env python3
"""General interface (Definition def:layout) versus the M0-template, for the SAME shared
measurement space, r = 2, full label space B = ({0,1}x{0,1})^Q, points t = 1..Q.

Measurement space: Lambda_J = span{ psi : j(psi) notin J } (product swap eigenvectors, j = number
of antisymmetric factors), J a set of eigen-levels; budget eps(J) = Pr_{Bin(Q,1/4)}[j notin J].

Row u (relabelled so a_u = 0^Q, d_u = 1_{E_u}) and degree bound deg P_u <= R-1:
 * TEMPLATE (any M0, commuting or not): exists lambda in Lambda with lambda_w = delta_{uw} for all
   w with |E_{u,w}| >= R   (E_{u,w} = {t : a_w(t) != d_u(t)}).
 * GENERAL interface: exist lambda_1..lambda_Q in Lambda such that for every w with |E_{u,w}| >= R
   the data ((lambda_t)_w - delta_{uw})_{t in E_{u,w}} lies in span{(t^k)_{t in E_{u,w}}: 1<=k<=R-1}
   (then P_u(T)_w is the interpolant; see parity-barrier.md section 5).
Both are linear feasibility problems, decided EXACTLY by rank computations over GF(2^31-1)
(all data are small integers; a GF(p) rank equals the rational rank unless p divides a minor,
so "infeasible mod p" could in principle be spurious; we re-check every infeasible verdict at a
second prime).
Output: for each J, the least R for which all rows are feasible, template vs general.
"""
import numpy as np, itertools, sys
from fractions import Fraction
from math import comb

PRIMES = (2147483647, 2147483629)

def rank_mod(M, p):
    M = np.array(M, dtype=np.int64) % p
    nr, nc = M.shape; r = 0
    for c in range(nc):
        if r == nr:
            break
        piv = np.nonzero(M[r:, c])[0]
        if piv.size == 0:
            continue
        i = r + piv[0]
        if i != r:
            M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        col = M[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if nzr.size:
            M[nzr] = (M[nzr] - (col[nzr, None] * M[r][None, :]) % p) % p
        r += 1
    return r

def feasible(A, b):
    for p in PRIMES:
        ra = rank_mod(A, p); rb = rank_mod(np.hstack([A, b[:, None]]), p)
        if ra == rb:
            return True
    return False

def local_basis():
    # coordinates of one position: index 2*a + d for (a,d); vectors and their sign
    e = np.eye(4, dtype=np.int64)
    return [(e[0], 0), (e[3], 0), (e[1] + e[2], 0), (e[1] - e[2], 1)]   # (vector, antisym flag)

def build(Q):
    D = 4**Q
    # coordinate index: digits base 4, position t (0-based) -> digit t ; digit = 2*a_t + d_t
    lb = local_basis()
    psis = []; levels = []
    for choice in itertools.product(range(4), repeat=Q):
        v = np.ones(1, dtype=np.int64); j = 0
        for t in range(Q - 1, -1, -1):          # kron order: position Q-1 most significant
            vec, s = lb[choice[t]]
            v = np.kron(v, vec); j += s
        psis.append(v); levels.append(j)
    Psi = np.array(psis).T        # D x D, column = psi
    lev = np.array(levels)
    a = np.zeros((D, Q), dtype=np.int64); d = np.zeros((D, Q), dtype=np.int64)
    for w in range(D):
        x = w
        for t in range(Q):
            dig = x % 4; x //= 4
            a[w, t] = dig // 2; d[w, t] = dig % 2
    return D, Psi, lev, a, d

def null_int(E, R):
    """integer basis of {y in Z^E : sum_t y_t t^k = 0, k=1..R-1} (exact)."""
    import sympy
    M = sympy.Matrix([[sympy.Integer(t)**k for t in E] for k in range(1, R)])
    if R == 1:
        return [np.eye(len(E), dtype=np.int64)[i] for i in range(len(E))]
    ns = M.nullspace()
    out = []
    for v in ns:
        den = sympy.ilcm(*[x.q for x in v])
        out.append(np.array([int(x * den) for x in v], dtype=np.int64))
    return out

_ncache = {}
def nullb(E, R):
    key = (tuple(E), R)
    if key not in _ncache:
        _ncache[key] = null_int(E, R)
    return _ncache[key]

def row_coord(Q, Eu):
    # u with a_u = 0, d_u(t) = 1 iff t in Eu (0-based positions)
    return sum((1 if t in Eu else 0) * 4**t for t in range(Q))

def template_ok(Q, D, B, a, d, Eu, R):
    u = row_coord(Q, Eu)
    du = d[u]
    far = [w for w in range(D) if np.sum(a[w] != du) >= R]
    if not far:
        return True
    A = B[far, :]; b = np.array([1 if w == u else 0 for w in far], dtype=np.int64)
    if B.shape[1] == 0:
        return not b.any()
    return feasible(A, b)

def general_ok(Q, D, B, a, d, Eu, R):
    u = row_coord(Q, Eu)
    du = d[u]; c = B.shape[1]
    rows = []; rhs = []
    for w in range(D):
        E = [t for t in range(Q) if a[w, t] != du[t]]
        if len(E) < R:
            continue
        pts = [t + 1 for t in E]          # evaluation points are 1..Q
        for y in nullb(pts, R):
            row = np.zeros(Q * c, dtype=np.int64)
            for yi, t in zip(y, E):
                row[t * c:(t + 1) * c] += yi * B[w]
            rows.append(row); rhs.append((1 if w == u else 0) * int(y.sum()))
    if not rows:
        return True
    A = np.array(rows); b = np.array(rhs, dtype=np.int64)
    if c == 0:
        return not b.any()
    return feasible(A, b)

def least_R(Q, D, B, a, d, checker):
    for R in range(1, Q + 1):
        ok = True
        for k in range(R, Q + 1):          # rows with |E_u| <= R-1 are trivially feasible
            for Eu in itertools.combinations(range(Q), k):
                if not checker(Q, D, B, a, d, set(Eu), R):
                    ok = False; break
            if not ok:
                break
        if ok:
            return R
    return Q + 1

def main(Qs):
    for Q in Qs:
        D, Psi, lev, a, d = build(Q)
        pm = [Fraction(comb(Q, j)) * Fraction(1, 4)**j * Fraction(3, 4)**(Q - j) for j in range(Q + 1)]
        Js = []
        for mask in range(1, 2**(Q + 1)):
            J = [j for j in range(Q + 1) if mask >> j & 1]
            Js.append(J)
        if Q >= 5:   # only level sets with eps <= 0.3 (small c), to keep time bounded
            Js = [J for J in Js if 1 - sum(pm[j] for j in J) <= Fraction(3, 10)]
        print(f"== Q={Q}, D={D}: least R (template, general) for each level set J ==")
        diffs = 0
        for J in Js:
            eps = 1 - sum(pm[j] for j in J)
            B = Psi[:, [i for i in range(D) if lev[i] not in J]]
            rt = least_R(Q, D, B, a, d, template_ok)
            rg = least_R(Q, D, B, a, d, general_ok)
            flag = "  <-- GENERAL BEATS TEMPLATE" if rg < rt else ""
            diffs += rg < rt
            print(f"J={J}  eps={float(eps):.5f}  c={B.shape[1]}  R_template={rt}  R_general={rg}{flag}")
            sys.stdout.flush()
        print(f"Q={Q}: level sets where the general interface needs smaller R: {diffs}")

if __name__ == "__main__":
    main([int(x) for x in sys.argv[1:]] or [2, 3, 4])
