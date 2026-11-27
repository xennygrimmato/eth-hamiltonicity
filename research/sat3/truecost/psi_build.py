#!/usr/bin/env python3
"""Fast exact construction (mod a 31-bit prime) of the crossing pieces Psi_N of [AN] Prop. B.2.

Psi(X; s_a, s_b, s_c, s_d) = det M is a polynomial in y = X^2 of degree <= Theta/2 = e1 + e2 (after
multiplying the rows of a, d by X and their columns by 1/X, every entry of M lies in Z[y]).  We evaluate
the determinant at Theta/2 + 2 values of y and interpolate.  Psi_N = coefficient of y^(N/2).

Index order of the returned tensor: coef[k, a, b, c, d], k = N/2.  Symbols at c, d are NOT renamed
(the renaming I <-> J of the paper is a permutation of the index set; no rank depends on it).

Used as a module by the other scripts; as a program it prints the seven flattening ranks:
    psi_build.py n1 e1 n2 e2 [prime]
"""
import sys, itertools, time
import numpy as np
from math import comb
from numba import njit, prange
import flint

P0 = 2147483629


def symbols(n, e):
    """all (I, J), |I| = |J| = n, sum(2i+1) + sum(2j+1) = e, sorted."""
    out = []
    if e % 2 or e < 2 * n * n:
        return out
    tot = (e - 2 * n) // 2
    by = {}
    for I in itertools.combinations(range(tot + 1), n):
        s = sum(I)
        if s <= tot:
            by.setdefault(s, []).append(I)
    for s, L in by.items():
        for J in by.get(tot - s, []):
            for I in L:
                out.append((I, J))
    return sorted(out)


def tables(mx, y, p):
    """B(r,n), C(r,n) for r, n < mx at the value y, mod p."""
    B = np.zeros((mx, mx), dtype=np.int64)
    C = np.zeros((mx, mx), dtype=np.int64)
    for r in range(mx):
        for n in range(mx):
            sb = 0
            sc = 0
            for k in range(0, min(r, n) + 1):
                m = n - k
                sb += comb(r, k) * comb(r + m, m) * pow(-y, m, p)
                sc += comb(r, k) * pow(y, k, p) * comb(r + m, m) * (-1) ** m
            B[r, n] = sb % p
            C[r, n] = sc % p
    return B, C


@njit(cache=True)
def _inv(a, p):
    # extended Euclid
    t, nt, r, nr = 0, 1, p, a % p
    while nr != 0:
        q = r // nr
        t, nt = nt, t - q * nt
        r, nr = nr, r - q * nr
    return t % p


@njit(cache=True)
def _det(M, m, p):
    det = 1
    for c in range(m):
        piv = -1
        for r in range(c, m):
            if M[r, c] != 0:
                piv = r
                break
        if piv < 0:
            return 0
        if piv != c:
            for k in range(c, m):
                tmp = M[c, k]; M[c, k] = M[piv, k]; M[piv, k] = tmp
            det = p - det
        det = det * M[c, c] % p
        inv = _inv(M[c, c], p)
        for r in range(c + 1, m):
            if M[r, c] != 0:
                f = M[r, c] * inv % p
                for k in range(c + 1, m):
                    M[r, k] = (M[r, k] - f * M[c, k]) % p
    return det % p


@njit(cache=True, parallel=True)
def _eval_all(I1, J1, I2, J2, n1, n2, B, C, y, p, out):
    """out[a,b,c,d] = det M at this y.  I1[s] = I-part of symbol s of class 1, etc."""
    d1 = I1.shape[0]
    d2 = I2.shape[0]
    m = 2 * (n1 + n2)
    mx = B.shape[0]
    ypow = np.empty(mx + 1, dtype=np.int64)
    ypow[0] = 1
    for i in range(1, mx + 1):
        ypow[i] = ypow[i - 1] * y % p
    ym1 = (y - 1) % p
    for ia in prange(d1):
        M = np.empty((m, m), dtype=np.int64)
        W = np.empty((m, m), dtype=np.int64)
        for id_ in range(d2):
            # block rows a (0..n1), d (n1..n1+n2): columns a, d fixed
            for ic in range(d1):
                for ib in range(d2):
                    # parties in order a, d, c, b ; offsets
                    oa = 0; od = n1; oc = n1 + n2; ob = 2 * n1 + n2
                    for u in range(m):
                        for v in range(m):
                            M[u, v] = 0
                    # rows a
                    for u in range(n1):
                        i = I1[ia, u]
                        for v in range(n2):   # ad : C(i,j)
                            M[oa + u, od + v] = C[i, J2[id_, v]]
                        for v in range(n1):   # ac : [i=j] y^(i+1)
                            if J1[ic, v] == i:
                                M[oa + u, oc + v] = ypow[i + 1]
                        for v in range(n2):   # ab : (y-1) y^(i+1) B(i,j)
                            M[oa + u, ob + v] = ym1 * ypow[i + 1] % p * B[i, J2[ib, v]] % p
                    # rows d
                    for u in range(n2):
                        i = I2[id_, u]
                        for v in range(n1):   # da : -C(j,i)
                            M[od + u, oa + v] = (p - C[J1[ia, v], i]) % p
                        for v in range(n1):   # dc : y^(j+1) B(j,i)
                            j = J1[ic, v]
                            M[od + u, oc + v] = ypow[j + 1] * B[j, i] % p
                        for v in range(n2):   # db : -[i=j] y^(i+1)
                            if J2[ib, v] == i:
                                M[od + u, ob + v] = (p - ypow[i + 1]) % p
                    # rows c
                    for u in range(n1):
                        i = I1[ic, u]
                        for v in range(n1):   # ca : -[i=j] y^i
                            if J1[ia, v] == i:
                                M[oc + u, oa + v] = (p - ypow[i]) % p
                        for v in range(n2):   # cd : -y^i B(i,j)
                            M[oc + u, od + v] = (p - ypow[i] * B[i, J2[id_, v]] % p) % p
                        for v in range(n2):   # cb : -(y-1) C(i,j)
                            M[oc + u, ob + v] = (p - ym1 * C[i, J2[ib, v]] % p) % p
                    # rows b
                    for u in range(n2):
                        i = I2[ib, u]
                        for v in range(n1):   # ba : -(y-1) y^j B(j,i)
                            j = J1[ia, v]
                            M[ob + u, oa + v] = (p - ym1 * ypow[j] % p * B[j, i] % p) % p
                        for v in range(n2):   # bd : [i=j] y^i
                            if J2[id_, v] == i:
                                M[ob + u, od + v] = ypow[i]
                        for v in range(n1):   # bc : (y-1) C(j,i)
                            M[ob + u, oc + v] = ym1 * C[J1[ic, v], i] % p
                    for u in range(m):
                        for v in range(m):
                            W[u, v] = M[u, v]
                    out[ia, ib, ic, id_] = _det(W, m, p)


@njit(cache=True, parallel=True)
def _interp(vals, Vinv, p, out):
    K = vals.shape[0]
    n = vals.shape[1]
    for x in prange(n):
        for k in range(K):
            acc = 0
            for t in range(K):
                acc = (acc + Vinv[k, t] * vals[t, x]) % p
            out[k, x] = acc


def vander_inv(pts, p):
    n = len(pts)
    A = flint.nmod_mat(n, n, [pow(x, k, p) for x in pts for k in range(n)], p)
    Ai = A.inv()
    return np.array([[int(Ai[i, j]) for j in range(n)] for i in range(n)], dtype=np.int64)


def build(n1, e1, n2, e2, p=P0, verbose=False):
    S1, S2 = symbols(n1, e1), symbols(n2, e2)
    assert S1 and S2
    d1, d2 = len(S1), len(S2)
    K = e1 + e2 + 2            # degree <= e1+e2 in y ; one extra point as a check
    mx = max(max(max(s[0] + s[1]) for s in S1 if s[0]) if n1 else 0,
             max(max(s[0] + s[1]) for s in S2 if s[0]) if n2 else 0) + 2
    I1 = np.array([s[0] for s in S1], dtype=np.int64).reshape(d1, n1)
    J1 = np.array([s[1] for s in S1], dtype=np.int64).reshape(d1, n1)
    I2 = np.array([s[0] for s in S2], dtype=np.int64).reshape(d2, n2)
    J2 = np.array([s[1] for s in S2], dtype=np.int64).reshape(d2, n2)
    vals = np.empty((K, d1 * d2 * d1 * d2), dtype=np.int64)
    pts = list(range(2, K + 2))
    t0 = time.time()
    for t, y in enumerate(pts):
        B, C = tables(mx, y, p)
        out = np.empty((d1, d2, d1, d2), dtype=np.int64)
        _eval_all(I1, J1, I2, J2, n1, n2, B, C, y, p, out)
        vals[t] = out.reshape(-1)
        if verbose and t % 10 == 0:
            print(f"  eval {t}/{K}  {time.time()-t0:.1f}s", flush=True)
    Vinv = vander_inv(pts, p)
    coef = np.empty_like(vals)
    _interp(vals, Vinv, p, coef)
    assert not coef[K - 1].any(), "degree exceeds Theta"
    return S1, S2, coef[:K - 1].reshape(K - 1, d1, d2, d1, d2)


def rank_mod(A, p=P0):
    A = np.ascontiguousarray(A)
    r, c = A.shape
    if r == 0 or c == 0:
        return 0
    return flint.nmod_mat(r, c, A.reshape(-1).tolist(), p).rank()


CUTS = ['a|bcd', 'b|acd', 'c|abd', 'd|abc', 'ab|cd', 'ad|bc', 'ac|bd']


def flattenings(T):
    d1, d2 = T.shape[0], T.shape[1]
    return {
        'a|bcd': T.reshape(d1, -1),
        'b|acd': T.transpose(1, 0, 2, 3).reshape(d2, -1),
        'c|abd': T.transpose(2, 0, 1, 3).reshape(d1, -1),
        'd|abc': T.transpose(3, 0, 1, 2).reshape(d2, -1),
        'ab|cd': T.reshape(d1 * d2, d1 * d2),
        'ad|bc': T.transpose(0, 3, 1, 2).reshape(d1 * d2, d2 * d1),
        'ac|bd': T.transpose(0, 2, 1, 3).reshape(d1 * d1, d2 * d2),
    }


def check_identity(S1, S2, coef, p=P0):
    tot = coef.sum(axis=0) % p
    swap = lambda s: (s[1], s[0])
    i1 = {s: k for k, s in enumerate(S1)}
    i2 = {s: k for k, s in enumerate(S2)}
    want = np.zeros_like(tot)
    for a, sa in enumerate(S1):
        for d, sd in enumerate(S2):
            want[a, i2[swap(sd)], i1[swap(sa)], d] = 1
    return bool((tot == want).all() or (tot == (p - want) % p).all())


def Pcount(E):
    M = E // 2
    q = [1] + [0] * M
    for k in range(1, M + 1):
        for m in range(k, M + 1):
            q[m] += q[m - k]
    return sum(q)


if __name__ == '__main__':
    n1, e1, n2, e2 = map(int, sys.argv[1:5])
    p = int(sys.argv[5]) if len(sys.argv) > 5 else P0
    t0 = time.time()
    S1, S2, coef = build(n1, e1, n2, e2, p, verbose=True)
    d1, d2 = len(S1), len(S2)
    Th = 2 * (e1 + e2)
    print(f"classes ({n1},{e1}) d1={d1}, ({n2},{e2}) d2={d2}, Theta={Th}, prime {p}; build {time.time()-t0:.1f}s")
    print("identity (a):", check_identity(S1, S2, coef, p))
    print("  N | " + " ".join(f"{c:>6}" for c in CUTS) + " | cert(c) cert(b)")
    for k in range(coef.shape[0]):
        T = coef[k]
        if not T.any():
            continue
        N = 2 * k
        fl = flattenings(T)
        rk = [rank_mod(fl[c], p) for c in CUTS]
        cc = (Th - N + 1) * Pcount(Th - N)
        cb = (N + 1) * Pcount(N)
        print(f"{N:3d} | " + " ".join(f"{r:6d}" for r in rk) + f" | {min(cc,d1*d2):6d} {min(cb,d1*d2):6d}", flush=True)
