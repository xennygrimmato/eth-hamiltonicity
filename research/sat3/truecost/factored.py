#!/usr/bin/env python3
"""Ranks of Psi_N across ad|bc from the two-hub expansion of [AN] App. B.3, without building the 4-tensor.

    Psi(X) = sum_T  +-X^E(T)  P_T(s_a, s_d; y) Q_T(s_b, s_c; y)      (mod X^(2R), R arbitrary),
    P_T = det [[M1, F_{.,T1}], [F'_{T2,.}, 0]],   Q_T = det [[M2, G'_{.,T2}], [G_{T1,.}, 0]],

T = (T1, T2) a symbol.  Hence the ad|bc flattening of Psi_N (N = 2n) is  PP * J * QQ^t  where the columns of
PP are the coefficient vectors [y^k] P_T, the columns of QQ are [y^l] Q_T and J pairs (T,k) with
(T, n - E(T)/2 - k).  Everything mod a 31-bit prime.

    factored.py n1 e1 n2 e2 nmax      -> table of rank(Psi_2n), rank PP_n, rank QQ_n, #columns, for n <= nmax
"""
import sys, itertools, time
import numpy as np
from numba import njit, prange
import flint
from psi_build import symbols, tables, vander_inv, _det, P0


def all_symbols(Emax, tmax):
    """symbols T with |T| <= tmax and energy <= Emax, sorted by energy."""
    out = []
    for t in range(0, tmax + 1):
        for e in range(2 * t * t, Emax + 1, 2):
            for s in symbols(t, e):
                out.append((e, t, s))
    out.sort()
    return out


@njit(cache=True, parallel=True)
def _evalP(Ia, Ja, Id, Jd, n1, n2, T1, T2, tsz, B, C, p, out):
    """out[row=(a,d), T] = P_T at this y."""
    d1 = Ia.shape[0]; d2 = Id.shape[0]; nT = T1.shape[0]
    tm = T1.shape[1]
    for ia in prange(d1):
        M = np.empty((n1 + n2 + tm, n1 + n2 + tm), dtype=np.int64)
        for idd in range(d2):
            for it in range(nT):
                t = tsz[it]
                m = n1 + n2 + t
                for u in range(m):
                    for v in range(m):
                        M[u, v] = 0
                for u in range(n1):
                    i = Ia[ia, u]
                    for v in range(n2):
                        M[u, n1 + v] = C[i, Jd[idd, v]]
                    for v in range(t):
                        if T1[it, v] == i:
                            M[u, n1 + n2 + v] = 1
                for u in range(n2):
                    i = Id[idd, u]
                    for v in range(n1):
                        M[n1 + u, v] = (p - C[Ja[ia, v], i]) % p
                    for v in range(t):
                        M[n1 + u, n1 + n2 + v] = B[T1[it, v], i]
                for u in range(t):
                    r = T2[it, u]
                    for v in range(n1):
                        if Ja[ia, v] == r:
                            M[n1 + n2 + u, v] = 1
                    for v in range(n2):
                        M[n1 + n2 + u, n1 + v] = B[r, Jd[idd, v]]
                out[ia * d2 + idd, it] = _det(M, m, p)


@njit(cache=True, parallel=True)
def _evalQ(Ib, Jb, Ic, Jc, n1, n2, T1, T2, tsz, B, C, y, p, out):
    """out[row=(b,c), T] = Q_T at this y.  class 2 at b, class 1 at c."""
    d2 = Ib.shape[0]; d1 = Ic.shape[0]; nT = T1.shape[0]
    tm = T1.shape[1]
    ym1 = (y - 1) % p
    for ib in prange(d2):
        M = np.empty((n1 + n2 + tm, n1 + n2 + tm), dtype=np.int64)
        for ic in range(d1):
            for it in range(nT):
                t = tsz[it]
                m = n1 + n2 + t
                for u in range(m):
                    for v in range(m):
                        M[u, v] = 0
                # rows I_c (n1), I_b (n2), T1 (t) ; cols J_c (n1), J_b (n2), T2 (t)
                for u in range(n1):
                    i = Ic[ic, u]
                    for v in range(n2):
                        M[u, n1 + v] = (p - ym1 * C[i, Jb[ib, v]] % p) % p
                    for v in range(t):
                        if T2[it, v] == i:
                            M[u, n1 + n2 + v] = 1
                for u in range(n2):
                    i = Ib[ib, u]
                    for v in range(n1):
                        M[n1 + u, v] = ym1 * C[Jc[ic, v], i] % p
                    for v in range(t):
                        M[n1 + u, n1 + n2 + v] = ym1 * B[T2[it, v], i] % p
                for u in range(t):
                    r = T1[it, u]
                    for v in range(n1):
                        if Jc[ic, v] == r:
                            M[n1 + n2 + u, v] = 1
                    for v in range(n2):
                        M[n1 + n2 + u, n1 + v] = ym1 * B[r, Jb[ib, v]] % p
                out[ib * d1 + ic, it] = _det(M, m, p)


@njit(cache=True, parallel=True)
def _interp_low(vals, Vinv, p, out):
    """vals[t, x]; out[k, x] = sum_t Vinv[k,t] vals[t,x] for k < out.shape[0]."""
    K = vals.shape[0]
    kk = out.shape[0]
    n = vals.shape[1]
    for x in prange(n):
        for k in range(kk):
            acc = 0
            for t in range(K):
                acc = (acc + Vinv[k, t] * vals[t, x]) % p
            out[k, x] = acc


def arrays(S, n):
    d = len(S)
    return (np.array([s[0] for s in S], dtype=np.int64).reshape(d, n),
            np.array([s[1] for s in S], dtype=np.int64).reshape(d, n))


def build_PQ(n1, e1, n2, e2, nmax, p=P0, tmax=None, verbose=False):
    """returns S1, S2, Ts, PPc, QQc with PPc[k, row, T] = [y^k] P_T (k <= nmax), same for Q."""
    S1, S2 = symbols(n1, e1), symbols(n2, e2)
    d1, d2 = len(S1), len(S2)
    if tmax is None:
        tmax = n1 + n2
    Ts = all_symbols(2 * nmax, tmax)
    nT = len(Ts)
    tm = max(1, max(t for (_, t, _) in Ts))
    T1 = np.zeros((nT, tm), dtype=np.int64); T2 = np.zeros((nT, tm), dtype=np.int64)
    tsz = np.zeros(nT, dtype=np.int64)
    for k, (e, t, s) in enumerate(Ts):
        tsz[k] = t
        T1[k, :t] = s[0]; T2[k, :t] = s[1]
    Ia, Ja = arrays(S1, n1); Id, Jd = arrays(S2, n2)
    mxa = max([max(s[0] + s[1]) for s in S1 if n1] + [0]); mxd = max([max(s[0] + s[1]) for s in S2 if n2] + [0])
    mxT = max([max(s[0] + s[1]) for (_, t, s) in Ts if t] + [0])
    mx = max(mxa, mxd, mxT) + 2
    # degree bound in y
    degP = n1 * mxa + n2 * mxd + tm * mxd + 2
    degQ = n1 * mxa + n2 * mxd + tm * mxd + 2 * (n1 + n2 + tm) + 2
    K = max(degP, degQ) + 1
    pts = list(range(2, K + 2))
    vP = np.empty((K, d1 * d2 * nT), dtype=np.int64)
    vQ = np.empty((K, d1 * d2 * nT), dtype=np.int64)
    t0 = time.time()
    for t, y in enumerate(pts):
        B, C = tables(mx, y, p)
        o = np.empty((d1 * d2, nT), dtype=np.int64)
        _evalP(Ia, Ja, Id, Jd, n1, n2, T1, T2, tsz, B, C, p, o)
        vP[t] = o.reshape(-1)
        o2 = np.empty((d2 * d1, nT), dtype=np.int64)
        _evalQ(Id, Jd, Ia, Ja, n1, n2, T1, T2, tsz, B, C, y, p, o2)
        vQ[t] = o2.reshape(-1)
        if verbose and t % 20 == 0:
            print(f"   eval {t}/{K} {time.time()-t0:.1f}s", flush=True)
    Vinv = vander_inv(pts, p)
    PPc = np.empty((nmax + 1, d1 * d2 * nT), dtype=np.int64)
    QQc = np.empty((nmax + 1, d1 * d2 * nT), dtype=np.int64)
    _interp_low(vP, Vinv, p, PPc)
    _interp_low(vQ, Vinv, p, QQc)
    return S1, S2, Ts, PPc.reshape(nmax + 1, d1 * d2, nT), QQc.reshape(nmax + 1, d1 * d2, nT)


def nm(A, p=P0):
    A = np.ascontiguousarray(A)
    return flint.nmod_mat(A.shape[0], A.shape[1], A.reshape(-1).tolist(), p)


def columns(Ts, n):
    """index list of (T, k) with E(T)/2 + k <= n, and the partner permutation (T,k) -> (T, n - m_T - k)."""
    cols = []
    for it, (e, t, s) in enumerate(Ts):
        m = e // 2
        for k in range(0, n - m + 1):
            cols.append((it, k))
    idx = {c: i for i, c in enumerate(cols)}
    partner = [idx[(it, n - Ts[it][0] // 2 - k)] for (it, k) in cols]
    return cols, partner


def ranks_at(Ts, PPc, QQc, n, p=P0):
    cols, partner = columns(Ts, n)
    it = np.array([c[0] for c in cols]); kk = np.array([c[1] for c in cols])
    PP = PPc[kk, :, it].T            # rows x cols
    QQ = QQc[kk, :, it].T
    QJ = QQ[:, partner]
    Pm, Qm = nm(PP, p), nm(QJ, p)
    rP, rQ = Pm.rank(), Qm.rank()
    F = Pm * Qm.transpose()
    return F.rank(), rP, rQ, len(cols)


if __name__ == '__main__':
    n1, e1, n2, e2, nmax = map(int, sys.argv[1:6])
    t0 = time.time()
    S1, S2, Ts, PPc, QQc = build_PQ(n1, e1, n2, e2, nmax, verbose=True)
    print(f"classes ({n1},{e1}) d1={len(S1)}, ({n2},{e2}) d2={len(S2)}; {len(Ts)} symbols T up to energy {2*nmax}; {time.time()-t0:.1f}s")
    print("  N | rank ad|bc | rank PP  rank QQ | #columns sum_T (m_T+1)")
    for n in range(nmax + 1):
        r, rP, rQ, nc = ranks_at(Ts, PPc, QQc, n)
        print(f"{2*n:3d} | {r:8d} | {rP:7d} {rQ:7d} | {nc:7d}", flush=True)
