#!/usr/bin/env python3
"""Rank of the three-point vertex at exact levels, for larger classes (one evaluation at y = 0).

V(s_a, s_d, T) = P_T(y = 0) = det [[0, +-binom(i+j,j), [i in T1]], [-+binom(i+j,i), 0, binom(r,i)], [[r in J_a], binom(r,j), 0]]
(rows I_a, I_d, T2; columns J_a, J_d, T1).  For every level m in the given range: number of symbols T of
energy 2m by size, the number that have size <= n1+n2, and the rank of the block  (Sigma1 x Sigma2) x {T at level m}.
    vertex0.py n1 e1 n2 e2 mlo mhi
"""
import sys, time, numpy as np
from psi_build import symbols, tables, P0
from factored import _evalP, arrays, nm
n1, e1, n2, e2, mlo, mhi = map(int, sys.argv[1:7])
S1, S2 = symbols(n1, e1), symbols(n2, e2)
d1, d2 = len(S1), len(S2)
Ia, Ja = arrays(S1, n1); Id, Jd = arrays(S2, n2)
print(f"classes ({n1},{e1}) d1={d1}, ({n2},{e2}) d2={d2}, D={d1*d2}; middle level m* = {(e1+e2)//2}")
print("  m | p(m) | #T of size <= n1+n2 | #T that split as a+d | rank of the level-m block")
def pnum(m):
    q = [1] + [0] * m
    for k in range(1, m + 1):
        for j in range(k, m + 1): q[j] += q[j - k]
    return q[m]
set1 = set(S1); set2 = set(S2)
for m in range(mlo, mhi + 1):
    Ts = []
    for t in range(0, n1 + n2 + 1):
        Ts += [(t, s) for s in symbols(t, 2 * m)]
    nT = len(Ts)
    if nT == 0:
        continue
    tm = max(1, max(t for t, _ in Ts))
    T1 = np.zeros((nT, tm), dtype=np.int64); T2 = np.zeros((nT, tm), dtype=np.int64); tsz = np.zeros(nT, dtype=np.int64)
    for k, (t, s) in enumerate(Ts):
        tsz[k] = t; T1[k, :t] = s[0]; T2[k, :t] = s[1]
    mx = max([max(s[0] + s[1]) for s in S1 if n1] + [max(s[0] + s[1]) for s in S2 if n2] + [max(s[0] + s[1]) for (t, s) in Ts if t] + [0]) + 2
    B, C = tables(mx, 0, P0)
    out = np.empty((d1 * d2, nT), dtype=np.int64)
    t0 = time.time()
    _evalP(Ia, Ja, Id, Jd, n1, n2, T1, T2, tsz, B, C, P0, out)
    # symbols of full size that are disjoint unions of an element of Sigma1 and one of Sigma2
    nsplit = 0
    if m == (e1 + e2) // 2:
        import itertools
        for (t, s) in Ts:
            if t != n1 + n2: continue
            ok = False
            for A1 in itertools.combinations(s[0], n1):
                for A2 in itertools.combinations(s[1], n1):
                    if (A1, A2) in set1 and (tuple(x for x in s[0] if x not in A1), tuple(x for x in s[1] if x not in A2)) in set2:
                        ok = True; break
                if ok: break
            nsplit += ok
    r = nm(out).rank()
    print(f"{m:3d} | {pnum(m):6d} | {nT:6d} | {nsplit if m == (e1+e2)//2 else '-':>6} | {r:6d}   ({time.time()-t0:.0f}s)", flush=True)
