#!/usr/bin/env python3
"""Rank of the three-point vertex  V(s_a, s_d, T) = [y^0] P_T  (rows (s_a,s_d) in the two classes, columns the
symbols T of energy <= 2m, |T| <= n1+n2), against the number of such T, and the rank of the piece Psi_2m.
    vertex_rank.py n1 e1 n2 e2 mmax
"""
import sys, numpy as np
from factored import build_PQ, nm, ranks_at
from psi_build import P0
n1, e1, n2, e2, mmax = map(int, sys.argv[1:6])
S1, S2, Ts, PPc, QQc = build_PQ(n1, e1, n2, e2, mmax)
print(f"classes ({n1},{e1}) d1={len(S1)}, ({n2},{e2}) d2={len(S2)}, full {len(S1)*len(S2)}")
print("  m | #T(E<=2m) by size | rank vertex (levels<=m) | rank vertex (level m only) | rank Psi_2m | #cols")
en = np.array([e for (e, t, s) in Ts]); sz = np.array([t for (e, t, s) in Ts])
for m in range(mmax + 1):
    sel = np.nonzero(en <= 2 * m)[0]
    sel1 = np.nonzero(en == 2 * m)[0]
    V = PPc[0][:, sel]
    r = nm(V).rank()
    r1 = nm(PPc[0][:, sel1]).rank() if len(sel1) else 0
    bysz = [int(((en <= 2 * m) & (sz == t)).sum()) for t in range(n1 + n2 + 1)]
    rr, rP, rQ, nc = ranks_at(Ts, PPc, QQc, m)
    print(f"{m:3d} | {len(sel):5d} {bysz} | {r:6d} | {r1:6d} | {rr:6d} | {nc}", flush=True)
