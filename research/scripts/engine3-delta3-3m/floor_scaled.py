"""floor_scaled.py -- the finite three-merge criterion at larger alphabets N0 = 2^m0 without enumeration [C + R]:
one bit-scaled orientation (every bit of edge e split as in o** = (1,1,1,1,1,-1,1,-1,1), the three-merge flattening
certificate) gives a box role g(T) for all three merges at once; the CVZ roles give 9 m0 - 1.5 log2 T per merge (over C);
the role-assignment bound of floor_assign.py then bounds V_tot from below for every T and every shape.
Reports, for each m0, the largest T for which rho < 1/2 (V_tot < 4.5 m0) is still NOT refuted by these roles."""
import numpy as np
from lib3m import *
from floor_assign import lb
ostar = (1, 1, 1, 1, 1, -1, 1, -1, 1)
def box(m0, T):
    x = {k: np.zeros((1, 3)) for k in 'rcd'}; y = {k: np.zeros((1, 3)) for k in 'rcd'}
    for (u, v), o in zip(edges, ostar):
        a, b = (u, v) if o == 1 else (v, u)
        for k, gf in MER.items(): x[k][0, gf(a)] += m0; y[k][0, gf(b)] += m0
    t = np.array([9.0 * m0 - np.log2(T)])
    return [ginv(Mg(legs8(x[k], y[k])), t)[0] for k in 'rcd']
for m0 in range(1, 9):
    out = []; open_T = []
    for T in range(2, 2 ** m0 + 3):
        lt = np.log2(T); g = box(m0, T)
        roles = [list((9 * m0 - 1.5 * lt) * np.eye(3)[k]) for k in range(3)] + [g]
        v = lb(roles, T)[0] if T <= 8 else min(g)          # for T > 8 only the box (pigeonhole) part is used
        tot = v + 1.5 * lt
        if tot < 4.5 * m0 - 1e-9: open_T.append(T)
        if T in (2, 3, 4, 2 ** m0): out.append(f'T={T}: box {np.round(g, 3).tolist()} V_tot>={tot:.3f}')
    print(f'm0 = {m0} (N0 = {2**m0}, rho<1/2 needs V_tot < {4.5*m0}): ' + '; '.join(out) +
          f'  -> T NOT refuted: {open_T if open_T else "none (refuted for every T)"}', flush=True)
