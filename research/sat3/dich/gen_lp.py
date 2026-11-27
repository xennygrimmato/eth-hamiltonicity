"""Generic label LP: unknowns delta(S), S a nonempty subset of n points.
Constraints: 0 on singletons, monotone, submodular on intersecting sets (elemental), delta = W on flat sets,
optional sound hull closure, optional tripod lower bounds.  The geometry is supplied by callbacks."""
import itertools
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog

def solve(n, flatW, target, sense="max", closure=None, lower=None):
    """flatW(mask) -> mean width or None; closure(mask) -> mask of points in the hull; lower(mask) -> float or None"""
    full = (1 << n) - 1
    lb = np.zeros(full); ub = np.full(full, np.inf)
    for m in range(1, full + 1):
        if m & (m - 1) == 0: ub[m-1] = 0.0; continue
        w = flatW(m)
        if w is not None: lb[m-1] = ub[m-1] = w
        elif lower is not None:
            l = lower(m)
            if l is not None: lb[m-1] = l
    rows, cols, vals = [], [], []; nr = 0
    er, ec, ev = [], [], []; ne = 0
    for m in range(1, full + 1):
        out = [i for i in range(n) if not m >> i & 1]
        cl = closure(m) if (closure is not None and m & (m - 1)) else m
        for x in out:
            mx = m | 1 << x
            if cl >> x & 1:
                er += [ne, ne]; ec += [mx-1, m-1]; ev += [1.0, -1.0]; ne += 1
            else:
                rows += [nr, nr]; cols += [m-1, mx-1]; vals += [1.0, -1.0]; nr += 1
        for x, y in itertools.combinations(out, 2):
            mx, my = m | 1 << x, m | 1 << y
            rows += [nr] * 4; cols += [(mx | my) - 1, m - 1, mx - 1, my - 1]; vals += [1.0, 1.0, -1.0, -1.0]; nr += 1
    A = coo_matrix((vals, (rows, cols)), shape=(nr, full)).tocsr()
    Ae = coo_matrix((ev, (er, ec)), shape=(ne, full)).tocsr() if ne else None
    c = np.zeros(full); c[target - 1] = -1.0 if sense == "max" else 1.0
    res = linprog(c, A_ub=A, b_ub=np.zeros(nr), A_eq=Ae, b_eq=np.zeros(ne) if ne else None,
                  bounds=list(zip(lb, ub)), method="highs")
    if res.status != 0: return None, res
    return (-res.fun if sense == "max" else res.fun), res
