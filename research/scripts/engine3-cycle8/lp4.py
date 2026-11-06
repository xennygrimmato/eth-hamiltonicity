"""lp4.py -- the 4-group flattening LP (K_4 bond structure) and its exact closed form.
Primal (cheapest K_4 network passing contraction M with group excesses n=(n_1..n_4), sum n = 0):
    d(n) = min sum_{i<j} e_ij  s.t.  e(delta S) >= |n_S| for every cut S|S^c (4 singletons + 3 pairs), e >= 0.
(For a labelling sigma: groups -> {X,Y} the inequality of M reads sum_{sigma=X} n <= e(sigma); both signs of every cut.)
Dual: max sum_S y_S |n_S|  s.t.  for every bond ij: sum_{S separating i,j} y_S <= 1, y >= 0.
We enumerate the dual vertices exactly (rational), giving d(n) = max_vertex <y,|n_S|>, and verify against linprog."""
import itertools, numpy as np
from fractions import Fraction
import sympy
from scipy.optimize import linprog

GR = 4
PAIRS = list(itertools.combinations(range(GR), 2))
CUTS = [(0,), (1,), (2,), (3,), (0, 1), (0, 2), (0, 3)]   # S with 0 in S for the 2|2 cuts
def sep(S, p): return (p[0] in S) != (p[1] in S)
Acut = np.array([[1 if sep(S, p) else 0 for p in PAIRS] for S in CUTS])  # 7 x 6

def nS(n): return [sum(n[i] for i in S) for S in CUTS]

def lp_value(n):
    b = [abs(x) for x in nS(n)]
    r = linprog(np.ones(6), A_ub=-Acut, b_ub=-np.array(b, float), bounds=[(0, None)] * 6, method='highs')
    return r.fun

def dual_vertices():
    # constraints of the dual polytope: Acut^T y <= 1 (6 rows), -y <= 0 (7 rows)
    M = sympy.Matrix.vstack(sympy.Matrix(Acut.T.tolist()), -sympy.eye(7))
    rhs = sympy.Matrix([1] * 6 + [0] * 7)
    verts = set()
    for rows in itertools.combinations(range(13), 7):
        A = M.extract(list(rows), list(range(7)))
        if A.det() == 0: continue
        y = A.LUsolve(rhs.extract(list(rows), [0]))
        if all(x >= 0 for x in y) and all(v <= 1 for v in (sympy.Matrix(Acut.T.tolist()) * y)):
            verts.add(tuple(y))
    return sorted(verts)

VERTS = None
def closed(n):
    global VERTS
    if VERTS is None: VERTS = dual_vertices()
    b = [abs(x) for x in nS(n)]
    return max(sum(Fraction(int(y.p), int(y.q)) * bb for y, bb in zip(v, b)) for v in VERTS)

if __name__ == '__main__':
    V = dual_vertices(); VERTS = V
    print(f"dual polytope of the 4-group LP: {len(V)} vertices; cuts order {CUTS}")
    for v in V: print("  y =", [str(x) for x in v])
    # nondominated vertices (as functionals of the nonnegative vector |n_S|)
    nd = [v for v in V if not any(w != v and all(a >= b for a, b in zip(w, v)) for w in V)]
    print(f"maximal (non-dominated) vertices: {len(nd)}")
    for v in nd: print("  y =", [str(x) for x in v])
    rng = np.random.default_rng(0); bad = 0
    for _ in range(3000):
        n = list(rng.integers(-7, 8, size=3)); n.append(-sum(n))
        if abs(float(closed(n)) - lp_value(n)) > 1e-7: bad += 1
    print("check closed form vs linprog on 3000 random n: mismatches =", bad)
