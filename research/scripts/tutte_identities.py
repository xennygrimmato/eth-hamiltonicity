"""Exact checks of the identities used in research/tutte-plane.md, sections 1-3.

  I1  Tutte by subset expansion == Tutte by deletion-contraction (multigraphs, loops)
  I2  T(x,y) = (x-1)^{-k(G)} (y-1)^{-n} Z((x-1)(y-1), y-1)          (FK representation)
  I3  Z(q,v) = sum_{c:V->[q]} prod_e (1 + v[c_u=c_v])  for integer q >= 1   (local colouring sum)
  I4  #F_q-flows on A = q^{|A|-n+k(A)}  (q = 2,3,5 and GF(4));  and
      q^{m-n} Z(q,v) = sum_{F_q flows f of G} (q+v)^{#zero} v^{#nonzero}   (local flow sum)
  I5  forest indicator: [z^{|S|-|X|}] det(L_H + z diag(2-deg_H)) = 2^{c(H)} [H forest]
  I6  line formulas: T(x,1)=sum_F (x-1)^{r(E)-|F|}, T(1,y)=sum_{A: k(A)=k(G)} (y-1)^{|A|-r(E)},
      T(1,1)=#maximal forests, T(2,1)=#forests, T(1,2)=#connected spanning (connected G),
      H_1: T = y^m (y-1)^{-r(E)},  chromatic: P(G,l) = (-1)^{r(E)} l^{k(G)} T(1-l,0),
      flow: F(G,l) = (-1)^{m-r(E)} T(0,1-l)
  I7  every exceptional point of Jaeger-Vertigan-Welsh lies on an integer hyperbola H_q, q in {1,2,3,4}
  I8  hyperbola interpolation count: T is determined by T|H_1..H_N iff N >= 1 + max_t #{i: c_{i,i+t} free}
      (checked: number of unknowns per diagonal = min(r, nullity)+1 on random graphs)
Prints PASS/FAIL.
"""
import random, itertools, cmath
from fractions import Fraction
from tutte_lib import *

def det_poly_z(M):
    """determinant of a matrix whose entries are polynomials in z (dict deg->Fraction), by
    evaluation at deg+1 points and Lagrange interpolation (exact)."""
    n = len(M)
    if n == 0:
        return {0: Fraction(1)}
    D = n + 1
    pts = list(range(D + 1))
    vals = []
    for z in pts:
        A = [[sum(Fraction(c) * z ** d for d, c in e.items()) for e in row] for row in M]
        vals.append(det_Q(A))
    # interpolate
    coeffs = [Fraction(0)] * (D + 1)
    for i, xi in enumerate(pts):
        num = [Fraction(1)]; den = Fraction(1)
        for j, xj in enumerate(pts):
            if j == i:
                continue
            num = [Fraction(0)] + num
            for k in range(len(num) - 1):
                num[k] -= xj * num[k + 1]
            den *= (xi - xj)
        for k in range(len(num)):
            coeffs[k] += vals[i] * num[k] / den
    return {d: c for d, c in enumerate(coeffs) if c}

def det_Q(A):
    A = [row[:] for row in A]; n = len(A); d = Fraction(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]
            if f:
                A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return d

def is_forest(n, X):
    return ncomp(n, X) == n - len(X)

def main(seed=1):
    rng = random.Random(seed)
    C = Checker("tutte_identities")
    graphs = []
    for _ in range(25):
        n = rng.randint(2, 6); m = rng.randint(0, 8)
        E = [(rng.randrange(n), rng.randrange(n)) for _ in range(m)]      # multigraph + loops
        graphs.append((n, E))
    simple = []
    for _ in range(25):
        n = rng.randint(3, 7); m = rng.randint(n - 1, min(10, n * (n - 1) // 2))
        simple.append((n, rand_graph(n, m, rng)))
    # I1
    for n, E in graphs + simple:
        C.check(tutte_subset(n, E) == tutte_dc(n, E), f"I1 {n} {E}")
    # I2
    for n, E in graphs + simple:
        for _ in range(3):
            x = Fraction(rng.randint(-7, 7), rng.randint(1, 4)); y = Fraction(rng.randint(-7, 7), rng.randint(1, 4))
            if x == 1 or y == 1:
                continue
            k = ncomp(n, E)
            lhs = tutte_eval(n, E, x, y)
            rhs = potts_eval(n, E, (x - 1) * (y - 1), y - 1) / ((x - 1) ** k * (y - 1) ** n)
            C.check(lhs == rhs, f"I2 {n} {E} {x} {y}")
    # I3
    for n, E in simple[:12]:
        for q in (1, 2, 3):
            for v in (-2, -1, 1, 3):
                C.check(potts_eval(n, E, q, v) == colour_sum(n, E, q, v), f"I3 q={q}")
    # I4
    for n, E in simple[:10]:
        E = E[:8]
        for q in (2, 3, 4, 5):
            if q ** len(E) > 400000:
                continue
            for _, A in itertools.islice(subsets(E), 0, None, 7):
                C.check(flow_count(n, A, q) == q ** (len(A) - n + ncomp(n, A)), f"I4a q={q}")
            for v in (-1, 2):
                C.check(flow_sum(n, E, q, v) == Fraction(q) ** (len(E) - n) * potts_eval(n, E, q, v), f"I4b q={q}")
    # I5 forest indicator
    for n, E in simple + [(n, [e for e in E if e[0] != e[1]]) for n, E in graphs]:
        S = list(range(n)); deg = [0] * n
        for a, b in E:
            deg[a] += 1; deg[b] += 1
        M = [[{} for _ in S] for _ in S]
        for a, b in E:
            for (i, j, c) in ((a, a, 1), (b, b, 1), (a, b, -1), (b, a, -1)):
                M[i][j][0] = M[i][j].get(0, 0) + c
        for i in S:
            M[i][i][1] = M[i][i].get(1, 0) + (2 - deg[i])
        D = det_poly_z(M)
        e = n - len(E)
        val = D.get(e, 0) if e >= 0 else 0
        target = 2 ** ncomp(n, E) if is_forest(n, E) else 0
        C.check(val == target, f"I5 {n} {E}: {val} vs {target}")
    # I6
    for n, E in simple:
        k = ncomp(n, E); rE = n - k
        R = rank_gen(n, E)
        forests = [A for _, A in subsets(E) if is_forest(n, A)]
        xs = Fraction(rng.randint(-5, 5), 3)
        C.check(tutte_eval(n, E, xs, 1) == sum((xs - 1) ** (rE - len(F)) for F in forests), "I6 y=1")
        ys = Fraction(rng.randint(-5, 5), 3)
        conn = [A for _, A in subsets(E) if ncomp(n, A) == k]
        C.check(tutte_eval(n, E, 1, ys) == sum((ys - 1) ** (len(A) - rE) for A in conn), "I6 x=1")
        C.check(tutte_eval(n, E, 1, 1) == sum(1 for F in forests if len(F) == rE), "I6 (1,1)")
        C.check(tutte_eval(n, E, 2, 1) == len(forests), "I6 (2,1)")
        if k == 1:
            C.check(tutte_eval(n, E, 1, 2) == len(conn), "I6 (1,2)")
        yv = Fraction(rng.randint(2, 9), rng.randint(1, 3))
        if yv != 1:
            C.check(tutte_eval(n, E, 1 + 1 / (yv - 1), yv) == yv ** len(E) * (yv - 1) ** (-rE), "I6 H1")
        for lam in (1, 2, 3, 4):
            chrom = sum(1 for c in itertools.product(range(lam), repeat=n) if all(c[a] != c[b] for a, b in E))
            C.check(chrom == (-1) ** rE * lam ** k * tutte_eval(n, E, 1 - lam, 0), "I6 chromatic")
        for lam in (2, 3):
            if lam ** len(E) > 300000:
                continue
            nz = 0
            for f in itertools.product(range(1, lam), repeat=len(E)):
                bal = [0] * n
                for (a, b), fe in zip(E, f):
                    bal[a] = (bal[a] + fe) % lam; bal[b] = (bal[b] - fe) % lam
                nz += all(x == 0 for x in bal)
            C.check(nz == (-1) ** (len(E) - rE) * tutte_eval(n, E, 0, 1 - lam), "I6 flow poly")
    # I7 JVW exceptional points
    j = cmath.exp(2j * cmath.pi / 3)
    pts = [(1, 1), (-1, -1), (0, -1), (-1, 0), (1j, -1j), (-1j, 1j), (j, j * j), (j * j, j)]
    for (x, y) in pts:
        q = (x - 1) * (y - 1)
        on = any(abs(q - qq) < 1e-12 for qq in (1, 2, 3, 4)) or (x == 1 and y == 1)
        C.check(on, f"I7 {x},{y} q={q}")
    # I8 unknowns per diagonal of T in coordinates (s=(x-1)(y-1), t=y-1): c_{ij} u^i v^j = s^i v^{j-i}
    for n, E in simple:
        R = rank_gen(n, E); rE = n - ncomp(n, E); nul = len(E) - rE
        diag = {}
        for (i, jj) in R:
            diag.setdefault(jj - i, set()).add(i)
        mx = max(len(s) for s in diag.values())
        C.check(mx <= min(rE, nul) + 1, "I8 support per diagonal")
        # reconstruct T from H_1..H_N with N = min(rE,nul)+1: solve Vandermonde per diagonal
        N = min(rE, nul) + 1
        ok = True
        for t in range(-rE, nul + 1):
            idx = [i for i in range(0, rE + 1) if 0 <= i + t <= nul]
            if not idx:
                continue
            # data: for q=1..N, value of sum_i q^i c_{i,i+t}  (coefficient of v^t in T|H_q)
            data = [sum(q ** i * R.get((i, i + t), 0) for i in idx) for q in range(1, N + 1)]
            if len(idx) > N:
                ok = False; break
            A = [[Fraction(q) ** i for i in idx] for q in range(1, N + 1)]
            sol = solve_ls(A, data)
            ok &= all(sol[a] == R.get((i, i + t), 0) for a, i in enumerate(idx))
        C.check(ok, "I8 reconstruction from min(r,nullity)+1 hyperbolas")
    return C.done()

def solve_ls(A, b):
    """solve A x = b (A has full column rank), exact."""
    m, k = len(A), len(A[0])
    M = [[Fraction(x) for x in row] + [Fraction(bb)] for row, bb in zip(A, b)]
    r = 0; piv = []
    for c in range(k):
        p = next((i for i in range(r, m) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    x = [Fraction(0)] * k
    for i, c in enumerate(piv):
        x[c] = M[i][k]
    return x

if __name__ == "__main__":
    import sys
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
