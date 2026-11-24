"""y2 checks: small exact verifications of Lemmas 2, 3 and the sanity examples in notebook.md.
Run: python3 checks.py   (sympy only; a few seconds)."""
import itertools, random
import sympy as sp

random.seed(1)
y, dl, T = sp.symbols('y delta T')


def ryser(n):
    X = sp.Matrix(n, n, lambda i, j: sp.Symbol(f'x{i}{j}'))
    xs = list(X)
    roots = []
    for e in itertools.product([0, 1], repeat=n):
        sgn = (-1) ** (n + sum(e))
        roots.append(sp.expand(sgn * sp.prod([sum(X[i, j] * e[j] for j in range(n)) for i in range(n)])))
    return X, xs, roots


def norm(roots):
    return sp.expand(sp.prod([y - r for r in roots]))


for n in (2, 3):
    X, xs, roots = ryser(n)
    D = len(roots)
    per = sp.expand(X.per())
    assert sp.expand(sum(roots) - per) == 0
    N = norm(roots)
    P = sp.Poly(N, y)
    # Lemma 2(a): coefficient of y^{D-1} is -S
    assert sp.expand(P.coeff_monomial(y ** (D - 1)) + per) == 0
    # Lemma 2(b): border extraction ((-delta)^D N(x,-1/delta) - 1)/delta -> S
    G = sp.expand(sp.cancel(((-dl) ** D * N.subs(y, -1 / dl) - 1) / dl))
    assert sp.expand(G.subs(dl, 0) - per) == 0
    # Lemma 2(c): homogeneity extraction: coefficient of eps^n in N(eps x, 1) is -S
    eps = sp.Symbol('eps')
    Ne = sp.expand(N.subs({v: eps * v for v in xs}, simultaneous=True).subs(y, 1))
    assert sp.expand(sp.Poly(Ne, eps).coeff_monomial(eps ** n) + per) == 0
    # span of the roots
    polys = [sp.Poly(r, *xs) for r in roots]
    mons = sorted({m for p in polys for m in p.monoms()})
    M = sp.Matrix([[p.coeff_monomial(m) for m in mons] for p in polys])
    print(flush=True); print(f'n={n}: D={D}, dim span{{g_e}} = {M.rank()}  (Lemma 2 checks pass)')

    # Lemma 3 (cofactor lemma): Q = N*H, recover S from Q and H by one division
    if n == 2:
        H = sp.expand((y ** 3 + xs[0] * y + 7) * (xs[1] ** 2 - y * xs[2] + 1))
        Q = sp.expand(N * H)
        ratio = sp.cancel((-dl) ** D * Q.subs(y, -1 / dl) / H.subs(y, -1 / dl))
        G2 = sp.expand(sp.cancel((ratio - 1) / dl))
        assert sp.expand(G2.subs(dl, 0) - per) == 0
        print('   Lemma 3 (one exact division, border limit) recovers S exactly: pass')

# Sanity example (a): char 2 Knapsack norm is a subspace (Moore) polynomial
x1, x2, x3 = sp.symbols('x1 x2 x3')
xsK = [x1, x2, x3]
for p in (2, 3):
    knap = sp.prod([y - sum(c * v for c, v in zip(e, xsK)) for e in itertools.product([0, 1], repeat=3)])
    # subspace polynomial of V = F_p-span(x1,x2,x3) via P_{V+Fp v}(y) = prod_{c in F_p} P_V(y - c v)
    # = P_V(y)^p - P_V(v)^{p-1} P_V(y)  (linearised), computed with O(log p) ops per generator
    PV = y
    for v in xsK:
        PV = sp.expand(PV ** p - PV.subs(y, v) ** (p - 1) * PV)
    full = sp.prod([y - sum(c * v for c, v in zip(e, xsK)) for e in itertools.product(range(p), repeat=3)])
    assert sp.Poly(sp.expand(full - PV), y, *xsK, modulus=p).is_zero
    q, r = sp.div(sp.Poly(PV, y, *xsK, modulus=p), sp.Poly(sp.expand(knap), y, *xsK, modulus=p))
    assert r.is_zero
    eq = sp.Poly(sp.expand(PV - knap), y, *xsK, modulus=p).is_zero
    print(f'char {p}: Knapsack norm (n=3) divides the Moore polynomial of span(x1,x2,x3); equal: {eq}')

# Sanity example (b): cyclic norm prod_j (y - sum_{i<=d} x_i zeta^{ij}) = det(y - Phi(C)) with C the M x M shift,
# and = Res_T(T^M - 1, y - Phi(T)) up to sign, computable by powering the d x d companion matrix of y - Phi(T).
M, d = 8, 2
xc = sp.symbols('c0:%d' % (d + 1))
Phi = sum(xc[i] * T ** i for i in range(d + 1))
zeta = sp.exp(2 * sp.pi * sp.I / M)
prodform = sp.prod([y - Phi.subs(T, zeta ** j) for j in range(M)])
res = sp.resultant(T ** M - 1, y - Phi, T)
vals = {xc[0]: sp.Rational(2, 3), xc[1]: sp.Rational(-1, 5), xc[2]: sp.Rational(3, 7), y: sp.Rational(5, 11)}
lhs = sp.N(prodform.subs(vals), 30)
rhs = sp.N(res.subs(vals), 30)
assert abs(sp.N(lhs - rhs * (-1) ** 0, 30)) < 1e-20 or abs(sp.N(lhs + rhs, 30)) < 1e-20
# companion-power formula: Res = lc^M * det(C_P^M - I) with P = y - Phi as polynomial in T (lc = -c_d), d x d matrix
Pd = sp.Poly(y - Phi, T)
lc = Pd.LC()
coeffs = [c / lc for c in Pd.all_coeffs()[1:]]  # monic: T^d + a_{d-1} T^{d-1} + ... + a_0
Cm = sp.zeros(d, d)
for i in range(1, d):
    Cm[i, i - 1] = 1
for i in range(d):
    Cm[i, d - 1] = -coeffs[d - 1 - i]
Cv = Cm.subs(vals)
Pw = Cv
for _ in range(3):  # M = 2^3: three squarings
    Pw = Pw * Pw
comp = sp.nsimplify(lc.subs(vals) ** M * (Pw - sp.eye(d)).det())
assert abs(sp.N(comp - lhs, 30)) < 1e-20 or abs(sp.N(comp + lhs, 30)) < 1e-20
print(f'cyclic norm M={M}, d={d}: product = +-Res = +-lc^M det(C^M - I) (3 squarings of a {d}x{d} matrix): pass;'
      f' its polynomial roots span <= d+1 = {d+1} dims')
print('all checks passed')
