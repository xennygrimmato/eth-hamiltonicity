#!/usr/bin/env python3
"""Exact toy check: OpenAI's replacement-form / measurement / Hermite engine
(ETH paper, Sections 2.3-2.7 and 4; github.com/openai/math, family 378) applied to
RYSER's formula for the permanent.

    per(A) = sum_{x in {0,1}^n} prod_i (A x)_i * prod_j (2 x_j - 1)

Factors: n row factors (scope = support of row i, X-degree 1) and n sign factors
(scope {j}). Total X-degree 2n, incidences M = nnz(A) + n.

Pipeline (all exact rationals):
  1. Auxiliary space B = ([r]x[r])^Q, swaps Pi_s, W0 = 1/2 sum (I - Pi_s), V0 = prod Pi_s,
     f = Lagrange interpolant of (-1)^j on an interval I of R integers, M0 = V0 f(W0),
     computed in the group algebra of (Z/2)^Q.
  2. Exceptional product eigenvectors psi (j notin I) = measurement rows;
     check  I - M0 = sum_exc kappa_psi psi psi^T  (so (I-M0) zeta is a function of C zeta).
  3. Rows  P_u(T)[w] = delta_uw - M0[u,w] + M0[u,w] * prod_{s in E_uw} (1 - T/s).
  4. Random schedules a_v, d_f in [r]^Q; labels u(f,v) = (a_v, d_f); copies.
  5. H(T) = sum_x prod_f Phi_f(replacement forms at T):  H(0) = per(A), deg H <= 2n(R-1).
  6. At each t in [Q]: H(t) = sum over measurement tuples of prod_g (group sums)  [separation].
  7. Taylor jets H(t+z) mod z^J from restricted sums Z_{t,E,U} (inclusion-exclusion over
     fixed Boolean substitutions X = 1_U), each computed by group separation.
  8. Hermite interpolation from the jets at t = 1..Q recovers H(0) = per(A).
Prints PASS/FAIL per check.  No randomness beyond a seeded RNG.
"""
import itertools, random, sys
from fractions import Fraction as Fr

# ---------------- univariate polynomials (lists of Fractions, low degree first) -------------
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pmul(a, b, J=None):
    if not a or not b: return []
    n = len(a) + len(b) - 1
    if J is not None: n = min(n, J)
    out = [Fr(0)] * n
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b):
            if i + j >= n: break
            out[i + j] += x * y
    return out
def pscale(a, c): return [c * x for x in a]
def peval(a, t):
    s = Fr(0)
    for x in reversed(a): s = s * t + x
    return s
def pshift(a, t, J):
    """coefficients of a(t+z) in z, truncated mod z^J"""
    out = [Fr(0)] * J
    # binomial expansion
    from math import comb
    for i, c in enumerate(a):
        if c == 0: continue
        for k in range(min(i, J - 1) + 1):
            out[k] += c * comb(i, k) * Fr(t) ** (i - k)
    return out

def interp(xs, ys):
    """Lagrange interpolation -> coefficient list"""
    n = len(xs); res = [Fr(0)] * n
    for i in range(n):
        num = [Fr(1)]; den = Fr(1)
        for j in range(n):
            if j != i:
                num = pmul(num, [Fr(-xs[j]), Fr(1)]); den *= (xs[i] - xs[j])
        res = padd(res, pscale(num, ys[i] / den))
    return res

def solve(Arows, b):
    """exact least-structure solve of an overdetermined consistent system; returns x or None"""
    m = len(Arows); n = len(Arows[0])
    M = [list(Arows[i]) + [b[i]] for i in range(m)]
    piv = []; row = 0
    for col in range(n):
        p = next((i for i in range(row, m) if M[i][col] != 0), None)
        if p is None: continue
        M[row], M[p] = M[p], M[row]
        inv = 1 / M[row][col]; M[row] = [x * inv for x in M[row]]
        for i in range(m):
            if i != row and M[i][col] != 0:
                f = M[i][col]; M[i] = [x - f * y for x, y in zip(M[i], M[row])]
        piv.append(col); row += 1
    for i in range(row, m):
        if M[i][n] != 0: return None  # inconsistent
    if len(piv) < n: return None      # underdetermined
    x = [Fr(0)] * n
    for i, col in enumerate(piv): x[col] = M[i][n]
    return x

# ---------------- the auxiliary construction -------------------------------------------------
def build(r, Q, R):
    p = Fr(r - 1, 2 * r)
    A0 = int((Q * p - Fr(R - 1, 2)) // 1)
    A0 = max(0, min(A0, Q - R + 1))
    I = list(range(A0, A0 + R))
    fpoly = interp(I, [Fr((-1) ** j) for j in I])          # deg <= R-1, f(j) = (-1)^j on I
    # group algebra of (Z/2)^Q : dict frozenset -> Fr ;  W0 = Q/2 * 1 - 1/2 sum_s pi_s
    def gmul(x, y):
        out = {}
        for S, a in x.items():
            for T_, b in y.items():
                U = S ^ T_; out[U] = out.get(U, 0) + a * b
        return {k: v for k, v in out.items() if v != 0}
    W0 = {frozenset(): Fr(Q, 2)}
    for s in range(Q): W0[frozenset([s])] = Fr(-1, 2)
    fW = {}
    for c in reversed(fpoly):                               # Horner
        fW = gmul(fW, W0) if fW else {}
        fW[frozenset()] = fW.get(frozenset(), 0) + c
        fW = {k: v for k, v in fW.items() if v != 0}
    full = frozenset(range(Q))
    M0g = gmul({full: Fr(1)}, fW)                            # V0 f(W0)
    labels = list(itertools.product(itertools.product(range(r), range(r)), repeat=Q))
    index = {u: i for i, u in enumerate(labels)}
    def apply(S, u):
        return tuple((d, a) if s in S else (a, d) for s, (a, d) in enumerate(u))
    def M0row(u):
        row = {}
        for S, c in M0g.items():
            w = apply(S, u); row[w] = row.get(w, 0) + c
        return {w: c for w, c in row.items() if c != 0}
    # per-position eigenvectors of the swap on [r]x[r]
    pos = []
    for a in range(r):
        pos.append(({(a, a): 1}, +1))
    for a in range(r):
        for b in range(a + 1, r):
            pos.append(({(a, b): 1, (b, a): 1}, +1))
            pos.append(({(a, b): 1, (b, a): -1}, -1))
    exc = []  # (psi dict over labels, kappa)
    for choice in itertools.product(range(len(pos)), repeat=Q):
        j = sum(1 for c in choice if pos[c][1] == -1)
        if j in I: continue
        psi = {}
        for u in itertools.product(*[list(pos[c][0].items()) for c in choice]):
            lab = tuple(k for k, _ in u); val = 1
            for _, v in u: val *= v
            psi[lab] = val
        fj = peval(fpoly, Fr(j))
        kappa = (1 - (-1) ** j * fj) / len(psi)               # |psi|^2 = support size
        exc.append((psi, kappa))
    return dict(r=r, Q=Q, R=R, I=I, fpoly=fpoly, M0row=M0row, labels=labels, exc=exc, M0g=M0g)

def check_eigen(B, ntest=40, rng=None):
    """I - M0 == sum_exc kappa psi psi^T  on sampled rows (all columns)"""
    ok = True
    labs = B['labels']
    rows = labs if len(labs) <= ntest else rng.sample(labs, ntest)
    for u in rows:
        row = B['M0row'](u)
        lhs = {w: -c for w, c in row.items()}; lhs[u] = lhs.get(u, 0) + 1
        rhs = {}
        for psi, k in B['exc']:
            pu = psi.get(u, 0)
            if pu == 0: continue
            for w, pw in psi.items():
                rhs[w] = rhs.get(w, 0) + k * pu * pw
        keys = set(lhs) | set(rhs)
        if any(lhs.get(w, 0) != rhs.get(w, 0) for w in keys): ok = False; break
    return ok

def Prow(B, u):
    """P_u(T) as dict w -> polynomial in T (degree <= R-1)"""
    out = {}
    for w, c in B['M0row'](u).items():
        E = [s + 1 for s in range(B['Q']) if w[s][0] != u[s][1]]   # a_w(s) != d_u(s); points are s+1
        phi = [Fr(1)]
        for s in E: phi = pmul(phi, [Fr(1), Fr(-1, s)])
        out[w] = padd(out.get(w, []), pscale(padd(phi, [Fr(-1)]), c))
    out[u] = padd(out.get(u, []), [Fr(1)])
    return {w: p for w, p in out.items() if any(x != 0 for x in p)}

# ---------------- the instance ---------------------------------------------------------------
def permanent(A):
    n = len(A); s = 0
    for sig in itertools.permutations(range(n)):
        p = 1
        for i in range(n): p *= A[i][sig[i]]
        s += p
    return s

def run(n, r, Q, R, density, seed):
    rng = random.Random(seed)
    while True:
        A = [[1 if rng.random() < density else 0 for _ in range(n)] for _ in range(n)]
        if all(any(row) for row in A): break
    per = permanent(A)
    B = build(r, Q, R)
    res = {}
    res['eigen I-M0 = sum kappa psi psi^T'] = check_eigen(B, rng=rng)
    # factors: ('row', i) scope supp(row i);  ('sgn', j) scope {j}
    factors = [('row', i, [j for j in range(n) if A[i][j]]) for i in range(n)] + [('sgn', j, [j]) for j in range(n)]
    a = {v: tuple(rng.randrange(r) for _ in range(Q)) for v in range(n)}
    d = {k: tuple(rng.randrange(r) for _ in range(Q)) for k in range(len(factors))}
    copies = {}; occ = {}; where = {}   # occ[(c, w)] = v ; where[(k, v)] = (c, u)
    for k, (_, _, scope) in enumerate(factors):
        for v in scope:
            u = tuple((a[v][s], d[k][s]) for s in range(Q))
            c = copies.get(u, 0); copies[u] = c + 1
            occ[(c, u)] = v; where[(k, v)] = (c, u)
    h = max(copies.values())
    # coefficient polynomials coef[(k,v)][v'] (T)
    Pcache = {}
    coef = {}
    for (k, v), (c, u) in where.items():
        if u not in Pcache: Pcache[u] = Prow(B, u)
        cv = {}
        for w, poly in Pcache[u].items():
            if (c, w) in occ:
                vv = occ[(c, w)]; cv[vv] = padd(cv.get(vv, []), poly)
        coef[(k, v)] = cv
    Dg = 2 * n * (R - 1)

    def factor_value(k, inputs, J=None):
        """inputs: dict v -> value (Fraction) or truncated poly (list) if J given"""
        kind, idx, scope = factors[k]
        if J is None:
            if kind == 'row': return sum(A[idx][v] * inputs[v] for v in scope)
            return 2 * inputs[idx] - 1
        if kind == 'row':
            s = []
            for v in scope: s = padd(s, pscale(inputs[v], Fr(A[idx][v])))
            return (s + [Fr(0)] * J)[:J]
        x = pscale(inputs[idx], Fr(2)); x = padd(x, [Fr(-1)]); return (x + [Fr(0)] * J)[:J]

    def H_direct(t):
        tot = Fr(0)
        for x in itertools.product((0, 1), repeat=n):
            prod = Fr(1)
            for k, (_, _, scope) in enumerate(factors):
                inp = {v: sum(peval(p, Fr(t)) * x[vv] for vv, p in coef[(k, v)].items()) for v in scope}
                prod *= factor_value(k, inp)
                if prod == 0: break
            tot += prod
        return tot

    res['H(0) = per(A)'] = (H_direct(0) == per)
    pts = list(range(-(Dg // 2) - 1, Dg - Dg // 2 + 2))       # Dg+3 points
    vals = [H_direct(t) for t in pts]
    Hpoly = interp(pts[:Dg + 1], vals[:Dg + 1])
    res['deg H <= 2n(R-1)'] = all(peval(Hpoly, Fr(t)) == v for t, v in zip(pts, vals))

    # ---------- separation at t in [Q] ----------
    def separated(t, J=None, E=frozenset(), U=frozenset()):
        """sum over x with x_E = 1 of prod_f Phi_f( <P(t),x> + <Delta P(z), 1_U> ), via groups.
        Returns Fraction (J None) or truncated poly."""
        s = t - 1
        groups = {g: [v for v in range(n) if a[v][s] == g] for g in range(r)}
        assigned = {g: [k for k in range(len(factors)) if d[k][s] == g] for g in range(r)}
        # measurement keys: (copy c, psi index); y_{h}[c, psi] = sum_{w in copy c, occupant in group h} psi_w x
        exc = B['exc']
        # constant corrections from U (fixed Boolean substitution), only when J given
        corr = {}
        if J is not None:
            for kv, cv in coef.items():
                tot = [Fr(0)] * J
                for vv, p in cv.items():
                    if vv in U:
                        dp = pshift(p, t, J); dp[0] -= peval(p, Fr(t)); tot = padd(tot, dp)
                corr[kv] = tot[:J]
        def meas(g, xg):
            y = []
            for c in range(h):
                for pi, (psi, _) in enumerate(exc):
                    val = 0
                    for w, pw in psi.items():
                        vv = occ.get((c, w))
                        if vv is not None and a[vv][s] == g: val += pw * xg[vv]
                    y.append(val)
            return tuple(y)
        tables = {}
        for g in range(r):
            vs = groups[g]; lst = []
            for bits in itertools.product((0, 1), repeat=len(vs)):
                xg = dict(zip(vs, bits))
                if any(xg[v] != 1 for v in vs if v in E): continue
                lst.append((xg, meas(g, xg)))
            tables[g] = lst
        nm = h * len(exc)
        Ys = {g: sorted(set(y for _, y in tables[g])) for g in range(r)}
        total = Fr(0) if J is None else [Fr(0)] * J
        for ytuple in itertools.product(*[Ys[g] for g in range(r)]):
            ysum = [sum(ytuple[g][i] for g in range(r)) for i in range(nm)]   # <psi, zeta^(c)>
            prod_all = Fr(1) if J is None else [Fr(1)] + [Fr(0)] * (J - 1)
            for g in range(r):
                Bg = Fr(0) if J is None else [Fr(0)] * J
                for xg, yg in tables[g]:
                    if yg != ytuple[g]: continue
                    pr = Fr(1) if J is None else [Fr(1)] + [Fr(0)] * (J - 1)
                    for k in assigned[g]:
                        scope = factors[k][2]; inp = {}
                        for v in scope:
                            c, u = where[(k, v)]
                            # measurement part: sum_psi kappa psi_u <psi, zeta^(c)>
                            val = Fr(0)
                            for pi, (psi, kap) in enumerate(exc):
                                pu = psi.get(u, 0)
                                if pu: val += kap * pu * ysum[c * len(exc) + pi]
                            # local part: sum_{w in copy c, a_w(t)=d_u(t)} M0[u,w] phi(t) zeta_w
                            for w, cM in B['M0row'](u).items():
                                if w[s][0] != u[s][1]: continue
                                vv = occ.get((c, w))
                                if vv is None: continue
                                Es = [q + 1 for q in range(Q) if w[q][0] != u[q][1]]
                                ph = Fr(1)
                                for q in Es: ph *= (1 - Fr(t, q))
                                val += cM * ph * xg[vv]
                            inp[v] = val if J is None else padd([val] + [Fr(0)] * (J - 1), corr[(k, v)])
                        fv = factor_value(k, inp, J)
                        pr = pr * fv if J is None else pmul(pr, fv, J)
                    Bg = Bg + pr if J is None else padd(Bg, pr)
                prod_all = prod_all * Bg if J is None else pmul(prod_all, Bg, J)
            total = total + prod_all if J is None else padd(total, prod_all)
        return total

    res['separation H(t) at t=1..Q'] = all(separated(t) == peval(Hpoly, Fr(t)) for t in range(1, Q + 1))

    # ---------- Taylor jets via restricted sums, then Hermite ----------
    J = Dg // Q + 1
    assert Q * J > Dg
    q = J - 1
    jets = {}
    for t in range(1, Q + 1):
        tot = [Fr(0)] * J
        for e in range(q + 1):
            for E in itertools.combinations(range(n), e):
                E = frozenset(E)
                for uu in range(len(E) + 1):
                    for U in itertools.combinations(sorted(E), uu):
                        Z = separated(t, J, E, frozenset(U))
                        tot = padd(tot, pscale(Z, Fr((-1) ** (len(E) - len(U)))))
        jets[t] = tot
    res['Taylor jets via restricted sums'] = all(jets[t] == pshift(Hpoly, t, J) for t in range(1, Q + 1))
    from math import comb
    rows, rhs = [], []
    for t in range(1, Q + 1):
        for k in range(J):
            rows.append([Fr(comb(i, k)) * Fr(t) ** (i - k) if i >= k else Fr(0) for i in range(Dg + 1)])
            rhs.append(jets[t][k])
    sol = solve(rows, rhs)
    res['Hermite recovery H(0) = per(A)'] = (sol is not None and sol[0] == per)
    # nontriviality: at t>=1 the forms really read other groups (through measurements)
    cross = 0
    for t in range(1, Q + 1):
        for (k, v), cv in coef.items():
            for vv, p in cv.items():
                if a[vv][t - 1] != d[k][t - 1] and peval(p, Fr(t)) != 0: cross += 1
    res['nontrivial: cross-group coefficients > 0'] = cross > 0
    # negative control: one Taylor coefficient fewer per point does not determine H
    rows2 = [rw for i, rw in enumerate(rows) if i % J != J - 1]; rhs2 = [x for i, x in enumerate(rhs) if i % J != J - 1]
    res['control: J-1 jets underdetermined'] = (Q * (J - 1) <= Dg) == (solve(rows2, rhs2) is None)
    info = dict(n=n, r=r, Q=Q, R=R, I=B['I'], D=(r * r) ** Q, nexc=len(B['exc']), h=h, cross=cross,
                H1=str(peval(Hpoly, Fr(1))),
                M=sum(len(f[2]) for f in factors), per=per, degH=Dg, J=J)
    return res, info

if __name__ == '__main__':
    configs = [(4, 2, 4, 2, 0.6, 1), (5, 2, 4, 2, 0.5, 2), (5, 2, 4, 2, 1.0, 3), (5, 3, 3, 2, 0.7, 7), (5, 2, 5, 3, 0.6, 5)]
    if len(sys.argv) > 1: configs = configs[:int(sys.argv[1])]
    allok = True
    for cfg in configs:
        res, info = run(*cfg)
        print('config n=%d r=%d Q=%d R=%d density=%.1f seed=%d' % cfg, info)
        for k, v in res.items():
            print('   %-40s %s' % (k, 'PASS' if v else 'FAIL')); allok &= v
        sys.stdout.flush()
    print('ALL PASS' if allok else 'SOME FAIL')
