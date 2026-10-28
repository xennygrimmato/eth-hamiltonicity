"""Exact implementation of Appendix B (Anthropic, "A 2^{o(n)} time algorithm for 3-SAT"):
the ring V = Q[t_1, t_2, ...] graded by weight, the operators a[r] of display (47) via the
recursion (O2), the families a_mu (Lemma 10), b_mu, and the pieces A_s of (53).

Conventions.  A polynomial is a dict {partition (sorted tuple, descending): integer coefficient}.
nabla_{-k} f = t_k f,  nabla_k f = k d f/d t_k  (k >= 1).
a[r] for a monomial a = t^mu (parts listed in mu), by (O2) with a = t_n a':
    a[r] = sum_{l >= n} C(l-1, n-1) nabla_{-l} a'[r-l]  +  sum_{k >= 1} C(-k-1, n-1) a'[r+k] nabla_k,
with 1[r] = [r = 0] Id.  Differentiations are applied first in every term.
"""
import math
from functools import lru_cache
from collections import defaultdict


# ---------- partitions ----------
@lru_cache(maxsize=None)
def partitions(n, maxpart=None):
    """All partitions of n (descending tuples), parts <= maxpart."""
    if maxpart is None:
        maxpart = n
    if n == 0:
        return ((),)
    out = []
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            out.append((k,) + rest)
    return tuple(out)


@lru_cache(maxsize=None)
def p(n):
    return len(partitions(n)) if n >= 0 else 0


def gbinom(k, j):
    """C(k, j) = k(k-1)...(k-j+1)/j! for integer k, j >= 0; 0 for j < 0."""
    if j < 0:
        return 0
    num = 1
    for t in range(j):
        num *= (k - t)
    return num // math.factorial(j)


def add_part(sigma, l):
    return tuple(sorted(sigma + (l,), reverse=True))


def remove_part(sigma, k):
    """(count of k in sigma, sigma with one k removed) or (0, None)."""
    c = sigma.count(k)
    if c == 0:
        return 0, None
    lst = list(sigma)
    lst.remove(k)
    return c, tuple(lst)


def wt(sigma):
    return sum(sigma)


# ---------- the operators a[r] on monomials ----------
@lru_cache(maxsize=None)
def op_mono(mu, r, sigma):
    """(t^mu)[r] applied to t^sigma, as a dict partition -> integer coefficient (weight |sigma|+r)."""
    if not mu:
        return {sigma: 1} if r == 0 else {}
    n, rest = mu[0], mu[1:]
    E = wt(sigma)
    out = defaultdict(int)
    # multiplications nabla_{-l}, l >= n, after rest[r-l]; rest[r-l] on V_E is zero if E + r - l < 0
    for l in range(n, E + r + 1):
        c = gbinom(l - 1, n - 1)
        if c == 0:
            continue
        for tau, d in op_mono(rest, r - l, sigma).items():
            out[add_part(tau, l)] += c * d
    # differentiations nabla_k first (k must be a part of sigma), then rest[r+k]
    for k in set(sigma):
        cnt, sig2 = remove_part(sigma, k)
        c = gbinom(-k - 1, n - 1) * k * cnt
        for tau, d in op_mono(rest, r + k, sig2).items():
            out[tau] += c * d
    return {t: v for t, v in out.items() if v}


def op_poly(a, r, f):
    """a[r] f for polynomials a, f (dicts)."""
    out = defaultdict(int)
    for mu, ca in a.items():
        for sigma, cf in f.items():
            for tau, d in op_mono(mu, r, sigma).items():
                out[tau] += ca * cf * d
    return {t: v for t, v in out.items() if v}


# ---------- the families of Lemma 10 ----------
def poly_mul(pp, q):
    out = defaultdict(int)
    for a, x in pp.items():
        for b, y in q.items():
            out[tuple(sorted(a + b, reverse=True))] += x * y
    return {k: v for k, v in out.items() if v}


def y_poly(n):
    return {(j,): math.comb(n, j) for j in range(1, n + 1)}


@lru_cache(maxsize=None)
def a_fam(mu):
    """a^mu = prod_i (-1)^{mu_i - 1} y_{mu_i}."""
    pp = {(): 1}
    for n in mu:
        yn = {k: (-1) ** (n - 1) * v for k, v in y_poly(n).items()}
        pp = poly_mul(pp, yn)
    return pp


def z_mu(mu):
    z = 1
    for k in set(mu):
        c = mu.count(k)
        z *= k ** c * math.factorial(c)
    return z


def b_fam(mu):
    h = wt(mu)
    return {mu: math.factorial(h) // z_mu(mu)}


def angle(a, h, i):
    """a^<i> = sum_{h'} C(h'+h, i) abar_{h'}."""
    out = {}
    for mu, c in a.items():
        cc = c * math.comb(wt(mu) + h, i)
        if cc:
            out[mu] = cc
    return out


# ---------- the pieces ----------
def piece_tensor(h, s, labels=None, order="auto"):
    """A_s(x, y, u, v) = [t^{mu(u)}] Q_s(a_{mu(x)}, b_{mu(v)}) t^{mu(y)} for all x, v in `labels`
    (default: all partitions of h) and y, u over all partitions of h.  Returns (parts, labels, T)
    with T a dict (x, y, u, v) -> integer (indices into parts / labels).
    order = 'col' computes a^<i>[s-h+i] (b[h-s-i] f)  (display (48) as written: passes through V_{2h-s-i}),
    order = 'row' computes b[h-s-i] (a^<i>[s-h+i] f)  (exchanged: passes through V_{s+i}),
    'auto' picks the cheaper one.  Lemma 9(a) says both give the same tensor."""
    parts = partitions(h)
    if labels is None:
        labels = parts
    if order == "auto":
        order = "row" if s <= 0 else "col"
    idx = {q: i for i, q in enumerate(parts)}
    T = defaultdict(int)
    A = {x: a_fam(mu) for x, mu in enumerate(labels)}
    B = {v: b_fam(nu) for v, nu in enumerate(labels)}
    for i in range(0, 2 * h + 1):
        sign = (-1) ** i
        if order == "col":
            w = 2 * h - s - i
            if w < 0:
                continue
            # first b_v[h-s-i]: V_h -> V_w, then a_x^<i>[s-h+i]: V_w -> V_h
            first = {}
            for v in B:
                for y, eta in enumerate(parts):
                    g = op_poly(B[v], h - s - i, {eta: 1})
                    if g:
                        first[(y, v)] = g
            needed = set()
            for g in first.values():
                needed |= set(g)
            second = {}
            for x in A:
                ai = angle(A[x], h, i)
                for sg in needed:
                    g = op_poly(ai, s - h + i, {sg: 1})
                    for upart, d in g.items():
                        if upart in idx:
                            second.setdefault(sg, []).append((x, idx[upart], d))
            for (y, v), g in first.items():
                for sg, c1 in g.items():
                    for (x, u, d) in second.get(sg, []):
                        T[(x, y, u, v)] += sign * c1 * d
        else:
            w = s + i
            if w < 0:
                continue
            # first a_x^<i>[s-h+i]: V_h -> V_w, then b_v[h-s-i]: V_w -> V_h
            first = {}
            for x in A:
                ai = angle(A[x], h, i)
                for y, eta in enumerate(parts):
                    g = op_poly(ai, s - h + i, {eta: 1})
                    if g:
                        first[(x, y)] = g
            needed = set()
            for g in first.values():
                needed |= set(g)
            second = {}
            for v in B:
                for sg in needed:
                    g = op_poly(B[v], h - s - i, {sg: 1})
                    for upart, d in g.items():
                        if upart in idx:
                            second.setdefault(sg, []).append((v, idx[upart], d))
            for (x, y), g in first.items():
                for sg, c1 in g.items():
                    for (v, u, d) in second.get(sg, []):
                        T[(x, y, u, v)] += sign * c1 * d
    return parts, labels, {k: v for k, v in T.items() if v}


def count_bounds(h, s):
    """The paper's R^row_s = sum_i p(s+i), R^col_s = sum_i p(2h-s-i)."""
    Rrow = sum(p(s + i) for i in range(2 * h + 1))
    Rcol = sum(p(2 * h - s - i) for i in range(2 * h + 1))
    return Rrow, Rcol
