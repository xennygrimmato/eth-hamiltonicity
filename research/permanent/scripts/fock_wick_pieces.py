"""Wick (Leibniz) slicing on a sparse Fock space V_S = Q[t_k : k in S]  (sparse-fock.md, Section 4).

Labels x, v <-> S-partitions mu, nu of h (N = p_S(h)).  A_x = multiplication by t^mu : V_E -> V_{E+h};
B_v = (h!/z_nu) prod_i nabla_{nu_i}, nabla_k = k d/dt_k : V_E -> V_{E-h}, so that B_v t^mu = h! [mu = nu] on V_h.
Wick's theorem (nabla_k t_l = t_l nabla_k + k [k = l]) gives on V_h

    B_v A_x = sum_{rho subset mu cap nu} c(mu,nu,rho) t^{mu \\ rho} (h!/z_nu) nabla_{nu \\ rho}          (*)

(one term per sub-multiset rho of the common parts; on V_h the term rho passes through V_{|rho|} in the
order written (nabla_{nu \ rho} lowers by h-|rho|) and through V_{2h-|rho|} with the factors exchanged
(t^{mu \ rho} first); rho = mu = nu gives h! [x = v] Id).  The coefficient c factorises as
c_1(mu,rho) c_2(nu,rho), so the slice T_w has a column factorisation through sum_{|rho|=w} dim V_w = p_S(w) D_S(w)
terms; the exchanged order gives a row factorisation of B_v A_x through D_S(2h) terms.
Slices by contraction weight: T_w(x,y,u,v) = <t^u| sum_{|rho|=w} ... |t^y>, w = 0..h, with
    sum_{w<=h} T_w = <u|B_v A_x|y>   and   T_h = h! [x=v][y=u]  (the crossing).
Every family of signed interval sums  { sum_{w in [w0,h]} T_w } u { -sum_{w in J} T_w : J a partition of [w0,h-1] into intervals }
adds up to the crossing; we compute the true row rank (x,y)|(u,v) and column rank (x,u)|(y,v) of every
interval sum (mod the prime 2^61-1: a lower bound for the rank over Q, generically exact), the cost
log2 r + log2 o, and the best family by dynamic programming (min over families of the max cost).
rho_true := best max cost / (4 lambda), lambda = log2 N; compared with the law f_S(2h)/(2 f_S(h)).

Checks printed as PASS/FAIL: (*) summed over rho equals B_v A_x computed directly; T_h = h!*crossing.
Usage: python3 fock_wick_pieces.py [S=N|sq|pow2|cubes] h1 h2 ...
"""
import sys, math, time
from functools import lru_cache
from collections import defaultdict
from flint import nmod_mat

PR = (1 << 61) - 1
SETS = {"N": lambda k: True, "sq": lambda k: int(round(k ** .5)) ** 2 == k,
        "pow2": lambda k: k & (k - 1) == 0, "cubes": lambda k: round(k ** (1 / 3)) ** 3 == k}


def make_parts(ind):
    @lru_cache(maxsize=None)
    def parts(n, maxpart=None):
        if maxpart is None: maxpart = n
        if n == 0: return ((),)
        out = []
        for k in range(min(n, maxpart), 0, -1):
            if ind(k):
                for rest in parts(n - k, k): out.append((k,) + rest)
        return tuple(out)
    return parts


def z_mu(mu):
    z = 1
    for k in set(mu): c = mu.count(k); z *= k ** c * math.factorial(c)
    return z


def nabla_prod(nu, mono):
    """prod_{k in nu} nabla_k applied to t^mono (a multiset tuple); returns (coef, monomial) or (0, None)."""
    m = list(mono); c = 1
    for k in nu:
        cnt = m.count(k)
        if cnt == 0: return 0, None
        c *= k * cnt; m.remove(k)
    return c, tuple(sorted(m, reverse=True))


def sub_multisets(common):
    """all sub-multisets rho of the multiset `common` (tuple), with the multiplicity data."""
    keys = sorted(set(common))
    mult = {k: common.count(k) for k in keys}
    out = [()]
    for k in keys:
        new = []
        for r in out:
            for j in range(mult[k] + 1): new.append(r + (k,) * j)
        out = new
    return [tuple(sorted(r, reverse=True)) for r in out]


def wick_coef(mu, nu, rho):
    c = 1
    for k in set(rho):
        j = rho.count(k)
        c *= math.comb(mu.count(k), j) * math.comb(nu.count(k), j) * math.factorial(j) * k ** j
    return c


def rank_mod(entries, nrows, ncols):
    """entries: dict (r,c)->int."""
    if not entries: return 0
    rows = defaultdict(dict)
    for (r, c), v in entries.items(): rows[r][c] = v % PR
    M = [[0] * ncols for _ in rows]
    for i, r in enumerate(sorted(rows)):
        for c, v in rows[r].items(): M[i][c] = v
    return nmod_mat(M, PR).rank()


def build(ind, h):
    parts = make_parts(ind)
    basis = parts(h); N = len(basis); idx = {b: i for i, b in enumerate(basis)}
    hf = math.factorial(h)
    T = {w: defaultdict(int) for w in range(h + 1)}
    for x, mu in enumerate(basis):
        for v, nu in enumerate(basis):
            scale = hf // z_mu(nu)
            common = []
            for k in set(mu) & set(nu): common += [k] * min(mu.count(k), nu.count(k))
            for rho in sub_multisets(tuple(common)):
                cw = wick_coef(mu, nu, rho)
                nur = list(nu)
                mur = list(mu)
                for k in rho: nur.remove(k); mur.remove(k)
                for y, eta in enumerate(basis):
                    c, m = nabla_prod(nur, eta)
                    if c == 0: continue
                    u = idx[tuple(sorted(m + tuple(mur), reverse=True))]
                    T[sum(rho)][(x, y, u, v)] += cw * c * scale
    # direct check of (*): B_v A_x via nabla_prod on t^{mu + eta}
    direct = defaultdict(int)
    for x, mu in enumerate(basis):
        for v, nu in enumerate(basis):
            scale = hf // z_mu(nu)
            for y, eta in enumerate(basis):
                c, m = nabla_prod(nu, tuple(sorted(mu + eta, reverse=True)))
                if c: direct[(x, y, idx[m], v)] += c * scale
    total = defaultdict(int)
    for w in T:
        for k, val in T[w].items(): total[k] += val
    ok1 = {k: v for k, v in total.items() if v} == {k: v for k, v in direct.items() if v}
    ok2 = {k: v for k, v in T[h].items() if v} == {(x, y, y, x): hf for x in range(N) for y in range(N)}
    return basis, N, T, ok1, ok2


def run(name, h):
    ind = SETS[name]
    t0 = time.time()
    basis, N, T, ok1, ok2 = build(ind, h)
    lam = math.log2(N)
    parts = make_parts(ind)
    D = lambda E: len(parts(E)) if E >= 0 else 0
    law = math.log2(D(2 * h)) / (2 * lam)
    print(f"\nS={name} h={h} N=p_S(h)={N} lam={lam:.3f}  Wick identity (*): {'PASS' if ok1 else 'FAIL'}  T_h = h!*crossing: {'PASS' if ok2 else 'FAIL'}  (build {time.time()-t0:.1f}s)")
    # ranks of all interval sums [a,b]
    cost = {}
    print("  interval sums  sum_{w=a..b} T_w :  row rank (x,y)|(u,v), col rank (x,u)|(y,v), bits = log2 r + log2 o   [certified: col(T_w) <= p_S(w) D_S(w); row(B_vA_x) <= D_S(2h)]")
    for a in range(h + 1):
        acc = defaultdict(int)
        for b in range(a, h + 1):
            for k, val in T[b].items(): acc[k] += val
            ent = {k: v for k, v in acc.items() if v}
            if not ent:
                cost[(a, b)] = 0.0; continue
            r = rank_mod({(x * N + y, u * N + v): val for (x, y, u, v), val in ent.items()}, N * N, N * N)
            o = rank_mod({(x * N + u, y * N + v): val for (x, y, u, v), val in ent.items()}, N * N, N * N)
            cost[(a, b)] = math.log2(r) + math.log2(o)
            if b == h or a == b or a == 0:
                tag = "B_v A_x (all w)" if (a, b) == (0, h) else ("T_%d" % a if a == b else "")
                print(f"    [{a:2d},{b:2d}]  r={r:5d}  o={o:5d}  bits={cost[(a,b)]:6.2f}  {tag}")
    # DP: best family = piece [w0,h] plus a partition of [w0,h-1] into intervals; minimise the max cost
    @lru_cache(maxsize=None)
    def best(a, b):  # min over partitions of [a,b] into intervals of the max cost; a>b -> 0
        if a > b: return 0.0
        return min(max(cost[(a, c)], best(c + 1, b)) for c in range(a, b + 1))
    fam = min((max(cost[(w0, h)], best(w0, h - 1)), w0) for w0 in range(h + 1))
    fine = max([cost[(0, h)]] + [cost[(w, w)] for w in range(h)])
    coarse = max(cost[(0, h)], cost[(0, h - 1)])
    print(f"  fine family {{B_vA_x, T_w (w<h)}}: max bits {fine:6.2f} -> rho_true = {fine/(4*lam):.4f}")
    print(f"  coarse family {{B_vA_x, sum_(w<h) T_w}}: max bits {coarse:6.2f} -> rho_true = {coarse/(4*lam):.4f}")
    print(f"  best interval family (w0={fam[1]}): max bits {fam[0]:6.2f} -> rho_true = {fam[0]/(4*lam):.4f}      law f(2h)/(2f(h)) = {law:.4f}   1/sqrt2 = 0.7071")
    return fam[0] / (4 * lam), law, ok1 and ok2


if __name__ == "__main__":
    name = sys.argv[1]; hs = [int(a) for a in sys.argv[2:]]
    allok = True
    for h in hs:
        rho, law, ok = run(name, h); allok &= ok
    print("\nIDENTITIES", "PASS" if allok else "FAIL")
