"""Appendix B pieces A_s (Heisenberg Fock space), computed exactly for small h.
Checks  sum_s A_s = h! [x=v][y=u]  and compares the TRUE row/column ranks of each A_s with the
paper's bound  R_s^row = sum_i p(s+i),  R_s^col = sum_i p(2h-s-i).
"""
import sys, math, itertools
from functools import lru_cache
from collections import defaultdict
from flint import nmod_mat
P = (1<<61)-1

def partitions(n, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0: yield (); return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n-k, k):
            yield (k,)+rest

def gbinom(n, j):  # generalized binomial, j>=0
    if j < 0: return 0
    num = 1
    for t in range(j): num *= (n - t)
    return num // math.factorial(j)

def compositions_lower(total, lows):
    """all tuples l with l_i >= lows_i and sum = total"""
    if not lows:
        if total == 0: yield ()
        return
    first, rest = lows[0], lows[1:]
    rmin = sum(rest)
    for l in range(first, total - rmin + 1):
        for tail in compositions_lower(total - l, rest):
            yield (l,)+tail

def mult(part):
    d = defaultdict(int)
    for k in part: d[k] += 1
    return d

@lru_cache(maxsize=None)
def apply_mono(mu, r, sigma):
    """(t^mu)[r] applied to t^sigma; returns dict partition->coef.  mu, sigma: sorted tuples."""
    out = defaultdict(int)
    m = len(mu)
    if m == 0:
        if r == 0: out[sigma] += 1
        return dict(out)
    msig = mult(sigma)
    distinct = sorted(msig)
    for mask in range(1 << m):
        ann = [mu[i] for i in range(m) if mask >> i & 1]
        cre = [mu[i] for i in range(m) if not (mask >> i & 1)]
        # assign annihilation values k_i (parts of sigma) to each ann part
        for ks in itertools.product(distinct, repeat=len(ann)):
            cnt = defaultdict(int)
            for k in ks: cnt[k] += 1
            if any(cnt[k] > msig[k] for k in cnt): continue
            coef = 1
            for mui, k in zip(ann, ks):
                coef *= gbinom(-k-1, mui-1)
            if coef == 0: continue
            dcoef = 1
            for k, c in cnt.items():
                dcoef *= k**c * math.factorial(msig[k]) // math.factorial(msig[k]-c)
            rem = defaultdict(int, msig)
            for k, c in cnt.items(): rem[k] -= c
            total = r + sum(ks)
            if cre:
                for ls in compositions_lower(total, tuple(cre)):
                    c2 = 1
                    for mui, l in zip(cre, ls): c2 *= gbinom(l-1, mui-1)
                    if c2 == 0: continue
                    new = defaultdict(int, rem)
                    for l in ls: new[l] += 1
                    key = tuple(sorted([k for k in new for _ in range(new[k])], reverse=True))
                    out[key] += coef*dcoef*c2
            else:
                if total != 0: continue
                key = tuple(sorted([k for k in rem for _ in range(rem[k])], reverse=True))
                out[key] += coef*dcoef
    return {k: v for k, v in out.items() if v}

def poly_mul(p, q):
    out = defaultdict(int)
    for a, x in p.items():
        for b, y in q.items():
            out[tuple(sorted(a+b, reverse=True))] += x*y
    return dict(out)

def a_mu(mu):
    p = {(): 1}
    for n in mu:
        yn = {(j,): (-1)**(n-1) * math.comb(n, j) for j in range(1, n+1)}
        p = poly_mul(p, yn)
    return p

def z_mu(mu):
    z = 1
    for k, c in mult(mu).items(): z *= k**c * math.factorial(c)
    return z

def run(h):
    parts = list(partitions(h)); N = len(parts); idx = {p:i for i,p in enumerate(parts)}
    hf = math.factorial(h)
    A = {mu: a_mu(mu) for mu in parts}
    Bc = {nu: hf // z_mu(nu) for nu in parts}  # b_nu = Bc * t^nu
    results = []
    total = defaultdict(int)
    for s in range(-2*h, 2*h+1):
        T = defaultdict(int)  # (x,y,u,v)->value
        for i in range(0, 2*h+1):
            w = s + i  # middle weight in (54)
            if w < 0: continue
            # first factor: [t^sigma] a_x<i>[s-h+i] t^y ;  a<i> = sum_{h'} C(h'+h,i) abar_{h'}
            F1 = defaultdict(dict)  # (x,y) -> {sigma: c}
            for x, mu in enumerate(parts):
                for y, ym in enumerate(parts):
                    acc = defaultdict(int)
                    for nu, c in A[mu].items():
                        hp = sum(nu)
                        cc = c * math.comb(hp + h, i)
                        if cc == 0: continue
                        for sg, d in apply_mono(nu, s-h+i, ym).items():
                            acc[sg] += cc*d
                    F1[(x,y)] = {k:v for k,v in acc.items() if v}
            # second factor: [t^u] b_v[h-s-i] t^sigma
            sig_needed = set()
            for d in F1.values(): sig_needed |= set(d)
            F2 = {}
            for sg in sig_needed:
                for v, nu in enumerate(parts):
                    res = apply_mono(nu, h-s-i, sg)
                    for uu, d in res.items():
                        if uu in idx:
                            F2[(sg, idx[uu], v)] = Bc[nu]*d
            sign = (-1)**i
            # combine
            F2by = defaultdict(list)
            for (sg,u,v), d in F2.items(): F2by[sg].append((u,v,d))
            for (x,y), d1 in F1.items():
                for sg, c1 in d1.items():
                    for (u,v,d) in F2by.get(sg, []):
                        T[(x,y,u,v)] += sign*c1*d
        T = {k:v for k,v in T.items() if v}
        for k,v in T.items(): total[k] += v
        if not T: continue
        # ranks
        Mr = [[0]*(N*N) for _ in range(N*N)]; Mc = [[0]*(N*N) for _ in range(N*N)]
        for (x,y,u,v), val in T.items():
            Mr[x*N+y][u*N+v] = val % P
            Mc[x*N+u][y*N+v] = val % P
        rr = nmod_mat(Mr, P).rank(); rc = nmod_mat(Mc, P).rank()
        pb = lambda n: sum(1 for _ in partitions(n)) if n >= 0 else 0
        Rrow = sum(pb(s+i) for i in range(2*h+1)); Rcol = sum(pb(2*h-s-i) for i in range(2*h+1))
        results.append((s, rr, rc, Rrow, Rcol))
    # check identity
    ok = all((total.get((x,y,u,v),0) == (hf if (x==v and y==u) else 0))
             for x in range(N) for y in range(N) for u in range(N) for v in range(N))
    return N, ok, results

if __name__ == "__main__":
    for h in [int(a) for a in sys.argv[1:]]:
        N, ok, res = run(h)
        lam = math.log2(N)
        print(f"h={h} N=p(h)={N} identity_ok={ok}")
        worst = 0; worstb = 0
        for s, rr, rc, Rr, Rc in res:
            c = math.log2(rr)+math.log2(rc); cb = math.log2(min(Rr,N*N))+math.log2(min(Rc,N*N))
            worst = max(worst, c); worstb = max(worstb, cb)
            print(f"  s={s:3d} rank_row={rr:5d} (bound {Rr:6d}) rank_col={rc:5d} (bound {Rc:6d})  bits={c:6.2f} / 4lam={4*lam:.2f}")
        print(f"  worst true bits/(4 lam) = {worst/(4*lam):.4f};  worst bound bits/(4lam) = {worstb/(4*lam):.4f}; #pieces={len(res)}")
