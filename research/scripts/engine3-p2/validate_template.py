"""Validation of the P2 encoding on OpenAI's M0-template (auxiliary coordinates B = ([r]^Q)^2).
(a) the paper's explicit rows P_u(T) = d_u(I-M0) + sum_w M0[u,w] phi_{u,w}(T) d_w satisfy our constraint system
    exactly (rational rank test), with degree R_OAI-1;
(b) our generic solver (t-dependent measurement spaces allowed) finds min degree per orbit rep;
(c) template subclass (shared Lambda, polynomial measurement part):  e_u in Lambda + span{e_w : |E_uw| <= deg};
(d) Theorem 1 of parity-barrier.md: rank(I-M0) >= #{u : phi(d_u)-phi(a_u) >= R_OAI}.
usage: python3 validate_template.py r Q A0 ROAI
"""
import sys, itertools, math
import numpy as np
from fractions import Fraction
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from p2common import rank_modp, rank_exact, min_R_occ, feasible, lower_count, foreign_count

r, Q, A0, ROAI = map(int, sys.argv[1:5])
labels = list(itertools.product(range(r), repeat=Q))
B = [(a, d) for a in labels for d in labels]
D = len(B); idx = {u: k for k, u in enumerate(B)}
print(f"r={r} Q={Q} D={D} window I={list(range(A0, A0+ROAI))} (deg {ROAI-1})")

# per-position eigenbasis of the pair swap on [r]^2: list of (vector dict on (al,de), sign)
loc = []
for al in range(r): loc.append(({(al, al): 1}, +1))
for al in range(r):
    for de in range(al+1, r):
        loc.append(({(al, de): 1, (de, al): 1}, +1))
        loc.append(({(al, de): 1, (de, al): -1}, -1))
I = set(range(A0, A0 + ROAI))
meas = []   # measured eigenvectors (j not in I), as dict coord->value
for choice in itertools.product(range(len(loc)), repeat=Q):
    j = sum(1 for c in choice if loc[c][1] == -1)
    if j in I: continue
    vec = {}
    # product over positions
    parts = [loc[c][0] for c in choice]
    for keys in itertools.product(*[list(p.items()) for p in parts]):
        a = tuple(k[0][0] for k in keys); d = tuple(k[0][1] for k in keys)
        val = 1
        for k in keys: val *= k[1]
        vec[idx[(a, d)]] = val
    meas.append(vec)
binom_tail = sum(math.comb(Q, j) * (r-1)**j * (r+1)**(Q-j) for j in range(Q+1) if j not in I) / (2*r)**Q
print(f"measured eigenvectors c_B = {len(meas)}  = D*Pr[W notin I] = {D*binom_tail:.1f}")

# M0 = V0 f(W0); Wt = 2 W0 = sum_s (I - Pi_s)
Pi = []
for s in range(Q):
    Pm = np.zeros((D, D), dtype=np.int64)
    for (a, d) in B:
        a2 = list(a); d2 = list(d); a2[s], d2[s] = d[s], a[s]
        Pm[idx[(a, d)], idx[(tuple(a2), tuple(d2))]] = 1
    Pi.append(Pm)
Id = np.eye(D, dtype=np.int64)
Wt = sum(Id - P for P in Pi)
V0 = Id.copy()
for P in Pi: V0 = V0 @ P
# f(z) = (-1)^A0 sum_{j<ROAI} (-2)^j C(z-A0, j);  z = Wt/2
# (-2)^j C(z-A0,j) = (-1)^j/j! prod_{a<j} (Wt - 2(A0+a))
fW = np.zeros((D, D), dtype=object)
prod = Id.astype(object)
for j in range(ROAI):
    fW = fW + prod * Fraction((-1)**j, math.factorial(j))
    prod = prod.dot((Wt - 2*(A0+j)*Id).astype(object))
fW = fW * ((-1)**A0)
M0 = V0.astype(object).dot(fW)
IM = Id.astype(object) - M0
den = 1
for x in M0.flat:
    if x != 0: den = den * Fraction(x).denominator // math.gcd(den, Fraction(x).denominator)
IMi = np.array([[int(Fraction(x) * den) for x in row] for row in IM], dtype=np.int64)
rk = rank_modp(IMi)
print(f"rank(I - M0) = {rk}  (expected c_B = {len(meas)})")
# support condition (T2)
bad = 0
for u in range(D):
    for w in np.nonzero(np.array([x != 0 for x in M0[u]]))[0]:
        E = sum(1 for s in range(Q) if B[w][0][s] != B[u][1][s])
        if E > ROAI - 1: bad += 1
print(f"(T2) support violations: {bad}")

# Theorem 1: phi(x) = #{t : x_t in half}; also signed weighted variants
half = set(range(r // 2)) if r % 2 == 0 else set(range(r // 2))
best = 0
for wts in itertools.product([1, -1], repeat=Q):
    cnt = 0
    for (a, d) in B:
        phi = lambda x: sum(wts[t] * (1 if x[t] in half else 0) for t in range(Q))
        if phi(d) - phi(a) >= ROAI: cnt += 1
    best = max(best, cnt)
print(f"Theorem 1 triangular lower bound (best of 2^Q signed phi) = {best} <= rank {rk}: {best <= rk}")

# design in our encoding: variables = coordinates u, one occurrence per u, own clause e=u
design = {'Q': Q,
          'part': [[B[u][0][t] for u in range(D)] for t in range(Q)],
          'alpha': [[B[u][1][t] for u in range(D)] for t in range(Q)],
          'rows': [[[] for h in range(r)] for t in range(Q)]}
for t in range(Q):
    for vec in meas:
        for h in range(r):
            rw = {i: x for i, x in vec.items() if B[i][0][t] == h}
            if rw: design['rows'][t][h].append(rw)
print("rows per (t,h):", [[len(design['rows'][t][h]) for h in range(r)] for t in range(Q)])

# (a) explicit OAI rows satisfy constraints: check P_u(t)|_{S_{t,h}} in span(rows) exactly
def check_explicit(u):
    ok = True
    for t in range(Q):
        tt = t + 1
        Pt = [Fraction(x) for x in IM[u]]
        for w in range(D):
            m = M0[u, w]
            if m == 0: continue
            E = [s+1 for s in range(Q) if B[w][0][s] != B[u][1][s]]
            ph = Fraction(1)
            for s in E: ph *= (1 - Fraction(tt, s))
            Pt[w] += Fraction(m) * ph
        for h in range(r):
            if h == B[u][1][t]: continue
            Sh = [i for i in range(D) if B[i][0][t] == h]
            target = [Pt[i] for i in Sh]
            if all(x == 0 for x in target): continue
            dd = 1
            for x in target: dd = dd * x.denominator // math.gcd(dd, x.denominator)
            Rm = [[rw.get(i, 0) for i in Sh] for rw in design['rows'][t][h]]
            if rank_exact(Rm + [[int(x*dd) for x in target]]) != rank_exact(Rm) if Rm else True:
                ok = False
    return ok

reps = {}
for u, (a, d) in enumerate(B):
    k = sum(1 for s in range(Q) if a[s] != d[s])
    if a == tuple([0]*Q) and k not in reps and all(d[s] in (0, 1) for s in range(Q)) and \
       list(d) == sorted(d, reverse=True):
        reps[k] = u
reps = dict(sorted(reps.items()))
print("orbit representatives (k = #positions with a != d):", reps)
for k, u in reps.items():
    ex = check_explicit(u)
    # (b) general solver min degree; (c) template subclass min degree
    Rgen = min_R_occ(design, u, u)
    ok_exact = feasible(design, u, u, Rgen, exact=True)
    below = feasible(design, u, u, Rgen - 1, exact=True) if Rgen > lower_count(design, u, u) else None
    # template: e_u in Lambda + span{e_w: |E_uw| <= deg}
    Rtpl = None
    for deg in range(0, Q + 1):
        near = [w for w in range(D) if sum(1 for s in range(Q) if B[w][0][s] != B[u][1][s]) <= deg]
        Mt = [[vec.get(i, 0) for i in range(D)] for vec in meas] + [[1 if i == w else 0 for i in range(D)] for w in near]
        eu = [1 if i == u else 0 for i in range(D)]
        if rank_modp(Mt + [eu]) == rank_modp(Mt):
            Rtpl = deg; break
    print(f" k={k}: explicit OAI rows satisfy constraints exactly: {ex}; general-interface min deg = {Rgen} "
          f"(exact Q-rank check feasible={ok_exact}, deg-1 feasible={below}); template-subclass min deg = {Rtpl}; "
          f"#foreign pts of own coord = {foreign_count(design,u,u)}")

# ---------------------------------------------------------------- (e) the template pushed to a real instance
if len(sys.argv) > 5:
    import random
    from p2common import make_instance, occurrences, design_R
    fam, nn = sys.argv[5], int(sys.argv[6])
    cl = make_instance(fam, nn, 1); occ = occurrences(cl)
    rng = random.Random(7)
    av = [tuple(rng.randrange(r) for _ in range(Q)) for _ in range(nn)]
    df = [tuple(rng.randrange(r) for _ in range(Q)) for _ in range(len(cl))]
    copies = []          # list of dict position-index -> variable
    place = {}
    for (f, v) in occ:
        u = idx[(av[v], df[f])]
        for c, cp in enumerate(copies):
            if u not in cp: cp[u] = v; place[(f, v)] = (c, u); break
        else:
            copies.append({u: v}); place[(f, v)] = (len(copies) - 1, u)
    print(f"instance {fam} n={nn}: {len(occ)} occurrences placed in {len(copies)} copies of B")
    def push(vec, c):     # vector on copy c of B -> vector on variables
        out = {}
        for w, x in vec.items():
            if w in copies[c] and x != 0:
                out[copies[c][w]] = out.get(copies[c][w], 0) + x
        return {k: x for k, x in out.items() if x != 0}
    des = {'Q': Q, 'part': [[av[v][t] for v in range(nn)] for t in range(Q)],
           'alpha': [[df[f][t] for f in range(len(cl))] for t in range(Q)],
           'rows': [[[] for h in range(r)] for t in range(Q)]}
    for t in range(Q):
        for c in range(len(copies)):
            for vec in meas:
                for h in range(r):
                    rw = push({i: x for i, x in vec.items() if B[i][0][t] == h}, c)
                    if rw: des['rows'][t][h].append(rw)
    # explicit pushed-forward OAI rows; check constraints exactly
    allok = True
    for (f, v) in occ:
        c, u = place[(f, v)]
        for t in range(Q):
            tt = t + 1
            Pt = {}
            for w in range(D):
                val = Fraction(IM[u, w])
                if M0[u, w] != 0:
                    E = [s+1 for s in range(Q) if B[w][0][s] != B[u][1][s]]
                    ph = Fraction(1)
                    for s in E: ph *= (1 - Fraction(tt, s))
                    val += Fraction(M0[u, w]) * ph
                if val != 0 and w in copies[c]:
                    Pt[copies[c][w]] = Pt.get(copies[c][w], 0) + val
            if t == 0:
                pass
            for h in range(r):
                if h == df[f][t]: continue
                Sh = [x for x in range(nn) if av[x][t] == h]
                target = [Pt.get(x, Fraction(0)) for x in Sh]
                if all(x == 0 for x in target): continue
                dd = 1
                for x in target: dd = dd * x.denominator // math.gcd(dd, x.denominator)
                Rm = [[rw.get(x, 0) for x in Sh] for rw in des['rows'][t][h]]
                if not Rm or rank_exact(Rm + [[int(x*dd) for x in target]]) != rank_exact(Rm): allok = False
        # restoration at T = 0
        P0 = {}
        for w in range(D):
            if IM[u, w] + M0[u, w] != 0 and w in copies[c]:
                P0[copies[c][w]] = P0.get(copies[c][w], 0) + Fraction(IM[u, w] + M0[u, w])
        if {k: x for k, x in P0.items() if x != 0} != {v: 1}: allok = False
    dims = [[rank_exact([[rw.get(x, 0) for x in range(nn) if av[x][t] == h] for rw in des['rows'][t][h]]) if des['rows'][t][h] else 0
             for h in range(r)] for t in range(Q)]
    sizes = [[sum(1 for x in range(nn) if av[x][t] == h) for h in range(r)] for t in range(Q)]
    Rg, _ = design_R(des, cl)
    print(f" pushed-forward OAI rows (deg {ROAI-1}) satisfy all constraints + P(0)=e_v exactly: {allok}")
    print(f" dim R_(t,h) after pushforward = {dims}  vs group sizes {sizes};  general-solver max R on this design = {Rg}")
    print(f" max l1 of pushed rows = {max(sum(abs(x) for x in rw.values()) for t in range(Q) for h in range(r) for rw in des['rows'][t][h])}")
