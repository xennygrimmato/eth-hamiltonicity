"""Numerical checks for the meta-theorem (research/meta-theorem.md), problems NOT in exact-extensions.md.

For every family, three independent evaluations on random small instances:
  truth : brute force (combinatorial definition, no determinants),
  ident : the identity "local constraints x product of determinants", by explicit determinants,
  net   : the blob network (meta_engine, multi-field) on several random partitions, K = 2, 3 (4).
Generating variables are carried by Kronecker substitution Y = 2^b (balanced digits).

Families
  P1  connected feedback vertex set      CONN(Y) x FOREST(V\\Y)          two fields
  P2  connected odd cycle transversal    CONN(X) x local 2-colouring      one field
  P3  exact k-leaf out-branching          OUT-BRANCH (directed, root r)    exact count
  P4  spanning trees by degree statistics (max full degree, max internal, max degree <= d)  exact
  P5  directed k-paths / k-cycles (directed longest path / cycle)           exact
  P6  graph-metric TSP (and poly-weight TSP walks)  CONN(support) x even degrees, mult <= 2
  P7  min cycle cover, undirected and directed   lowest w-power of det(L_X + wI)
  P8  ordered pairs of edge-disjoint spanning trees   TREE x TREE, two fields, exact
  P9  min strongly connected spanning subgraph        IN-ARB(r) x OUT-ARB(r), two fields

Run: python3 meta_problems.py [seed] [trials] [comma-separated subset, e.g. p1,p5]
"""
import itertools, random, sys, math
from fractions import Fraction
from ext_engine import ONE, ZERO, gmul, gadd, gscale, gexp, det_exact, kron_decode
from ext_problems import rand_graph, rand_digraph, components, laplacian, minor, tau
from meta_engine import MSpec, check_network

ALL_OK = True
def report(name, rows):
    global ALL_OK
    ok = all(r[-1] for r in rows)
    ALL_OK &= ok
    print(f"{name}: {'OK' if ok else 'FAIL'}")
    for r in rows:
        print("     ", r)

def netok(rows):
    return all(x[-1] for x in rows)

def short(rows):
    return [x[:3] for x in rows]

def adjacency(n, E):
    adj = {v: set() for v in range(n)}
    for i, j in E:
        adj[i].add(j); adj[j].add(i)
    return adj

def connected(vs, E):
    vs = list(vs)
    if not vs:
        return False
    return len(components(vs, E)[0]) == 1

def is_forest(vs, E):
    return not components(list(vs), E)[1]

def bipartite_colourings(vs, E):
    vs = list(vs); cnt = 0
    for col in itertools.product((0, 1), repeat=len(vs)):
        c = dict(zip(vs, col))
        if all(c[i] != c[j] for i, j in E):
            cnt += 1
    return cnt

def reach(n, arcs, s, rev=False):
    out = {v: [] for v in range(n)}
    for i, j in arcs:
        (out[j].append(i) if rev else out[i].append(j))
    seen = {s}; st = [s]
    while st:
        x = st.pop()
        for y in out[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    return seen

def dlap(vs, arcs, kind):
    """kind 'out': D_out - A ; 'in': D_in - A^T, on vertex list vs."""
    idx = {v: t for t, v in enumerate(vs)}
    L = [[0] * len(vs) for _ in vs]
    for i, j in arcs:
        a, b = idx[i], idx[j]
        if kind == "out":
            L[a][a] += 1; L[a][b] -= 1
        else:
            L[b][b] += 1; L[b][a] -= 1
    return L

def add_diag(L, d):
    L = [row[:] for row in L]
    for t in range(len(L)):
        L[t][t] += d[t] if isinstance(d, list) else d
    return L

# ================================================================== P1 connected FVS
class CFVSSpec(MSpec):
    """field 0: connectivity of G[Y] (mass Wm, rootless: [Wm^1] det(L_Y+Wm I) = |Y| tau(G[Y]));
    field 1: forest indicator of G[V\\Y] by the 2-deg mass trick (variable Zv)."""
    nf = 2
    def __init__(s, n, E, Wm, Zv, T):
        s.n, s.edges, s.Wm, s.Zv, s.T = n, E, Wm, Zv, T
    def vstates(s, v): return [0, 1]
    def C(s, v, y, sig): return s.T * 2 * s.Zv if y else 1
    def M(s, v, y):
        if y:
            return gmul(s.mass(v, 0, s.Wm), s.delete(v, 1))
        return gmul(s.delete(v, 0), s.mass(v, 1, 2 * s.Zv))
    def F(s, k, yu, yv, sig):
        u, v = s.edges[k]
        if yu and yv:
            return gadd(ONE, s.q_und(u, v, 0))
        if not yu and not yv:
            X = gadd(s.q_und(u, v, 1), gscale(gadd(s.pbps(u, 1), s.pbps(v, 1)), -s.Zv))
            return gscale(gexp(X), 2 * s.Zv)
        return ONE

def prob_cfvs(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n + 1, min(n * (n - 1) // 2, 2 * n - 1))
        E = rand_graph(n, m, rng)
        b = 64; Y = 1 << b
        Wm, T, Zv = Y, Y ** (n + 1), Y ** ((n + 1) ** 2)
        truth = [0] * (n + 1); target = 0
        for r in range(n + 1):
            for Ys in itertools.combinations(range(n), r):
                Yl = list(Ys); Fl = [v for v in range(n) if v not in Ys]
                EY = [e for e in E if e[0] in Ys and e[1] in Ys]
                EF = [e for e in E if e[0] in Fl and e[1] in Fl]
                if r and connected(Yl, EY) and is_forest(Fl, EF):
                    truth[r] += r * int(tau(Yl, EY))
                d1 = det_exact(add_diag(laplacian(Yl, EY), Wm))
                degF = {v: 0 for v in Fl}
                for i, j in EF:
                    degF[i] += 1; degF[j] += 1
                d2 = det_exact(add_diag(laplacian(Fl, EF), [Zv * (2 - degF[v]) for v in Fl]))
                target += T ** r * (2 * Zv) ** (r + len(EF)) * d1 * d2
        dist = kron_decode(target, b, (n + 1) ** 2 * (3 * n + m + 2))
        got = [Fraction(dist[1 + (n + 1) * k + (n + 1) ** 2 * n], 2 ** n) for k in range(n + 1)]
        sp = CFVSSpec(n, E, Wm, Zv, T)
        net = check_network(sp, E, target, rng, Ks=(2, 3), max_cross=5, max_inc=4)
        kmin = next((k for k in range(n + 1) if truth[k]), None)
        ok = got == truth and netok(net)
        rows.append((n, m, f"min CFVS={kmin}", short(net), ok))
    report("P1 connected FVS: [w^1 Zv^n t^k]/2^n = k*sum tau(G[Y]) over CFVS Y, |Y|=k", rows)

# ================================================================== P2 connected OCT
class COCTSpec(MSpec):
    """states: 0 = in X (connectivity field, mass Wm), 1/2 = colour outside X."""
    def __init__(s, n, E, Wm, T):
        s.n, s.edges, s.Wm, s.T = n, E, Wm, T
    def vstates(s, v): return [0, 1, 2]
    def C(s, v, st, sig): return s.T if st == 0 else 1
    def M(s, v, st): return s.mass(v, 0, s.Wm) if st == 0 else s.delete(v, 0)
    def F(s, k, a, c, sig):
        u, v = s.edges[k]
        if a == 0 and c == 0:
            return gadd(ONE, s.q_und(u, v, 0))
        if a and c and a == c:
            return ZERO
        return ONE

def prob_coct(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n + 2, min(n * (n - 1) // 2, 2 * n))
        E = rand_graph(n, m, rng)
        b = 48; Y = 1 << b; Wm, T = Y, Y ** (n + 1)
        truth = [0] * (n + 1); target = 0; best = None
        for r in range(n + 1):
            for Xs in itertools.combinations(range(n), r):
                Xl = list(Xs); Ol = [v for v in range(n) if v not in Xs]
                EX = [e for e in E if e[0] in Xs and e[1] in Xs]
                EO = [e for e in E if e[0] in Ol and e[1] in Ol]
                nc = bipartite_colourings(Ol, EO)
                if r and connected(Xl, EX) and nc:
                    truth[r] += r * int(tau(Xl, EX)) * nc
                    best = r if best is None else min(best, r)
                target += T ** r * det_exact(add_diag(laplacian(Xl, EX), Wm)) * nc
        dist = kron_decode(target, b, (n + 1) * (n + 2))
        got = [dist[1 + (n + 1) * k] for k in range(n + 1)]
        opt = next((k for k in range(n + 1) if got[k]), None)
        sp = COCTSpec(n, E, Wm, T)
        net = check_network(sp, E, target, rng, Ks=(2, 3, 4), max_cross=6, max_inc=5)
        ok = got == truth and opt == best and netok(net)
        rows.append((n, m, f"min COCT={opt}", short(net), ok))
    report("P2 connected OCT: [w^1 t^k] = k*sum tau(G[X]) 2^{c(V-X)}; lowest k = optimum", rows)

# ================================================================== P3 exact k-leaf out-branching
class OutBranchSpec(MSpec):
    def __init__(s, n, A, r, U):
        s.n, s.edges, s.r, s.U = n, A, r, U
    def has(s, v, f): return v != s.r
    def estates(s, k): return [0, 1]
    def C(s, v, st, sig):
        out = sum(x for k, x in sig.items() if s.edges[k][0] == v)
        inn = sum(x for k, x in sig.items() if s.edges[k][1] == v)
        if inn != (0 if v == s.r else 1):
            return 0
        return s.U if out == 0 else 1
    def F(s, k, a, c, x):
        u, v = s.edges[k]
        return gadd(ONE, s.q_in(u, v, 0)) if x else ONE

def prob_outbranch(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(2 * n, min(n * (n - 1), 3 * n))
        A = rand_digraph(n, m, rng); r = rng.randrange(n)
        b = 40; U = 1 << b
        truth = [0] * (n + 1); target = 0
        into = {v: [k for k, a in enumerate(A) if a[1] == v] for v in range(n)}
        choices = [[None] if v == r else into[v] for v in range(n)]
        for ch in itertools.product(*choices):
            X = [A[k] for k in ch if k is not None]
            outd = [0] * n
            for i, j in X:
                outd[i] += 1
            leaves = sum(1 for v in range(n) if outd[v] == 0)
            if len(reach(n, X, r)) == n:
                truth[leaves] += 1
            target += U ** leaves * det_exact(minor(dlap(list(range(n)), X, "in"), {r}))
        got = kron_decode(target, b, n + 2)[:n + 1]
        sp = OutBranchSpec(n, A, r, U)
        net = check_network(sp, A, target, rng, Ks=(2, 3, 4), max_cross=7, max_inc=6)
        ok = got == truth and netok(net)
        rows.append((n, m, f"#outbranchings by leaves={truth[1:]}", short(net), ok))
    report("P3 exact k-leaf out-branching: sum_X u^{#leaves} det L_in^(r) = exact distribution", rows)

# ================================================================== P4 spanning trees, degree statistics
class DegTreeSpec(MSpec):
    def __init__(s, n, E, dmax, A, B, Zz):
        s.n, s.edges, s.dmax, s.A, s.B, s.Zz = n, E, dmax, A, B, Zz
        s.degG = [sum(1 for e in E if v in e) for v in range(n)]
    def has(s, v, f): return v != 0
    def estates(s, k): return [0, 1]
    def C(s, v, st, sig):
        d = sum(sig.values())
        if d > s.dmax:
            return 0
        return (s.A if d == s.degG[v] else 1) * (s.B if d >= 2 else 1)
    def F(s, k, a, c, x):
        u, v = s.edges[k]
        return gscale(gadd(ONE, s.q_und(u, v, 0)), s.Zz) if x else ONE

def prob_degtrees(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n + 1, min(n * (n - 1) // 2, 2 * n))
        E = rand_graph(n, m, rng)
        degG = [sum(1 for e in E if v in e) for v in range(n)]
        b = 40; Y = 1 << b
        A, B, Zz = Y, Y ** (n + 1), Y ** ((n + 1) ** 2)
        trees = []
        for X in itertools.combinations(range(m), n - 1):
            EX = [E[k] for k in X]
            if connected(range(n), EX):
                deg = [0] * n
                for i, j in EX:
                    deg[i] += 1; deg[j] += 1
                trees.append(deg)
        res = []
        for dmax in (2, 3, n):
            truth = {}
            for deg in trees:
                if max(deg) <= dmax:
                    key = (sum(1 for v in range(n) if deg[v] == degG[v]), sum(1 for d in deg if d >= 2))
                    truth[key] = truth.get(key, 0) + 1
            target = 0
            for r in range(m + 1):
                for X in itertools.combinations(range(m), r):
                    EX = [E[k] for k in X]
                    deg = [0] * n
                    for i, j in EX:
                        deg[i] += 1; deg[j] += 1
                    if max(deg) > dmax:
                        continue
                    w = 1
                    for v in range(n):
                        w *= (A if deg[v] == degG[v] else 1) * (B if deg[v] >= 2 else 1)
                    target += Zz ** r * w * tau(range(n), EX)
            dist = kron_decode(target, b, (n + 1) ** 2 * (m + 1) + 1)
            base = (n + 1) ** 2 * (n - 1)
            got = {}
            for f in range(n + 1):
                for i in range(n + 1):
                    c = dist[base + f + (n + 1) * i]
                    if c:
                        got[(f, i)] = c
            sp = DegTreeSpec(n, E, dmax, A, B, Zz)
            net = check_network(sp, E, target, rng, Ks=(2, 3), parts=1, max_cross=6, max_inc=5)
            res.append((dmax, got == truth and netok(net), short(net), truth))
        ok = all(x[1] for x in res)
        mfd = max((k[0] for k in res[2][3]), default=None)
        mis = max((k[1] for k in res[2][3]), default=None)
        dstar = next((d for d, okk, _, tr in res if tr), f">3 (or {max(max(t) for t in trees) if trees else None})")
        rows.append((n, m, f"maxFullDeg={mfd} maxInternal={mis} deg<=d exists from d={dstar}",
                     [x[2] for x in res], ok))
    report("P4 spanning trees: [z^{n-1}] sum_X z^|X| a^{#full} b^{#internal} [maxdeg<=d] tau(X)", rows)

# ================================================================== P5 directed k-paths / k-cycles
class DPathSpec(MSpec):
    def __init__(s, n, A, Wm, T, Zz):
        s.n, s.edges, s.Wm, s.T, s.Zz = n, A, Wm, T, Zz
    def vstates(s, v): return [0, 1]
    def estates(s, k): return [0, 1]
    def C(s, v, y, sig):
        out = sum(x for k, x in sig.items() if s.edges[k][0] == v)
        inn = sum(x for k, x in sig.items() if s.edges[k][1] == v)
        if not y:
            return 1 if out == inn == 0 else 0
        return s.T if (out, inn) in ((1, 1), (1, 0), (0, 1)) else 0
    def M(s, v, y): return s.mass(v, 0, s.Wm) if y else s.delete(v, 0)
    def F(s, k, a, c, x):
        if not x:
            return ONE
        if not (a and c):
            return ZERO
        u, v = s.edges[k]
        return gscale(gadd(ONE, s.q_out(u, v, 0)), s.Zz)

def dpaths_cycles(n, A):
    out = {v: [] for v in range(n)}
    for i, j in A:
        out[i].append(j)
    P = [0] * (n + 1); Cc = [0] * (n + 1)
    def dfs(s, v, seen, k):
        P[k] += 1 if k >= 2 else 0
        for u in out[v]:
            if u == s and k >= 2:
                Cc[k] += 1
            elif u not in seen:
                dfs(s, u, seen | {u}, k + 1)
    for s in range(n):
        dfs(s, s, {s}, 1)
    return P, [Cc[k] // k if k else 0 for k in range(n + 1)]

def prob_dpaths(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([4, 5]); m = rng.randint(n + 2, min(n * (n - 1), 2 * n + 1))
        A = rand_digraph(n, m, rng)
        b = 40; Y = 1 << b
        Wm, T, Zz = Y, Y ** (n + 1), Y ** ((n + 1) ** 2)
        P, Cy = dpaths_cycles(n, A)
        target = 0
        for r in range(n + 1):
            for X in itertools.combinations(range(m), r):
                AX = [A[k] for k in X]
                o = [0] * n; i_ = [0] * n
                for a, c in AX:
                    o[a] += 1; i_[c] += 1
                if max(o + i_) > 1:
                    continue
                S = [v for v in range(n) if o[v] + i_[v] > 0]
                target += T ** len(S) * Zz ** r * det_exact(add_diag(dlap(S, AX, "out"), Wm))
        dist = kron_decode(target, b, (n + 1) ** 2 * (n + 2))
        gp = [dist[1 + (n + 1) * k + (n + 1) ** 2 * (k - 1)] if k >= 1 else 0 for k in range(n + 1)]
        gc = [dist[1 + (n + 1) * k + (n + 1) ** 2 * k] for k in range(n + 1)]
        ok1 = all(gp[k] == P[k] for k in range(2, n + 1)) and all(gc[k] == k * Cy[k] for k in range(2, n + 1))
        sp = DPathSpec(n, A, Wm, T, Zz)
        net = check_network(sp, A, target, rng, Ks=(2, 3), max_cross=6, max_inc=5)
        ok = ok1 and netok(net)
        lp = max(k for k in range(n + 1) if P[k] or k == 1)
        lc = max((k for k in range(2, n + 1) if Cy[k]), default=0)
        rows.append((n, m, f"paths={P[2:]} cycles={Cy[2:]} longest path={lp} cycle={lc}", short(net), ok))
    report("P5 directed k-paths / k-cycles: [w^1 t^k z^{k-1}] = #P_k, [w^1 t^k z^k] = k #C_k", rows)

# ================================================================== P6 graph-metric TSP (closed walks)
class WalkSpec(MSpec):
    def __init__(s, n, E, lens, Zz):
        s.n, s.edges, s.lens, s.Zz = n, E, lens, Zz
    def has(s, v, f): return v != 0
    def estates(s, k): return [0, 1, 2]
    def C(s, v, st, sig): return 1 if sum(sig.values()) % 2 == 0 else 0
    def F(s, k, a, c, x):
        if not x:
            return ONE
        u, v = s.edges[k]
        return gscale(gadd(ONE, s.q_und(u, v, 0)), s.Zz ** (x * s.lens[k]))

def metric_tsp(n, E, lens):
    INF = 10 ** 9
    d = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for (i, j), l in zip(E, lens):
        d[i][j] = min(d[i][j], l); d[j][i] = min(d[j][i], l)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                d[i][j] = min(d[i][j], d[i][k] + d[k][j])
    best = INF
    for p in itertools.permutations(range(1, n)):
        tour = (0,) + p + (0,)
        best = min(best, sum(d[tour[t]][tour[t + 1]] for t in range(n)))
    return best

def prob_walk(rng, trials):
    rows = []
    for t in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n, min(n * (n - 1) // 2, n + 3))
        E = rand_graph(n, m, rng)
        lens = [1] * m if t % 2 == 0 else [rng.randint(1, 3) for _ in E]
        b = 40; Zz = 1 << b
        truth = metric_tsp(n, E, lens)
        target = 0
        for xs in itertools.product((0, 1, 2), repeat=m):
            deg = [0] * n
            for (i, j), x in zip(E, xs):
                deg[i] += x; deg[j] += x
            if any(d % 2 for d in deg):
                continue
            supp = [E[k] for k in range(m) if xs[k]]
            target += Zz ** sum(x * l for x, l in zip(xs, lens)) * tau(range(n), supp)
        dist = kron_decode(target, b, 2 * 3 * m + 2)
        opt = next(k for k, c in enumerate(dist) if c)
        sp = WalkSpec(n, E, lens, Zz)
        net = check_network(sp, E, target, rng, Ks=(2, 3), max_cross=5, max_inc=4)
        ok = opt == truth and netok(net)
        rows.append((n, m, f"{'graph metric' if t % 2 == 0 else 'weights 1..3'} TSP walk={truth} lowest power={opt}",
                     short(net), ok))
    report("P6 graph-metric TSP: lowest z-power of sum_{x in {0,1,2}^E, even} z^{w(x)} tau(supp x)", rows)

# ================================================================== P7 min cycle cover
class CycleCoverSpec(MSpec):
    def __init__(s, n, E, directed, Wm):
        s.n, s.edges, s.directed, s.Wm = n, E, directed, Wm
    def estates(s, k): return [0, 1]
    def C(s, v, st, sig):
        if s.directed:
            out = sum(x for k, x in sig.items() if s.edges[k][0] == v)
            inn = sum(x for k, x in sig.items() if s.edges[k][1] == v)
            return int(out == 1 and inn == 1)
        return int(sum(sig.values()) == 2)
    def M(s, v, st): return s.mass(v, 0, s.Wm)
    def F(s, k, a, c, x):
        if not x:
            return ONE
        u, v = s.edges[k]
        return gadd(ONE, s.q_out(u, v, 0) if s.directed else s.q_und(u, v, 0))

def planted(n, rng, directed, extra, mincuts=0):
    while True:
        perm = list(range(n)); rng.shuffle(perm)
        cuts = sorted(rng.sample(range(1, n), rng.randint(mincuts, 2)))
        parts = [perm[a:b] for a, b in zip([0] + cuts, cuts + [n])]
        if all(len(p) >= (2 if directed else 3) for p in parts):
            break
    E = set()
    for p in parts:
        for t in range(len(p)):
            a, c = p[t], p[(t + 1) % len(p)]
            E.add((a, c) if directed else (min(a, c), max(a, c)))
    allp = [(i, j) for i in range(n) for j in range(n) if i != j] if directed else \
           [(i, j) for i in range(n) for j in range(i + 1, n)]
    rest = [e for e in allp if e not in E]
    E |= set(rng.sample(rest, min(extra, len(rest))))
    return sorted(E)

def prob_cyclecover(rng, trials, directed):
    rows = []
    for t in range(trials):
        n = rng.choice([6, 7]) if not directed else rng.choice([4, 5, 6])
        # odd trials: >= 2 planted cycles and few extra edges, so that min #cycles > 1 occurs
        E = planted(n, rng, directed, rng.randint(2, 5) if t % 2 == 0 else rng.randint(0, 2),
                    mincuts=t % 2); m = len(E)
        b = 48; Wm = 1 << b
        covers = []
        for r in [n]:
            for X in itertools.combinations(range(m), r):
                EX = [E[k] for k in X]
                if directed:
                    o = [0] * n; i_ = [0] * n
                    for a, c in EX:
                        o[a] += 1; i_[c] += 1
                    if o != [1] * n or i_ != [1] * n:
                        continue
                else:
                    deg = [0] * n
                    for a, c in EX:
                        deg[a] += 1; deg[c] += 1
                    if deg != [2] * n:
                        continue
                covers.append(EX)
        cmin = None; wsum = 0; target = 0
        for EX in covers:
            comps, _ = components(range(n), EX)
            c = len(comps)
            wt = math.prod(len(C) ** (1 if directed else 2) for C in comps)
            if cmin is None or c < cmin:
                cmin, wsum = c, wt
            elif c == cmin:
                wsum += wt
            L = dlap(list(range(n)), EX, "out") if directed else laplacian(list(range(n)), EX)
            target += det_exact(add_diag(L, Wm))
        dist = kron_decode(target, b, n + 2)
        low = next((k for k, c in enumerate(dist) if c), None)
        sp = CycleCoverSpec(n, E, directed, Wm)
        net = check_network(sp, E, target, rng, Ks=(2, 3), max_cross=7, max_inc=6)
        ok = low == cmin and dist[low] == wsum and netok(net)
        rows.append((n, m, f"#covers={len(covers)} min #cycles={cmin} lowest w-power={low} coef={dist[low]}",
                     short(net), ok))
    nm = "directed" if directed else "undirected"
    report(f"P7 min cycle cover ({nm}): lowest power of sum_X det(L_X + wI) = min #cycles; "
           f"coef = sum prod l_i^{1 if directed else 2}", rows)

# ================================================================== P8 two edge-disjoint spanning trees
class TwoTreeSpec(MSpec):
    nf = 2
    def __init__(s, n, E, Z1, Z2):
        s.n, s.edges, s.Z1, s.Z2 = n, E, Z1, Z2
    def has(s, v, f): return v != 0
    def estates(s, k): return [0, 1, 2]
    def F(s, k, a, c, x):
        u, v = s.edges[k]
        if x == 1:
            return gscale(gadd(ONE, s.q_und(u, v, 0)), s.Z1)
        if x == 2:
            return gscale(gadd(ONE, s.q_und(u, v, 1)), s.Z2)
        return ONE

def prob_twotrees(rng, trials):
    rows = []
    for _ in range(trials):
        n = 5; m = rng.randint(8, 10)
        E = rand_graph(n, m, rng)
        b = 32; Y = 1 << b; Z1, Z2 = Y, Y ** (m + 1)
        trees = [set(X) for X in itertools.combinations(range(m), n - 1)
                 if connected(range(n), [E[k] for k in X])]
        truth = sum(1 for A in trees for B in trees if not A & B)
        target = 0
        for xs in itertools.product((0, 1, 2), repeat=m):
            E1 = [E[k] for k in range(m) if xs[k] == 1]
            E2 = [E[k] for k in range(m) if xs[k] == 2]
            t1 = tau(range(n), E1)
            if t1 == 0:
                continue
            target += Z1 ** len(E1) * Z2 ** len(E2) * t1 * tau(range(n), E2)
        dist = kron_decode(target, b, (m + 1) ** 2 + 1)
        got = dist[(n - 1) + (m + 1) * (n - 1)]
        sp = TwoTreeSpec(n, E, Z1, Z2)
        net = check_network(sp, E, target, rng, Ks=(2, 3), max_cross=5, max_inc=4)
        ok = got == truth and netok(net)
        rows.append((n, m, f"#ordered disjoint tree pairs={truth}", short(net), ok))
    report("P8 two edge-disjoint spanning trees: [z1^{n-1} z2^{n-1}] sum tau(X1) tau(X2)", rows)

# ================================================================== P9 min strongly connected spanning subgraph
class StrongSpec(MSpec):
    nf = 2
    def __init__(s, n, A, Zz):
        s.n, s.edges, s.Zz = n, A, Zz
    def has(s, v, f): return v != 0
    def estates(s, k): return [0, 1]
    def F(s, k, a, c, x):
        if not x:
            return ONE
        u, v = s.edges[k]
        return gscale(gmul(gadd(ONE, s.q_out(u, v, 0)), gadd(ONE, s.q_in(u, v, 1))), s.Zz)

def prob_strong(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([4, 5])
        while True:
            m = rng.randint(n + 2, min(n * (n - 1), 2 * n + 1))
            A = rand_digraph(n, m, rng)
            if len(reach(n, A, 0)) == n and len(reach(n, A, 0, rev=True)) == n:
                break
        b = 40; Zz = 1 << b
        best = None; target = 0; cnt = 0
        for r in range(m + 1):
            for X in itertools.combinations(range(m), r):
                AX = [A[k] for k in X]
                strong = len(reach(n, AX, 0)) == n and len(reach(n, AX, 0, rev=True)) == n
                if strong and best is None:
                    best = r
                d = det_exact(minor(dlap(list(range(n)), AX, "out"), {0}))
                if d:
                    d *= det_exact(minor(dlap(list(range(n)), AX, "in"), {0}))
                assert (d != 0) == strong
                target += Zz ** r * d
        dist = kron_decode(target, b, m + 2)
        low = next(k for k, c in enumerate(dist) if c)
        sp = StrongSpec(n, A, Zz)
        net = check_network(sp, A, target, rng, Ks=(2, 3), max_cross=6, max_inc=5)
        ok = low == best and netok(net)
        rows.append((n, m, f"MSCS={best} (n={n}) lowest power={low}", short(net), ok))
    report("P9 min strongly connected spanning subgraph: sum_X z^|X| det L_out^(r) det L_in^(r)", rows)


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    which = sys.argv[3].split(",") if len(sys.argv) > 3 else None
    rng = random.Random(seed)
    jobs = [("p1", lambda: prob_cfvs(rng, trials)), ("p2", lambda: prob_coct(rng, trials)),
            ("p3", lambda: prob_outbranch(rng, trials)), ("p4", lambda: prob_degtrees(rng, trials)),
            ("p5", lambda: prob_dpaths(rng, trials)), ("p6", lambda: prob_walk(rng, trials)),
            ("p7", lambda: prob_cyclecover(rng, trials, False)),
            ("p7d", lambda: prob_cyclecover(rng, trials, True)),
            ("p8", lambda: prob_twotrees(rng, trials)), ("p9", lambda: prob_strong(rng, trials))]
    for name, f in jobs:
        if which is None or name in which:
            f()
    print("ALL OK" if ALL_OK else "SOME FAILURE")
