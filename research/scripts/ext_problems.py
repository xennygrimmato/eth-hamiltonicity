"""Extensions of the fermionic matrix-tree blob network (see research/exact-extensions.md).

For every problem: (1) brute-force combinatorial ground truth, (2) the exact identity
(local constraints x determinant), evaluated by explicit determinants, (3) the blob network
(ext_engine) on random blob partitions.  All arithmetic exact.  Polynomial generating
functions are carried by Kronecker substitution Y = 2^b (balanced digits).

Run: python3 ext_problems.py [seed] [trials-per-problem]
"""
import itertools, random, sys, math
from fractions import Fraction
from ext_engine import (Spec, ONE, ZERO, gmul, gadd, gscale, gexp, det_exact, kron_decode,
                        network_value, random_blobs, crossing_ok)

# ================================================================== graph utilities
def rand_graph(n, m, rng, connected=True):
    allp = [(i, j) for i in range(n) for j in range(i + 1, n)]
    while True:
        E = sorted(rng.sample(allp, m))
        if not connected:
            return E
        adj = {v: set() for v in range(n)}
        for i, j in E:
            adj[i].add(j); adj[j].add(i)
        seen = {0}; st = [0]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y); st.append(y)
        if len(seen) == n:
            return E

def rand_digraph(n, m, rng):
    allp = [(i, j) for i in range(n) for j in range(n) if i != j]
    return sorted(rng.sample(allp, m))

def components(vs, E):
    par = {v: v for v in vs}
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    cyc = False
    for i, j in E:
        a, b = f(i), f(j)
        if a == b:
            cyc = True
        else:
            par[a] = b
    comps = {}
    for v in vs:
        comps.setdefault(f(v), set()).add(v)
    return list(comps.values()), cyc

def laplacian(vs, E, w=None, directed=False):
    idx = {v: t for t, v in enumerate(vs)}
    L = [[0] * len(vs) for _ in vs]
    for t, (i, j) in enumerate(E):
        c = 1 if w is None else w[t]
        a, b = idx[i], idx[j]
        if directed:   # arc i->j: L = D_out - A
            L[a][a] += c; L[a][b] -= c
        else:
            L[a][a] += c; L[b][b] += c; L[a][b] -= c; L[b][a] -= c
    return L

def minor(L, drop):
    keep = [t for t in range(len(L)) if t not in drop]
    return [[L[r][c] for c in keep] for r in keep]

def tau(vs, E, root=None):
    vs = list(vs)
    if not vs:
        return 0
    L = laplacian(vs, E)
    r = 0 if root is None else vs.index(root)
    return det_exact(minor(L, {r}))

# ================================================================== ground truths
def hc_list(n, E, directed=False):
    adj = {v: [] for v in range(n)}
    for t, (i, j) in enumerate(E):
        adj[i].append((j, t))
        if not directed:
            adj[j].append((i, t))
    out = []
    def dfs(v, seen, path):
        if len(path) == n - 1:
            for (u, t) in adj[v]:
                if u == 0 and (directed or n > 2):
                    out.append(path + [t])
            return
        for (u, t) in adj[v]:
            if not seen >> u & 1:
                dfs(u, seen | 1 << u, path + [t])
    dfs(0, 1, [])
    if directed:
        return [frozenset(c) for c in out]
    return list({frozenset(c) for c in out})

def ham_paths(n, E, directed=False):
    """list of (start, end, edge-set) of Hamiltonian paths; undirected paths once."""
    adj = {v: [] for v in range(n)}
    for t, (i, j) in enumerate(E):
        adj[i].append((j, t))
        if not directed:
            adj[j].append((i, t))
    res = set()
    def dfs(s, v, seen, path):
        if bin(seen).count("1") == n:
            if directed:
                res.add((s, v, frozenset(path)))
            else:
                res.add((min(s, v), max(s, v), frozenset(path)))
            return
        for (u, t) in adj[v]:
            if not seen >> u & 1:
                dfs(s, u, seen | 1 << u, path + [t])
    for s in range(n):
        dfs(s, s, 1 << s, [])
    return res

# ================================================================== problem specs
class DegSpec(Spec):
    """x_e in {0,1} visible; C_v = cons(v, deg) (undirected) or cons(v, outdeg, indeg)."""
    def __init__(s, n, E, cons, root, directed=False, eweight=None, mass=None):
        s.n, s.edges, s.cons, s.root, s.directed = n, E, cons, root, directed
        s.eweight = eweight or (lambda k: 1)
        s.mass = mass   # optional per-vertex mass weight w: M_v = 1 + w psibar psi
        s.inc = [s_ for s_ in [None]]
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def gens(s, v): return v != s.root
    def incident(s, v): return s._inc[v]
    def estates(s, k): return [0, 1]
    def C(s, v, st, sig):
        if s.directed:
            out = sum(x for k, x in sig.items() if s.edges[k][0] == v)
            inn = sum(x for k, x in sig.items() if s.edges[k][1] == v)
            return s.cons(v, out, inn)
        return s.cons(v, sum(sig.values()))
    def M(s, v, st):
        if s.mass is None:
            return ONE
        return gadd(ONE, gscale(s.pbps(v), s.mass(v)))
    def F(s, k, su, sv, x):
        if x == 0:
            return ONE
        u, v = s.edges[k]
        q = s.q_arc(u, v) if s.directed else s.q_undirected(u, v)
        return gscale(gadd(ONE, q), s.eweight(k))

def check_network(spec, n, E, target, rng, label, trials=3, max_cross=7, max_inc=6, Ks=(2, 3, 4)):
    res = []
    for K in Ks:
        if K > n:
            continue
        for _ in range(60):
            bl = random_blobs(n, K, rng)
            if crossing_ok(E, bl, max_cross, max_inc):
                break
        else:
            continue
        Z, bits, _ = network_value(spec, bl)
        ok = (Z == target)
        res.append((K, len(bits), max(bits.values()) if bits else 0, ok))
        if not ok:
            print(f"   !! {label} K={K} blob={bl} Z={Z} target={target}")
    return res

ALL_OK = True
def report(name, rows):
    global ALL_OK
    ok = all(r[-1] for r in rows)
    ALL_OK &= ok
    print(f"{name}: {'OK' if ok else 'FAIL'}  " + "; ".join(str(r) for r in rows))

# ------------------------------------------------------------------ 0. undirected HC (baseline)
def prob_hc(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6, 7]); m = rng.randint(n + 2, min(n * (n - 1) // 2, 2 * n))
        E = rand_graph(n, m, rng)
        hc = len(hc_list(n, E))
        sp = DegSpec(n, E, lambda v, d: int(d == 2), root=0)
        # identity: sum_{2-factors} tau
        idt = sum(tau(range(n), [E[k] for k in X]) for X in subsets_deg(n, E, lambda v, d: d == 2))
        net = check_network(sp, n, E, n * hc, rng, "HC")
        rows.append((n, m, hc, idt == n * hc, net))
    flat = [(r[0], r[2], r[3] and all(x[-1] for x in r[4]), [x[:3] for x in r[4]]) for r in rows]
    report("HC (baseline)  n#HC = sum_2f tau", [f + (f[2],) for f in flat])

def subsets_deg(n, E, pred, directed=False):
    """all edge subsets X (as index lists) with pred(v, deg) (undirected) / pred(v,out,in)."""
    out = []
    deg = [0] * n; di = [0] * n
    def rec(k, ch):
        if k == len(E):
            if directed:
                if all(pred(v, deg[v], di[v]) for v in range(n)):
                    out.append(list(ch))
            elif all(pred(v, deg[v]) for v in range(n)):
                out.append(list(ch))
            return
        rec(k + 1, ch)
        i, j = E[k]
        if directed:
            deg[i] += 1; di[j] += 1
        else:
            deg[i] += 1; deg[j] += 1
        if max(deg) <= n and max(di) <= n:
            ch.append(k); rec(k + 1, ch); ch.pop()
        if directed:
            deg[i] -= 1; di[j] -= 1
        else:
            deg[i] -= 1; deg[j] -= 1
    rec(0, [])
    return out

# ------------------------------------------------------------------ 1. directed HC
def prob_dhc(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([4, 5, 6]); m = rng.randint(2 * n, min(n * (n - 1), 3 * n))
        E = rand_digraph(n, m, rng)
        truth = len(hc_list(n, E, directed=True))
        cons = lambda v, o, i: int(o == 1 and i == 1)
        idt = 0
        for X in subsets_deg(n, E, cons, directed=True):
            L = laplacian(list(range(n)), [E[k] for k in X], directed=True)
            idt += det_exact(minor(L, {0}))
        sp = DegSpec(n, E, cons, root=0, directed=True)
        net = check_network(sp, n, E, truth, rng, "DHC")
        rows.append((n, m, truth, [x[:3] for x in net], idt == truth and all(x[-1] for x in net)))
    report("1  directed HC  #DHC = sum_{cycle covers} det L_out^(r)", rows)

# ------------------------------------------------------------------ 2. TSP via Kronecker
def prob_tsp(rng, trials, directed=False):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]) if not directed else rng.choice([4, 5])
        m = rng.randint(n + 3, min(n * (n - 1) // (1 if directed else 2), 2 * n + 1))
        E = rand_digraph(n, m, rng) if directed else rand_graph(n, m, rng)
        W = 5
        w = [rng.randint(1, W) for _ in E]
        b = 64; Y = 1 << b
        cyc = hc_list(n, E, directed=directed)
        mult = 1 if directed else n
        target = sum(mult * Y ** sum(w[k] for k in H) for H in cyc)
        if directed:
            cons = lambda v, o, i: int(o == 1 and i == 1)
        else:
            cons = lambda v, d: int(d == 2)
        sp = DegSpec(n, E, cons, root=0, directed=directed, eweight=lambda k: Y ** w[k])
        net = check_network(sp, n, E, target, rng, "TSP", Ks=(2, 3))
        dist = kron_decode(target, b, n * W + 2)
        opt = next((d for d, c in enumerate(dist) if c), None)
        truth_opt = min((sum(w[k] for k in H) for H in cyc), default=None)
        nopt = sum(1 for H in cyc if sum(w[k] for k in H) == truth_opt) if cyc else 0
        ok = (opt == truth_opt) and (not cyc or dist[opt] == mult * nopt) and all(x[-1] for x in net)
        rows.append((n, m, f"opt={opt} #opt={dist[opt] // mult if opt is not None else 0}",
                     [x[:3] for x in net], ok))
    report(f"2  {'A' if directed else ''}TSP generating fn  sum_H z^w(H) (Kronecker)", rows)

# ------------------------------------------------------------------ 3. Hamiltonian paths
def prob_paths(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6, 7]); m = rng.randint(n + 1, min(n * (n - 1) // 2, 2 * n))
        E = rand_graph(n, m, rng)
        HP = ham_paths(n, E)
        s, t = rng.sample(range(n), 2)
        st_truth = sum(1 for (a, c, P) in HP if {a, c} == {s, t})
        cons = lambda v, d: int(d == (1 if v in (s, t) else 2))
        sp = DegSpec(n, E, cons, root=s)
        net1 = check_network(sp, n, E, st_truth, rng, "HPst", Ks=(2, 3))
        idt1 = sum(tau(range(n), [E[k] for k in X], root=s) for X in subsets_deg(n, E, cons))
        # any Hamiltonian path: deg<=2, z per edge, [z^{n-1}]
        b = 40; Y = 1 << b
        hc = len(hc_list(n, E))
        target = len(HP) * Y ** (n - 1) + n * hc * Y ** n
        sp2 = DegSpec(n, E, lambda v, d: int(d <= 2), root=0, eweight=lambda k: Y)
        net2 = check_network(sp2, n, E, target, rng, "HPany", Ks=(2, 3))
        ok = idt1 == st_truth and all(x[-1] for x in net1 + net2)
        rows.append((n, m, f"st={st_truth} all={len(HP)}", [x[:3] for x in net1 + net2], ok))
    report("3a Ham s-t paths (deg 1 at s,t) and all HP ([z^{n-1}] of deg<=2)", rows)
    rows = []
    for _ in range(trials):
        n = rng.choice([4, 5, 6]); m = rng.randint(2 * n, min(n * (n - 1), 3 * n))
        E = rand_digraph(n, m, rng)
        HP = ham_paths(n, E, directed=True)
        s, t = rng.sample(range(n), 2)
        truth = sum(1 for (a, c, P) in HP if (a, c) == (s, t))
        def cons(v, o, i):
            if v == s: return int(o == 1 and i == 0)
            if v == t: return int(o == 0 and i == 1)
            return int(o == 1 and i == 1)
        sp = DegSpec(n, E, cons, root=t, directed=True)
        net = check_network(sp, n, E, truth, rng, "DHPst", Ks=(2, 3))
        rows.append((n, m, truth, [x[:3] for x in net], all(x[-1] for x in net)))
    report("3b directed Ham s->t paths (root t)", rows)

# ------------------------------------------------------------------ 4a. spanning trees, leaf distribution
def prob_leaves(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n + 1, min(n * (n - 1) // 2, 2 * n))
        E = rand_graph(n, m, rng)
        b = 48; Y = 1 << b
        U, Zz = Y, Y ** (n + 1)
        # identity side: sum over all X of z^|X| u^{#deg1} tau(X)
        target = 0; truth = [0] * (n + 1)
        for r in range(m + 1):
            for X in itertools.combinations(range(m), r):
                EX = [E[k] for k in X]
                deg = [0] * n
                for i, j in EX:
                    deg[i] += 1; deg[j] += 1
                lv = sum(1 for d in deg if d == 1)
                tv = tau(range(n), EX)
                target += Zz ** r * U ** lv * int(tv)
                if r == n - 1:
                    comps, cyc = components(range(n), EX)
                    if len(comps) == 1:
                        truth[lv] += 1
        dist = kron_decode(target, b, (m + 1) * (n + 1) + 1)
        got = dist[(n - 1) * (n + 1):(n - 1) * (n + 1) + n + 1]
        sp = DegSpec(n, E, lambda v, d: U if d == 1 else 1, root=0, eweight=lambda k: Zz)
        net = check_network(sp, n, E, target, rng, "leaves", Ks=(2, 3), max_cross=6)
        ok = got == truth and all(x[-1] for x in net)
        rows.append((n, m, f"leafdist={truth[1:]}", [x[:3] for x in net], ok))
    report("4a spanning trees by #leaves: [z^{n-1}] sum_X z^|X| u^{#deg1} tau(X)", rows)

# ------------------------------------------------------------------ 4b. Steiner trees
class SteinerSpec(Spec):
    def __init__(s, n, E, term, root, ew):
        s.n, s.edges, s.term, s.root, s.ew = n, E, set(term), root, ew
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def incident(s, v): return s._inc[v]
    def gens(s, v): return v != s.root
    def vstates(s, v): return [1] if v in s.term else [0, 1]
    def M(s, v, y): return ONE if y else s.pbps(v)
    def F(s, k, yu, yv, sig):
        if not (yu and yv):
            return ONE
        u, v = s.edges[k]
        return gadd(ONE, gscale(s.q_undirected(u, v), s.ew(k)))

def subtrees(n, E, term):
    res = []
    term = set(term)
    for r in range(len(E) + 1):
        for X in itertools.combinations(range(len(E)), r):
            EX = [E[k] for k in X]
            Vs = set(term) | {x for e in EX for x in e}
            comps, cyc = components(Vs, EX)
            if not cyc and len(comps) == 1:
                res.append(X)
    return res

def prob_steiner(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([6, 7]); m = rng.randint(n, min(n * (n - 1) // 2, 2 * n - 1))
        E = rand_graph(n, m, rng)
        term = rng.sample(range(n), rng.choice([2, 3]))
        w = [rng.randint(1, 4) for _ in E]
        b = 40; Y = 1 << b
        trees = subtrees(n, E, term)
        target = sum(Y ** sum(w[k] for k in X) for X in trees)
        # identity: sum_{S >= term} det of weighted reduced Laplacian of G[S]
        idt = 0
        others = [v for v in range(n) if v not in term]
        for r in range(len(others) + 1):
            for A in itertools.combinations(others, r):
                Sset = sorted(set(term) | set(A))
                ES = [(t, e) for t, e in enumerate(E) if e[0] in Sset and e[1] in Sset]
                L = laplacian(Sset, [e for t, e in ES], w=[Y ** w[t] for t, e in ES])
                idt += det_exact(minor(L, {Sset.index(term[0])}))
        sp = SteinerSpec(n, E, term, term[0], lambda k: Y ** w[k])
        net = check_network(sp, n, E, target, rng, "steiner", Ks=(2, 3))
        dist = kron_decode(target, b, 4 * m + 2)
        opt = next(d for d, c in enumerate(dist) if c)
        ok = idt == target and all(x[-1] for x in net)
        rows.append((n, m, f"#subtrees={len(trees)} optw={opt} #opt={dist[opt]}", [x[:3] for x in net], ok))
    report("4b Steiner trees: sum_{S>=T} det L_w(G[S])^(t0) = sum_{subtrees>=T} z^w", rows)

# ------------------------------------------------------------------ 4c. connected vertex cover / connected dominating set
class ConnSpec(Spec):
    """states y (and domination flag d for CDS). Mass term w on S (no root): [w^1] det(L_S+wI)
    = |S| tau(G[S]).  t^{|S|} in C."""
    def __init__(s, n, E, kind, Wm, T):
        s.n, s.edges, s.kind, s.Wm, s.T = n, E, kind, Wm, T
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def incident(s, v): return s._inc[v]
    def vstates(s, v):
        return [(0, 0), (1, 0)] if s.kind == "cvc" else [(0, 0), (1, 0), (0, 1)]
    def C(s, v, st, sig):
        y, d = st
        return (s.T if y else 1) * (-1 if d else 1)
    def M(s, v, st):
        return gadd(ONE, gscale(s.pbps(v), s.Wm)) if st[0] else s.pbps(v)
    def F(s, k, su, sv, sig):
        (yu, du), (yv, dv) = su, sv
        if s.kind == "cvc" and not (yu or yv):
            return ZERO
        if s.kind == "cds" and ((du and yv) or (dv and yu)):
            return ZERO
        if yu and yv:
            u, v = s.edges[k]
            return gadd(ONE, s.q_undirected(u, v))
        return ONE

def prob_conn(rng, trials, kind):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n, min(n * (n - 1) // 2, 2 * n - 1))
        E = rand_graph(n, m, rng)
        adj = {v: set() for v in range(n)}
        for i, j in E:
            adj[i].add(j); adj[j].add(i)
        b = 48; Y = 1 << b
        Wm, T = Y, Y ** (n + 1)
        target = 0; best = None; tr = [0] * (n + 1)
        for r in range(n + 1):
            for S in itertools.combinations(range(n), r):
                Ss = set(S)
                if kind == "cvc":
                    good = all(i in Ss or j in Ss for i, j in E)
                else:
                    good = all(v in Ss or adj[v] & Ss for v in range(n))
                if not good:
                    continue
                ES = [e for e in E if e[0] in Ss and e[1] in Ss]
                L = laplacian(sorted(Ss), ES)
                for t_ in range(len(L)):
                    L[t_][t_] += Wm
                target += T ** r * det_exact(L)
                if Ss:
                    comps, _ = components(sorted(Ss), ES)
                    if len(comps) == 1:
                        tr[r] += r * int(tau(sorted(Ss), ES))
                        best = r if best is None else min(best, r)
        dist = kron_decode(target, b, (n + 1) * (n + 1) + 1)
        got = [dist[1 + (n + 1) * k] for k in range(n + 1)]
        opt = next((k for k, c in enumerate(got) if c), None)
        sp = ConnSpec(n, E, kind, Wm, T)
        net = check_network(sp, n, E, target, rng, kind, Ks=(2, 3), max_cross=6)
        ok = got == tr and opt == best and all(x[-1] for x in net)
        rows.append((n, m, f"min={opt}", [x[:3] for x in net], ok))
    nm = "connected vertex cover" if kind == "cvc" else "connected dominating set"
    report(f"4c {nm}: [w^1 t^k] sum_S [local] t^|S| det(L_S + w I) = k sum tau", rows)

# ------------------------------------------------------------------ 4d. induced forests (FVS) and all forests
class ForestSpec(Spec):
    """[forest] = 2^{|E(S)|-|S|} [z^{|S|-|E(S)|}] det(L_S + z diag(2 - deg_S)).
    induced=True: states y (S = induced vertex set);  induced=False: S=V, edges x free."""
    def __init__(s, n, E, induced, Zv, T):
        s.n, s.edges, s.induced, s.Zv, s.T = n, E, induced, Zv, T
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def incident(s, v): return s._inc[v]
    def vstates(s, v): return [0, 1] if s.induced else [1]
    def C(s, v, y, sig):
        return (s.T if y else 2 * s.Zv) if s.induced else 1
    def M(s, v, y):
        return gadd(ONE, gscale(s.pbps(v), 2 * s.Zv)) if y else s.pbps(v)
    def efac(s, k):
        u, v = s.edges[k]
        X = gadd(s.q_undirected(u, v), gscale(gadd(s.pbps(u), s.pbps(v)), -s.Zv))
        return gscale(gexp(X), 2 * s.Zv)
    def F(s, k, yu, yv, sig):
        if not (yu and yv):
            return ONE
        if s.induced:
            return s.efac(k)
        return gadd(ONE, gscale(s.efac(k), s.T))

def prob_forest(rng, trials, induced):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n, min(n * (n - 1) // 2, 2 * n))
        E = rand_graph(n, m, rng)
        b = 80; Y = 1 << b
        tdeg = n if induced else m
        T, Zv = Y, Y ** (tdeg + 1)
        truth = [0] * (tdeg + 1)
        target = 0
        if induced:
            for r in range(n + 1):
                for S in itertools.combinations(range(n), r):
                    Ss = sorted(S); ES = [e for e in E if e[0] in S and e[1] in S]
                    _, cyc = components(Ss, ES)
                    if not cyc:
                        truth[r] += 1
                    L = laplacian(Ss, ES)
                    deg = {v: 0 for v in Ss}
                    for i, j in ES:
                        deg[i] += 1; deg[j] += 1
                    for t_, v in enumerate(Ss):
                        L[t_][t_] += Zv * (2 - deg[v])
                    target += T ** r * 2 ** (len(ES) + n - r) * Zv ** (n - r + len(ES)) * det_exact(L)
        else:
            for r in range(m + 1):
                for X in itertools.combinations(range(m), r):
                    EX = [E[k] for k in X]
                    _, cyc = components(range(n), EX)
                    if not cyc:
                        truth[r] += 1
                    L = laplacian(list(range(n)), EX)
                    deg = [0] * n
                    for i, j in EX:
                        deg[i] += 1; deg[j] += 1
                    for v in range(n):
                        L[v][v] += Zv * (2 - deg[v])
                    target += T ** r * 2 ** r * Zv ** r * det_exact(L)
        dist = kron_decode(target, b, (tdeg + 1) * (n + m + 2) + 1)
        got = dist[n * (tdeg + 1): n * (tdeg + 1) + tdeg + 1]
        got = [Fraction(g, 2 ** n) for g in got]
        sp = ForestSpec(n, E, induced, Zv, T)
        net = check_network(sp, n, E, target, rng, "forest", Ks=(2, 3), max_cross=6)
        ok = got == truth and all(x[-1] for x in net)
        if induced:
            fvs = n - max(k for k, c in enumerate(truth) if c)
            info = f"minFVS={fvs} #min={truth[n - fvs]}"
        else:
            info = f"#forests={sum(truth)}"
        rows.append((n, m, info, [x[:3] for x in net], ok))
    nm = "induced forests / FVS (by size)" if induced else "all forests T_G(2,1) (by #edges)"
    report(f"4d {nm}: 2-deg mass trick", rows)

# ------------------------------------------------------------------ 4e. Steiner forest, two pairs (colours)
class SFSpec(Spec):
    def __init__(s, n, E, col, roots, ncol, ew):
        s.n, s.edges, s.col, s.roots, s.ncol, s.ew = n, E, col, set(roots), ncol, ew
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def incident(s, v): return s._inc[v]
    def gens(s, v): return v not in s.roots
    def vstates(s, v): return [s.col[v]] if v in s.col else list(range(s.ncol + 1))
    def M(s, v, c): return ONE if c else s.pbps(v)
    def F(s, k, cu, cv, sig):
        if cu and cu == cv:
            u, v = s.edges[k]
            return gadd(ONE, gscale(s.q_undirected(u, v), s.ew(k)))
        return ONE

def prob_steiner_forest(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([6, 7]); m = rng.randint(n, min(n * (n - 1) // 2, 2 * n - 1))
        E = rand_graph(n, m, rng)
        s1, t1, s2, t2 = rng.sample(range(n), 4)
        w = [rng.randint(1, 3) for _ in E]
        b = 40; Y = 1 << b
        target = 0
        for r in range(m + 1):
            for X in itertools.combinations(range(m), r):
                EX = [E[k] for k in X]
                Vs = {s1, t1, s2, t2} | {x for e in EX for x in e}
                comps, cyc = components(Vs, EX)
                if cyc:
                    continue
                cid = {v: i for i, C in enumerate(comps) for v in C}
                if cid[s1] != cid[t1] or cid[s2] != cid[t2]:
                    continue
                if any(not (C & {s1, t1, s2, t2}) for C in comps):
                    continue
                target += Y ** sum(w[k] for k in X)
        Z = 0; netrows = []
        # partition {1}{2}: two colours, roots s1, s2 ; partition {12}: one colour, root s1
        for col, roots, nc in (({s1: 1, t1: 1, s2: 2, t2: 2}, (s1, s2), 2),
                               ({s1: 1, t1: 1, s2: 1, t2: 1}, (s1,), 1)):
            sp = SFSpec(n, E, col, roots, nc, lambda k: Y ** w[k])
            for K in (2, 3):
                for _ in range(60):
                    bl = random_blobs(n, K, rng)
                    if crossing_ok(E, bl, 6, 5):
                        break
                v, bits, _ = network_value(sp, bl)
                netrows.append((nc, K, max(bits.values()) if bits else 0, v))
        Zs = {}
        for nc, K, mb, v in netrows:
            Zs.setdefault(K, 0); Zs[K] += v
        ok = all(Zs[K] == target for K in Zs)
        dist = kron_decode(target, b, 3 * m + 2)
        opt = next((d for d, c in enumerate(dist) if c), None)
        rows.append((n, m, f"optw={opt} #opt={dist[opt] if opt is not None else 0}",
                     [(nc, K, mb) for nc, K, mb, v in netrows], ok))
    report("4e Steiner forest, 2 pairs: sum_partitions sum_colourings prod_colour det", rows)

# ------------------------------------------------------------------ 4f. k-paths and k-cycles (subgraph counting)
class KPathSpec(Spec):
    def __init__(s, n, E, Wm, T, Zv):
        s.n, s.edges, s.Wm, s.T, s.Zv = n, E, Wm, T, Zv
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def incident(s, v): return s._inc[v]
    def vstates(s, v): return [0, 1]
    def estates(s, k): return [0, 1]
    def C(s, v, y, sig):
        d = sum(sig.values())
        if y == 0:
            return s.Zv if d == 0 else 0
        return s.T if d in (1, 2) else 0
    def M(s, v, y): return gadd(ONE, gscale(s.pbps(v), s.Wm)) if y else s.pbps(v)
    def F(s, k, yu, yv, x):
        if not x:
            return ONE
        if not (yu and yv):
            return ZERO
        u, v = s.edges[k]
        return gscale(gadd(ONE, s.q_undirected(u, v)), s.Zv)

def count_paths_cycles(n, E):
    paths = [0] * (n + 1); cycles = [0] * (n + 1)
    for r in range(1, len(E) + 1):
        for X in itertools.combinations(range(len(E)), r):
            EX = [E[k] for k in X]
            Vs = {x for e in EX for x in e}
            deg = {v: 0 for v in Vs}
            for i, j in EX:
                deg[i] += 1; deg[j] += 1
            if max(deg.values()) > 2:
                continue
            comps, cyc = components(Vs, EX)
            if len(comps) != 1:
                continue
            if cyc:
                cycles[len(Vs)] += 1
            else:
                paths[len(Vs)] += 1
    return paths, cycles

def prob_kpaths(rng, trials):
    rows = []
    for _ in range(trials):
        n = rng.choice([5, 6]); m = rng.randint(n, min(n * (n - 1) // 2, 2 * n - 1))
        E = rand_graph(n, m, rng)
        b = 48; Y = 1 << b
        Wm, T, Zv = Y, Y ** (n + 1), Y ** ((n + 1) ** 2)
        paths, cycles = count_paths_cycles(n, E)
        sp = KPathSpec(n, E, Wm, T, Zv)
        # identity side (independent): the same sum evaluated by determinants
        target = 0
        for r in range(m + 1):
            for X in itertools.combinations(range(m), r):
                EX = [E[k] for k in X]
                Vs = sorted({x for e in EX for x in e})
                deg = {v: 0 for v in Vs}
                for i, j in EX:
                    deg[i] += 1; deg[j] += 1
                if any(d > 2 for d in deg.values()):
                    continue
                for extra in range(0, n - len(Vs) + 1):
                    for A in itertools.combinations([v for v in range(n) if v not in Vs], extra):
                        # isolated vertices of S would need deg>=1: not allowed
                        if extra:
                            continue
                        L = laplacian(Vs, EX)
                        for t_ in range(len(L)):
                            L[t_][t_] += Wm
                        target += det_exact(L) * T ** len(Vs) * Zv ** (r + n - len(Vs))
        dist = kron_decode(target, b, (n + 1) ** 2 * (n + m + 2) + 1)
        gp = [dist[1 + (n + 1) * k + (n + 1) ** 2 * (n - 1)] for k in range(n + 1)]
        gc = [dist[1 + (n + 1) * k + (n + 1) ** 2 * n] for k in range(n + 1)]
        ok1 = all(gp[k] == k * paths[k] for k in range(2, n + 1)) and all(gc[k] == k * k * cycles[k] for k in range(3, n + 1))
        net = check_network(sp, n, E, target, rng, "kpath", Ks=(2, 3), max_cross=5)
        ok = ok1 and all(x[-1] for x in net)
        rows.append((n, m, f"paths={paths[2:]} cycles={cycles[3:]}", [x[:3] for x in net], ok))
    report("4f k-vertex paths / k-cycles: [w^1 z^{n-1 or n} t^k]", rows)

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    which = sys.argv[3].split(",") if len(sys.argv) > 3 else None
    rng = random.Random(seed)
    jobs = [("hc", lambda: prob_hc(rng, trials)), ("dhc", lambda: prob_dhc(rng, trials)),
            ("tsp", lambda: prob_tsp(rng, trials)), ("atsp", lambda: prob_tsp(rng, trials, True)),
            ("paths", lambda: prob_paths(rng, trials)), ("leaves", lambda: prob_leaves(rng, trials)),
            ("steiner", lambda: prob_steiner(rng, trials)), ("cvc", lambda: prob_conn(rng, trials, "cvc")),
            ("cds", lambda: prob_conn(rng, trials, "cds")), ("fvs", lambda: prob_forest(rng, trials, True)),
            ("forests", lambda: prob_forest(rng, trials, False)),
            ("sforest", lambda: prob_steiner_forest(rng, trials)), ("kpaths", lambda: prob_kpaths(rng, trials))]
    for name, f in jobs:
        if which is None or name in which:
            f()
    print("ALL OK" if ALL_OK else "SOME FAILURE")
