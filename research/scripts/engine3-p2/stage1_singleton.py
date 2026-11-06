"""Stage 1 [C heuristic search, N exact evaluation]: designs whose measurement rows are singletons e_a
(height 1, l1 = 1).  For singleton rows the per-occurrence system decouples coordinatewise and
R_o = #{t : v foreign at t (part_t(v) != alpha_t(e)) and v unmeasured at t}  exactly.
Simulated annealing over balanced partitions (|S_{t,h}| = n/r), clause assignments, measured sets
(<= rho per group per point).  Energy sum_o 5^{R_o}; we report the best max_o R_o.
usage: python3 stage1_singleton.py FAM n Q rho r seed iters  -> prints a JSON line, saves design pickle
"""
import sys, random, math, json, pickle, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import make_instance, occurrences

def run(fam, n, Q, rho, r, seed, iters, inst_seed=None, fixed=False):
    """fixed=True: template-type subclass, one t-independent measured set A (Lambda = span e_A),
    rho members of A in every group at every point."""
    clauses = make_instance(fam, n, inst_seed if inst_seed is not None else seed)
    rng = random.Random(seed)
    occ = occurrences(clauses)
    occ_of_var = {v: [k for k, (e, w) in enumerate(occ) if w == v] for v in range(n)}
    occ_of_cl = {e: [k for k, (f, w) in enumerate(occ) if f == e] for e in range(len(clauses))}
    s = n // r
    part = []; alpha = []; meas = []
    A = set(rng.sample(range(n), rho * r))
    for t in range(Q):
        perm = list(range(n)); rng.shuffle(perm)
        if fixed:
            aa = [v for v in perm if v in A]; bb = [v for v in perm if v not in A]
            perm = []
            for h in range(r): perm += aa[h*rho:(h+1)*rho] + bb[h*(s-rho):(h+1)*(s-rho)]
        p = [0] * n
        for k, v in enumerate(perm): p[v] = k // s
        part.append(p)
        # majority assignment
        a = []
        for c in clauses:
            cnt = {}
            for v in c: cnt[p[v]] = cnt.get(p[v], 0) + 1
            a.append(max(cnt, key=lambda g: (cnt[g], rng.random())))
        alpha.append(a)
        m = set()
        if fixed: meas.append(set(A)); continue
        for h in range(r):
            mem = [v for v in range(n) if p[v] == h]
            rng.shuffle(mem); m.update(mem[:rho])
        meas.append(m)
    def f(k, t):
        e, v = occ[k]
        return 1 if (part[t][v] != alpha[t][e] and v not in meas[t]) else 0
    L = [sum(f(k, t) for t in range(Q)) for k in range(len(occ))]
    W = lambda x: 5.0 ** x
    E = sum(W(x) for x in L)
    best = (max(L), sum(L)); best_state = None
    T0 = 2.0
    for it in range(iters):
        temp = T0 * (1 - it / iters) + 0.02
        t = rng.randrange(Q)
        mv = rng.random()
        if mv < 0.45:      # swap two variables in different groups
            x, y = rng.sample(range(n), 2)
            if part[t][x] == part[t][y]: continue
            if fixed and ((x in A) != (y in A)): continue
            aff = set(occ_of_var[x]) | set(occ_of_var[y])
            old = {k: f(k, t) for k in aff}
            hx, hy = part[t][x], part[t][y]
            mx, my = x in meas[t], y in meas[t]
            def do():
                part[t][x], part[t][y] = hy, hx
                if mx != my:      # measured slot stays in its group
                    if mx: meas[t].discard(x); meas[t].add(y)
                    else:  meas[t].discard(y); meas[t].add(x)
            def undo():
                part[t][x], part[t][y] = hx, hy
                if mx != my:
                    if mx: meas[t].discard(y); meas[t].add(x)
                    else:  meas[t].discard(x); meas[t].add(y)
        elif mv < 0.75:    # reassign a clause
            e = rng.randrange(len(clauses))
            g_old = alpha[t][e]; g_new = rng.randrange(r)
            if g_new == g_old: continue
            aff = set(occ_of_cl[e]); old = {k: f(k, t) for k in aff}
            def do(): alpha[t][e] = g_new
            def undo(): alpha[t][e] = g_old
        elif fixed:        # exchange roles of x in A and y not in A at every point
            if rho == 0: continue
            x = rng.choice(sorted(A)); y = rng.choice([v for v in range(n) if v not in A])
            aff = set(occ_of_var[x]) | set(occ_of_var[y])
            old = {k: sum(f(k, tt) for tt in range(Q)) for k in aff}
            def do():
                A.discard(x); A.add(y)
                for tt in range(Q):
                    part[tt][x], part[tt][y] = part[tt][y], part[tt][x]
                    meas[tt].discard(x); meas[tt].add(y)
            def undo():
                A.discard(y); A.add(x)
                for tt in range(Q):
                    part[tt][x], part[tt][y] = part[tt][y], part[tt][x]
                    meas[tt].discard(y); meas[tt].add(x)
            t = None
        else:              # move a measurement inside a group
            if rho == 0: continue
            x = rng.choice(sorted(meas[t])); h = part[t][x]
            cand = [v for v in range(n) if part[t][v] == h and v not in meas[t]]
            if not cand: continue
            y = rng.choice(cand)
            aff = set(occ_of_var[x]) | set(occ_of_var[y]); old = {k: f(k, t) for k in aff}
            def do(): meas[t].discard(x); meas[t].add(y)
            def undo(): meas[t].discard(y); meas[t].add(x)
        do()
        dE = 0.0; newL = {}
        for k in aff:
            nl = (L[k] - old[k] + f(k, t)) if t is not None else sum(f(k, tt) for tt in range(Q))
            if nl != L[k]:
                dE += W(nl) - W(L[k]); newL[k] = nl
        if dE <= 0 or rng.random() < math.exp(-dE / temp):
            for k, nl in newL.items(): L[k] = nl
            E += dE
            cur = (max(L), sum(L))
            if cur < best:
                best = cur
                best_state = ([p[:] for p in part], [a[:] for a in alpha], [sorted(m) for m in meas])
        else:
            undo()
    if best_state is None:
        best_state = ([p[:] for p in part], [a[:] for a in alpha], [sorted(m) for m in meas])
    return clauses, best, best_state

if __name__ == '__main__':
    fam = sys.argv[1]; n, Q, rho, r, seed, iters = map(int, sys.argv[2:8])
    fixed = len(sys.argv) > 8 and sys.argv[8] == 'fixed'
    clauses, best, st = run(fam, n, Q, rho, r, seed, iters, inst_seed=1, fixed=fixed)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'designs')
    os.makedirs(out, exist_ok=True)
    fn = os.path.join(out, ('s1fix_' if fixed else 's1_') + f'{fam}_n{n}_Q{Q}_rho{rho}_r{r}_s{seed}.pkl')
    pickle.dump({'clauses': clauses, 'part': st[0], 'alpha': st[1], 'meas': st[2], 'Q': Q, 'r': r, 'rho': rho, 'n': n}, open(fn, 'wb'))
    print(json.dumps({'fixed': fixed, 'fam': fam, 'n': n, 'Q': Q, 'rho': rho, 'r': r, 'seed': seed, 'M': 3*0 + sum(len(c) for c in clauses),
                      'Rmax': best[0], 'Rsum': best[1]}))
