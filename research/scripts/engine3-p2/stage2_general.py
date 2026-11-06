"""Stage 2 [C heuristic search, N exact evaluation]: general measurement spaces R_{t,h} (t-dependent,
<= rho rows per group, integer entries of height <= 2: singletons, pairs e_a + c e_b, 2e_a +- e_b,
group sums, signed sums, subset sums, random {-2..2} rows).  Per-occurrence min degree R_o computed
exactly mod p (verified over Q at the end).  Starts from a stage-1 design (or random rows) and anneals
rows + clause assignments + partition swaps on energy sum_o 5^{R_o}.
usage: python3 stage2_general.py design.pkl iters seed [mode]   mode in {mixed, dense, sparse}
"""
import sys, os, random, math, pickle, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import occurrences, min_R_occ, occ_system, row_l1, rank_modp, rank_exact, feasible, P2

def component(design, e, v):
    part, alpha, rows, Q = design['part'], design['alpha'], design['rows'], design['Q']
    comp = {v}; stack = [v]
    while stack:
        i = stack.pop()
        for t in range(Q):
            h = part[t][i]
            if h == alpha[t][e]: continue
            rl = rows[t][h]
            if not any(i in rw for rw in rl): continue
            for rw in rl:
                for j in rw:
                    if j not in comp: comp.add(j); stack.append(j)
    return comp

def main():
    fn = sys.argv[1]; iters = int(sys.argv[2]); seed = int(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else 'mixed'
    rng = random.Random(seed)
    d = pickle.load(open(fn, 'rb'))
    clauses, Q, r, rho, n = d['clauses'], d['Q'], d['r'], d['rho'], d['n']
    occ = occurrences(clauses)
    design = {'Q': Q, 'part': d['part'], 'alpha': d['alpha'],
              'rows': [[[] for _ in range(r)] for _ in range(Q)]}
    S = lambda t, h: [v for v in range(n) if design['part'][t][v] == h]
    def cand_row(t, h, focus=None):
        mem = S(t, h)
        if not mem: return None
        a = focus if focus in mem else rng.choice(mem)
        kinds = {'mixed': ['single', 'pair', 'pair', 'pair2', 'gsum', 'signed', 'subset', 'rand'],
                 'dense': ['gsum', 'signed', 'rand'],
                 'sparse': ['single', 'pair', 'pair', 'pair2'],
                 'mixedrand': ['single', 'pair', 'pair', 'pair2', 'gsum', 'signed', 'subset', 'rand']}[mode]
        k = rng.choice(kinds)
        if k == 'single' or len(mem) == 1: return {a: 1}
        b = rng.choice([x for x in mem if x != a])
        if k == 'pair':  return {a: 1, b: rng.choice([1, -1, 2, -2])}
        if k == 'pair2': return {a: 2, b: rng.choice([1, -1])}
        if k == 'gsum':  return {x: 1 for x in mem}
        if k == 'signed': return {x: rng.choice([1, -1]) for x in mem}
        if k == 'subset':
            sub = [x for x in mem if rng.random() < 0.5 or x == a]
            return {x: 1 for x in sub}
        rw = {x: rng.choice([-2, -1, 1, 2]) for x in mem if rng.random() < 0.7 or x == a}
        return rw
    if mode == 'sparse' or mode == 'mixed':
        for t in range(Q):
            for v in d['meas'][t]:
                design['rows'][t][design['part'][t][v]].append({v: 1})
    else:
        for t in range(Q):
            for h in range(r):
                for _ in range(rho):
                    rw = cand_row(t, h)
                    if rw: design['rows'][t][h].append(rw)
    W = lambda x: 5.0 ** x
    Rs = [min_R_occ(design, e, v) for (e, v) in occ]
    comps = [component(design, e, v) for (e, v) in occ]
    start = (max(Rs), sum(Rs))
    best = start; best_rows = pickle.dumps(design)
    t0 = time.time()
    for it in range(iters):
        temp = 1.5 * (1 - it / iters) + 0.02
        t = rng.randrange(Q)
        mv = rng.random()
        saved_rows = [[list(rl) for rl in design['rows'][t]]]
        saved_alpha = None; saved_part = None
        if mv < 0.7:
            h = rng.randrange(r)
            # focus on a variable of a worst occurrence
            worst = [k for k in range(len(occ)) if Rs[k] >= max(Rs) - 1]
            k0 = rng.choice(worst); fv = occ[k0][1]
            if design['part'][t][fv] == design['alpha'][t][occ[k0][0]]:
                pass
            else:
                h = design['part'][t][fv] if rng.random() < 0.7 else h
            rw = cand_row(t, h, focus=fv)
            if rw is None: continue
            rl = design['rows'][t][h]
            if len(rl) < rho: rl.append(rw)
            else: rl[rng.randrange(len(rl))] = rw
            changed = set(rw)
            for x in saved_rows[0][h]: changed |= set(x)
            aff = [k for k, (e, v) in enumerate(occ) if design['alpha'][t][e] != h and (comps[k] & changed or v in changed)]
        elif mv < 0.85:
            e = rng.randrange(len(clauses)); g = rng.randrange(r)
            if g == design['alpha'][t][e]: continue
            saved_alpha = (t, e, design['alpha'][t][e]); design['alpha'][t][e] = g
            aff = [k for k, (f, v) in enumerate(occ) if f == e]
        else:
            x, y = rng.sample(range(n), 2)
            hx, hy = design['part'][t][x], design['part'][t][y]
            if hx == hy: continue
            saved_part = (t, x, y, hx, hy)
            design['part'][t][x], design['part'][t][y] = hy, hx
            for hh in (hx, hy):   # drop rows touching x or y, replace by singletons of remaining support
                new = []
                for rw in design['rows'][t][hh]:
                    if x in rw or y in rw:
                        rest = [z for z in rw if z not in (x, y)]
                        if rest: new.append({rest[0]: 1})
                    else: new.append(rw)
                design['rows'][t][hh] = new
            aff = list(range(len(occ)))
        newR = {}; newC = {}
        dE = 0.0
        for k in aff:
            e, v = occ[k]
            R = min_R_occ(design, e, v, hint=Rs[k]); newR[k] = R; newC[k] = component(design, e, v)
            dE += W(R) - W(Rs[k])
        if dE <= 0 or rng.random() < math.exp(-dE / temp):
            for k in aff: Rs[k] = newR[k]; comps[k] = newC[k]
            cur = (max(Rs), sum(Rs))
            if cur < best:
                best = cur
                best_rows = pickle.dumps(design)
        else:
            design['rows'][t] = saved_rows[0]
            if saved_alpha: design['alpha'][saved_alpha[0]][saved_alpha[1]] = saved_alpha[2]
            if saved_part:
                tt, x, y, hx, hy = saved_part
                design['part'][tt][x], design['part'][tt][y] = hx, hy
    bd = pickle.loads(best_rows)
    # exact verification over Q of the best design: R_o feasible and R_o - 1 infeasible
    ver = True; Rs_b = []
    for (e, v) in occ:
        R = min_R_occ(bd, e, v); Rs_b.append(R)
        if not feasible(bd, e, v, R, exact=True): ver = False
        from p2common import lower_count
        if R > lower_count(bd, e, v) and feasible(bd, e, v, R - 1, exact=True): ver = False
    nonsingle = sum(1 for t in range(Q) for h in range(r) for rw in bd['rows'][t][h] if len(rw) > 1)
    maxl1 = max([row_l1(rw) for t in range(Q) for h in range(r) for rw in bd['rows'][t][h]] or [0])
    maxsys = 0
    for (e, v), R in zip(occ, Rs_b):
        A, b = occ_system(bd, e, v, max(R, 1))
        maxsys = max(maxsys, len(A) * (len(A[0]) if A else 0))
    out = {'file': os.path.basename(fn), 'mode': mode, 'seed': seed, 'iters': iters,
           'start': start, 'best': [max(Rs_b), sum(Rs_b)], 'exact_verified': ver,
           'nonsingleton_rows': nonsingle, 'max_row_l1': maxl1, 'max_system_entries': maxsys,
           'secs': round(time.time() - t0, 1)}
    print(json.dumps(out))
    bd.update({'clauses': clauses, 'r': r, 'rho': rho, 'n': n})
    pickle.dump(bd, open(fn.replace('.pkl', f'.s2{mode}{seed}.pkl'), 'wb'))

main()
