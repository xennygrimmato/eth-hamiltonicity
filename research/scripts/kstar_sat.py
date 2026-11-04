"""k*(G) by CEGAR SAT (python-sat/CaDiCaL as a search tool; every SAT answer re-verified on all cycles).
Usage: python3 kstar_sat.py <family> <args>   families: grid p q | cubic n seed | K t"""
import sys, time, random
sys.path.insert(0, '/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/pylib')
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from pysat.solvers import Cadical153
from linenc2_lib import directed_simple_cycles, random_regular, turn_index, eid_map, cycle_turns
import kstar_grid
def kstar(n, E, kmax=4, tlimit=600, log=print):
    T = turn_index(n, E); Ei = eid_map(E)
    cyc = [cycle_turns(c, Ei, T) for c in directed_simple_cycles(n, E)]
    masks = [sum(1 << t for t in c) for c in cyc]
    log(f'  n={n} m={len(E)} turns={len(T)} directed cycles={len(cyc)}')
    for k in range(1, kmax+1):
        t0 = time.time(); cnt = [0]
        def new(): cnt[0] += 1; return cnt[0]
        X = [[new() for _ in range(len(T))] for i in range(k)]
        s = Cadical153()
        def add(ci):
            c = cyc[ci]; outs = []
            for i in range(k):
                acc = X[i][c[0]]
                for t in c[1:]:
                    y = new(); a, b = acc, X[i][t]
                    s.add_clause([-y, a, b]); s.add_clause([-y, -a, -b]); s.add_clause([y, -a, b]); s.add_clause([y, a, -b]); acc = y
                outs.append(acc)
            s.add_clause(outs)
        rng = random.Random(1)
        active = set(rng.sample(range(len(cyc)), min(len(cyc), 200)))
        for ci in active: add(ci)
        res = None
        while True:
            if time.time() - t0 > tlimit: res = 'timeout'; break
            if not s.solve(): res = 'UNSAT'; break
            mdl = set(l for l in s.get_model() if l > 0)
            f = [sum(1 << t for t in range(len(T)) if X[i][t] in mdl) for i in range(k)]
            bad = [ci for ci, mk in enumerate(masks) if all(bin(mk & fi).count('1') % 2 == 0 for fi in f)]
            if not bad: res = 'SAT'; break
            for ci in bad[:300]:
                if ci not in active: active.add(ci); add(ci)
        log(f'  k={k}: {res} ({len(active)} cycles used, {time.time()-t0:.1f}s)')
        if res == 'SAT': return k
        if res == 'timeout': return None
    return None
if __name__ == '__main__':
    fam = sys.argv[1]
    if fam == 'grid':
        p, q = int(sys.argv[2]), int(sys.argv[3]); n, E, _, _ = kstar_grid.H(p, q); name = f'H_{p},{q}'
    elif fam == 'cubic':
        n = int(sys.argv[2]); seed = int(sys.argv[3]); E = random_regular(n, 3, random.Random(seed)); name = f'cubic n={n} seed={seed}'
    elif fam == 'K':
        n = int(sys.argv[2]); E = [(i, j) for i in range(n) for j in range(i+1, n)]; name = f'K_{n}'
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    print(name, flush=True); print(name, 'k* =', kstar(n, E, tlimit=tl, log=lambda x: print(x, flush=True)))
