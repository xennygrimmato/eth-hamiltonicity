"""engine2d_sat: exhaustive GF(2) search (lambda=1) for the minimum rank-sum  S = sum_t 2^{cost_t}
of a decomposition  (x) F_q = sum_t T_t  into row-networks / column-networks (arbitrary local tensors).
Theorem (engine2-decorrelated.md, Thm 1): S >= 2^{lambda*Q} for every diagonal configuration.
Prints one line per configuration; PASS iff the SAT optimum is consistent with Theorem 1."""
import itertools, sys, time
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/scripts')
from engine2d_lib import *
from pysat.solvers import Solver

def term_types(cfg, G):
    """(bonds dict, weight) for grouping G, bonds only on pairs carrying rectangles."""
    P = cfg['pairs'][G]; out = []
    for dims in itertools.product(range(1, 9), repeat=len(P)):
        w = 1
        for d in dims: w *= d
        if w <= 8: out.append((dict(zip(P, dims)), w))
    return out

def profiles(cfg, S):
    """multisets of terms with total weight exactly S.  For a 2-class grouping, ranks add, so one term
    of rank r per grouping suffices (weight-1 terms of that grouping are subsumed)."""
    types = []
    for G in ('row', 'col'):
        two = len(cfg['cls'][G]) == 2
        for b, w in term_types(cfg, G):
            types.append((G, tuple(sorted(b.items())), w, two))
    types.sort(key=lambda t: t[2])
    res = []
    def rec(i, rem, cur, used2):
        if rem == 0: res.append(list(cur)); return
        for j in range(i, len(types)):
            G, b, w, two = types[j]
            if w > rem: continue
            if two and G in used2: continue
            cur.append((G, dict(b))); rec(j if not two else j + 1, rem - w, cur, used2 | ({G} if two else set())); cur.pop()
    rec(0, S, [], frozenset())
    return res

TLIM = 60
def solve(cfg, terms, tlim=None):
    """True/False, or None on timeout (TLIM seconds per instance)."""
    import threading
    E, tv = encode(cfg, terms)
    with Solver(name='glucose4', bootstrap_with=E.cl) as s:
        tm = threading.Timer(tlim or TLIM, s.interrupt); tm.start()
        ok = s.solve_limited(expect_interrupt=True); tm.cancel()
        return ok, (evaluate(cfg, tv, s.get_model()) if ok else None)

def check_solution(cfg, terms, Ts):
    D = cfg['D']; nl = len(cfg['legs'])
    for e in itertools.product(range(D), repeat=nl):
        if sum(T[e] for T in Ts) % 2 != cfg['target'](e): return False
    return True

def minimise(name, rects, Smax, diag, Smin=None):
    cfg = make_config(rects); Q = len(rects); t0 = time.time(); nprof = 0
    # S below the Theorem-1 bound is impossible (proved; Lean-proved for config C), so start there
    for S in range(Smin or (2 ** Q if diag else 1), Smax + 1):
        nto = 0
        for prof in profiles(cfg, S):
            nprof += 1
            ok, Ts = solve(cfg, prof)
            if ok is None: nto += 1
            if ok:
                good = check_solution(cfg, prof, Ts)
                desc = ' + '.join(f"{G}{list(b.values())}" for G, b in prof)
                lb = 2 ** Q if diag else None
                consistent = good and (lb is None or S >= lb)
                print(f"{name:28s} Q={Q} min S={S:2d}  (Thm1 bound {lb})  profile: {desc}   "
                      f"[{nprof} profiles, {time.time()-t0:.1f}s] {'PASS' if consistent else 'FAIL'}")
                return S
        print(f"{name:28s}   S={S:2d}: no decomposition ({nto} of the profiles timed out at {TLIM}s)", flush=True)
    print(f"{name:28s} Q={Q} no decomposition with S<={Smax} [{nprof} profiles, {time.time()-t0:.1f}s]")
    return None

if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'two'
    if which in ('one', 'two', 'all'):
        minimise('single rectangle', [((0, 1), (0, 1))], 4, True)
    if which in ('two', 'all'):
        minimise('A fat cell (same pairs)', [((0, 1), (0, 1)), ((0, 1), (0, 1))], 8, True)
        minimise('B same rows, disj cols', [((0, 1), (0, 1)), ((0, 1), (2, 3))], 8, True)
        minimise('B\' same rows, shared col', [((0, 1), (0, 1)), ((0, 1), (1, 2))], 8, True)
        minimise('C disjoint', [((0, 1), (0, 1)), ((2, 3), (2, 3))], 8, True)
        minimise('D chain rows, disj cols', [((0, 1), (0, 1)), ((1, 2), (2, 3))], 8, True)
        minimise('E chain rows+cols', [((0, 1), (0, 1)), ((1, 2), (1, 2))], 8, True)
    if which in ('three', 'all'):
        minimise('triangle (diagonal)', [((0, 1), (0, 1)), ((1, 2), (1, 2)), ((0, 2), (0, 2))], 8, True)
        minimise('3x2 grid (non-diagonal)', [((0, 1), (0, 1)), ((1, 2), (0, 1)), ((0, 2), (0, 1))], 8, False)
