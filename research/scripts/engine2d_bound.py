"""engine2d_bound: exact checks for engine2-decorrelated.md.
(a) Theorem 1 (two-party form): for random exact decompositions F^(x)Q = sum_t T_t (terms of random
    row/column low-rank type, last term = remainder, of arbitrary type), sum_t min(rk_row, rk_col) >= N^Q,
    and the contracted matrices C_t(x|v) (y=u=0) satisfy rank C_t <= min(rk_row, rk_col), sum C_t = I.
(b) Diagonal labellings: brute force over f: rows->[m], h: cols->[m] (m<=3); which configurations are
    diagonal, and the best diagonal fraction of rectangles in the full g x g grid (g = 3, 4).
"""
import itertools, random, sys
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/scripts')
from engine2_lib import rank_exact, report
from engine2d_lib import make_config

def flat(cfg, T, left):
    D = cfg['D']; nl = len(cfg['legs']); right = [i for i in range(nl) if i not in left]
    L = list(itertools.product(range(D), repeat=len(left))); R = list(itertools.product(range(D), repeat=len(right)))
    M = []
    for a in L:
        row = []
        for b in R:
            e = [0] * nl
            for i, v in zip(left, a): e[i] = v
            for i, v in zip(right, b): e[i] = v
            row.append(T[tuple(e)])
        M.append(row)
    return M

def cuts(cfg):
    """the 2-class cuts used by Theorem 1: rows {a-side} and columns {left-side} (diagonal 2-labelling)"""
    rects = cfg['rects']
    # 2-colour rows and columns so that every rectangle is split (exists for the configs used)
    rows = sorted({r for (rs, cs) in rects for r in rs}); cols = sorted({c for (rs, cs) in rects for c in cs})
    for f in itertools.product((0, 1), repeat=len(rows)):
        for h in itertools.product((0, 1), repeat=len(cols)):
            F = dict(zip(rows, f)); H = dict(zip(cols, h))
            if all(F[r] != F[s] and H[c] != H[d] for ((r, s), (c, d)) in rects):
                rl = [i for i, (_, nd) in enumerate(cfg['legs']) if F[nd[0]] == 0]
                cl = [i for i, (_, nd) in enumerate(cfg['legs']) if H[nd[1]] == 0]
                return F, H, rl, cl
    return None

def random_term(cfg, rl, cl, rng, kind, r):
    """random integer tensor of row rank <= r (kind 'row') or column rank <= r (kind 'col')"""
    D = cfg['D']; nl = len(cfg['legs']); left = rl if kind == 'row' else cl
    right = [i for i in range(nl) if i not in left]
    A = [{a: rng.randint(-2, 2) for a in itertools.product(range(D), repeat=len(left))} for _ in range(r)]
    B = [{b: rng.randint(-2, 2) for b in itertools.product(range(D), repeat=len(right))} for _ in range(r)]
    T = {}
    for e in itertools.product(range(D), repeat=nl):
        a = tuple(e[i] for i in left); b = tuple(e[i] for i in right)
        T[e] = sum(A[k][a] * B[k][b] for k in range(r))
    return T

def check_thm1(name, rects, lam, trials, rng):
    cfg = make_config(rects, lam); Q = len(rects); N = cfg['D']
    F, H, rl, cl = cuts(cfg); nl = len(cfg['legs']); ok = True; worst = None
    xs = []; vs = []  # kept legs: for each rectangle the crossing edge with ends (0,0) | (1,1)
    for q, ((r, s), (c, d)) in enumerate(rects):
        idx = cfg['idx']
        for a, b in ((f'x{q}', f'v{q}'), (f'y{q}', f'u{q}'), (f'v{q}', f'x{q}'), (f'u{q}', f'y{q}')):
            na = cfg['legs'][idx[a]][1]
            if F[na[0]] == 0 and H[na[1]] == 0: xs.append(idx[a]); vs.append(idx[b]); break
    rest = [i for i in range(nl) if i not in xs + vs]
    for _ in range(trials):
        k = rng.randint(1, 3)
        terms = [random_term(cfg, rl, cl, rng, rng.choice(('row', 'col')), rng.randint(1, N ** Q // 2)) for _ in range(k)]
        tgt = {e: cfg['target'](e) for e in itertools.product(range(N), repeat=nl)}
        terms.append({e: tgt[e] - sum(T[e] for T in terms) for e in tgt})
        tot = 0; Csum = None
        for T in terms:
            rr = rank_exact(flat(cfg, T, rl)); rc = rank_exact(flat(cfg, T, cl))
            C = []
            for a in itertools.product(range(N), repeat=len(xs)):
                row = []
                for b in itertools.product(range(N), repeat=len(vs)):
                    e = [0] * nl
                    for i, v in zip(xs, a): e[i] = v
                    for i, v in zip(vs, b): e[i] = v
                    row.append(T[tuple(e)])
                C.append(row)
            rC = rank_exact(C); ok &= rC <= min(rr, rc); tot += min(rr, rc)
            Csum = C if Csum is None else [[x + y for x, y in zip(r1, r2)] for r1, r2 in zip(Csum, C)]
        ok &= all(Csum[i][j] == (1 if i == j else 0) for i in range(len(Csum)) for j in range(len(Csum)))
        ok &= tot >= N ** Q
        worst = tot if worst is None else min(worst, tot)
    return report(f"Thm1 {name:24s} lam={lam}: {trials} random exact decompositions, min sum_t min(rk_row,rk_col) = {worst} >= N^Q = {N**Q}", ok)

def diagonal(rects, m):
    rows = sorted({r for (rs, cs) in rects for r in rs}); cols = sorted({c for (rs, cs) in rects for c in cs})
    best = 0
    for f in itertools.product(range(m), repeat=len(rows)):
        F = dict(zip(rows, f))
        for h in itertools.product(range(m), repeat=len(cols)):
            H = dict(zip(cols, h))
            n = sum(1 for ((r, s), (c, d)) in rects if F[r] != F[s] and {F[r], F[s]} == {H[c], H[d]})
            best = max(best, n)
    return best

if __name__ == '__main__':
    rng = random.Random(20261104); ok = True
    two = {'A fat cell': [((0, 1), (0, 1)), ((0, 1), (0, 1))], 'B same rows': [((0, 1), (0, 1)), ((0, 1), (2, 3))],
           "B' shared col": [((0, 1), (0, 1)), ((0, 1), (1, 2))], 'C disjoint': [((0, 1), (0, 1)), ((2, 3), (2, 3))],
           'D chain rows': [((0, 1), (0, 1)), ((1, 2), (2, 3))], 'E chain rows+cols': [((0, 1), (0, 1)), ((1, 2), (1, 2))]}
    for nm, rc in two.items():
        ok &= check_thm1(nm, rc, 1, 6, rng)
    ok &= check_thm1('C disjoint', two['C disjoint'], 2, 2, rng)
    print("(b) diagonal labellings (max #rectangles diagonal, over m <= 3 labels):")
    cfgs = dict(two)
    cfgs['triangle'] = [((0, 1), (0, 1)), ((1, 2), (1, 2)), ((0, 2), (0, 2))]
    cfgs['3x2 grid'] = [((0, 1), (0, 1)), ((1, 2), (0, 1)), ((0, 2), (0, 1))]
    for nm, rc in cfgs.items():
        b = max(diagonal(rc, m) for m in (2, 3))
        print(f"    {nm:18s}: {b}/{len(rc)} diagonal")
        ok &= (b == len(rc)) == (nm != '3x2 grid')
    for g in (3, 4):
        rects = [((a, b), (j, k)) for a, b in itertools.combinations(range(g), 2) for j, k in itertools.combinations(range(g), 2)]
        res = {m: diagonal(rects, m) for m in (2, 3)}
        print(f"    full {g}x{g} grid: |R| = {len(rects)}, best diagonal sub-configuration m=2: {res[2]}, m=3: {res[3]}")
        ok &= res[2] >= res[3]
    report("engine2d_bound overall", ok)
