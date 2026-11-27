"""Three K_{2,2,1} blocks for the 3-net of Z_g (classes r, c, r+c): exact check over a prime field q = 1 mod g.

Block types (frequencies in the dual group, diagonal = alpha - beta):
   type 1: rows {0,1}, columns {0,1}, diagonal {2}        (R,C,D dimensions 2,2,1)
   type 2: rows {0,1}, column  {2},   diagonals {3,4}?    chosen by search below  (2,1,2)
   type 3: row  {.},   columns {..},  diagonals {..}                                (1,2,2)
Each block: 8 frequencies, W_block = cut space of K_{2,2,1}, rank 4.  Direct sum of the three: N = 24, hubs of
dimension k = 5, node spaces of dimension w = 12.  Printed: for which non-collinear t the node spaces W_0 and
rho(t)W_0 meet (blockwise), compared with the special differences (a,a), (a,-2a), (-2a,a).
"""
import sys, itertools
from cyclic_octa import rank_mod, isprime

def setup_block(g, rows, cols, diags, q):
    lines = [('R', b % g) for b in rows] + [('C', a % g) for a in cols] + [('D', d % g) for d in diags]
    def on(pt):
        a, b = pt
        return [i for i, (t, v) in enumerate(lines) if (t == 'R' and b == v) or (t == 'C' and a == v) or (t == 'D' and (a-b) % g == v)]
    pts = set()
    for (t1, v1), (t2, v2) in itertools.combinations(lines, 2):
        if t1 == t2: continue
        d = {t1: v1, t2: v2}
        if 'R' in d and 'C' in d: pts.add((d['C'], d['R']))
        elif 'R' in d: pts.add(((d['R'] + d['D']) % g, d['R']))
        else: pts.add((d['C'], (d['C'] - d['D']) % g))
    pts = sorted(pts)
    ne = len(rows)*len(cols) + len(rows)*len(diags) + len(cols)*len(diags)
    if len(pts) != ne or any(len(on(p)) != 2 for p in pts): return None
    M = [[0]*len(pts) for _ in lines]
    for j, p in enumerate(pts):
        i1, i2 = on(p); M[i1][j] = 1; M[i2][j] = q - 1
    return pts, M

def badset(g, rows, cols, diags):
    q = g + 1
    while not isprime(q): q += g
    for x in range(2, q):
        w = pow(x, (q-1)//g, q)
        if all(pow(w, g//p, q) != 1 for p in range(2, g+1) if g % p == 0 and isprime(p)): break
    s = setup_block(g, rows, cols, diags, q)
    if s is None: return None
    pts, M = s; rk = rank_mod(M, q); bad = set()
    for t1 in range(1, g):
        for t2 in range(1, g):
            if (t1 + t2) % g == 0: continue
            Mt = [[x * pow(w, (a*t1 + b*t2) % g, q) % q for x, (a, b) in zip(r, pts)] for r in M]
            if rank_mod(M + Mt, q) != 2*rk: bad.add((t1, t2))
    return rk, len(pts), bad

if __name__ == "__main__":
    for g in map(int, sys.argv[1:]):
        fam = {1: set((a, a) for a in range(1, g) if 2*a % g), 2: set((a, (-2*a) % g) for a in range(1, g) if 2*a % g and a % g),
               3: set(((-2*a) % g, a) for a in range(1, g) if 2*a % g)}
        special = set().union(*fam.values())
        special = {t for t in special if t[0] and t[1] and (t[0]+t[1]) % g}
        res = {}
        for name, (rows, cols, diags) in {"(2,2,1)": ((0, 1), (0, 1), (2,)), "(2,1,2)": ((0, 1), (2,), (0, 3)), "(1,2,2)": ((2,), (0, 1), (0, 3))}.items():
            best = None
            # small search for parameters of this shape with the fewest bad t
            shapes = [(rows, cols, diags)] + [((0, x) if len(rows) == 2 else (x,), (0, y) if len(cols) == 2 else (y,), (0, z) if len(diags) == 2 else (z,))
                                               for x in range(1, 6) for y in range(1, 6) for z in range(1, 6)]
            for sh in shapes:
                r = badset(g, *sh)
                if r is None: continue
                if best is None or len(r[2]) < len(best[1][2]): best = (sh, r)
                if len(r[2]) <= g - 1: break
            res[name] = best
            sh, (rk, N, bad) = best
            print("g = %d block %s lines %s: rank %d, N = %d, bad t: %d, all special: %s" % (g, name, sh, rk, N, len(bad), bad <= special))
        allbad = set().union(*[r[1][2] for r in res.values()])
        ng = (g-1)*(g-2)
        print("g = %d: three blocks, k = 5, w = 12: independent on %d of %d non-collinear differences; value there sqrt(5/12) = 0.6455"
              % (g, ng - len(allbad), ng))
