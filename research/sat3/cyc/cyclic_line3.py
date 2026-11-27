"""The (3,3,3) block with a two-dimensional relation space ("three directions on a projective line"): exact check.

Net of Z_g with classes r, c, r-c (diagonal vectors live on alpha+beta = const, which is invariant under the
translations (t,t)); isomorphic to the net with classes r, c, r+c by c -> -c.  Collinear differences: t1 = 0, t2 = 0,
t1 = t2.  Special differences (Prop. 3.2) in this convention: t2 = -t1, t2 = 2 t1, t1 = 2 t2.
Directions X, Y, Z = (1,0), (0,1), (1,1) in K^2 (p_X + p_Y - p_Z = 0); each direction carries one row, one column and
one diagonal:  rows beta_a, columns alpha_a = beta_a + c, diagonals s_a = (sum of the two other betas) + c.
15 frequency points: for each direction a the three pairwise intersections of its row, column, diagonal (coefficients
+1, -1), and for each permutation (a,b,c) of the directions the point (alpha_b, beta_a), which lies on the diagonal
s_c (coefficients +1 on X- and Y-symbols, -1 on Z-symbols).
M is 9 x 15 of rank 7; hubs R_0, C_0, D_0 = spans of the three rows of M of each class (dimension 3), W_0 = row
space (dimension 7).  Value on an independent pair: sqrt(3/7) = 0.65465.
For each g: number of non-collinear t with W_0 ^ rho(t)W_0 != 0, exactly, over F_q, q = 1 mod g.
usage: cyclic_line3.py g1 g2 [beta_Y beta_Z c]
"""
import sys, itertools, math
from cyclic_octa import rank_mod, isprime

def block(g, beta=(0, 1, 3), c=0):
    b = [x % g for x in beta]; a = [(x + c) % g for x in beta]
    s = [(beta[1]+beta[2]+c) % g, (beta[0]+beta[2]+c) % g, (beta[0]+beta[1]+c) % g]
    sign = [1, 1, -1]
    pts = []; cols = []
    R = lambda i: i; C = lambda i: 3+i; D = lambda i: 6+i
    def add(freq, ent):
        col = [0]*9
        for r, v in ent: col[r] = v
        pts.append(freq); cols.append(col)
    for i in range(3):
        add((a[i], b[i]), [(R(i), 1), (C(i), -1)])
        add(((s[i]-b[i]) % g, b[i]), [(R(i), 1), (D(i), -1)])
        add((a[i], (s[i]-a[i]) % g), [(C(i), 1), (D(i), -1)])
    for (i, j, l) in itertools.permutations(range(3)):
        add((a[j], b[i]), [(R(i), sign[i]), (C(j), sign[j]), (D(l), sign[l])])
    if len(set(pts)) != 15: return None
    # every point must lie on its own lines only
    for (al, be), col in zip(pts, cols):
        on = {R(i) for i in range(3) if b[i] == be} | {C(i) for i in range(3) if a[i] == al} | {D(i) for i in range(3) if s[i] == (al+be) % g}
        if on != {r for r in range(9) if col[r]}: return None
    M = [[cols[j][r] for j in range(15)] for r in range(9)]
    return pts, M

def check(g, beta=(0, 1, 3), c=0):
    bl = block(g, beta, c)
    if bl is None: return None
    pts, M = bl
    q = g + 1
    while not isprime(q): q += g
    for x in range(2, q):
        w = pow(x, (q-1)//g, q)
        if all(pow(w, g//p, q) != 1 for p in range(2, g+1) if g % p == 0 and isprime(p)): break
    Mq = [[v % q for v in r] for r in M]
    ok = rank_mod(Mq, q) == 7 and all(rank_mod(Mq[3*i:3*i+3] + Mq[3*j:3*j+3], q) == 6 for i in range(3) for j in range(i+1, 3))
    bad = []
    for t1 in range(1, g):
        for t2 in range(1, g):
            if (t1-t2) % g == 0: continue
            Mt = [[v * pow(w, (al*t1 + be*t2) % g, q) % q for v, (al, be) in zip(r, pts)] for r in Mq]
            if rank_mod(Mq + Mt, q) != 14: bad.append((t1, t2))
    return ok, bad

if __name__ == "__main__":
    g1, g2 = int(sys.argv[1]), int(sys.argv[2])
    par = tuple(map(int, sys.argv[3:6])) if len(sys.argv) > 5 else None
    for g in range(g1, g2+1):
        best = None
        cands = [((0, par[0], par[1]), par[2])] if par else [((0, 1, 3), 0), ((0, 1, 3), 1), ((0, 1, 4), 0), ((0, 2, 5), 1), ((0, 1, 3), 5), ((0, 1, 5), 2), ((0, 2, 3), 0), ((0, 1, 4), 2), ((0, 3, 4), 1)]
        for beta, c in cands:
            r = check(g, beta, c)
            if r is None or not r[0]: continue
            if best is None or len(r[1]) < len(best[2]): best = (beta, c, r[1])
        if best is None: print("g = %d: no valid parameters" % g); continue
        ng = (g-1)*(g-2); nb = len(best[2])
        slopes = sorted(set((t2 * pow(t1, -1, g)) % g for t1, t2 in best[2])) if isprime(g) else None
        special = {t for a in range(1, g) for t in ((a, (-a) % g), (a, (2*a) % g), ((2*a) % g, a)) if t[0] and t[1] and (t[0]-t[1]) % g}
        allsp = set(best[2]) <= special
        print("g = %2d: beta=%s c=%d: independent on %d of %d non-collinear differences (%d fail%s; all failures special: %s; #special %d)"
              % (g, best[0], best[1], ng - nb, ng, nb, "" if slopes is None else ", slopes t2/t1 = %s" % slopes, allsp, len(special)))
        sys.stdout.flush()
