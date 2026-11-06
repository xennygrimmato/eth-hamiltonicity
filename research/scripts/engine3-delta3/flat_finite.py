"""flat_finite.py -- exact finite flattening test for f_Delta = sum of row/column triangle networks at N0 = 2.
For every orientation o in {0,+,-}^9 of the edges (0 = both strings fixed to a common value, i.e. the edge is removed by
restriction; + / - = the string at the lower / higher node goes to side X, the other to side Y), the restricted f has
rank 2^{#oriented edges} across X|Y.  A triangle network with bonds d on groups G0,G1,G2 has rank across X|Y at most
  min over sides s in {X,Y}^3 of  prod_g 2^{|legs of g on the side opposite to s_g|} * prod_{g<h, s_g != s_h} d_gh
(min-cut of the network; valid over every field).  An identity f = sum_t T_t forces rank(f) <= sum_t bound(T_t) for every o.
Reports the worst (smallest) slack  sum_t bound - rank(f)  for each term list; a negative value is an exact refutation."""
import itertools, sys
import numpy as np
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
def bound(xcount, ycount, bonds):
    # xcount[g], ycount[g] = numbers of open legs of group g on side X / Y (after restriction)
    best = None
    pairs = [(0, 1), (0, 2), (1, 2)]
    for s in itertools.product((0, 1), repeat=3):
        val = 1
        for g in range(3):
            val *= 2 ** (ycount[g] if s[g] == 0 else xcount[g])
        for k, (g, h) in enumerate(pairs):
            if s[g] != s[h]: val *= bonds[k]
        best = val if best is None else min(best, val)
    return best
def run(termlist, label):
    worst = None
    for o in itertools.product((0, 1, -1), repeat=9):
        if not any(o): continue
        xr = [0, 0, 0]; yr = [0, 0, 0]; xc = [0, 0, 0]; yc = [0, 0, 0]
        for (u, v), oe in zip(edges, o):
            if oe == 0: continue
            a, b = (u, v) if oe == 1 else (v, u)       # string at a -> X, string at b -> Y
            xr[a[0]] += 1; yr[b[0]] += 1; xc[a[1]] += 1; yc[b[1]] += 1
        rk = 2 ** sum(1 for oe in o if oe)
        tot = 0
        for kind, bonds in termlist:
            tot += bound(xr, yr, bonds) if kind == 'row' else bound(xc, yc, bonds)
        slack = tot - rk
        if worst is None or slack < worst[0] or (slack == worst[0] and rk > worst[2]): worst = (slack, o, rk, tot)
    print(f'{label}: worst slack {worst[0]} (rank f = {worst[2]}, sum of bounds = {worst[3]}) at orientation {worst[1]}'
          + ('  -> EXACT REFUTATION' if worst[0] < 0 else '  -> no flattening obstruction'), flush=True)
if __name__ == "__main__":
    R = lambda *b: ('row', b); C = lambda *b: ('col', b)
    run([R(2, 2, 2), C(2, 2, 2)], 'R(2,2,2)+C(2,2,2)')
    run([R(2, 2, 2)], 'R(2,2,2) alone (control: must refute)')
    run([R(8, 8, 8)], 'R(8,8,8) alone (control: f itself, must pass)')
    run([R(2, 2, 4), C(2, 2, 4)], 'R(2,2,4)+C(2,2,4)')
    run([R(2, 2, 2), C(2, 2, 2), R(2, 2, 2)], 'R+C+R (2,2,2)')
    for T in (1, 2, 3, 4, 6, 8):
        run([R(2, 2, 2)] * T + [C(2, 2, 2)] * T, f'{T} x R(2,2,2) + {T} x C(2,2,2)')
