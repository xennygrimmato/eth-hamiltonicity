"""flat_two.py -- the finite flattening test (flat_finite.py) on the restriction of Delta_3 to two triangles
(= Majdoddin's C with two of its three merges): which R + C bond patterns are refuted there."""
import itertools
from flat_finite import bound
nodes = [(r, c) for r in range(3) for c in range(3) if (r + c) % 3 in (0, 1)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
def run(terms, label):
    worst = None
    for o in itertools.product((0, 1, -1), repeat=len(edges)):
        if not any(o): continue
        xr = [0]*3; yr = [0]*3; xc = [0]*3; yc = [0]*3
        for (u, v), oe in zip(edges, o):
            if oe == 0: continue
            a, b = (u, v) if oe == 1 else (v, u)
            xr[a[0]] += 1; yr[b[0]] += 1; xc[a[1]] += 1; yc[b[1]] += 1
        rk = 2 ** sum(1 for x in o if x)
        tot = sum(bound(xr, yr, b) if k == 'row' else bound(xc, yc, b) for k, b in terms)
        if worst is None or tot - rk < worst[0]: worst = (tot - rk, rk, tot, o)
    print(f'two triangles, {label}: worst slack {worst[0]} (rank {worst[1]}, bounds {worst[2]}, o = {worst[3]})', '-> REFUTED' if worst[0] < 0 else '-> passes')
run([('row', (2, 2, 2)), ('col', (2, 2, 2))], 'R(2,2,2)+C(2,2,2)')
run([('row', (2, 2, 2)), ('col', (2, 2, 2)), ('row', (2, 2, 2))], 'R+C+R (2,2,2)')
run([('row', (4, 4, 4))], 'R(4,4,4) alone (= f: must pass)')
