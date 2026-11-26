import sys, itertools
from relax import *
net = delta3()
def nodemids(n):
    hs = [('h',) + net.hub_of(n, k) for k in range(3)]
    return [canon_mid(a, b) for a, b in itertools.combinations(hs, 2)]
zp = []
for n in net.nodes:
    for a, b in itertools.combinations(nodemids(n), 2):
        zp.append((a, b))
for spec in [s.split(',') for s in sys.argv[1:]]:
    print("TRIPOD branch (the three node midpoints coincide), spec", spec, flush=True)
    solve(net, level_points(net, spec), lazy_triangle=2, zero_pairs=zp)
