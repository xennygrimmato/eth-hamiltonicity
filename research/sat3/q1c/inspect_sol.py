import sys, itertools, numpy as np
from relax import *
net = delta3()
spec = sys.argv[1].split(',')
val, info = solve(net, level_points(net, spec), lazy_triangle=2, verbose=False)
print("bound", val)
pts, idx, pid, x = info['pts'], info['idx'], info['pair_id'], info['x']
D = lambda p, q: x[pid[idx[p], idx[q]]] if p != q else 0.0
h = lambda k, v: ('h', k, v)
n, n1, n2 = (0, 0), (1, 2), (0, 1)       # n~n1 edge (r+c=0); n, n2 collinear (row 0)
hs = lambda n: [('h',) + net.hub_of(n, k) for k in range(3)]
mids = lambda n: [canon_mid(a, b) for a, b in itertools.combinations(hs(n), 2)]
print("same-class hub D:", D(h(0,0), h(0,1)), " cross-class hub D:", D(h(0,0), h(1,0)))
print("node-mid to node-mid same node:", [round(D(a,b),4) for a,b in itertools.combinations(mids(n),2)])
print("node-mid(n) to hubs of n:", [[round(D(a,o),4) for o in hs(n)] for a in mids(n)])
print("node-mid(n) to hubs of edge-neighbour:", [[round(D(a,o),4) for o in hs(n1)] for a in mids(n)])
print("node-mid(n) to node-mid(edge nb):", [[round(D(a,b),4) for b in mids(n1)] for a in mids(n)])
print("node-mid(n) to node-mid(collinear):", [[round(D(a,b),4) for b in mids(n2)] for a in mids(n)])
if 'edgemid' in spec:
    c0 = canon_mid(mids(n)[0], mids(n1)[0])
    print("c0 to hubs:", sorted(set(round(D(c0, ('h',)+hh),4) for hh in net.hubs)))
    print("c0 to node-mids:", sorted(set(round(D(c0, m),4) for nn in net.nodes for m in mids(nn))))
    oth = [p for p in pts if p[0]=='m' and p[1][0]=='m' and p[2][0]=='m']
    print("c0 to other edge-mids:", sorted(set(round(D(c0, m),4) for m in oth if m != c0))[:12])
