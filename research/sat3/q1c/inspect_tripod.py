import itertools, numpy as np
from relax import *
from run_tripod2 import net, H, Z, Zs, pts
val, info = solve(net, pts(2), lazy_triangle=2, verbose=False)
idx, pid, x = info['idx'], info['pair_id'], info['x']
D = lambda p, q: float(x[pid[idx[p], idx[q]]]) if p != q else 0.0
h = lambda k, v: ('h', k, v)
print("bound", val)
print("same-class", round(D(h(0,0),h(0,1)),4), "cross-class", round(D(h(0,0),h(1,0)),4), "(rho^2 =", round(D(h(0,0),h(1,0))/4,4), ")")
n, e1, e2 = (0,0), (1,2), (2,1)
print("z-z edge:", round(D(Z(n),Z(e1)),4), " z-z collinear:", sorted(set(round(D(Z(n),Z(m)),4) for m in net.nodes if m not in (n,e1,e2))))
print("z to hubs (incident / other):", sorted(set(round(D(Z(n),hh),4) for hh in H)))
c0 = canon_mid(Z(n), Z(e1)); c0b = canon_mid(Z(n), Z(e2)); c0c = canon_mid(Z((0,1)), Z((1,0)))
print("c0-c0' same triangle:", round(D(c0,c0b),5), " other triangle:", round(D(c0,c0c),5))
print("c0 to hubs:", sorted(set(round(D(c0,hh),4) for hh in H)), " c0 to z:", sorted(set(round(D(c0,zz),4) for zz in Zs)))
for (a,b,name) in [(h(0,0),h(0,1),'R0,R1'), (h(0,0),h(1,0),'R0,C0')]:
    ma, mb = canon_mid(c0,a), canon_mid(c0,b)
    print(f"mid(c0,{name.split(',')[0]}) - mid(c0,{name.split(',')[1]}): D = {D(ma,mb):.4f}  (flat triangle would give {D(a,b)/4:.4f}; straight angle would give {(np.sqrt(D(c0,a))+np.sqrt(D(c0,b)))**2/4:.4f})")
