# Exhaustive search over GF(2): all factorisations R_2 = sum_k u_k v_k^T (mod 2) for the 4x4 disjointness matrix.
# Middle gates = a set U of distinct nonzero vectors u in GF(2)^4 (bitmask over rows a).
# r[a] = #{u in U : u(a)=1};  c[b] = min number of u's XOR-ing to column b of R (0 if unreachable -> invalid).
import itertools, numpy as np, time
from ovgame import tau_star
d0 = 2; n = 4
R = [[1 if (a & b) == 0 else 0 for b in range(n)] for a in range(n)]
cols = [sum(R[a][b] << a for a in range(n)) for b in range(n)]   # column b as bitmask over rows
def profile(U):
    r = tuple(sum((u >> a) & 1 for u in U) for a in range(n))
    INF = 99; dist = [INF]*16; dist[0] = 0
    # min-weight representation: dp over elements (each used at most once)
    for u in U:
        nd = dist[:]
        for x in range(16):
            if dist[x] + 1 < nd[x ^ u]: nd[x ^ u] = dist[x] + 1
        dist = nd
    c = tuple(dist[cb] for cb in cols)
    return r, c
profs = set(); t = time.time()
for mask in range(1, 1 << 15):
    U = [u + 1 for u in range(15) if (mask >> u) & 1]
    r, c = profile(U)
    if max(c) >= 99: continue
    # only gates actually needed matter; keep as is (superset profiles are dominated anyway)
    profs.add((r, c))
print("valid profiles:", len(profs), "time", round(time.time() - t, 1))
def dominated(p, q):  # q dominates p
    return all(x <= y for x, y in zip(q[0] + q[1], p[0] + p[1])) and q != p
pl = list(profs)
par = [p for p in pl if not any(dominated(p, q) for q in pl)]
print("Pareto-minimal profiles:", len(par))
for p in sorted(par, key=lambda p: (max(p[0] + p[1]), sum(p[0] + p[1]))): print(p)
base = [([1, 1], [2, 1], 1), ([2, 1], [1, 1], 1), ([1, 2], [1, 2], 1)]
lib = base + [(list(r), list(c), 2) for r, c in par] + [(list(c), list(r), 2) for r, c in par]
print("tau* with d0<=2 GF(2) gadgets:", tau_star(lib))
import pickle; pickle.dump(par, open("par_gf2_d2.pkl", "wb"))
