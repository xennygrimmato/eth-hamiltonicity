"""min sopfr(c) over c = -1 mod k^2 (cost of the c^omega weight in the mod-k chain), vs log k. Also for prime powers."""
import heapq, math, sys
from sympy import primerange, factorint
def best(k):
    M = k*k; tgt = M-1
    gens = [p for p in primerange(2, 3*M+50) if k % p]
    dist = {1 % M: 0}; pq = [(0, 1 % M, 1)]
    while pq:
        d, u, c = heapq.heappop(pq)
        if u == tgt: return d, c
        if dist[u] < d: continue
        for p in gens:
            nd = d + p
            if nd > dist.get(tgt, 10**18): break
            v = u*p % M
            if nd < dist.get(v, 10**18): dist[v] = nd; heapq.heappush(pq, (nd, v, c*p))
ks = [int(a) for a in sys.argv[1:]] or [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,53,59,61,64,67,71,73,79,81,83,89,97,101,113,125,127,128,256]
for k in ks:
    s, c = best(k)
    print(f"k={k:4d} min sopfr={s:4d}  c={c} = {factorint(c)}  sopfr/ln k={s/math.log(k):.2f}  naive k^2-1={k*k-1}")
