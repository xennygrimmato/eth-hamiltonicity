"""rank_Q(H_t) = sum_{lambda |- t, lambda_3 <= 1} dim S^{2 lambda}  (zonal spherical function of
(S_2t,B_t) at the full cycle type is prop. to prod_{cells != (1,1)} (2(j-1)-(i-1)), which vanishes
iff cell (3,2) is in lambda).  Checked against lowrank_hecke.py for t <= 6; growth table here."""
import math
from lowrank_rs import hook_dim, partitions
def rk(t):
    return sum(hook_dim([2*x for x in l]) for l in partitions(t) if len(l) < 3 or l[2] <= 1)
def dfact(t): return math.prod(range(1, 2*t, 2))
prev = None
for t in list(range(1, 13)) + [16, 20, 24, 30]:
    r = rk(t)
    print(f"t={t:2d} rank={r}  (2t-1)!!={dfact(t)}  log2(rank)/t={math.log2(r)/t:.3f}" + (f"  ratio={r/prev:.2f}" if prev and t<=12 else ""))
    prev = r
# per-cut bound: rank(b) <= sum_k C(b,2k) rank(H_k)
for b in (8, 16, 24, 32, 48, 60):
    R = sum(math.comb(b, 2*k)*rk(k) for k in range(1, b//2+1))
    print(f"b={b}: log2(sum_k C(b,2k) rank H_k)/b = {math.log2(R)/b:.3f}")
