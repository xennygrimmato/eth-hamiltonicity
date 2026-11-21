"""Do real primes look like the all-even adversary? (p3, subtask 3 part 2)
Segmented sieve of [N, N+W); block-parity statistics; a deterministic doubling strategy.
Usage: python3 realparity.py [N] [W]
"""
import numpy as np, sys, math

def base_primes(m):
    s = np.ones(m + 1, bool); s[:2] = False
    for p in range(2, int(m ** .5) + 1):
        if s[p]: s[p*p::p] = False
    return np.flatnonzero(s)

def seg_sieve(N, W):
    s = np.ones(W, bool)
    for p in base_primes(int(math.isqrt(N + W)) + 1):
        st = max(p * p, ((N + p - 1) // p) * p)
        s[st - N::p] = False
    return s

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**12
W = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10**7
s = seg_sieve(N, W)
P = np.flatnonzero(s)
print(f"N={N:.3g} W={W:.3g} primes={len(P)} (W/logN={W/math.log(N):.0f}) maxgap={np.diff(P).max()}")
c = np.concatenate(([0], np.cumsum(s)))
for h in [8, 30, 100, 1000, 10000]:
    nb = W // h
    blk = c[h::h][:nb] - c[0:nb*h:h][:nb]
    par = blk % 2
    # longest run of even blocks
    run = best = 0
    for b in par:
        run = run + 1 if b == 0 else 0; best = max(best, run)
    # empty-block run (forced even) vs even-but-nonempty
    print(f"h={h:6d}: blocks={nb:7d} frac odd={par.mean():.4f} longest even run={best:3d} "
          f"(coin-flip expect ~{math.log2(nb):.1f}) frac even&nonempty={((par==0)&(blk>0)).mean():.4f}")
# deterministic doubling strategy from many starts: first j with pi([y, y+2^j)) odd
js = []
for y in range(0, W - 2**22, 997):
    j = 0
    while c[y + 2**j] - c[y] & 1 == 0:
        j += 1
    js.append(j)
js = np.array(js)
print("doubling strategy: first j with odd count, distribution:",
      {int(k): int(v) for k, v in zip(*np.unique(js, return_counts=True))})
print(f"  mean queries {js.mean():.2f}, max {js.max()} over {len(js)} starts; then bisection = j more queries")
