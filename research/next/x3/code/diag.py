# smallest k with SWAP_n = R + L, opSR(R)<=k, rank(L)<=k (alternating projections)
from swap_split import run
import sys
n=int(sys.argv[1])
for k in map(int,sys.argv[2].split(',')):
    b=run(n,k,k,iters=int(sys.argv[3]),restarts=int(sys.argv[4]),seed=k)
    print(f"n={n} r=s={k} res={b:.2e}",flush=True)
