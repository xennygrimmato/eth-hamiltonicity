from swap_split import run
import sys
n=int(sys.argv[1]); rmax=int(sys.argv[2])
prev=n*n
for r in range(1,rmax+1):
    for s in range(0,prev+1):
        b=run(n,r,s,iters=1500,restarts=6,seed=r)
        if b<1e-7: print(f"n={n} r={r}: min s = {s} (res {b:.1e})",flush=True); prev=s; break
