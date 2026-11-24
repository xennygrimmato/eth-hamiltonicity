from swap_split import run
import sys
n=int(sys.argv[1]); r=int(sys.argv[2])
for s in map(int,sys.argv[3].split(',')):
    b=run(n,r,s,iters=int(sys.argv[4]) if len(sys.argv)>4 else 2000,restarts=6,seed=s)
    print(f"n={n} r={r} s={s} res={b:.2e}",flush=True)
