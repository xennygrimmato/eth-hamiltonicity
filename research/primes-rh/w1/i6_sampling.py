# I6: residue-mod-M scanning of disjoint windows of length h ~ M log x / 2 (expected count M/2).
# Fraction of windows with pi == 0 mod M, and longest run of consecutive bad windows.
import numpy as np, sympy, math
x=10**9; W=2*10**7
P=np.array(list(sympy.primerange(x,x+W)))
for M in [4,8,16,32]:
    h=int(M*math.log(x)/2)
    c=np.bincount((P-x)//h, minlength=W//h)[:W//h]
    bad=(c%M==0)
    run=0;best=0
    for b in bad:
        run=run+1 if b else 0; best=max(best,run)
    print(f"M={M} h={h}: windows {len(c)}, bad fraction {bad.mean():.4f}, longest bad run {best}, mean count {c.mean():.1f} sd {c.std():.1f}")
