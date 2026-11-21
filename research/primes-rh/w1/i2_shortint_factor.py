# I2: integers in [Y,Y+W] with a prime factor in [x,2x], Y ~ x^k. Max gap between such integers vs prime gaps.
import numpy as np, sympy, sys, random
random.seed(1)
for x,k in [(10**4,2),(10**5,2),(10**4,3),(10**6,2)]:
    P=np.array(list(sympy.primerange(x,2*x+1)),dtype=object)
    W=200000
    worst=0; res=[]
    for trial in range(5):
        Y=random.randint(x**k, 2*x**k)
        mark=np.zeros(W,dtype=bool)
        for p in P:
            p=int(p); s=(-Y)%p
            mark[s::p]=True
        pos=np.flatnonzero(mark)
        g=np.diff(pos).max(); worst=max(worst,g)
        res.append((mark.mean(),g))
    dens=np.mean([r[0] for r in res])
    print(f"x={x} Y~x^{k}: density {dens:.4f} (ln2/ln x={np.log(2)/np.log(x):.4f}) max gap in window {W}: {worst}  vs sqrt(x)={x**0.5:.0f}, log^2 x={np.log(x)**2:.0f}")
