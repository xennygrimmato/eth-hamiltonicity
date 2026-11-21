# Idea 6: bootstrap. Given a prime p ~ sqrt(x), search N = k p + 1 in [x,2x] (Pocklington-certifiable).
# Empirical least k vs the GRH-provable bound (least prime = 1 mod p is << (p log p)^2, i.e. k << p log^2 p).
import numpy as np, math
from sympy import isprime, nextprime
for x in [10**8,10**10,10**12,10**14,10**16]:
    worst=0; tot=0; trials=300
    p=nextprime(math.isqrt(x))
    for t in range(trials):
        k0=-(-x//p); k=k0
        while not isprime(k*p+1): k+=1
        worst=max(worst,k-k0); tot+=k-k0; p=nextprime(p)
    print(f"x=1e{round(math.log10(x))}: p~sqrt x; mean extra k={tot/trials:.1f} worst={worst}  (log x={math.log(x):.1f}); "
          f"candidates GRH guarantees: ~ x/p ~ {x/p:.2e} = sqrt(x)")
