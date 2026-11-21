# I5: cheap exact z-rough indicator via Bezout (gcd(m,P(z))=1 <=> exists u: u m = 1 mod P(z)),
# P(z) must have O(n) bits => z ~ c log x.  Certifying weight w = 1_rough(z) * (1 - s_z(m)),
# s_z = #divisors in [z, sqrt m]. w<=0 on composites, =1 on primes>z. Is Sum w > 0 ?
import numpy as np, sympy, sys, math
x=int(float(sys.argv[1])); W=int(float(sys.argv[2]))
lo=x; m=np.arange(lo,lo+W,dtype=np.int64)
r=int(math.isqrt(lo+W))+1
small=list(sympy.primerange(2,10**4))
pi=sum(1 for v in range(lo,lo+W) if sympy.isprime(v))
print("x",x,"window",W,"primes",pi,"log x",round(math.log(x),1))
for z in [20,50,100,200,500,1000,3000,10000]:
    rough=np.ones(W,dtype=bool)
    for p in small:
        if p>=z: break
        rough[(-lo)%p::p]=False
    s=np.zeros(W,dtype=np.int64)
    for d in range(z,r+1):
        st=(-lo)%d
        if st>=W: continue
        idx=np.arange(st,W,d)
        s[idx]+=(d*d<=m[idx])
    w=(rough*(1-s)).sum()
    bits=sum(math.log2(p) for p in small if p<z)
    print(f"z={z}: P(z) has {bits:.0f} bits (= {bits/math.log2(x):.1f} n); rough={rough.sum()} sum w={w}  (need >0)",flush=True)
