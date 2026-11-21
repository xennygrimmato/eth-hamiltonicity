# Check Graham (JNT 1978): sum_{n<=N} Lambda_z(n)^2 = N log z + O(N), Lambda_z(n)=sum_{d|n,d<=z} mu(d) log(z/d)
import numpy as np, sympy, math
N=2*10**6
for z in [10,100,1000]:
    lam=np.zeros(N+1)
    for d in range(1,z+1):
        m=int(sympy.mobius(d))
        if m: lam[d::d]+=m*math.log(z/d)
    s=(lam[1:]**2).sum()
    print("z=%5d  sum/N=%.3f  log z=%.3f  diff=%.3f"%(z,s/N,math.log(z),s/N-math.log(z)))
