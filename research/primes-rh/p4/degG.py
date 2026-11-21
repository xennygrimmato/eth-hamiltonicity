# deg over GF(2) of G_Q = lcm_{q<=Q}(t^q-1) = prod_{d odd<=Q} Phi_d^{2^floor(log2(Q/d))}
from sympy import totient
import math
for Q in [10,100,1000,10000]:
    s=0
    for d in range(1,Q+1,2):
        e=1
        while 2*e*d<=Q: e*=2
        s+=int(totient(d))*e
    print(Q, s, s/Q**2)
