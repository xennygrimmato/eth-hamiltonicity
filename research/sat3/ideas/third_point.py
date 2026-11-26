# Test: does the crossing-identity polynomial Psi(X) carry a THIRD rank grading at a third point of P^1?
# Phi_M = coefficient of (X-pt)^M in Psi(X) = sum_N C(N,M) pt^(N-M) Psi_N.  Ranks across the three cuts, mod p.
import sys, numpy as np
from math import comb
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/ports/protocol')
from crossing_identity_modp import psi, rankmod, p
n1,e1,n2,e2 = map(int, sys.argv[1:5])
pts = [int(x) for x in sys.argv[5:]] or [1]
S1,S2,coef = psi(n1,e1,n2,e2)
d1,d2 = len(S1),len(S2); Th = 2*(e1+e2)
print("dims",d1,d2,"Theta",Th)
def ranks(T):
    return (rankmod(T.reshape(d1*d2,d1*d2)),
            rankmod(T.transpose(0,3,1,2).reshape(d1*d2,d2*d1)),
            rankmod(T.transpose(0,2,1,3).reshape(d1*d1,d2*d2)))
print("X^N coefficients (ab|cd, ad|bc, ac|bd):")
for N in range(Th+1):
    if coef[N].any(): print(" N",N,ranks(np.array(coef[N],dtype=object)))
for pt in pts:
    print("expansion at X =",pt,": (ab|cd, ad|bc, ac|bd) of Phi_M and of partial sums span test")
    for M in range(Th+1):
        acc = 0
        for N in range(M,Th+1):
            acc = acc + (comb(N,M)*pow(pt % p, N-M, p) % p)*coef[N]
        acc = acc % p
        if acc.any(): print(" M",M,ranks(np.array(acc,dtype=object)))
