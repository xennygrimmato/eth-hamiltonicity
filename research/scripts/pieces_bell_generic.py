"""Generic-flag value for S_lambda-symmetric commutative classes with m local types.
Pauli/Bell class: per qubit, E-basis = 4 Bell projectors (rank 1 each), G-basis = sigma_a (x) sigma_a (OSR 1 each).
Types = compositions k of lambda into m parts; cost(type) = log2 multinomial + sum k_a log2 dim_a.
Generic formula: 4 rho lambda = max_i (q1[i] + q2[n-1-i]) over sorted cost lists."""
import math, sys
def comps(l, m):
    if m == 1: yield (l,); return
    for a in range(l+1):
        for r in comps(l-a, m-1): yield (a,)+r
def lmult(k):
    return (math.lgamma(sum(k)+1) - sum(math.lgamma(x+1) for x in k))/math.log(2)
def value(l, dimsE, dimsG):
    m = len(dimsE)
    q1 = sorted(lmult(k)+sum(x*math.log2(d) for x,d in zip(k,dimsE)) for k in comps(l,m))
    q2 = sorted(lmult(k)+sum(x*math.log2(d) for x,d in zip(k,dimsG)) for k in comps(l,m))
    n = len(q1)
    return max(q1[i]+q2[n-1-i] for i in range(n))/(4*l)
if __name__ == "__main__":
    for l in [16, 32, 64, 128, 256]:
        print(l, "Bell(4 types)", round(value(l,[1,1,1,1],[1,1,1,1]),4), " qubit(2 types)", round(value(l,[3,1],[1,3]),4),
              " 3 types [2,1,1]/[1,1,2]", round(value(l,[2,1,1],[1,1,2]),4), flush=True)
