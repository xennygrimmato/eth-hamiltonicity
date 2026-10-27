"""Closed-form ('generic flag') value of the commutative tensor-power classes.

Two generic flags in C^n admit a common adapted basis v_1..v_n with A_a=<v_1..v_a>, B_b=<v_{n-b+1}..v_n>,
so A_a cap B_b = <v_{n-b+1},...,v_a>.  Pieces cheapest-first => F in the span iff the intervals cover [1,n]
iff  B >= max_i ( q1[i] + q2[n-1-i] )  with q1,q2 the sorted cost lists.  Asymptotically
     4 rho = max_x ( Q1(x) + Q2(1-x) ),  Q = quantile function of the per-block cost over the type simplex
(uniform measure on types, NOT entropy-weighted).
"""
import math, sys
import numpy as np
def lgC(n,k): return (math.lgamma(n+1)-math.lgamma(k+1)-math.lgamma(n-k+1))/math.log(2)
def discrete(l, dE=(3,1), dG=(1,3)):
    f1 = sorted(lgC(l,k)+(l-k)*math.log2(dE[0])+k*math.log2(dE[1]) for k in range(l+1))
    f2 = sorted(lgC(l,j)+(l-j)*math.log2(dG[0])+j*math.log2(dG[1]) for j in range(l+1))
    n = l+1
    return max(f1[i]+f2[n-1-i] for i in range(n))/(4*l)
def H(p): 
    p = np.clip(p,1e-300,1); q=np.clip(1-p,1e-300,1); return -(p*np.log2(p)+q*np.log2(q))
def continuum(dE=(3,1), dG=(1,3), M=2_000_001):
    k = np.linspace(0,1,M)
    f1 = np.sort(H(k)+(1-k)*np.log2(dE[0])+k*np.log2(dE[1]))
    f2 = np.sort(H(k)+(1-k)*np.log2(dG[0])+k*np.log2(dG[1]))
    s = f1 + f2[::-1]
    i = np.argmax(s)
    return s[i]/4, k[i]
if __name__ == "__main__":
    for l in [32,64,128,256,1024,4096]:
        print("discrete", l, discrete(l))
    print("qubit class continuum rho, argmax x:", continuum())
    print("log12/4 =", math.log2(12)/4)
    # quaternion (N=4) and octonion (N=8) 2-dim classes, per block of b bits: normalise by b
    for N,b in [(4,2),(8,3)]:
        r, x = continuum(dE=(N, N*N-N), dG=(N, N*N-N))
        print(f"Hurwitz N={N} class: rho = {r/b:.4f}")
