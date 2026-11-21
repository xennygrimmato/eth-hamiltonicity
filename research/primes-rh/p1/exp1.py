# Failure statistics of parity-query families on real primes (<=2.1e9).
import numpy as np, sys
P=np.load(sys.argv[1]).astype(np.int64)
rng=np.random.default_rng(1)
def cnt(a,b): # primes in [a,b]
    return np.searchsorted(P,b,'right')-np.searchsorted(P,a,'left')
def seg(a,b): return P[np.searchsorted(P,a,'left'):np.searchsorted(P,b,'right')]
print("E1: parity of pi([N,2N]) over N random in [1e6,1e9]")
Ns=rng.integers(10**6,10**9,20000)
od=(cnt(Ns,2*Ns)%2); print(" frac odd",od.mean())
# consecutive N: run lengths of even parity of pi([N,2N]) as N varies by 1 (parity changes when N or 2N prime)
print("E2: windows W=[N,N+h]: frac pi even, frac XOR==0 (all bit-class parities even)")
for e in [4,6,8,10,12,14,16,20]:
    h=2**e; Ns=rng.integers(10**8,10**9,4000 if e<16 else 400)
    ev=0; x0=0; emp=0
    for N in Ns:
        s=seg(N,N+h); 
        if len(s)==0: emp+=1
        ev+= len(s)%2==0; x0+= (np.bitwise_xor.reduce(s) if len(s) else 0)==0
    print(f"  h=2^{e}: even {ev/len(Ns):.3f}  xor0 {x0/len(Ns):.4f}  empty {emp/len(Ns):.4f}")
print("E3: geometric prefix family [N,N+2^i]; index of first odd; also XOR family")
worst=0; hist={}; worstx=0
Ns=rng.integers(10**8,2*10**9,200000)
for N in Ns:
    i=0
    while cnt(N,N+2**i)%2==0: i+=1
    hist[i]=hist.get(i,0)+1; worst=max(worst,i)
print("  first-odd index histogram",sorted(hist.items()))
# XOR family: first i with XOR(primes in [N,N+2^i]) != 0
hist={}
for N in Ns[:50000]:
    i=0
    while True:
        s=seg(N,N+2**i)
        if len(s) and np.bitwise_xor.reduce(s)!=0: break
        i+=1
    hist[i]=hist.get(i,0)+1
print("  XOR first-nonzero index histogram",sorted(hist.items()))
