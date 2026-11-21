import numpy as np
def isprime_table(N):
    s=np.ones(N+1,dtype=bool); s[:2]=False
    for p in range(2,int(N**0.5)+1):
        if s[p]: s[p*p::p]=False
    return s
def primes_upto(N):
    return np.nonzero(isprime_table(N))[0]
def seg_isprime(lo,hi):
    """bool array for [lo,hi)"""
    s=np.ones(hi-lo,dtype=bool)
    for p in primes_upto(int(hi**0.5)+1):
        st=max(p*p,((lo+p-1)//p)*p)
        s[st-lo::p]=False
    if lo<2: s[:2-lo]=False
    return s
