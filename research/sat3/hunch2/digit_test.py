# Rank profile of Psi_N mod p for size-1 classes of dimension 2^m, and test of digit (Lucas) structure.
import pickle, sys, numpy as np
from crossing_ranks_by_char import rank_mod
q=int(sys.argv[1]); cases=sys.argv[2:]
def load(c):
    S1,S2,X=pickle.load(open(f"psi_{c}.pkl","rb")); return S1,S2,X
def ranks(T,d1,d2,q):
    return (rank_mod(T.reshape(d1*d2,d1*d2),q),rank_mod(T.transpose(0,3,1,2).reshape(d1*d2,d2*d1),q))
for c in cases:
    S1,S2,X=load(c); d1,d2=len(S1),len(S2)
    print("case",c,"dims",d1,d2,"symbols",S1)
    prof=[]
    for N in range(0,X.shape[0],2):
        T=X[N]%q
        if not T.any(): prof.append((N//2,0,0)); continue
        r=ranks(X[N],d1,d2,q); r0=ranks(X[N],d1,d2,2147483629)
        prof.append((N//2,)+r)
        print("  y-degree",N//2,"ranks mod",q,r,"  char0",r0,"  nonzero entries mod q",int((T!=0).sum()))
    print("  #nonzero terms mod",q,":",sum(1 for t in prof if t[1]),"of",len(prof))
