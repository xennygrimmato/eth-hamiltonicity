# Dump integer Psi_N (CRT lift) to a pickle and check the identity sum_N Psi_N = +-<S1>_ac<S2>_bd over Z
# (so in particular mod 2 the right-hand side is a 0/1 permutation tensor, not 0).
import sys, pickle, numpy as np
from crossing_ranks_by_char import integer_psi, rank_mod
n1,e1,n2,e2=map(int,sys.argv[1:5])
S1,S2,X,ok,M=integer_psi(n1,e1,n2,e2)
d1,d2=len(S1),len(S2)
tot=X.sum(axis=0)
want=np.zeros((d1,d2,d1,d2),dtype=object)
for ia,sa in enumerate(S1):
    for ib,sb in enumerate(S2):
        for ic,sc in enumerate(S1):
            for id_,sd in enumerate(S2):
                if sc[1]==sa[0] and sc[0]==sa[1] and sb[1]==sd[0] and sb[0]==sd[1]: want[ia,ib,ic,id_]=1
sgn=None
for s in (1,-1):
    if (tot==s*want).all(): sgn=s
print("dims",d1,d2,"CRT ok",ok,"integer identity sum_N Psi_N = sign*perm tensor, sign =",sgn,
      "; RHS mod 2 nonzero entries:",int((want%2).sum()),"= d1*d2 =",d1*d2)
pickle.dump((S1,S2,X),open(f"psi_{n1}_{e1}_{n2}_{e2}.pkl","wb"))
