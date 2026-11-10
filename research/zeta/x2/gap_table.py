"""Lead task (1): bound(c,lambda) in the DNN model: row (1/N) E#{ordered distinct pairs, 0<|x_j-x_k|<lambda} >= c,
which is implied by 'a proportion c of zeros (with multiplicity) have a distinct zero within lambda'."""
import sys, numpy as np
from circle_dnn_gap import dnn_gap
N=int(sys.argv[1]); M=12*N
base=dnn_gap(N,M,0.5,0.0)
print('N=%d base %.4f'%(N,base),flush=True)
for lam in [0.3,0.5,0.7,0.9]:
    row=[]
    for c in [0.01,0.02,0.05,0.10]:
        v=dnn_gap(N,M,lam,c); row.append(v)
    print('lam=%.1f '%lam+' '.join('c=%.2f:%.4f(+%.4f)'%(c,v,v-base) for c,v in zip([0.01,0.02,0.05,0.10],row)),flush=True)
