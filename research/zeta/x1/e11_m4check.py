# exact Wick value of m4 for the Gaussian-trace (diagonal) model at finite N, vs CUE simulation.
import numpy as np
from scipy.stats import unitary_group
from scipy.linalg import toeplitz
def gauss_m4(N):
    i=np.arange(N); g=np.abs(i[:,None]-i[None,:]).sum(1).astype(float)   # sum_j |i-j|
    S2=(g**2).sum()
    k=np.arange(1,N); S1=0.0
    for a in k:
        m=k[k<=N-1-a]            # |kappa|+|mu| <= N-1
        S1+= (a*m*(N-a-m)).sum()
    S1*=4                         # four sign combinations, span |kappa|+|mu|
    trP2=2*(k*(N-k)).sum()
    return 1+6*trP2/N**3+(2*S2+S1)/N**5, trP2/N**3
for N in [20,40,200,1000]:
    print("Gaussian model exact N=%d: m4=%.5f  (m2-1=%.5f)"%((N,)+gauss_m4(N)))
print("limit 49/15 =",49/15)
rng=np.random.default_rng(5); N=20; S=60000; acc=[]
for s in range(S):
    z=np.linalg.eigvals(unitary_group.rvs(N,random_state=rng))
    t=np.array([np.sum(z**k) for k in range(1,N)])
    ev=np.linalg.eigvalsh(toeplitz(np.concatenate(([N],t)).conj()))/N
    acc.append(np.mean(ev**4))
acc=np.array(acc); print("CUE N=20: m4 = %.5f +- %.5f ; Gaussian exact N=20: %.5f ; difference %.5f (prediction -1/60=%.5f)"%(acc.mean(),acc.std()/np.sqrt(S),gauss_m4(20)[0],acc.mean()-gauss_m4(20)[0],-1/60))
