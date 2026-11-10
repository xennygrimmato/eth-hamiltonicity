# moments m_k = E tr(K^k)/N^{k+1}... of the CUE Toeplitz Gram K=[Tr U^{j-l}]_{j,l<N} (bandwidth theta=1),
# true CUE vs "diagonal/Gaussian model" (independent complex Gaussian traces of variance k).
import numpy as np
from scipy.stats import unitary_group
from scipy.linalg import toeplitz
rng=np.random.default_rng(1); N=40; S=1500
def moms(t):
    K=toeplitz(np.concatenate(([N],t)).conj()); ev=np.linalg.eigvalsh(K)/N
    return [np.mean(ev**k) for k in (1,2,3,4)]
A=np.zeros(4);B=np.zeros(4)
for s in range(S):
    z=np.linalg.eigvals(unitary_group.rvs(N,random_state=rng))
    A+=moms(np.array([np.sum(z**k) for k in range(1,N)]))
    k=np.arange(1,N); B+=moms(np.sqrt(k/2)*(rng.standard_normal(N-1)+1j*rng.standard_normal(N-1)))
print("N",N,"CUE      m1..m4:",np.round(A/S,4),"  (sine-process prediction 1, 4/3, 2, 13/4=3.25)")
print("N",N,"Gaussian m1..m4:",np.round(B/S,4),"  (diagonal model: 1, 4/3, 2, 3.35; extremal 3-atom measure has 10/3)")
