# Idea 3 test: mollified rank-trace  n_+(K) >= (tr KR)^2 / tr(KRKR),  R = I + c*Q/N,
# K = Toeplitz[Tr U^{j-l}] (d = theta N),  Q = Toeplitz of the same traces truncated to |k|<=eta N.
import numpy as np
from scipy.stats import unitary_group
from scipy.linalg import toeplitz
rng=np.random.default_rng(0); N=60; S=300
tr=[]
for s in range(S):
    z=np.linalg.eigvals(unitary_group.rvs(N,random_state=rng))
    tr.append(np.array([np.sum(z**k) for k in range(N+1)]))
def ratio(theta,eta,c):
    d=int(round(theta*N)); y=int(round(eta*N)); A=B=0
    for t in tr:
        K=toeplitz(t[:d].conj()); 
        q=t[:d].copy(); q[0]=0; q[y+1:]=0
        R=np.eye(d)+c*toeplitz(q.conj())/N
        KR=K@R; A+=np.trace(KR).real; B+=np.trace(KR@KR).real
    A/=S;B/=S
    return A*A/B/N
for theta,eta in [(1.0,0.0),(0.9,0.1),(0.8,0.2),(0.7,0.3),(0.5,0.5),(1.0,0.2),(1.0,0.5)]:
    best=max((ratio(theta,eta,c),c) for c in [0,-0.25,-0.5,-0.75,-1.0])
    print(f"theta_K={theta} eta_R={eta}: best ratio/N={best[0]:.4f} at c={best[1]}   (unmollified {theta/(1+theta**2/3):.4f})")
