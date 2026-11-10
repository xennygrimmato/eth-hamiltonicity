# CUE finite model. Zeros z_a=e^{i t_a}. Gram side G (N x N), nonzero spectrum = that of Toeplitz K.
# rank-trace: n_+ >= (tr G)^2 / tr G^2.  Report rho = (E tr G)^2/(N E tr G^2).
import numpy as np, sys
from scipy.stats import unitary_group
rng=np.random.default_rng(0)
N=int(sys.argv[1]) if len(sys.argv)>1 else 80
S=int(sys.argv[2]) if len(sys.argv)>2 else 200
def dirich(D,d):  # centered Dirichlet kernel of d frequencies at angle differences D
    with np.errstate(divide='ignore',invalid='ignore'):
        k=np.sin(d*D/2)/np.sin(D/2)
    k[np.isclose(np.sin(D/2),0)]=d
    return k
angs=[]
for s in range(S):
    U=unitary_group.rvs(N,random_state=rng)
    t=np.sort(np.angle(np.linalg.eigvals(U))); angs.append(t)
def rho(th1,th2,c,mode):
    a=b=0
    for t in angs:
        D=t[:,None]-t[None,:]
        G=dirich(D,int(round(th1*N)))
        if th2>0:
            if mode=='alt': s=(-1.0)**np.arange(N)
            elif mode=='zp':   # Z'(t_a) normalised by its rms: unmollified derivative
                Z=np.array([np.prod(2*np.sin((t[i]-np.delete(t,i))/2)) for i in range(N)])
                s=Z/np.sqrt(np.mean(Z**2))
            G=G+c*np.outer(s,s)*dirich(D,int(round(th2*N)))
        a+=np.trace(G); b+=np.sum(G*G)
    a/=len(angs); b/=len(angs)
    return a*a/(N*b)
print("baseline th: rho, theory th/(1+th^2/3)")
for th in [0.5,0.75,1.0]:
    print(th, round(rho(th,0,0,'alt'),4), round(th/(1+th*th/3),4))
print("ideal sign-twisted block (alt): th1, th2, best c, rho")
for th1 in [0.5,0.75,1.0]:
    for th2 in [0.25,0.5,1.0]:
        best=max((rho(th1,th2,c,'alt'),c) for c in [0.1,0.2,0.35,0.5,0.75,1.0,1.5,2,3])
        print(th1,th2,best[1],round(best[0],4))
print("unmollified Z' block (zp):")
for th1 in [1.0]:
    for th2 in [0.25,0.5]:
        best=max((rho(th1,th2,c,'zp'),c) for c in [0.01,0.03,0.1,0.2,0.35,0.5,1.0])
        print(th1,th2,best[1],round(best[0],4))
