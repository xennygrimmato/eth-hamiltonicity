import numpy as np, sys
from fastnum import *
def K1dd(x):
    x=np.atleast_1d(x); return -2*(np.cos(2*np.pi*np.outer(x,A1))*(R1*(2*np.pi*A1)**2)*W1).sum(1)
K1dd0 = K1dd(0)[0]
print('K1dd(0)=',K1dd0)
zs=[1.0498]+[2*k/3 for k in range(3,200)]
v=K1dd(np.array(zs))
print('K1dd at zeros', [(round(z,3), round(float(w),4)) for z,w in zip(zs[:12],v[:12])])
print('S+ (both sides, zeros<=15.5)', 2*np.clip(v[np.array(zs)<=15.5],0,None).sum()/abs(K1dd0),
      ' all', 2*np.clip(v,0,None).sum()/abs(K1dd0), ' S_abs', 2*abs(v).sum()/abs(K1dd0))
def R4(y, X=15.5, h=1e-3, dmax=0.7):
    x=np.arange(0,X,h)+h/2
    g=-Gf(x,y); neg=g>0
    # pieces: runs of neg split at length dmax
    tot=0; i=0; n=len(x); pieces=0
    kap=lambda d: K(np.array([d]))[0]
    while i<n:
        if not neg[i]: i+=1; continue
        j=i
        while j<n and neg[j] and (j-i+1)*h<=dmax: j+=1
        gg=g[i:j].max(); d=(j-i)*h; kk=kap(d)
        hc = 8*gg if 2*gg<=kk else (2*gg+kk)**2/kk
        tot+=hc; pieces+=1; i=j
    return 2*tot/(2*Delta(y)), pieces
for y in [1e-3,3e-3,0.01,0.03,0.1,0.2,0.3,0.5,0.6,0.7,0.75,0.8,0.9,1.0,1.2,1.5,2,3]:
    print(y, R4(y))
