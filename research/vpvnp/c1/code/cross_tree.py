# Crossing inequality (Prop B.3) in random metric trees, hubs ranging over all vertices.
import numpy as np, sys
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
al=np.linspace(0,np.pi/2,91); P=np.cos(al); Q=np.sin(al)
best=-9
for trial in range(3000):
    n=rng.integers(6,25); par=[rng.integers(0,i) for i in range(1,n)]
    L=rng.exponential(size=n-1) if trial%2 else np.ones(n-1)
    D=np.full((n,n),np.inf); np.fill_diagonal(D,0)
    for i,p in enumerate(par,1): D[i,p]=D[p,i]=L[i-1]
    for k in range(n): D=np.minimum(D,D[:,k:k+1]+D[k:k+1,:])
    x,v,y,u=rng.integers(0,n,4)
    A=P*D[x,v]+Q*D[y,u]                                   # (91,)
    S1=(P[:,None,None]*(D[x][None,:,None]+D[v][None,None,:])+Q[:,None,None]*(D[y][None,:,None]+D[u][None,None,:]))
    S2=(P[:,None,None]*(D[x][None,:,None]+D[v][None,None,:])+Q[:,None,None]*(D[u][None,:,None]+D[y][None,None,:]))
    H=D[None]
    def term(S):
        E=np.maximum(A[:,None,None]-S,0)
        with np.errstate(divide='ignore',invalid='ignore'):
            t=np.where(E>1e-12,E**2/H**2,0.)
        return t.reshape(len(al),-1).max(1)
    val=(term(S1)+term(S2)-2).max()
    if val>best: best=val; print(trial,n,best,flush=True)
print('best',best)
