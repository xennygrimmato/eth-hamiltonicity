# [N] Linear regime, k up to 50: (i) simplex config has |Z_S|^2 = k s(k-s)/2 for sampled S;
# (ii) for random and for gradient-optimised antisymmetric unit fields z, the minimum of |Z_S| over
# sampled balanced S (s=ceil(k/3)) never exceeds c_k = sqrt(k s0 (k-s0)/2).
import numpy as np
rng=np.random.default_rng(1)
for k in (10,20,30,40,50):
    s0=-(-k//3); ck=np.sqrt(k*s0*(k-s0)/2)
    d=k
    # simplex
    Z=np.zeros((k,d))
    for a in range(k):
        for b in range(k):
            if a!=b: v=np.zeros(d); v[a]=1; v[b]=-1; Z[a]+=v/np.sqrt(2)
    dev=max(abs(np.linalg.norm(Z[list(S)].sum(0))**2-k*len(S)*(k-len(S))/2)
            for S in [rng.choice(k,size=rng.integers(s0,k-s0+1),replace=False) for _ in range(200)])
    # optimise random field: ascend the mean of |Z_S| over the 50 currently-worst sampled S
    z=rng.normal(size=(k,k,d)); z=z-z.transpose(1,0,2)
    best=0
    for it in range(300):
        zn=z/ (np.linalg.norm(z,axis=2,keepdims=True)+1e-12)
        for a in range(k): zn[a,a]=0
        Za=zn.sum(1)
        Ss=[rng.choice(k,size=s0,replace=False) for _ in range(400)]
        vals=np.array([np.linalg.norm(Za[S].sum(0)) for S in Ss])
        if it>250: best=max(best,vals.min())
        idx=np.argsort(vals)[:50]
        G=np.zeros_like(z)
        for i in idx:
            S=Ss[i]; m=np.zeros(k,bool); m[S]=True
            g=Za[S].sum(0); g/=np.linalg.norm(g)+1e-12
            G[np.ix_(m,~m)]+=g
        G=G-G.transpose(1,0,2)
        z=zn+0.05*G
    print(f"k={k} c_k={ck:.3f} simplex dev={dev:.1e} optimised field: min over sampled S={best:.3f} (ratio {best/ck:.3f})")
