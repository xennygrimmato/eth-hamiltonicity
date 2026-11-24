# [N] check of the linear-regime formula: for the simplex configuration z_ab=(e_a-e_b)/sqrt2,
# |Z_S|^2 = k s (k-s)/2 for every S, and the triangle bound sum_a |Z_a|^2 <= k^2(k-1)/2
# for random antisymmetric unit vectors; plus E.10's configuration value min_S |w_S|.
import itertools, numpy as np
rng=np.random.default_rng(0)
def ZS(z,S,k):
    return sum(z[a][b] for a in S for b in range(k) if b not in S)
for k in range(4,11):
    d=k
    zs={a:{} for a in range(k)}
    for a in range(k):
        for b in range(k):
            if a!=b:
                v=np.zeros(d); v[a]=1; v[b]=-1; zs[a][b]=v/np.sqrt(2)
    bal=[S for s in range(1,k) if k<=3*s<=2*k for S in itertools.combinations(range(k),s)]
    vals=[np.linalg.norm(ZS(zs,set(S),k))**2 - k*len(S)*(k-len(S))/2 for S in bal]
    # E.10 config: wire ab (a<b) direction -e_a  (end (a,b) at e_a/2, (b,a) at -e_a/2)
    ze={a:{} for a in range(k)}
    for a in range(k):
        for b in range(a+1,k):
            v=np.zeros(d); v[a]=-1; ze[a][b]=v; ze[b][a]=-v
    e10=min(np.linalg.norm(ZS(ze,set(S),k)) for S in bal)
    # random antisymmetric unit vectors: sum |Z_a|^2 <= k^2(k-1)/2
    worst=0
    for t in range(200):
        zr={a:{} for a in range(k)}
        for a in range(k):
            for b in range(a+1,k):
                v=rng.normal(size=d); v/=np.linalg.norm(v); zr[a][b]=v; zr[b][a]=-v
        tot=sum(np.linalg.norm(sum(zr[a][b] for b in range(k) if b!=a))**2 for a in range(k))
        worst=max(worst,tot/(k*k*(k-1)/2))
    s0=-(-k//3)
    print(k,"simplex dev",max(abs(x) for x in vals),"c_k=",np.sqrt(k*s0*(k-s0)/2),"E10 min|w_S|=",round(e10,3),"rand sum|Za|^2/bound max",round(worst,3))
