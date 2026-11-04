exec(open('match.py').read().split("np.save")[0])
from collections import Counter
rng=np.random.default_rng(1)
P=rng.standard_normal((1<<NL,200))
V=np.array([vec(m)@P for m in Ms])
hv=vec(H)@P
C=[cost(m) for m in Ms]
mc=[min(r,c) for r,c in C]
print(Counter(mc))
def rk(A): 
    s=np.linalg.svd(A,compute_uv=False); return int((s>1e-8*s[0]).sum())
print('total rank',rk(V))
for k in range(0,7):
    S=V[[i for i in range(len(Ms)) if mc[i]<=k]]
    r1=rk(S); r2=rk(np.vstack([S,hv]))
    print(k,len(S),r1,'H in span' if r1==r2 else 'no')
np.save('V.npy',V); np.save('hv.npy',hv)
