exec(open('cert.py').read().split("mH=mincut")[0])
from scipy.optimize import linprog
mH=mincut(*struct('H',None))
# column: mincut(alpha)=min(A, B+alpha); compute A (bond infinite -> merge), B (bond 0)
mA=mincut(*struct('col',100)); mB=mincut(*struct('col',0))
colmin=np.where(mA>=mH, np.maximum(mH-mB,0), 99)
print('colmin dist',np.unique(colmin,return_counts=True))
# row LP for candidate patterns
n,E=struct('row',{(0,1):0,(0,2):0,(1,2):0})
const,inS=cutvals(n,E)
subs=np.arange(1<<9); inSf=((subs[:,None]>>np.arange(9))&1)
bondcut=np.stack([(inSf[:,6+r]!=inSf[:,6+s]) for r,s in [(0,1),(0,2),(1,2)]],1).astype(float)
def rowmin(k):
    base=const+(Y[k]*inS).sum(1)+(X[k]*(1-inS)).sum(1)
    # constraints: base_S + bondcut_S . a >= mH  ->  -bondcut a <= base - mH
    r=linprog(np.ones(3),A_ub=-bondcut,b_ub=base-mH[k],bounds=[(0,None)]*3,method='highs')
    return r.fun if r.status==0 else 99, (r.x if r.status==0 else None)
cand=np.where(colmin>=2.5)[0]
print('candidates',len(cand))
best=[]
for k in cand:
    v,a=rowmin(k)
    best.append((min(v,colmin[k]),v,colmin[k],k,a))
best.sort(key=lambda z:-z[0])
for b in best[:10]: print('min',b[0],'row',b[1],'col',b[2],'x',X[b[3]],'y',Y[b[3]],'mH',mH[b[3]],'a',b[4])
