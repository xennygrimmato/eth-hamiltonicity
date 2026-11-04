exec(open('match.py').read().split("np.save")[0])
sel=np.load('sol_min_0.0.npy')
A=np.load('A.npy'); h=np.load('h.npy')
al,res,_,_=np.linalg.lstsq(A[sel].T,h,rcond=None); print('coef',al.round(4),'res',np.abs(A[sel].T@al-h).max())
# verify in full space
V=sum(a*vec(Ms[i]) for a,i in zip(al,sel)); print('full residual',np.abs(V-vec(H)).max())
oddlegs=[l for l in range(12) if col(node(l))==0]; evenlegs=[l for l in range(12) if col(node(l))==1]
def colflat(v):
    t=v.reshape([2]*12)  # index order: bit l is (idx>>l)&1 -> reshape gives axis 0 = highest bit l=11
    axes=[11-l for l in oddlegs]+[11-l for l in evenlegs]
    return t.transpose(axes).reshape(64,64)
for grp in ['col','row']:
    G=[(a,i) for a,i in zip(al,sel) if (min(cost(Ms[i]))==cost(Ms[i])[1])==(grp=='col')]
    print(grp,[cost(Ms[i]) for a,i in G])
    if grp=='col':
        S=sum(a*vec(Ms[i]) for a,i in G); print('grouped col rank',np.linalg.matrix_rank(colflat(S)))
for m in [Ms[i] for i in sel]: print(m, cost(m))
