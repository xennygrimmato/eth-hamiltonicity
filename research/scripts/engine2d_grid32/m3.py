exec(open('match.py').read().split("np.save")[0])
V=np.load('V.npy'); hv=np.load('hv.npy')
C=[cost(m) for m in Ms]; mc=[min(r,c) for r,c in C]
def rk(A):
    s=np.linalg.svd(A,compute_uv=False); return int((s>1e-8*s[0]).sum())
I0=[i for i in range(len(Ms)) if mc[i]==0]
I2=[i for i in range(len(Ms)) if mc[i]==2]
# orth basis of cost0 span, project out
Q,_=np.linalg.qr(V[I0].T)
Q=Q[:, :32] if False else None
U,s,Vt=np.linalg.svd(V[I0].T,full_matrices=False); B=U[:,s>1e-8*s[0]]
print(B.shape)
proj=lambda x: x-B@(B.T@x)
h=proj(hv)
good=[]
for i in I2:
    w=proj(V[i])
    # h parallel to w?
    if np.linalg.norm(w)>1e-8:
        res=h-w*(w@h)/(w@w)
        if np.linalg.norm(res)<1e-8*np.linalg.norm(h): good.append(i)
print('single cost2 + cost0 span works:',len(good))
# pairs of cost2
import itertools
W=np.array([proj(V[i]) for i in I2])
cnt=0
Wn=W
G=0
for a in range(len(I2)):
    pass
