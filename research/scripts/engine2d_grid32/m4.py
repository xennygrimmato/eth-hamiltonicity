exec(open('match.py').read().split("np.save")[0])
import sympy
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix, hstack, vstack, identity
C=[cost(m) for m in Ms]
# exact coordinates: pick 132 basis entries
rng=np.random.default_rng(0)
full=np.array([vec(m) for m in Ms],dtype=np.int8)   # 10395 x 4096 ~ 42MB
hfull=vec(H).astype(np.int8)
# greedy select columns giving rank 132 using float QR on subset of matchings
sub=full[rng.choice(len(Ms),400,replace=False)].astype(float)
_,_,piv=__import__('scipy.linalg',fromlist=['qr']).qr(sub,pivoting=True,mode='economic')
cols=piv[:132]
A=full[:,cols].astype(float); h=hfull[cols].astype(float)
print('rank',np.linalg.matrix_rank(A))
np.save('A.npy',A); np.save('h.npy',h); np.save('C.npy',np.array(C))
