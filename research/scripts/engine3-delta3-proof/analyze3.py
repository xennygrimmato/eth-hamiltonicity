import numpy as np, sys
from d3lib import *
cfg = delta3(); f = cfg.to3_row(cfg.target())
fn, spec = sys.argv[1], sys.argv[2]
terms = [('row' if t[0]=='r' else 'col', tuple(int(ch) for ch in t[1:])) for t in spec.split('+')]
z = np.load(fn); arrs = [z[k] for k in sorted(z.files, key=lambda s:int(s.split('_')[1]))]
Ws = [arrs[3*k:3*k+3] for k in range(len(terms))]
parts=[(tri_net(Ws[k]) if kind=='row' else cfg.from3_col(tri_net(Ws[k]))) for k,(kind,b) in enumerate(terms)]
R, C = parts
def rk(M, tol=1e-6):
    s = np.linalg.svd(M, compute_uv=False); return int((s > tol*s[0]).sum())
eleg = {i:[k for k,(v,j) in enumerate(cfg.strings) if j==i] for i in range(9)}
def rowpair(e): return tuple(sorted((e[0][0],e[1][0])))
def colpair(e): return tuple(sorted((e[0][1],e[1][1])))
for name,T in (('R',R),('C',C)):
    t=T.reshape((2,)*18)
    out=[]
    for i,e in enumerate(cfg.edges):
        ax=eleg[i]; other=[a for a in range(18) if a not in ax]
        out.append((e, rowpair(e), colpair(e), rk(np.transpose(t,ax+other).reshape(4,-1))))
    print(name); [print('  ',o) for o in out]
