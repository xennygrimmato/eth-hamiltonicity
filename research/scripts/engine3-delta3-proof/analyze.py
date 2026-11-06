import numpy as np, sys, itertools
from d3lib import *
cfg = delta3()
f = cfg.to3_row(cfg.target())
fn = sys.argv[1]; spec = sys.argv[2]
terms = [('row' if t[0]=='r' else 'col', tuple(int(ch) for ch in t[1:])) for t in spec.split('+')]
z = np.load(fn); arrs = [z[k] for k in sorted(z.files, key=lambda s:int(s.split('_')[1]))]
Ws = [arrs[3*k:3*k+3] for k in range(len(terms))]
parts=[]
for k,(kind,b) in enumerate(terms):
    T = tri_net(Ws[k]); parts.append(T if kind=='row' else cfg.from3_col(T))
R, C = parts
print('residual', np.linalg.norm(f-R-C)/np.linalg.norm(f))
def cuts(T):
    r3 = cfg.to3_row(T); c3 = cfg.to3_col(T)
    return [flat_rank(r3,i) for i in range(3)], [flat_rank(c3,i) for i in range(3)]
def rk(M, tol=1e-6):
    s = np.linalg.svd(M, compute_uv=False); return int((s > tol*s[0]).sum())
def cuts2(T):
    r3 = cfg.to3_row(T); c3 = cfg.to3_col(T)
    return [rk(unfold(r3,i)) for i in range(3)], [rk(unfold(c3,i)) for i in range(3)]
for name,T in (('f',f),('R',R),('C',C)):
    print(name, 'row cuts', cuts2(T)[0], 'col cuts', cuts2(T)[1], 'norm', np.linalg.norm(T))
# diagonality: support on x=y?
T18 = lambda T: T.reshape((2,)*18)
mask = cfg.target().astype(bool)
for name,T in (('R',R),('C',C)):
    t = T18(T); on = np.linalg.norm(t[mask]); off = np.linalg.norm(t[~mask]); print(name, 'norm on supp f', on, 'off', off)
# triangle cuts: strings of triangle s
tri = {s:[k for k,(v,i) in enumerate(cfg.strings) if (v[0]+v[1])%3==s] for s in range(3)}
for name,T in (('R',R),('C',C)):
    t = T18(T)
    for s in range(3):
        ax = tri[s]; other=[a for a in range(18) if a not in ax]
        M = np.transpose(t, ax+other).reshape(2**6,-1); print(name,'triangle',s,'| rest rank', rk(M))
# node cuts
for name,T in (('R',R),('C',C)):
    t=T18(T); out=[]
    for v in cfg.nodes:
        ax=[k for k,(u,i) in enumerate(cfg.strings) if u==v]; other=[a for a in range(18) if a not in ax]
        out.append(rk(np.transpose(t,ax+other).reshape(4,-1)))
    print(name,'node ranks',out)
# singular values of R's col-cut 0 and row-cut 0
r3=cfg.to3_row(R); c3=cfg.to3_col(R)
print('R row-cut0 sv', np.round(np.linalg.svd(unfold(r3,0),compute_uv=False)[:20],3))
print('R col-cut0 sv', np.round(np.linalg.svd(unfold(c3,0),compute_uv=False)[:70],3))
print('C row-cut0 sv', np.round(np.linalg.svd(unfold(cfg.to3_row(C),0),compute_uv=False)[:70],3))
