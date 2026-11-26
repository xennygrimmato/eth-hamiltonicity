#!/usr/bin/env python3
"""Float value n*(B) of the bucket game using the symmetry group (S_3 on v1,v2,v3 x u1<->u2, order 12).
    python3 game_values_sym.py B
Solves one LP per orbit of types (same LP as make_certs.py), 4 processes.  Prints n*(B), the worst
orbit representative and the next ones.  For B <= 8 it also checks invariance on all types.
Floating point only (no certificate)."""
import sys, itertools, time; sys.path.insert(0,'.')
import make_certs as M, verify as V
from multiprocessing import Pool
VP=V.VP
def act(sig,flip,tau,B):
    # sig: permutation of v indices (2,3,4)->...
    out=[None]*3
    for e,(i,j) in enumerate(VP):
        x,y=sig[i],sig[j]
        k=tau[e]
        if (x,y) in VP: f=VP.index((x,y)); rev=False
        else: f=VP.index((y,x)); rev=True
        if rev!=flip: k=B-1-k
        out[f]=k
    return tuple(out)
G=[(dict(zip((2,3,4),p)),fl) for p in itertools.permutations((2,3,4)) for fl in (False,True)]
def orbit_rep(tau,B): return min(act(s,f,tau,B) for s,f in G)
B=int(sys.argv[1]); bk=V.buckets(B)
def val(t): return t,M.solve_type(t,bk).fun
if __name__=='__main__':
    reps=sorted({orbit_rep(t,B) for t in itertools.product(range(B),repeat=3)})
    t0=time.time()
    with Pool(4) as p: vals=dict(p.map(val,reps,chunksize=64))
    if B<=8:  # check invariance
        md=max(abs(M.solve_type(t,bk).fun-vals[orbit_rep(t,B)]) for t in itertools.product(range(B),repeat=3))
        print("invariance check maxdiff",md)
    top=sorted(vals.items(),key=lambda kv:-kv[1])[:4]
    mid=[k for k in range(B) if k in (B//2-1,B//2)]
    print("B",B,"reps",len(reps),"n*",top[0][1],"at",top[0][0],"top",top,"time",time.time()-t0, flush=True)
