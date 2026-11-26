# Arc-coverage test.  Units: p=ln d1, q=ln d2.  A Euclidean parallelogram whose wires cross at angle theta
# needs a term with ln rank(ab|cd) >= r*(theta), ln rank(ad|bc) >= r'*(theta), r*^2 = p^2+q^2+2pq cos(theta),
# r'*^2 = p^2+q^2-2pq cos(theta) (a point of the arc r^2+r'^2 = 2(p^2+q^2)).  We report, WITHOUT any entropy
# allowance for the number of terms (i.e. the most favourable reading for the hunch), the fraction of the arc
# not covered by a single term of the mod-q identity.  Uncovered fraction 0 = outcome (i): no gain.
import pickle, sys, numpy as np
from math import log, sqrt, cos, pi
from crossing_ranks_by_char import rank_mod
SL=float(sys.argv[1])
for c in sys.argv[2:]:
    S1,S2,X=pickle.load(open(f"psi_{c}.pkl","rb")); d1,d2=len(S1),len(S2); p,q_=log(d1),log(d2)
    for ch in (2,3,5,7,2147483629):
        pts=[]
        for N in range(X.shape[0]):
            if not (X[N]%ch).any(): continue
            r1=rank_mod(X[N].reshape(d1*d2,d1*d2),ch); r2=rank_mod(X[N].transpose(0,3,1,2).reshape(d1*d2,d2*d1),ch)
            pts.append((log(r1),log(r2),N,r1,r2))
        unc=0; K=2000; worst=None
        for k in range(K+1):
            th=pi*k/K
            rs=sqrt(max(0,p*p+q_*q_+2*p*q_*cos(th))); rp=sqrt(max(0,p*p+q_*q_-2*p*q_*cos(th)))
            if not any(a>=rs-SL and b>=rp-SL for a,b,_,_,_ in pts):
                unc+=1
        best=max(pts,key=lambda t:min(t[0],t[1]))
        print(f"case {c} dims {d1}x{d2} char {ch if ch<100 else 0}: terms {len(pts)}, uncovered arc fraction (slack {SL:.3f} nats per coordinate) {unc/(K+1):.3f}, "
              f"most balanced term N={best[2]} ranks ({best[3]},{best[4]}) of {d1*d2}")
