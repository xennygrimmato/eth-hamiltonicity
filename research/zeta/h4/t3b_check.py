#!/usr/bin/env python3
"""T3b [N] checks.
(1) spoke coprimality density: for coprime (b,r) and k != 0, among q == -k*b^{-1} (mod r) the proportion with
    gcd((k+b*q)/r, q) = 1 is phi(k)/k  (independent of r).
(2) brute-force (mu*F_H)(x) for q in (Q0,Q], weight w(q/Q)/q, against the predicted density Q*Phi(t), t = x*Q (near 0)
    and t = |x-1/2|*2Q (near 1/2), Phi(t) = (1/t) sum_{t*Q0/Q < k <= t} (phi(k)/k) w(k/t)."""
import numpy as np
from math import gcd, pi
rng = np.random.default_rng(3)
def phi(n):
    r=n; p=2; m=n
    while p*p<=m:
        if m%p==0:
            while m%p==0: m//=p
            r-=r//p
        p+=1
    if m>1: r-=r//m
    return r
print("(1) spoke coprimality")
for (b,r,k) in ((1,1,6),(1,2,6),(1,6,6),(5,12,30),(3,10,7),(7,30,-210),(2,9,12)):
    X=400000; binv=pow(b,-1,r) if r>1 else 0
    q0=(-k*binv)%r if r>1 else 0
    qs=np.arange(q0 if q0>0 else r, X, r)
    cnt=sum(1 for q in qs if gcd((k+b*int(q))//r, int(q))==1)
    print(f"  b/r={b}/{r} k={k}: observed {cnt/len(qs):.5f}  phi(|k|)/|k| = {phi(abs(k))/abs(k):.5f}")
print("(2) brute force local density")
def setup(Q, Q0, w):
    pts=[]; wts=[]
    for q in range(Q0+1, Q+1):
        ww=w(q/Q)/q
        a=np.arange(1,q); a=a[np.gcd(a,q)==1]
        pts.append(a/q); wts.append(np.full(len(a),ww))
    return np.concatenate(pts), np.concatenate(wts)
def conv(x, pts, wts, H):
    d=x-pts; s=np.sin(pi*d)
    return np.sum(wts*np.where(np.abs(s)<1e-13, H, np.sin(pi*H*d)**2/np.maximum(s*s,1e-300)/H))
def Phi(t, w, ratio):
    k=np.arange(1,int(np.floor(t))+1); k=k[k>t*ratio]
    return sum(phi(int(j))/j*w(j/t) for j in k)/t if len(k) else 0.0
Q=3000; Q0=1500; H=40*Q   # regime Q << H << Q*Q0, H*t << Q0^2
for name,w in (("w=1",lambda u:1.0),("w=(1-u)^2",lambda u:(1-u)**2)):
    pts,wts=setup(Q,Q0,w)
    print(f"  {name}: Q={Q} Q0={Q0} H={H} points={len(pts)}  total mass/Q={wts.sum()/Q:.4f}")
    for t in (1.02,1.1,1.3,1.6,2.05,2.53,3.13,4.27,6.3,9.7):
        v0=conv(t/Q,pts,wts,H)/Q; v2=conv(0.5+t/(2*Q),pts,wts,H)/Q
        print(f"    t={t:4.2f}: near 0: {v0:.4f}   near 1/2: {v2:.4f}   predicted Q*Phi: {Phi(t,w,Q0/Q):.4f}")
    xs=rng.random(150); vals=[conv(x,pts,wts,H)/Q for x in xs]
    print(f"    random x: mean {np.mean(vals):.4f} max {np.max(vals):.4f}   (bulk prediction (6/pi^2)*int_{{Q0/Q}}^1 w = {6/pi**2*( (1-Q0/Q) if name=='w=1' else (1-Q0/Q)**3/3):.4f})")
