#!/usr/bin/env python3
"""T3b [N]: local-density constant of weighted Farey points.
mu = sum_{q<=Q} (w(q/Q)/q) sum*_{a mod q} delta_{a/q}.   Claim (h4/T3b_sharp_large_sieve.md):
  sup_x (mu * F_K)(x) = (C*_w + o(1)) Q,   C*_w := sup_{t>0} (1/t) sum_{1<=k<=t} (phi(k)/k) w(k/t),
for Q^{1+eps} <= K <= Q^{2-eps}.  Large-sieve ratio  K_w = C*_w / (S * int w),  S = prod_p (1-p^-2-p^-3).
Part 1: C*_w by direct evaluation.  Part 2: brute-force check of sup_x (mu*F_K)(x) for moderate Q."""
import numpy as np, sys
from math import gcd, pi
def phi_over_k(n):
    ph = np.arange(n+1, dtype=float)
    for p in range(2, n+1):
        if ph[p] == p:
            ph[p::p] *= (1-1/p)
    ph[1:] /= np.arange(1, n+1); return ph
S = 1.0
sieve = np.ones(2_000_001, bool); sieve[:2] = False
for p in range(2, 1415):
    if sieve[p]: sieve[p*p::p] = False
for p in np.nonzero(sieve)[0]:
    S *= 1 - 1.0/p**2 - 1.0/p**3
print("S = prod_p(1-p^-2-p^-3) =", S, "  (6/pi^2)/S =", 6/pi**2/S, "  1/S =", 1/S)
c = phi_over_k(20000)
weights = {"w=1": (lambda u: np.ones_like(u), 1.0), "w=1-u": (lambda u: 1-u, 0.5), "w=(1-u)^2": (lambda u: (1-u)**2, 1/3),
           "w=(1-u)^3": (lambda u: (1-u)**3, 0.25), "w=1-u^2": (lambda u: 1-u*u, 2/3), "w=cos^2(pi u/2)": (lambda u: np.cos(pi*u/2)**2, 0.5)}
for name,(w,I) in weights.items():
    best=(0,0)
    for t in np.concatenate([np.arange(1,60,0.001), np.arange(60,20000,0.37)]):
        k = np.arange(1, int(np.floor(t))+1)
        v = np.sum(c[k]*w(k/t))/t
        if v>best[0]: best=(v,t)
    print(f"{name:16s} C*_w = {best[0]:.6f} at t={best[1]:.3f};  mean (6/pi^2) int w = {6/pi**2*I:.6f};  C*/mean = {best[0]/(6/pi**2*I):.5f};  K_w = C*/(S int w) = {best[0]/(S*I):.5f}")
# Part 2: brute force
def brute(Q, lam, w, Q0frac=0.0, nx=4000):
    K = int(Q**lam)
    pts=[]; wts=[]
    for q in range(max(2,int(Q0frac*Q)+1), Q+1):
        ww = w(np.array([q/Q]))[0]/q
        if ww<=0: continue
        for a in range(1,q):
            if gcd(a,q)==1: pts.append(a/q); wts.append(ww)
    pts=np.array(pts); wts=np.array(wts)
    FK = lambda d: (np.sin(pi*K*d)**2/np.maximum(np.sin(pi*d)**2,1e-300))/K
    # scan x in a neighbourhood of 0 (the 1/q spoke) and at random x
    best=0; arg=None
    xs = np.concatenate([np.linspace(0.2/Q, 8/Q, nx), np.random.default_rng(0).random(300)])
    for x in xs:
        d = x-pts; v = np.sum(wts*np.where(np.abs(np.sin(pi*d))<1e-12, K, FK(d)))
        if v>best: best=v; arg=x
    return best/Q, arg*Q, K
if len(sys.argv)>1:
    for Q in (200, 400):
        for name in ("w=1","w=(1-u)^2"):
            w,I = weights[name]
            for lam in (1.3,1.6):
                b,a,K = brute(Q, lam, w)
                print(f"brute Q={Q} lam={lam} K={K} {name}: sup_x (mu*F_K)/Q = {b:.4f} at xQ={a:.3f}")
