#!/usr/bin/env python3
"""Abstract linear-algebra test of the cubic lemma  tr[G(G-1)^2] >= tr Q'  (equivalently tr P1 >= 2 tr G^2 - tr G^3),
G = P1 + Q',  P1 = sum of s rank-one u u^T (|u|=1),  Q' = sum_j m_j w_j w_j^T (m_j=2, |w|=1) + sum_k 2(a_k a_k^T - b_k b_k^T),
a_k perp b_k, |a_k|^2-|b_k|^2 = 1  (the only relations Poisson-Gabor gives for an off-line pair by itself).
Adversarial minimisation of  tr g(G) - (2*#doubles + 2*#pairs)."""
import numpy as np, sys
from scipy.optimize import minimize
rng=np.random.default_rng(0)
def build(z,d,s,nd,npair):
    i=0; G=np.zeros((d,d))
    for _ in range(s):
        u=z[i:i+d]; i+=d; u=u/np.linalg.norm(u); G+=np.outer(u,u)
    for _ in range(nd):
        u=z[i:i+d]; i+=d; u=u/np.linalg.norm(u); G+=2*np.outer(u,u)
    for _ in range(npair):
        a=z[i:i+d]; i+=d; b=z[i:i+d]; i+=d; beta=min(z[i]**2,30.0); i+=1
        a=a/np.linalg.norm(a); b=b-(b@a)*a; b=b/np.linalg.norm(b)
        G+=2*((1+beta)*np.outer(a,a)-beta*np.outer(b,b))
    return G
def F(z,d,s,nd,npair):
    G=build(z,d,s,nd,npair); G1=G-np.eye(d)
    return np.trace(G@G1@G1)-2*nd-2*npair
worst=1e9
for trial in range(int(sys.argv[1]) if len(sys.argv)>1 else 300):
    d=rng.integers(3,8); s=rng.integers(0,5); nd=rng.integers(0,3); npair=rng.integers(1,3)
    nz=d*(s+nd)+npair*(2*d+1)
    r=minimize(F,rng.normal(size=nz),args=(d,s,nd,npair),method='L-BFGS-B',options={'maxiter':150})
    if r.fun<worst:
        worst=r.fun; print(f"trial {trial} d={d} s={s} doubles={nd} pairs={npair}: min = {r.fun:.5f}",flush=True)
print("worst",worst)
