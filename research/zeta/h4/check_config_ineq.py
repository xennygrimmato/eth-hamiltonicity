#!/usr/bin/env python3
"""T2 sanity check [N].  Configuration form of the A-F zero-side inequality
    I(f):  sum_{z,z' in Z} f(z-z')  >=  4|Z| - 3 s1 - 4 s2 - 4 p
for finite multisets Z of normalised ordinates, symmetric under complex conjugation
(real z = on-line zero, pair {z, conj z} = off-line pair), f(0)=1.
 (a) f = k^2, k = psi^ with psi >= 0 on [-1/2,1/2]  (flat, Montgomery-Taylor): never violated.
 (b) f = |k|^2-type with f^ <= 0 on 1<|alpha|<=lam (CGdL-type sign condition): violated by ONE
     off-line pair, because f(iy) -> -infinity.
Numerical quadrature only; no rigorous enclosures."""
import numpy as np
rng = np.random.default_rng(1)
t = np.linspace(-0.5, 0.5, 4001)
def trap(y): return np.sum((y[1:]+y[:-1])*0.5*(t[1]-t[0]))
def kernel(psi):
    w = psi(t); w = w/trap(w)
    return lambda z: trap(w*np.exp(2j*np.pi*z*t))      # k(z), entire, k(0)=1
k_flat = kernel(lambda s: np.ones_like(s))
k_MT   = kernel(lambda s: np.cos(np.sqrt(2)*s))
def lhs(f, Z):
    return sum(f(a-b) for a in Z for b in Z).real
def rand_config():
    Z=[]; s1=s2=p=0; x=0.0
    for _ in range(rng.integers(3,9)):
        x += rng.exponential(0.7)
        typ = rng.integers(0,3)
        if typ==0: Z.append(x); s1+=1
        elif typ==1:
            m=rng.integers(2,4); Z += [x]*m; s2+=1
        else:
            eta = rng.exponential(0.3)+1e-3; m=rng.integers(1,3)
            Z += [x+1j*eta]*m + [x-1j*eta]*m; p+=1      # pair of multiplicity m counts as one pair
    return Z,s1,s2,p
for name,k in (("flat",k_flat),("MT",k_MT)):
    f = lambda z,k=k: k(z)**2
    worst = 1e9
    for _ in range(400):
        Z,s1,s2,p = rand_config()
        worst = min(worst, lhs(f,Z) - (4*len(Z)-3*s1-4*s2-4*p))
    print(f"(a) {name:4s}: min over 400 random configs of LHS-RHS = {worst:.6f}  (>=0 expected)")
# (b) genuine CGdL-type test function: f^(alpha) = c (1-alpha^2) exp(-pi alpha^2)  (<= 0 for |alpha|>1),
#     f(x) = (1 + x^2/(1-1/(2 pi))) exp(-pi x^2) >= 0 on R, f(0)=1.   Then f(iy) = (1 - y^2/(1-1/(2pi))) e^{pi y^2} -> -inf.
c0 = 1-1/(2*np.pi)
fz = lambda z: (1 + z*z/c0)*np.exp(-np.pi*z*z)
print("(b) min of f on the real axis (grid):", min(fz(x).real for x in np.linspace(-6,6,1201)))
for eta in (0.1,0.3,0.5,0.8,1.2):
    Z=[1j*eta,-1j*eta]
    print(f"(b) single pair depth eta={eta}: f(2i eta)={fz(2j*eta).real:12.4f}  LHS-RHS={lhs(fz,Z)-(8-4):12.4f}")
