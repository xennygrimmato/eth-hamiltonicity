#!/usr/bin/env python3
"""Scalar (commuting idealisation) cubic rank-trace certificate.
f(x)=c1 x+c2 x^2+c3 x^3.  Conditions:
 (S) f(p) <= t + c p        for all p>=0   (eigenvalues of the simple-on-line part; rank counts t, trace counts c)
 (M) f(q) <= 2c'            for all q>=0   (a positive eigenvalue of the rest = one object using >=2 zeros)
 (O) f(2+nu)+f(-nu) <= 2c'  for all nu>=0  (isolated off-line pair: eigenvalues 2+nu, -nu); omitted in RH mode
 (N) f(x) <= 0 for x<=0 on [-V,0] (only in 'neg' mode: arbitrary unpaired negative eigenvalues up to size V)
 normalisation t+c-c'=1, t,c,c'>=0.   Then  s1/N >= c1 + c2 m2 + c3 m3 - c'.
"""
import numpy as np, sys
from scipy.optimize import linprog
def moments(psi,u):
    h=u[1]-u[0]; I=h*psi.sum(); D=np.abs(u[:,None]-u[None,:])
    m2=(h*(psi**2).sum()+h*h*psi@D@psi)/I**2
    m3=(h*(psi**3).sum()+3*h*h*(psi**2)@D@psi)/I**3
    return m2,m3
def solve(m2,m3,mode='unc',cubic=True,P=40.0):
    # vars: c1,c2,c3,t,c'   (c = 1 - t + c')
    A=[];b=[]
    for p in np.concatenate([np.linspace(0,6,1201),np.linspace(6,P,400)]):
        A.append([p,p*p,p**3,-1+p,-p]); b.append(p)          # f(p) - t - (1-t+c')p <= 0  -> f - t + t p - c' p <= p
        A.append([p,p*p,p**3,0,-2]); b.append(0)               # (M)
    if mode in('unc','neg'):
        for nu in np.concatenate([np.linspace(0,6,601),np.linspace(6,P,300)]):
            A.append([2,(2+nu)**2+nu**2,(2+nu)**3-nu**3,0,-2]); b.append(0)
    if mode=='neg':
        for x in np.linspace(0,P,800): A.append([-x,x*x,-x**3,0,0]); b.append(0)
    A.append([0,0,0,1,-1]); b.append(1)                         # c = 1-t+c' >= 0
    bounds=[(None,None),(None,None),(None,0) if cubic else (0,0),(0,None),(0,None)]
    r=linprog([-1,-m2,-m3,0,1],A_ub=np.array(A),b_ub=np.array(b),bounds=bounds,method='highs')
    return -r.fun,r.x
if __name__=='__main__':
    n=2000;u=(np.arange(n)+.5)/n-.5
    for name,psi in [('flat',np.ones(n)),('MT cos(sqrt2 s)',np.cos(np.sqrt(2)*u)),('cos(1.6 s)',np.cos(1.6*u)),('cos(1.8 s)',np.cos(1.8*u)),('cos(2.2 s)',np.cos(2.2*u)),('cos(2.6 s)',np.cos(2.6*u))]:
        m2,m3=moments(psi,u)
        out=[solve(m2,m3,mode,cub) for mode,cub in [('unc',False),('rh',True),('unc',True),('neg',True)]]
        print(f"{name:16s} m2={m2:.5f} m3={m3:.5f} | quadratic {out[0][0]:.5f} | cubic RH {out[1][0]:.5f} | cubic +isolated pairs {out[2][0]:.5f} | cubic +free negatives {out[3][0]:.5f}")
        print("    cubic(unc) coeffs c1,c2,c3,t,c' =",np.round(out[2][1],4))
