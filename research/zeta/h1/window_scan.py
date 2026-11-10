#!/usr/bin/env python3
"""Scan cos(a s) windows: certificate 2-R(a) + delta(a), delta = max_U (x0-2/U)/3 * mu3(U) (triples of simple on-line zeros)."""
import numpy as np, importlib.util
from scipy.optimize import minimize
spec=importlib.util.spec_from_file_location('rr','refined_ranktrace.py'); rr=importlib.util.module_from_spec(spec); spec.loader.exec_module(rr)
def mu3(a,U):
    f=lambda g: rr.e3(abs(g[0]),abs(g[1]),a)+ (1e3*max(0,abs(g[0])+abs(g[1])-U)**2)
    best=1e9
    for g1 in np.arange(0.6,U,0.25):
        for g2 in np.arange(0.6,U-g1+1e-9,0.25):
            r=minimize(f,[g1,g2],method='Nelder-Mead',options={'xatol':1e-6,'fatol':1e-13})
            if min(abs(r.x))>0.3: best=min(best,rr.e3(abs(r.x[0]),abs(r.x[1]),a))
    return best
for a in [1.30,1.38,np.sqrt(2),1.45,1.50,1.60]:
    x0=2-rr.Rnum(a); out=[]
    for U in [3.6,4.0,4.4]:
        out.append(((x0-2/U)/3*mu3(a,U),U))
    d,U=max(out); print(f"a={a:.4f} 2-R={x0:.6f} delta={d:.2e} (U={U}) total={x0+d:.6f}")
