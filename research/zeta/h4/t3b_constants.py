#!/usr/bin/env python3
"""T3b [N]: family constants from h5's window optimiser (h5/family_opt.py) with the sharp large-sieve ratios."""
import sys; sys.path.insert(0,'/home/user/eth-hamiltonicity/research/zeta/h5')
import numpy as np
from family_opt import optimise, Ft_LS
S=0.47914535993425167
for name,K in (("sharp cutoff, K=1/S",1/S),("smooth weight, K=(6/pi^2)/S",6/np.pi**2/S),("MV, K=1.5/S",1.5/S)):
    print("==",name,"K=%.4f"%K, flush=True)
    for lam in (1.25,1.5,1.75,1.99):
        R,Rf,u,psi=optimise(lam,Ft_LS(K),n=240)
        print("  lam=%.2f R=%.5f simple>=%.5f distinct>=%.5f"%(lam,R,2-R,(3-R)/2), flush=True)
