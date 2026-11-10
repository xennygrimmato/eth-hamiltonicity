# Chebyshev-Markov LP: spectral measure mu on R (mass 1 = d=N at theta=1), m1=1, m2=4/3, m3=2 (all
# diagonal, unconditional), m4 <= u.  Minimise mu((0,inf)) = n_+/N.  Then simple-on-line >= 2 n_+ - 1.
import numpy as np
from scipy.optimize import linprog
lam=np.concatenate([np.linspace(-6,0,1201),np.linspace(0.0025,8,3200)])
c=(lam>1e-12).astype(float)
def nplus(u,use_m3=True):
    Aeq=[np.ones_like(lam),lam,lam**2]; beq=[1,1,4/3]
    if use_m3: Aeq.append(lam**3); beq.append(2)
    r=linprog(c,A_ub=[lam**4],b_ub=[u],A_eq=np.array(Aeq),b_eq=beq,bounds=(0,None),method="highs")
    return r.fun if r.success else float('nan')
print("no m4 constraint (u=1e9): n_+ >=",round(nplus(1e9),4)," (Cauchy-Schwarz 3/4)")
for u in [13/4, 3.26, 49/15, 3.28, 3.30, 3.32, 10/3, 3.4, 3.5, 4.0, 5.0]:
    n=nplus(u); print(f"m4 <= {u:.4f}: n_+/N >= {n:.4f}   => simple on line >= {2*n-1:.4f}")
