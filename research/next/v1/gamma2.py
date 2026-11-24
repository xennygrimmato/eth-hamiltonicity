# gamma_2 norm of the 2x2 disjointness matrix R1 = [[1,1],[1,0]].
# Dual form: gamma_2(A) = max over unit vectors u,v of trace-norm(A o (u v^T)).
import numpy as np
A = np.array([[1.,1.],[1.,0.]])
best = 0
for s in np.linspace(0, np.pi/2, 2001):
    u = np.array([np.cos(s), np.sin(s)])
    for t in np.linspace(0, np.pi/2, 2001):
        v = np.array([np.cos(t), np.sin(t)])
        val = np.linalg.svd(A*np.outer(u,v), compute_uv=False).sum()
        if val > best: best, arg = val, (s,t)
print("dual lower bound  gamma2(R1) >=", best, " 2/sqrt3 =", 2/np.sqrt(3))
print("log2(2/sqrt3) =", np.log2(2/np.sqrt(3)), "  log2(1.16) =", np.log2(1.16), " log2(1.25)=", np.log2(1.25))
