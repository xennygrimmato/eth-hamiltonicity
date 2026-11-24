# Cross-ranks of the pieces of the exact three-cut splitting (4,1,1) on the cube, and the exponent it yields under tensor powering.
# Power exponent of a splitting with rank matrix M[k][j] = rank across cut k of piece j:
#   E = max over type distributions t of  H(t) + min_k sum_j t_j log2 M[k][j]     (trivial: log2 16 = 4)
import numpy as np, itertools
from split import *
from scipy.optimize import minimize
N = 2
T = wires(N, [(v, v ^ 7) for v in range(8) if v < (v ^ 7)], 8)
cut = lambda k: [v for v in range(8) if not (v >> k) & 1]
C = [cut(0), cut(1), cut(2)]
def als_terms(T, cuts, ranks, seed, iters=4000):
    rng = np.random.default_rng(seed); shape = T.shape; fac = []
    for S, p in zip(cuts, ranks):
        M, _ = flatten(T, S); fac.append([rng.normal(size=(M.shape[0], p)), rng.normal(size=(M.shape[1], p))])
    term = lambda k: unflatten(fac[k][0] @ fac[k][1].T, shape, cuts[k])
    terms = [term(k) for k in range(len(cuts))]
    for it in range(iters):
        for k in range(len(cuts)):
            Rk = T - sum(terms[j] for j in range(len(cuts)) if j != k); M, _ = flatten(Rk, cuts[k]); L, Rr = fac[k]
            L = M @ Rr @ np.linalg.pinv(Rr.T @ Rr); Rr = M.T @ L @ np.linalg.pinv(L.T @ L); fac[k] = [L, Rr]; terms[k] = term(k)
        if np.linalg.norm(T - sum(terms)) < 1e-12*np.linalg.norm(T): break
    return np.linalg.norm(T - sum(terms))/np.linalg.norm(T), terms
def rk(X, S): 
    s = np.linalg.svd(flatten(X, S)[0], compute_uv=False); return int((s > 1e-8*s[0]).sum())
def power_exponent(M):
    M = np.log2(np.array(M, float)); J = M.shape[1]; best = -1
    def f(z):
        t = np.exp(z - z.max()); t /= t.sum(); H = -(t*np.log2(t + 1e-300)).sum()
        return -(H + (M @ t).min())
    for s in range(40):
        r = minimize(f, np.random.default_rng(s).normal(size=J), method="Nelder-Mead", options={"xatol": 1e-9, "fatol": 1e-11, "maxiter": 20000})
        best = max(best, -r.fun)
    return best
print("crossing N=2, antisymmetriser: E =", round(power_exponent([[1, 4], [3, 1]]), 4), "(trivial 2)")
for name, cuts, ranks in [("two cuts (6,1)", C[:2], [6, 1]), ("three cuts (4,1,1)", C, [4, 1, 1])]:
    for seed in range(40):
        res, terms = als_terms(T, cuts, ranks, seed)
        if res < 1e-10: break
    M = [[rk(X, S) for X in terms] for S in C]
    print(name, "residual %.1e" % res, " rank matrix rows=cuts (bit0,bit1,bit2), cols=pieces:", M)
    used = M[:len(cuts)]
    print("   power exponent using its own cuts:", round(power_exponent(used), 4), "  using all three cuts:", round(power_exponent(M), 4), " (trivial 4)")
