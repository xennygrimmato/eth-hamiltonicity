"""Splitting numbers.  T is a tensor on m parties.  For a list of cuts (each a subset S of parties),
ask whether T = sum_k X_k with rank of X_k across cut k at most p_k.  Alternating least squares with restarts.
The engine's merge-by-merge accounting needs exactly this: every term cheap across its own cut."""
import numpy as np, itertools, sys, time

def flatten(T, S):
    m = T.ndim; S = list(S); Sc = [i for i in range(m) if i not in S]
    dS = int(np.prod([T.shape[i] for i in S])); dC = int(np.prod([T.shape[i] for i in Sc]))
    return np.transpose(T, S + Sc).reshape(dS, dC), (S, Sc)

def unflatten(M, shape, S):
    m = len(shape); S = list(S); Sc = [i for i in range(m) if i not in S]
    perm = S + Sc; A = M.reshape([shape[i] for i in perm])
    return np.transpose(A, np.argsort(perm))

def als(T, cuts, ranks, iters=3000, seed=0, tol=1e-11, verbose=False):
    rng = np.random.default_rng(seed); shape = T.shape
    fac = []
    for S, p in zip(cuts, ranks):
        M, _ = flatten(T, S)
        fac.append([rng.normal(size=(M.shape[0], p)), rng.normal(size=(M.shape[1], p))] if p > 0 else None)
    def term(k):
        if fac[k] is None: return np.zeros(shape)
        return unflatten(fac[k][0] @ fac[k][1].T, shape, cuts[k])
    terms = [term(k) for k in range(len(cuts))]
    nT = np.linalg.norm(T); res = None
    for it in range(iters):
        for k in range(len(cuts)):
            if fac[k] is None: continue
            Rk = T - sum(terms[j] for j in range(len(cuts)) if j != k)
            M, _ = flatten(Rk, cuts[k]); L, Rr = fac[k]
            L = M @ Rr @ np.linalg.pinv(Rr.T @ Rr + 1e-12*np.eye(Rr.shape[1]))
            Rr = M.T @ L @ np.linalg.pinv(L.T @ L + 1e-12*np.eye(L.shape[1]))
            fac[k] = [L, Rr]; terms[k] = term(k)
        res = np.linalg.norm(T - sum(terms))/nT
        if res < tol: break
    return res, it

def best(T, cuts, ranks, restarts=20, iters=3000):
    b = 1
    for s in range(restarts):
        r, it = als(T, cuts, ranks, iters=iters, seed=s)
        b = min(b, r)
        if b < 1e-9: return b
    return b

def wires(N, pairs, m):
    """tensor on m parties of dimension N: product of identity wires on the given pairs (perfect matching)."""
    T = np.zeros([N]*m)
    for vals in itertools.product(range(N), repeat=len(pairs)):
        idx = [0]*m
        for (i, j), v in zip(pairs, vals): idx[i] = v; idx[j] = v
        T[tuple(idx)] = 1
    return T
