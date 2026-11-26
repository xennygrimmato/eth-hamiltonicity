"""Dense check of Lemma S for K=3, a=1: build T_3(2) as an explicit 16x16x16 array, build the local
maps M_u explicitly, contract, and compare with A_0 (x) A_1 (x) A_2 (grouped rows).  Also checks the
polynomial identity f_U(X) = f_T(Y), Y_u = M_u^t X_u, at a random point."""
import numpy as np, itertools
rng = np.random.default_rng(3)
K, D, qv = 3, 2, 3
oth = {u: [w for w in range(K) if w != u] for u in range(K)}
# row u of T: index (own_u[w0], own_u[w1], leaf_u[w0], leaf_u[w1]) each in [D]; dimension D^4 = 16
def enc(own, leaf): 
    v = 0
    for x in list(own) + list(leaf): v = v * D + x
    return v
R = D ** (2 * (K - 1))
T = np.zeros((R,) * K)
# one string of 2 bits per edge = (own-part of smaller endpoint..): edge {u,w} carries (s_uw [star u], s_wu [star w])
edges = [(u, w) for u in range(K) for w in range(u + 1, K)]
for lab in itertools.product(range(D), repeat=2 * len(edges)):
    s = {}
    for e, (u, w) in enumerate(edges):
        s[(u, w)] = lab[2 * e]      # star at u, leg to w
        s[(w, u)] = lab[2 * e + 1]  # star at w, leg to u
    idx = []
    for u in range(K):
        own = [s[(u, w)] for w in oth[u]]
        leaf = [s[(w, u)] for w in oth[u]]
        idx.append(enc(own, leaf))
    T[tuple(idx)] += 1
assert T.sum() == D ** (2 * len(edges))
A = []
for v in range(K):
    shape = [D] * K; shape[v] = qv
    A.append(rng.standard_normal(shape))
# U row u index: (i_u^{(0)}, i_u^{(1)}, i_u^{(2)}), side qv for own, D for others
sides = [[(qv if v == u else D) for v in range(K)] for u in range(K)]
def encU(u, tup):
    v = 0
    for s_, x in zip(sides[u], tup): v = v * s_ + x
    return v
RU = [int(np.prod(sides[u])) for u in range(K)]
M = []
for u in range(K):
    Mu = np.zeros((RU[u], R))
    for own in itertools.product(range(D), repeat=K - 1):
        for leaf in itertools.product(range(D), repeat=K - 1):
            for i in range(qv):
                ind = [None] * K; ind[u] = i
                for w, x in zip(oth[u], own): ind[w] = x
                tup = [None] * K; tup[u] = i
                for w, x in zip(oth[u], leaf): tup[w] = x
                Mu[encU(u, tup), enc(own, leaf)] += A[u][tuple(ind)]
    M.append(Mu)
MT = np.einsum('ia,jb,kc,abc->ijk', M[0], M[1], M[2], T)
U = np.zeros(RU)
for idx in itertools.product(*[itertools.product(*[range(s_) for s_ in sides[u]]) for u in range(K)]):
    p = 1.0
    for v in range(K):
        p *= A[v][tuple(idx[u][v] for u in range(K))]
    U[tuple(encU(u, idx[u]) for u in range(K))] = p
print("max |U - (M0 x M1 x M2) T_3(2)| =", np.abs(U - MT).max(), " (U has shape", U.shape, ")")
X = [rng.standard_normal(RU[u]) for u in range(K)]
fU = np.einsum('ijk,i,j,k->', U, *X)
Y = [M[u].T @ X[u] for u in range(K)]
fT = np.einsum('abc,a,b,c->', T, *Y)
print("f_U(X) =", fU, "  f_T(M^t X) =", fT)
