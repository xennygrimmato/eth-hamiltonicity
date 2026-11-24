"""Search for violations of the rank inequalities over small prime fields.

(SCSH)  rank(M^Gamma) <= Sr(M) * rank(M)   (Song-Chen-Sun-Hu Thm 9, stated over C)
(CHLW1) rA <= rAB * rAC for 4-party tensors (field-free proof, checked anyway)
M in M_{m1,n1} (x) M_{m2,n2}; Sr = operator-Schmidt rank (rank of realignment); Gamma = transpose of each block.
"""
import itertools, random, sys
import numpy as np

def rank_mod(M, p):
    M = np.array(M, dtype=np.int64) % p
    M = M.copy(); r = 0; rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c] % p:
                piv = i; break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == rows:
            break
    return r

def check_tensor(T, p):
    """T has shape (m1, m2, n1, n2): M[(i1,i2),(j1,j2)] = T[i1,i2,j1,j2]; R acts on (i1,j1), S on (i2,j2)."""
    m1, m2, n1, n2 = T.shape
    M = T.reshape(m1 * m2, n1 * n2)
    MG = T.transpose(0, 3, 2, 1).reshape(m1 * n2, n1 * m2)  # partial transpose on second factor
    Rl = T.transpose(0, 2, 1, 3).reshape(m1 * n1, m2 * n2)  # realignment
    return rank_mod(M, p), rank_mod(MG, p), rank_mod(Rl, p)

random.seed(1)
viol = 0; tested = 0
for p in [2, 3]:
    # exhaustive: rank-one M = u v^T, block sizes 2x2 (x) 2x2 and 3x3 (x) 3x3 (random for the latter)
    for (m1, m2, n1, n2) in [(2, 2, 2, 2), (2, 3, 2, 3), (3, 3, 3, 3)]:
        U = list(itertools.product(range(p), repeat=m1 * m2))
        V = list(itertools.product(range(p), repeat=n1 * n2))
        pairs = [(u, v) for u in U for v in V] if len(U) * len(V) <= 70000 else \
            [(random.choice(U), random.choice(V)) for _ in range(30000)]
        for u, v in pairs:
            T = np.einsum('ab,cd->abcd', np.array(u).reshape(m1, m2), np.array(v).reshape(n1, n2)) % p
            r, rg, sr = check_tensor(T, p)
            tested += 1
            if rg > sr * r:
                viol += 1; print('VIOLATION rank1', p, (m1, m2, n1, n2), u, v, r, rg, sr)
    # random low-rank M: M = sum of k rank-one terms with structured sparsity
    for trial in range(20000):
        m1, m2, n1, n2 = random.choice([(2, 2, 2, 2), (3, 2, 3, 2), (3, 3, 3, 3), (2, 3, 3, 2), (4, 2, 4, 2)])
        k = random.randint(1, 3)
        T = np.zeros((m1, m2, n1, n2), dtype=np.int64)
        for _ in range(k):
            u = np.random.randint(0, p, (m1, m2)) * (np.random.rand(m1, m2) < 0.5)
            v = np.random.randint(0, p, (n1, n2)) * (np.random.rand(n1, n2) < 0.5)
            T += np.einsum('ab,cd->abcd', u, v)
        T %= p
        r, rg, sr = check_tensor(T, p)
        tested += 1
        if rg > sr * r:
            viol += 1; print('VIOLATION', p, T.shape, r, rg, sr, T.flatten().tolist())
    # random small Schmidt rank: M = sum_{k<=K} R_k (x) S_k
    for trial in range(20000):
        m1, m2, n1, n2 = random.choice([(2, 2, 2, 2), (3, 3, 3, 3), (2, 3, 2, 3), (4, 4, 2, 2)])
        K = random.randint(1, 3)
        T = np.zeros((m1, m2, n1, n2), dtype=np.int64)
        for _ in range(K):
            R = np.random.randint(0, p, (m1, n1)) * (np.random.rand(m1, n1) < 0.4)
            S = np.random.randint(0, p, (m2, n2)) * (np.random.rand(m2, n2) < 0.4)
            T += np.einsum('ac,bd->abcd', R, S)
        T %= p
        r, rg, sr = check_tensor(T, p)
        tested += 1
        if rg > sr * r:
            viol += 1; print('VIOLATION', p, T.shape, r, rg, sr, T.flatten().tolist())
print('tested', tested, 'violations', viol)
