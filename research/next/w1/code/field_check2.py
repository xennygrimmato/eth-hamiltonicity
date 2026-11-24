"""Random 4-party tensors over GF(2), GF(3): test CHLW2 (rA^2 <= rAB rAC rBC) and L2 (rBC <= rAB rAC) and L1."""
import numpy as np, random, itertools
from field_check import rank_mod
random.seed(7); np.random.seed(7)
def flat(T, parts):
    ax = list(parts) + [i for i in range(4) if i not in parts]
    U = T.transpose(ax)
    m = int(np.prod([T.shape[i] for i in parts]))
    return U.reshape(m, -1)
viol = 0; tested = 0
for p in [2, 3]:
    for trial in range(60000):
        dims = [random.choice([2, 2, 3, 3, 4]) for _ in range(4)]
        k = random.randint(1, 6)
        T = np.zeros(dims, dtype=np.int64)
        for _ in range(k):  # sum of k random product-ish terms with structured sparsity
            vs = [np.random.randint(0, p, d) * (np.random.rand(d) < 0.6) for d in dims]
            if random.random() < 0.5:  # sometimes a matrix on two parties
                i, j = random.sample(range(4), 2)
                M = np.random.randint(0, p, (dims[i], dims[j])) * (np.random.rand(dims[i], dims[j]) < 0.5)
                rest = [x for x in range(4) if x not in (i, j)]
                term = np.einsum('ab,c,d->abcd', M, vs[rest[0]], vs[rest[1]])
                T += term.transpose(np.argsort([i, j] + rest))
            else:
                T += np.einsum('a,b,c,d->abcd', *vs)
        T %= p
        if not T.any():
            continue
        r = {}
        for S in [(0,), (1,), (2,), (3,), (0, 1), (0, 2), (0, 3)]:
            r[S] = rank_mod(flat(T, S), p)
        rBC = r[(0, 3)]; rAB = r[(0, 1)]; rAC = r[(0, 2)]
        tested += 1
        for perm in itertools.permutations(range(4)):
            a, b, c, d = perm
            def R(*s):
                s = tuple(sorted(s))
                if s in r: return r[s]
                comp = tuple(sorted(set(range(4)) - set(s)))
                return r[comp]
            if R(a) ** 2 > R(a, b) * R(a, c) * R(b, c): viol += 1; print('CHLW2 viol', p, dims, perm)
            if R(b, c) > R(a, b) * R(a, c): viol += 1; print('L2 viol', p, dims, perm)
            if R(a) > R(a, b) * R(a, c): viol += 1; print('L1 viol', p, dims, perm)
print('tested', tested, 'violations', viol)
