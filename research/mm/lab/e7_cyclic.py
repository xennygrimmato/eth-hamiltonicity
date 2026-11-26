"""ideas-E7: M_n(F2) = End_F2(F_{2^n}) = F_{2^n}[x; Frob]/(x^n - 1).
A linear map is L(z) = sum_i a_i z^{2^i}; composition gives c_k = sum_{i+j=k mod n} a_i * b_j^{2^i}.
Check for n = 2..8: (1) coefficient->matrix map Phi is an F2-linear bijection (rank n^2 over F2),
(2) Phi(a*b) = Phi(a) Phi(b) on random inputs."""
import random
IRR = {2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011, 7: 0b10000011, 8: 0b100011011}

def gmul(x, y, n):
    r = 0
    while y:
        if y & 1: r ^= x
        y >>= 1; x <<= 1
        if x >> n & 1: x ^= IRR[n]
    return r

def frob(x, i, n):
    for _ in range(i): x = gmul(x, x, n)
    return x

def apply(a, z, n):
    r = 0
    for i, ai in enumerate(a): r ^= gmul(ai, frob(z, i, n), n)
    return r

def phi(a, n):  # matrix (columns = images of basis 2^col), as list of column ints
    return [apply(a, 1 << c, n) for c in range(n)]

def matmul_cols(P, Q, n):  # (P Q) columns: P applied to columns of Q
    out = []
    for q in Q:
        v = 0
        for r in range(n):
            if q >> r & 1: v ^= P[r]
        out.append(v)
    return out

def skew(a, b, n):
    c = [0] * n
    for i in range(n):
        for j in range(n):
            c[(i + j) % n] ^= gmul(a[i], frob(b[j], i, n), n)
    return c

def rank_F2(vecs):
    basis = {}
    r = 0
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in basis: v ^= basis[h]
            else: basis[h] = v; r += 1; break
    return r

for n in range(2, 9):
    # rank of Phi: images of the n^2 F2-basis vectors of the coefficient space
    imgs = []
    for i in range(n):
        for bit in range(n):
            a = [0] * n; a[i] = 1 << bit
            cols = phi(a, n)
            imgs.append(sum(col << (n * k) for k, col in enumerate(cols)))
    rk = rank_F2(imgs)
    ok = True
    for _ in range(50):
        a = [random.randrange(1 << n) for _ in range(n)]; b = [random.randrange(1 << n) for _ in range(n)]
        ok &= phi(skew(a, b, n), n) == matmul_cols(phi(a, n), phi(b, n), n)
    print(f"n={n}: rank(Phi)={rk} (n^2={n*n}), product identity on 50 random pairs: {ok}")
