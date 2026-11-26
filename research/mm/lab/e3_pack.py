"""E3: Kronecker / polynomial packing of matrix product.
(a) Minimal 1-D monomial packing: exponents alpha(i,k) for A, beta(k,j) for B in [0,L),
    such that coefficient of z^{gamma(i,j)} in A(z)B(z) equals C_ij exactly, i.e.
    alpha(i,k)+beta(k,j) = gamma(i,j) for all k, and no other pair alpha(i,k)+beta(k',j')
    hits any gamma value. Output length 2L-1 compared with n^3. (z3 search.)
(b) Scaling experiment: big-int Kronecker product computing all n^2 inner products mod 2.
"""
import sys, time, math, random
import z3

def min_pack(n, Lmax=200):
    for L in range(1, Lmax):
        s = z3.Solver()
        al = {(i, k): z3.Int(f"a{i}_{k}") for i in range(n) for k in range(n)}
        be = {(k, j): z3.Int(f"b{k}_{j}") for k in range(n) for j in range(n)}
        for v in list(al.values()) + list(be.values()):
            s.add(v >= 0, v < L)
        s.add(al[(0, 0)] == 0)
        ga = {}
        for i in range(n):
            for j in range(n):
                ga[(i, j)] = al[(i, 0)] + be[(0, j)]
                for k in range(1, n):
                    s.add(al[(i, k)] + be[(k, j)] == ga[(i, j)])
        for i in range(n):
            for k in range(n):
                for k2 in range(n):
                    for j in range(n):
                        if k == k2:
                            continue
                        for (i2, j2), g in ga.items():
                            s.add(al[(i, k)] + be[(k2, j)] != g)
        # distinct gammas
        gl = list(ga.values())
        s.add(z3.Distinct(gl))
        if s.check() == z3.sat:
            m = s.model()
            return L, {key: m[v].as_long() for key, v in al.items()}, {key: m[v].as_long() for key, v in be.items()}
    return None

def kron_matmul_mod2(A, B):
    """A,B n x n 0/1 lists. One big-int product gives all C_ij (over Z), then mod 2.
    Slot width w bits >= log2(n)+1. A(z)=sum a_ik z^{i*n*(2n-1)... } standard stride packing."""
    n = len(A)
    w = n.bit_length() + 1
    s1 = 2 * n - 1           # k offsets of A row (k) and B col (n-1-k) sum to n-1 +- garbage in [0,2n-2]
    s2 = n * s1              # i stride for A, j stride for B
    X = 0
    for i in range(n):
        for k in range(n):
            if A[i][k]:
                X |= 1 << (w * (i * s1 + k))
    Y = 0
    for j in range(n):
        for k in range(n):
            if B[k][j]:
                Y |= 1 << (w * (j * s2 + (n - 1 - k)))
    Z = X * Y
    mask = (1 << w) - 1
    C = [[(Z >> (w * (i * s1 + j * s2 + n - 1))) & 1 for j in range(n)] for i in range(n)]
    return C, X.bit_length(), Y.bit_length()

if __name__ == '__main__':
    if sys.argv[1] == 'pack':
        for n in [2, 3]:
            t = time.time()
            r = min_pack(n)
            L = r[0]
            print(f"n={n}: min exponent range L={L}, product length 2L-1={2*L-1}, n^3={n**3}, {time.time()-t:.1f}s; alpha={r[1]} beta={r[2]}", flush=True)
    else:
        print("n bitsX bitsY time(s) n^3*logn-normalised")
        for e in range(5, 11):
            n = 1 << e
            rnd = random.Random(e)
            A = [[rnd.randint(0, 1) for _ in range(n)] for _ in range(n)]
            B = [[rnd.randint(0, 1) for _ in range(n)] for _ in range(n)]
            t = time.time(); C, bx, by = kron_matmul_mod2(A, B); dt = time.time() - t
            if n <= 128:
                for i in range(n):
                    for j in range(n):
                        assert C[i][j] == sum(A[i][k] & B[k][j] for k in range(n)) & 1
            print(n, bx, by, f"{dt:.3f}", f"{bx/(n**2*math.log2(n)):.2f} {by/(n**3*math.log2(n)):.2f}", flush=True)
