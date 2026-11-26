"""E2: word-RAM baselines over F2 with w=64-bit words.
Implements bit-packed naive, M4RM (Four Russians) and Strassen-Winograd over F2 with
M4RM base case, on numpy uint64 arrays; counts 64-bit word operations exactly
(XOR/AND of a word = 1 op, table lookup = 1 op), verifies against a reference product.
"""
import numpy as np, math, sys, time

W = 64
class Ctr:
    ops = 0

def pack(M):  # n x n 0/1 -> n x n/64 uint64
    n = M.shape[0]
    return np.packbits(M.astype(np.uint8), axis=1, bitorder='little').view(np.uint64).reshape(n, -1)

def unpack(P, n):
    return np.unpackbits(P.view(np.uint8), axis=1, bitorder='little')[:, :n]

def m4rm(A, Bp, n, k=None):
    """A: n x n 0/1 uint8 matrix (rows), Bp: packed B. returns packed C."""
    if k is None:
        k = max(1, int(math.log2(n)) - 1)
    nw = Bp.shape[1]
    C = np.zeros_like(Bp)
    for c0 in range(0, n, k):
        kk = min(k, n - c0)
        # Gray-code table: 2^kk rows each nw words, one XOR-row per entry
        T = np.zeros((1 << kk, nw), dtype=np.uint64)
        for s in range(1, 1 << kk):
            low = (s & -s).bit_length() - 1
            T[s] = T[s ^ (1 << low)] ^ Bp[c0 + low]
        Ctr.ops += ((1 << kk) - 1) * nw
        idx = np.zeros(n, dtype=np.int64)
        for t in range(kk):
            idx |= A[:, c0 + t].astype(np.int64) << t
        C ^= T[idx]
        Ctr.ops += n * nw + n  # XOR rows + index extraction (1 op per row)
    return C

def strassen(A, B, n, cut):
    """A, B: 0/1 uint8 n x n. Winograd variant: 7 mults, 15 adds. Returns 0/1 product."""
    if n <= cut:
        return unpack(m4rm(A, pack(B), n), n)
    h = n // 2
    a11, a12, a21, a22 = A[:h, :h], A[:h, h:], A[h:, :h], A[h:, h:]
    b11, b12, b21, b22 = B[:h, :h], B[:h, h:], B[h:, :h], B[h:, h:]
    add = lambda x, y: x ^ y
    words = h * max(1, h // W)
    s1 = add(a21, a22); s2 = add(s1, a11); s3 = add(a11, a21); s4 = add(a12, s2)
    t1 = add(b12, b11); t2 = add(b22, t1); t3 = add(b22, b12); t4 = add(t2, b21)
    m1 = strassen(a11, b11, h, cut); m2 = strassen(a12, b21, h, cut)
    m3 = strassen(s4, b22, h, cut); m4 = strassen(a22, t4, h, cut)
    m5 = strassen(s1, t1, h, cut); m6 = strassen(s2, t2, h, cut); m7 = strassen(s3, t3, h, cut)
    u2 = m1 ^ m6; u3 = u2 ^ m7; u4 = u2 ^ m5
    C = np.empty_like(A)
    C[:h, :h] = m1 ^ m2; C[:h, h:] = u4 ^ m3; C[h:, :h] = u3 ^ m4; C[h:, h:] = u3 ^ m5
    Ctr.ops += 15 * words
    return C

def run(n, mode, cut=256):
    rng = np.random.default_rng(n)
    A = rng.integers(0, 2, (n, n), dtype=np.uint8); B = rng.integers(0, 2, (n, n), dtype=np.uint8)
    Ctr.ops = 0; t = time.time()
    if mode == 'm4rm':
        C = unpack(m4rm(A, pack(B), n), n)
    elif mode == 'strassen':
        C = strassen(A, B, n, cut)
    dt = time.time() - t
    if n <= 1024:
        ref = (A.astype(np.int64) @ B.astype(np.int64)) & 1
        assert (ref == C).all()
    return Ctr.ops, dt

if __name__ == '__main__':
    print("n mode wordops ops/n^2 ops/(n^3/64) time")
    for mode in ['m4rm', 'strassen']:
        prev = None
        for e in range(6, 13):
            n = 1 << e
            ops, dt = run(n, mode)
            naive = n**3 / W
            slope = '' if prev is None else f"slope {math.log2(ops/prev):.3f}"
            print(f"{n} {mode} {ops} {ops/n**2:.1f} {ops/naive:.4f} {dt:.2f}s {slope}", flush=True)
            prev = ops
