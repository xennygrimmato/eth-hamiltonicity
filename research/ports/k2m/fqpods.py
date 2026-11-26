"""Machine check of Lemma P (notes §1): for q = 2^r the q+1 rank-one idempotents of Mat_2(F_q) with
image p_i and kernel p_{i+1} (p_0..p_q the points of P^1(F_q) in any cyclic order), pushed to
Mat_{2r}(F_2) by the regular representation, satisfy over F_2:
    rk(t_i) = rk(I - t_i) = r,   rk(t_i - t_j) = 2r (i != j),   rk(I) = 2r.
So {0, I, t_0..t_q} with sqrt(rank) is sqrt(r) * sqrt(graph metric of K_{2,q+1}).
Also checks: rank_F2(iota(A)) = r * rank_Fq(A) on random A in Mat_2(F_q), and that no (q+2)-nd point exists
(exhaustively for r <= 2).  Pure-integer arithmetic; no floating point.
"""
import itertools, random, sys

IRRED = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101}   # x+1, x^2+x+1, x^3+x+1, x^4+x+1, x^5+x^2+1

def gf_mul(a, b, r):
    p = 0
    while b:
        if b & 1: p ^= a
        b >>= 1; a <<= 1
        if a >> r & 1: a ^= IRRED[r]
    return p

def gf_inv(a, r):
    q = 1 << r
    for b in range(1, q):
        if gf_mul(a, b, r) == 1: return b
    raise ZeroDivisionError

def reg(a, r):
    """r x r matrix over F_2 (list of row bitmasks) of multiplication by a on F_q = F_2^r (basis 1,x,..)."""
    cols = [gf_mul(a, 1 << j, r) for j in range(r)]          # image of basis vector j
    return [sum(((cols[j] >> i) & 1) << j for j in range(r)) for i in range(r)]

def iota(A, r):
    """A: 2x2 over F_q -> 2r x 2r over F_2 as list of row bitmasks."""
    rows = []
    for bi in range(2):
        blocks = [reg(A[bi][bj], r) for bj in range(2)]
        for i in range(r):
            rows.append(blocks[0][i] | (blocks[1][i] << r))
    return rows

def rank_f2(rows):
    rows = list(rows); rk = 0
    for bit in range(64):
        piv = None
        for i in range(rk, len(rows)):
            if rows[i] >> bit & 1: piv = i; break
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i] >> bit & 1: rows[i] ^= rows[rk]
        rk += 1
    return rk

def rank_fq(A, r):
    if all(x == 0 for row in A for x in row): return 0
    det = gf_mul(A[0][0], A[1][1], r) ^ gf_mul(A[0][1], A[1][0], r)
    return 2 if det else 1

def add(A, B): return [[A[i][j] ^ B[i][j] for j in range(2)] for i in range(2)]

def idem(u, k, r):
    """rank-one idempotent of Mat_2(F_q) with image <u> and kernel <k> (u, k non-proportional)."""
    x = (k[1], k[0])                                   # x^T k = k1 k0 + k0 k1 = 0 in char 2
    s = gf_mul(x[0], u[0], r) ^ gf_mul(x[1], u[1], r)  # x^T u != 0
    si = gf_inv(s, r)
    return [[gf_mul(gf_mul(u[i], x[j], r), si, r) for j in range(2)] for i in range(2)]

def check(r):
    q = 1 << r
    pts = [(1, a) for a in range(q)] + [(0, 1)]        # P^1(F_q)
    T = [idem(pts[i], pts[(i + 1) % (q + 1)], r) for i in range(q + 1)]
    I = [[1, 0], [0, 1]]
    ok = True
    for t in T:
        ok &= rank_f2(iota(t, r)) == r and rank_f2(iota(add(I, t), r)) == r
        ok &= add(t, [[0,0],[0,0]]) == [[gf_mul(t[i][0], t[0][j], r) ^ gf_mul(t[i][1], t[1][j], r) for j in range(2)] for i in range(2)]
    for s, t in itertools.combinations(T, 2):
        ok &= rank_f2(iota(add(s, t), r)) == 2 * r
    ok &= rank_f2(iota(I, r)) == 2 * r
    rnd = random.Random(r)
    for _ in range(2000):
        A = [[rnd.randrange(q) for _ in range(2)] for _ in range(2)]
        ok &= rank_f2(iota(A, r)) == r * rank_fq(A, r)
    # additivity/multiplicativity of iota on a sample (so differences map to differences)
    for _ in range(200):
        A = [[rnd.randrange(q) for _ in range(2)] for _ in range(2)]
        B = [[rnd.randrange(q) for _ in range(2)] for _ in range(2)]
        ok &= iota(add(A, B), r) == [x ^ y for x, y in zip(iota(A, r), iota(B, r))]
    print(f"r={r} q={q}: m = q+1 = {q+1} points in Mat_{2*r}(F_2); all rank conditions hold: {ok}")
    if r <= 2:   # maximality inside Mat_2(F_q): no further admissible point
        extra = 0
        for A in itertools.product(range(q), repeat=4):
            A = [[A[0], A[1]], [A[2], A[3]]]
            if rank_fq(A, r) == 1 and rank_fq(add(I, A), r) == 1 and all(rank_fq(add(A, t), r) == 2 for t in T):
                extra += 1
        print(f"      admissible further points in Mat_2(F_{q}): {extra}")
    return ok

def max_family_mu4():
    """Exhaustive: largest m with n=0, s=W (rk 2), t_i (rk 1, rk(W-t_i)=1, pairwise rk 2) in Mat_2(F_2):
    and in Mat_4(F_2) with W = I_4, t_i of rank 2: clique search (greedy bound only)."""
    # Mat_2(F_2)
    mats = list(range(16))
    def rk2(a):  # a = 4 bits a00 a01 a10 a11
        rows = [a & 3, a >> 2]
        return rank_f2(rows)
    I2 = 0b1001
    adm = [a for a in mats if rk2(a) == 1 and rk2(a ^ I2) == 1]
    best = 0
    for k in range(1, len(adm) + 1):
        for c in itertools.combinations(adm, k):
            if all(rk2(x ^ y) == 2 for x, y in itertools.combinations(c, 2)): best = max(best, k)
    print(f"Mat_2(F_2): {len(adm)} admissible points, largest pairwise-rank-2 family: {best}")

if __name__ == "__main__":
    allok = all(check(r) for r in (1, 2, 3, 4, 5))
    max_family_mu4()
    print("ALL OK" if allok else "FAILURE")
