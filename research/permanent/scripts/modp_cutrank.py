"""modp_cutrank.py -- cut ranks over F_p (and over Q, via a large prime) of the char-p
representations of per; the engine's c_ab >= lg(rank) (perm-mod-p.md section 4).
(1) Ryser row-group factor F_a(x) = prod_{i in R_a} (w_i + r_i(x)) mod p, cut (x_{C_b} ; x_rest)
(2) Ryser half split M[x_L, x_R] = prod_i (w_i + r_i) mod p (the Bax-Franklin / BW object)
(3) the 2-local Fourier form: [zeta^{t^T A_ab s}] for t in Z_p^{|R_a|}, s in {0,1}^{|C_b|}, over F_q
"""
import random, itertools, math
random.seed(7)

def rank_mod(M, p):
    M = [[x % p for x in row] for row in M]
    r = 0; rows = len(M); cols = len(M[0]) if rows else 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c]: piv = i; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [x * inv % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r

BIGQ = (1 << 61) - 1
def rand01(n): return [[random.randint(0, 1) for _ in range(n)] for _ in range(n)]
bits = lambda m, L: [(m >> t) & 1 for t in range(L)]

n = 8
print("(1) Ryser row-group factor, n=8, random dense 0/1 A, random shift w; rank over F_p and over Q; generic prediction 2^min(|R_a|,q)")
print(" p |R_a| q : ranks F_p (5 samples)        ranks Q          pred")
for p in (3, 5, 7):
    for pa in (1, 2, 3, 4):
        for q in (2, 3, 4):
            rp, rq = [], []
            for _ in range(5):
                A = rand01(n); w = [random.randrange(p) for _ in range(n)]
                Ra = list(range(pa)); Cb = list(range(q)); rest = list(range(q, n))
                def F(x):
                    return math.prod(w[i] + sum(A[i][j] * x[j] for j in range(n)) for i in Ra)
                M = []
                for mb in range(1 << q):
                    row = []
                    for mr in range(1 << (n - q)):
                        x = [0] * n
                        for t, j in enumerate(Cb): x[j] = (mb >> t) & 1
                        for t, j in enumerate(rest): x[j] = (mr >> t) & 1
                        row.append(F(x))
                    M.append(row)
                rp.append(rank_mod(M, p)); rq.append(rank_mod(M, BIGQ))
            print(f" {p}   {pa}   {q} : {rp}   {rq}   {2**min(pa,q)}")

print("\n(2) half split M[x_L,x_R] = prod_i (w_i + r_i) mod p, n=8 (16 x 16); rank over F_p")
for p in (2, 3, 5, 7, 11):
    rs = []
    for _ in range(6):
        A = rand01(n); w = [random.randrange(p) for _ in range(n)] if p > 2 else [0]*n
        M = [[math.prod(w[i] + sum(A[i][j] for j in range(4) if mL >> j & 1) + sum(A[i][4 + j] for j in range(4) if mR >> j & 1) for i in range(n))
              for mR in range(16)] for mL in range(16)]
        rs.append(rank_mod(M, p))
    print(f" p={p:2d}: {rs}  (full = 16)")

print("\n(3) 2-local Fourier form [zeta^(t^T A_ab s)], t in Z_p^{|R_a|}, s in {0,1}^q, over F_q (q = 1 mod p)")
def is_prime(m):
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return m > 1
for p in (3, 5):
    qq = 1 + p * 1000
    while not is_prime(qq): qq += p
    g = 2
    while pow(g, (qq - 1) // p, qq) == 1: g += 1
    z = pow(g, (qq - 1) // p, qq)
    for pa, q in ((2, 4), (3, 4), (4, 4), (4, 6)):
        rs = []
        for _ in range(4):
            Aab = [[random.randint(0, 1) for _ in range(q)] for _ in range(pa)]
            M = []
            for t in itertools.product(range(p), repeat=pa):
                M.append([pow(z, sum(t[i] * Aab[i][j] * s[j] for i in range(pa) for j in range(q)) % p, qq)
                          for s in itertools.product((0, 1), repeat=q)])
            rs.append(rank_mod(M, qq))
        print(f" p={p} |R_a|={pa} q={q}: {rs}   (2^q = {2**q}; rows p^|R_a| = {p**pa})")
