"""The octahedron arrangement over F_{2^s}, g odd, g | 2^s - 1 (needed for the price statement via Theorem B of
q1-notes, which is for fields of characteristic 2).  Exact arithmetic in GF(2^s) with log tables."""
import sys, itertools
IRRED = {3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011, 8: 0b100011101, 10: 0b10000001001, 11: 0b100000000101, 12: 0b1000001010011}
def field(s):
    poly = IRRED[s]; n = 1 << s; exp = [1]*(2*n); log = [0]*n; x = 1
    for i in range(n-1):
        exp[i] = x; log[x] = i; x <<= 1
        if x & n: x ^= poly
    for i in range(n-1, 2*n): exp[i] = exp[i-(n-1)]
    assert len(set(exp[:n-1])) == n-1, "polynomial not primitive"
    mul = lambda a, b: 0 if a == 0 or b == 0 else exp[log[a]+log[b]]
    inv = lambda a: exp[(n-1-log[a]) % (n-1)]
    return n, exp, mul, inv
def rank2(rows, mul, inv):
    M = [r[:] for r in rows]; rk = 0
    for c in range(len(M[0])):
        p = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]; iv = inv(M[rk][c]); M[rk] = [mul(x, iv) for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]; M[i] = [x ^ mul(f, y) for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk
def run(g, par):
    s = next(s for s in range(2, 13) if (2**s - 1) % g == 0)
    n, exp, mul, inv = field(s); w_log = (n-1)//g
    a2, b2, g1, g2 = par
    lines = [('R', 0), ('R', b2 % g), ('C', 0), ('C', a2 % g), ('D', g1 % g), ('D', g2 % g)]
    on = lambda pt: [i for i, (t, v) in enumerate(lines) if (t == 'R' and pt[1] == v) or (t == 'C' and pt[0] == v) or (t == 'D' and (pt[0]-pt[1]) % g == v)]
    pts = set()
    for b in (0, b2 % g):
        for a in (0, a2 % g): pts.add((a, b))
        for d in (g1 % g, g2 % g): pts.add(((b+d) % g, b))
    for a in (0, a2 % g):
        for d in (g1 % g, g2 % g): pts.add((a, (a-d) % g))
    pts = sorted(pts)
    if len(pts) != 12 or any(len(on(p)) != 2 for p in pts): return None
    M = [[0]*12 for _ in range(6)]
    for j, p in enumerate(pts):
        for i in on(p): M[i][j] = 1
    bad = 0
    for t1 in range(1, g):
        for t2 in range(1, g):
            if (t1+t2) % g == 0: continue
            Mt = [[mul(x, exp[(w_log*((a*t1+b*t2) % g)) % (n-1)]) for x, (a, b) in zip(r, pts)] for r in M]
            if rank2(M + Mt, mul, inv) != 10: bad += 1
    return s, rank2(M, mul, inv), bad
for g in (5, 7, 9, 11, 13, 15, 17, 21, 23, 31, 33, 35, 39):
    out = None
    for par in [(1,1,2,3), (1,1,2,4), (1,1,2,5), (1,2,3,4), (1,1,3,5), (1,1,2,6), (1,1,2,7), (1,3,2,5), (2,1,3,5), (1,2,4,7), (2,3,1,6)] + \
               [p for p in itertools.product(range(1, 8), repeat=4) if p[2] < p[3]]:
        try: r = run(g, par)
        except StopIteration: r = None; break
        if r is not None and r[2] == 0 and r[1] == 5: out = (par, r); break
    print("g =", g, ": no field with s <= 12" if r is None and out is None else ("F_2^%d, params %s: rank M = %d, all non-collinear t independent" % (out[1][0], out[0], out[1][1]) if out else "no parameters found (char 2)"))
    sys.stdout.flush()
