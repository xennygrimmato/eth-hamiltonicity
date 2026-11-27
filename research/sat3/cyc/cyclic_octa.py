"""Octahedron arrangement for the 3-net of Z_g (classes r, c, r+c): exact verification over a prime field.

Construction (cyclic-cap.md section 4).  F = F_q, q prime, q = 1 mod g, w in F of order g.
Frequencies: the 12 intersection points xi = (alpha,beta) in Z_g^2 of two rows beta in {0,b2}, two columns
alpha in {0,a2} and two diagonals alpha-beta in {g1,g2} (pairwise intersections, each point on exactly two lines).
F^12 has basis e_xi; translations act by rho(t1,t2) e_xi = w^(alpha t1 + beta t2) e_xi.
M = oriented incidence matrix (6 lines x 12 points) of the octahedron K_{2,2,2}; rank 5.
   V_{R_0} = span of the two row vectors, V_{C_0} = span of the two column vectors, V_{D_0} = the two diagonal vectors,
   V_{R_r} = rho(r,0) V_{R_0}, V_{C_c} = rho(0,c) V_{C_0}, V_{D_d} = rho(d,0) V_{D_0};  W_(r,c) = rho(r,c) W_0, W_0 = rowspace(M).
Checked here, exactly (Gaussian elimination mod q):
   (a) rho(0,c) fixes V_{R_0}, rho(r,0) fixes V_{C_0}, rho(t,-t) fixes V_{D_0}  (hubs well defined, node (r,c) has hubs
       R_r, C_c, D_{r+c} inside W_(r,c));
   (b) dim of every hub is 2, dim W = 5;
   (c) W_0 and rho(t) W_0 are independent for EVERY non-collinear t (t1, t2, t1+t2 all nonzero).
Then every non-collinear edge has s^k = delta*sqrt(2/5) for the three merges at once (legs: W_n at the top level,
W_n' at the bottom level), delta = 2.
usage: cyclic_octa.py g [a2 b2 g1 g2]
"""
import sys, itertools

def rank_mod(rows, q):
    M = [r[:] for r in rows]; rk = 0
    ncol = len(M[0])
    for c in range(ncol):
        p = next((i for i in range(rk, len(M)) if M[i][c] % q), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        inv = pow(M[rk][c], q-2, q); M[rk] = [x*inv % q for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % q:
                f = M[i][c]; M[i] = [(x - f*y) % q for x, y in zip(M[i], M[rk])]
        rk += 1
        if rk == len(M): break
    return rk

def isprime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True

def setup(g, a2, b2, g1, g2):
    q = g + 1
    while not isprime(q): q += g
    # element of order g
    for x in range(2, q):
        w = pow(x, (q-1)//g, q)
        if all(pow(w, g//p, q) != 1 for p in range(2, g+1) if g % p == 0 and isprime(p)): break
    lines = [('R', 0), ('R', b2 % g), ('C', 0), ('C', a2 % g), ('D', g1 % g), ('D', g2 % g)]
    def on(pt):
        a, b = pt
        return [i for i, (t, v) in enumerate(lines) if (t == 'R' and b == v) or (t == 'C' and a == v) or (t == 'D' and (a-b) % g == v)]
    pts = set()
    for (t1, v1), (t2, v2) in itertools.combinations(lines, 2):
        if t1 == t2: continue
        d = {t1: v1, t2: v2}
        if 'R' in d and 'C' in d: pts.add((d['C'], d['R']))
        elif 'R' in d: pts.add(((d['R'] + d['D']) % g, d['R']))
        else: pts.add((d['C'], (d['C'] - d['D']) % g))
    pts = sorted(pts)
    if len(pts) != 12 or any(len(on(p)) != 2 for p in pts): return None
    M = [[0]*12 for _ in range(6)]
    for j, p in enumerate(pts):
        i1, i2 = on(p); M[i1][j] = 1; M[i2][j] = q - 1
    return q, w, pts, M

def rho(rows, t, pts, w, q):
    return [[x * pow(w, (a*t[0] + b*t[1]) % (q-1), q) % q for x, (a, b) in zip(r, pts)] for r in rows]

def verify(g, a2, b2, g1, g2, verbose=True):
    s = setup(g, a2, b2, g1, g2)
    if s is None: return None
    q, w, pts, M = s
    VR, VC, VD = M[0:2], M[2:4], M[4:6]
    ok = rank_mod(M, q) == 5 and all(rank_mod(V, q) == 2 for V in (VR, VC, VD))
    for t in range(1, g):
        ok &= rank_mod(VR + rho(VR, (0, t), pts, w, q), q) == 2
        ok &= rank_mod(VC + rho(VC, (t, 0), pts, w, q), q) == 2
        ok &= rank_mod(VD + rho(VD, (t, (-t) % g), pts, w, q), q) == 2
    bad = []
    for t1 in range(1, g):
        for t2 in range(1, g):
            if (t1 + t2) % g == 0: continue
            if rank_mod(M + rho(M, (t1, t2), pts, w, q), q) != 10: bad.append((t1, t2))
    if verbose:
        print("g = %d  field F_%d  params %s  structure ok: %s  non-collinear t with W_0 ^ rho(t)W_0 != 0: %d"
              % (g, q, (a2, b2, g1, g2), ok, len(bad)), bad[:4])
    return ok, bad

if __name__ == "__main__":
    if len(sys.argv) > 2:
        verify(int(sys.argv[1]), *map(int, sys.argv[2:6]))
    else:
        gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 40
        fam = [(1, 1, 2, 3), (1, 1, 2, 4), (1, 1, 2, 5), (1, 1, 2, 6), (1, 2, 3, 4), (1, 1, 3, 5), (1, 3, 2, 7)]
        import math
        for g in range(4, gmax + 1):
            for par in fam + [p for p in itertools.product(range(1, min(g, 9)), repeat=4) if p[2] < p[3]]:
                r = verify(g, *par, verbose=False)
                if r is not None and r[0] and not r[1]:
                    ng = (g-1)*(g-2)
                    val0 = (g-2)/(g+1)*math.sqrt(0.4)
                    print("g = %2d: params %s verified;  value >= (g-2)/(g+1)*sqrt(2/5) = %.4f ;  with collinear edges at one merge: %.4f"
                          % (g, par, val0, ((g-2)*math.sqrt(0.4) + 1)/(g+1)))
                    break
            else:
                print("g = %2d: no parameters found in the list" % g)
            sys.stdout.flush()
