"""Q1 check: the 3-net of F_2^m placed in the space C_N of real filtrations of V = F_2^(m+2).

Points of C_N: filtrations = lists [(level, subspace)], levels decreasing, subspaces increasing, last = V.
d(F,F')^2 = sum_{i,j} m(i,j) (a_i-b_j)^2,  m = second difference of dim(A_i cap B_j)
(= Euclidean distance in any frame adapted to both; the joint multiset of levels is frame independent).

Hubs: the points <(x,y)>, x in F_2^2 nonzero, y in F_2^m  (level 1 on the line, 0 on V).
Nodes: a = (r,c) in (F_2^m)^2, W_a = {0,(e1,r),(e2,c),(e1+e2,r+c)}.  Classes r, c, r+c.
Generic edge (W cap W' = 0): legs x = [W:(1+T)/2, W+R:0, V:-T/2], y = same with W'.
Reports s^k_e, b_k, rho for finite T, and tests metric / CAT(0) four-point inequalities on random points.
"""
import itertools, math, random, sys

def span(vs):
    S = {0}
    for v in vs:
        if v not in S:
            S |= {s ^ v for s in S}
    return frozenset(S)

def dim(S):
    return len(S).bit_length() - 1

def dist(F, G):
    d2 = 0.0
    prevA = frozenset({0}); 
    for i, (a, A) in enumerate(F):
        prevB = frozenset({0})
        for j, (b, B) in enumerate(G):
            m = dim(A & B) - dim(prevA & B) - dim(A & prevB) + dim(prevA & prevB)
            if m:
                d2 += m * (a - b) ** 2
            prevB = B
        prevA = A
    return math.sqrt(d2)

def run(m, T):
    N = m + 2
    V = frozenset(range(1 << N))
    g = 1 << m
    xs = [1, 2, 3]                      # classes: e1, e2, e1+e2 (low two bits)
    def pt(x, y): return x | (y << 2)
    def hub(x, y): return [(1.0, span([pt(x, y)])), (0.0, V)]
    nodes = [(r, c) for r in range(g) for c in range(g)]
    def W(n):
        r, c = n
        return span([pt(1, r), pt(2, c)])
    def hubs_of(n):
        r, c = n
        return [hub(1, r), hub(2, c), hub(3, r ^ c)]
    def complement(S):
        # extend S to V; return subspace S + R with R a complement of S+S' ... here: any chain element W+R
        return None
    Ltot = 0.0; H = [0.0, 0.0, 0.0]; E = 0; Egen = 0
    smin = 9; smax = -9
    for n, n2 in itertools.combinations(nodes, 2):
        E += 1
        Wn, Wn2 = W(n), W(n2)
        I = Wn & Wn2
        if len(I) == 1:
            Egen += 1
            S = span(list(Wn) + list(Wn2))
            # R: complement of S in V ; W+R and W'+R
            R = [0]
            cur = S
            for v in range(1, 1 << N):
                if v not in cur:
                    R.append(v); cur = span(list(cur) + [v])
            WR = span(list(Wn) + R); WR2 = span(list(Wn2) + R)
            a, b = (1 + T) / 2, T / 2
            if dim(WR) == N:   # R empty and W+W' = V : skip the middle level
                x = [(a, Wn), (-b, V)]
            else:
                x = [(a, Wn), (0.0, WR), (-b, V)]
            if dim(WR2) == N:
                y = [(a, Wn2), (-b, V)]
            else:
                y = [(a, Wn2), (0.0, WR2), (-b, V)]
            # for N=4, W+W'=V: chain W < V with level 0 absent; fix: levels W:a, V:-b is right (W' at -b)
            dxy = dist(x, y)
            hs, hs2 = hubs_of(n), hubs_of(n2)
            for k in range(3):
                s = dxy - dist(x, hs[k]) - dist(y, hs2[k])
                smin = min(smin, s); smax = max(smax, s)
                H[k] += dist(x, hs[k]) + dist(y, hs2[k])
            Ltot += dxy
        else:
            # collinear nodes (common hub p, class k0): far legs that give sqrt2 to ONE other class k1 and 0 to the rest.
            # frame (h, p, r.., h'), h = hub of class k1 at n, h' = hub of class k1 at n2; direction (1,0,..,0,-1)/sqrt2.
            p = [v for v in I if v][0]
            hs, hs2 = hubs_of(n), hubs_of(n2)
            k0 = [k for k in range(3) if hs[k][0][1] == hs2[k][0][1]][0]
            k1 = [k for k in range(3) if k != k0][E % 2]      # alternate between the two other classes
            h = [v for v in hs[k1][0][1] if v][0]; h2 = [v for v in hs2[k1][0][1] if v][0]
            R = []; cur = span([h, p, h2])
            for v in range(1, 1 << N):
                if v not in cur:
                    R.append(v); cur = span(list(cur) + [v])
            t = T / math.sqrt(2)
            x = [(t, span([h])), (0.0, span([h, p] + R)), (-t, V)]
            y = [(t, span([h2])), (0.0, span([h2, p] + R)), (-t, V)]
            dxy = dist(x, y)
            Ltot += dxy
            for k in range(3):
                H[k] += dist(x, hs[k]) + dist(y, hs2[k])
    delta = math.sqrt(2)
    b = [(Ltot - H[k]) / delta for k in range(3)]
    print(f"m={m} g={g} T={T}: E={E} generic={Egen}  s^k on generic edges in [{smin:.6f},{smax:.6f}]")
    print("   b_k/E =", [round(x / E, 6) for x in b], " cap sqrt(Ex/2E) =",
          round(math.sqrt((E - g * g * (g - 1) / 2) / (2 * E)), 6), " 1/sqrt2 =", round(1 / math.sqrt(2), 6),
          " predicted (g-2)/((g+1)sqrt2) + 1/(g+1) =", round((g - 2) / ((g + 1) * delta) + 1 / (g + 1), 6))

def random_filtration(N, rng):
    V = frozenset(range(1 << N))
    basis = []
    cur = frozenset({0})
    while dim(cur) < N:
        v = rng.randrange(1, 1 << N)
        if v not in cur:
            basis.append(v); cur = span(basis)
    lv = sorted([rng.choice([0, 0.5, 1, 1.5, 2]) for _ in range(N)], reverse=True)
    F = []
    for i in range(N):
        if i == N - 1 or lv[i + 1] != lv[i]:
            F.append((lv[i], span(basis[: i + 1])))
    return F

def cat0_tests(N, trials, rng):
    worst_tri = 0.0; worst_quad = 0.0
    for _ in range(trials):
        P = [random_filtration(N, rng) for _ in range(4)]
        D = [[dist(P[i], P[j]) for j in range(4)] for i in range(4)]
        for i, j, k in itertools.permutations(range(3), 3):
            worst_tri = max(worst_tri, D[i][j] - D[i][k] - D[k][j])
        # Reshetnyak: |xv|^2+|yu|^2 <= |xy|^2+|yv|^2+|vu|^2+|ux|^2 for the cycle x,y,v,u
        for (x, y, v, u) in itertools.permutations(range(4), 4):
            worst_quad = max(worst_quad, D[x][v] ** 2 + D[y][u] ** 2 - D[x][y] ** 2 - D[y][v] ** 2 - D[v][u] ** 2 - D[u][x] ** 2)
    print(f"N={N}: {trials} random 4-tuples: max triangle violation {worst_tri:.2e}, max quadrilateral violation {worst_quad:.2e}")

if __name__ == "__main__":
    rng = random.Random(1)
    cat0_tests(4, 3000, rng)
    cat0_tests(5, 1500, rng)
    for m, T in [(2, 1e2), (2, 1e4), (3, 1e4), (4, 1e4)]:
        run(m, T)
