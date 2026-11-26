#!/usr/bin/env python3
"""Search for placements f: V(G) -> Mat_mu(F_2) maximising
   beta(f) = E_pairs rank(f(u)-f(v)) / E_edges rank(f(u)-f(v))
(pairs = ordered pairs incl. u=v, uniform; edges uniform). Compare with the best cut (diagonal / L1) value.
Simulated annealing over single-vertex moves (replace f(v) by f(v) + low-rank or random matrix)."""
import sys, random, math, itertools

def rank_bits(rows, mu):
    # rows: list of mu ints (each a row of the matrix as bitmask)
    r = 0; rows = list(rows)
    for c in range(mu):
        p = None
        for i in range(r, mu):
            if rows[i] >> c & 1: p = i; break
        if p is None: continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(mu):
            if i != r and rows[i] >> c & 1: rows[i] ^= rows[r]
        r += 1
    return r

class Rank:
    def __init__(self, mu):
        self.mu = mu; self.cache = {}
    def __call__(self, a, b):
        x = a ^ b
        r = self.cache.get(x)
        if r is None:
            mu = self.mu
            rows = [(x >> (mu * i)) & ((1 << mu) - 1) for i in range(mu)]
            r = rank_bits(rows, mu); self.cache[x] = r
        return r

def graphs():
    G = {}
    # Petersen
    E = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
    G['petersen'] = (10, E)
    # Heawood (LCF [5,-5]^7)
    def lcf(n, pat):
        E = set()
        for i in range(n):
            E.add(tuple(sorted((i, (i + 1) % n))))
            E.add(tuple(sorted((i, (i + pat[i % len(pat)]) % n))))
        return (n, sorted(E))
    G['heawood'] = lcf(14, [5, -5])
    G['pappus'] = lcf(18, [5, 7, -7, 7, -7, -5])
    G['mcgee'] = lcf(24, [12, 7, -7])
    G['tutte-coxeter'] = lcf(30, [-13, -9, 7, -7, 9, 13])
    G['K4'] = (4, list(itertools.combinations(range(4), 2)))
    G['K33'] = (6, [(i, 3 + j) for i in range(3) for j in range(3)])
    G['cube'] = (8, [(i, i ^ (1 << b)) for i in range(8) for b in range(3) if i < i ^ (1 << b)])
    return G

def best_cut(n, E):
    best = 0; arg = None
    m = len(E)
    for S in range(1, 1 << (n - 1)):
        s = bin(S).count('1')
        cut = sum(1 for (u, v) in E if (S >> u & 1) != (S >> v & 1))
        if cut == 0: continue
        val = (2 * s * (n - s) / n ** 2) / (cut / m)
        if val > best: best = val; arg = S
    return best, arg

def anneal(n, E, mu, iters, seed, rk):
    rnd = random.Random(seed)
    m = len(E); adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    M = 1 << (mu * mu)
    def rand_low():
        # random rank-one matrix u x^T
        u = rnd.randrange(1, 1 << mu); x = rnd.randrange(1, 1 << mu)
        a = 0
        for i in range(mu):
            if u >> i & 1: a |= x << (mu * i)
        return a
    f = [0] * n
    for v in range(n): f[v] = rnd.randrange(M) if rnd.random() < 0.5 else rand_low()
    def energies(f):
        e = sum(rk(f[u], f[v]) for u, v in E)
        p = sum(rk(f[u], f[v]) for u in range(n) for v in range(u + 1, n))
        return e, p
    e, p = energies(f)
    def val(e, p): return (2 * p / n ** 2) / (e / m) if e > 0 else 0.0
    cur = val(e, p); best = cur; bestf = f[:]
    T0 = 0.3
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-3
        v = rnd.randrange(n)
        mv = rnd.random()
        if mv < 0.6: new = f[v] ^ rand_low()
        elif mv < 0.8: new = f[rnd.choice(adj[v])] ^ (rand_low() if rnd.random() < 0.7 else 0)
        else: new = rnd.randrange(M)
        de = sum(rk(new, f[w]) - rk(f[v], f[w]) for w in adj[v])
        dp = sum(rk(new, f[w]) - rk(f[v], f[w]) for w in range(n) if w != v)
        ne, np_ = e + de, p + dp
        nv = val(ne, np_)
        if nv >= cur or rnd.random() < math.exp((nv - cur) / T):
            f[v] = new; e, p, cur = ne, np_, nv
            if cur > best: best = cur; bestf = f[:]
    return best, bestf

if __name__ == "__main__":
    G = graphs()
    names = sys.argv[1].split(',') if len(sys.argv) > 1 else list(G)
    mus = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [1, 2, 3]
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
    for name in names:
        n, E = G[name]
        bc, arg = best_cut(n, E) if n <= 24 else (float('nan'), None)
        out = [f"{name}: n={n} m={len(E)} best cut ratio={bc:.4f}"]
        for mu in mus:
            rk = Rank(mu)
            b = 0; bf = None
            for seed in range(6):
                bb, ff = anneal(n, E, mu, iters, seed, rk)
                if bb > b: b, bf = bb, ff
            out.append(f"mu={mu}: {b:.4f}")
        print("  ".join(out), flush=True)
