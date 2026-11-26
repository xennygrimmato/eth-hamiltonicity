# brute-force check of the far-leg hub terms (points / hyperplanes, levels a >= c) against exact filtration distances
import sys, random, math, itertools
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/sat3')
from q1_verify import span, dim, dist
N = 4; V = frozenset(range(1 << N)); rng = random.Random(3)
def frame():
    while True:
        f = [rng.randrange(1, 1 << N) for _ in range(N)]
        if dim(span(f)) == N: return f
def filt_from(f, x):
    lv = sorted(set(x), reverse=True)
    return [(s, span([f[i] for i in range(N) if x[i] >= s])) for s in lv]
def hub(kind, p, a, c):
    U = span([p]) if kind == 0 else frozenset(v for v in range(1 << N) if bin(v & p).count('1') % 2 == 0)
    return [(a, U), (c, V)] if a > c else [(c, V)]
def term(f, kind, p, a, c, d, side):
    # predicted
    coords = []
    # support of p in frame f: solve f-combination
    for combo in range(1, 1 << N):
        v = 0
        for i in range(N):
            if combo >> i & 1: v ^= f[i]
        if v == p: A = [i for i in range(N) if combo >> i & 1]
    D = [i for i in range(N) if bin(f[i] & p).count('1') % 2 == 1]
    S = sum(d)
    if kind == 0:
        return (a - c) * min(d[i] for i in A) + c * S if side == 0 else -(a - c) * max(d[i] for i in A) - c * S
    return a * S - (a - c) * max(d[i] for i in D) if side == 0 else -a * S + (a - c) * min(d[i] for i in D)
worst = 0
for t in range(300):
    f = frame(); d = [rng.gauss(0, 1) for _ in range(N)]; nr = math.sqrt(sum(x * x for x in d)); d = [x / nr for x in d]
    T = 1e5
    x = filt_from(f, [T * di for di in d]); y = filt_from(f, [-T * di for di in d])
    kind, kind2 = rng.randrange(2), rng.randrange(2)
    p, p2 = rng.randrange(1, 1 << N), rng.randrange(1, 1 << N)
    a, c = rng.uniform(0, 2), rng.uniform(-1, 1); a = max(a, c)
    b, c2 = rng.uniform(0, 2), rng.uniform(-1, 1); b = max(b, c2)
    s_exact = dist(x, y) - dist(x, hub(kind, p, a, c)) - dist(y, hub(kind2, p2, b, c2))
    s_pred = term(f, kind, p, a, c, d, 0) + term(f, kind2, p2, b, c2, d, 1)
    worst = max(worst, abs(s_exact - s_pred))
print('max |exact - predicted| over 300 random cases at T=1e5:', worst)
def d2_pred(h1, h2):
    (k1, p1, a, c), (k2, p2, b, c2) = h1, h2
    dk = lambda k: 1 if k == 0 else N - 1
    dot = bin(p1 & p2).count('1') % 2
    if k1 == 0 and k2 == 0: i = int(p1 == p2)
    elif k1 == 1 and k2 == 1: i = N - 1 if p1 == p2 else N - 2
    else: i = int(dot == 0)
    K1, K2 = dk(k1), dk(k2)
    return i * (a - b) ** 2 + (K1 - i) * (a - c2) ** 2 + (K2 - i) * (c - b) ** 2 + (N - K1 - K2 + i) * (c - c2) ** 2
w2 = 0
for t in range(500):
    h1 = (rng.randrange(2), rng.randrange(1, 1 << N), rng.uniform(0, 2), rng.uniform(-1, 1))
    h2 = (rng.randrange(2), rng.randrange(1, 1 << N), rng.uniform(0, 2), rng.uniform(-1, 1))
    h1 = (h1[0], h1[1], max(h1[2], h1[3] + 1e-3), h1[3]); h2 = (h2[0], h2[1], max(h2[2], h2[3] + 1e-3), h2[3])
    w2 = max(w2, abs(dist(hub(*h1), hub(*h2)) ** 2 - d2_pred(h1, h2)))
print('max |d^2 exact - formula| over 500 hub pairs:', w2)
