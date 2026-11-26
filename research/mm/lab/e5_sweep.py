"""E5: sweep tiny bilinear maps F2^a x F2^b -> F2^c (a,b,c <= 3) and compare
  R   = bilinear rank over F2,
  Qf  = formal commutative quadratic complexity (products of linear forms in (x,y), identity of polynomials),
  Qb  = Boolean quadratic complexity (same but x^2 = x allowed),
  MC  = general XOR-AND multiplicative complexity (gates may take earlier AND outputs; function equality).
Always MC <= Qb <= Qf <= R, and Qf >= R/2.
Question: is MC < Qb ever?  (one example = 'function not formula' buys an AND)
usage: e5_sweep.py [nrandom] [seed]
"""
import sys, itertools, random, time, json
import pycryptosat
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from mc_sat import Enc, eval_circuit

def mk(nv0=0):
    s = pycryptosat.Solver(threads=1)
    st = {'n': nv0}
    def new():
        st['n'] += 1; return st['n']
    def AND(*xs):
        y = new()
        for x in xs: s.add_clause([-y, x])
        s.add_clause([y] + [-x for x in xs]); return y
    return s, new, AND

def rank_sat(T, a, b, k):
    c = len(T)
    s, new, AND = mk()
    al = [[new() for _ in range(a)] for _ in range(k)]
    be = [[new() for _ in range(b)] for _ in range(k)]
    g = [[new() for _ in range(k)] for _ in range(c)]
    P = [[[AND(al[j][u], be[j][v]) for v in range(b)] for u in range(a)] for j in range(k)]
    for o in range(c):
        for u in range(a):
            for v in range(b):
                s.add_xor_clause([AND(g[o][j], P[j][u][v]) for j in range(k)], bool(T[o][u][v]))
    return s.solve()[0]

def quad_sat(T, a, b, k, formal):
    c = len(T); n = a + b
    s, new, AND = mk()
    l1 = [[new() for _ in range(n)] for _ in range(k)]
    l2 = [[new() for _ in range(n)] for _ in range(k)]
    g = [[new() for _ in range(k)] for _ in range(c)]
    P = [[[AND(l1[j][u], l2[j][v]) for v in range(n)] for u in range(n)] for j in range(k)]
    for o in range(c):
        for u in range(n):
            for v in range(u + 1, n):
                tgt = (u < a <= v) and T[o][u][v - a]
                terms = []
                for j in range(k):
                    terms += [AND(g[o][j], P[j][u][v]), AND(g[o][j], P[j][v][u])]
                s.add_xor_clause(terms, bool(tgt))
            if formal:
                s.add_xor_clause([AND(g[o][j], P[j][u][u]) for j in range(k)], False)
    return s.solve()[0]

def mc_sat(T, a, b, k):
    c = len(T); n = a + b
    def f(bits):
        return [sum(bits[u] & bits[a + v] for u in range(a) for v in range(b) if T[o][u][v]) & 1 for o in range(c)]
    if k == 0:
        return all(f(bits) == [0] * c for bits in itertools.product([0, 1], repeat=n))
    E = Enc(n, c, k, f, threads=1)
    rows = list(itertools.product([0, 1], repeat=n))
    for r in rows:
        E.add_row(r)   # all 2^n rows: exact
    sat, sol = E.s.solve()
    if sat:
        C = E.model_circuit(sol)
        assert all(eval_circuit(C, r, n, k, c) == f(r) for r in rows)
    return sat

def minimize(fn, lo, hi):
    k = lo
    while k <= hi:
        if fn(k): return k
        k += 1
    return None

def analyse(T, a, b):
    c = len(T)
    R = minimize(lambda k: rank_sat(T, a, b, k), 0, a * b)
    Qf = minimize(lambda k: quad_sat(T, a, b, k, True), (R + 1) // 2, R)
    Qb = minimize(lambda k: quad_sat(T, a, b, k, False), 0, Qf)
    MC = minimize(lambda k: mc_sat(T, a, b, k), 0, Qb)
    return R, Qf, Qb, MC

def structured():
    S = {}
    # polynomial mult mod x^2 (truncated): (a0+a1x)(b0+b1x) -> c0=a0b0, c1=a0b1+a1b0
    S['trunc2'] = (2, 2, [[[1, 0], [0, 0]], [[0, 1], [1, 0]]])
    # full poly mult 2x2 terms -> 3 coefficients
    S['polymul2'] = (2, 2, [[[1, 0], [0, 0]], [[0, 1], [1, 0]], [[0, 0], [0, 1]]])
    # F4 = F2[x]/(x^2+x+1): c0=a0b0+a1b1, c1=a0b1+a1b0+a1b1
    S['F4'] = (2, 2, [[[1, 0], [0, 1]], [[0, 1], [1, 1]]])
    # poly mult 3-term -> 5 coeffs
    pm3 = [[[1 if u + v == d else 0 for v in range(3)] for u in range(3)] for d in range(5)]
    S['polymul3'] = (3, 3, pm3)
    S['trunc3'] = (3, 3, pm3[:3])
    # F8 = F2[x]/(x^3+x+1)
    def f8():
        out = [[[0] * 3 for _ in range(3)] for _ in range(3)]
        red = {0: [0], 1: [1], 2: [2], 3: [0, 1], 4: [1, 2]}
        for u in range(3):
            for v in range(3):
                for d in red[u + v]:
                    out[d][u][v] ^= 1
        return out
    S['F8'] = (3, 3, f8())
    # 2x2 matrix times vector: x = A (4 entries) too big for a<=3; use 3x... keep a<=3: 1x3 . 3x1 inner product
    S['inner3'] = (3, 3, [[[1 if u == v else 0 for v in range(3)] for u in range(3)]])
    # 2x2 matrix (a=4) x vector (b=2) -> 2 outputs (n=6 inputs, still easy)
    S['matvec2'] = (4, 2, [[[1 if (u // 2 == i and u % 2 == v) else 0 for v in range(2)] for u in range(4)] for i in range(2)])
    # <1,2,2>: row vector (2) times 2x2 matrix (4)
    S['vecmat'] = (2, 4, [[[1 if (v % 2 == k and v // 2 == u) else 0 for v in range(4)] for u in range(2)] for k in range(2)])
    # outer product 2x2
    S['outer2'] = (2, 2, [[[1 if (u == i and v == j) else 0 for v in range(2)] for u in range(2)] for i in range(2) for j in range(2)])
    # <2,1,3>-ish outer 2x3 needs 6 ANDs
    S['outer23'] = (2, 3, [[[1 if (u == i and v == j) else 0 for v in range(3)] for u in range(2)] for i in range(2) for j in range(3)])
    # cyclic convolution length 3 over F2 (F2[x]/(x^3-1))
    S['cyc3'] = (3, 3, [[[1 if (u + v) % 3 == d else 0 for v in range(3)] for u in range(3)] for d in range(3)])
    return S

if __name__ == '__main__':
    nrand = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rnd = random.Random(seed)
    res = []
    items = list(structured().items())
    for t in range(nrand):
        a = rnd.randint(2, 3); b = rnd.randint(2, 3); c = rnd.randint(2, 3)
        T = [[[rnd.randint(0, 1) for _ in range(b)] for _ in range(a)] for _ in range(c)]
        items.append((f'rand{seed}_{t}_{a}{b}{c}', (a, b, T)))
    gaps = 0
    print("name a b c | R Qf Qb MC | time")
    for name, (a, b, T) in items:
        t0 = time.time()
        R, Qf, Qb, MC = analyse(T, a, b)
        flag = ' <-- MC<Qb' if MC < Qb else (' <-- Qb<Qf' if Qb < Qf else '')
        gaps += MC < Qb
        print(f"{name} {a} {b} {len(T)} | {R} {Qf} {Qb} {MC} | {time.time()-t0:.1f}s{flag}", flush=True)
        res.append(dict(name=name, a=a, b=b, c=len(T), R=R, Qf=Qf, Qb=Qb, MC=MC))
    json.dump(res, open(f'e5_res_{seed}_{nrand}.json', 'w'))
    print("maps:", len(items), "with MC<Qb:", gaps)
