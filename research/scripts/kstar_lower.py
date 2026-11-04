"""Checks for Theorem L (k* = Omega(log n) on the bounded-degree crossing grids H_t), see kstar.md.
 (a) decomposition lemma: for a random F: turns -> GF(2)^k on H_{p,q}, F(C) = XOR of phi_kappa(a,b)
     over the corners of C, for EVERY directed cycle C (phi computed from F by the prefix-sum formula);
 (b) the balanced 24-cycle B on the 4x4 abstract grid (each corner type used twice) lifts to a
     simple cycle of H_t for random row/column 4-subsets, with the same corner types;
 (c) hence: F constant-coloured on a 4x4 subgrid => F(lift of B) = 0 (checked on planted examples)."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kstar_grid as g
from linenc2_lib import directed_simple_cycles
def phi_table(F, p, q, R, Cc):
    def f(v, u, w): return F.get((v, u, w), 0)
    sp = {}; sm = {}; cp = {}; cm = {}
    for a in range(p):
        for x in range(1, q-1):
            sp[a, x] = f(R(a, x), R(a, x-1), R(a, x+1)); sm[a, x] = f(R(a, x), R(a, x+1), R(a, x-1))
    for b in range(q):
        for x in range(1, p-1):
            cp[x, b] = f(Cc(x, b), Cc(x-1, b), Cc(x+1, b)); cm[x, b] = f(Cc(x, b), Cc(x+1, b), Cc(x-1, b))
    def Pp(a, y): return 0 if y < 0 else __import__('functools').reduce(lambda s, x: s ^ sp.get((a, x), 0), range(y+1), 0)
    def Pm(a, y): return __import__('functools').reduce(lambda s, x: s ^ sm.get((a, x), 0), range(max(y, 0), q), 0)
    def Qp(b, y): return 0 if y < 0 else __import__('functools').reduce(lambda s, x: s ^ cp.get((x, b), 0), range(y+1), 0)
    def Qm(b, y): return __import__('functools').reduce(lambda s, x: s ^ cm.get((x, b), 0), range(max(y, 0), p), 0)
    rowEnd = lambda a, b, h: Pp(a, b-1) if h > 0 else Pm(a, b+1)
    rowSt = lambda a, b, h: Pp(a, b) if h > 0 else Pm(a, b)
    colEnd = lambda a, b, v: Qp(b, a-1) if v > 0 else Qm(b, a+1)
    colSt = lambda a, b, v: Qp(b, a) if v > 0 else Qm(b, a)
    def phi(kind, a, b, h, v):
        if kind == 'HV':
            return f(R(a, b), R(a, b-h), Cc(a, b)) ^ f(Cc(a, b), R(a, b), Cc(a+v, b)) ^ rowEnd(a, b, h) ^ colSt(a, b, v)
        return f(Cc(a, b), Cc(a-v, b), R(a, b)) ^ f(R(a, b), Cc(a, b), R(a, b+h)) ^ colEnd(a, b, v) ^ rowSt(a, b, h)
    return phi
def corners_with_pos(cyc, p, q):
    L = len(cyc); out = []
    for i in range(L):
        u, v, w = cyc[i-1], cyc[i], cyc[(i+1) % L]
        tv, a, b = g.info(v, p, q)
        if tv != 'r': continue
        tu, tw = g.info(u, p, q)[0], g.info(w, p, q)[0]
        if tu == 'r' and tw == 'r': continue
        if tw == 'c': out.append(('HV', a, b, b - g.info(u, p, q)[2], g.info(cyc[(i+2) % L], p, q)[1] - a))
        else: out.append(('VH', a, b, g.info(w, p, q)[2] - b, a - g.info(cyc[i-2], p, q)[1]))
    return out
def Fsum(F, cyc):
    L = len(cyc); s = 0
    for i in range(L): s ^= F.get((cyc[i], cyc[i-1], cyc[(i+1) % L]), 0)
    return s
def random_F(n, E, k, rng):
    adj = [[] for _ in range(n)]
    for i, j in E: adj[i].append(j); adj[j].append(i)
    return {(v, u, w): rng.randrange(1 << k) for v in range(n) for u in adj[v] for w in adj[v] if u != w}, adj
B44 = [('r',0,0),('r',0,1),('r',0,2),('r',0,3),('c',0,3),('c',1,3),('c',2,3),('c',3,3),('r',3,3),('r',3,2),('r',3,1),('c',3,1),('c',2,1),('c',1,1),('r',1,1),('r',1,2),('c',1,2),('c',2,2),('r',2,2),('r',2,1),('r',2,0),('c',2,0),('c',1,0),('c',0,0)]
def lift(Bab, A, Bc, t):
    """lift abstract cycle on 4x4 grid to H_{t,t} with rows A, columns Bc (sorted)."""
    _, _, R, Cc = g.H(t, t); vs = [(R if s == 'r' else Cc)(A[a], Bc[b]) for s, a, b in Bab]
    out = []
    for i in range(len(vs)):
        x, y = vs[i], vs[(i+1) % len(vs)]; out.append(x)
        tx, a1, b1 = g.info(x, t, t); ty, a2, b2 = g.info(y, t, t)
        if tx == ty == 'r' and a1 == a2:
            st = 1 if b2 > b1 else -1; out += [R(a1, b) for b in range(b1+st, b2, st)]
        elif tx == ty == 'c' and b1 == b2:
            st = 1 if a2 > a1 else -1; out += [Cc(a, b1) for a in range(a1+st, a2, st)]
    return out
if __name__ == '__main__':
    rng = random.Random(7); ok = True
    for (p, q) in [(3, 4), (4, 4), (4, 5)]:
        n, E, R, Cc = g.H(p, q); cycles = directed_simple_cycles(n, E)
        for trial in range(3):
            F, _ = random_F(n, E, 5, rng); phi = phi_table(F, p, q, R, Cc)
            for c in cycles:
                s = 0
                for (kind, a, b, h, v) in corners_with_pos(c, p, q): s ^= phi(kind, a, b, h, v)
                if s != Fsum(F, c): ok = False
        print(f'(a) H_{p},{q}: {len(cycles)} cycles x 3 random F: decomposition', 'PASS' if ok else 'FAIL')
    t = 9; n, E, R, Cc = g.H(t, t); adj = [set() for _ in range(n)]
    for i, j in E: adj[i].add(j); adj[j].add(i)
    okb = True
    for trial in range(200):
        A = sorted(rng.sample(range(t), 4)); Bc = sorted(rng.sample(range(t), 4)); C = lift(B44, A, Bc, t)
        simple = len(set(C)) == len(C) and all(C[(i+1) % len(C)] in adj[C[i]] for i in range(len(C)))
        from collections import Counter
        cnt = Counter((k, h, v) for (k, a, b, h, v) in corners_with_pos(C, t, t))
        okb &= simple and all(x % 2 == 0 for x in cnt.values()) and len(cnt) == 4
    print('(b) 200 random lifts of the balanced 4x4 cycle into H_9: simple and balanced', 'PASS' if okb else 'FAIL')
    # (c) planted: F random, then fix phi to be constant on A x Bc by adjusting rung turns, test F(C)=0
    okc = True
    for trial in range(50):
        F, _ = random_F(n, E, 6, rng); A = sorted(rng.sample(range(t), 4)); Bc = sorted(rng.sample(range(t), 4))
        target = {}; phi = phi_table(F, t, t, R, Cc)
        for a in A:
            for b in Bc:
                for (kind, h, v) in [('HV', 1, 1), ('HV', -1, -1), ('VH', 1, -1), ('VH', -1, 1)]:
                    if not ((0 <= b-h < t and 0 <= a+v < t) if kind == 'HV' else (0 <= a-v < t and 0 <= b+h < t)): continue
                    cur = phi(kind, a, b, h, v); want = target.setdefault((kind, h, v), rng.randrange(64))
                    key = (R(a, b), R(a, b-h), Cc(a, b)) if kind == 'HV' else (R(a, b), Cc(a, b), R(a, b+h))
                    F[key] ^= cur ^ want      # this rung turn appears only in phi_kind(a,b)
        C = lift(B44, A, Bc, t); okc &= Fsum(F, C) == 0
    print('(c) 50 planted cell-homogeneous F: F(lift of B) = 0', 'PASS' if okc else 'FAIL')
    print('ALL PASS' if ok and okb and okc else 'SOME FAIL')
