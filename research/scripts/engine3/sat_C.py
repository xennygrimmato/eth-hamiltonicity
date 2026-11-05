"""Task B: GF(2) SAT search at N=2 for f_C = sum_t T_t, T_t an arbitrary triangle network on the 3 groups of its
merge k_t (bond dims d01,d02,d12; local tensors W_g arbitrary on the 4 legs of group g -> NON-local terms allowed).
Cost of a term = log2(d01 d02 d12) (network cost); weight 2^cost; S = sum of weights.  Solutions re-verified."""
import itertools, sys, time, threading, numpy as np
from pysat.solvers import Solver
from lib import *
cfg = config_C(2); target = graph_tensor(cfg).reshape(-1); NL = 12
PAIRS = [(0, 1), (0, 2), (1, 2)]
class Enc:
    def __init__(s): s.n = 0; s.cl = []
    def var(s): s.n += 1; return s.n
    def AND(s, xs):
        z = s.var()
        for x in xs: s.cl.append([-z, x])
        s.cl.append([z] + [-x for x in xs]); return z
    def XOR_eq(s, xs, b):
        if not xs:
            if b: s.cl.append([])
            return
        acc = xs[0]
        for x in xs[1:]:
            z = s.var(); s.cl += [[-z, acc, x], [-z, -acc, -x], [z, -acc, x], [z, acc, -x]]; acc = z
        s.cl.append([acc] if b else [-acc])
def encode(terms):
    E = Enc(); tv = []
    for (k, d) in terms:
        gl = group_legs(cfg, cfg['merges'][k]); W = {}
        for g in range(3):
            inc = [p for p in PAIRS if g in p]
            for lv in itertools.product(range(2), repeat=len(gl[g])):
                for bi in itertools.product(*[range(d[p]) for p in inc]): W[(g, lv, bi)] = E.var()
        tv.append((k, d, gl, W))
    for idx, e in enumerate(itertools.product(range(2), repeat=NL)):
        lits = []
        for (k, d, gl, W) in tv:
            for th in itertools.product(*[range(d[p]) for p in PAIRS]):
                thd = dict(zip(PAIRS, th))
                lits.append(E.AND([W[(g, tuple(e[i] for i in gl[g]), tuple(thd[p] for p in PAIRS if g in p))] for g in range(3)]))
        E.XOR_eq(lits, int(target[idx]))
    return E, tv
def rebuild(tv, model):
    pos = set(l for l in model if l > 0); Ts = []
    for (k, d, gl, W) in tv:
        T = np.zeros((2,) * NL, dtype=np.int64)
        for e in itertools.product(range(2), repeat=NL):
            s = 0
            for th in itertools.product(*[range(d[p]) for p in PAIRS]):
                thd = dict(zip(PAIRS, th)); pr = 1
                for g in range(3): pr &= int(W[(g, tuple(e[i] for i in gl[g]), tuple(thd[p] for p in PAIRS if g in p))] in pos)
                s ^= pr
            T[e] = s
        Ts.append((k, T))
    return Ts
def run(terms, tlim):
    E, tv = encode(terms); t0 = time.time()
    with Solver(name='glucose4', bootstrap_with=E.cl) as s:
        tm = threading.Timer(tlim, s.interrupt); tm.start(); ok = s.solve_limited(expect_interrupt=True); tm.cancel()
        if ok:
            Ts = rebuild(tv, s.get_model()); tot = sum(T for _, T in Ts) % 2
            assert (tot.reshape(-1) == target).all()
            return 'SAT (verified)', Ts, time.time() - t0
        return ('UNSAT' if ok is False else 'timeout'), None, time.time() - t0
def W(d): return d[(0, 1)] * d[(0, 2)] * d[(1, 2)]
if __name__ == "__main__":
    tlim = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    B = lambda a, b, c: {(0, 1): a, (0, 2): b, (1, 2): c}
    profiles = [
        ('sanity: P(x)F(x)F + B(x)F(x)F, S=48', [(0, B(2, 8, 2)), (1, B(1, 4, 4))]),
        ('S=32 m0(2,2,4)+m1(2,2,4)', [(0, B(2, 2, 4)), (1, B(2, 2, 4))]),
        ('S=32 m0(4,2,2)+m1(2,4,2)', [(0, B(4, 2, 2)), (1, B(2, 4, 2))]),
        ('S=32 m0(2,4,2)+m1(4,2,2)', [(0, B(2, 4, 2)), (1, B(4, 2, 2))]),
        ('S=32 m0(2,2,4)+m2(2,2,4)', [(0, B(2, 2, 4)), (2, B(2, 2, 4))]),
        ('S=24 m0(2,2,2)+m1(2,2,4)', [(0, B(2, 2, 2)), (1, B(2, 2, 4))]),
        ('S=24 m0(2,2,4)+m1(2,2,2)', [(0, B(2, 2, 4)), (1, B(2, 2, 2))]),
        ('S=24 m0(2,2,2)+m1(2,2,2)+m2(2,2,2)', [(0, B(2, 2, 2)), (1, B(2, 2, 2)), (2, B(2, 2, 2))]),
        ('S=40 m0(2,2,4)+m1(2,2,4)+m2(2,2,2)', [(0, B(2, 2, 4)), (1, B(2, 2, 4)), (2, B(2, 2, 2))]),
        ('S=40 m0(2,2,4)+m1(2,2,4)+m1(2,2,2)', [(0, B(2, 2, 4)), (1, B(2, 2, 4)), (1, B(2, 2, 2))]),
    ]
    for name, terms in profiles:
        st, Ts, dt = run(terms, tlim)
        S = sum(W(d) for _, d in terms)
        extra = ''
        if Ts: extra = ' c_flat of found terms: ' + str([(k, c_flat(cfg, T, cfg['merges'][k])) for k, T in Ts])
        print(f"{name}: S={S} -> {st} ({dt:.1f}s){extra}", flush=True)
