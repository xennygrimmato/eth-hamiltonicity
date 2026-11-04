"""engine2d: decorrelated decompositions of products of rectangles F=[x=v][y=u] (GF(2) SAT + exact ranks).

A configuration = rectangles placed on grid nodes (row, col).  Rectangle q on rows r<s, cols c<d has legs
x@(r,c), y@(r,d), u@(s,c), v@(s,d) and F_q = [x=v][y=u].  Grouping 'row' (classes = rows) or 'col'.
A term in grouping G is a network on the classes of G: bond dims d_P on class pairs P, local tensors W_i
(arbitrary, coupling all legs of class i).  Cost = log2 prod_P d_P ; rank-sum weight = prod_P d_P.
"""
import itertools, sys
sys.path.insert(0, '/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/pylib')

def make_config(rects, lam=1):
    """rects: list of ((r,s),(c,d)) with r<s, c<d.  Returns dict with legs, classes, target."""
    legs = []  # (name, node, bits)
    for q, ((r, s), (c, d)) in enumerate(rects):
        legs += [(f'x{q}', (r, c)), (f'y{q}', (r, d)), (f'u{q}', (s, c)), (f'v{q}', (s, d))]
    idx = {n: i for i, (n, _) in enumerate(legs)}
    rows = sorted({nd[0] for _, nd in legs}); cols = sorted({nd[1] for _, nd in legs})
    cls = {'row': [[i for i, (_, nd) in enumerate(legs) if nd[0] == r] for r in rows],
           'col': [[i for i, (_, nd) in enumerate(legs) if nd[1] == c] for c in cols]}
    pairs = {}
    for G in ('row', 'col'):  # class pairs carrying at least one crossing edge
        ps = set()
        for q, ((r, s), (c, d)) in enumerate(rects):
            key = (r, s) if G == 'row' else (c, d)
            names = rows if G == 'row' else cols
            ps.add((names.index(key[0]), names.index(key[1])))
        pairs[G] = sorted(ps)
    D = 2 ** lam
    def target(e):  # e: tuple of leg values in range(D)
        return int(all(e[idx[f'x{q}']] == e[idx[f'v{q}']] and e[idx[f'y{q}']] == e[idx[f'u{q}']]
                       for q in range(len(rects))))
    return dict(rects=rects, legs=legs, idx=idx, cls=cls, pairs=pairs, D=D, lam=lam, target=target)

class Enc:
    def __init__(self): self.n = 0; self.cl = []
    def var(self): self.n += 1; return self.n
    def AND(self, xs):
        if len(xs) == 1: return xs[0]
        z = self.var()
        for x in xs: self.cl.append([-z, x])
        self.cl.append([z] + [-x for x in xs]); return z
    def XOR_eq(self, xs, b):
        """xor of literals xs == b, via chain"""
        if not xs: 
            if b: self.cl.append([])
            return
        acc = xs[0]
        for x in xs[1:]:
            z = self.var()
            self.cl += [[-z, acc, x], [-z, -acc, -x], [z, -acc, x], [z, acc, -x]]
            acc = z
        self.cl.append([acc] if b else [-acc])

def encode(cfg, terms):
    """terms: list of (G, bonds) with bonds a dict pair->dim (pairs of cfg['pairs'][G], or extra pairs).
    Returns (Enc, decoder) for the GF(2) identity  sum_t term_t = target."""
    E = Enc(); D = cfg['D']; nl = len(cfg['legs'])
    tv = []  # per term: (G, bonds, Wvars dict (class, legvals, bondidx-tuple) -> var)
    for (G, bonds) in terms:
        classes = cfg['cls'][G]; plist = sorted(bonds)
        W = {}
        for ci, cl in enumerate(classes):
            inc = [p for p in plist if ci in p]
            for lv in itertools.product(range(D), repeat=len(cl)):
                for bi in itertools.product(*[range(bonds[p]) for p in inc]):
                    W[(ci, lv, bi)] = E.var()
        tv.append((G, bonds, plist, W))
    for e in itertools.product(range(D), repeat=nl):
        lits = []
        for (G, bonds, plist, W) in tv:
            classes = cfg['cls'][G]
            for th in itertools.product(*[range(bonds[p]) for p in plist]):
                thd = dict(zip(plist, th)); xs = []
                for ci, cl in enumerate(classes):
                    inc = [p for p in plist if ci in p]
                    xs.append(W[(ci, tuple(e[i] for i in cl), tuple(thd[p] for p in inc))])
                lits.append(E.AND(xs))
        E.XOR_eq(lits, cfg['target'](e))
    return E, tv

def evaluate(cfg, tv, model):
    """Rebuild the term tensors (dict e -> GF(2) value) from a SAT model."""
    pos = set(l for l in model if l > 0); D = cfg['D']; nl = len(cfg['legs']); out = []
    for (G, bonds, plist, W) in tv:
        classes = cfg['cls'][G]; T = {}
        for e in itertools.product(range(D), repeat=nl):
            s = 0
            for th in itertools.product(*[range(bonds[p]) for p in plist]):
                thd = dict(zip(plist, th)); prod = 1
                for ci, cl in enumerate(classes):
                    inc = [p for p in plist if ci in p]
                    prod &= int(W[(ci, tuple(e[i] for i in cl), tuple(thd[p] for p in inc))] in pos)
                s ^= prod
            T[e] = s
        out.append(T)
    return out

def rank_gf2(rows):
    """rows: list of int bitmasks"""
    basis = []; r = 0
    for v in rows:
        for b in basis: v = min(v, v ^ b)
        if v: basis.append(v); r += 1
    return r

def cut_rank_gf2(cfg, T, left):
    """GF(2) rank of tensor T (dict e->bit) across leg set `left` | rest."""
    D = cfg['D']; nl = len(cfg['legs']); right = [i for i in range(nl) if i not in left]
    rowsd = {}
    rc = {c: k for k, c in enumerate(itertools.product(range(D), repeat=len(right)))}
    for e, val in T.items():
        if val:
            key = tuple(e[i] for i in left); rowsd[key] = rowsd.get(key, 0) | (1 << rc[tuple(e[i] for i in right)])
    return rank_gf2(list(rowsd.values()))
