"""Label LP in the product of two tripods T x T' (l2 product; a convex subset of C_4(2): block sum of two lines).
Tips of T sit over the centre of T': the spine of the book T x T' is the tripod T', which is singular at that point.
Flats: (ray i u ray j) x (ray k u ray l) = R^2, nine of them.  Question: does a non-flat spine set K in T'
give a better bound on delta(tips of T) than the flat one-dimensional spine (2 sqrt 2 = 2.82843)?"""
import itertools, math, random, sys, time
from gen_lp import solve
from label_lp import mean_width_planar, in_hull_planar
class P2:
    def __init__(s, i, r, k, t):
        if r < 1e-12: i, r = None, 0.0
        if t < 1e-12: k, t = None, 0.0
        s.i, s.r, s.k, s.t = i, r, k, t
def flats_of(pts):
    """list of (ri, rj, rk, rl) flats containing all points"""
    I = sorted({p.i for p in pts if p.i is not None}); K = sorted({p.k for p in pts if p.k is not None})
    if len(I) > 2 or len(K) > 2: return None
    return I, K
def coords(p, I, K):
    u = 0.0 if p.i is None else (p.r if p.i == I[0] else -p.r)
    v = 0.0 if p.k is None else (p.t if p.k == K[0] else -p.t)
    return (u, v)
def run(pts, target, hull=True, sense="max", lower=None):
    n = len(pts)
    def flatW(m):
        S = [pts[i] for i in range(n) if m >> i & 1]
        f = flats_of(S)
        if f is None: return None
        I, K = (f[0] or [0]), (f[1] or [0])
        return mean_width_planar([coords(p, I, K) for p in S])
    allflats = [(I, K) for I in itertools.combinations(range(3), 2) for K in itertools.combinations(range(3), 2)]
    def inflat(p, I, K): return (p.i is None or p.i in I) and (p.k is None or p.k in K)
    def closure(m):
        cl = m; ch = True
        while ch:
            ch = False
            for I, K in allflats:
                T = [i for i in range(n) if cl >> i & 1 and inflat(pts[i], I, K)]
                if len(T) < 2: continue
                C = [coords(pts[i], I, K) for i in T]
                for z in range(n):
                    if not cl >> z & 1 and inflat(pts[z], I, K) and in_hull_planar(coords(pts[z], I, K), C):
                        cl |= 1 << z; ch = True
        return cl
    v, res = solve(n, flatW, target, sense=sense, closure=closure if hull else None, lower=lower)
    return v
if __name__ == "__main__":
    a = 1.0
    tips = [P2(i, a, None, 0) for i in range(3)]
    t = 0b111
    def rep(aux, label, **kw):
        t0 = time.time(); v = run(tips + aux, t, **kw)
        print(f"{label:60s} n={3+len(aux):2d} max delta(tips) = {v:.5f}  [{time.time()-t0:.0f}s]", flush=True); return v
    H = 1 / (2 * math.sqrt(2))
    rep([P2(None, 0, 0, H), P2(None, 0, 1, H)], "K = two points of T' at radius H* on rays 0,1 (flat spine)")
    for Hh in (0.2, 0.3, H, 0.45):
        rep([P2(None, 0, k, Hh) for k in range(3)], f"K = three tips of T' at radius {Hh:.3f} (non-flat spine)")
    rep([P2(None, 0, k, H) for k in range(3)] + [P2(None, 0, None, 0)], "K = three tips of T' + centre")
    rep([P2(None, 0, k, Hh) for k in range(3) for Hh in (0.25, 0.6)], "K = tips of T' at radii 0.25 and 0.6")
    rep([P2(None, 0, k, 0.35) for k in range(3)] + [P2(i, 0.5, i, 0.4) for i in range(3)], "K = tips of T' + mixed (i,.5; i,.4)")
    rep([P2(None, 0, k, 0.35) for k in range(3)] + [P2(i, 1.0, (i + 1) % 3, 0.5) for i in range(3)], "K = tips of T' + mixed (i,1; i+1,.5)")
    random.seed(2); best = 9
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 20):
        aux = []
        for j in range(7):
            u = random.random()
            if u < 0.5: aux.append(P2(None, 0, random.randrange(3), random.uniform(0.1, 1.2)))
            else: aux.append(P2(random.randrange(3), random.uniform(0.1, 1.5), random.randrange(3), random.uniform(0.0, 1.2)))
        v = rep(aux, f"random #{trial}"); best = min(best, v)
    print("best random:", best, " flat one-dimensional spine: 2.82843; (8/3) = 2.66667")
