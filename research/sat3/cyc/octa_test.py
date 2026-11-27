import numpy as np, itertools, sys
def build(p, al, be, ga):
    pts = []; M = []
    lines = [('R', b) for b in be] + [('C', a) for a in al] + [('D', g) for g in ga]
    def on(pt):
        a, b = pt
        return [i for i, (t, v) in enumerate(lines) if (t == 'R' and b == v) or (t == 'C' and a == v) or (t == 'D' and (a-b) % p == v)]
    cand = set()
    for a in al:
        for b in be: cand.add((a, b))
    for b in be:
        for g in ga: cand.add(((b+g) % p, b))
    for a in al:
        for g in ga: cand.add((a, (a-g) % p))
    pts = sorted(cand)
    if len(pts) != 12 or any(len(on(pt)) != 2 for pt in pts): return None
    M = np.zeros((6, 12))
    for j, pt in enumerate(pts):
        i1, i2 = on(pt); M[i1, j] = 1; M[i2, j] = -1
    return pts, M
def check(p, al, be, ga, verbose=False):
    r = build(p, al, be, ga)
    if r is None: return None
    pts, M = r
    z = np.exp(2j*np.pi/p)
    bad = []
    minsv = 1e9
    for t1 in range(p):
        for t2 in range(p):
            if t1 == 0 or t2 == 0 or (t1+t2) % p == 0: continue
            D = np.array([z**((a*t1 + b*t2) % p) for a, b in pts])
            S = np.vstack([M, M*D[None, :]])
            sv = np.linalg.svd(S, compute_uv=False)
            rk = int((sv > 1e-9).sum()); minsv = min(minsv, sv[9])
            if rk != 10: bad.append((t1, t2, rk))
    return bad, minsv
if __name__ == "__main__":
    for p in [3, 4, 5, 7, 8, 9, 11, 13]:
        best = None; nconf = 0
        for a2, b2, g1, g2 in itertools.product(range(p), repeat=4):
            if a2 == 0 or b2 == 0 or g1 >= g2: continue
            r = check(p, (0, a2), (0, b2), (g1, g2))
            if r is None: continue
            nconf += 1
            bad, ms = r
            if best is None or len(bad) < len(best[0]) or (len(bad) == len(best[0]) and ms > best[1]):
                best = (bad, ms, (a2, b2, g1, g2))
            if p > 9 and len(bad) == 0 and nconf > 50: break
        print("p =", p, "configs", nconf, "best: #bad t =", None if best is None else len(best[0]),
              "min 10th s.v. %.4f" % best[1] if best else "", "params", best[2] if best else None,
              "bad:", best[0][:6] if best else None)
        sys.stdout.flush()
