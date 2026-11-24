# Greedy library growth over GF(2) factorisations of the 8x8 disjointness matrix.
# Objective: mean game value over the "ridge" (grid points where the current library is within 0.01 of its max).
import random, math, pickle, sys, numpy as np, time
from ovgame import profile_costs
n = 8
R = [[1 if (a & b) == 0 else 0 for b in range(n)] for a in range(n)]
cols = [sum(R[a][b] << a for a in range(n)) for b in range(n)]
def profile(U):
    r = [sum((u >> a) & 1 for u in U) for a in range(n)]
    dist = [99]*256; dist[0] = 0
    for u in U:
        nd = dist[:]
        for x in range(256):
            dx = dist[x]
            if dx < 99 and dx + 1 < nd[x ^ u]: nd[x ^ u] = dx + 1
        dist = nd
    return r, [dist[cb] for cb in cols]
alphas = np.linspace(0.02, 0.98, 49)
base = [([1, 1], [2, 1], 1), ([2, 1], [1, 1], 1), ([1, 2], [1, 2], 1)]
par2 = pickle.load(open("par_gf2_d2.pkl", "rb"))
base += [(list(r), list(c), 2) for r, c in par2] + [(list(c), list(r), 2) for r, c in par2]
LR = [profile_costs(r, c, d, alphas)[0] for r, c, d in base]; LC = [profile_costs(r, c, d, alphas)[1] for r, c, d in base]
th = np.linspace(0, 1, 301)[:, None]
allpairs = [(i, j) for i in range(len(alphas)) for j in range(len(alphas)) if alphas[i] + alphas[j] <= 1.0]
def values(LR, LC, pairs):
    Rm = np.array(LR); Cm = np.array(LC)
    return np.array([(th*Rm[None, :, i] + (1-th)*Cm[None, :, j]).min(axis=1).max() for i, j in pairs])
random.seed(int(sys.argv[1])); budget = float(sys.argv[2]); t0 = time.time()
rnd = 0
while time.time() - t0 < budget:
    v = values(LR, LC, allpairs); tau = v.max(); ridge = [p for p, x in zip(allpairs, v) if x > tau - 0.01]
    print("round", rnd, "library", len(LR), "tau* = %.5f" % tau, "ridge points", len(ridge), "t=%d" % (time.time()-t0)); sys.stdout.flush()
    Rr = np.array(LR); Cr = np.array(LC)
    baseV = values(LR, LC, ridge)
    def score(U):
        r, c = profile(U)
        if max(c) >= 99 or min(r) == 0: return 9, None
        a, b = profile_costs(r, c, 3, alphas); a2, b2 = profile_costs(c, r, 3, alphas)
        return values(LR + [a, a2], LC + [b, b2], ridge).mean(), (r, c)
    U = set(1 << a for a in range(n)); cur, prof = score(U); best = (cur, set(U), prof); steps = 700
    for it in range(steps):
        T = 0.004*(1 - it/steps) + 1e-5; V = set(U); mv = random.random()
        if mv < 0.35 or len(V) <= 8: V.add(random.randrange(1, 256))
        elif mv < 0.6: V.discard(random.choice(list(V)))
        else:
            u = random.choice(list(V)); V.discard(u); V.add((u ^ (1 << random.randrange(8))) or 1)
        s, p = score(V)
        if s <= cur or random.random() < math.exp((cur - s)/T):
            U, cur = V, s
            if s < best[0] - 1e-9: best = (s, set(V), p)
        if time.time() - t0 > budget: break
    print("   ridge mean %.5f -> %.5f with gadget" % (baseV.mean(), best[0]), sorted(best[1]), best[2]); sys.stdout.flush()
    if best[2] is None or best[0] > baseV.mean() - 1e-5: print("   no improving gadget found this round"); rnd += 1; continue
    r, c = best[2]
    for rr, cc in [(r, c), (c, r)]:
        a, b = profile_costs(rr, cc, 3, alphas); LR.append(a); LC.append(b)
    rnd += 1
v = values(LR, LC, allpairs); print("FINAL tau* = %.5f" % v.max())
