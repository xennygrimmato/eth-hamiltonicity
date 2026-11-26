"""[N] Random two-apex instances (m = 3, 4): is min over books always = min over (m-pod) x R ?
Also cross-check m = 3 against Toyoda's five-point criterion (tensorlab.min_ratio, families triangle+box)."""
import itertools, numpy as np, sys
from multiprocessing import Pool
from twoapex import TwoApex, flow_value, cut_value
def job(seed):
    rng = np.random.default_rng(seed)
    m = 3 if seed % 3 else 4
    c1 = rng.integers(1, 4, m); c2 = rng.integers(1, 4, m)
    r = {(i, j): int(rng.integers(0, 4)) for i, j in itertools.combinations(range(m), 2)}
    w = int(rng.integers(0, 4)); c0 = int(rng.integers(0, 2)) * int(rng.integers(0, 2))
    if sum(r.values()) + w == 0: return None
    T = TwoApex(m, c1, c2, r, w, c0)
    sup, dem = T.graphs()
    fl = flow_value(m+2, sup, dem); ct, X = cut_value(m+2, sup, dem)
    bk = T.minimise(False, 40, seed); pd = T.minimise(True, 40, seed+1)
    toy = None
    if m == 3:
        try:
            import tensorlab
            pr = list(itertools.combinations(range(5), 2))
            num = [float(sup.get(p, 0)) for p in pr]; den = [float(dem.get(p, 0)) for p in pr]
            sol = tensorlab.min_ratio(5, num, den, ["triangle", "box"], 60, seed, 1)
            toy = sol[0]["value"] if isinstance(sol[0], dict) and "value" in sol[0] else sol[0]
        except Exception as e:
            toy = repr(e)
    return seed, m, list(c1), list(c2), r, w, c0, fl, bk[0], pd[0], ct, toy
if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    with Pool(4) as p:
        for res in p.imap(job, range(1, N+1)):
            if res is None: continue
            seed, m, c1, c2, r, w, c0, fl, bk, pd, ct, toy = res
            flag = ""
            if pd - bk > 1e-6: flag += " BOOK<POD"
            if bk < ct - 1e-6 and bk > fl + 1e-6: flag += " 3-distinct"
            if isinstance(toy, float) and abs(toy - bk) > 1e-5: flag += " TOYODA-MISMATCH"
            print(f"#{seed} m={m} c1={c1} c2={c2} r={list(r.values())} w={w} c0={c0}: flow={fl:.5f} book={bk:.6f} pod={pd:.6f} cut={ct:.5f} toyoda={toy if not isinstance(toy,float) else round(toy,6)}{flag}", flush=True)
