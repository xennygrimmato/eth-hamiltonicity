"""[N] Two-apex instances near K_{2,3}(w), K_{2,4}(w) with perturbed capacities / demands (where flow < cut):
is min over books = min over (m-pod) x R (all hubs strictly inside the spine)?  Usage: python3 scan3.py [N]"""
import itertools, numpy as np, sys
from multiprocessing import Pool
from twoapex import TwoApex, flow_value, cut_value
def job(seed):
    rng = np.random.default_rng(1000 + seed)
    m = 3 if seed % 4 else 4
    spread = (0.15, 0.4, 0.8)[seed % 3]
    c1 = np.exp(spread*rng.normal(size=m)); c2 = np.exp(spread*rng.normal(size=m))
    r = {(i, j): float(np.exp(spread*rng.normal())) for i, j in itertools.combinations(range(m), 2)}
    w = float(np.exp(rng.uniform(np.log(0.3), np.log(3.0))))
    T = TwoApex(m, c1, c2, r, w)
    sup, dem = T.graphs()
    fl = flow_value(m+2, sup, dem); ct, X = cut_value(m+2, sup, dem)
    bk = T.minimise(False, 50, seed); pd = T.minimise(True, 50, seed+1)
    _, ends = T.ratio(bk[1], bk[2], False, True)
    return seed, m, spread, w, fl, bk[0], pd[0], ct, ends, bk[2]
if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    cnt = dict(total=0, distinct=0, bookltpod=0, cut=0)
    with Pool(4) as p:
        for seed, m, spread, w, fl, bk, pd, ct, ends, D in p.imap(job, range(N)):
            cnt['total'] += 1
            flag = ""
            if pd - bk > 1e-6: flag += " BOOK<POD"; cnt['bookltpod'] += 1
            if fl + 1e-6 < bk < ct - 1e-6: flag += " 3-distinct"; cnt['distinct'] += 1
            if abs(bk - ct) < 1e-6: cnt['cut'] += 1
            print(f"#{seed} m={m} spread={spread} w={w:.3f}: flow={fl:.5f} book={bk:.6f} pod={pd:.6f} cut={ct:.5f} ends={ends} D={D}{flag}", flush=True)
    print(cnt)
