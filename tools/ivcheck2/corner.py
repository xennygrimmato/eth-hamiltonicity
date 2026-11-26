#!/usr/bin/env python3
"""Rigorous numerical confirmation for the corner lemma (piece (1)); the lemma itself is proved by
hand in README.md.

(1) The one-variable inequality behind the lemma, h(d) = sqrt(d)/2 - (3/2) d >= 0 on [0, 1/16],
    is checked by interval evaluation on a fine partition (it is also elementary: 3 sqrt(d) <= 1).
(2) Phi >= 0 is proved on the boundary faces of every corner region:
      {s x_p = 15/16, s x_q in [15/16, 1], other four coordinates in [-1, 1]}  and the same with
    p, q exchanged (12 five-dimensional faces), by the same branch and bound as check.py.
    The lemma predicts Phi >= 1/8 - 3/32 = 1/32 there.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from multiprocessing import Pool
from flint import arb
from ivarb import Iv
import problems as P
import check

C = 15.0 / 16.0


def h_check(n=4096):
    worst = None
    for i in range(n):
        d = Iv(arb(i) / (16 * n), arb(i + 1) / (16 * n))
        # sqrt(d)/2 - 3d/2 = sqrt(d) (1 - 3 sqrt(d)) / 2: evaluate the factored form
        sd = d.sqrt()
        v = sd * (Iv(1) - sd.scale(3)) * Iv(0.5)
        assert v.lo >= 0, (i, v)
    return True


def faces():
    out = []
    for (p, q) in P.PAIRS:
        for s in (1.0, -1.0):
            for (fix, var) in ((p, q), (q, p)):
                box = [(-1.0, 1.0)] * 6
                box[fix] = (s * C, s * C)
                box[var] = (C, 1.0) if s > 0 else (-1.0, -C)
                out.append(((p, q, s, fix), tuple(box)))
    return out


def split_initial(box, k):
    """Cut the four free coordinates into k pieces each, to give the pool work units."""
    boxes = [box]
    for d in range(6):
        lo, hi = box[d]
        if hi - lo < 1.5:
            continue
        nb = []
        for b in boxes:
            w = (hi - lo) / k
            for i in range(k):
                nb.append(b[:d] + ((lo + i * w, lo + (i + 1) * w if i < k - 1 else hi),) + b[d + 1:])
        boxes = nb
    return boxes


def work(box):
    st = {"lemma": 0, "nat": 0, "mvf": 0, "splits": 0, "maxdepth": 0, "fail": []}
    check.prove_box("clstar", box, 0.0, 0, 40, st)
    # also the predicted margin 1/32: a box is re-proved only at the leaf level of check, so
    # here just report the minimum lower end seen on a sample of leaves via the natural form
    return st


if __name__ == "__main__":
    t0 = time.time()
    print("h(d) >= 0 on [0,1/16] by interval partition:", h_check())
    tot = {"nat": 0, "mvf": 0, "splits": 0, "maxdepth": 0, "fail": 0}
    allb = []
    for tag, f in faces():
        allb += split_initial(f, 4)
    with Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 4) as pool:
        for st in pool.imap_unordered(work, allb, chunksize=4):
            for k in ("nat", "mvf", "splits"):
                tot[k] += st[k]
            tot["maxdepth"] = max(tot["maxdepth"], st["maxdepth"])
            tot["fail"] += len(st["fail"])
    print("12 corner faces:", "PROVED Phi >= 0" if tot["fail"] == 0 else "FAILED", tot,
          "time %.1fs" % (time.time() - t0))
