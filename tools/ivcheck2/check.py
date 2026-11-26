#!/usr/bin/env python3
"""Independent checker: re-proves the inequality on every leaf box of an ivcert certificate.

usage: check.py [--jobs N] [--max-extra-depth D] [--json OUT] CERT...

For each certificate: rebuild the leaf boxes from the split tree (certparse), check coverage,
check that excluded (X) leaves lie in the corner regions or the central cube (clstar only),
then for every other leaf prove f >= bound on the box by, in order:
  lemma  - the box lies in the origin region proved by originlemma (hull3, clnear only);
  nat    - natural interval extension (ivarb endpoint arithmetic on Arb);
  mvf    - mean-value form with a hand-derived interval gradient;
  bisect - otherwise the box is bisected (widest coordinate) and each piece is retried, up to
           --max-extra-depth extra levels; failures are reported with the box.
The prover's per-leaf tags and data are ignored (except X).
"""
import argparse, json, os, sys, time
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb
import certparse
import problems as P

R_LEMMA = 0.125  # origin-region radius proved by originlemma (see LEMMA_PARAMS)
K2_LEMMA_PARAMS = (0.0625, 8, 3)  # (r, Hessian sub-boxes per axis, L sub-boxes per axis)
LEMMA_PARAMS = {"hull3": (R_LEMMA, 32), "clnear": (R_LEMMA, 16, 4)}
CORNER = 15.0 / 16.0
RHO = 0.5


def kind_of(problem):
    if problem == "hull3":
        return "hull3"
    if problem.startswith("clnear:"):
        return "clnear"
    if problem.startswith("clstar:"):
        return "clstar"
    if problem.startswith("k2far:") or problem.startswith("k2near:"):
        return "k2"
    raise ValueError(problem)


# (natural form, mean-value form, certificate bound c); the forms already return f - c,
# so a box is closed when the returned lower end is >= 0.
FUNCS = {
    "hull3": (P.hull3_nat, P.hull3_mvf, 3.0),
    "clnear": (P.clnear_nat, P.clnear_mvf, 0.0),
    "clstar": (P.clstar_nat, P.clstar_mvf, 0.0),
}


_K2 = {}
K2_LEMMA = {}  # (lam, eta) -> radius r of the proved origin region in (a, e) coordinates
K2_SHIFT = 0.0  # mutation tests only


def k2spec(problem):
    if problem not in _K2:
        sp_ = P.K2Spec(problem)
        sp_.shift = K2_SHIFT
        _K2[problem] = sp_
    return _K2[problem]


def k2_lemma_box(spec, box):
    r = K2_LEMMA.get((spec.lam_pq, spec.eta_pq))
    return spec.near and r is not None and spec.shift == 0.0 and spec.bound <= 0.0 and spec.ae_box_in(box, r)


def in_lemma_region(kind, box):
    if kind not in ("hull3", "clnear"):
        return False
    return all(-R_LEMMA <= lo and hi <= R_LEMMA for lo, hi in box)


def excluded_ok(box):
    """X leaf of clstar: inside the central cube [-rho, rho]^6 or inside a corner region
    {s x_p >= 15/16, s x_q >= 15/16} for a pair (p, q).  Exact float comparisons."""
    if all(-RHO <= lo and hi <= RHO for lo, hi in box):
        return "central"
    for (p, q) in P.PAIRS:
        if box[p][0] >= CORNER and box[q][0] >= CORNER:
            return "corner+%d%d" % (p, q)
        if box[p][1] <= -CORNER and box[q][1] <= -CORNER:
            return "corner-%d%d" % (p, q)
    return None


def prove_box(kind, box, bound, depth, maxd, stats, problem=None):
    if kind == "k2":
        spec = k2spec(problem)
        if spec.misses(box):
            stats["outside"] += 1
            return True
        if k2_lemma_box(spec, box):
            stats["lemma"] += 1
            return True
        nat, mvf = spec.nat, spec.mvf
    else:
        nat, mvf, _ = FUNCS[kind]
    if kind != "k2" and in_lemma_region(kind, box):
        stats["lemma"] += 1
        return True
    r = nat(box)
    if r.lo.is_finite() and r.lo >= 0:
        stats["nat"] += 1
        return True
    r = mvf(box)
    if r is not None and r.lo.is_finite() and r.lo >= 0:
        stats["mvf"] += 1
        return True
    if depth >= maxd:
        stats["fail"].append(box)
        return False
    d = max(range(len(box)), key=lambda i: box[i][1] - box[i][0])
    lo, hi = box[d]
    m = lo + 0.5 * (hi - lo)
    assert lo < m < hi
    stats["splits"] += 1
    stats["maxdepth"] = max(stats["maxdepth"], depth + 1)
    a = prove_box(kind, box[:d] + ((lo, m),) + box[d + 1:], bound, depth + 1, maxd, stats, problem)
    b = prove_box(kind, box[:d] + ((m, hi),) + box[d + 1:], bound, depth + 1, maxd, stats, problem)
    return a and b


def work(args):
    kind, bound, maxd, chunk, problem, extra = args
    global K2_SHIFT
    K2_SHIFT = extra["shift"]
    K2_LEMMA.update(extra["lemma"])
    stats = {"lemma": 0, "nat": 0, "mvf": 0, "outside": 0, "splits": 0, "maxdepth": 0, "fail": [],
             "leaves_bisected": 0, "leaf_methods": {"lemma": 0, "nat": 0, "mvf": 0, "outside": 0, "bisect": 0}}
    for idx, box in chunk:
        before = stats["splits"]
        sub = {"lemma": stats["lemma"], "nat": stats["nat"], "mvf": stats["mvf"], "outside": stats["outside"]}
        ok = prove_box(kind, box, bound, 0, maxd, stats, problem)
        if stats["splits"] > before:
            stats["leaves_bisected"] += 1
            stats["leaf_methods"]["bisect"] += 1
        else:
            for k in ("lemma", "nat", "mvf", "outside"):
                if stats[k] > sub[k]:
                    stats["leaf_methods"][k] += 1
        if not ok:
            stats.setdefault("failed_leaves", []).append(idx)
    return stats


def check_cert(path, jobs, maxd):
    t0 = time.time()
    c = certparse.Cert(path)
    kind = kind_of(c.problem)
    if kind == "k2":
        bound = k2spec(c.problem).bound
    else:
        _, _, bound = FUNCS[kind]
    assert c.bound == bound, "certificate bound differs from the stated inequality"
    cov = c.coverage_report()
    res = {"cert": os.path.basename(path), "problem": c.problem, "dim": c.dim,
           "domain": c.domain, "coverage": cov}
    problems_found = []
    if cov["declared"] != cov["leaves"]:
        problems_found.append("leaf count mismatch")
    if not cov["volume_equal"]:
        problems_found.append("volume mismatch")
    if cov["tags"].get("P") or cov["tags"].get("F"):
        problems_found.append("certificate contains P or F leaves")
    # domain must be the stated one
    if kind == "clstar":
        dom_ok = c.domain == [(-1.0, 1.0)] * 6
    elif kind == "hull3":
        hp = arb.pi() / 2
        dom_ok = all(lo == -hi and arb(hi) >= hp for lo, hi in c.domain) and len(c.domain) == 3
    elif kind == "k2":
        spec = k2spec(c.problem)
        if spec.near:
            r = spec.rho
            assert 0 < r <= 0.5
            want = [(-r, r)] * 3 + [(0.0, spec.T)] * 3
            dom_ok = c.domain == want
        else:
            dom_ok = c.domain == [(-1.0, 1.0)] * 6
    else:
        s = c.problem.split("s=")[1]
        want = [(-RHO, RHO)] * 3 + [((0.0, RHO) if ch == "+" else (-RHO, 0.0)) for ch in s]
        dom_ok = c.domain == want
    res["domain_ok"] = bool(dom_ok)
    if not dom_ok:
        problems_found.append("domain is not the stated one")
    todo = []
    excl = {}
    for i, (tag, box) in enumerate(c.leaves):
        if tag == "X" and kind == "k2":
            spec = k2spec(c.problem)
            r = spec.rho
            if spec.misses(box):
                excl["outside"] = excl.get("outside", 0) + 1
            elif (not spec.near) and r > 0 and all(-r <= lo and hi <= r for lo, hi in box):
                excl["central"] = excl.get("central", 0) + 1
            else:
                excl["X_reproved"] = excl.get("X_reproved", 0) + 1
                todo.append((i, box))
            continue
        if tag == "X":
            where = excluded_ok(box) if kind == "clstar" else None
            if where is None:
                problems_found.append("X leaf %d not inside an excluded region: %r" % (i, box))
            else:
                key = where if where == "central" else "corner"
                excl[key] = excl.get(key, 0) + 1
            continue
        todo.append((i, box))
    res["excluded"] = excl
    t1 = time.time()
    n = len(todo)
    nchunks = max(1, min(4 * jobs * 8, n // 200 + 1))
    chunks = [todo[k::nchunks] for k in range(nchunks)]
    tot = {"lemma": 0, "nat": 0, "mvf": 0, "outside": 0, "splits": 0, "maxdepth": 0, "fail": [],
           "leaves_bisected": 0, "leaf_methods": {"lemma": 0, "nat": 0, "mvf": 0, "outside": 0, "bisect": 0},
           "failed_leaves": []}
    extra = {"shift": K2_SHIFT, "lemma": dict(K2_LEMMA)}
    with Pool(jobs) as pool:
        for st in pool.imap_unordered(work, [(kind, bound, maxd, ch, c.problem, extra) for ch in chunks]):
            for k in ("lemma", "nat", "mvf", "outside", "splits", "leaves_bisected"):
                tot[k] += st[k]
            tot["maxdepth"] = max(tot["maxdepth"], st["maxdepth"])
            tot["fail"] += st["fail"]
            tot["failed_leaves"] += st.get("failed_leaves", [])
            for k in tot["leaf_methods"]:
                tot["leaf_methods"][k] += st["leaf_methods"][k]
    res["checked_leaves"] = n
    res["leaf_methods"] = tot["leaf_methods"]
    res["closed_pieces"] = {k: tot[k] for k in ("lemma", "nat", "mvf", "outside")}
    res["extra_splits"] = tot["splits"]
    res["max_extra_depth"] = tot["maxdepth"]
    res["failed_leaves"] = [{"index": i, "box": c.leaves[i][1], "tag": c.leaves[i][0]}
                            for i in sorted(tot["failed_leaves"])]
    res["failed_pieces"] = tot["fail"][:50]
    if tot["failed_leaves"]:
        problems_found.append("%d leaves not closed" % len(tot["failed_leaves"]))
    res["problems"] = problems_found
    res["verdict"] = "VERIFIED" if not problems_found else "NOT VERIFIED"
    res["time_parse_s"] = round(t1 - t0, 2)
    res["time_bounds_s"] = round(time.time() - t1, 2)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certs", nargs="+")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--max-extra-depth", type=int, default=24)
    ap.add_argument("--json")
    ap.add_argument("--skip-lemma", action="store_true", help="(debug) do not re-prove the origin lemma")
    ap.add_argument("--shift", type=float, default=0.0,
                    help="(mutation test, k2 only) prove Br' - SHIFT >= bound; disables the origin lemma")
    a = ap.parse_args()
    global K2_SHIFT
    K2_SHIFT = a.shift
    out = {"lemma": {}, "certs": []}
    kinds = set()
    k2near_params = set()
    for p in a.certs:
        with open(p) as f:
            for ln in f:
                if ln.startswith("problem "):
                    kinds.add(kind_of(ln.split()[1]))
                    if ln.split()[1].startswith("k2near:"):
                        sp_ = P.K2Spec(ln.split()[1])
                        k2near_params.add((sp_.lam_pq, sp_.eta_pq))
                    break
    if not a.skip_lemma:
        import originlemma as L
        if "hull3" in kinds:
            ok, info = L.prove_hull3(*LEMMA_PARAMS["hull3"])
            out["lemma"]["hull3"] = {"ok": ok, **info}
            print("origin lemma hull3:", ok, info, flush=True)
            assert ok
        if "clnear" in kinds:
            ok, info = L.prove_clnear(*LEMMA_PARAMS["clnear"])
            out["lemma"]["clnear"] = {"ok": ok, **info}
            print("origin lemma clnear:", ok, info, flush=True)
            assert ok
        if a.shift == 0.0:
            for (lpq, epq) in sorted(k2near_params):
                ok, info = L.prove_k2near(lpq, epq, *K2_LEMMA_PARAMS)
                out["lemma"]["k2near %s %s" % (lpq, epq)] = {"ok": ok, **info}
                print("origin lemma k2near lam=%d/%d eta=%d/%d:" % (lpq + epq), ok, info, flush=True)
                if ok:
                    K2_LEMMA[(lpq, epq)] = K2_LEMMA_PARAMS[0]
    allok = True
    for p in a.certs:
        r = check_cert(p, a.jobs, a.max_extra_depth)
        out["certs"].append(r)
        allok &= r["verdict"] == "VERIFIED"
        print("%s  %s  %s" % (r["verdict"], r["cert"], r["problem"]))
        print("   coverage %s; excluded %s; checked %d leaves: per-leaf %s; pieces closed %s; "
              "extra splits %d (max extra depth %d); time %.1fs + %.1fs"
              % (r["coverage"], r["excluded"], r["checked_leaves"], r["leaf_methods"],
                 r["closed_pieces"], r["extra_splits"], r["max_extra_depth"],
                 r["time_parse_s"], r["time_bounds_s"]), flush=True)
        for pr in r["problems"]:
            print("   PROBLEM:", pr)
        for fl in r["failed_leaves"][:20]:
            print("   FAILED LEAF", fl)
    out["overall"] = "VERIFIED" if allok else "NOT VERIFIED"
    print("OVERALL:", out["overall"])
    if a.json:
        with open(a.json, "w") as f:
            json.dump(out, f, indent=1, default=str)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
