#!/usr/bin/env python3
"""Check that a set of verified k2 certificates (check.py --json outputs) covers the hard region F'_1
of a job completely (k2m notes §5.4):
  F'_1 = union over case in {c, l} and s in {+,-}^3 of the pieces P(case, s)   (trivially: every point
  has a sign pattern of (eps12, eps13, eps23) and either 2Q3 <= lam W3 or 2Q3 >= lam W3);
  every piece needs a VERIFIED k2far certificate; a k2far certificate with rho = R > 0 has X leaves in the
  central cube [-R,R]^6 (checked by check.py), which then needs the 8 k2near certificates with T^2 = R
  for the same (lam, eta) and case, all VERIFIED (they cover [-R,R]^6 in (a, e), which contains the image
  of the sigma-cube [-R,R]^6).
usage: k2cover.py LAM ETA JSON...      e.g. k2cover.py 9/10 6/5 results/k2_s910.json
"""
import itertools, json, sys
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import problems as P


def main():
    lam, eta = sys.argv[1], sys.argv[2]
    ok = {}
    for path in sys.argv[3:]:
        for r in json.load(open(path))["certs"]:
            ok[r["problem"]] = ok.get(r["problem"], False) or r["verdict"] == "VERIFIED"
    specs = {n: P.K2Spec(n) for n in ok if n.startswith("k2")}
    missing = []
    for case in "cl":
        for sg in itertools.product("+-", repeat=3):
            st = "".join(sg)
            far = [n for n, sp in specs.items() if not sp.near and ok[n] and sp.case == case and
                   "".join("+" if v > 0 else "-" for v in sp.s) == st and sp.lam_pq == P._rat(lam)
                   and sp.eta_pq == P._rat(eta) and sp.bound == 0.0]
            if not far:
                missing.append("far piece case=%s s=%s" % (case, st))
                continue
            good = False
            for n in far:
                R = specs[n].rho
                if R == 0:
                    good = True
                    break
                near = [m for m, sp in specs.items() if sp.near and ok[m] and sp.rho == R and sp.case == case
                        and sp.lam_pq == P._rat(lam) and sp.eta_pq == P._rat(eta) and sp.bound == 0.0]
                pats = {"".join("+" if v > 0 else "-" for v in specs[m].s) for m in near}
                if len(pats) == 8:
                    good = True
                    break
            if not good:
                missing.append("central cube of piece case=%s s=%s (k2near orthants)" % (case, st))
    if missing:
        print("COVER INCOMPLETE:", missing)
        return 1
    print("COVER OK: lam=%s eta=%s, all 16 pieces of F'_1 (and central cubes) verified" % (lam, eta))
    return 0


if __name__ == "__main__":
    sys.exit(main())
