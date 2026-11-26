#!/usr/bin/env python3
"""Check that results.tsv covers every (orbit root, helper pair) cube with a verified UNSAT proof."""
import itertools, os, sys

res = sys.argv[1]
K = 6
here = os.path.dirname(os.path.abspath(__file__))
roots = [tuple(map(int, l.split()[:2])) for l in open(os.path.join(here, "plane_orbits.txt"))]
need = {(r, a, b, ",".join(map(str, H))) for r, (a, b) in enumerate(roots) for H in itertools.combinations(range(K), 2)}
ok, bad, tsolve, tcheck, lrat = set(), [], 0.0, 0.0, 0
for l in open(res):
    w = l.rstrip("\n").split("\t")
    if w[0] == "root":
        continue
    key = (int(w[0]), int(w[1]), int(w[2]), w[3])
    if w[4] == "UNSATISFIABLE" and w[5] == "VERIFIED":
        ok.add(key)
        tsolve += float(w[6]); tcheck += float(w[7]); lrat += int(w[10])
    else:
        bad.append(l.strip())
missing = need - ok
print(f"cubes needed {len(need)}, verified UNSAT {len(ok & need)}, missing {len(missing)}, other lines {len(bad)}")
print(f"solver time {tsolve/3600:.2f} h, LRAT check time {tcheck/3600:.2f} h, total LRAT size {lrat/1e9:.2f} GB")
for b in bad:
    print("NOT UNSAT/VERIFIED:", b)
if missing or bad:
    sys.exit(1)
print("ALL CUBES UNSAT WITH CHECKED LRAT PROOFS")
