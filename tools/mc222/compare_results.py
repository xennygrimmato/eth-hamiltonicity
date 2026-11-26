#!/usr/bin/env python3
"""Compare a fresh SAT results table with the recorded one in results/.

Usage: python3 compare_results.py results/sat_k6_results.tsv out/sat_k6/results.tsv

Lines are matched on (root, a, b, helpers). For every recorded cube the fresh table must have
the same verdict and proof status, and the same size and sha256 of the CNF and of the LRAT proof.
Solve and check times are not compared. Exit status 0 means every recorded line was reproduced.
"""
import sys

COLS = ("verdict", "proof", "cnf_bytes", "cnf_sha256", "lrat_bytes", "lrat_sha256")


def load(path):
    rows = {}
    with open(path) as fh:
        header = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            w = dict(zip(header, line.rstrip("\n").split("\t")))
            rows[(w["root"], w["a"], w["b"], w["helpers"])] = w
    return rows


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    old, new = load(sys.argv[1]), load(sys.argv[2])
    missing = [k for k in old if k not in new]
    differ = [k for k in old if k in new and any(old[k][c] != new[k][c] for c in COLS)]
    extra = [k for k in new if k not in old]
    print(f"recorded cubes {len(old)}, fresh cubes {len(new)}, missing {len(missing)}, "
          f"different {len(differ)}, extra {len(extra)}")
    for k in differ[:10]:
        print("DIFFERENT:", k, {c: (old[k][c], new[k][c]) for c in COLS if old[k][c] != new[k][c]})
    for k in missing[:10]:
        print("MISSING:", k)
    if missing or differ:
        sys.exit(1)
    print("ALL RECORDED CUBES REPRODUCED (same verdicts, same CNF and LRAT sizes and sha256)")


if __name__ == "__main__":
    main()
