#!/usr/bin/env python3
"""Proof-producing SAT run for "no XOR-AND circuit with k AND gates for <1,2,3> over F2".

Same scheme as run_sat.py (which is for mm222 and is left unchanged), with three differences:
problem mm123, roots from plane_orbits_mm123.txt (orbits_mm123.py), and k - 3 helper positions
per cube (rem(A) = 3 for mm123), so there are 51 x C(k, k-3) cubes.
For each cube: generate CNF (gen_cnf.py), solve with CaDiCaL writing an LRAT proof, check the
proof with lrat-check, record sha256/size of CNF and proof, delete both.  Resumable.
At the end it checks that every cube is present, UNSAT and VERIFIED, and prints totals.

usage: run_sat_mm123.py <cadical> <lrat-check> [workers] [k]
Results: out/sat_mm123_k<k>/results.tsv
"""
import hashlib, itertools, os, subprocess, sys, time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
CAD, CHK = sys.argv[1], sys.argv[2]
WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 3
K = int(sys.argv[4]) if len(sys.argv) > 4 else 5
NH = K - 3  # number of helper positions
OUT = os.path.join(HERE, "out", f"sat_mm123_k{K}")
os.makedirs(OUT, exist_ok=True)
RES = os.path.join(OUT, "results.tsv")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def job(arg):
    r, a, b, H = arg
    hs = ",".join(map(str, H))
    tag = f"r{r}_h" + "".join(map(str, H))
    cnf, prf, sol = (os.path.join(OUT, tag + e) for e in (".cnf", ".lrat", ".out"))
    with open(cnf, "w") as f:
        subprocess.run([sys.executable, os.path.join(HERE, "gen_cnf.py"), "mm123", str(K),
                        "--root", f"{a},{b}", "--helpers", hs], stdout=f, check=True)
    t0 = time.time()
    with open(sol, "w") as f:
        subprocess.run([CAD, "-q", "--lrat=true", "--binary=false", cnf, prf], stdout=f)
    t1 = time.time()
    verdict = open(sol).readline().strip()
    chk = "-"
    if verdict == "s UNSATISFIABLE":
        out = subprocess.run([CHK, cnf, prf], capture_output=True, text=True).stdout
        chk = "VERIFIED" if "c VERIFIED" in out.splitlines() else "PROOF-FAILED"
    t2 = time.time()
    line = "\t".join(map(str, [r, a, b, hs, verdict.replace("s ", ""), chk, f"{t1-t0:.2f}", f"{t2-t1:.2f}",
                               os.path.getsize(cnf), sha(cnf), os.path.getsize(prf) if os.path.exists(prf) else 0,
                               sha(prf) if os.path.exists(prf) else "-"]))
    if verdict == "s SATISFIABLE":
        circ = os.path.join(OUT, tag + "_circuit.txt")
        with open(circ, "w") as f:
            subprocess.run([sys.executable, os.path.join(HERE, "gen_cnf.py"), "mm123", str(K), "--root", f"{a},{b}",
                            "--helpers", hs, "--decode", sol], stdout=f, check=True)
        line += "\tSAT-CIRCUIT " + circ
    else:
        for p in (cnf, prf, sol):
            if os.path.exists(p):
                os.remove(p)
    return line


def summarize(roots):
    need = {(r, a, b, ",".join(map(str, H))) for r, (a, b) in enumerate(roots)
            for H in itertools.combinations(range(K), NH)}
    ok, bad, ts, tc, lrat, mx = set(), [], 0.0, 0.0, 0, 0
    for l in open(RES):
        w = l.rstrip("\n").split("\t")
        if w[0] == "root":
            continue
        key = (int(w[0]), int(w[1]), int(w[2]), w[3])
        if w[4] == "UNSATISFIABLE" and w[5] == "VERIFIED":
            ok.add(key)
            ts += float(w[6]); tc += float(w[7]); lrat += int(w[10]); mx = max(mx, int(w[10]))
        else:
            bad.append(l.strip())
    missing = need - ok
    print(f"k={K}: cubes needed {len(need)}, verified UNSAT {len(ok & need)}, missing {len(missing)}, other lines {len(bad)}")
    print(f"solver time {ts:.1f} s, LRAT check time {tc:.1f} s, total LRAT {lrat/1e6:.1f} MB, largest {mx/1e6:.1f} MB")
    for b in bad:
        print("NOT UNSAT/VERIFIED:", b)
    if missing or bad:
        return False
    print("ALL CUBES UNSAT WITH CHECKED LRAT PROOFS")
    return True


if __name__ == "__main__":
    roots = [tuple(map(int, l.split()[:2])) for l in open(os.path.join(HERE, "plane_orbits_mm123.txt"))]
    done = set()
    if os.path.exists(RES):
        for l in open(RES):
            w = l.split("\t")
            if w[0] != "root" and w[5] == "VERIFIED":
                done.add((int(w[0]), w[3]))
    else:
        with open(RES, "w") as f:
            f.write("root\ta\tb\thelpers\tverdict\tproof\tsolve_s\tcheck_s\tcnf_bytes\tcnf_sha256\tlrat_bytes\tlrat_sha256\n")
    jobs = [(r, a, b, H) for r, (a, b) in enumerate(roots) for H in itertools.combinations(range(K), NH)
            if (r, ",".join(map(str, H))) not in done]
    print(f"{len(jobs)} cubes to run", flush=True)
    with Pool(WORKERS) as pool, open(RES, "a") as f:
        for line in pool.imap_unordered(job, jobs):
            f.write(line + "\n")
            f.flush()
            print(line[:120], flush=True)
            if line.split("\t")[4] == "SATISFIABLE":
                print("!!! SAT cube found:", line, flush=True)
    sys.exit(0 if summarize(roots) else 1)
