#!/usr/bin/env python3
"""Proof-producing SAT run for "no XOR-AND circuit with k=6 AND gates for 2x2 MM over F2".

Cubes: (first-gate orbit representative from plane_orbits.txt) x (set H of 2 gate positions that
are the only gates allowed outside A+T+span(earlier gates of H)); 72 x 15 = 1080 CNFs.
For each cube: generate CNF (gen_cnf.py), solve with CaDiCaL writing an LRAT proof, check the
proof with lrat-check, record sha256/size of CNF and proof, delete both.  Resumable.

usage: run_sat.py <cadical> <lrat-check> [workers] [k]
Results: out/sat_k<k>/results.tsv
"""
import hashlib, itertools, os, subprocess, sys, time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
CAD, CHK = sys.argv[1], sys.argv[2]
WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 3
K = int(sys.argv[4]) if len(sys.argv) > 4 else 6
OUT = os.path.join(HERE, "out", f"sat_k{K}")
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
    tag = f"r{r}_h{H[0]}{H[1]}"
    cnf, prf, sol = (os.path.join(OUT, tag + e) for e in (".cnf", ".lrat", ".out"))
    hs = ",".join(map(str, H))
    with open(cnf, "w") as f:
        subprocess.run([sys.executable, os.path.join(HERE, "gen_cnf.py"), "mm222", str(K),
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
            subprocess.run([sys.executable, os.path.join(HERE, "gen_cnf.py"), "mm222", str(K), "--root", f"{a},{b}",
                            "--helpers", hs, "--decode", sol], stdout=f, check=True)
        line += "\tSAT-CIRCUIT " + circ
    else:
        for p in (cnf, prf, sol):
            if os.path.exists(p):
                os.remove(p)
    return line


if __name__ == "__main__":
    roots = [tuple(map(int, l.split()[:2])) for l in open(os.path.join(HERE, "plane_orbits.txt"))]
    done = set()
    if os.path.exists(RES):
        for l in open(RES):
            w = l.split("\t")
            if w[0] != "root" and w[5] in ("VERIFIED",):
                done.add((int(w[0]), w[3]))
    else:
        with open(RES, "w") as f:
            f.write("root\ta\tb\thelpers\tverdict\tproof\tsolve_s\tcheck_s\tcnf_bytes\tcnf_sha256\tlrat_bytes\tlrat_sha256\n")
    jobs = [(r, a, b, H) for r, (a, b) in enumerate(roots) for H in itertools.combinations(range(K), 2)
            if (r, ",".join(map(str, H))) not in done]
    print(f"{len(jobs)} cubes to run", flush=True)
    with Pool(WORKERS) as pool, open(RES, "a") as f:
        for line in pool.imap_unordered(job, jobs):
            f.write(line + "\n")
            f.flush()
            print(line[:120], flush=True)
            if "SATISFIABLE" in line.split("\t")[4] and "UNSAT" not in line.split("\t")[4]:
                print("!!! SAT cube found:", line, flush=True)
