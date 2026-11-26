# Reproducing "The multiplicative complexity of 2 × 2 matrix multiplication over F₂ is seven"

This guide gives the exact commands that check every computational claim of the paper
(`main.tex` in this folder), starting from a fresh Linux machine. Each step says what it proves,
how long it took here, and what output to expect. A step that was not tested from scratch says so.

**Repository and version.** Everything below refers to the tag `mc222-v1` of
<https://github.com/xennygrimmato/math> (the repository was renamed from
`xennygrimmato/eth-hamiltonicity`; the old URL redirects). The tag points to the commit that the
paper cites. The code that the paper describes has not changed since commit `aef111e`; the tagged
commit adds this guide and two small checking scripts.

## 0. What is checked, and by what

| claim | checked by | trusted | time here | disk |
|---|---|---|---|---|
| MC(⟨2,2,2⟩) ≤ 7 (Strassen's circuit is correct) | `verify_circuit.py`, and Lean | Python, or the Lean kernel | seconds | — |
| MC(⟨2,2,2⟩) ≥ 7, method A: exact search over 72 orbit roots | `tools/mc222` (Rust) | the paper's lemmas N1–N3, `src/main.rs`, the Rust compiler | 8–9 min on 4 cores | < 1 GB |
| MC(⟨2,2,2⟩) ≥ 7, method B: 1080 SAT cubes, every LRAT proof checked | `gen_cnf.py`, CaDiCaL 2.1.3, `lrat-check` | lemmas N1–N3 and H, `gen_cnf.py`, `orbits.py`, `lrat-check.c`; **not** CaDiCaL | about 10 min on 3 workers | ≈ 0.2 GB at a time (proofs are deleted after checking) |
| MC(⟨2,2,2⟩) = 7 in Lean (`MC222.mc_eq_seven : MC = 7`) | `research/mm/lean-mc222` | Lean kernel + Lean compiler and runtime (365 compiled Boolean evaluations) | 75 min on 4 cores (loaded machine) | ≈ 25 GB |
| MC(⟨1,2,3⟩) = 6 (Theorem 1.2; not in Lean) | `tools/mc222`, both methods | as for methods A and B | 8 min | < 1 GB |

The validation cases of the paper's Table 2 (problems with known multiplicative complexity) run
first, inside `run_all.sh`. All of §2 and §3 together took 28 minutes from a fresh clone (§6).

## 1. Requirements

Tested on Ubuntu 24.04 (x86-64, 4 cores, 15 GB RAM).

* `git`, `make`, a C and C++ compiler (tested: gcc 13.3), `curl`, `sha256sum`.
* Rust with `cargo` (tested: 1.97). Install with `curl https://sh.rustup.rs -sSf | sh -s -- -y`
  if needed. The Rust program has no dependencies outside the standard library.
* Python 3.8 or later (tested: 3.13). Only the standard library is used.
* For the Lean part only: about 25 GB of free disk and 4 GB of RAM (about 1 GB per parallel Lean
  process). `elan` installs the Lean toolchain (§5).
* Network access to github.com (to clone the repository, CaDiCaL and drat-trim) and, for Lean,
  to the Mathlib cache.

```
git clone https://github.com/xennygrimmato/math.git mc222-repro
cd mc222-repro
git checkout mc222-v1
```

## 2. Methods A and B, and the validation cases: one command

```
cd tools/mc222
./run_all.sh "$PWD/ext"
```

`run_all.sh` does the following, in this order:

1. Clones CaDiCaL at tag `rel-2.1.3` and drat-trim at commit `2e3b2dc0ecf9…`, and builds both
   in `ext/`. Do not substitute the CaDiCaL development head: version 3.1.0 printed partial
   models that the decoder misread.
2. Builds the Rust search (`cargo build --release`).
3. Runs the validation cases with the exact search, re-checking every circuit found with
   `verify_circuit.py`, which evaluates the circuit on all inputs against its own definition of
   the targets.
4. Runs the same validation cases through the SAT encoding, decoding every satisfying assignment
   into a circuit and re-checking it.
5. Recomputes the 72 first-gate orbit representatives in Python (independently of the Rust code).
6. Runs the exact search for k = 6 over the 72 orbit roots (method A).
7. Runs the 1080 SAT cubes for k = 6, writing an LRAT proof for each and checking it with
   `lrat-check` (method B); then `summarize_sat.py` checks that all cubes are present, UNSAT and
   verified.

**Expected output (abridged).** Each validation case prints one line, and every circuit found
prints `OK: …`. The decisive lines are:

```
OK: out/circuit_mm222_7_p2.txt: mm222, 7 AND gates, all 256 inputs, 4 outputs correct
72 orbits; sizes [4, 6, 6, 9, …, 432]
# SUMMARY problem mm222 k=6 roots done 72/72 found=false states=3547604 wall=…
# RESULT: no circuit with <= 6 AND gates for roots 0..72
cubes needed 1080, verified UNSAT 1080, missing 0, other lines 0
ALL CUBES UNSAT WITH CHECKED LRAT PROOFS
```

The number of search states (3 547 604) is deterministic for the committed code; the wall time
is not.

**Compare with the recorded run.** The recorded per-cube table, with the size and sha256 of every
CNF and every LRAT proof, is `results/sat_k6_results.tsv`. CaDiCaL is deterministic, so a fresh
run reproduces the proofs byte for byte:

```
python3 compare_results.py results/sat_k6_results.tsv out/sat_k6/results.tsv
```

Expected: `ALL RECORDED CUBES REPRODUCED (same verdicts, same CNF and LRAT sizes and sha256)`.
Identical hashes show that the run is deterministic. They are not an independent check: a
different encoding or a different checker would be.

**Measured here, from a fresh clone at the tagged code** (4 cores shared with other jobs):
see §6.

### 2.1 Check one cube by hand

This does not use `run_sat.py`. It regenerates the cube "first gate = orbit representative 0
(input masks 1, 2), helper gates {0, 3}", solves it, checks the proof, and compares hashes with
the recorded line.

```
cd tools/mc222
CAD=ext/cadical-2.1.3/build/cadical
CHK=ext/drat-trim/lrat-check
python3 gen_cnf.py mm222 6 --root 1,2 --helpers 0,3 > x.cnf
$CAD -q --lrat=true --binary=false x.cnf x.lrat > x.out; head -1 x.out    # s UNSATISFIABLE
$CHK x.cnf x.lrat | grep VERIFIED                                         # c VERIFIED
sha256sum x.cnf x.lrat
grep -P "^0\t1\t2\t0,3\t" results/sat_k6_results.tsv | cut -f10,12
```

Expected hashes: CNF `8561c7e2d615bb92…`, LRAT `3854bd00b6f7b4cb…`; both match the recorded line.

**Negative test of the checker.** Remove the last five lines of the proof:

```
head -n -5 x.lrat > bad.lrat; $CHK x.cnf bad.lrat | grep VERIFIED          # c NOT VERIFIED
rm -f x.cnf x.lrat x.out bad.lrat
```

Every other cube can be checked the same way: the four parameters are columns 1–4 of the table
(`root`, `a`, `b`, `helpers`), and `--root a,b --helpers h1,h2` selects the cube.

### 2.2 Strassen's circuit

```
python3 verify_circuit.py results/circuit_mm222_7_p2.txt
```

Expected: `OK: … mm222, 7 AND gates, all 256 inputs, 4 outputs correct`.

### 2.3 The exact search on its own

```
cargo build --release
target/release/mc222 mm222 6 --threads 4 > k6.log; tail -2 k6.log
target/release/mc222 mm222 5 --no-orbits | grep RESULT     # all 10795 first gates, k = 5
```

The recorded per-orbit log is `results/exact_k6_orbits.log`; the state count per orbit is
deterministic and can be compared line by line (the times differ).

## 3. The ⟨1,2,3⟩ result (Theorem 1.2)

Requires the CaDiCaL and drat-trim builds from §2.

```
cd tools/mc222
./run_mm123.sh "$PWD/ext"
python3 compare_results.py results/sat_mm123_k5_results.tsv out/sat_mm123_k5/results.tsv
python3 compare_results.py results/sat_mm123_k4_results.tsv out/sat_mm123_k4/results.tsv
```

Expected decisive lines: `same 51 representatives`; `# RESULT: no circuit with <= 5 AND gates`
for the exact search; a verified 6-AND circuit; all 510 (k = 5) and 204 (k = 4) cubes UNSAT with
verified proofs; and both comparisons reproduced. This result is not formalised in Lean.

## 4. What the lemmas are and where they are used

Both external methods rest on lemmas proved on paper (the paper's Section 4; also
`tools/mc222/README.md` §2): N1 (normal form of a gate), N2 (the rem lemma), N3 (the symmetry
group of order 432, checked by computer in both programs), and, for method B only, lemma H
(at most two helper gates). These are the hand-proved part of the trusted base of methods A and
B. The Lean proof does not use them: it proves its own reduction (§5).

## 5. The Lean proof

### 5.1 Install and build

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- -y --default-toolchain none
source "$HOME/.elan/env"
cd research/mm/lean-mc222          # from the repository root
lake exe cache get                 # downloads compiled Mathlib (v4.36.0); do not build Mathlib
lake build                         # builds the MC222 library: 18426 jobs
./check_axioms.sh
```

`lean-toolchain` pins `leanprover/lean4:v4.36.0` and `lakefile.toml` pins Mathlib `v4.36.0`, so
`elan` and `lake` fetch exactly those. If `lake build` starts compiling Mathlib files, the cache
step did not work: stop and rerun `lake exe cache get`.

**Time and space.** The 72 files `MC222/Cubes/R*.lean` hold 360 cube propositions, each
discharged by `bv_decide` (CaDiCaL inside Lean, with the LRAT certificate checked by Lean's
verified checker). On the 4-core machine used here, with other jobs running, a complete rebuild
of the library from source took 75 minutes. A single cube takes 11–22 s when run alone. The build
directory is 11 GB, of which 5.7 GB are the compiled cube files; the Mathlib packages take 7.3 GB.
Peak memory is about 1 GB per Lean process.

**Expected output of `./check_axioms.sh`:**

```
MC222.mc_eq_seven : MC222.MC = 7
'MC222.hasCircuit_seven' depends on axioms: [propext, Classical.choice, Quot.sound]
'MC222.mc_eq_seven' depends on axioms: [propext,
ok   statement: 1
ok   upper bound uses only standard axioms: 1
ok   sorryAx absent: 0
ok   standard axioms: 3
ok   compiled-evaluation axioms: 365
ok     of which cubes: 360
ok     of which native_decide: 2
ok   other axioms: 0
AXIOM CHECK PASSED
```

### 5.2 What the axioms mean

Lean 4.36 records each `bv_decide` and `native_decide` call as an auxiliary axiom of the form
"this compiled Boolean evaluation returned `true`", for example
`MC222.cube_0_1._native.bv_decide.ax_1_37`. There are 365 of them: 360 cubes, 3 `bv_decide`
lemmas and 2 `native_decide` checks. So the trusted base of the Lean proof is the Lean kernel
together with the Lean compiler and runtime, which carry out these evaluations. It is not the
kernel alone. A kernel-only proof would have to replay 5.7 GB of certificates by reduction and is
not realistic. The upper bound `hasCircuit_seven` (Strassen) uses only the three standard axioms.

The Python encoder, the external CaDiCaL runs, `lrat-check` and the paper's hand-proved lemmas
are outside this trusted base: `MC222/Final.lean` proves in Lean that any 6-gate circuit yields a
satisfying assignment of one of the 360 cube propositions.

### 5.3 What to read to check that the theorem says what the paper says

`MC222/Statement.lean` (about 50 lines) contains every definition the main theorem uses:
Boolean functions F₂⁸ → F₂ with pointwise operations, the spans S_j, circuits, "computes", and
`MC := sInf {k | HasCircuit k}`. `MC222/Main.lean` states `mc_eq_seven : MC = 7`. These two files
are the part a reader must check by eye; everything else is checked by Lean.

## 6. What was run for this guide, and where

All steps of §2, §2.1 and §3 were run from a fresh clone of the repository at the tagged code,
with CaDiCaL and drat-trim cloned and built from scratch by `run_all.sh`, on the machine described
in §1. The results are recorded below.

Run on 26 November 2026 from a fresh clone, with nothing reused from earlier runs:

| step | result | time (wall) |
|---|---|---|
| `run_all.sh`: build CaDiCaL rel-2.1.3 and lrat-check from fresh clones, build the Rust search | built | included below |
| validation cases, both methods (Table 2 of the paper) | every case as in Table 2; every circuit found re-checked `OK` | included below |
| Python orbit representatives | 72 orbits, sizes as recorded | included below |
| method A, k = 6 | `no circuit with <= 6 AND gates`, 3 547 604 states; the state count of each of the 72 orbits identical to `results/exact_k6_orbits.log` | 513 s |
| method B, k = 6 | 1080 of 1080 cubes UNSAT, every LRAT proof `VERIFIED`; 0.26 h solver CPU, 0.06 h check CPU, 5.41 GB of LRAT in total | — |
| `compare_results.py`, k = 6 | all 1080 recorded cubes reproduced: same verdicts, same sizes and sha256 of every CNF and LRAT proof | seconds |
| whole of `run_all.sh` | exit status 0 | 19 min 47 s |
| `run_mm123.sh` | 51 representatives identical in Rust and Python; method A `no circuit with <= 5 AND gates`, 2 829 011 states, per-orbit counts identical to the record; 6-AND circuit `OK`; 204 (k = 4) and 510 (k = 5) cubes UNSAT with verified proofs | 7 min 57 s |
| `compare_results.py`, ⟨1,2,3⟩ | k = 4 and k = 5 reproduced byte for byte | seconds |
| §2.1 by hand | CNF `8561c7e2…`, LRAT `3854bd00…`, `c VERIFIED`; truncated proof `c NOT VERIFIED` | seconds |
| §2.2 | `OK: … 7 AND gates, all 256 inputs, 4 outputs correct` | seconds |

The machine had 4 cores shared with other jobs. With three workers the proofs on disk take at most about
0.2 GB at a time (the largest single proof is 54 MB); `run_sat.py` deletes each one after checking it.

The Lean build of §5 was tested by deleting every build product of the MC222 library and running
`lake build` from source on the same machine (75 min, 18426 jobs, the axiom list above, no
`sorryAx`). The `elan` installation and `lake exe cache get` steps were run when the project was
set up and were not repeated from a fresh clone for this guide, because the machine did not have
the 25 GB of free disk that a second copy needs.

All runs were on one machine and one toolchain. They show that the computations are reproducible
there; they are not independent confirmations.
