# CHECKS for main.tex (revision of 26 November 2026)

Build: `pdflatex`, `bibtex`, `pdflatex`, `pdflatex` from a clean directory. Result: **13 pages** (A4, 25 mm margins,
bibliography in footnotesize). `main.log`: no errors, no undefined references or citations, no overfull boxes;
one underfull box (badness 6188) in the paragraph with the `run_sat.py` command line. `main.blg`: no warnings.

Paths below are relative to `/home/user/eth-hamiltonicity/tools/mc222/` (abbreviated `T/`) or
`/home/user/eth-hamiltonicity/research/mm/lean-mc222/` (abbreviated `L/`). The repository folder is a git checkout;
`git diff --quiet aef111e -- <file>` was run for every source file named below, and each one is identical to the
pinned commit aef111eb9bcac4f32267dc730c0098be3a4b5179. `out/` is git-ignored output of the lead's second run; it is
not at the pinned commit. Statistics over the tsv files were computed with a short Python script (sums, minima,
maxima, grouping by the `helpers` column, distinct hash counts); it is not kept.

Numbering: the paper numbers gates from 1; the code, the tsv files and Lean number them from 0. Paper H = {1,4} is
code H = {0,3}, and so on.

## Numbers in the paper and their sources

### Abstract and Section 1

| number in paper | value checked | source |
|---|---|---|
| MC = 7; upper bound 7 (Strassen) | `verify_circuit.py` accepts the 7-gate file | `T/results/circuit_mm222_7_p2.txt` (13 lines; gates = m1,m2,m4,m5,m7,m3,m6 by inspection) |
| 256 points, 8 inputs, 4 outputs | definition | — |
| 1080 cubes | 1080 data rows, 1080 distinct (root, helpers) keys = 72 × 15 | `T/results/sat_k6_results.tsv` |
| CaDiCaL 2.1.3 | tag `rel-2.1.3` | `T/run_all.sh` line 12 |
| 360 cubes in Lean | 72 files × 5 theorems; 360 `bv_decide` calls in `L/MC222/Cubes/*.lean` (grep count) | `L/NOTES.md`; `L/MC222/Cubes/` |
| 365 auxiliary axioms (360 + 3 + 2) | 360 cube calls; `bv_decide` in `BVLemmas.lean` (2) and `Normal.lean` (1); `native_decide` in `Orbit.lean` (2) | `L/NOTES.md` "Axioms"; grep of `L/MC222/*.lean` |
| ⟨1,2,3⟩: MC = 6 | see Section 10 below | `T/README.md` §7 |
| Morse: 9; 3 and 6 | from the literature check and the referee (F13) | `research/ports/literature-check.md` C.1; `REVIEW.md` F13 |
| register dated 4 September 2026 | bib entries | `refs.bib` (unchanged from the first version; pages fetched 26 Nov 2026 by the first author pass) |
| Wang, arXiv:2603.07280, §1.1 | arXiv metadata `citation_author = "Wang, Chengu"`, date 2026/03/07, fetched in this revision | arxiv.org/abs/2603.07280; `REVIEW.md` F1 |
| Boyar–Find §2.1 and §5 | text of arXiv:1407.6169v2, fetched and read in this revision: §2.1 "Related Results" states Mirwald–Schnorr; §5 "Open Problems" states the open question | arxiv.org/pdf/1407.6169v2. TCS pagination not checked; the bib note says the section numbers are those of arXiv v2 |

### Sections 2 to 4

| number | value checked | source |
|---|---|---|
| dim F = 256; dim S_i = 9 + i | definition, Lemma 4.1(d) | — |
| rem(A) = 4 | proof in Lemma 4.2 (distinct monomials) | — |
| Remark 3.1: alternating rank 8, ≥ 4 products each, 12 ≤ 2s, s ≥ 6; lemmas alone give ≥ 5 | re-derived: J = [[0,1],[1,1]], J² = I + J, det J = det(I+J) = 1 over F₂; rank Φ_t = 4·rank Λ = 8 | `REVIEW.md` F10 (argument); Mirwald–Schnorr's pair theorem used only as stated by Boyar–Find |
| \|G\| = 432 = 2·6³; τ∘φ_{P,Q,R}∘τ = φ_{R^{-T},Q^{-T},P^{-T}} | re-derived: τφτ(A,B) = (R^{-T} A Q^T, Q^{-T} B P^T) | `REVIEW.md` F8; `T/orbits.py` builds 432 maps |
| 10795 planes = 255·254/6 | arithmetic; 72 orbit sizes in `plane_orbits.txt` sum to 10795 | `T/plane_orbits.txt` |
| 72 orbits, sizes 4, 6², 9, 12², 18³, 27², 36⁵, 54⁵, 72², 108¹⁹, 216²³, 432⁷ | counted from column 3 of `plane_orbits.txt`; identical multiset in line 1 of the Rust log; Rust root planes = Python representatives, root by root | `T/plane_orbits.txt`, `T/results/exact_k6_orbits.log` line 1 |
| Lemma 4.5: rank 2 vs 4·rank μ ∈ {4, 8} | re-derived | — |
| 720 cubes with 1 ∉ H; 15 sets H | 72 × 10; C(6,2) = 15 | tsv |

### Section 5 (Method A)

| number | value | source |
|---|---|---|
| 889 lines of Rust | `wc -l src/main.rs` = 889; identical to aef111e (`git show aef111e:tools/mc222/src/main.rs \| wc -l` = 889) | `T/src/main.rs` |
| 3,547,604 states, 462.1 s, 4 threads | SUMMARY line | `T/results/exact_k6_orbits.log` (last lines); same in `T/out/mm222_k6_orbits.log` |
| 69 roots between 42,196 and 42,358 | parsed per-root lines: 69 roots below 100,000 states, min 42196, max 42358 | `T/results/exact_k6_orbits.log` |
| roots 4, 5, 36: 211,365, 211,267, 211,169 | parsed | `T/results/exact_k6_orbits.log` |
| earlier build: 3,546,906 states, 396.8 s; 10,943 states for k = 5 without orbits; commit 61cf603 | `git show 61cf603:tools/mc222/results/exact_k6_orbits.log` SUMMARY line: states=3546906 wall=396.8s; README at 61cf603 line 34: 10943 | git history; `T/README.md` lines 34, 36 (current) |

### Section 6 (Method B)

| number | value | source |
|---|---|---|
| 249 lines of Python | `wc -l gen_cnf.py` = 249; identical at aef111e | `T/gen_cnf.py` |
| about 0.1 s per cube with 1 ∉ H | 720 cubes, 56.0 s solve total (mean 0.078 s); README "about 0.1 s" | tsv; `T/README.md` §4 |
| 42,036 variables, 152,710 clauses, 2.89 MB (root 0, H = {1,4}) | regenerated in this revision with `gen_cnf.py mm222 6 --root 1,2 --helpers 0,3`: header `p cnf 42036 152710`, 2,893,361 bytes, sha256 8561c7e2… = tsv line 2 | `T/gen_cnf.py`; tsv line 2 |
| CaDiCaL flags `-q --lrat=true --binary=false`; accept only line `c VERIFIED` | `run_sat.py` lines 42, 48 | `T/run_sat.py` |
| drat-trim commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985 | | `T/run_all.sh` line 17 |
| 1080 UNSAT, 1080 VERIFIED | Counter over columns 5, 6 | tsv |
| 3.05 GB of CNF, 2.68–2.96 MB | sum 3,050,066,820; min 2,684,257; max 2,962,722 | tsv column cnf_bytes |
| 5.41 GB of LRAT, 0.40–54.05 MB, largest root 65, H = {1,2} | sum 5,408,088,012; min 404,139; max 54,053,390 at root 65 (22,99), code H = 0,1 | tsv column lrat_bytes |
| 0.33 h solve, max 17.2 s, 0.08 h check | 1174.6 s = 0.326 h; max 17.16 s (root 9, code H = 0,1); check 272.9 s = 0.076 h | tsv; `T/README.md` line 36 |
| second run 0.59 h / 0.13 h | 2135.0 s = 0.593 h; 474.7 s = 0.132 h | `T/out/sat_k6/results.tsv` (not committed) |
| 685 s, 263 s, 116 s for H = {1,2}, {1,3}, {1,4} | 684.5, 262.8, 116.1 s | tsv grouped by helpers; `T/README.md` §4 |
| 720 cubes with 1 ∉ H: 56 s | 56.0 s | tsv |
| 1080 distinct CNF hashes, 864 distinct proof hashes, 216 pairs, e.g. root 0 H = {2,5}/{3,4} | 648 hashes occur once, 216 twice; all duplicates have 0 ∉ H (code); first pair root 0, code H = 1,4 and 2,3 | tsv |
| hashes of the second run identical | `cmp` of columns 1–6, 9–12 (sorted) of `results/` and `out/` tsv: identical | `T/results/sat_k6_results.tsv`, `T/out/sat_k6/results.tsv` |
| recorded proof hash 3854bd00… | tsv line 2 (not regenerated in this revision; the paper now states only the CNF regeneration) | tsv |

### Section 7 (validation)

| number | value | source |
|---|---|---|
| Table 2, all verdicts and values | as recorded | `T/README.md` lines 30–35 |
| 60 s, 9 s (3-term polynomials, SAT) | README "k=5 UNSAT (60 s), k=6 SAT (9 s)". The first version printed 49 s and 8 s from an unrecorded run; replaced by the README figures | `T/README.md` line 33 |
| k = 5: 72 roots, 75 states; 10795 planes, 10975 states; root 0 UNSAT (5 s) | | `T/README.md` line 34 |
| k = 7: m1, m2 fixed, 0.7 s; SAT in H = {1,2,3}, 77 s | README "77 s" (first version: 73 s from an unrecorded run) | `T/README.md` line 35; `T/run_all.sh` line 32 (prefix 9,144;12,16 = m1, m2) |
| CaDiCaL 3.1.0 partial model | | `T/README.md` §4 (not re-checked) |

### Section 8 (Lean)

| number | value | source |
|---|---|---|
| Lean 4.36.0, Mathlib v4.36.0 | `leanprover/lean4:v4.36.0`; `rev = "v4.36.0"` | `L/lean-toolchain`, `L/lakefile.toml` |
| statement listing | copied from the file with comments removed and one long line broken | `L/MC222/Statement.lean` (48 lines) |
| theorem name `mc_eq_seven : MC = 7`; `hasCircuit_seven`; `not_hasCircuit_six` | | `L/MC222/Main.lean`, `L/MC222/Upper.lean` |
| 432 maps, 72 representatives; `checkT_all`, `covers_all` | | `L/MC222/Orbit.lean` lines 137, 184; `L/NOTES.md` |
| dim U = 13 at the start, ≤ 15 at the end; helpers in {1,h} (paper numbering) | | `L/MC222/Helpers.lean` header; `L/NOTES.md` |
| `lower_of_cubes` hypothesis: reps × h ∈ 1..5 (code numbering) | | `L/MC222/Final.lean` |
| axiom names `AT_indep…ax_1_24`, `ech_exists…ax_1_5`, `first_helper…ax_1_25`, `checkT_all…ax_1_1`, `covers_all…ax_1_1`, `cube_r_h…ax_1_37`; example `verifyBVExpr cube_0_1._expr_def_1_32 …` | | `L/NOTES.md` "Axioms" (printed by the Lean pass and by the lead; not re-printed here because building in `L/` was not allowed during this revision) |
| no `sorryAx` | | `L/NOTES.md` |
| 1396 hand-written lines in 13 files | `cat` of `L/MC222/*.lean` without `OrbitData.lean` and `AllCubes.lean`, `wc -l` = 1396 | **Differs from `L/NOTES.md` ("about 1400"; consistent)** |
| 4057 generated lines | `OrbitData.lean` 515 + `AllCubes.lean` 518 + 72 cube files 3024 | **`L/NOTES.md` says "plus 1600 generated lines"; my count is 4057. The paper prints 4057.** |
| 4245 s wall, 4 files in parallel, load ≈ 20; per-file sum 16,897 s; slowest file 427 s | | `L/NOTES.md` "Measurements" |
| root 0 H = {1,4} (code {0,3}): 11 s, SAT 4.6 s; root 9 H = {1,2} (code {0,1}): 22 s, SAT 12.2 s | | `L/NOTES.md`; root 9 code H = 0,1 is the slowest cube in the tsv (17.16 s) |
| 0.9–1.0 GB per Lean process | | `L/NOTES.md` |
| 5.7 GB of cube `.olean` files | | `L/NOTES.md` |
| full `lake build` about 6 min after cubes; `covers_all` about 3 min | | `L/NOTES.md` |
| not printed: the NOTES estimate "15–20 min wall on an idle 4-core machine" | an estimate, not a measurement | — |

### Section 9 (trusted base)

| number | value | source |
|---|---|---|
| rustc 1.97.0 | `rustc --version` on this machine: 1.97.0 (2d8144b78 2026-07-07) | — |
| `--member` checked for six orbits | | `T/README.md` §3 |
| 72 · 15 cubes in `summarize_sat.py` | `itertools.combinations(range(6), 2)` over 72 roots | `T/summarize_sat.py` |

### Section 10 (⟨1,2,3⟩ and ⟨2,2,1⟩)

| number | value | source |
|---|---|---|
| rem(A) = 3; \|H\| = 2 at k = 5 | | `T/README.md` §7 |
| \|G′\| = 6 · 168 = 1008 | | `T/README.md` §7; `T/orbits_mm123.py` enumerates 1008 distinct maps (per README) |
| 51 orbits, sizes 1, 7², 14², 21⁵, 42⁵, 63³, 126¹², 168², 252¹⁰, 336, 504⁵, 1008³ | counted from `plane_orbits_mm123.txt` (sum 10795); same multiset in log line 1; Rust root planes = Python representatives | `T/plane_orbits_mm123.txt`, `T/results/exact_mm123_k5_orbits.log` |
| alternating rank 4 for nonzero t | re-derived (M is 2×6 of rank 2) | `T/README.md` §7 |
| Method A: 2,829,011 states, 199.1 s, 4 threads | SUMMARY line | `T/results/exact_mm123_k5_orbits.log` |
| 510 = 51 · 10 cubes, all UNSAT and VERIFIED | 510 rows, 510 distinct keys | `T/results/sat_mm123_k5_results.tsv` |
| 145.5 s solve, 54.4 s check | sums of columns 7, 8 (README: 146 s, 54 s) | same tsv |
| 1.14 GB LRAT, largest 16.5 MB | sum 1,140,101,271; max 16,520,923 (root 31, code H = 0,1) | same tsv |
| 459 distinct proof hashes | 408 once, 51 twice | same tsv |
| k = 4: 204 = 51 · 4 cubes refuted with proofs; Method A none | 204 rows, all UNSAT/VERIFIED | `T/results/sat_mm123_k4_results.tsv`; `T/README.md` §7 |
| k = 6: prefix a1·b11, a1·b12, 1.6 s; SAT with H = {1,2,3} 5 s | | `T/README.md` §7; `T/results/circuit_mm123_6_p2.txt`; `T/run_mm123.sh` (`--prefix "1,4;1,8"`) |
| second run of mm123 hashes identical | `cmp` of tsv columns as above: identical | `T/out/sat_mm123_k5/results.tsv` (not stated in the paper) |
| ⟨2,2,1⟩: value 4 | | Table 2, `T/README.md` line 32 |

### Section 12

| number | value | source |
|---|---|---|
| commit aef111eb9bcac4f32267dc730c0098be3a4b5179 | exists locally (`git cat-file -t` = commit); contains `tools/mc222` and `research/mm/lean-mc222` including 72 cube files | git |

## Numbers that could not be verified here

- The Lean build times, memory, disk sizes and the axiom list are taken from `L/NOTES.md`. They could not be re-measured
  because nothing may be run in `L/` during this revision (a full rebuild by the lead is in progress).
- The generated-line count in `L/NOTES.md` (1600) disagrees with `wc -l` (4057); the paper uses 4057.
- The TCS 2018 section numbering of Boyar–Find was not checked; the arXiv v2 numbering was.
- The proof hash 3854bd00… was not regenerated in this revision (the formula hash was).

## Lemmas (carried over from the first version, with the referee's corrections)

| item | status |
|---|---|
| Lemma 4.1 | (c) restated as a procedure on a given shortest circuit that changes no S_j and keeps the plane of gate 1 (F6); "either vector zero or the two equal" (F6) |
| Lemma 4.2 | unchanged |
| Lemma 4.3 and the group G | G = G₀ ∪ G₀τ proved (τ² = 1, τG₀τ = G₀); right action P ↦ σᵀP stated (F8); plane vectors renamed α, β |
| Lemma 4.5 | B_f renamed Φ_f; alternating rank defined |
| Lemma 4.6 | "computing T" added (F5); proof wording on S_j ∘ σ corrected (F7); role of "Moreover" stated (F11) |
| Faithfulness claim for gen_cnf.py | stated explicitly in Section 6 (F5) |
