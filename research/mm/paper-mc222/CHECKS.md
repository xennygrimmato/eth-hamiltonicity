# CHECKS for main.tex (26 November 2026)

Paths are relative to `/home/user/eth-hamiltonicity/tools/mc222/` unless stated.
"Re-run" means the lead's run of `run_all.sh` whose outputs are in `out/` (git-ignored, not committed).
"My run" means commands run while writing, outputs in the session scratchpad (not kept).

## Lemmas and propositions

| item | re-derived | issues found |
|---|---|---|
| Prop. 2.2 (Strassen over F2, 7 ANDs) | yes, by hand; `verify_circuit.py results/circuit_mm222_7_p2.txt` re-run: OK on 256 inputs | none. The committed circuit is exactly Strassen's m1..m7 (order m1,m2,m4,m5,m7,m3,m6). |
| Sec. 3 (homogenization gap) | yes | Only the logical gap is shown (x1x2·x1x2 = x1x2, x1x2·x1 = x1x2). No example of MC < quadratic complexity is known to us; the paper says so. |
| Lemma 4.1 normal form (README N1) | yes | README's N1 is correct but terse. Added: (i) why the coefficient vectors of L_i, R_i are independent in a shortest circuit (else g_i in S_{i-1}); (ii) padding gate x1x2 is in RREF; (iii) the deletion argument. The RREF in gen_cnf.py is on coefficient vectors over (x, g_<i), not on functions; this is fine because a shortest circuit has independent generators. |
| Lemma 4.2 counting (README N2) | yes | none. Independence of c_ij mod A proved via distinct monomials (README says only "the code checks"). |
| Lemma 4.3 symmetry (README N3) | yes | none. Strengthened to T∘σ = T (not only A+T). |G| = 432 proved (injectivity). |
| Prop. 4.4 orbits (computed) | re-ran `orbits.py` (my run): identical `plane_orbits.txt`; Rust reps (out/mm222_k6_orbits.log) = Python reps root by root; size multiset equal | none. Rust's generator set {s,t} per slot generates GL2(F2) (two distinct involutions of S3), so closure under generators gives G-orbits. |
| Lemma 4.5 first gate is a helper | yes (alternating rank 2 vs 4·rank μ ∈ {4,8}) | README states it with the same argument; correct. Explains why the 720 cubes with 0∉H (code numbering) are trivial. |
| Lemma 4.6 helper sets (README "lemma H") | yes | README step 5 ("these spaces do not change when a gate is altered by an element of S_{i-1}") is true for W_i only because S_{i-1} ⊆ W_i; the README does not say this. The paper avoids the issue by normalizing (symmetry, then N1) first and running the W-argument on the normalized circuit. No gap in the conclusion. |
| Lemma H vs code | checked | `gen_cnf.py` lines 166-191 encode exactly g_i = e0 + Σ ell_k x_k + Σ mu_t c_t + Σ_{j∈H, j<i} α_j g_j at all 256 points for i ∉ H; `run_sat.py` line 77 runs all 15 pairs of {0..5} for each of the 72 roots from plane_orbits.txt; `summarize_sat.py` checks coverage. Matches. |
| RREF constraints in gen_cnf.py (lines 122-144) | checked | Encode: L≠0, R≠0, pivot(L)=c ⇒ R[0..c]=0, pivot(R)=c ⇒ L[c]=0. This is exactly the 2-row RREF (unique basis per plane). |
| Root fixing (gen_cnf.py rref_plane, lines 96-107, 145-149) | checked | correct RREF of span{a,b}. |
| Method A completeness (main.rs reducer_classes, helper_successors, dfs) | read | Reducer class enumeration (kernel tags, Gray code over u) and helper deduplication by residue mod S are exhaustive and exact. Memo key = fully reduced echelon basis of S mod A, exact. |
| Proof of Theorem 1.1 | yes | none. |
| F4 validation lower bound (Sec. 7) | yes (2 gates ⇒ both reducers ⇒ first gate ∈ A+T, impossible by rank) | none |

## Discrepancies between README / committed results and the code (report to lead)

1. `results/exact_k6_orbits.log` (states=3546906, wall=396.8 s, line 75) does not match the current code.
   The re-run `out/mm222_k6_orbits.log` line 75 gives states=3547604, wall=462.1 s. Per-root counts agree for
   roots 0-3 (first root of each thread) and are smaller in the committed log for later roots. My run of
   `mc222 mm222 6 --roots 68:72 --threads 1` gave 42196 states for each root, equal to the re-run, so the current
   code is deterministic per root. Consistent with an earlier build that did not clear the memo per root (sound).
   README line 36 ("3 546 906 states, 6.6 min") and README line 34 ("10943 states" for k=5 --no-orbits; current code: 10975, my run) come from that build. Verdicts are unaffected.
2. README line 172: "each one takes 0.1-15 s". Committed tsv: 0.03-17.16 s. Minor.
3. README line 36 "0.33 h solver CPU, 0.08 h check CPU" matches the committed tsv; the re-run gives 0.59 h / 0.13 h. Both stated in the paper.
4. README says the trust base for (A) includes `--member` checks on 6 orbits; not re-run by me (paper says so).

## Numeric claims

| claim in paper | source |
|---|---|
| 72 orbits, sizes 4,6²,9,12²,18³,27²,36⁵,54⁵,72²,108¹⁹,216²³,432⁷ | `plane_orbits.txt` (counted); `results/exact_k6_orbits.log` line 1 |
| 10795 planes | `orbits.py` line 124 assert; 255·254/6 |
| |G| = 432 | proved in text; `orbits.py` builds 216·2 maps (lines 57-64) |
| k=6, re-run: 3,547,604 states, 462.1 s, 4 threads | `out/mm222_k6_orbits.log` line 75 |
| roots 4, 5, 36: 211,365 / 211,267 / 211,169 | `out/mm222_k6_orbits.log` lines 25, 29, 68 |
| other 69 roots 42,196-42,358 | `out/mm222_k6_orbits.log` (computed min/max) |
| roots 68-71 single-thread: 42,196 each | my run |
| committed: 3,546,906 states, 396.8 s | `results/exact_k6_orbits.log` line 75 |
| k=5: 72 roots, 75 states; all planes 10,975 states (README: 10,943) | my run; README line 34 |
| 1080 cubes, all UNSAT, all VERIFIED | `results/sat_k6_results.tsv` (1081 lines incl. header); `summarize_sat.py` output on it and on `out/sat_k6/results.tsv` |
| formulas total 3.05 GB, 2.68-2.96 MB each | tsv column cnf_bytes (sum 3,050,066,820; min 2,684,257; max 2,962,722) |
| proofs total 5.41 GB, 0.40-54.05 MB, largest root 65 H={0,1} | tsv column lrat_bytes (sum 5,408,088,012; min 404,139; max 54,053,390 at tsv line 1000) |
| solver 0.33 h total, max 17.2 s; check 0.08 h | committed tsv (sum 1174.5 s; max 17.16 s at tsv line 152; check sum 272.9 s) |
| re-run 0.59 h / 0.13 h | `out/sat_k6/results.tsv` via summarize_sat.py |
| H={0,1},{0,2},{0,3}: 685 s, 263 s, 116 s; 720 cubes with 0∉H: 56 s | committed tsv, grouped by column helpers |
| all 1080 formula and proof hashes identical in re-run | `cmp` of tsv columns 1-6, 9-12 between results/ and out/ (my check: SAME) |
| root 0, H={0,3}: hashes 8561c7e2…, 3854bd00…, VERIFIED; 42,036 vars, 152,710 clauses, 2,893,361 bytes | my run with CaDiCaL 2.1.3 and lrat-check 2e3b2dc; tsv line 2 |
| validation table times (49 s, 8 s, 5 s, 73 s) and verdicts | my run (CaDiCaL 2.1.3, one core); README lines 30-35 give 60 s, 9 s, 5 s, 77 s |
| (A) k=7 with m1,m2 fixed: found, 0.7 s | my run; `run_all.sh` line 32 |
| 813 lines main.rs; 246 lines gen_cnf.py | `wc -l` |
| drat-trim commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985 | `run_all.sh` line 17; checked in scratch clone |
| CaDiCaL rel-2.1.3 | `run_all.sh` line 12 |
| rustc 1.97.0 | `rustc --version` on this machine |
| CaDiCaL 3.1.0 printed partial model | README lines 187-188 (not re-checked) |
| repo commit 3bf15be93674c5382d9fc816922abdc1e70c0303 | given by the lead (not checked: local folder is not a git repository) |
| 128-bit hash in mc_span.c | `research/mm/lab/notebook.md` line 126 |
| ⟨1,2,3⟩: k=4 refuted by mc_span, 10865 states | `research/mm/lab/notebook.md` lines 134-135 |

## References

| reference | status |
|---|---|
| Strassen 1969, Numer. Math. 13:354-356 | verified online (Springer, EuDML) |
| Winograd 1971, LAA 4(4):381-388 | verified online (ScienceDirect, IBM Research) |
| Hopcroft–Kerr 1971, SIAM J. Appl. Math. 20(1):30-36 | verified online (SIAM, Cornell TR abstract). The claim "rank ≥ 7 over F2" is taken from Alder–Strassen's statement, as in the literature check. |
| Strassen 1973, J. reine angew. Math. 264:184-202 | verified online (EuDML, De Gruyter) |
| Mirwald–Schnorr 1992, TCS 102(2):307-328 | bibliographic data verified online; content (quadratic circuits optimal for 1 and 2 outputs) only via Boyar–Find's statement, from the literature check; the paper itself was not read |
| Boyar–Peralta–Pochuev 2000, TCS 235:43-57 | verified online (bibliographic data and abstract) |
| Boyar–Find 2018, TCS 720:36-46 | verified online; §4 quotes from the literature check [read] |
| Morse, arXiv:2608.30238 | verified online (abstract: Mul4 = 9, Lean, three-term = 6); Mul2 = 3 from the literature check |
| Alder–Strassen, arXiv:2603.07280 | verified online (abstract and §1.1: HK give R_F2(⟨2,2,2⟩) ≥ 7) |
| Stoffelen, FSE 2016, LNCS 9783, 140-160 | verified online; cited in Sec. 6 for the truth-table encoding |
| CaDiCaL 2.0, CAV 2024, LNCS 14681, 133-152 | verified online |
| Cruz-Filipe et al., CADE 26, LNCS 10395 (LRAT) | verified online (pages not found; omitted) |
| Wetzler–Heule–Hunt, SAT 2014, LNCS 8561 (DRAT-trim) | verified online (pages not found; omitted) |
| Slop Dealer MF-149, MF-180, ML-088 (4 Sep 2026) | verified online (pages fetched 26 Nov 2026) |
| Shpilka FOCS 2001; Häner arXiv:2307.07424; Spiizer arXiv:2611.23622 | not cited (not needed; Häner only a snippet in the literature check) |
