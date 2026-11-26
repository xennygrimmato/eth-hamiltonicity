# Referee report: "The multiplicative complexity of 2×2 matrix multiplication over F₂ is seven"

Version reviewed: `main.tex` / `main.pdf` as of 26 Nov 2026 18:17 (repository link pinned to commit `c3b3a73`). Code read: `tools/mc222` at HEAD. For `mm222`, HEAD differs from `c3b3a73` only by an added `mm123` problem. Scratch work for this review is in the session scratchpad (`rev/`, `rev/toy/`).

## Verdict

**Minor revision.**

I found no error in the mathematics. The lemmas hold as proved, up to wording gaps listed below. The encoding implements exactly the constraints the lemmas justify. I regenerated three proof objects and all three matched the recorded hashes and verified. No prior result implies the theorem. In particular, I found no theorem saying that multiplicative complexity equals quadratic complexity for sets of three or more quadratic forms over F₂. The literature records that question as open.

The paper does need corrections before release:

- one wrong author on a citation;
- a paragraph that contradicts the files at the pinned commit;
- a wrong section number in a citation;
- a few statements of lemmas that do not quite say what their proofs use;
- the trusted base is incomplete, and the word "independent" overstates the separation between the two methods.

None of these affects the theorem.

## What I checked, and how

1. **Lemmas.** I re-derived Lemmas 4.1, 4.2, 4.3 and 4.5 and Lemma 4.6 ("lemma H") from scratch. Details are under F5–F8 below.
2. **Encoding.** I read `gen_cnf.py` line by line: the RREF clauses, root fixing, the linear-part recursion, the helper/cube constraint and the outputs. I also read `run_sat.py`, `summarize_sat.py` and `orbits.py`. I read `src/main.rs`: `reducer_classes`, `helper_successors`, `dfs`, the memo key, `plane_orbits` and `check_symmetry`. The successor enumeration is exhaustive and the memo is exact.
3. **Toy tests that the authors did not tune on.** I wrote an independent brute-force MC search (`rev/toy/brute.py`). It uses plain DFS over spaces and no lemma except "skip products in S". I ran it on new targets with n = 4:
   - t6 = {x₀x₁+x₂x₃, x₀x₂+x₁x₃, x₀x₃+x₁x₂}: MC 4;
   - t7 = the first two of these: MC 3;
   - t8 = the first alone: MC 2;
   - t4 = {x₀x₁x₂, x₀x₁x₃}, cubic: MC 3;
   - t9 = {x₀x₁x₂+x₀x₃, x₁x₂x₃+x₀x₂}, cubic: MC 3;
   - and t1, t3 (n = 4, 5): MC 3.

   For each target, at k = MC and at k = MC−1, and for **every** first-gate plane (35 for n = 4), I compared four verdicts:
   - brute force with that first gate fixed;
   - `src/main.rs` with `--prefix` (a scratch copy with the toy problems added);
   - `gen_cnf.py --root` with no cube;
   - the OR over all cubes `--root … --helpers H` with |H| = k − rem(𝒜) (a scratch copy of `gen_cnf.py` with the toy targets added).

   Results: t7, t8, t9, t4 at k = MC and k = MC−1, and t6 at k = MC−1, gave 0 mismatches. Planes with a circuit numbered 29, 20, 5 and 1 respectively, and 0 at k−1.

   This exercises the root-fixing code, the RREF clauses, the cube constraint and the Rust search, including cubic targets and cases where the first gate is a *reducer*. For example, in t6 with plane (3,12), the gate (x₀+x₁)(x₂+x₃) lies in 𝒯. In those cases the cubes with 0 ∈ H are UNSAT and the others SAT, exactly as lemma H predicts.

   The t6 run at k = 4 (35 planes × 6 SAT calls) was still running when this report was written; see the note at the end.
4. **Positive control on the real target.** `gen_cnf.py mm222 7 --root 6,96 --helpers 0,1,2` is SAT. The plane (6,96) is the representative of the orbit of Strassen's m₁ plane (9,144), root 26, orbit size 36. The decoded 7-gate circuit passes `verify_circuit.py` on all 256 inputs. So the root and cube machinery admits real circuits on mm222 itself, not only from scratch as in Table 2.
5. **Proof objects.** I regenerated three cubes with the pinned CaDiCaL 2.1.3 and `lrat-check` at 2e3b2dc. None of them is root 0, H = {0,3}. In code numbering they are:

   | cube | CNF sha | LRAT sha | lrat-check |
   |---|---|---|---|
   | root 4 (1,16), H = {0,1}; 28.1 MB proof, one of the three hard roots | a36af623… | 67fe544e… | `c VERIFIED` |
   | root 65 (22,99), H = {0,2} | 5c544255… | 36660ca2… | `c VERIFIED` |
   | root 36 (17,67), H = {1,3}, a "trivial" cube | d496263c… | 39dbce99… | `c VERIFIED` |

   All six hashes equal `results/sat_k6_results.tsv`.

   A negative test (one hint deleted from a proof line) gave `c FAILED … NOT VERIFIED`. `lrat-check` prints `c VERIFIED` only when the empty clause is derived and no error occurred (lrat-check.c lines 479–496). `run_sat.py` tests for that exact line.
6. **Coverage.** `results/sat_k6_results.tsv` has 1080 data rows and 1080 distinct (root, H) keys, equal to {0..71} × C({0..5},2). Each row's (a,b) equals `plane_orbits.txt`. All rows are UNSATISFIABLE/VERIFIED. All 1080 CNF hashes are distinct. The re-run tsv agrees on all hash columns.

   There are only 864 distinct LRAT hashes: 216 pairs of 0∉H cubes have byte-identical proofs, for example root 0 with H = {1,4} and H = {2,3}. This is expected: the refutation only uses gate 0's clauses, and the variable numbering coincides. It is harmless, but a reader who sees the tsv will wonder, so one sentence would help.
7. **Orbits.** Re-running `orbits.py` reproduces `plane_orbits.txt` byte for byte. Rust's log lists the same 72 representatives in the same order. Running `--member` on roots 0–2 gave the same state counts as the representatives (42271, 42358, 42250).
8. **Numbers.** Every figure in §5–§6 matches the tsv and logs:
   - 3,547,604 states and 462.1 s;
   - 69 roots in 42,196–42,358; roots 4, 5 and 36 at 211,365 / 211,267 / 211,169;
   - 3.05 GB of CNF and 5.41 GB of LRAT; min/max sizes; root 65 H = {1,2} is the largest proof;
   - 0.33 h / 0.08 h committed and 0.59 h / 0.13 h re-run; max 17.16 s;
   - 685 / 263 / 116 / 56 s;
   - 42,036 variables and 152,710 clauses.

   The exception is the stale log paragraph (F2).
9. **Literature.** See §4 below.

## Findings, ordered by severity

### F1 (citation error; must fix). The reference `AlderStrassen26` has the wrong author.

arXiv:2603.07280, "Automated Lower Bounds for Bilinear Complexity over Finite Fields", is by **Chengu Wang** (arXiv metadata: `citation_author = "Wang, Chengu"`, dated 2026-03-07). The bibliography lists "A. Alder and V. Strassen". The error probably comes from a search engine's metadata; the same tool also mislabels Wang's arXiv:2609.06725 as "M. Bläser". "Alder–Strassen" is also the name of a classical 1981 bound, so the wrong label reads as a confusion.

The content claim is correct: §1.1 of Wang's paper says Hopcroft–Kerr established R_F₂(⟨2,2,2⟩) ≥ 7.

**Fix:**
- Rename the key to `Wang26` with author Chengu Wang.
- In the intro, write "… gives bilinear rank at least 7 over F₂ (see \cite[§1.1]{Wang26})".
- CHECKS.md wrongly marks this entry as verified; correct it.

### F2 (text contradicts the pinned files; must fix). Section 5, "Result for k=6", second half.

The paper now pins commit `c3b3a73`. At that commit, `results/exact_k6_orbits.log` *is* the re-run log: 3,547,604 states, 462.1 s, identical to `out/mm222_k6_orbits.log`. The README line 34 there already gives 10,975 for `--no-orbits` "with the committed code".

The paper still says: "The log committed in results/exact_k6_orbits.log records … 3,546,906 states and 396.8 s … the committed description gives 10,943 states". That was true at the previous pin `3bf15be`, not at `c3b3a73`.

**Fix:** replace the three sentences beginning "The log committed in…" with:

> An earlier log from a build that kept its cache of failed states across the roots of one thread (commit 61cf603) recorded the same verdicts with 3,546,906 states in 396.8 s, and 10,943 states for k = 5 without orbit reduction; such a cache is sound.

Also update CHECKS.md discrepancy 1, which says the same.

### F3 (citation detail; must fix). `\cite[\S4]{BoyarFind18}` is cited for both the Mirwald–Schnorr statement and the open question.

In the arXiv v2 text (dated 21 Aug 2018, matching the TCS version):
- the Mirwald–Schnorr statement is in **§2.1 "Related Results"**;
- the open question ("It is still not known whether this is true for (n,m)-functions in general", with the remark that Strassen's result is not known to hold over F₂) is in **§5 "Open Problems"**;
- §4 is "Multiplicative Complexity of an Explicit Vector valued function".

**Fix:** cite §2.1 for the Mirwald–Schnorr statement and §5 for the open question, after checking against the TCS pagination.

The paper's content of Mirwald–Schnorr comes second-hand. The FOCS'87 abstract does say they determine L for single forms and for pairs, which supports the claim. The paper should say "as stated in" (it does) or, better, cite the theorem in MS'92 directly.

### F4 (overclaim of independence; should fix). Abstract ("Two independent programs"), §1 ("carried out twice by programs that share no code" is fine), §6 ("In the independent re-run"), §11.

The two methods share no code, which is true and checkable. They share:
- the model;
- Lemmas 4.1–4.3, whose correctness is the crux for both;
- the orbit idea;
- authorship in one session.

The "re-run" was the same scripts on the same machine. Hash identity shows determinism, not independent confirmation.

**Fix:**
- Abstract: "Two separately written programs, which share no code but rely on the same lemmas, then carry out the search."
- §6: "In a second run of the same pipeline every one of the 1080 formula hashes and 1080 proof hashes was identical to the committed record."

Also note that byte-identical LRAT output requires the same CaDiCaL build. Determinism is per binary, so hashes may differ with another compiler, and the proofs then need checking rather than comparison.

### F5 (lemma statement gap; should fix). Lemma 4.6 does not say the circuit computes 𝒯.

As stated, "there is a circuit g₁,…,g₆ in the normal form … and a set H … such that every i∉H satisfies g_i∈W_i". Any circuit with those properties would do, whether or not it computes 𝒯; the proof of the theorem uses that it does.

**Fix:** "…there is a circuit g₁,…,g₆ **computing 𝒯**, in the normal form…". Also state explicitly that the cube formula is satisfiable exactly when such a circuit exists for that (root, H). That is the faithfulness claim in §8.

### F6 (lemma statement gap; should fix). Lemma 4.1(c) is stated as an existence claim, but Lemmas 4.3 and 4.6 use it as a procedure.

Both later proofs need: "a given shortest circuit can be brought into normal form *without changing any S_j and without changing the plane of gate 1*". The proof of (c) shows this. The statement only says "some circuit … in which …".

**Fix:** restate (c) as:

> Every circuit with the least number of gates computing 𝒯 can be transformed, gate by gate in increasing order and without changing any space S_j, into one in which…; appending k−m gates x₁x₂ then gives exactly k gates.

Also in (c), "If the coefficient vectors … were zero or equal" should read "If either coefficient vector is zero, or the two are equal". The case of one zero and one nonzero vector is covered by the argument but not by the wording.

### F7 (wording; should fix). Proof of Lemma 4.6: "they change no space S_j, so each gate stays a reducer or a helper".

The symmetry step maps S_j to S_j∘σ; it does not leave S_j unchanged. Classification is preserved because (S+𝒯)∘σ = S∘σ + 𝒯. Only the normal-form step leaves the S_j unchanged.

**Fix:** "The substitution maps each S_j to S_j∘σ and, since 𝒯∘σ = 𝒯, maps reducers to reducers and helpers to helpers; the normal-form step changes no S_j."

### F8 (small gap; optional). |G| = 432 and "G acts on planes".

The proof gives injectivity of (P,Q,R) ↦ map and τ ∉ H, but not G = H ∪ Hτ. That needs τ² = 1 and τHτ = H; for example, τ∘(P,Q,R)∘τ = (R^{−T}, Q^{−T}, P^{−T}).

Also say explicitly that the action on planes is P ↦ σᵀP, a right action. `orbits.py` computes exactly the set {σᵀP : σ ∈ G}, which is the set Lemma 4.3 needs.

One line fixes both points. Neither affects correctness: the Rust code generates the orbit by closure and agrees.

### F9 (trusted base incomplete; should fix). §8, Method B.

The verdict "all 1080 proofs VERIFIED" is evidenced only by `results/sat_k6_results.tsv`, because the proofs were deleted. So the trusted base must include:
- `run_sat.py`: it invokes `gen_cnf.py` with the right (root, H), records the verdict, runs `lrat-check` on the same file it hashes, and greps for the exact line `c VERIFIED`;
- `summarize_sat.py`: the coverage check;
- `plane_orbits.txt`, as produced by `orbits.py`;
- the Python interpreter;
- `lrat-check`'s DIMACS parser, which must accept the leading `c …` comment line that `gen_cnf.py` writes.

For Method A, the trusted base should include the logs being produced by the pinned code. Also say that a reader can independently re-verify any subset of cubes in minutes; I did three.

### F10 (framing; recommended). A human proof of MC ≥ 6 is available and would sharpen what the computation is needed for.

Let W = {Tr(Λᵀ·AB) : Λ ∈ 𝔽₄ ⊂ M₂(F₂)}, the plane used in MF-180. Its three nonzero forms have alternating rank 4·rank Λ = 8 by the computation in Lemma 4.5, so each has MC 4. In a quadratic circuit with s products, write supports S₁, S₂ for two basis forms. Then |S₁|, |S₂| and |S₁ Δ S₂| are each ≥ 4, and 2|S₁ ∪ S₂| ≤ 2s, so s ≥ 6. Mirwald–Schnorr's theorem for pairs (MC = quadratic complexity) then gives MC(𝒯) ≥ MC(W) ≥ 6.

So the computation is needed only to exclude exactly 6. This depends on MS'92 for pairs, which the authors have not read; they should either read it and add the remark, or omit it. As it stands, the paper's own lemmas give only MC ≥ 5: rem = 4, plus "the first gate is a helper".

### F11 (minor). Lemma 4.5's role.

The table says Lemma 4.5 is "not used" by either method, yet Lemma 4.6 ends with "Moreover 1 ∈ H", which uses it. Say in the lemma that "Moreover" is not needed for the theorem and only explains the 720 trivial cubes. Also, the abstract says "Four short lemmas" while §4 has five. Write "Short lemmas, proved here, reduce…".

### F12 (minor). Section 3 and Remark 9.1.

"Strassen's homogenization … does not survive this" overstates. Section 3 shows that the *proof* does not transfer, not that the conclusion fails. Write "does not carry over".

Remark 9.1 (⟨2,2,1⟩, two outputs) and the 𝔽₄ row (two outputs) fall under Mirwald–Schnorr's pair theorem. For these, MC equals quadratic complexity, so "we did not locate a published source" can be softened to "by Mirwald–Schnorr the value equals the quadratic complexity, which is 4".

### F13 (minor). Morse 2026 is an unrefereed arXiv preprint.

"Morse proved" should read "Morse gives a proof (unrefereed preprint, with a Lean 4 formalization)". Verified: the abstract states Mul₄ = 9, three-term = 6 and Lean 4; the body (eq. at line ~108) gives (0,1,3,6,9) for Mul₀…Mul₄, so two-term = 3 is correct.

### F14 (minor). Winograd's model.

Winograd 1971 proves the bound 7 *even for commutative algorithms*, i.e. quadratic algorithms over a field, with entries as indeterminates. The intro mentions only "identity of polynomials". Saying "even when commutativity is used, i.e. for quadratic algorithms, with entries indeterminates over an infinite field" makes the contrast with the Boolean model sharper and more accurate.

### F15 (minor). Line counts and code state.

The counts 813 (`main.rs`) and 246 (`gen_cnf.py`) are correct at the pinned commit `c3b3a73`. HEAD now has 889 and 249 after the `mm123` problem was added. Say "at the pinned commit", and pin the reproduction instructions (`run_all.sh`) to that commit.

## Literature check (item 4 of the brief)

- **Is MC = quadratic complexity known for sets of quadratic forms over F₂?** No. Boyar–Find (arXiv:1407.6169v2, §2.1 and §5) state that Mirwald–Schnorr proved quadratic circuits optimal for (n,1)- and (n,2)-functions and that "it is still not known whether this is true for (n,m)-functions in general". They add that Strassen's infinite-field result is not known to hold over F₂. Morse (arXiv:2608.30238, Aug 2026) restates this as open. I found no later paper that resolves it.

  An unrefereed machine-generated register entry (slopdealer.com MF-165, 4 Sep 2026) claims MC = qMC for 3-dimensional spaces of forms on n ≤ 5 variables only. It does not cover 8 variables or 4 forms. **Conclusion: the theorem is not a corollary of a known general result, and the paper's framing stands.**
  - https://arxiv.org/pdf/1407.6169v2
  - https://arxiv.org/abs/1407.6169v1
  - https://arxiv.org/abs/2608.30238
  - https://slopdealer.com/research/papers/mf-165/
- **Mirwald–Schnorr.** TCS 102(2):307–328, 1992; FOCS'87 abstract: L(f) for single forms from the coefficients, and the complexity of pairs of forms. https://doi.org/10.1016/0304-3975(92)90235-8, https://doi.org/10.1109/sfcs.1987.57
- **Winograd 1971.** "The minimum number of multiplications required to multiply two 2×2 matrices is seven". Secondary sources (Paterson's lecture notes) state the bound holds even with commutativity. https://research.ibm.com/publications/on-multiplication-of-2-2-matrices, https://warwick.ac.uk/fac/sci/dcs/teaching/material-archive/cs341/matrixmult09.pdf
- **Hopcroft–Kerr 1971.** A non-commutative model; R_F₂(⟨2,2,2⟩) ≥ 7 is attributed to them in Wang, arXiv:2603.07280, §1.1. See F1 for the author. https://arxiv.org/abs/2603.07280
- **Bshouty (SIAM J. Comput. 1989) and Bshouty–Kaminski.** Lower bounds over F₂ in the formal straight-line, bilinear or quadratic models. They do not treat Boolean functions modulo x² − x, as Morse also notes. Shpilka (arXiv:cs/0201001) covers bilinear and quadratic circuits only. None of these implies the theorem. https://doi.org/10.1137/0218052, https://arxiv.org/abs/cs/0201001
- **Prior statements of MC(⟨2,2,2⟩) over F₂.** Slop Dealer MF-149, MF-180 and ML-088 state 6 ≤ MC ≤ 7, with 6 vs 7 open, as the paper says. MF-086 and ML-051 (29 Aug 2026) explicitly name "refuting an unrestricted six-gate circuit" as the next milestone. I found no statement of MC = 7 anywhere.
  - https://slopdealer.com/research/papers/mf-180/
  - https://slopdealer.com/research/papers/mf-149/
  - https://slopdealer.com/research/papers/ml-088/
  - https://slopdealer.com/research/papers/mf-086/
  - https://slopdealer.com/research/papers/ml-051/
- **Other citations** (Strassen 1969/1973, BPP 2000, Stoffelen FSE 2016, CaDiCaL 2.0, Cruz-Filipe et al. CADE 2017, DRAT-trim SAT 2014): bibliographic data look right. I did not re-open each.

## Prose edits

1. **Abstract.** Replace "Four short lemmas, proved here, reduce the question to a finite search. Two independent programs then carry out the search:" with "Short lemmas, proved here, reduce the question to a finite search, which two separately written programs carry out:".
2. **Abstract.** "The classical lower bounds of Winograd and of Hopcroft and Kerr concern bilinear and arithmetic algorithms and do not apply to this model." Replace with "The classical lower bounds of Winograd and of Hopcroft and Kerr concern algorithms over polynomials and do not transfer to this model."
3. **§1 "Why the classical bound does not apply".** "does not survive this" → "does not carry over to this model".
4. **§1 "What is claimed".** "which was carried out twice by programs that share no code" → "which was carried out by two programs that share no code".
5. **§1 "Prior statements".** "We do not claim priority beyond this." Replace with "If an earlier statement exists, we would be glad to cite it." The current sentence sounds defensive.
6. **§2.** "We call a gate g_i a reducer if … and a helper if …" Add: "(every gate of a shortest circuit is one or the other, by Lemma 4.1(d))".
7. **§3, last sentence.** "The point is only that no known general argument transfers the bound 7 to the Boolean model." Replace with "So no known general argument transfers the bound 7 to the Boolean model."
8. **§4, first paragraph.** "This section proves the four lemmas used by the computations, and one more that explains the running times." Fine, but name them: "Lemmas 4.1–4.3 and 4.6 are used; Lemma 4.5 only explains why 720 cubes are trivial."
9. **Lemma 4.3.** The letters a, b are used both for plane vectors and for matrix entries a_{ik}, b_{kj}. Use α, β throughout for plane vectors (Lemma 4.6 already does) or u, w. Lemma 4.5 likewise uses B_f while B is a matrix; rename it β_f or Φ_f.
10. **Lemma 4.6.** Add "computing 𝒯" (F5). Call it "Lemma 4.6 (helper sets)" consistently. The README calls it "lemma H", and the paper never connects the two names.
11. **§5.** "The cache depends only on the state and is therefore sound; the current code clears it at the start of each root." Replace with "The cache depends only on the state and is therefore sound; it is cleared at the start of each root, so per-root counts are deterministic."
12. **§5, "Result for k=6".** Replace the stale sentences (F2).
13. **§5, "Helpers".** "Since S+span{w}∖S = w+S" → "Since (S+span{w})∖S = w+S".
14. **§6, "Cubes".** "they were run anyway" → "they were run anyway as a consistency check; each is refuted in about 0.1 s".
15. **§6, "Proof objects".** "CaDiCaL is deterministic, so one script regenerates all of them" → "CaDiCaL is deterministic for a fixed build, so one script regenerates all of them".
16. **§6.** Add one sentence on the 864 distinct LRAT hashes (finding 6 above).
17. **§7.** "an earlier SAT computation in our notebook" refers to unpublished internal material. Replace with "an earlier computation", or drop it.
18. **§7.** "the three nonzero target combinations have alternating rank 4". "Alternating rank" is undefined. Define it once in Lemma 4.5: "the rank of B_f, which we call the alternating rank of f".
19. **§8, "Both methods".** Add `run_sat.py`, `summarize_sat.py` and the Python interpreter (F9).
20. **§9, Remark 9.3.** "It was also obtained earlier by a separate enumeration of decomposable alternating forms, which we have not re-checked." Either give the source or delete the sentence. An unverifiable internal result adds nothing.
21. **§10, Question 4.** The second sentence repeats §3 verbatim; drop it.
22. **§11.** "re-implemented the search independently" → "re-implemented the search as two programs, without reading the first program".
23. **General.** The text is mostly plain and precise. The remaining machine-writing tells are:
    - "Status: computed by both programs";
    - "The point is only that…";
    - repeated "we did not …" disclaimers in §5 and §8.

    Consolidate the disclaimers in §8.
24. **PDF.** Renders cleanly on all 10 pages, with no overfull boxes in `main.log`. The only warning is that one `[h]` float was changed to `[ht]`. Table 2's narrow first column wraps "F₄ multiplication, 4 inputs" onto two lines; widen it or abbreviate.

## Note on the remaining toy run

The t6 run at k = 4 (MC = 4, one helper, 35 planes) was still running at the time of writing. Every other toy comparison (≈ 400 plane × method verdicts) agreed. Its result is reported in the hand-off message.
