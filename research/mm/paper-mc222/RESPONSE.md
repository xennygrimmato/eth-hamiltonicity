# Response to the referee

Revision of 26 November 2026. The paper now pins commit aef111eb9bcac4f32267dc730c0098be3a4b5179 of
github.com/xennygrimmato/eth-hamiltonicity, which contains `tools/mc222` and the new Lean proof in
`research/mm/lean-mc222`. Section numbers below are those of the revised paper (13 pages).

## Findings

- **F1** (wrong author on arXiv:2603.07280). Key renamed `Wang26`, author Chengu Wang (checked against the arXiv
  metadata, `citation_author = "Wang, Chengu"`). The intro now reads "gives bilinear rank at least 7 over F₂ (see
  [Wang26, §1.1])". CHECKS.md corrected.
- **F2** (stale log paragraph). The three sentences replaced by the referee's text (commit 61cf603, 3,546,906 states,
  396.8 s, 10,943 states; "such a cache is sound"); verified against `git show 61cf603:…/exact_k6_orbits.log`. The
  unrecorded single-thread re-run of roots 68–71 was removed. CHECKS.md updated.
- **F3** (`\cite[\S4]`). Now §2.1 for the Mirwald–Schnorr statement and §5 for the open question, checked against the
  text of arXiv:1407.6169v2. The bib entry says the section numbers are those of arXiv v2; the TCS pagination was not
  checked. Mirwald–Schnorr is still cited "as stated in" Boyar–Find, since we have not read MS'92.
- **F4** (independence overclaim). Abstract and §1 use the referee's wording ("two separately written programs …
  share no code but rely on the same lemmas"). §6 now says the second run was the same pipeline on the same machine
  with the same binaries, that identical hashes show determinism and not independent confirmation, and that hashes
  may differ with another build. §12 says the same. A paragraph "Independence of (a) and (b)" in §9 states what the
  external pipeline and the Lean proof share and do not share.
- **F5** (Lemma 4.6 omits "computing T"). Added. The faithfulness claim ("satisfiable if and only if such a circuit
  exists for that (α, β, H); only the direction circuit ⇒ assignment is needed") is stated in §6 and referred to in §9.
- **F6** (Lemma 4.1(c) as a procedure). Restated: every shortest circuit can be transformed gate by gate without
  changing any S_j, and the plane of gate 1 does not change; then padding. "If either coefficient vector is zero, or
  the two are equal" adopted, and the proof now treats the one-zero case.
- **F7** (proof of Lemma 4.6). Replaced by the referee's sentence: the substitution maps S_j to S_j∘σ and preserves
  reducers and helpers since T∘σ = T; only the normal-form step leaves the S_j unchanged.
- **F8** (|G| = 432 and the action). Added τ² = 1 and τφ_{P,Q,R}τ = φ_{R^{-T},Q^{-T},P^{-T}} (re-derived), so
  G = G₀ ∪ G₀τ; stated that P ↦ σᵀP is a right action and that its orbits are what `orbits.py` computes.
- **F9** (trusted base). §9 Method B now lists `run_sat.py`, `summarize_sat.py`, `plane_orbits.txt` from `orbits.py`,
  the Python interpreter, and the DIMACS parser of `lrat-check` (leading comment line); it says that the verdict rests
  on the tsv because the proofs were deleted. Method A lists that the log was produced by the pinned code. §6 says any
  subset of cubes can be re-verified in minutes.
- **F10** (human proof of MC ≥ 6). Added as Remark 3.1, explicitly conditional on Mirwald–Schnorr's pair theorem as
  stated by Boyar–Find, with the sentence that we have not read MS'92 and that nothing else uses the remark; it also
  says the paper's lemmas alone give only MC ≥ 5 and the computation is needed to exclude exactly 6. This is a middle
  course between the referee's two options (read MS'92 and add, or omit); we chose it because the argument is short,
  the dependency is stated where it is used, and it explains where the public bound 6 comes from.
- **F11** (role of Lemma 4.5; "four lemmas"). §4 opens by naming the lemmas used (4.1–4.3, 4.6) and saying 4.5 only
  explains the 720 trivial cubes; a sentence after Lemma 4.6 says "Moreover" is not needed for Method B and is used by
  the Lean proof. Table 1 updated (now with a Lean column). The abstract no longer counts the lemmas.
- **F12** ("does not survive"; Remark on ⟨2,2,1⟩). "The proof behind … homogenization does not carry over". The
  ⟨2,2,1⟩ remark (now Remark 10.1) says that by Mirwald–Schnorr, as stated by Boyar–Find, its multiplicative complexity
  equals its quadratic complexity; "we did not locate a published source" removed.
- **F13** (Morse). Now "Morse gives a proof (unrefereed preprint, with a Lean 4 formalization)".
- **F14** (Winograd's model). Now "whose entries are indeterminates over an infinite field, even when the algorithm may
  use commutativity, that is, for quadratic algorithms".
- **F15** (line counts and pinning). Counts are now those at the new pinned commit aef111e: 889 lines (`main.rs`,
  which includes the ⟨1,2,3⟩ problem) and 249 lines (`gen_cnf.py`), each stated as "at the pinned commit"; the
  `run_sat.py` command and `run_all.sh` are described as run at the pinned commit. All cited files were checked to be
  identical to aef111e.

## Prose edits

1. Abstract wording on the lemmas and the two programs: adopted.
2. "concern algorithms over polynomials and do not transfer to this model": adopted.
3. "does not carry over to this model": adopted.
4. "carried out by two programs that share no code": adopted.
5. "If an earlier statement exists, we would be glad to cite it": adopted.
6. Parenthetical after the reducer/helper definition: adopted.
7. "So no known general argument transfers …": adopted.
8. §4 first paragraph names the lemmas used: adopted.
9. Plane vectors renamed α, β throughout (Lemma 4.3, the paragraph on G, Lemma 4.5, Method A roots); B_f renamed Φ_f.
10. "computing T" added; "Lemma 4.6 (helper sets)" used consistently; one sentence connects it to the README's
    "lemma H".
11. Cache sentence: adopted.
12. Stale sentences replaced (F2).
13. "(S + span{w}) \ S = w + S": adopted.
14. "run anyway as a consistency check; each is refuted in about 0.1 s": adopted.
15. "deterministic for a fixed build": adopted.
16. Sentence on 864 distinct proof hashes added (216 pairs, example root 0 with H = {2,5} and {3,4}, checked in the
    tsv); the analogous count (459) is given for ⟨1,2,3⟩.
17. "our notebook" removed.
18. Alternating rank defined in Lemma 4.5.
19. `run_sat.py`, `summarize_sat.py`, the Python interpreter added to §9 (F9).
20. Second sentence of the quadratic-model remark deleted; the remaining one-line remark was folded into §3 ("all
    three equal 7") to save space.
21. Second sentence of the question on bilinear rank deleted.
22. §12: "re-implemented the search as two programs, … without reading the first program".
23. "Status: computed by both programs" and "The point is only that" removed; the §5 and §9 disclaimers ("we have not
    identified that build", "we did not repeat this") removed or consolidated into §9.
24. Table 2: first column widened, "F₄ multiplication" shortened to "F₄ product"; no overfull boxes remain.

## New material (requested by the project lead, not by the referee)

- §8 "A formal proof in Lean": statement listing, proof architecture, axiom list with its meaning for trust (kernel
  plus compiler and runtime for 365 evaluations, not the kernel alone), sizes and measured times from `NOTES.md`,
  reproduction. Abstract, §1 ("What is claimed", now two supports (a) and (b)), §9 and §12 updated accordingly. The
  sentence "No part of the argument is formalized in a proof assistant" and the old "Formalization" paragraph were
  removed.
- Theorem 1.2 and §10: MC(⟨1,2,3⟩) = 6 by the external pipeline (exact search, 510 cubes with checked LRAT proofs);
  stated as not formalized. The old Remark (MC ∈ {5,6}) and the open question on ⟨1,2,3⟩ were removed.
- A new open question: a proof checked by the Lean kernel without compiled evaluation.

## Not done, and why

- MS'92 was not read, so its theorem is still cited second-hand through Boyar–Find (F3, F10, F12).
- The TCS pagination of Boyar–Find was not checked (no access); the bib entry names arXiv v2 as the source of the
  section numbers.
- No numbers were re-measured in the Lean folder: the brief forbids running anything there while the lead's rebuild is
  in progress. The Lean figures are quoted from `NOTES.md`, except the generated-line count, which I recounted (4057;
  `NOTES.md` says 1600).
- The proof hash of root 0, H = {1,4}, was not regenerated (CaDiCaL was not run in this revision); the paper now
  reports only the regenerated formula hash.
- The validation times in Table 2 now follow the README (60 s, 9 s, 77 s) instead of an unrecorded run (49 s, 8 s,
  73 s).
- To stay at 13 pages the margins were reduced from 27 mm to 25 mm and the bibliography is set in footnotesize.
