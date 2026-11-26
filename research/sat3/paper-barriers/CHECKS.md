# CHECKS for main.tex ("Three barriers at exponent one half for the counting engines")

Build: `pdflatex`, `bibtex`, `pdflatex`, `pdflatex` in this folder. Result: **17 pages** (amsart 10pt, 1 in margins) after the review fixes of `REVIEW.md`.
`main.log`: no errors, no undefined references or citations, no overfull boxes. `main.blg`: no warnings.
Not committed or pushed by the author of this folder. (Note: a snapshot commit by another session, c45c683, picked up an early version of `refs.bib`; the
working copy differs from it.)

Paths are relative to `research/sat3/` unless they start with `research/`. "Status" is the label used in the
paper: P = proved here (full proof in the paper; also checked by an AI referee unless noted), PL = proved here and
in Lean, R = refereed by an AI referee only (sketch in the paper), C = conditional, N = numerical, U = not refereed,
I = imported (quoted from an unrefereed lab paper).

Pinned repository commit in the paper (`\commit`): e97d95610af61382c28171bda4d9ebeb18345051, the HEAD of the working repository at the time of
the final build (`git rev-parse HEAD`). This folder itself (main.tex, CHECKS.md, main.pdf) is not in that commit.

## Section 1 (introduction)

| statement | source | status |
|---|---|---|
| AN and OA claim #3-SAT in 2^{O(n/√log n)}; unrefereed | AN-ETH `pb/aneth/paper.txt` (scratchpad), OA-ETH; `prior-barriers.md` | quoted |
| ρ = 1/√2 from App. B, α′ = log_β(1/ρ*) = 1/2 | `notes.md` §1.1, `research/ports/c1d1/notes.md` D1.1 | quoted / R |
| p-nets have β = 2 for every p; flat floor would allow ½log₂p | `notes.md` §1.2 (table rows (a), (d)) | R (`review-sat3.md` did not object) |
| Items (1)–(4) | see Sections 4–7 below | as there |

## Section 2 (setting)

| statement | source | status |
|---|---|---|
| D1 cost, level value, engine class, log-exponent | `research/ports/c1d1/notes.md` D1.1; `attain-notes.md` §1.1 | definitions |
| Net counts E_gen, E_coll, E_other (2.1) | `q1-notes.md` §2.1; recounted by referee `review-q1.md` §2(iv) | P (rank counts) |
| X_q(P), X₄ (16 nodes, 48 edges), E_D (8 wires) | `q1-notes.md` §4.2 | definitions |
| Placement, b_k, s^k_e, value, F_CAT; balance Def. 2.1 | `notes.md` §2, `q1-notes.md` §0 | definitions |
| Full p-net level balanced (both sides g²−1) | `notes.md` Cor. 3.4; `review-sat3.md` item 1(iii) | P |
| Imported 2.2 (a) Prop. C.3, (b) Def. D.1, (c) thm_alt, (d) thm_alt_rank_price | `scratchpad/fm/paper.txt` l. 1608, 1698–1714; `research/ports/note-contracting-eth.md` §2.1 | I |
| CAT(0) definition, CN inequality (2.2) | `fm/paper.txt` Lemma C.4(a); BH99 | quoted / classical |
| Theorem R, C1-AN (power-saving 3-SAT from contracting) | `research/ports/note-contracting-eth.md` §3, §5.3 (status lines there) | R (advice form); uniform form by audit |
| Prop. 2.3 price method (★) | `research/vpvnp/b2/notebook.md` §1; `notes.md` §2 ("refereed") | R |

## Section 3 (CAT(0) inequalities)

| statement | source | status |
|---|---|---|
| Convexity of the metric along pairs of geodesics | BH99 Prop. II.2.2; Lean `dist_interp_le` | classical (+ Lean) |
| Prop. 3.1 two bimedians (weighted t) | `notes.md` Prop. 3.1; `review-sat3.md` item 1; `review-thmW.md` §2; Lean `Bimedian.lean` `bimedian_weighted`, `bimedian_half`, `bimedian_inner_eq` | PL |
| Thm. 3.2 two-merge cap | `notes.md` Thm. 3.2; `review-sat3.md` item 1 | P |
| Cor. 3.3 cap on p-nets √(g/(2(g+1))) | `notes.md` Cor. 3.4; `q1-notes.md` Thm. A proof; `review-q1.md` §2(i) | P |
| K₄: min_k b_k ≤ 2√2, attained by flat | `notes.md` Cor. 3.3; `review-sat3.md` item 1(ii) | R |
| Δ₃: min_k b_k ≤ 9/√2 | `notes.md` §3 last bullet | P (Thm 3.2 per pair) |

## Section 4 (Theorem A)

| statement | source | status |
|---|---|---|
| Lemma 4.1 (common adapted basis; d well defined) | `q1-notes.md` Lemma 1.1; `review-q1.md` §1 | R (standard) |
| Subspace formula d² = dim(U+U′) − dim(U∩U′) | `q1-notes.md` §1; `review-q1.md` §1 | R |
| Fact 4.2 C_N(q) = Cone(Δ) × ℝ, CAT(0) | `q1-notes.md` Fact 1.2; `review-q1.md` §1 (identification checked); BH99 II.10A.4, II.3.14 | classical |
| Lemma 4.3 far legs at point hubs | `q1-notes.md` Lemma 1.4; `review-q1.md` Minor | P |
| Prop. 4.4 generic-edge legs, s → 1 | `q1-notes.md` Prop. 2.1; `review-q1.md` §2 | P |
| Rank-one edges: saving √2 in one class, 0 elsewhere; E/(g+1) per merge | `q1-notes.md` §2.2; `review-q1.md` §2(ii) | P |
| Thm. 4.5 (Theorem A), bounds on F_CAT, F_CAT(C) = 1/√2 for balanced generic C | `q1-notes.md` §2.2 [R]; `review-q1.md` §2 ("correct, can be [R]") | P |
| Single wire: cap 1 (balance needed) | `review-q1.md` §2′ | R |
| Remark: mechanism; m = 1 gives Σ_k s ≤ √2 (Lemma 6.1) | `q1-notes.md` §2.2, Lemma 6.1; `review-q1.md` §6b | R |
| Cor. 4.6 quotients (1/√2)(1−q^{−m})(1−q^{1−m}) | `q1-notes.md` Cor. 2.2; `review-q1.md` §2(v) | R |
| Numbers 0.999950; 0.48279/0.58247/0.64111 vs 0.48284/0.58252/0.64115; caps 0.63246/0.66667/0.68599 | `review-q1.md` §2 table (referee's `refQ1/t_place.py`); formulas recomputed for this file | N |
| Rust reproduction 0.482843, 0.582516 (merge average; min_k 0.433, 0.569 by tie-breaking) | `s3-experiments.md` §5c | N |

## Section 5 (price barrier)

| statement | source | status |
|---|---|---|
| Thm. 5.1 (Theorem B), Steps 0–6 | `q1-notes.md` §3; `review-q1.md` §3 ("correct [D on thm_alt_rank_price]") | R; C (¬contracting; Imported 2.2(a),(d)) |
| Step 2 checked by explicit ι (two cases, 0 failures); restriction of scalars √s-isometry | `review-q1.md` §3 (`refQ1/t_step2.py`, `t_metric.py`) | N |
| Odd q price statement open | `q1-notes.md` §8 item 2; `review-q1.md` §3 | open |
| Hull of Sub(F_q^N) = union of cubes (Cor. 3.2 of notes) | `q1-notes.md` Cor. 3.2; `review-q1.md` §3 | R |
| Thm. 5.2 (Theorem C) fixed configuration | `q1-notes.md` §4.1 | R (via B and (★)); C |
| Cor. 5.3 per-level form, constant 1.13 = 3/√2 − 1, λ₀ depends on g | `q1-notes.md` §4.1; `review-q1.md` §4 (S′(b)) | R; C |
| Lemma 5.4 (a) partition into X_q copies, (b) X_q balanced, (c) E_D balanced | `q1-notes.md` Lemma 4.1, §4.2; `review-q1.md` §§4–5 | P |
| Partition numbers 1/28/560 copies, remainders; X₃(P) balance for 11 slope sets; b_k = 5.656851 | `review-q1.md` §4, §5 | N |
| Cor. 5.5 positive target; floors 8λ/√2 and 48λ/√2 | `q1-notes.md` §4.2; `review-q1.md` §5 | R; C |
| E_D union of four AN crossings per pair of merges | `q1-notes.md` §4.2; `review-q1.md` §5 (`t_misc.py`) | R |
| Thm. 5.6 (Theorem D′ / S′(a)) per-copy engines ⇒ contracting over k̄ | `q1-notes.md` §4.3; `review-q1.md` §4 (incl. the k̄ wording fix) | R; C (also Theorem R / C1-AN) |
| Not covered: whole-level identities, non-product term sets; thresholds 0.7075/0.79 conjectural | `review-q1.md` §4; `review-sat3.md` item 5; `notes.md` §6 banner | as stated |
| §5.5 tree products: Thm 4.3 (product hull), Δ₃ ≥ 2/3 (nine tripods), 0.6124 limit, finite-g 0.5410/0.5729/0.5915 | `notes.md` Thms 4.3, 5.2, 5.4; `review-sat3.md` items 3, 4(i), 4(iii) | R; C (price form); N (finite-g values) |

## Section 6 (Theorem W)

| statement | source | status |
|---|---|---|
| Class of covers, leg invariant, moves M0/M1, circle covering, Khoruzhii inside | `attain-notes.md` §5.1; `review-thmW.md` §4 (repairs adopted) | R (definitions) |
| Certified cost (6.1), c_k ≤ cost_k | `attain-notes.md` §5.1; `review-thmW.md` §1 | P |
| (S1), (S2) | `attain-notes.md` §5.1; `review-thmW.md` §4 (leaf step) | P |
| Lemma 6.1 (Lemma S) with full proof | `attain-notes.md` §5.3; `review-thmW.md` §2 ("correct [R]"); Lean `LemmaS.lean` (`lemmaS_core`, `lemmaS_interp`, `lemmaS_inner`, `Nc_le`, `Nb_le`, `circle_of_linear`, `circle_of_sSup`), note `lean-lemmaS.md` | PL (core; scope in §11) |
| Lemma S tests: 503 instances in ℝ², ℝ³, star trees (table of §2; the verdict line says "650+"), ℓ¹/ℓ^∞ violations up to −0.59 | `review-thmW.md` §2 | N |
| Lemma 6.2 (zero loss) | `attain-notes.md` Lemma 5.3; `review-lemma53.md` (verdict: correct; presentational repairs; finite parts recomputed in interval arithmetic, 7380 pairs) | R (see "downgrades/updates" below); uses quoted (K2) [BO16] |
| Referee of W: loss 0 for energies ≤ 300 exhaustively, grid to 1200 | `review-thmW.md` §3 | N |
| Lemma 5.2 fallback ε ≥ κ′ ≈ 2.6 bits | `attain-notes.md` Lemma 5.2; `review-thmW.md` §3 | R |
| Thm. 6.3 (Theorem W) with ε-term; exact with Lemma 6.2 | `attain-notes.md` §5.3; `review-thmW.md` §§1–5 | R |
| "Barrier for a proof method"; Ψ₄ rank 7 vs 20, Ψ₂₄ rank 15 vs 25 | `attain-notes.md` §5.3 ("What Theorem W bounds"); `review-thmW.md` §1 (`refW/psi_ranks.py`) | R; N |
| Cor. 6.4 certified value ≥ 1/√2 − ((q+1)/√2 − 1)/(g+1), odd q included; Δ₃ ≥ 2/3; window [0.4828, 0.6243] at g = 4 | `attain-notes.md` §5.3 Consequences, Addendum §6; `review-thmW.md` §9; `q1-notes.md` §7 | R |
| Prop. 6.5 rectangle piece (1/√2, 1/√2, 3/2) | `attain-notes.md` §1.2, §2.2; `review-thmW.md` §7 (correction 3/2) | R |
| Table 1 level-1 values | `attain-notes.md` §2.1 (`attain/game1.py`); `review-thmW.md` §7 reproduces K₄, AG(2,3) | N |

## Section 7 (Theorem T)

| statement | source | status |
|---|---|---|
| f_{K,λ} = f_{T_K(λ)} (AN-ETH Def. 3) | `q2-notes.md` §5; `review-q2.md` item 2 | R |
| Ports definition (EG Def. 11.1) | `research/ports/note-contracting-eth.md` §2.3; `review-q2.md` item 1 | I |
| Imported 7.1 (HC Thm 3.1), 7.2 (IM Thm 7.1) | `q2-notes.md` §1.2, Cor. T2 (quotes with line numbers); `review-q2.md` items 1, 7 | I |
| Lemma 7.3 (Lemma N), K ≥ 4; false at K = 2 | `q2-notes.md` §2.2; `review-q2.md` item 6; Lean `research/ports/lean/PortsLean/LemmaN.lean` `LemmaN.lemmaN`, `LemmaN.lemmaN_false_K2`, note `lean-lemmaN.md` | PL |
| Cor. N1/N3 consequences (rows as sites prove nothing; literal Q2 false) | `q2-notes.md` §2.2; `review-q2.md` item 6 | P |
| Lemma 7.4 star lemma | `q2-notes.md` §3.3; `review-q2.md` item 3 (explicit contraction K = 3, 4); Lean arithmetic only (`star_row_bits`, `star_hosted_bits`, `star_overhead`) | P (tensor part not in Lean) |
| Lemma 7.5 (Lemma L) | `q2-notes.md` §3.3; `review-q2.md` item 2 | P |
| Thm. 7.6 (Theorem T) | `q2-notes.md` §3.3; `review-q2.md`; arithmetic `LemmaN.thmT_arith` | R; C (Imported 7.1) |
| Oblivious algebraic definition; AN-ETH engine qualifies | `q2-notes.md` §0, §5; `review-q2.md` item 4 | R |
| Cor. 7.7 (Cor. T2) | `q2-notes.md` Cor. T2; `review-q2.md` items 4, 1 | R; C (7.1, 7.2) |
| Referee's sentence on what may be claimed | `review-q2.md` last section (paraphrased with all its qualifiers) | as stated |
| Tower: geometric mean ≥ 1/√2 | `q2-notes.md` §4; `review-q2.md` "§4 tower statement" | R; C |
| What the referee did/did not verify in HC | `review-q2.md` item 7 | as stated |

## Section 8 (open)

| statement | source | status |
|---|---|---|
| Prop. 8.1 (corrected Prop. 6.2), counterexample without transversality | `q1-notes.md` Prop. 6.2; `review-q1.md` §6a | R |
| Point hubs give Δ₃ ≤ 1/3 under the hypothesis; F_CAT(Δ₃) ∈ [2/3, 1/√2] | `q1-notes.md` §6.4; `q1-cyclic.md` §0 item 5 | R / summary |
| Convex relaxation gives 19.091883 = 27/√2 up to 1665 points; Euclidean forcing still cap unless barycentres | `q1-cyclic.md` §§1.2–1.3 | N, U |
| Lemmas 2.1 (flat hub hull), 2.2 (fins) | `q1-cyclic.md` §2 | U |
| Equality analysis (tripod branch ends excluded) | `q1-cyclic.md` §3 | U |
| Searches land on Γ = 36 (trees, cones over 15 graphs, C₃(F₂), C₃(F₃)) | `s3-experiments.md` §§3.3, 5b, 5c | N |
| Full nets g = 3, 5: 0.5202, 0.5519 vs flat 0.4979, 0.5244 | `s3-experiments.md` §4 | N |
| Cyclic Z_g limit of subgroup construction 0.5857 | `review-sat3.md` 4(iii) (`refsat3/transfer.py`) | N |
| Table 2, type A values (Z₅ and Δ₃) | `attain-notes.md` §10.3 (`attain/out3/`); out4 driver reruns | N |
| Table 2, type B values: Z₅ at (½,½,0), (0.48,0.48,0.04), (0.45,0.45,0.1), (0.4,0.4,0.2), uniform; Δ₃ uniform and (½,½,0) | `attain/out4/B_z5_50.txt`, `B_z5_48.txt`, `B_z5_45.txt`, `B_z5_40.txt`, `B_z5_uni.txt`, `B_d3_uniform.txt`, `B_test_d3.txt`; `research/next/LOGBOOK.md` entry "H45, type B (executor, interim)" | N, U (not written up in `attain-notes.md`; §11 there does not exist yet; `B_z5_40`, `B_z5_45`, `B_z5_uni` were untracked when checked) |
| Uniform-weight gain 0.5% (0.773799 → 0.769856) | `attain/out4/B_z5_uni.txt` (computed: 0.51%) | N |
| Δ₃ game value 0.89190 → ≤ 0.89102 (type A) | `attain-notes.md` §10.3 | N |
| O(1/g) window 0.354/(g+1) to 1.121/(g+1) | `q1-notes.md` §2.2 "Finite g"; `review-q1.md` Minor | R |

## Sections 9–12

| statement | source | status |
|---|---|---|
| Limitations | summary of the above | — |
| Related work: Majdoddin Prop. 4.23, Prop. 4.8 reading | `attain-notes.md` §4.1; `prior-barriers.md` §3 | as read in the notes |
| de Brito, Fradj, Sra, Khoruzhii summaries | `hexagon-survey.md` §§c.1, c.2, c.5 | as read in the notes |
| OpenAI EG §11.1 (Grassmannian gap ⇒ ports) | `research/ports/note-contracting-eth.md` §0 "Prior work" | as read in the notes |
| Lean names, no sorry, axioms | `research/ports/lean/PortsLean/{Bimedian,LemmaS,LemmaN}.lean`; re-checked here with `lake env lean` on a scratch file printing axioms of 14 theorems: all `[propext, Classical.choice, Quot.sound]`; `grep -c sorry` = 0 in the three files | checked |
| Provenance section | task instructions | — |

## Statements whose status differs from the brief, or that could not be verified

1. **Lemma 5.3 (zero loss).** The brief says "NOT yet refereed". At the time of writing the repository contains
   `research/sat3/review-lemma53.md` (verdict: correct, no real gap, presentational repairs) and a logbook entry
   "Zero-loss Lemma 5.3 refereed: correct, no gap". The paper therefore says that the lemma was refereed by a
   separate AI referee after the other reports, lists the requested repairs, and notes that the referee took the
   quoted bound (K2) as given. `attain-notes.md` itself still tags it [D].
2. **Lemma N in Lean.** Not in the brief; `PortsLean/LemmaN.lean` appeared during writing (commit e97d956). The paper
   marks Lemma N "proved here and in Lean" and says that only the arithmetic of the star lemma is formalised.
3. **Type-B depth-2 game (§11 of attain-notes).** The brief cites attain-notes §10–§11; §11 does not exist in
   `attain-notes.md`. Values are taken from the raw outputs in `attain/out4/` and the logbook interim entry, and are
   marked numerical and not refereed.
4. **Two-sided cut lemma, Δ₃ level-1 0.9085, etc.** Used only as context; statuses as in the notes.
5. **Bessenrodt–Ono bibliographic data.** Only "Ann. Comb. (2016); arXiv:1403.3352" as given in the notes; volume
   and pages not checked, so not given. Lehmer is mentioned without a bibliography entry because no source text
   of his paper was read.
6. **Theorem R / C1-AN.** Quoted from `research/ports/note-contracting-eth.md` with its own status (non-uniform form
   refereed; uniform form by audit); not re-checked here.
7. **"Proved here" items** were checked against the referee reports and re-derived while writing (Prop. 3.1,
   Thm. 3.2, Cor. 3.3, Lemma 4.3, Prop. 4.4, Thm. 4.5, Lemma 5.4, Lemma S, Lemma N, star lemma, Lemma L). The
   numerical formulas for Theorem A and the level-1 two-merge values were recomputed (Python one-liners, not kept):
   0.48284, 0.58252, 0.64115, 0.52426, 0.55796; caps 0.63246, 0.66667, 0.68599; two-merge 0.569036, 0.603553,
   0.624264, 0.638071; 27/√2 = 19.091883; 9√3 = 15.588457; 8/√2 = 5.656854.
