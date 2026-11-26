# Referee review of `main.tex` ("Three barriers at exponent one half for the counting engines")

Scope: fidelity of every statement to the source notes after their referee corrections; the proofs printed in
full; the printed numbers against the sources named in `CHECKS.md`; the bibliography against texts available in
the project; the Lean identifiers; the prose. The mathematics was not refereed again from scratch.

**Verdict.** After the fixes below the paper is accurate to its sources. Before the fixes it had no false theorem.
It did have one factual error in the opening sentence (the running time), several overclaims in the abstract and
introduction (exactness of Theorem W for every circle-covering identity, the class of Theorem T, "explain why this
does not happen"), two misreported numerical checks (Lemma S test count, Rust reproduction), one overclaim about
which tree products are prices, and a few undefined symbols (σ_ℓ, C₀, e(K), a doubly used κ). The proofs printed in
full (bimedian inequality, two-merge cap, cap on p-nets, far-leg lemma, generic-edge legs, Theorem A, Lemma 5.4
balance of X_q and E_D, Lemma S, Lemma N, star lemma, Lemma L) were read line by line. All constants and signs check,
and the gaps found are presentational. The build is clean: no errors, warnings, overfull boxes or undefined
references, and bibtex reports 0 warnings. The paper now has **17 pages**; it had 16, and the bibliography now runs
onto page 17.

Statuses checked and found right: Theorem W bounds certified costs only (§6, "What Theorem W bounds"). Theorem D′
covers per-copy engines only, with the conclusion over k̄. Price statements need q = 2^s (Thm 5.1, 5.2, Cor 5.3,
§8 "Odd q"). Theorem T concerns straight-line programs computing f_{K,λ} as a polynomial, in asymptotic form, and
only characteristic 0 is used for the 3-SAT consequence. Prop. 8.1 carries the transversality hypothesis, and its
counterexample is stated. Lemma N is stated for K ≥ 4, and its failure at K = 2 is in Lean.

## Findings

**F1 (factual, abstract and §1.1). Running time.** The paper said both labs claim time 2^{O(n/√log n)}. Both
preprints claim 2^{O(n log log n/√log n)}: AN-ETH Thm D(b), "2^{Ck² n log log n/√log n}", and OA-ETH Thm 1.1. The
bound without log log n holds only for formulas with O(n) clauses (AN footnote 1; OA Thm 1.1, second bound).
*Changed:* the abstract now gives 2^{O(n log log n/√log n)}. §1.1 gives both bounds, with the sparse case marked.

**F2 (overclaim, abstract).** "Four results that explain why this does not happen with the present methods." The
results bound what certain methods can certify or prove. They do not show that net levels cannot beat 1/√2: cyclic
nets and true versus certified costs are open. *Changed:* "four results that bound what the present methods give on
such levels". I also added one clause linking the four results to the title's "three barriers": (1) supplies the
geometry, and (2)–(4) are the barriers. I added "No lower bound for 3-SAT is claimed."

**F3 (overclaim, abstract item (3), §1.2 item (3), Cor. 6.4, §8.2). Exactness of Theorem W at all depths.**
Theorem W has the defect term D·Σε_s. The zero-loss lemma gives ε = 0 for Anthropic's identity (B.2) only.
`review-thmW.md` §4 says it did not check whether Khoruzhii's identity has zero loss. The abstract said "covers
generated from crossing identities … at every depth". Item (3) said "with the zero-loss lemma this holds exactly at
all depths" for all circle-covering identities. Cor. 6.4 stated the bound for "every crossing-generated cover".
*Changed:* the abstract now names covers generated from Anthropic's identity. Item (3) states the defect term and
the zero defect of Anthropic's identity. Cor. 6.4 is restricted to identities of defect 0, with one sentence on
positive defect. §8.2 now says "built from Anthropic's identity".

**F4 (overclaim / imprecision, abstract item (4), §1.2 item (4) and the paragraph after it). Theorem T's class and
hypotheses.** The abstract mentioned only the consequence (two OpenAI theorems). It did not state Theorem T itself
(one theorem), the even-K and wire-length regime, or "deterministic". The paragraph after the list said Statement
(4) "covers all algebraic algorithms in its regime". The referee (`review-q2.md`, item 4 and the final sentence)
limits it to straight-line programs that compute f_{K,λ} as a polynomial identity, and excludes programs correct
only on bounded integer tables. *Changed:* the abstract now gives Theorem T with its hypothesis and regime, then the
consequence over ℚ. In §1.2 the consequence names its class and exponent, adds "deterministic" and "unspecified
absolute constants", and says that bounded-table algorithms are not covered.

**F5 (prose, §1.2).** "Ordered by strength of hypothesis" was false: the order is none, ¬contracting, none, OpenAI.
"We consolidate one day's results" was filler, and the notes are dated 26–27 Nov. *Changed:* "We collect the
results obtained … on 26–27 November 2026". §12 now gives the same dates.

**F6 (hidden hypothesis, §1.2 item (1), Thm 3.2, Cor 3.3, the paragraph after the list).** "No price over any
field proves more" and "every price, under any hypothesis" rest on Anthropic's Prop. C.3 (Imported 2.2(a),
unrefereed). The CAT(0) inequalities themselves need nothing. *Changed:* the dependence on Imported 2.2(a) is now
stated in all four places.

**F7 (Lemma S numerics, §6.2).** The paper said "no violation in more than 650 instances in ℝ², ℝ³ and metric trees".
The referee's table (`review-thmW.md` §2) has 150 + 100 + 253 = 503 instances in CAT(0) spaces, in star trees with 3
or 4 arms, and 240 in ℓ¹/ℓ^∞. The "650+" comes from the report's own verdict line, which disagrees with its table.
*Changed:* the paper now gives 503 (150/100/253) in star trees, and "violations up to about 0.59 among 240 instances"
in the normed planes. The CHECKS.md row is updated.

**F8 (numerics misreported, §4 numerical checks).** "An independent Rust implementation reproduces 0.482843 and
0.582516." In `s3-experiments.md` §5c these are merge averages. With that code's tie-breaking, min_k b_k/E is 0.433
and 0.569. *Changed:* the paper says the Rust check confirms the averaged form only, and gives the min_k values. The
CHECKS.md row is updated.

**F9 (zero-loss paragraph, §6.3).** (a) "An exact check of all 7260 pairs" overstates it. `review-lemma53.md` §3
says `zeroloss.py` uses 60-digit floats without an error bound; only the referee's recomputation is rigorous.
(b) The Lehmer/Bessenrodt–Ono bound was "checked against that source". That source is not in the project, and both
referees took it as given. (c) The analytic part for E ≥ 800 was missing from the list of proof parts.
*Changed:* all three are now stated. The referee's run is described as exact integers plus interval arithmetic over
7380 pairs with m₂ ≥ 1.

**F10 (notation clash, §6.3).** κ was defined as π/√3. Two lines later, "at least κ/ln 2 ≈ 2.6 bits" was used for
Lemma 5.2, whose constant is Anthropic's Lemma B.1 κ. Keeping these two constants apart is one of the referee's
requested repairs. *Changed:* the paper now writes κ_B/ln 2 for the Lemma 5.2 bound, with κ_B the constant of
Lemma B.1, and says that the bound is at least about 2.6 bits per crossing.

**F11 (overclaim, §5.5 tree products).** "Products of trees, which are prices when contracting fails (notes Thm
4.3)." Thm 4.3 covers finite ℓ²-products of spaces 𝕋_m × ℝ (m-pods with infinite arms), not arbitrary trees.
"Theorem A supersedes these values" holds for price floors only when q = 2^s. *Changed:* the paper now states
Thm 4.3's actual class. It says that Theorem A supersedes the tree values as CAT(0) values for every q, as price
floors only for q = 2^s, and gives no price statement for odd q.

**F12 (undefined notation, §7.1 after Lemma N).** In the missing-lemma inequality, σ_ℓ was undefined, and the
unit-sites hypothesis of `prior-barriers.md` §5.3 was missing, so the claim could not be checked. *Changed:* the
paper now states the hypothesis (sites at distance 1 from a base point) and the definition
σ_ℓ = Σ_i (1 − d(x_i, y_{b(i)})), and adds the one-line derivation from Lemma N (q2-notes Cor. N3).

**F13 (proof of Theorem T).** (a) C₀ was used but never defined. *Changed:* the paper now says that q₀ = 2^{⌈C₀w⌉}
(HC, proof of Cor. 3.2), so b₀ = ⌈C₀w⌉ and λ₀(K) = 2b₀. (b) "Imported 7.1 bounds the latter by exp(…)" did not
give the direction. *Changed:* "bounds the size of the latter from below". (c) "T_K(λ) ≥ T_d^{⊗h}" used an
undefined order. *Changed:* "restricts row-wise to".

**F14 (undefined notation, §7, Cor. 7.7 and §1.2).** e(K) was used but never defined. *Changed:* a definition from
AN-ETH Def. 4 was added (cost C·2^{eK²λ}(B+λ)^C), with its relation to the log-exponent.

**F15 (missing hypotheses, §7 last paragraph).** "In a tower … Theorem T forces the geometric mean ≥ 1/√2" holds only
under no ports and HC Thm 3.1, for towers realised as polynomial-identity programs (`review-q2.md`, "§4 tower
statement"). *Changed:* these hypotheses and the source are now stated.

**F16 (imprecision, §8.3).** The O(1/g) window: 0.354/(g+1) is the cap only to first order in 1/g
(`q1-notes.md` §2.2 "Finite g"). *Changed:* the paper now says so, and says which end is the cap and which is the
placement.

**F17 (precision, Remark in §4).** Lemma 6.1 (Σ_k s ≤ √2 when node planes meet) is stated for hubs at points.
*Changed:* "with hubs at points" was added.

**F18 (status wording, §2.4 and §9).** The uniform form of Theorem R rests on "an audit … by one reader". Read
alone, this could suggest a human check. `research/ports/review-uniformity.md` is an agent report that built
nothing. *Changed:* "one AI reader, nothing built". In §9, the moot-barriers sentence now names Theorem R
(characteristic 0) and C1-AN (characteristic p, randomised), and says "price barriers".

**F19 (related work, §10).** (a) "None of these papers treats three merges or nets": Majdoddin discusses three
merges, as open, in §4.8. *Changed:* "proves a statement for … ; Majdoddin discusses three merges as open". (b) The
Fradj summary, "window costs above 1/√2", left out the asymptotic and fixed-density form
(`hexagon-survey.md` c.5). *Changed:* the paper now gives 1/√2 + η_J − C_J m^{−1/2}, with η_J > 0 unevaluated, for
isotropic Kleinian codes at fixed density. (c) "Contains the Grassmannian as its 0/1 points": the 0/1 points are all
subspaces. *Changed:* this is now said precisely. (d) "Two-merge barriers are now numerous" was filler.
*Changed:* "Several papers give barriers for two merges."

**F20 (proof wording, Prop. 3.1).** "By (CN) for m′ against m" did not say which geodesic or which test point.
*Changed:* the paper now says "with z = m on the geodesic from o′ to w′, then with z = o′, z = w′ on the geodesic from
o to w". The computation itself checks, including the cancellation of the brackets.

**F21 (notation, Thm 5.1 Step 5).** "1₀" was undefined. *Changed:* it is now 1_{{0}}, with 1_U the cube vertex of
the coordinate subspace U.

**F22 (proof details, Lemma 5.4(b),(c)).** The range of u (F_q²) and the form φ_x were left implicit. Part (c) uses
characteristic 2 for the sign and φ_x(x′) ≠ 0 for uniqueness. *Changed:* these are now stated, together with the
count (q²−1)(q²−q).

**F23 (undefined term, Cor. 5.5).** "Price floor" was undefined. *Changed:* a parenthetical definition through
Prop. 2.3 was added.

**F24 (prose, §6.3).** "The gap is real." was replaced by "Certificates and true costs do differ."

**F25 (table caption, Table 1).** The referee reproduced only the K₄ and AG(2,3) entries at (½,½,0) and at uniform
w, not every entry of those rows. *Changed:* the caption now says which entries were reproduced.

**F26 (bibliography: author field).** `AnthropicETH` and `AnthropicVP` named a model in the author field. The
Hexagon records (`scratchpad/hx/cand.txt`: 2610.00577, 2611.00954) list the author as "Anthropic". *Changed:* the
author field is now "Anthropic". One cited title, de Brito's, contains a product name. It is kept verbatim because
it is the paper's title.

**F27 (Lean section).** The second file was cited as `LemmaS.lean` relative to the previous path. *Changed:* the
full path is now given. I re-ran `#print axioms` with `lake env lean` (research/ports/lean, built library) on 17
theorems: the 14 the paper listed, plus `Nb_le`, `LemmaN.core` and `LemmaN.sum_cuts_same`. All 17 give
[propext, Classical.choice, Quot.sound]. `grep sorry` finds 0 in the three files. *Changed:* the sentence now lists
the 17 theorems.

## Checked and found correct (no change)

- **Numbers.** Theorem A formula values 0.48284/0.58252/0.64115. Caps 0.63246/0.66667/0.68599. Referee placement
  values 0.48279/0.58247/0.64111 and saving 0.999950 (`review-q1.md` §2). Partition 1/28/560 and remainders
  0.6/0.3333/0.1765. Eleven slope sets for X₃(P). E_D b_k = 5.656851. Window [0.4828, 0.6243]. 11 175 energy pairs,
  grid to 1200. Ψ₄ rank 7 vs 20 and Ψ₂₄ rank 15 vs 25. 7260 = 120·121/2. 7380 pairs. Table 1: all 23 entries
  against `attain-notes.md` §2.1. Table 2: every entry against `attain/out4/*.txt` (level 1 with 11 ratios, "after
  type A", "after type B"). 0.773945 with 9 ratios. Gain 0.773799 → 0.769856 = 0.51%. 0.89190 → 0.89102.
  Tree values 0.5202/0.5519 against flat 0.4979/0.5244, and 0.5857. 0.5410/0.5729/0.5915. 27/8 and 0.6124.
  19.091883 = 27/√2, at 1665 points. 108 automorphisms. 2√2 for K₄ and 9/√2 for Δ₃. 1.1213 = 3/√2 − 1.
- **Proofs.** The two-merge cap: convexity, the two CN steps, the balance cancellation (cross terms against
  Σ deg n), and Σ μ_k² E_k δ_k² = (E₁+E₂)/Λ². The cap on p-nets: the pair sum over C(p,2) pairs gives √(EE_×/2).
  Far-leg lemma: d² = |c+Tu|² + 1 − 2(c+Tu)_{i*}. Prop. 4.4: d² = (α−1)² + α² + 2β² = T² + ½. Rank-one recipe:
  saving u₁ − u_N = √2, other classes 0, E/(g+1) per merge. Theorem A identity
  (g−q)/√2 + 1 = (g+1)/√2 − ((q+1)/√2 − 1). Lemma S: the chain (i)–(iv), (1−t)N₁ + tN₂ ≤ β₁|z_az_c| + β₂|z_bz_d|,
  Λ(1−t) = a₁/|oo′| and the final circle. Lemma N averaging. Star lemma (i)–(iv) and Theorem T arithmetic
  ⌊λ/2⌋ ≥ λ/3, ⌊x/b₀⌋ ≥ x/(2b₀), giving K²λ/(12C₀√m). Lemma L substitution. Theorem B Steps 0–6 against
  `review-q1.md` §3.
- **Lean names.** Every identifier cited exists, with the statement the paper gives. `bimedian_weighted` uses six CN
  instances. `dist_interp_le` uses six CN instances and one auxiliary point. `lemmaS_core` has hypotheses
  h_rest = (i), h_parent = (ii) and hca…hcd = (iii), plus the bimedian bound. `lemmaS_interp` discharges (iii) and
  the bimedian bound from `IsCNInterp`. `LemmaN.lemmaN` has K ≥ 4, even K, and the cut chosen before y₀, y₁. The
  lab names `thm_alt`, `thm_alt_rank_price` (scratchpad `fm/repo/vp-vnp/Paper/Alternative.lean`) and
  `middle_count_bridge` (`survey/oa/lean/…/MiddleDecision.lean`) also exist.
- **Lab-paper citations.** These numbered results exist in the AN-VP text: Prop. B.2, Lemma A.2, Lemma A.3,
  Def. A.4, Prop. C.3, Lemma C.4, Def. D.1 (μ ≥ 2, 1 ≤ s, s² < μ) and Thm D.2. The paper's statements of them match.
  The disclaimer quotes are accurate: AN-VP l. 578, and the OpenAI README's "raw research data". HC Thm 3.1 and IM
  Thm 7.1 match the referee's quotes.
- **Repository paths.** Every `\src{…}` path exists.

## Bibliography: what could and could not be confirmed

Confirmed from texts in the project: AnthropicETH (title, date 26 Oct 2026, Hexagon 2610.00577), OpenAIETH (title;
17 Oct, revised 25 Oct), AnthropicVP (title, Hexagon 2611.00954), OpenAIEG, OpenAIHC and OpenAIIM (titles, date
24 Nov 2026), Maj26 (arXiv:2610.41622v1, 30 Oct), Sra26 (2611.01066, 25 Nov record), deBrito26 (2610.00692; record
date 31 Oct, PDF dated 30 Oct; author spelled "Carlos Stein Naves de Brito" in the record and "Carlos Stein Brito"
in the PDF), Fradj26 (2611.00627; record 19 Nov, PDF dated 17 Nov), Kho26 (Lemmata page, v1 2 Nov, last 4 Nov) and
Tul26barrier (2611.00149, 6 Nov).

Not available as texts in the project, so not confirmable here: **BO16** (Bessenrodt–Ono). Its title and
arXiv:1403.3352 come only from `attain-notes.md`, and the volume and pages are not given. **BH99**, **Lean4** and
**Mathlib20** are standard references whose data look right, but no copy is in the project. Nothing in the
bibliography looks invented.

## Not fixed

- The paper is 17 pages, not 16, because the abstract and introduction now carry their hypotheses. I did not cut
  content to win back the page.
- The type-B depth-2 values (Table 2, last column) are still only in raw outputs (`attain/out4/`) and a logbook
  entry. They are not written up or refereed, and the paper says so.
- `review-thmW.md` itself disagrees with itself (650+ against its table's 503). The paper now follows the table.
- The hypothesis that Theorem R's uniform form needs (the audit) and the unrefereed lab inputs (Prop. C.3,
  `thm_alt_rank_price`, HC Thm 3.1, IM Thm 7.1) are reported, not re-checked.
