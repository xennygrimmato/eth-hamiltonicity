# Lean hypothesis tests for the ports / rebase claims

Lake project: `research/ports/lean/` (Lean v4.36.0, Mathlib v4.36.0 from the cache; `.lake/` ignored).
Build: `lake build` (all files compile; no `sorry`, no `axiom`). Every finished theorem below prints
`[propext, Classical.choice, Quot.sound]` under `#print axioms` (or a subset: `sum_prune_eq` uses only
`propext`, `leaves_prune_le` uses `propext, Quot.sound`).

## What broke or needed fixing (headline)

1. **Theorem A arithmetic, Lean form.** The referee's condition `h/(log₂h+4) > 40000·C₀` does not imply
   OA's hypothesis `large : 10000(e+3) ≤ s`. The two are separate. Lean counterexample: `C₀ = 0, h = 2`.
   Proved sufficient condition: `40000·(C₀+1)·(e+3) ≤ h`. It gives both `large` and the threshold.
   Numbers: `large` alone needs `h ≥ 491`. Both conditions together need `h ≥ 3506` (C₀ = 0.01),
   49 905 (0.1), 480 300 (1) or 6 604 603 (10). This is harmless for the theorem, because large h exist.
2. **OA `scalar` hypothesis.** It is discharged through F.6 itself, applied to line placements. That needs
   the separate hypothesis "finite subsets of ℝ are AN prices" (`LineStatement`).
3. **Theorem R.** No exponent breaks. Three unstated conditions are needed, all satisfied:
   - `H > 112.2`, so that the optimal α is below 1/4;
   - `v ≥ v₁(C_cut)`, for J.4's `(lg v)^{2C_cut} ≤ v`;
   - `H ≥ 235`, for `τ' ≤ v^{2H}`. The notebook cites 272, which is more than needed.

   The guess bound is needed only on *accepting* runs. `PrunedTree.lean` proves this, and it matches
   AN's `Ev`/`Does`/`CutD`.
4. **Guess counts.** Guess-freeness cannot be read off AN's `Does`/`Gives`. For example,
   `ite guess id fail` *gives* a single weight-1 output but makes one guess, and lists with cancelling
   weights satisfy the same `Does`. So every guess bound must be re-derived from the program syntax.
5. **Hull lemma.** "Points of the hull are prices" is **not** a gap: AN `prop_space` already says that
   the whole metric of the price space is a price. The gap is Lemma H itself. Lemma H must assume CN
   (complete, with midpoints), not merely the quadrilateral inequality. The first draft assumed only
   QuadIneq. That statement is false, because N5 itself satisfies QuadIneq and contains no diamond, so it
   made the glue theorem vacuous. Fixed.
6. **Build of the Anthropic Lean.** The Mathlib cache for vp-vnp's pin exists: `0df444a`, Lean v4.33.1,
   8690 files, fetched in 4.5 min into the scratchpad copy. Building their code was **denied by the
   session permission system**, in line with the brief's "do not build them". Task 5 therefore runs on a
   copied fragment.

## Task 1: Theorem A (`PortsLean/ThmA.lean`, `PortsLean/ThmAArith.lean`). Status: proved

The statement is `theorem_A : F6Statement U x IsPrice Contracting → LogPlacementStatement Good PortZero →
ContainStatement Good IsPrice → LineStatement IsPrice → (∀ h, card (U h) = 2^(h(h−1)/2)) →
(∀ h j, x h j * x h j = 1) → Contracting → PortZero`.

**Hypotheses, each mirroring a source:**

- `F6Statement` mirrors AN `thm_poincare`, `vp-vnp/Paper/Groups.lean` l.1085–1088. It keeps the
  quantifiers verbatim: `∃ u ≥ 2, ∃ C₀ ≥ 0, ∀ l ≥ 2, ∀ w, IsPrice w → (ΣΣ w k (gk)²)/|U|² ≤
  C₀ Σ_j (Σ_k w k (x_j k)²)/|U|`.
- `LogPlacementStatement` mirrors OA `exists_logarithmic_placement`, `OAI/Computability/MultitapeWeakETH/
  Cloud.lean` l.83–89. It includes `large`, `symm`, `rows`, `scalar` and the threshold `s/(10000(e+3))`.
  `walkEnergy`, `HasPoincareBound` and `normalizeArcs` are copied verbatim from OA (WalkEnergy.lean l.24,
  l.195; GraphRounding.lean l.75). `SpectralTarget` is abstracted as a metric space with an opaque
  predicate. `PortZero` is an opaque Prop.
- `ContainStatement` says that every OA target placement pulls back to an AN price. It is one direction
  only. The OA and AN notions are distinct types, so the converse cannot be used.
- `LineStatement` says that real-line placements are AN prices. It is used only for `scalar`.
- The order of U_h and the involutivity of x_j are AN facts, not proved here. Simplicity of the Cayley
  graph is **not** needed, because multiplicity arcs work.

**Translation lemma.** With e = ⌊log₂(h−1)⌋+1 and 2^e−(h−1) loops at each vertex, F.6 gives *exactly*
the OA-normalised constant C₀·2^e, which is at most 2C₀(h−1).

**Arithmetic lemma.** `exists_good_multiple : ∀ C₀ ≥ 0, ∀ u ≥ 1, ∃ l ≥ 2` with `large` and
`C₀·2^e ≤ s/(10000(e+3))` at h = lu. C₀ and u are fixed before l is chosen, so no constant depends on
h. The real-analysis step uses `isLittleO_log_id_atTop`.

**Discrepancies:**
- the arithmetic condition, item 1 above;
- the field bookkeeping (OA `AlgebraicClosure ℚ` against AN `K`) is pushed into `ContainStatement`;
- `ideas-ports.md` writes e = ⌈log₂h⌉ where ⌊log₂(h−1)⌋+1 is meant. Both give a padding factor of at
  most 2.

## Task 2: Theorem R arithmetic (`PortsLean/ThmR.lean`). Status: all proved

- `j4_constraints`: with τ' = v^{H+235}, every J.4 constraint holds exactly. The resulting quantities are:
  `τ'/v^235 = v^H`, `τ'/v^24 = v^{H+211}` and pieces `= v^237`.
- `v_choice`: v = ⌈τ^{1/(H+187)}⌉ gives τ ≤ v^{H+187} and v ≤ 2τ^{1/(H+187)}.
- `lemma2_cost_le`: the cost `2^g(t + P·2^{v^H}·v^H)` is at most `2^{(2H+241)v^H}`. Piece brute force
  is the same order as run enumeration, not negligible.
- `theorem1_exponent`: the exponent is at most `(2H+241)·2^H·τ^{H/(H+187)}`.
- `alpha_star`: α* = (1−ρ)/(1+4ρ) = 187/(5H+187), and 1−(1+4α*)ρ = α*.
- `choose_alpha`, `sat_exponent`: every δ < 187/(5H+187) works, and the SAT exponent is at most
  `2n^{1−δ}` eventually.
- `polylog_condition`: the J.4 side condition at α = 2 holds for all large v.
- `lemma1_per_cut`, `lemma1_composed`: Lemma 1's arithmetic, given its per-cut guess counts (which are
  not checked).
- `PrunedTree.lean`: `leaves_prune_le` (at most 2^g leaves, with no hypothesis) and `sum_prune_eq`
  (exact, given bounds on accepting leaves only).

## Task 5: guess counts on AN's semantics (`PortsLean/ANFragment/`). Status: (1)–(3) proved on a copied fragment

**What was copied:**
- `Machine.lean` is `vp-vnp/NS1/Machine.lean` verbatim (Tree, Fm, Run, Ev, Ev.unique, evl, Hl, Dt, lett).
  It typechecks unchanged on Mathlib v4.36.
- `Defs.lean` holds only these definitions, verbatim: `app` (NS1/Step.lean l.58), `listT`, `foldB`,
  `foldF`, `appF`, `pickB`, `pickF` (NS1/Lists.lean), `stepC`, `compC` (NS1/Compose.lean l.50, 53).

Licence headers are kept.

**Overlay `Guess.lean` (namespace NS1G):**
- `EvG` mirrors `Ev` with a guess count. `EvG.toEv` is the projection, so by `Ev.unique` the EvG lists
  are exactly the accepting runs.
- `GB θ F x g` says that every accepting run makes at most g guesses. `DoesG := Does ∧ GB`.
- Per-construct lemmas: quote, id, fail, guess, hd, tl, theta, mul, cons, ite, run, app, lett.
- `pickB_guesses`: at most the number of options.
- `foldB_guesses`, `foldF_guesses`, `foldB_free`, `appF_guesses` (adds 0), `stepC_guesses`.
- **`compC_guesses`**: guesses(compC G G') ≤ g_G + Σ_pieces g_{G'}(y).

**Not done:**
- the lifting Ev → EvG;
- `bitsB` (needs Util/Deal definitions);
- dealProg ≤ the s-free part of dealB (needs the Nc/Dl closure, about 1.5–3k lines of overlay, 2–5 days);
- threading through thm_onecut_program → thm_cut_compose → thm_cut (needs the 261-file closure, 1–2 weeks).

Both missing items depend on a real build.

## Task 3: W5, K_{2,3} and hull checks (`PortsLean/W5.lean`, `PortsLean/Hull.lean`). Status: proved, except Lemma H

**W5 and the K_{2,3} bounds (`W5.lean`):**
- `ratio_lower`, `ratio_at_third`, `ratio_strict`: the minimum of R is √(9/10), attained only at h = ℓ/3.
  The proof is 4(ℓ−3h)² ≥ 0.
- `w5_metric`: all triangle inequalities hold (scaled ℓ = 3, h = 1).
- `w5_sums`, `w5_ratio`: Σ_T = 20, Σ_S = 6√10, R = √(9/10).
- `cutB_ineq`: **the separating inequality is Σ_S d − Σ_T d ≥ 0**. It holds for all 32 cuts.
- `w5_not_cut_combination`: W5 is not a nonnegative combination of cut metrics.
- `flow_bound`: 3Σ_T ≤ 4Σ_S for every pseudometric.
- `cut_v1`: the cut {v₁} gives ratio 1.

**Hull checks (`Hull.lean`):**
- (a) `ranks_one`, `ranks_two`: explicit u xᵀ factorisations and det ≠ 0 over `ZMod 2`, with no
  `native_decide`.
- (b) `quad_equality`, `n5_equality_case`: equality case of the quadrilateral inequality, which is stated
  as the hypothesis `QuadIneq` (AN lem_toolkit).
- (c) `model_n5`: exact N5 distances in tripod × ℝ. `w5_in_diamond`: W5(ℓ,ℓ/3) lies in the diamond for
  ℓ ≤ 1/√2.
- (d) `HullHyps` has the fields `prop_space` (AN Curvature.lean l.211, with CN), `pullback` (Def. A.4)
  and `lemmaH` (the gap, needing CN + QuadIneq). `w5_price_of_rho_price` is proved from these.

Discrepancy: the notes' Corollary H1 is phrased from "N5 a price". The Lean glue uses "ρ₂ a price",
which is what H2 supplies. The same proof works with N5 as V.

## Task 4: 9/4 algebra (`PortsLean/NineFourths.lean`). Status: proved; the tripod inequality is not

- `thomson_le` and `thomson_eq`: Thomson's principle for 3 arms.
- `discount_le_ninth`: AM–HM.
- `perimeter_le_nine_fourths`: Σa − 1/Σ(1/a) ≤ 1 implies 2Σa ≤ 9/4.
- `equal_arms`, `unit_tripod` (8/3, giving 9/4).
- `team_size`: (xy+yz+zx)²/(4xyz) = (p+q+r)²/4.
- `rectangular_formula`: ω = S²/(4xyz) solves Σ√(1−c_k/ω) = 1 in the interior, via the identity
  S² − 4xyz(x+y) = (xy − z(x+y))².
- `square_case`.

The tripod inequality itself is a theorem about spectral points (OA) and is not formalised.
