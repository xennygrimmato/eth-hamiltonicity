# Lean blueprint: exact #HC (Result 2)

Source of truth: `exact-hc-theorem.md`. Section and lemma numbers below refer to it. Lean files live
in `lean/EthFollowup/ExactHC/`, namespace `EthFollowup.ExactHC`.

The files must compile both in `lean/` (Lean v4.34.1, Mathlib d13f23b) and in Anthropic's workspace
(Lean v4.33.1, Mathlib 0df444a), where the final theorem is assembled.

**Rules for agents:**
* Import only the Mathlib modules you need; avoid `import Mathlib`, because of memory.
* Check files with `lake env lean <file>`. Do not run `lake build` (concurrent builds race). The
  coordinator integrates and builds.
* No `sorry` in delivered files. Do not run git.

## Layer M (mathematics)

| Id | Statement (write-up ref) | File | Depends on | Status |
|---|---|---|---|---|
| M0 | n·#HC = Σ_{2-factors} τ (Lemma 3.1) | `ExactHC.lean` | — | **done** |
| M1 | Concrete exterior algebra Λ(Γ) over ℤ (basis e_S, merge sign); Fact 2.1; Koszul rule (Lemma 2.2); block factorisation of top coefficients (Lemma 2.3); product of linear forms = det · top monomial | `ExactHC/Grassmann.lean` | — | **done** (906 lines; checked in both environments) |
| M2 | Reduced incidence matrix of F with \|F\| = n−1: det² = [F is a spanning tree] (inside Lemma 3.3) | `ExactHC/Incidence.lean` | — | **done** (det² = [tree], sum form; checked in both environments) |
| M3 | Chord/parity combinatorics: Lemma 4.3, Prop. 4.4 (ε = Πσ_a · interleaving), Lemma 4.5 (parity copies) | `ExactHC/SignRule.lean` | — | **done** (Lemma 4.3, Prop 4.4, Lemma 4.5; checked in both environments) |
| M4 | Degree reduction (Lemma 6.1) and degree-balanced partition (Lemma 6.2) | `ExactHC/Preprocess.lean` | — | **done** (Lemma 6.1 identity + bounds, Lemma 6.2; checked in both environments) |
| M4b | Shared interface: psibar/psi/omega/qEdge/genSet/OmegaSet/edgeProd/topV/fermionSum | `ExactHC/Fermion.lean` | M1 | **done** (coordinator) |
| M5 | Lemma 3.2 (Berezin Cauchy–Binet) and Lemma 3.3 (fermionic matrix-tree), Corollary 3.4 | `ExactHC/MatrixTree.lean` | M1, M2 | **done**: `fermionSum_eq : fermionSum G r = n·#HC` (standard axioms; builds in both environments) |
| M6 | Lemma 4.1, Prop. 4.2 (sign rule), Theorem 4.6 (blob factorisation) | `ExactHC/Blobs.lean` | M1, M3 | **done**: `sum_sigma_chi_I` and `sum_eps_prod_I` (blob sum = `fermionSum`), plus the locality lemmas |
| M7 | Definition 5.1, Lemma 5.2, Theorem 5.3 (network value = n·#HC), Prop. 5.4 (parameters) | `bridge …/HCNetwork.lean` | M6, C1a | **done**: `hcNet_value` (network value = n·#HC), `hcNet_is` (Prop. 5.4 bounds), standard axioms |

## Layer C (computation, in Anthropic's workspace)

| Id | Statement | Depends on | Status |
|---|---|---|---|
| C0 | Scout of Anthropic's API (`research/anthropic-api.md`) | — | **done**: the theorems are general for any `Eight.SecNetworks.Net g` |
| C1 | Tables W_a, Ψ, f as algorithms in their cost model, with cost τ | M7, C0 | wave 3 |
| C2 | Theorem 1 (2^{δn}) and Theorem 2 (2^{O(max(m,n)/√log n)}) as Lean theorems | C1, M4 | wave 4 |

## Plan after C0 (see `anthropic-api.md`)

* **Target types.**
  * Network: `Eight.SecNetworks.Net g` with `Net.Is P B` and `Net.value`.
  * Procedures: `Given.IsGivenNetwork (ofProcs Np) noTable c N P B τ S`.
  * Machines: `QueryMachine` / `Stepped` → TM2 via `CountKSat.exists_tmW` or `GraphProblems.tm_of_stepped` on `GraphProblems.code G`.
* **Constraint.** The state bound S must be poly(n) uniformly, so the node tables W_a must be evaluated
  by streaming over monomials (poly state, 2^{O(μ)} steps), not by storing Λ_a densely.
* **Theorem 1 route** (2^{δn}): `Given.stEveryEta` → `Printed.groupingLemma` → `Given.stOnGiven` on
  our procedures (template `Given.onFormula`) → Lemma 6.1 branching and summation →
  `GraphProblems.tm_of_stepped`.
* **Theorem 2 route:** E = `cliqueMachine` from `CountedRoute.onTheCountedRecursion` →
  `groupingExplicit` case (i) → `plug` our procedures → a uniform `Stepped` machine → `exists_tmW`.
* **New modules, all compiled in `/home/user/anth-build/bridge/EthFollowup/ExactHC/`.** The math files
  are symlinked from `lean/`; M2 and M3 already compile there.
  * **C1a:** a generic label-sharing network as a `Net g`, with value = Σ over global labellings of
    Π_a W_a(ℓ|δ(a)), equality-test edges, and `Is P B`.
  * **C1b:** streaming procedures for W_a (`IsGivenNetwork`), with a poly-state proof.
  * **C2:** Theorems 1 and 2.

## Progress log
* **C1a done:** `LabelNetwork.lean` (577 lines; saved at `research/lean-bridge-wip/`), checked in
  Anthropic's environment.
  * Theorems: `value_net` (value = Σ over global labellings of Π_a T_a), `net_is` (`Is P B`),
    `U_eq` (U = 2(|K|·w + |R|)).
  * Deviation: labels are binary-coded, 3 bits per item instead of log₂5. This is a constant
    factor; Theorems 1 and 2 are unaffected.
* **C1b (generic procedures) started.**
* **M5 done:** `fermionSum_eq` (Lemma 3.2 and Lemma 3.3). M0 was made portable (it used a bridge lemma whose name differs between the two Mathlib versions).
* **C1b done:** `LabelProcs.lean` (536 lines; saved at `research/lean-bridge-wip/`). `labelProcs_given`
  gives `Given.IsGivenNetwork … (X.net C) P B τ (S + size c + 2g + 4P + 8)`, with standard axioms.
  Still needed from the Hamiltonian side:
  * a poly-time reader `lay` with `Describes`;
  * a parity procedure `par` with `ParSpec`;
  * a T-procedure with `IsPolyT`, τ = 2^{O(μ)}·poly and S = poly(n) (C1c).
* **C2 started** in parameterised form: the TM-level Theorem 1 from an abstract "HC network package".
* **MATH LAYER COMPLETE.** M6 is done (Lemma 4.1, Prop. 4.2, Theorem 4.6 and the locality lemmas).
  `ExactHC/Main.lean` proves `blob_factorisation`: Σ_ℓ Π_a σ_a χ_a I_a = n·#HC(G) for every G, r, β and
  crossing order. It uses only the three standard axioms, is in the default build and the axiom audit,
  and also builds in Anthropic's environment. I renamed 5 duplicate lemma names in M5 (`mt_` prefix).
* **Next:**
  * M7: instantiate the C1a `LabelSystem` with the HC tables (value = n·#HC, bounds);
  * C1c: a streaming T-procedure for σ·χ·I, plus `par`;
  * C2: the assembly (running, parametric).
* **M7 done:** `HCNetwork.lean` (562 lines). The Hamiltonian network in Anthropic's `Net` format:
  * `hcNet_value : value = n·#HC(G)` (Theorem 5.3);
  * `hcNet_is_labelCode : Is (3μ + g² + 1) (2μ + 1)` (Prop. 5.4);
  * `hcNet_U ≤ 2(3m + g³)`.

  Coordinator-checked, standard axioms. Remaining for Theorem 1: the C1c streaming table procedure
  (running) and the C2 assembly (running).
* **Layout:** the canonical bridge modules now live in `lean-bridge-anthropic/bridge/EthFollowup/ExactHC/`. They are symlinked into `/home/user/anth-build/bridge/…`, and the math modules are symlinked from `lean/`. New bridge modules (TableProc, Assembly) will move there once done.
* **C1c done:** `TableProc.lean` (1396 lines):
  * `tableStream_eq` (streamed sum = σ·χ·I);
  * `tableMachine_runs` (≤ 2·8^{μ_a} steps, state linear in the input);
  * `tableProc_poly`;
  * `parBit` with `P_eq_parBit`.

  The coordinator fixed the build under the workspace's `autoImplicit = false` (re-enabled
  `autoImplicit` in this one file).
* **C2 done:** `Assembly.lean` (1273 lines). `theorem1_TM (hpkg : ∃ c₀, ∀ g ≥ 1, Nonempty (HCPackage g c₀))`
  states: ∀ δ > 0, ∀ D, a TM2 machine outputs #HC(G) in binary within ⌊C·2^{δn}⌋ steps for every G
  with |E| ≤ D·n. `theorem1_TM_of_label` is the same from `LabelPackage`s. Standard axioms.
* **Remaining (C3, final glue):** construct `∃ c₀, ∀ g ≥ 1, LabelPackage g c₀` from M7 (`hcSystem`,
  `hcNet_is`), C1b (`labelProcs_given`) and C1c (`tableProc`, `parBit`). This needs the poly-time
  reader `prep` (partition by M4, root, crossing order, layout) with `Describes`/`TDesc`, the `par`
  wrapper with `ParSpec`, and the size bounds.
* **C3 DONE: THEOREM 1 IS UNCONDITIONAL IN LEAN.** `Package.lean` (1037 lines) proves
  `exists_labelPackage` (c₀ = 6) and
  `theorem1 : ∀ δ > 0, ∀ D, ∃ M C, (finite alphabets) ∧ ∀ n G, |E| ≤ D·n →
  GraphProblems.Outputs M (code G) (bits #hamCycles G) ⌊C·2^{δn}⌋`.
  Here `code G` is n in unary followed by the adjacency matrix, and `Outputs` is Mathlib's
  `TM2OutputsInTime`. Axioms: propext, Classical.choice, Quot.sound. Coordinator-checked with
  `lake build` and `#print axioms`; a fresh `leanchecker --fresh EthFollowup.ExactHC.Package` replay of the full closure (Mathlib, Anthropic's development and ours) **passed (exit 0)**.
* **Theorem 2 (conditional) done:** `Theorem2.lean` (1764 lines) proves `theorem2_TM : (∃ c₀, Nonempty (T2.UPackage c₀)) →`
  one TM2 machine M and a constant C with Outputs M (code G) (bits #HC) ⌊C·2^{C(m+n)/√log₂(n+2)}⌋ for every G.
  Standard axioms; coordinator-checked. It needs a package **uniform in g** (one Ctx, one reader taking
  `(unary g, code G)`, one q). Remaining: `UPackage.lean`, constructing it from Package.lean's
  components (running).
* **THEOREM 2 IS UNCONDITIONAL.** `UPackage.lean` (639 lines) builds the uniform-in-g package (q absolute, g read in unary); `theorem2 := theorem2_TM_of_label exists_ulabelPackage`. Coordinator-checked: lake build, standard axioms.
* **Weighted (TSP) math + network layer done:** `lean/EthFollowup/ExactHC/Weighted.lean` and
  `bridge/…/WeightedNetwork.lean`. `blob_factorisation_w : Σ_ℓ Π_a σ_a χ_a I^w_a = n·Σ_H z^{wt H}` (z : ℤ,
  Kronecker), `kronecker_decode` (digit extraction gives n·#tours of each weight),
  `hcNetW_kron` (network value and `Is (3μ+g²+1) (bWμ+2μ+1)`). Standard axioms, both environments.
  Remaining for a TM-level TSP theorem: weighted streaming table procedure, package with weights in
  the input, and the digit post-processing.
* Fresh `leanchecker --fresh EthFollowup.ExactHC.UPackage` (closure of theorem2) **passed (exit 0)**.
* **TSP AT TM LEVEL DONE.** `WeightedPackage.lean` (743 lines) and `TSP.lean` (689 lines):
  `theoremTSP : ∀ δ > 0, ∀ D, ∃ M C, finite alphabets ∧ ∀ n G W w, |E| ≤ D·n → (∀ e, w e ≤ W) →
  Outputs M (tspCode G W w) (bits (n·Σ_H 2^{bK n · wt w H})) ⌊C·2^{δn}·(W+2)^C⌋` and
  `theoremTSP_decode` (digit j = n·tourCount j; lowest non-zero digit = optimum; digit/n = #optimal).
  Coordinator-checked: `lake build`, standard axioms. Fresh `leanchecker --fresh EthFollowup.ExactHC.TSP` **passed (exit 0)**.
* **LEAN FOR EVERY CLAIM (29 Oct 2026).** New, all coordinator-verified (build, `#print axioms`, fresh `leanchecker`):
  * Thm 1.3: `theorem3`, `theorem3_maxdeg` (Unrank, PairCode, VertexBalanced, RankNetwork, RankProcs, DegTableProc, RankWordProcs, Theorem3, DPackage; ~6.5k lines).
  * Cor 1.4: `decision_TM`, `search_TM`, `hamPaths_*_TM` and `_rate` versions (SelfReduction, HamPath, SearchMachine, Corollaries, Paths).
  * Directed HC / ATSP: math layer (DirectedMatrixTree, DirectedBlobs, DirectedWeighted, DirectedNetwork) and `theoremDHC`, `theoremDHC_rate`, `theoremATSP`, `theoremATSP_decode` via vertex splitting (VertexSplit, DirectedTheorems).
  * Barriers: 39 lemmas incl. `colouring_barrier_graph` (paper Prop.), row-cut rank, Model-R bound, triangular rank, spread lemma, derandomization bound, algebra rank, per mod p.
  * `AuditAll.lean` (bridge) and `AxiomsExtended.lean` (repo): all standard; `leanchecker --fresh` passed for both.
  * Not formalised and therefore not claimed: forest-indicator lemma, s–t paths, ATSP explicit rate, graphic TSP and the other extension rows, Theorem S (sat-width), randomized (b) (superseded).
