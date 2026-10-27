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
| M5 | Lemma 3.2 (Berezin Cauchy–Binet) and Lemma 3.3 (fermionic matrix-tree), Corollary 3.4 | `ExactHC/MatrixTree.lean` | M1, M2 | wave 2 running — target `fermionSum G r = n·#HC` |
| M6 | Lemma 4.1, Prop. 4.2 (sign rule), Theorem 4.6 (blob factorisation) | `ExactHC/Blobs.lean` | M1, M3 | wave 2 running — target blob sum = `fermionSum G r` |
| M7 | Definition 5.1, Lemma 5.2, Theorem 5.3 (network value = n·#HC), Prop. 5.4 (parameters) | `ExactHC/Network.lean` | M6, C0 | wave 3 |

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
