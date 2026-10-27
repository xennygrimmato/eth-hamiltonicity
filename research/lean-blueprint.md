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
| M1 | Concrete exterior algebra Λ(Γ) over ℤ (basis e_S, merge sign); Fact 2.1; Koszul rule (Lemma 2.2); block factorisation of top coefficients (Lemma 2.3); product of linear forms = det · top monomial | `ExactHC/Grassmann.lean` | — | wave 1 |
| M2 | Reduced incidence matrix of F with \|F\| = n−1: det² = [F is a spanning tree] (inside Lemma 3.3) | `ExactHC/Incidence.lean` | — | wave 1 |
| M3 | Chord/parity combinatorics: Lemma 4.3, Prop. 4.4 (ε = Πσ_a · interleaving), Lemma 4.5 (parity copies) | `ExactHC/SignRule.lean` | — | wave 1 |
| M4 | Degree reduction (Lemma 6.1) and degree-balanced partition (Lemma 6.2) | `ExactHC/Preprocess.lean` | — | wave 1 |
| M5 | Lemma 3.2 (Berezin Cauchy–Binet) and Lemma 3.3 (fermionic matrix-tree), Corollary 3.4 | `ExactHC/MatrixTree.lean` | M1, M2 | wave 2 |
| M6 | Lemma 4.1, Prop. 4.2 (sign rule), Theorem 4.6 (blob factorisation) | `ExactHC/Blobs.lean` | M1, M3, M5 | wave 2 |
| M7 | Definition 5.1, Lemma 5.2, Theorem 5.3 (network value = n·#HC), Prop. 5.4 (parameters) | `ExactHC/Network.lean` | M6, C0 | wave 3 |

## Layer C (computation, in Anthropic's workspace)

| Id | Statement | Depends on | Status |
|---|---|---|---|
| C0 | Scout: exact Lean statements of `ExplicitCost.groupingExplicit` (Lemma 8), `ExplicitCost.recursionSolves` (Theorem A(b)), `PiecesCounted.halfPieces` (Theorem B), and their network/clique/cost definitions. Can they be applied to an arbitrary network? | — | wave 1 |
| C1 | Tables W_a, Ψ, f as algorithms in their cost model, with cost τ | M7, C0 | wave 3 |
| C2 | Theorem 1 (2^{δn}) and Theorem 2 (2^{O(max(m,n)/√log n)}) as Lean theorems | C1, M4 | wave 4 |
