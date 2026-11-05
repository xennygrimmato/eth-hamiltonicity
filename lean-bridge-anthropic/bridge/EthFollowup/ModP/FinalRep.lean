/-
# Representation numbers of positive-definite integral quadratic forms in `2^{O(n/√log n)}` (repnum-plan.md §4, B4)

For every fixed `k` and every positive-definite `A : Matrix (Fin k) (Fin k) ℤ` (Mathlib's `Matrix.PosDef`):
ONE Mathlib `TM2ComputableAux` machine with finite alphabets and ONE constant `C` such that on the input
`encodeNat n` it halts within `⌊C · 2^{C |w| / √(log₂(|w|+2))}⌋` steps (`|w|` the input length) with

* **`repNum_TM_rate`**: the representation number `r_A(n) = #{x ∈ ℤ^k : xᵀ A x = n}` (`repNum`, RepQF);
* **`diagRep_TM_rate`**: for diagonal forms `Σ a_i x_i²` (`a_i ≥ 1`), `#{x : Σ a_i x_i² = n}`;
* **`tunnell_TM_rate`**: Tunnell's test value `tunnellTest n` (one bit).

Method: the box bound `x_i² ≤ cQ(A) · n` (Cauchy–Schwarz with the adjugate, RepQF), the shift
`u = x + B` (`B = cQ(A) n + 1`), a straight-line-program description of `Q(u − B) = n` (SlpDesc,
RepDesc) counted by the arithmetic network of ModP, on a zero-padded input word (CntPad).

The general theorem gives, for every fixed form, `r_Q(n)` in deterministic time `n^{o(1)}`
(`|encodeNat n| ≈ log₂ n`), versus the trivial `O(n^{k/2})` enumeration of the box; for ternary forms
(`k = 3`) the classical routes through class numbers / modular forms take `n^{1/2+o(1)}`. The constant
`C` depends on `A` and is not tracked.

**Tunnell's theorem** (J. B. Tunnell, *A classical Diophantine problem and modular forms of weight 3/2*,
Invent. Math. 72 (1983) 323–334): for squarefree `n`, if `n` is a congruent number then
`tunnellTest n = true` (unconditionally, via Coates–Wiles), and conversely `tunnellTest n = true` implies
that `n` is congruent under the Birch–Swinnerton-Dyer conjecture for `y² = x³ − n²x`. Congruent numbers
are NOT formalised here: the machine computes the test value only.

Standard axioms only.
-/
import EthFollowup.ModP.RepPkg
import EthFollowup.ModP.Final

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring

/-- **Representation numbers of a fixed positive-definite integral quadratic form in `2^{O(n/√log n)}`.**
On `encodeNat n` the machine outputs `encodeNat (repNum A n)`, `repNum A n = #{x ∈ ℤ^k : xᵀ A x = n}`. -/
theorem repNum_TM_rate (k : ℕ) (A : Matrix (Fin k) (Fin k) ℤ) (hA : A.PosDef) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : ℕ, GraphProblems.Outputs M (Computability.encodeNat n) (Computability.encodeNat (repNum A n))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat n).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat n).length + 2)))⌋₊ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact repNum_TM_zero A tabAF_polyT arithCirc.prep_polyT
  · exact repNum_TM_of A (cQ A) (posDef_coercive hA) hk tabAF_polyT
      (repFam k (fun _ _ => A) (cQ A) hk).prep_polyT

/-- **Diagonal forms** `Σ a_i x_i²` with all `a_i ≥ 1`: the number of representations of `n`. -/
theorem diagRep_TM_rate (k : ℕ) (a : Fin k → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : ℕ, GraphProblems.Outputs M (Computability.encodeNat n)
        (Computability.encodeNat (Set.ncard {x : Fin k → ℤ | ∑ i, (a i : ℤ) * x i ^ 2 = n}))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat n).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat n).length + 2)))⌋₊ := by
  obtain ⟨M, C, hfin, h⟩ := repNum_TM_rate k (Matrix.diagonal fun i => (a i : ℤ))
    (posDef_diagonal_of_pos fun i => by exact_mod_cast ha i)
  refine ⟨M, C, hfin, fun n => ?_⟩
  have := h n
  rwa [repNum_diag] at this

/-- **Tunnell's test as a decision machine**: on `encodeNat n` the output is the one bit `[tunnellTest n]`,
`tunnellTest n = (A_n = 2 B_n)` for odd `n` and `(C_n = 2 D_n)` for even `n`, with
`A_n = #{x² + 2y² + 8z² = n}`, `B_n = #{x² + 2y² + 32z² = n}`, `C_n = #{8x² + 2y² + 16z² = n}`,
`D_n = #{8x² + 2y² + 64z² = n}`. By Tunnell (Invent. Math. 72 (1983) 323–334), for squarefree `n`:
`n` congruent ⇒ `tunnellTest n = true` (unconditionally, via Coates–Wiles), and the converse holds under
BSD for `y² = x³ − n²x`. Congruent numbers are not formalised; the machine computes the test value only. -/
theorem tunnell_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : ℕ, GraphProblems.Outputs M (Computability.encodeNat n) [tunnellTest n]
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat n).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat n).length + 2)))⌋₊ :=
  tunnell_TM_of tabAF_polyT arithTun.prep_polyT

end EthFollowup.ModP
