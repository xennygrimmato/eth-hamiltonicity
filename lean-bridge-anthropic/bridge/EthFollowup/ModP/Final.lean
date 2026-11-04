/-
# ModP: the unconditional results (module B7)

`scratchpad/plans/modp-plan.md` §2 and ADDENDUM §B. The polynomial-time table and reader of the
arithmetic network (`ArithPoly.tabAF_polyT`, `ArithPoly.aCtxOf_polyT`) discharge the hypotheses of
the instance theorems of `ArithPkgs.lean`. For each problem: ONE Mathlib `TM2ComputableAux` machine
with finite alphabets and ONE constant `C`, halting within `⌊C · 2^{C n/√(log₂(n+2))}⌋` steps
(`n` the input length) with the answer:

* **`hForm_TM_rate`** (headline): the number `hForm (−N)` of reduced forms of discriminant `−N`;
  `hFormPrim_TM_rate`: for fundamental `−N < 0` it is the number of primitive reduced forms
  (`hForm_eq_card_primitive`), i.e. the form class number `h(−N)`;
* **`sqrtMod_TM_rate`**: the least square root of `a` modulo `m` (`m` if there is none), on
  `encodePair m a`;
* **`lqnr_TM_rate`**: the least quadratic non-residue modulo a prime `p` (and some `y ≤ p` on every `p`);
* **`divisorSum_TM_rate`** (`Σ_{m≤x} τ(m)`), `sigmaSum_TM_rate` (`Σ_{m≤x} σ(m)`), **`circle_TM_rate`**
  (`#{(u,v) ∈ ℤ² : u² + v² ≤ x}`).

Standard axioms only.
-/
import EthFollowup.ModP.ArithPkgs
import EthFollowup.ModP.ArithPoly

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring

/-- The number of variables of a reader's descriptions, in unary (`nV ≤ cA ≤ cD`). -/
theorem ArithSpec.nV_unary (A : ArithSpec) :
    Unary fun y : List Unit × (List Bool × List Bool) => (A.desc y.2).nV :=
  Unary.of_le (Unary.const A.cD) (by have h := A.desc_poly'; fun_prop)
    fun y => (nV_le_cA _).trans (A.cA_le _)

/-- **The reader of every description reader is polynomial-time.** -/
theorem ArithSpec.prep_polyT (A : ArithSpec) : PolyT A.prep :=
  aCtxOf_polyT A.nf_unary' A.desc_poly' A.nV_unary g_unary' A.PA_unary

/-- **(E), the headline: class numbers in `2^{O(n/√log n)}`.** On `encodeNat N` the machine outputs
`encodeNat (hForm (−N))`, the number of reduced binary quadratic forms of discriminant `−N`. -/
theorem hForm_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, GraphProblems.Outputs M (Computability.encodeNat N)
        (Computability.encodeNat (hForm (-(N : ℤ))))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat N).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat N).length + 2)))⌋₊ :=
  hForm_TM_of tabAF_polyT arithE.prep_polyT

/-- **(E) for fundamental discriminants**: the same machine outputs the number of primitive reduced
forms of discriminant `−N` (the form class number `h(−N)`) whenever `−N` is fundamental. -/
theorem hFormPrim_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, IsFundDisc (-(N : ℤ)) → 0 < N → GraphProblems.Outputs M (Computability.encodeNat N)
        (Computability.encodeNat (primRedForms (-(N : ℤ))).card)
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat N).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat N).length + 2)))⌋₊ := by
  obtain ⟨M, C, hfin, h⟩ := hForm_TM_rate
  refine ⟨M, C, hfin, fun N hD hN => ?_⟩
  rw [← hForm_eq_card_primitive hD (by omega)]
  exact h N

/-- **(A) the least square root of `a` modulo any `m`** (`m` if there is none), on `encodePair m a`. -/
theorem sqrtMod_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ m a : ℕ, GraphProblems.Outputs M (encodePair m a) (Computability.encodeNat (minRoot m a))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodePair m a).length /
          Real.sqrt (Real.logb 2 ((encodePair m a).length + 2)))⌋₊ :=
  sqrtMod_TM_of tabAF_polyT arithA.prep_polyT

/-- **(B) the least quadratic non-residue modulo a prime `p`**; on every `p` the machine halts within
the same bound with some `y ≤ p`. -/
theorem lqnr_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ p : ℕ, p.Prime → GraphProblems.Outputs M (Computability.encodeNat p)
        (Computability.encodeNat (lqnr p))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat p).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat p).length + 2)))⌋₊) ∧
      (∀ p : ℕ, ∃ y ≤ p, GraphProblems.Outputs M (Computability.encodeNat p) (Computability.encodeNat y)
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat p).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat p).length + 2)))⌋₊) :=
  lqnr_TM_of tabAF_polyT arithB.prep_polyT

/-- **(F) the divisor sum `Σ_{m ≤ x} τ(m)`.** -/
theorem divisorSum_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (∑ m ∈ Finset.Icc 1 x, (Nat.divisors m).card))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ :=
  divisorSum_TM_of tabAF_polyT arithDiv.prep_polyT

/-- **(F) the sum of divisors `Σ_{m ≤ x} σ(m)`.** -/
theorem sigmaSum_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (∑ m ∈ Finset.Icc 1 x, ∑ d ∈ Nat.divisors m, d))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ :=
  sigmaSum_TM_of tabAF_polyT arithSig.prep_polyT

/-- **(F) the Gauss circle count `#{(u, v) ∈ ℤ² : u² + v² ≤ x}`.** -/
theorem circle_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (((Finset.Icc (-(x : ℤ)) x ×ˢ Finset.Icc (-(x : ℤ)) x).filter
          fun q : ℤ × ℤ => q.1 ^ 2 + q.2 ^ 2 ≤ x).card))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ :=
  circle_TM_of tabAF_polyT arithCirc.prep_polyT

end EthFollowup.ModP
