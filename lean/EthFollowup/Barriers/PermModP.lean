/-
# Low rank over `F_p` kills the permanent (`research/permanent/perm-mod-p.md` (M4))

Source (`perm-mod-p.md`, §2, (M4)):

> **(M4) Low rank over F_p.** If A ≡ UVᵀ (mod p) with U, V ∈ F_p^{n×r}, then mod p only exponent
> vectors α ∈ [0, p−1]^r survive in Barvinok's formula (α! ≡ 0 otherwise) … so
> **per(A) ≡ 0 (mod p) whenever rank_p(A)·(p−1) < n**.

and the summary line "(M4, new here, verified) per ≡ 0 mod p when rank_p(A)(p−1) < n".

We prove it over any commutative ring of characteristic `p` (in particular `F_p = ZMod p`), with
"rank ≤ r" in its factorisation form `A = U Vᵀ`, `U, V ∈ R^{n×r}`. The proof is not Barvinok's
formula but the equivalent elementary route: expanding `A = U Vᵀ` column-wise gives
`per A = Σ_{λ : [n] → [r]} (Π_i V_{i λ(i)}) · per(U_λ)` with `U_λ` the matrix whose `i`-th column is
column `λ(i)` of `U`; if `r(p−1) < n`, some value of `λ` is taken `≥ p` times, so `U_λ` has `p`
equal columns, and a `p`-cycle `τ` permuting them makes the summands of `per(U_λ)` constant on the
free orbits of `⟨τ⟩` (of size `p`), so `per(U_λ) ≡ 0`. (`α! ≡ 0 (mod p)` for `α_l ≥ p` in the
source is the same fact.)

* `sum_eq_zero_of_invariant` — a sum over a finite group of a function invariant under right
  multiplication by a subgroup of order `p` vanishes in characteristic `p`;
* `permanent_eq_zero_of_equal_columns` — `p` equal columns (`λ`-fibre of size `≥ p`) ⇒ `per = 0`;
* `permanent_eq_zero_of_low_rank` — (M4).
-/
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.CharP.Defs

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.PermModP

open Finset

/-- A function on a finite group, invariant under right multiplication by a subgroup `H` with
`|H| = p`, sums to `0` in characteristic `p`. -/
theorem sum_eq_zero_of_invariant {G R : Type*} [Group G] [Fintype G] [CommRing R] (p : ℕ)
    [CharP R p] (H : Subgroup G) [Fintype H] (hH : Fintype.card H = p) (f : G → R)
    (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : ∑ g, f g = 0 := by
  classical
  rw [← Fintype.sum_fiberwise (fun g : G => (g : G ⧸ H)) f]
  refine Finset.sum_eq_zero fun q _ => ?_
  let e : {g : G // (g : G ⧸ H) = q} ≃ H :=
    { toFun := fun g => ⟨q.out⁻¹ * g.1, by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', g.2]⟩
      invFun := fun h => ⟨q.out * h.1, by
        rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, QuotientGroup.out_eq']
        simp⟩
      left_inv := fun g => by ext; simp
      right_inv := fun h => by ext; simp }
  rw [← Fintype.sum_equiv e.symm (fun h : H => f (q.out * h.1)) _ (fun h => rfl)]
  rw [Finset.sum_congr rfl fun h _ => hf q.out h.1 h.2, Finset.sum_const, Finset.card_univ, hH,
    nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- `per(U_λ) = 0` in characteristic `p` when some value of `λ` is taken at least `p` times
(`U_λ` has `p` equal columns). -/
theorem permanent_eq_zero_of_equal_columns [DecidableEq κ] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (U : Matrix ι κ R) (lam : ι → κ) (l : κ) (hl : p ≤ #{i | lam i = l}) :
    (Matrix.of fun j i => U j (lam i)).permanent = 0 := by
  classical
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hl
  set L := C.toList with hL
  have hnodup : L.Nodup := Finset.nodup_toList C
  have hlen : L.length = p := by rw [hL, Finset.length_toList, hCcard]
  have hp2 : 2 ≤ p := hp.out.two_le
  let τ : Equiv.Perm ι := L.formPerm
  have hcyc : τ.IsCycle := List.isCycle_formPerm hnodup (by omega)
  have hsupp : τ.support = C := by
    rw [List.support_formPerm_of_nodup L hnodup (fun x h => by rw [h] at hlen; simp at hlen; omega)]
    simp [hL]
  have hord : orderOf τ = p := by rw [hcyc.orderOf, hsupp, hCcard]
  have hlam : ∀ i, lam (τ i) = lam i := by
    intro i
    by_cases hi : i ∈ C
    · have h1 : τ i ∈ C := by
        have : τ i ∈ L := List.formPerm_apply_mem_of_mem (by simpa [hL] using hi)
        simpa [hL] using this
      have e1 := (Finset.mem_filter.1 (hCsub h1)).2
      have e2 := (Finset.mem_filter.1 (hCsub hi)).2
      rw [e1, e2]
    · have : τ i = i := by
        by_contra hne
        exact hi (hsupp ▸ Equiv.Perm.mem_support.2 hne)
      rw [this]
  -- the summand of the permanent is invariant under `σ ↦ σ * τ`
  let f : Equiv.Perm ι → R := fun σ => ∏ i, U (σ i) (lam i)
  have hfτ : ∀ σ, f (σ * τ) = f σ := by
    intro σ
    simp only [f, Equiv.Perm.mul_apply]
    rw [← Equiv.prod_comp τ (fun i => U (σ i) (lam i))]
    exact Finset.prod_congr rfl fun i _ => by rw [hlam]
  have hfH : ∀ σ, ∀ h ∈ Subgroup.zpowers τ, f (σ * h) = f σ := by
    intro σ h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    induction k using Int.induction_on generalizing σ with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, ← mul_assoc, hfτ, ih σ (Subgroup.zpow_mem_zpowers τ k)]
    | pred k ih =>
      have := hfτ (σ * τ ^ (-(k : ℤ) - 1))
      rw [mul_assoc, ← zpow_add_one, sub_add_cancel] at this
      rw [← this, ih σ (Subgroup.zpow_mem_zpowers τ _)]
  have := sum_eq_zero_of_invariant p (Subgroup.zpowers τ)
    (by rw [Fintype.card_zpowers, hord]) f hfH
  simpa [Matrix.permanent, f] using this

/-- **`perm-mod-p.md` (M4)**: over a commutative ring of characteristic `p` (e.g. `F_p`), if
`A = U Vᵀ` with `U, V ∈ R^{n×r}` and `r(p−1) < n`, then `per A = 0`. -/
theorem permanent_eq_zero_of_low_rank [Fintype κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime]
    [CharP R p] (A : Matrix ι ι R) (U V : Matrix ι κ R) (hA : A = U * V.transpose)
    (hr : Fintype.card κ * (p - 1) < Fintype.card ι) : A.permanent = 0 := by
  classical
  have hexp : A.permanent = ∑ lam : ι → κ, (∏ i, V i (lam i)) *
      (Matrix.of fun j i => U j (lam i)).permanent := by
    rw [hA, Matrix.permanent]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [Finset.prod_univ_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [Matrix.permanent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib, mul_comm]
    simp
  rw [hexp]
  refine Finset.sum_eq_zero fun lam _ => ?_
  obtain ⟨l, hl⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card lam hr
  rw [permanent_eq_zero_of_equal_columns p U lam l (by omega), mul_zero]

end EthFollowup.Barriers.PermModP
