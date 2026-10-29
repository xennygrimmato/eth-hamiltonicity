/-
# The algebra-rank barrier (`research/permanent/wild-ideas.md` F2)

Source (`wild-ideas.md`, F2):

> **F2 (algebra rank).** Let R be any ring (not necessarily commutative) with a linear functional
> φ and elements r_{ij} (i, j ∈ [n]) such that φ(r_{1f(1)} r_{2f(2)} ⋯ r_{nf(n)}) = [f is a
> bijection] for all f: [n] → [n]. Then dim R ≥ C(n, n/2). Proof: for f₁: [n/2] → [n] and
> f₂: [n/2]+1..n → [n] put u(f₁) = r_{1f₁(1)}⋯r_{n/2, f₁(n/2)} and v(f₂) likewise;
> M[f₁,f₂] := φ(u(f₁)v(f₂)) = [im f₁ ⊔ im f₂ = [n], both injective]. Restricted to injective
> f₁, f₂ with im f₁ = S, im f₂ = S^c and a fixed order, M contains a C(n,n/2) permutation matrix,
> and M = ⟨φ, u ⊗ v⟩ has rank ≤ dim R. ∎ … The same holds … for Σ_{t ≤ T} φ_t over T algebras
> (rank adds: Σ dim R_t ≥ C(n,n/2)). … over every field.

"Dimension" requires a base field: we take `R` a (possibly noncommutative) `K`-algebra over an
arbitrary field `K`, `φ : R →ₗ[K] K`, and `R` finite-dimensional (otherwise `dim R = ∞` and there
is nothing to prove). The proof shows that the `C(n,m)` elements `u_S` (`|S| = m`) are linearly
independent, which is the rank statement in the source.

* `algebra_rank` — for every split `n = m + k`: `C(m + k, m) ≤ dim_K R`;
* `algebra_rank_half` — the stated form `C(n, n/2) ≤ dim_K R`;
* `algebra_rank_sum` — the version for `Σ_t φ_t` over finitely many algebras:
  `C(n, n/2) ≤ Σ_t dim R_t`.
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Tuple.Basic

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.AlgebraRank

open Finset

variable {K : Type*} [Field K] {R : Type*} [Ring R] [Algebra K R]

/-- The ordered word `r_{1 f(1)} r_{2 f(2)} ⋯ r_{n f(n)}`. -/
def word {n : ℕ} (r : Fin n → Fin n → R) (f : Fin n → Fin n) : R :=
  (List.ofFn fun i => r i (f i)).prod

section Split

variable (m k : ℕ)

/-- The `m`-subsets of `Fin (m + k)`. -/
abbrev Msub := {S : Finset (Fin (m + k)) // S.card = m}

theorem card_compl_eq (S : Msub m k) : Fintype.card (Fin k) = Fintype.card {j // j ∉ S.1} := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe, S.2, Fintype.card_fin, Fintype.card_fin]
  omega

theorem card_eq (S : Msub m k) : Fintype.card (Fin m) = Fintype.card {j // j ∈ S.1} := by
  rw [Fintype.card_coe, S.2, Fintype.card_fin]

/-- A bijection of the first `m` positions onto `S`. -/
noncomputable def f₁ (S : Msub m k) : Fin m → Fin (m + k) :=
  fun a => (Fintype.equivOfCardEq (card_eq m k S) a).1

/-- A bijection of the last `k` positions onto `Sᶜ`. -/
noncomputable def f₂ (S : Msub m k) : Fin k → Fin (m + k) :=
  fun b => (Fintype.equivOfCardEq (card_compl_eq m k S) b).1

theorem f₁_mem (S : Msub m k) (a) : f₁ m k S a ∈ S.1 :=
  (Fintype.equivOfCardEq (card_eq m k S) a).2

theorem f₂_not_mem (S : Msub m k) (b) : f₂ m k S b ∉ S.1 :=
  (Fintype.equivOfCardEq (card_compl_eq m k S) b).2

theorem f₁_surj (S : Msub m k) {j} (hj : j ∈ S.1) : ∃ a, f₁ m k S a = j :=
  ⟨(Fintype.equivOfCardEq (card_eq m k S)).symm ⟨j, hj⟩, by simp [f₁]⟩

theorem f₂_surj (S : Msub m k) {j} (hj : j ∉ S.1) : ∃ b, f₂ m k S b = j :=
  ⟨(Fintype.equivOfCardEq (card_compl_eq m k S)).symm ⟨j, hj⟩, by simp [f₂]⟩

/-- The glued map is a bijection iff `S = S'`. -/
theorem bijective_append_iff (S S' : Msub m k) :
    Function.Bijective (Fin.append (f₁ m k S) (f₂ m k S')) ↔ S = S' := by
  rw [← Finite.surjective_iff_bijective]
  constructor
  · intro hsurj
    have hsub : S'.1 ⊆ S.1 := by
      intro j hj
      obtain ⟨i, hi⟩ := hsurj j
      induction i using Fin.addCases with
      | left a => rw [Fin.append_left] at hi; exact hi ▸ f₁_mem m k S a
      | right b => rw [Fin.append_right] at hi; exact absurd (hi ▸ hj) (f₂_not_mem m k S' b)
    exact (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [S.2, S'.2]))).symm
  · rintro rfl j
    by_cases hj : j ∈ S.1
    · obtain ⟨a, ha⟩ := f₁_surj m k S hj
      exact ⟨Fin.castAdd k a, by rw [Fin.append_left, ha]⟩
    · obtain ⟨b, hb⟩ := f₂_surj m k S hj
      exact ⟨Fin.natAdd m b, by rw [Fin.append_right, hb]⟩

variable {m k}

/-- `u(S) = r_{1 f₁(1)} ⋯ r_{m f₁(m)}`. -/
noncomputable def uS (r : Fin (m + k) → Fin (m + k) → R) (S : Msub m k) : R :=
  (List.ofFn fun a : Fin m => r (Fin.castAdd k a) (f₁ m k S a)).prod

/-- `v(S) = r_{m+1, f₂(1)} ⋯ r_{m+k, f₂(k)}`. -/
noncomputable def vS (r : Fin (m + k) → Fin (m + k) → R) (S : Msub m k) : R :=
  (List.ofFn fun b : Fin k => r (Fin.natAdd m b) (f₂ m k S b)).prod

theorem uS_mul_vS (r : Fin (m + k) → Fin (m + k) → R) (S S' : Msub m k) :
    uS r S * vS r S' = word r (Fin.append (f₁ m k S) (f₂ m k S')) := by
  rw [word, List.ofFn_add, List.prod_append, uS, vS]
  congr 2
  · congr 1
    funext a
    exact (congrArg (r (Fin.castAdd k a)) (Fin.append_left _ _ a)).symm
  · congr 1
    funext b
    rw [Fin.append_right]

/-- **F2, any split**: if `φ(r_{1f(1)} ⋯ r_{nf(n)}) = [f bijective]` for all `f`, then
`C(m + k, m) ≤ dim_K R`. -/
theorem algebra_rank [FiniteDimensional K R] (φ : R →ₗ[K] K) (r : Fin (m + k) → Fin (m + k) → R)
    (h : ∀ f, φ (word r f) = if Function.Bijective f then 1 else 0) :
    (m + k).choose m ≤ Module.finrank K R := by
  classical
  have hM : ∀ S S' : Msub m k, φ (uS r S * vS r S') = if S = S' then 1 else 0 := by
    intro S S'
    rw [uS_mul_vS, h]
    simp only [bijective_append_iff]
  have hli : LinearIndependent K (uS r) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc S'
    have := congrArg (fun x => φ (x * vS r S')) hc
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hM, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_mul, map_zero] at this
    exact this
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_finset_len, Fintype.card_fin] at this

end Split

/-- **`wild-ideas.md` F2** as stated: `dim_K R ≥ C(n, n/2)`. -/
theorem algebra_rank_half {n : ℕ} [FiniteDimensional K R] (φ : R →ₗ[K] K)
    (r : Fin n → Fin n → R) (h : ∀ f, φ (word r f) = if Function.Bijective f then 1 else 0) :
    n.choose (n / 2) ≤ Module.finrank K R := by
  generalize hm : n / 2 = m
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  exact algebra_rank φ r h

/-- F2 for sums over finitely many algebras: if `Σ_t φ_t(r^t_{1f(1)} ⋯ r^t_{nf(n)}) = [f
bijective]`, then `Σ_t dim R_t ≥ C(n, n/2)` ("rank adds"). -/
theorem algebra_rank_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ t, Ring (A t)] [∀ t, Algebra K (A t)] [∀ t, FiniteDimensional K (A t)] {n : ℕ}
    (φ : ∀ t, A t →ₗ[K] K) (r : ∀ t, Fin n → Fin n → A t)
    (h : ∀ f, ∑ t, φ t (word (r t) f) = if Function.Bijective f then 1 else 0) :
    n.choose (n / 2) ≤ ∑ t, Module.finrank K (A t) := by
  let Φ : (∀ t, A t) →ₗ[K] K := ∑ t, (φ t).comp (LinearMap.proj t)
  have hw : ∀ f, word (fun i j t => r t i j) f = fun t => word (r t) f := by
    intro f
    funext t
    rw [word, word, Pi.list_prod_apply, List.map_ofFn]
    rfl
  have := algebra_rank_half (R := ∀ t, A t) Φ (fun i j t => r t i j) (fun f => by
    rw [hw, ← h f]
    simp [Φ])
  rwa [Module.finrank_pi_fintype] at this

end EthFollowup.Barriers.AlgebraRank
