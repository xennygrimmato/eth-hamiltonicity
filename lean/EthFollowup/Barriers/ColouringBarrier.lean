/-
# The colouring barrier (paper `prop:colouring-barrier`, `hamiltonicity.md` §8)

Source (paper/main.tex, `\label{prop:colouring-barrier}`):

> Work over a field of characteristic `0`. Suppose that weights `z_0,…,z_{q-1}` on `q` colours,
> with the root coloured `0` and every component `C ∌ r` of a `2`-factor contributing
> `h(C) = ∑_j z_j^{|C|}`, give a sum equal to `HC(G)` up to a nonzero factor, for every graph `G`
> on `n` vertices. Then `q ≥ n-4`.

and the proof: "the filter needs `∑_{j=0}^{q-1} z_j^k = 0` for `k = 3,…,n-3`. Drop the `z_j`
equal to `0`, and group the rest into distinct nonzero values `λ_i` with positive integer
multiplicities. … If `n-5 ≥ q`, the Vandermonde matrix on those integers forces every coefficient
to `0`, a contradiction because `λ = 1` has multiplicity at least `1`."

`hamiltonicity.md` §8 states the same claim ("With vertex-uniform weights, `ω(v, j) = z_j`, an
exact filter for all graphs on `n` vertices forces `q ≥ n − 4`") and the converse ("`q = n − 2`
colours with `z_j = ζ^j`, `ζ` a primitive `(n−2)`-th root of unity, give `Σ_j ζ^{jk} = 0` for
`1 ≤ k ≤ n−3`. So the threshold lies in `[n−4, n−2]`.").

## What is formalised

* `no_exact_filter` / `colouring_barrier`: the **polynomial form**. Over a field of
  characteristic `0`, if `z : Fin q → K` has a nonzero entry (the root colour) and
  `∑_j z_j^k = 0` for every `k` with `3 ≤ k ≤ n - 3`, then `n ≤ q + 4`, i.e. `q ≥ n - 4`.
  (We do not even need to drop the zero values: the base `0` gets the coefficient
  `mult(0)·0^3 = 0` in the Vandermonde system, which is harmless.)
* `rootsOfUnity_powerSum_eq_zero` / `colouring_threshold_upper`: the converse with `q = n - 2`.

The **combinatorial half** of the proposition — that an exact filter forces
`∑_j z_j^k = 0` for each `k ∈ [3, n-3]`, because the disjoint union `C_{n-k} ⊔ C_k` (root in
`C_{n-k}`) has exactly one `2`-factor and it is disconnected — is *not* formalised (it needs a
theory of `2`-factors, their components and consistent colourings that Mathlib lacks). It enters
`colouring_barrier` as the explicit hypothesis `hvan`.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.Colouring

open Finset

variable {K : Type*} [Field K]

/-- Grouping the power sum by the distinct values of `z` (with their multiplicities). -/
theorem powerSum_eq_sum_image [DecidableEq K] {q : ℕ} (z : Fin q → K) (k : ℕ) :
    ∑ j, z j ^ k = ∑ b ∈ univ.image z, ((#{j | z j = b} : ℕ) : K) * b ^ k := by
  rw [Finset.sum_comp (fun b => b ^ k) z]
  simp [nsmul_eq_mul]

/-- The polynomial core of `prop:colouring-barrier`: if `z_{j₀} = 1` and the power sums
`∑_j z_j^k` vanish for all `3 ≤ k ≤ n - 3`, then `q + 5 ≤ n` is impossible. -/
theorem no_exact_filter [CharZero K] {n q : ℕ} (z : Fin q → K) (j₀ : Fin q) (hz : z j₀ = 1)
    (hvan : ∀ k, 3 ≤ k → k + 3 ≤ n → ∑ j, z j ^ k = 0) (hq : q + 5 ≤ n) : False := by
  classical
  set Λ : Finset K := univ.image z with hΛ
  have hm : Λ.card ≤ q := by simpa using card_image_le (s := (univ : Finset (Fin q))) (f := z)
  let e : Fin Λ.card ≃ Λ := Λ.equivFin.symm
  let f : Fin Λ.card → K := fun i => (e i : K)
  have hf : Function.Injective f := fun a b h => e.injective (Subtype.ext h)
  let v : Fin Λ.card → K := fun i => ((#{j | z j = f i} : ℕ) : K) * f i ^ 3
  have key : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf
    intro i
    have hi : (i : ℕ) < Λ.card := i.isLt
    have h1 := hvan (3 + i) (by omega) (by omega)
    rw [powerSum_eq_sum_image, ← hΛ, ← Finset.sum_coe_sort Λ, ← e.sum_comp] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [v, f, pow_add]
    ring
  have h1mem : (1 : K) ∈ Λ := mem_image.2 ⟨j₀, mem_univ _, hz⟩
  have hv := congrFun key (e.symm ⟨1, h1mem⟩)
  simp only [v, f, Equiv.apply_symm_apply, one_pow, mul_one, Pi.zero_apply,
    Nat.cast_eq_zero, Finset.card_eq_zero] at hv
  have : j₀ ∈ (univ.filter fun j => z j = 1) := by simp [hz]
  rw [hv] at this
  simp at this

/-- `prop:colouring-barrier`, polynomial form: in characteristic `0`, if the root colour has a
nonzero weight `z_{j₀} ≠ 0` and `∑_{j<q} z_j^k = 0` for every `k ∈ [3, n-3]` (the vanishing
forced on an exact filter by the graphs `C_{n-k} ⊔ C_k`; this combinatorial step is a hypothesis
here), then `q ≥ n - 4`. -/
theorem colouring_barrier [CharZero K] {n q : ℕ} (z : Fin q → K) (j₀ : Fin q) (hz : z j₀ ≠ 0)
    (hvan : ∀ k, 3 ≤ k → k + 3 ≤ n → ∑ j, z j ^ k = 0) : n ≤ q + 4 := by
  by_contra hlt
  refine no_exact_filter (n := n) (fun j => z j / z j₀) j₀ (div_self hz) (fun k hk1 hk2 => ?_) (by omega)
  simp_rw [div_pow, div_eq_mul_inv, ← Finset.sum_mul, hvan k hk1 hk2, zero_mul]

/-- The converse construction: for a primitive `N`-th root of unity `ζ` and `N ∤ k`,
`∑_{j<N} (ζ^j)^k = 0`. -/
theorem rootsOfUnity_powerSum_eq_zero {N : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ N) {k : ℕ}
    (hk : ¬ N ∣ k) : ∑ j : Fin N, (ζ ^ (j : ℕ)) ^ k = 0 := by
  have hne : ζ ^ k ≠ 1 := fun h => hk ((hζ.pow_eq_one_iff_dvd k).1 h)
  have hpow : (ζ ^ k) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have : ∑ j : Fin N, (ζ ^ (j : ℕ)) ^ k = ∑ j ∈ range N, (ζ ^ k) ^ j := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ j) ^ k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [this, geom_sum_eq hne, hpow, sub_self, zero_div]

/-- `hamiltonicity.md` §8, converse: with `q = n - 2` colours and `z_j = ζ^j` for a primitive
`(n-2)`-th root of unity `ζ`, the root weight is `z_0 = 1` and `∑_j z_j^k = 0` for
`1 ≤ k ≤ n - 3`; so the threshold of `colouring_barrier` lies in `[n-4, n-2]`. -/
theorem colouring_threshold_upper {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ (n - 2)) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 3 ≤ n) : ∑ j : Fin (n - 2), (ζ ^ (j : ℕ)) ^ k = 0 :=
  rootsOfUnity_powerSum_eq_zero hζ fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega

end EthFollowup.Barriers.Colouring
