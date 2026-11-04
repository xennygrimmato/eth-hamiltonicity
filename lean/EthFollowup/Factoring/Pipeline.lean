/-
# The Nat-level Schönhage–Strassen pipeline computes the product (module F1, part 5)

Pure Mathlib; compiles in both toolchains.

The pipeline of the factoring network, in plain `ℕ` with residues `% (2^J+1)` and `ω^e` written as
`2^((2J/2^m) · (e % 2^m))`, `L = 2^m`, `L⁻¹ = 2^(2J-m)` (row DFTs, column DFTs, pointwise products,
inverse columns, inverse rows), stated relationally (one hypothesis per stage, on the index ranges
the network uses):
* `stages_eq_aconv2`: the final stage is the 2D acyclic convolution of the limb arrays;
* `stages_eval`: its limb evaluation `Σ_{a,u} Cc a u 2^(b (a + ℓ1 u))` is the product of the two
  limb evaluations, and `stages_eval_mul`: it is `p q` for the limb arrays of `p, q < 2^(b ℓ1 ℓ2)`;
* `convCoeff_eval`: grouping by position `k = a + ℓ1 u`; `convCoeff_le`: a position collects at most
  two coefficients when `L ≤ 2 ℓ1`.
-/
import EthFollowup.Factoring.Carry

set_option linter.unusedSectionVars false

namespace Factoring.Fermat

open Finset

/-- `ω^e` as a natural power of two, cast into the Fermat ring. -/
theorem cast_wP (J m : ℕ) (hm : 1 ≤ m) (hL : 2 ^ m ∣ 2 * J) (hJ : 0 < J) (e : ℕ) :
    (((2 : ℕ) ^ (2 * J / 2 ^ m * (e % 2 ^ m)) : ℕ) : ZMod (2 ^ J + 1)) =
      (fermatRoot J m hm hL hJ).ω ^ e := by
  rw [(fermatRoot J m hm hL hJ).pow_mod, fermatRoot_ω, fermatRoot_L, ← pow_mul]; push_cast; rfl

/-- The pipeline, stage by stage, produces the 2D acyclic convolution of the limb arrays. -/
theorem stages_eq_aconv2 {J m ℓ1 ℓ2 b : ℕ} (hm : 1 ≤ m) (hL : 2 ^ m ∣ 2 * J) (hJ : 0 < J)
    (h1 : 2 * ℓ1 ≤ 2 ^ m) (h2 : 2 * ℓ2 ≤ 2 ^ m) (hb : ℓ1 * ℓ2 * 2 ^ (2 * b) ≤ 2 ^ J)
    (x y Ap Aq Pf Qf Cf Dc Cc : ℕ → ℕ → ℕ)
    (hx : ∀ i1 i2, x i1 i2 < 2 ^ b) (hy : ∀ i1 i2, y i1 i2 < 2 ^ b)
    (hAp : ∀ s < 2 ^ m, ∀ i2 < ℓ2,
      Ap s i2 = (∑ i1 ∈ range ℓ1, x i1 i2 * 2 ^ (2 * J / 2 ^ m * (i1 * s % 2 ^ m))) % (2 ^ J + 1))
    (hAq : ∀ s < 2 ^ m, ∀ i2 < ℓ2,
      Aq s i2 = (∑ i1 ∈ range ℓ1, y i1 i2 * 2 ^ (2 * J / 2 ^ m * (i1 * s % 2 ^ m))) % (2 ^ J + 1))
    (hPf : ∀ s < 2 ^ m, ∀ t < 2 ^ m,
      Pf s t = (∑ i2 ∈ range ℓ2, Ap s i2 * 2 ^ (2 * J / 2 ^ m * (i2 * t % 2 ^ m))) % (2 ^ J + 1))
    (hQf : ∀ s < 2 ^ m, ∀ t < 2 ^ m,
      Qf s t = (∑ i2 ∈ range ℓ2, Aq s i2 * 2 ^ (2 * J / 2 ^ m * (i2 * t % 2 ^ m))) % (2 ^ J + 1))
    (hCf : ∀ s < 2 ^ m, ∀ t < 2 ^ m, Cf s t = Pf s t * Qf s t % (2 ^ J + 1))
    (hDc : ∀ s < 2 ^ m, ∀ u < 2 ^ m, Dc s u = (2 ^ (2 * J - m) * ∑ t ∈ range (2 ^ m),
      Cf s t * 2 ^ (2 * J / 2 ^ m * ((2 ^ m - u) * t % 2 ^ m))) % (2 ^ J + 1))
    (hCc : ∀ a < 2 ^ m, ∀ u < 2 ^ m, Cc a u = (2 ^ (2 * J - m) * ∑ s ∈ range (2 ^ m),
      Dc s u * 2 ^ (2 * J / 2 ^ m * ((2 ^ m - a) * s % 2 ^ m))) % (2 ^ J + 1)) :
    ∀ a < 2 ^ m, ∀ u < 2 ^ m, Cc a u = aconv2 ℓ1 ℓ2 x y a u := by
  set ρ := fermatRoot J m hm hL hJ with hρ
  have hρL : ρ.L = 2 ^ m := rfl
  have hω : ∀ e, (2 : ZMod (2 ^ J + 1)) ^ (2 * J / 2 ^ m * (e % 2 ^ m)) = ρ.ω ^ e := fun e => by
    have := cast_wP J m hm hL hJ e; push_cast at this; exact this
  have hLinv : (2 : ZMod (2 ^ J + 1)) ^ (2 * J - m) = ρ.Linv := rfl
  let X : ℕ → ℕ → ZMod (2 ^ J + 1) := fun i1 i2 => (x i1 i2 : ZMod (2 ^ J + 1))
  let Y : ℕ → ℕ → ZMod (2 ^ J + 1) := fun i1 i2 => (y i1 i2 : ZMod (2 ^ J + 1))
  -- row stage
  have cA : ∀ s < 2 ^ m, ∀ i2 < ℓ2, (Ap s i2 : ZMod (2 ^ J + 1)) = ρ.rowT ℓ1 X s i2 := by
    intro s hs i2 hi2; rw [hAp s hs i2 hi2, ZMod.natCast_mod]; push_cast
    simp only [Root.rowT, Root.dft, X, hω]
  have cB : ∀ s < 2 ^ m, ∀ i2 < ℓ2, (Aq s i2 : ZMod (2 ^ J + 1)) = ρ.rowT ℓ1 Y s i2 := by
    intro s hs i2 hi2; rw [hAq s hs i2 hi2, ZMod.natCast_mod]; push_cast
    simp only [Root.rowT, Root.dft, Y, hω]
  -- column stage
  have cP : ∀ s < 2 ^ m, ∀ t < 2 ^ m, (Pf s t : ZMod (2 ^ J + 1)) = ρ.dft2 ℓ1 ℓ2 X s t := by
    intro s hs t ht; rw [hPf s hs t ht, ZMod.natCast_mod]; push_cast
    simp only [Root.dft2, Root.colT, Root.dft, hω]
    refine sum_congr rfl fun i2 hi2 => ?_
    rw [cA s hs i2 (mem_range.1 hi2)]
  have cQ : ∀ s < 2 ^ m, ∀ t < 2 ^ m, (Qf s t : ZMod (2 ^ J + 1)) = ρ.dft2 ℓ1 ℓ2 Y s t := by
    intro s hs t ht; rw [hQf s hs t ht, ZMod.natCast_mod]; push_cast
    simp only [Root.dft2, Root.colT, Root.dft, hω]
    refine sum_congr rfl fun i2 hi2 => ?_
    rw [cB s hs i2 (mem_range.1 hi2)]
  -- pointwise and inverse stages
  have cD : ∀ s < 2 ^ m, ∀ u < 2 ^ m, (Dc s u : ZMod (2 ^ J + 1)) =
      ρ.icol (fun s t => ρ.dft2 ℓ1 ℓ2 X s t * ρ.dft2 ℓ1 ℓ2 Y s t) s u := by
    intro s hs u hu; rw [hDc s hs u hu, ZMod.natCast_mod]; push_cast
    simp only [Root.icol, Root.idft, hρL, hLinv]
    congr 1
    refine sum_congr rfl fun t ht => ?_
    rw [hCf s hs t (mem_range.1 ht), ZMod.natCast_mod]; push_cast
    rw [cP s hs t (mem_range.1 ht), cQ s hs t (mem_range.1 ht), hω]
  intro a ha u hu
  have key : ((2 ^ (2 * J - m) * ∑ s ∈ range (2 ^ m),
      Dc s u * 2 ^ (2 * J / 2 ^ m * ((2 ^ m - a) * s % 2 ^ m)) : ℕ) : ZMod (2 ^ J + 1)) =
      ((aconv2 ℓ1 ℓ2 x y a u : ℕ) : ZMod (2 ^ J + 1)) := by
    rw [aconv2_cast, ← ρ.cconv2_eq_aconv2 h1 h2, ← ρ.idft2_dft2_mul ℓ1 ℓ2 _ _ ha hu]
    push_cast
    simp only [Root.irow, Root.idft, hρL, hLinv]
    congr 1
    refine sum_congr rfl fun s hs => ?_
    rw [cD s (mem_range.1 hs) u hu, hω]
  rw [hCc a ha u hu]
  refine eq_of_cast_eq_of_lt key ?_
  exact Nat.lt_succ_of_le (aconv2_le_two_pow hb x y hx hy a u)

/-- Limb evaluation of the pipeline output is the product of the limb evaluations. -/
theorem stages_eval {L ℓ1 ℓ2 b : ℕ} (h1 : 2 * ℓ1 ≤ L) (h2 : 2 * ℓ2 ≤ L) (x y Cc : ℕ → ℕ → ℕ)
    (hCc : ∀ a < L, ∀ u < L, Cc a u = aconv2 ℓ1 ℓ2 x y a u) :
    ∑ a ∈ range L, ∑ u ∈ range L, Cc a u * 2 ^ (b * (a + ℓ1 * u)) =
      (∑ i2 ∈ range ℓ2, ∑ i1 ∈ range ℓ1, x i1 i2 * 2 ^ (b * (i1 + ℓ1 * i2))) *
        ∑ j2 ∈ range ℓ2, ∑ j1 ∈ range ℓ1, y j1 j2 * 2 ^ (b * (j1 + ℓ1 * j2)) := by
  rw [← aconv2_eval_two_pow (L := L) (L' := L) (by omega) (by omega)]
  exact sum_congr rfl fun a ha => sum_congr rfl fun u hu => by
    rw [hCc a (mem_range.1 ha) u (mem_range.1 hu)]

/-- With the 2D limb arrays `(i1, i2) ↦ limb (i1 + ℓ1 i2)` of `p, q < 2^(b ℓ1 ℓ2)`, the limb
evaluation of the pipeline output is `p q`. -/
theorem stages_eval_mul {L ℓ1 ℓ2 b p q : ℕ} (h1 : 2 * ℓ1 ≤ L) (h2 : 2 * ℓ2 ≤ L)
    (hp : p < 2 ^ (b * (ℓ1 * ℓ2))) (hq : q < 2 ^ (b * (ℓ1 * ℓ2))) (Cc : ℕ → ℕ → ℕ)
    (hCc : ∀ a < L, ∀ u < L, Cc a u = aconv2 ℓ1 ℓ2
      (fun i1 i2 => p / 2 ^ (b * (i1 + ℓ1 * i2)) % 2 ^ b)
      (fun i1 i2 => q / 2 ^ (b * (i1 + ℓ1 * i2)) % 2 ^ b) a u) :
    ∑ a ∈ range L, ∑ u ∈ range L, Cc a u * 2 ^ (b * (a + ℓ1 * u)) = p * q := by
  rw [stages_eval h1 h2 _ _ Cc hCc, ← limb_sum2 b ℓ1 ℓ2 p hp, ← limb_sum2 b ℓ1 ℓ2 q hq]

/-! ## Grouping by carry position -/

/-- Grouping the coefficients by position `k = a + ℓ1 u`. -/
theorem convCoeff_eval {L L' ℓ1 K b : ℕ} (C : ℕ → ℕ → ℕ)
    (hK : ∀ a < L, ∀ u < L', a + ℓ1 * u < K) :
    ∑ k ∈ range K, (∑ a ∈ range L, ∑ u ∈ range L', if a + ℓ1 * u = k then C a u else 0) *
        2 ^ (b * k) =
      ∑ a ∈ range L, ∑ u ∈ range L', C a u * 2 ^ (b * (a + ℓ1 * u)) := by
  simp only [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a ha => ?_
  rw [sum_comm]
  refine sum_congr rfl fun u hu => ?_
  rw [sum_ite_eq]
  simp only [mem_range, hK a (mem_range.1 ha) u (mem_range.1 hu), ↓reduceIte]

/-- A carry position collects at most two coefficients when `L ≤ 2 ℓ1`. -/
theorem convCoeff_le {L L' ℓ1 B : ℕ} (hℓ : 1 ≤ ℓ1) (hL : L ≤ 2 * ℓ1) (C : ℕ → ℕ → ℕ)
    (hC : ∀ a < L, ∀ u < L', C a u ≤ B) (k : ℕ) :
    (∑ a ∈ range L, ∑ u ∈ range L', if a + ℓ1 * u = k then C a u else 0) ≤ 2 * B := by
  rw [sum_comm]
  have hin : ∀ u ∈ range L', (∑ a ∈ range L, if a + ℓ1 * u = k then C a u else 0) ≤
      if ℓ1 * u ≤ k ∧ k < ℓ1 * (u + 2) then B else 0 := by
    intro u hu
    have : ∀ a ∈ range L, (if a + ℓ1 * u = k then C a u else 0) =
        if a = k - ℓ1 * u then (if ℓ1 * u ≤ k then C a u else 0) else 0 := by
      intro a _; split_ifs <;> first | rfl | omega
    rw [sum_congr rfl this, sum_ite_eq']
    by_cases h3 : k - ℓ1 * u ∈ range L <;> by_cases h4 : ℓ1 * u ≤ k
    · have hP : ℓ1 * u ≤ k ∧ k < ℓ1 * (u + 2) :=
        ⟨h4, by have := mem_range.1 h3; rw [mul_add]; omega⟩
      simp only [h3, h4, hP, ↓reduceIte, and_self]
      exact hC _ (mem_range.1 h3) u (mem_range.1 hu)
    all_goals simp [h3, h4]
  refine (sum_le_sum hin).trans ?_
  rw [← sum_filter, sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  have hsub : (range L').filter (fun u => ℓ1 * u ≤ k ∧ k < ℓ1 * (u + 2)) ⊆ {k / ℓ1 - 1, k / ℓ1} := by
    intro u hu
    rw [mem_filter] at hu
    obtain ⟨_, h3, h4⟩ := hu
    have e1 : u ≤ k / ℓ1 := (Nat.le_div_iff_mul_le hℓ).2 (by rw [mul_comm]; exact h3)
    have e2 : k / ℓ1 < u + 2 := (Nat.div_lt_iff_lt_mul hℓ).2 (by rw [mul_comm]; exact h4)
    simp only [mem_insert, mem_singleton]
    omega
  exact (card_le_card hsub).trans (card_le_two)

end Factoring.Fermat
