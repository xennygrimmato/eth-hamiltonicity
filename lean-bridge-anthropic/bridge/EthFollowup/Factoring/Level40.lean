/-
# The level with exponent 40 (module F5a, plan §0.6)

The level choice of `T2` (`EthFollowup/ExactHC/Theorem2.lean`, exponent 30) with exponent 40, read
from the length `n` of an input word: `K = K_ℓ` for the largest level `ℓ` with
`K_ℓ ≤ max(⌊n^{1/40}⌋, K₀)` (`pickOf` on the bound in unary).

* `rootN40 n = ⌊n^{1/40}⌋` (`rootN40_spec`);
* `bndL40 K₀ w`: `max(⌊|w|^{1/40}⌋, K₀)` in unary; `bndL40_polyT`;
* `kN40 kf K₀ w`: the number `K`; `kN40_polyT`, `kN40_unary`, `kN40_spec`;
* `kfacts40`: `K = K_ℓ ≥ 2`, `K^40 ≤ K₀^40 (n+2)` and `n + 2 ≤ K^{40 C₀ + 1}`.

Standard axioms only.
-/
import EthFollowup.ExactHC.Theorem2

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Groundwork Groundwork.Prog QueryMachines.Bridge CliqueLevels

/-- `⌊n^{1/40}⌋`. -/
def rootN40 (n : ℕ) : ℕ := ((List.range n).filter fun r => decide ((r + 1) ^ 40 ≤ n)).length

theorem rootN40_spec (n : ℕ) : rootN40 n ^ 40 ≤ n ∧ n < (rootN40 n + 1) ^ 40 := by
  have hn1 : n < (n + 1) ^ 40 :=
    calc n < n + 1 := Nat.lt_succ_self n
      _ = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ 40 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hex : ∃ r, n < (r + 1) ^ 40 := ⟨n, hn1⟩
  classical
  set t := Nat.find hex with ht
  have hiff : ∀ r, (r + 1) ^ 40 ≤ n ↔ r < t := fun r => by
    rw [ht, Nat.lt_find_iff]
    constructor
    · intro h m hm
      have : (m + 1) ^ 40 ≤ (r + 1) ^ 40 := Nat.pow_le_pow_left (by omega) _
      omega
    · intro h; have := h r le_rfl; omega
  have htn : t ≤ n := Nat.find_min' hex hn1
  have hr : rootN40 n = t := by
    unfold rootN40
    rw [ExactHC.T2.length_filter_range_lt _ t (fun r => by rw [decide_eq_true_iff]; exact hiff r) n]
    omega
  rw [hr]
  refine ⟨?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]; simp
  · have := (hiff (t - 1)).2 (by omega)
    rwa [Nat.sub_add_cancel hpos] at this

/-- The bound handed to the program that picks the level: `max(⌊|w|^{1/40}⌋, K₀)` in unary. -/
def bndL40 (K₀ : ℕ) (w : List Bool) : List Unit := List.replicate (max (rootN40 w.length) K₀) ()

theorem rootL40_polyT :
    PolyT fun w : List Bool => (List.range w.length).filter fun r => decide ((r + 1) ^ 40 ≤ w.length) := by
  have hr : PolyT fun w : List Bool => List.range w.length := PolyT.range (Unary.of_length PolyT.id')
  have h1 : PolyT fun p : List Bool × ℕ => p.2 + 1 := PolyT.add PolyT.id'.snd (PolyT.const 1)
  have h2 : PolyT fun p : List Bool × ℕ => (p.2 + 1) ^ 40 := PolyT.pow_const h1 40
  have h3 : PolyT fun p : List Bool × ℕ => p.1.length := PolyT.length PolyT.id'.fst
  have hf : PolyT fun p : List Bool × ℕ => decide ((p.2 + 1) ^ 40 ≤ p.1.length) := PolyT.decide_le h2 h3
  exact PolyT.filter (f := fun (w : List Bool) (r : ℕ) => decide ((r + 1) ^ 40 ≤ w.length)) hf hr

theorem rootN40_unary : Unary fun w : List Bool => rootN40 w.length := Unary.of_length rootL40_polyT

theorem rootN40_polyT : PolyT fun w : List Bool => rootN40 w.length := PolyT.length rootL40_polyT

theorem bndL40_polyT (K₀ : ℕ) : PolyT (bndL40 K₀) := by
  have h2 : Unary fun w : List Bool => max (rootN40 w.length) K₀ :=
    Unary.of_le (rootN40_unary.add (Unary.const K₀)) (PolyT.max' rootN40_polyT (PolyT.const K₀))
      fun w => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  unfold bndL40
  exact h2

variable (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- `(ℓ, (ℓ, K_ℓ))` in unary for the largest level `ℓ` with `K_ℓ ≤ max(⌊|w|^{1/40}⌋, K₀)`. -/
def pickL40 (w : List Bool) : List Unit × (List Unit × List Unit) := pickOf kf K₀ (bndL40 K₀ w)

/-- The number `K` of groups read from the input word `w`. -/
def kN40 (w : List Bool) : ℕ := (pickL40 kf K₀ w).2.2.length

section Facts

variable {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : Levels Kf e C₀) (hk : ComputesLevels Kf kf)
include hL hk

theorem kN40_polyT : PolyT (kN40 kf (Kf 0)) := by
  have := ExactHC.T2.pickOf_polyT kf hL hk
  have := bndL40_polyT (Kf 0)
  unfold kN40 pickL40; fun_prop

theorem kN40_unary : Unary (kN40 kf (Kf 0)) := by
  have := ExactHC.T2.pickOf_polyT kf hL hk
  have := bndL40_polyT (Kf 0)
  unfold kN40 pickL40; exact Unary.of_length (by fun_prop)

/-- `g = 3K⁸` in unary. -/
theorem gN40_unary : Unary fun w => 3 * kN40 kf (Kf 0) w ^ 8 := by
  have h := kN40_unary kf hL hk
  have h2 := h.mul h
  have h4 := h2.mul h2
  have h8 := h4.mul h4
  have e : (fun w => 3 * kN40 kf (Kf 0) w ^ 8) = fun w => 3 * (kN40 kf (Kf 0) w * kN40 kf (Kf 0) w *
      (kN40 kf (Kf 0) w * kN40 kf (Kf 0) w) * (kN40 kf (Kf 0) w * kN40 kf (Kf 0) w *
        (kN40 kf (Kf 0) w * kN40 kf (Kf 0) w))) := by
    funext w; ring
  rw [e]
  exact (Unary.const 3).mul h8

/-- The level picked: `K = K_ℓ ≤ max(⌊|w|^{1/40}⌋, K₀)` and `⌊|w|^{1/40}⌋ < K_{ℓ+1}`. -/
theorem kN40_spec (w : List Bool) : ∃ l, kN40 kf (Kf 0) w = Kf l ∧
    Kf l ≤ max (rootN40 w.length) (Kf 0) ∧ rootN40 w.length < Kf (l + 1) := by
  obtain ⟨h1, h2, h3⟩ := (pickOfFacts Kf e C₀ kf hL hk).2 (bndL40 (Kf 0) w)
  have hb : (bndL40 (Kf 0) w).length = max (rootN40 w.length) (Kf 0) := List.length_replicate
  refine ⟨(pickOf kf (Kf 0) (bndL40 (Kf 0) w)).1.length, ?_, ?_, ?_⟩
  · unfold kN40 pickL40; rw [h1]; exact List.length_replicate
  · rw [← hb]; exact h2 (by rw [hb]; exact le_max_right _ _)
  · rw [hb] at h3; exact lt_of_le_of_lt (le_max_left _ _) h3

/-- **The level of an input word of length `n`**: `K = K_ℓ ≥ 2`, `K^40 ≤ K₀^40 (n+2)` and
`n + 2 ≤ K^{40C₀+1}`. -/
theorem kfacts40 (w : List Bool) :
    ∃ l, kN40 kf (Kf 0) w = Kf l ∧ 2 ≤ Kf l ∧ Kf l ^ 40 ≤ Kf 0 ^ 40 * (w.length + 2) ∧
      w.length + 2 ≤ Kf l ^ (40 * C₀ + 1) := by
  obtain ⟨l, h1, h2, h3⟩ := kN40_spec kf hL hk w
  set n := w.length
  obtain ⟨r1, r2⟩ := rootN40_spec n
  have hK2 := hL.K_two l
  have h01 : 1 ≤ Kf 0 ^ 40 := Nat.one_le_pow _ _ (by have := hL.K_two 0; omega)
  refine ⟨l, h1, hK2, ?_, ?_⟩
  · have e1 : Kf l ^ 40 ≤ (max (rootN40 n) (Kf 0)) ^ 40 := Nat.pow_le_pow_left h2 40
    have e2 : (max (rootN40 n) (Kf 0)) ^ 40 ≤ rootN40 n ^ 40 + Kf 0 ^ 40 := by
      rcases le_total (rootN40 n) (Kf 0) with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    have e3 : n + Kf 0 ^ 40 ≤ Kf 0 ^ 40 * (n + 2) := by nlinarith
    omega
  · have e1 : rootN40 n + 1 ≤ Kf l ^ C₀ := (Nat.succ_le_of_lt h3).trans (hL.K_le l)
    have e2 : n + 1 ≤ Kf l ^ (40 * C₀) := by
      have := Nat.pow_le_pow_left e1 40
      rw [← pow_mul, mul_comm C₀ 40] at this
      omega
    rw [pow_succ]
    nlinarith

end Facts

/-- Sanity checks on small instances. -/
example : rootN40 0 = 0 := by decide
example : rootN40 1 = 1 := by decide

end EthFollowup.Factoring
