import Mathlib

/-!
# Isolation with a pairwise-independent family (Valiant–Vazirani step)

`H` is a finite index set (counting measure), `h : H → X → Y`, `M = |Y|`, `S ⊆ X` with `|S| = N`.
Hypotheses (only at the target value `y₀` are needed):
* uniform marginals: `#{p : h p x = y₀} * M = |H|`;
* pairwise: for `x ≠ x'`, `#{p : h p x = y₀ ∧ h p x' = y₀} * M^2 = |H|`.

Main bound (exact form): `M^2 * #{p : exactly one x ∈ S has h p x = y₀} ≥ |H| * (N*M - N^2 + N)`,
from the pointwise inequality `[c = 1] ≥ 2c - c^2` (Bonferroni / inclusion–exclusion).
Consequence: if `M ≤ 4N ≤ 3M` then the fraction is `≥ 3/16`. (This window contains the notes'
window `M/4 ≤ N ≤ M/2`.)
-/

open Finset

namespace IsoLean

variable {H X Y : Type*} [Fintype H] [DecidableEq Y]

/-- Number of `x ∈ S` mapped to `y₀` by `h p`. -/
def hits (h : H → X → Y) (S : Finset X) (y0 : Y) (p : H) : ℕ :=
  (S.filter (fun x => h p x = y0)).card

lemma sum_hits (h : H → X → Y) (S : Finset X) (y0 : Y) :
    ∑ p, hits h S y0 p = ∑ x ∈ S, (univ.filter (fun p => h p x = y0)).card := by
  simp only [hits, card_filter]
  exact sum_comm

lemma sum_hits_sq (h : H → X → Y) (S : Finset X) (y0 : Y) :
    ∑ p, hits h S y0 p ^ 2 =
      ∑ x ∈ S, ∑ x' ∈ S, (univ.filter (fun p => h p x = y0 ∧ h p x' = y0)).card := by
  simp only [hits, card_filter, sq, sum_mul_sum, ite_zero_mul_ite_zero, mul_one]
  rw [sum_comm]
  exact sum_congr rfl (fun _ _ => sum_comm)

/-- Exact Bonferroni bound: `M² · #unique ≥ |H| · (N M − N² + N)`. -/
theorem isolation_exact [DecidableEq X] [Fintype Y] (h : H → X → Y) (S : Finset X) (y0 : Y)
    (hu : ∀ x, (univ.filter (fun p => h p x = y0)).card * Fintype.card Y = Fintype.card H)
    (hpw : ∀ x x', x ≠ x' →
      (univ.filter (fun p => h p x = y0 ∧ h p x' = y0)).card * Fintype.card Y ^ 2
        = Fintype.card H) :
    (Fintype.card H : ℤ) * (S.card * Fintype.card Y - S.card ^ 2 + S.card) ≤
      (Fintype.card Y : ℤ) ^ 2 * (univ.filter (fun p => hits h S y0 p = 1)).card := by
  set M := Fintype.card Y
  set K := Fintype.card H
  set N := S.card
  -- first moment
  have hA : (∑ p, hits h S y0 p) * M ^ 2 = N * M * K := by
    rw [sum_hits, sum_mul]
    have : ∀ x ∈ S, (univ.filter (fun p => h p x = y0)).card * M ^ 2 = M * K := by
      intro x _; rw [sq, ← mul_assoc, hu x, mul_comm]
    rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_assoc]
  -- second moment
  have hB : (∑ p, hits h S y0 p ^ 2) * M ^ 2 = N * M * K + N * (N - 1) * K := by
    rw [sum_hits_sq, sum_mul]
    have : ∀ x ∈ S, (∑ x' ∈ S, (univ.filter (fun p => h p x = y0 ∧ h p x' = y0)).card) * M ^ 2
        = M * K + (N - 1) * K := by
      intro x hx
      rw [sum_mul, ← add_sum_erase _ _ hx]
      have hd : (univ.filter (fun p => h p x = y0 ∧ h p x = y0)).card * M ^ 2 = M * K := by
        simp only [and_self]; rw [sq, ← mul_assoc, hu x, mul_comm]
      have he : ∀ x' ∈ S.erase x,
          (univ.filter (fun p => h p x = y0 ∧ h p x' = y0)).card * M ^ 2 = K := by
        intro x' hx'
        exact hpw x x' (Ne.symm (ne_of_mem_erase hx'))
      rw [hd, sum_congr rfl he, sum_const, card_erase_of_mem hx, smul_eq_mul]
    rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_add, ← mul_assoc, ← mul_assoc]
  -- pointwise inequality `[c = 1] ≥ 2c - c²`
  have hpt : ∀ p, (2 * (hits h S y0 p : ℤ) - (hits h S y0 p : ℤ) ^ 2) ≤
      (if hits h S y0 p = 1 then 1 else 0 : ℤ) := by
    intro p
    rcases Nat.lt_or_ge (hits h S y0 p) 2 with hc | hc
    · interval_cases (hits h S y0 p) <;> simp
    · rw [if_neg (by omega)]
      have : (2 : ℤ) ≤ hits h S y0 p := by exact_mod_cast hc
      nlinarith
  have hU : ((univ.filter (fun p => hits h S y0 p = 1)).card : ℤ)
      = ∑ p, (if hits h S y0 p = 1 then 1 else 0 : ℤ) := by
    rw [card_filter]; push_cast; rfl
  have hsum : ∑ p, (2 * (hits h S y0 p : ℤ) - (hits h S y0 p : ℤ) ^ 2) ≤
      ((univ.filter (fun p => hits h S y0 p = 1)).card : ℤ) := by
    rw [hU]; exact sum_le_sum (fun p _ => hpt p)
  rw [sum_sub_distrib, ← mul_sum] at hsum
  have hA' : ((∑ p, hits h S y0 p : ℕ) : ℤ) * M ^ 2 = N * M * K := by exact_mod_cast hA
  have hB' : ((∑ p, hits h S y0 p ^ 2 : ℕ) : ℤ) * M ^ 2 = N * M * K + N * ((N : ℤ) - 1) * K := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · have h0 : (∑ p, hits h S y0 p ^ 2) * M ^ 2 = 0 := by rw [hB, hN]; simp
      have : ((∑ p, hits h S y0 p ^ 2 : ℕ) : ℤ) * M ^ 2 = 0 := by exact_mod_cast h0
      rw [this, hN]; ring
    · have h1 : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
      rw [← h1]; exact_mod_cast hB
  push_cast at hA' hB'
  have hMnn : (0 : ℤ) ≤ (M : ℤ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hsum hMnn
  nlinarith [this, hA', hB']

/-- **Isolation bound.** If `M ≤ 4N ≤ 3M` then at least a `3/16` fraction of `H` isolates
exactly one element of `S` at `y₀`. (`M/4 ≤ N ≤ M/2` is a special case.) -/
theorem isolation [DecidableEq X] [Fintype Y] (h : H → X → Y) (S : Finset X) (y0 : Y)
    (hu : ∀ x, (univ.filter (fun p => h p x = y0)).card * Fintype.card Y = Fintype.card H)
    (hpw : ∀ x x', x ≠ x' →
      (univ.filter (fun p => h p x = y0 ∧ h p x' = y0)).card * Fintype.card Y ^ 2
        = Fintype.card H)
    (h1 : Fintype.card Y ≤ 4 * S.card) (h2 : 4 * S.card ≤ 3 * Fintype.card Y) :
    3 * Fintype.card H ≤ 16 * (univ.filter (fun p => hits h S y0 p = 1)).card := by
  have he := isolation_exact h S y0 hu hpw
  set M := Fintype.card Y
  set K := Fintype.card H
  set N := S.card
  set U := (univ.filter (fun p => hits h S y0 p = 1)).card
  have hMpos : 0 < M := Fintype.card_pos_iff.mpr ⟨y0⟩
  have h1' : (M : ℤ) ≤ 4 * N := by exact_mod_cast h1
  have h2' : (4 * N : ℤ) ≤ 3 * M := by exact_mod_cast h2
  have hK : (0 : ℤ) ≤ K := by positivity
  have hN : (0 : ℤ) ≤ N := by positivity
  have hq : (0 : ℤ) ≤ (4 * N - M) * (3 * M - 4 * N) := mul_nonneg (by linarith) (by linarith)
  -- 16 (N M - N²) - 3 M² = (4N - M)(3M - 4N)
  have key : (M : ℤ) ^ 2 * (3 * K) ≤ (M : ℤ) ^ 2 * (16 * U) := by
    nlinarith [mul_nonneg hK hq, mul_nonneg hK hN]
  have hM2 : (0 : ℤ) < (M : ℤ) ^ 2 := by positivity
  have := le_of_mul_le_mul_left key hM2
  exact_mod_cast this

/-- The notes' window `M/4 ≤ N ≤ M/2`, constant `3/16`. -/
theorem isolation_notes_window [DecidableEq X] [Fintype Y] (h : H → X → Y) (S : Finset X) (y0 : Y)
    (hu : ∀ x, (univ.filter (fun p => h p x = y0)).card * Fintype.card Y = Fintype.card H)
    (hpw : ∀ x x', x ≠ x' →
      (univ.filter (fun p => h p x = y0 ∧ h p x' = y0)).card * Fintype.card Y ^ 2
        = Fintype.card H)
    (h1 : Fintype.card Y ≤ 4 * S.card) (h2 : 2 * S.card ≤ Fintype.card Y) :
    3 * Fintype.card H ≤ 16 * (univ.filter (fun p => hits h S y0 p = 1)).card :=
  isolation h S y0 hu hpw h1 (by omega)

end IsoLean
