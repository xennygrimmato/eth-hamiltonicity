/-
# The carry chain (module F1, part 4)

Pure Mathlib; compiles in both toolchains.

Digits `c k` (any size), target limbs `nl k = N / 2^(b k) % 2^b`, carries `r k`.
The local check at position `k` (`carryStep`) is
`nl k ≤ c k + r k ∧ (c k + r k - nl k) % 2^b = 0 ∧ r (k+1) = (c k + r k - nl k) / 2^b`;
`ChainOK b K c nl r` adds `r 0 = 0` and `r K = 0`.

* `chain_iff`: for `N < 2^(b K)`, a valid carry chain exists iff `Σ_{k<K} c k 2^(b k) = N`;
* `chain_unique`: the carries of a valid chain are `r k = (Σ_{j<k} c j 2^(b j)) / 2^(b k)` (`k ≤ K`),
  so they are uniquely determined; `carry` (the recursive carry) is that chain (`chain_iff_carry`);
* `carry_le`: carries are bounded by any bound on the digits (for `b ≥ 1`).
-/
import EthFollowup.Factoring.Kronecker

set_option linter.unusedSectionVars false

namespace Factoring.Fermat

open Finset

/-- The check at one carry position. -/
def carryStep (b c r n r' : ℕ) : Prop :=
  n ≤ c + r ∧ (c + r - n) % 2 ^ b = 0 ∧ r' = (c + r - n) / 2 ^ b

/-- A valid carry chain of length `K`. -/
def ChainOK (b K : ℕ) (c nl r : ℕ → ℕ) : Prop :=
  r 0 = 0 ∧ r K = 0 ∧ ∀ k < K, carryStep b (c k) (r k) (nl k) (r (k + 1))

/-- The recursive carry: `carry 0 = 0`, `carry (k+1) = (c k + carry k - nl k) / 2^b`. -/
def carry (b : ℕ) (c nl : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (c k + carry b c nl k - nl k) / 2 ^ b

@[simp] theorem carry_zero (b : ℕ) (c nl : ℕ → ℕ) : carry b c nl 0 = 0 := rfl
theorem carry_succ (b : ℕ) (c nl : ℕ → ℕ) (k : ℕ) :
    carry b c nl (k + 1) = (c k + carry b c nl k - nl k) / 2 ^ b := rfl

/-- Partial digit sums `A k = Σ_{j<k} c j 2^(b j)`. -/
def psum (b : ℕ) (c : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ range k, c j * 2 ^ (b * j)

theorem psum_succ (b : ℕ) (c : ℕ → ℕ) (k : ℕ) : psum b c (k + 1) = psum b c k + c k * 2 ^ (b * k) := by
  simp [psum, sum_range_succ]

/-- Splitting a digit sum at `k ≤ K`. -/
theorem psum_split (b : ℕ) (c : ℕ → ℕ) {k K : ℕ} (hk : k ≤ K) :
    psum b c K = psum b c k + 2 ^ (b * k) * ∑ j ∈ range (K - k), c (k + j) * 2 ^ (b * j) := by
  unfold psum
  conv_lhs => rw [show K = k + (K - k) by omega, sum_range_add]
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun j _ => by rw [mul_add, pow_add]; ring

theorem carryStep_eq {b c r n r' : ℕ} (h : carryStep b c r n r') : c + r = n + 2 ^ b * r' := by
  obtain ⟨h1, h2, h3⟩ := h
  have := Nat.div_add_mod (c + r - n) (2 ^ b)
  rw [h2, add_zero, ← h3] at this
  omega

/-- The invariant of a chain: `A k = N % 2^(b k) + r k · 2^(b k)`. -/
theorem chain_inv {b N : ℕ} {c r : ℕ → ℕ} (h0 : r 0 = 0) : ∀ k : ℕ,
    (∀ j < k, carryStep b (c j) (r j) (N / 2 ^ (b * j) % 2 ^ b) (r (j + 1))) →
      psum b c k = N % 2 ^ (b * k) + r k * 2 ^ (b * k)
  | 0, _ => by simp [psum, h0, Nat.mod_one]
  | k + 1, h => by
    have ih := chain_inv h0 k fun j hj => h j (by omega)
    have hs := carryStep_eq (h k (by omega))
    rw [psum_succ, ih, limb_sum b N (k + 1), sum_range_succ, ← limb_sum b N k]
    have e : 2 ^ (b * (k + 1)) = 2 ^ b * 2 ^ (b * k) := by rw [mul_add, mul_one, pow_add, mul_comm]
    rw [e]
    calc N % 2 ^ (b * k) + r k * 2 ^ (b * k) + c k * 2 ^ (b * k)
        = N % 2 ^ (b * k) + (c k + r k) * 2 ^ (b * k) := by ring
      _ = _ := by rw [hs]; ring

/-- Carries of a valid chain are the scaled partial sums; in particular they are unique. -/
theorem chain_unique {b K N : ℕ} {c r : ℕ → ℕ}
    (h : ChainOK b K c (fun k => N / 2 ^ (b * k) % 2 ^ b) r) :
    ∀ k ≤ K, r k = psum b c k / 2 ^ (b * k) := by
  intro k hk
  rw [chain_inv h.1 k fun j hj => h.2.2 j (by omega)]
  have hpos : 0 < 2 ^ (b * k) := by positivity
  rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (Nat.mod_lt _ hpos), zero_add]

/-- A valid chain computes `N`. -/
theorem chain_sum {b K N : ℕ} (hN : N < 2 ^ (b * K)) {c r : ℕ → ℕ}
    (h : ChainOK b K c (fun k => N / 2 ^ (b * k) % 2 ^ b) r) :
    ∑ k ∈ range K, c k * 2 ^ (b * k) = N := by
  have := chain_inv h.1 K fun j hj => h.2.2 j hj
  rw [h.2.1, zero_mul, add_zero, Nat.mod_eq_of_lt hN] at this
  exact this

/-- Conversely, the scaled partial sums form a valid chain when the digits sum to `N`. -/
theorem chain_of_sum {b K N : ℕ} (hN : N < 2 ^ (b * K)) {c : ℕ → ℕ}
    (hs : ∑ k ∈ range K, c k * 2 ^ (b * k) = N) :
    ChainOK b K c (fun k => N / 2 ^ (b * k) % 2 ^ b) fun k => psum b c k / 2 ^ (b * k) := by
  have hS : psum b c K = N := hs
  refine ⟨by simp [psum], ?_, ?_⟩
  · show psum b c K / 2 ^ (b * K) = 0
    rw [hS]; exact Nat.div_eq_of_lt hN
  · intro k hk
    have hm : 0 < 2 ^ (b * k) := by positivity
    have hb : 0 < 2 ^ b := by positivity
    have e : 2 ^ (b * (k + 1)) = 2 ^ (b * k) * 2 ^ b := by rw [mul_add, mul_one, pow_add]
    -- the next carry
    have hnext : psum b c (k + 1) / 2 ^ (b * (k + 1)) = (c k + psum b c k / 2 ^ (b * k)) / 2 ^ b := by
      rw [psum_succ, e, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ hm, add_comm]
    -- the target limb
    have hlimb : N / 2 ^ (b * k) % 2 ^ b = (c k + psum b c k / 2 ^ (b * k)) % 2 ^ b := by
      rw [← hS, psum_split b c (show k + 1 ≤ K by omega), e, mul_assoc,
        Nat.add_mul_div_left _ _ hm, Nat.add_mul_mod_self_left, psum_succ,
        Nat.add_mul_div_right _ _ hm, add_comm]
    show carryStep b (c k) (psum b c k / 2 ^ (b * k)) (N / 2 ^ (b * k) % 2 ^ b)
      (psum b c (k + 1) / 2 ^ (b * (k + 1)))
    rw [carryStep, hnext, hlimb]
    set x := c k + psum b c k / 2 ^ (b * k)
    have := Nat.div_add_mod x (2 ^ b)
    refine ⟨Nat.mod_le _ _, ?_, ?_⟩
    · rw [show x - x % 2 ^ b = 2 ^ b * (x / 2 ^ b) by omega, Nat.mul_mod_right]
    · rw [show x - x % 2 ^ b = 2 ^ b * (x / 2 ^ b) by omega, Nat.mul_div_cancel_left _ hb]

/-- The carry chain lemma: for `N < 2^(b K)`, a valid carry chain exists iff `Σ c k 2^(b k) = N`. -/
theorem chain_iff {b K N : ℕ} (hN : N < 2 ^ (b * K)) (c : ℕ → ℕ) :
    (∃ r, ChainOK b K c (fun k => N / 2 ^ (b * k) % 2 ^ b) r) ↔
      ∑ k ∈ range K, c k * 2 ^ (b * k) = N :=
  ⟨fun ⟨_, h⟩ => chain_sum hN h, fun h => ⟨_, chain_of_sum hN h⟩⟩

/-- Any sequence obeying the carry recursion below `K` agrees with `carry` up to `K`. -/
theorem eq_carry_of_rec {b K : ℕ} {c nl r : ℕ → ℕ} (h0 : r 0 = 0)
    (hs : ∀ k < K, r (k + 1) = (c k + r k - nl k) / 2 ^ b) : ∀ k ≤ K, r k = carry b c nl k
  | 0, _ => h0
  | k + 1, hk => by rw [hs k (by omega), carry_succ, eq_carry_of_rec h0 hs k (by omega)]

/-- The recursive carry is a valid chain iff the digits sum to `N` (for `N < 2^(b K)`). -/
theorem chain_iff_carry {b K N : ℕ} (hN : N < 2 ^ (b * K)) (c : ℕ → ℕ) :
    ChainOK b K c (fun k => N / 2 ^ (b * k) % 2 ^ b) (carry b c fun k => N / 2 ^ (b * k) % 2 ^ b) ↔
      ∑ k ∈ range K, c k * 2 ^ (b * k) = N := by
  refine ⟨chain_sum hN, fun h => ?_⟩
  have hc := chain_of_sum hN h
  have heq := eq_carry_of_rec (K := K) (r := fun k => psum b c k / 2 ^ (b * k))
    (nl := fun k => N / 2 ^ (b * k) % 2 ^ b) hc.1 fun k hk => (hc.2.2 k hk).2.2
  refine ⟨rfl, ?_, fun k hk => ?_⟩
  · rw [← heq K le_rfl]; exact hc.2.1
  · rw [← heq k hk.le, ← heq (k + 1) hk]; exact hc.2.2 k hk

/-- Carries are bounded by any bound on the digits (limb width `b ≥ 1`). -/
theorem carry_le {b B : ℕ} (hb : 1 ≤ b) {c nl : ℕ → ℕ} (hc : ∀ k, c k ≤ B) :
    ∀ k, carry b c nl k ≤ B
  | 0 => Nat.zero_le _
  | k + 1 => by
    rw [carry_succ]
    have ih := carry_le hb (nl := nl) hc k
    have h2 : 2 ≤ 2 ^ b := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    calc (c k + carry b c nl k - nl k) / 2 ^ b ≤ (B + B) / 2 :=
          Nat.div_le_div (by have := hc k; omega) h2 (by norm_num)
      _ ≤ B := by omega

end Factoring.Fermat
