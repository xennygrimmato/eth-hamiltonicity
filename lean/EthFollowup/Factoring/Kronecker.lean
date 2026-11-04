/-
# Kronecker (limb) evaluation, coefficient bounds and value recovery (module F1, part 3)

Pure Mathlib; compiles in both toolchains.

* `sum_ite_add_mul`, `aconv2_eval`: in a commutative semiring,
  `Σ_{a<L} Σ_{u<L'} aconv2 n1 n2 f g a u · X^a Y^u = (Σ_{i2,i1} f i1 i2 X^i1 Y^i2)(Σ g …)`
  whenever `2 n1 ≤ L + 1`, `2 n2 ≤ L' + 1`; `aconv2_eval_two_pow`: the limb form with
  `X = 2^b`, `Y = 2^(b n1)`, weights `2^(b (a + n1 u))`.
* `aconv2_le`: `aconv2 ≤ n1 n2 B²` for entries `≤ B`; `aconv2_cast`: casts commute with `aconv2`.
* `limb_sum`: `x % 2^(b K) = Σ_{k<K} (x / 2^(b k) % 2^b) 2^(b k)`; `sum_range_mul`: re-indexing
  `k = i1 + n1 i2`; `limb_sum2`: a number below `2^(b n1 n2)` is the sum of its 2D limb array.
* `eq_of_cast_eq_of_lt`: value recovery (a residue `y % M` whose cast equals that of `c < M` is `c`).
-/
import EthFollowup.Factoring.DFT

set_option linter.unusedSectionVars false

namespace Factoring.Fermat

open Finset

section Semiring
variable {R : Type*} [CommSemiring R]

/-- Collapsing a sum over the "output index" of an acyclic convolution-like expression. -/
theorem sum_ite_add_mul {n L : ℕ} (hn : n + n ≤ L + 1) (H : ℕ → ℕ → R) (w : ℕ → R) :
    ∑ a ∈ range L, (∑ i ∈ range n, ∑ j ∈ range n, if i + j = a then H i j else 0) * w a =
      ∑ i ∈ range n, ∑ j ∈ range n, H i j * w (i + j) := by
  simp only [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_ite_eq]
  rw [mem_range] at hi hj
  simp only [mem_range, show i + j < L by omega, ↓reduceIte]

/-- 1D Kronecker evaluation. -/
theorem aconv_eval {n L : ℕ} (hn : n + n ≤ L + 1) (f g : ℕ → R) (X : R) :
    ∑ a ∈ range L, aconv n f g a * X ^ a =
      (∑ i ∈ range n, f i * X ^ i) * ∑ j ∈ range n, g j * X ^ j := by
  simp only [aconv]
  rw [sum_ite_add_mul hn (fun i j => f i * g j) (fun a => X ^ a), sum_mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [pow_add]; ring

/-- 2D Kronecker evaluation. -/
theorem aconv2_eval {n1 n2 L L' : ℕ} (h1 : n1 + n1 ≤ L + 1) (h2 : n2 + n2 ≤ L' + 1)
    (f g : ℕ → ℕ → R) (X Y : R) :
    ∑ a ∈ range L, ∑ u ∈ range L', aconv2 n1 n2 f g a u * (X ^ a * Y ^ u) =
      (∑ i2 ∈ range n2, ∑ i1 ∈ range n1, f i1 i2 * (X ^ i1 * Y ^ i2)) *
        ∑ j2 ∈ range n2, ∑ j1 ∈ range n1, g j1 j2 * (X ^ j1 * Y ^ j2) := by
  rw [sum_comm]
  have hin : ∀ u, ∑ a ∈ range L, aconv2 n1 n2 f g a u * (X ^ a * Y ^ u) =
      (∑ i2 ∈ range n2, ∑ j2 ∈ range n2, if i2 + j2 = u then
        (∑ i1 ∈ range n1, f i1 i2 * X ^ i1) * (∑ j1 ∈ range n1, g j1 j2 * X ^ j1) else 0) * Y ^ u := by
    intro u
    simp only [aconv2, ← mul_assoc]
    rw [← sum_mul]
    congr 1
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i2 _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j2 _ => ?_
    split_ifs
    · rw [← sum_mul, ← aconv_eval h1]
    · simp
  simp only [hin]
  rw [sum_ite_add_mul h2 _ (fun u => Y ^ u), sum_mul_sum]
  refine sum_congr rfl fun i2 _ => sum_congr rfl fun j2 _ => ?_
  rw [pow_add, sum_mul_sum, sum_mul_sum, sum_mul]
  exact sum_congr rfl fun i1 _ => by
    rw [sum_mul]; exact sum_congr rfl fun j1 _ => by ring

end Semiring

/-- Casts commute with the acyclic 2D convolution. -/
theorem aconv2_cast {R : Type*} [CommRing R] (n1 n2 : ℕ) (f g : ℕ → ℕ → ℕ) (a u : ℕ) :
    ((aconv2 n1 n2 f g a u : ℕ) : R) =
      aconv2 n1 n2 (fun i1 i2 => (f i1 i2 : R)) (fun j1 j2 => (g j1 j2 : R)) a u := by
  simp only [aconv2, aconv]; push_cast; rfl

/-- Limb form of 2D Kronecker evaluation (weights `2^(b (a + n1 u))`). -/
theorem aconv2_eval_two_pow {n1 n2 L L' : ℕ} (h1 : n1 + n1 ≤ L + 1) (h2 : n2 + n2 ≤ L' + 1)
    (b : ℕ) (f g : ℕ → ℕ → ℕ) :
    ∑ a ∈ range L, ∑ u ∈ range L', aconv2 n1 n2 f g a u * 2 ^ (b * (a + n1 * u)) =
      (∑ i2 ∈ range n2, ∑ i1 ∈ range n1, f i1 i2 * 2 ^ (b * (i1 + n1 * i2))) *
        ∑ j2 ∈ range n2, ∑ j1 ∈ range n1, g j1 j2 * 2 ^ (b * (j1 + n1 * j2)) := by
  have hw : ∀ x y, (2 : ℕ) ^ (b * (x + n1 * y)) = (2 ^ b) ^ x * (2 ^ (b * n1)) ^ y := by
    intro x y; rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  simp only [hw]
  exact aconv2_eval h1 h2 f g _ _

/-! ## Coefficient bound -/

theorem sum_ite_add_le {n i a C : ℕ} (h : ℕ → ℕ) (hh : ∀ j, h j ≤ C) :
    ∑ j ∈ range n, (if i + j = a then h j else 0) ≤ C := by
  have : ∀ j ∈ range n, (if i + j = a then h j else 0) =
      if j = a - i then (if i ≤ a then h j else 0) else 0 := by
    intro j _; split_ifs <;> first | rfl | omega
  rw [sum_congr rfl this, sum_ite_eq']
  split_ifs <;> simp [hh]

theorem aconv_le {n B : ℕ} (f g : ℕ → ℕ) (hf : ∀ i, f i ≤ B) (hg : ∀ j, g j ≤ B) (a : ℕ) :
    aconv n f g a ≤ n * (B * B) := by
  unfold aconv
  calc _ ≤ ∑ _i ∈ range n, B * B := sum_le_sum fun i _ =>
        sum_ite_add_le (fun j => f i * g j) fun j => Nat.mul_le_mul (hf i) (hg j)
    _ = n * (B * B) := by simp

/-- The 2D acyclic convolution of arrays with entries `≤ B` is at most `n1 n2 B²`. -/
theorem aconv2_le {n1 n2 B : ℕ} (f g : ℕ → ℕ → ℕ) (hf : ∀ i1 i2, f i1 i2 ≤ B)
    (hg : ∀ j1 j2, g j1 j2 ≤ B) (a u : ℕ) : aconv2 n1 n2 f g a u ≤ n1 * n2 * (B * B) := by
  unfold aconv2
  calc _ ≤ ∑ _i ∈ range n2, n1 * (B * B) := sum_le_sum fun i2 _ =>
        sum_ite_add_le (fun j2 => aconv n1 (fun i1 => f i1 i2) (fun j1 => g j1 j2) a)
          fun j2 => aconv_le _ _ (fun i1 => hf i1 i2) (fun j1 => hg j1 j2) a
    _ = n1 * n2 * (B * B) := by simp; ring

/-- The plan's bound: for limbs `≤ 2^b` and `n1 n2 2^(2b) ≤ 2^J`, coefficients are `≤ 2^J < 2^J + 1`. -/
theorem aconv2_le_two_pow {n1 n2 b J : ℕ} (hJ : n1 * n2 * 2 ^ (2 * b) ≤ 2 ^ J) (f g : ℕ → ℕ → ℕ)
    (hf : ∀ i1 i2, f i1 i2 < 2 ^ b) (hg : ∀ j1 j2, g j1 j2 < 2 ^ b) (a u : ℕ) :
    aconv2 n1 n2 f g a u ≤ 2 ^ J := by
  refine le_trans (aconv2_le (B := 2 ^ b) f g (fun i1 i2 => (hf i1 i2).le)
    (fun j1 j2 => (hg j1 j2).le) a u) ?_
  rw [← pow_add, ← two_mul]; exact hJ

/-! ## Value recovery -/

/-- If `(y : ZMod M) = (c : ZMod M)` and `c < M` then `y % M = c`. -/
theorem eq_of_cast_eq_of_lt {M y c : ℕ} (h : ((y : ℕ) : ZMod M) = ((c : ℕ) : ZMod M)) (hc : c < M) :
    y % M = c := by
  rw [ZMod.natCast_eq_natCast_iff'] at h; rw [h, Nat.mod_eq_of_lt hc]

/-- The canonical residue of `c < M` is `c`. -/
theorem val_natCast_eq {M c : ℕ} (hc : c < M) : ((c : ℕ) : ZMod M).val = c := ZMod.val_cast_of_lt hc

/-! ## Limbs -/

/-- `x % 2^(b K) = Σ_{k<K} (x / 2^(b k) % 2^b) · 2^(b k)`. -/
theorem limb_sum (b x : ℕ) : ∀ K : ℕ,
    x % 2 ^ (b * K) = ∑ k ∈ range K, x / 2 ^ (b * k) % 2 ^ b * 2 ^ (b * k)
  | 0 => by simp [Nat.mod_one]
  | K + 1 => by
    rw [sum_range_succ, ← limb_sum b x K, mul_add, mul_one, pow_add, Nat.mod_mul]
    ring

/-- Re-indexing `k = i1 + n1 i2`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (n1 : ℕ) (F : ℕ → M) : ∀ n2 : ℕ,
    ∑ k ∈ range (n1 * n2), F k = ∑ i2 ∈ range n2, ∑ i1 ∈ range n1, F (i1 + n1 * i2)
  | 0 => by simp
  | n2 + 1 => by
    rw [mul_add, mul_one, sum_range_add, sum_range_mul n1 F n2, sum_range_succ]
    congr 1
    exact sum_congr rfl fun i1 _ => by rw [add_comm]

/-- A number below `2^(b n1 n2)` is the evaluation of its 2D limb array
`(i1, i2) ↦ x / 2^(b (i1 + n1 i2)) % 2^b`. -/
theorem limb_sum2 (b n1 n2 x : ℕ) (hx : x < 2 ^ (b * (n1 * n2))) :
    x = ∑ i2 ∈ range n2, ∑ i1 ∈ range n1,
      x / 2 ^ (b * (i1 + n1 * i2)) % 2 ^ b * 2 ^ (b * (i1 + n1 * i2)) := by
  rw [← sum_range_mul n1 (fun k => x / 2 ^ (b * k) % 2 ^ b * 2 ^ (b * k)), ← limb_sum,
    Nat.mod_eq_of_lt hx]

end Factoring.Fermat
