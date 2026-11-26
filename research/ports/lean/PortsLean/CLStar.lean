import Mathlib

/-!
# Inequality (CL*) — an analytic proof

Source: `research/ports/note-k23-rate.md` §3.3 (the inequality, its algebraic form (3.5) and the
slice (I)) and `research/ports/k2m/clstar_analytic.py` (the analytic chain). Until now (CL*) was
certified only by interval arithmetic (`tools/ivcert/src/problems/clstar.rs`).

Notation: σ = (s12, s13, s21, s23, s31, s32) ∈ [−1,1]⁶, c_x = √(1 − s_x²),
* `V = |s12−s13| + |s21−s23| + |s31−s32|`,
* `E = |s12+s21| + |s13+s31| + |s23+s32|`,
* `m = max |s_x|`.

The proof:
1. hexagon lemma `V + E ≥ 2|s_x|` for each of the six coordinates;
2. every `c_x ≥ √(1−m²)`;
3. Cauchy–Schwarz `√(x² + K y²) ≥ x·a + t·m·|y|` with `a = √(1−m²)`, `b = m` (`a² + b² = 1`)
   and `t² ≤ K`;
4. `Φ + 3 ≥ 3(1−m²) + (t m/2)(V + E) ≥ 3(1−m²) + t m² ≥ 3` when `t ≥ 3`.

Remark on step 3. The informal proof takes `sin χ = 3m/√(9+w²)`, so `√K sin χ = 3m/w` for
`K = 1 + 9/w²` and `cos χ ≥ √(1−m²)`; that choice is correct. Here we take the simpler direction
`(a, b) = (√(1−m²), m)`; it only needs `√K ≥ 3/w`, i.e. **`K ≥ 9/w²`**. So the argument proves the
sharper constant (`K = 9` at `w = 1`, "1 + 8 sin²" in the trigonometric form) as well, and
`clstar_K_sharp` shows that `K = 9` cannot be lowered (the point (1,−1,−1,−1,1,1) gives
`Φ = √K − 3`).
-/

namespace PortsLean.CLStar

open Real

/-- The weighted functional `Φ` with inner constant `K` and edge weight `t/2`
(for the note's `Φ_w`: `K = 1 + 9/w²`, `t = 3/w`). -/
noncomputable def Phi (K t s12 s13 s21 s23 s31 s32 : ℝ) : ℝ :=
  (√((√(1 - s12^2) + √(1 - s13^2))^2 + K * (s12 - s13)^2)
   + √((√(1 - s21^2) + √(1 - s23^2))^2 + K * (s21 - s23)^2)
   + √((√(1 - s31^2) + √(1 - s32^2))^2 + K * (s31 - s32)^2)) / 2 - 3
  + t / 2 * (|s12 + s21| + |s13 + s31| + |s23 + s32|)

/-- Cauchy–Schwarz in the form used: `(x a + t m |y|)² ≤ (x² + t² y²)(a² + m²)` with
`a = √(1−m²)`. -/
lemma pair_bound {K t m x y : ℝ} (hK : t ^ 2 ≤ K) (hm1 : m ≤ 1) (hm0 : 0 ≤ m) :
    x * √(1 - m ^ 2) + t * m * |y| ≤ √(x ^ 2 + K * y ^ 2) := by
  have ha2 : (√(1 - m ^ 2)) ^ 2 = 1 - m ^ 2 := sq_sqrt (by nlinarith)
  have hY2 : |y| ^ 2 = y ^ 2 := sq_abs y
  apply le_sqrt_of_sq_le
  have h1 : t ^ 2 * y ^ 2 ≤ K * y ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg y)
  have key : x ^ 2 + t ^ 2 * y ^ 2 - (x * √(1 - m ^ 2) + t * m * |y|) ^ 2
      = (x * m - t * |y| * √(1 - m ^ 2)) ^ 2 := by
    linear_combination (-x ^ 2 - t ^ 2 * |y| ^ 2) * ha2 - t ^ 2 * hY2
  linarith [sq_nonneg (x * m - t * |y| * √(1 - m ^ 2))]

/-- Step 2: `c ≥ √(1−m²)` when `|s| ≤ m`. -/
lemma c_ge {s m : ℝ} (h : |s| ≤ m) : √(1 - m ^ 2) ≤ √(1 - s ^ 2) := by
  apply sqrt_le_sqrt
  have : s ^ 2 ≤ m ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h); simpa using this
  linarith

/-- The core estimate: for any `m` with all `|s_x| ≤ m ≤ 1` and `2m ≤ V + E`, `Φ ≥ 0`
whenever `t ≥ 3` and `K ≥ t²`. -/
theorem core {K t m s12 s13 s21 s23 s31 s32 : ℝ} (hK : t ^ 2 ≤ K) (ht : 3 ≤ t)
    (hm1 : m ≤ 1)
    (h12 : |s12| ≤ m) (h13 : |s13| ≤ m) (h21 : |s21| ≤ m) (h23 : |s23| ≤ m)
    (h31 : |s31| ≤ m) (h32 : |s32| ≤ m)
    (hVE : 2 * m ≤ (|s12 - s13| + |s21 - s23| + |s31 - s32|)
                   + (|s12 + s21| + |s13 + s31| + |s23 + s32|)) :
    0 ≤ Phi K t s12 s13 s21 s23 s31 s32 := by
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) h12
  set a := √(1 - m ^ 2) with ha_def
  have ha : 0 ≤ a := sqrt_nonneg _
  have ha2 : a ^ 2 = 1 - m ^ 2 := sq_sqrt (by nlinarith)
  have t0 : 0 ≤ t := by linarith
  have p1 := pair_bound (x := √(1 - s12 ^ 2) + √(1 - s13 ^ 2)) (y := s12 - s13) hK hm1 hm0
  have p2 := pair_bound (x := √(1 - s21 ^ 2) + √(1 - s23 ^ 2)) (y := s21 - s23) hK hm1 hm0
  have p3 := pair_bound (x := √(1 - s31 ^ 2) + √(1 - s32 ^ 2)) (y := s31 - s32) hK hm1 hm0
  have q12 := c_ge h12; have q13 := c_ge h13; have q21 := c_ge h21
  have q23 := c_ge h23; have q31 := c_ge h31; have q32 := c_ge h32
  rw [← ha_def] at p1 p2 p3 q12 q13 q21 q23 q31 q32
  -- (c + c') a ≥ 2 a²
  have u12 := mul_le_mul_of_nonneg_right q12 ha
  have u13 := mul_le_mul_of_nonneg_right q13 ha
  have u21 := mul_le_mul_of_nonneg_right q21 ha
  have u23 := mul_le_mul_of_nonneg_right q23 ha
  have u31 := mul_le_mul_of_nonneg_right q31 ha
  have u32 := mul_le_mul_of_nonneg_right q32 ha
  have hE0 : 0 ≤ |s12 + s21| + |s13 + s31| + |s23 + s32| := by positivity
  have hEm := mul_le_mul_of_nonneg_left hm1 (mul_nonneg t0 hE0)
  have hfin := mul_le_mul_of_nonneg_left hVE (mul_nonneg t0 hm0)
  have hm2 : 3 * m ^ 2 ≤ t * m ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg m)
  unfold Phi
  linarith

/-- Hexagon lemma: `2|s_x| ≤ V + E` for each coordinate (here stated for all six at once). -/
lemma hexagon (s12 s13 s21 s23 s31 s32 : ℝ) :
    let VE := (|s12 - s13| + |s21 - s23| + |s31 - s32|)
                + (|s12 + s21| + |s13 + s31| + |s23 + s32|)
    2 * |s12| ≤ VE ∧ 2 * |s13| ≤ VE ∧ 2 * |s21| ≤ VE ∧ 2 * |s23| ≤ VE ∧
      2 * |s31| ≤ VE ∧ 2 * |s32| ≤ VE := by
  intro VE
  have a1 := le_abs_self (s12 - s13); have b1 := neg_abs_le (s12 - s13)
  have a2 := le_abs_self (s21 - s23); have b2 := neg_abs_le (s21 - s23)
  have a3 := le_abs_self (s31 - s32); have b3 := neg_abs_le (s31 - s32)
  have a4 := le_abs_self (s12 + s21); have b4 := neg_abs_le (s12 + s21)
  have a5 := le_abs_self (s13 + s31); have b5 := neg_abs_le (s13 + s31)
  have a6 := le_abs_self (s23 + s32); have b6 := neg_abs_le (s23 + s32)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (rcases abs_cases s12 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)
  | (rcases abs_cases s13 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)
  | (rcases abs_cases s21 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)
  | (rcases abs_cases s23 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)
  | (rcases abs_cases s31 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)
  | (rcases abs_cases s32 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)

/-- (CL*) with general constants: `Φ ≥ 0` on `[−1,1]⁶` whenever `t ≥ 3` and `K ≥ t²`. -/
theorem clstar_gen {K t : ℝ} (hK : t ^ 2 ≤ K) (ht : 3 ≤ t) {s12 s13 s21 s23 s31 s32 : ℝ}
    (h12 : |s12| ≤ 1) (h13 : |s13| ≤ 1) (h21 : |s21| ≤ 1) (h23 : |s23| ≤ 1)
    (h31 : |s31| ≤ 1) (h32 : |s32| ≤ 1) :
    0 ≤ Phi K t s12 s13 s21 s23 s31 s32 := by
  obtain ⟨e12, e13, e21, e23, e31, e32⟩ := hexagon s12 s13 s21 s23 s31 s32
  set m := max (max (max |s12| |s13|) (max |s21| |s23|)) (max |s31| |s32|) with hm
  refine core (m := m) hK ht ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [hm, max_le_iff]; exact ⟨⟨⟨h12, h13⟩, ⟨h21, h23⟩⟩, ⟨h31, h32⟩⟩
  all_goals try (simp only [hm, le_max_iff, le_refl, true_or, or_true]; done)
  have : m ≤ ((|s12 - s13| + |s21 - s23| + |s31 - s32|)
                + (|s12 + s21| + |s13 + s31| + |s23 + s32|)) / 2 := by
    simp only [hm, max_le_iff]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> linarith
  linarith

/-- **Target 1.** The weighted inequality `Φ_w ≥ 0` for `0 < w ≤ 1`, `K = 1 + 9/w²`. -/
theorem clstar_weighted {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) {s12 s13 s21 s23 s31 s32 : ℝ}
    (h12 : |s12| ≤ 1) (h13 : |s13| ≤ 1) (h21 : |s21| ≤ 1) (h23 : |s23| ≤ 1)
    (h31 : |s31| ≤ 1) (h32 : |s32| ≤ 1) :
    0 ≤ (√((√(1 - s12^2) + √(1 - s13^2))^2 + (1 + 9 / w^2) * (s12 - s13)^2)
         + √((√(1 - s21^2) + √(1 - s23^2))^2 + (1 + 9 / w^2) * (s21 - s23)^2)
         + √((√(1 - s31^2) + √(1 - s32^2))^2 + (1 + 9 / w^2) * (s31 - s32)^2)) / 2 - 3
        + 3 / (2 * w) * (|s12 + s21| + |s13 + s31| + |s23 + s32|) := by
  have ht : 3 ≤ 3 / w := by rw [le_div_iff₀ hw0]; linarith
  have hK : (3 / w) ^ 2 ≤ 1 + 9 / w ^ 2 := by rw [div_pow]; norm_num
  have := clstar_gen hK ht h12 h13 h21 h23 h31 h32
  unfold Phi at this
  have e : 3 / w / 2 = 3 / (2 * w) := by field_simp
  rwa [e] at this

/-- **Target 1, corollary.** (CL*) itself, in the algebraic form (3.5): `w = 1`, `K = 10`. -/
theorem clstar {s12 s13 s21 s23 s31 s32 : ℝ}
    (h12 : |s12| ≤ 1) (h13 : |s13| ≤ 1) (h21 : |s21| ≤ 1) (h23 : |s23| ≤ 1)
    (h31 : |s31| ≤ 1) (h32 : |s32| ≤ 1) :
    0 ≤ (√((√(1 - s12^2) + √(1 - s13^2))^2 + 10 * (s12 - s13)^2)
         + √((√(1 - s21^2) + √(1 - s23^2))^2 + 10 * (s21 - s23)^2)
         + √((√(1 - s31^2) + √(1 - s32^2))^2 + 10 * (s31 - s32)^2)) / 2 - 3
        + 3 / 2 * (|s12 + s21| + |s13 + s31| + |s23 + s32|) :=
  clstar_gen (K := 10) (t := 3) (by norm_num) le_rfl h12 h13 h21 h23 h31 h32

/-- The weighted inequality with the sharper inner constant `K = 9/w²` (any `K ≥ 9/w²` works). -/
theorem clstar_weighted_sharp {w K : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) (hK : 9 / w ^ 2 ≤ K)
    {s12 s13 s21 s23 s31 s32 : ℝ}
    (h12 : |s12| ≤ 1) (h13 : |s13| ≤ 1) (h21 : |s21| ≤ 1) (h23 : |s23| ≤ 1)
    (h31 : |s31| ≤ 1) (h32 : |s32| ≤ 1) :
    0 ≤ Phi K (3 / w) s12 s13 s21 s23 s31 s32 := by
  have ht : 3 ≤ 3 / w := by rw [le_div_iff₀ hw0]; linarith
  exact clstar_gen (by rw [div_pow]; norm_num; simpa using hK) ht h12 h13 h21 h23 h31 h32

/-- **Target 2.** The sharper constant: (CL*) with `K = 9` at `w = 1`
("1 + 8 sin²" in the trigonometric form). The proof above goes through verbatim:
it only needs `K ≥ 9/w²`. -/
theorem clstar_K9 {s12 s13 s21 s23 s31 s32 : ℝ}
    (h12 : |s12| ≤ 1) (h13 : |s13| ≤ 1) (h21 : |s21| ≤ 1) (h23 : |s23| ≤ 1)
    (h31 : |s31| ≤ 1) (h32 : |s32| ≤ 1) :
    0 ≤ (√((√(1 - s12^2) + √(1 - s13^2))^2 + 9 * (s12 - s13)^2)
         + √((√(1 - s21^2) + √(1 - s23^2))^2 + 9 * (s21 - s23)^2)
         + √((√(1 - s31^2) + √(1 - s32^2))^2 + 9 * (s31 - s32)^2)) / 2 - 3
        + 3 / 2 * (|s12 + s21| + |s13 + s31| + |s23 + s32|) :=
  clstar_gen (K := 9) (t := 3) (by norm_num) le_rfl h12 h13 h21 h23 h31 h32

/-- `K = 9` is optimal at `w = 1`: at σ = (1,−1,−1,−1,1,1) (θ = (π/2, π/2, −π/2) on the slice (I)),
`Φ = √K − 3`, which is negative for `0 ≤ K < 9`. -/
theorem clstar_K_sharp {K : ℝ} (hK0 : 0 ≤ K) :
    Phi K 3 1 (-1) (-1) (-1) 1 1 = √K - 3 := by
  unfold Phi
  have h4 : √(K * 4) = 2 * √K := by
    rw [sqrt_mul hK0, show (4:ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]; ring
  norm_num [h4]

theorem clstar_K_lt9_fails {K : ℝ} (hK0 : 0 ≤ K) (hK : K < 9) :
    Phi K 3 1 (-1) (-1) (-1) 1 1 < 0 := by
  rw [clstar_K_sharp hK0]
  have : √K < 3 := by
    rw [show (3:ℝ) = √9 by rw [show (9:ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt hK0 hK
  linarith

end PortsLean.CLStar
