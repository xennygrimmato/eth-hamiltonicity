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

Contents:
* `clstar_gen` (any `t ≥ 3`, `K ≥ t²`), `clstar_weighted` (`K = 1 + 9/w²`, `t = 3/w`), `clstar`
  (w = 1, K = 10), `clstar_weighted_sharp` (`K ≥ 9/w²`), `clstar_K9`, `clstar_K_sharp`,
  `clstar_K_lt9_fails`;
* the three-angle inequality (I): `three_angle_alg` (slice `σ_ji = −σ_ij`, `θ₁ = ψ₁₂`,
  `θ₂ = −ψ₁₃`, `θ₃ = ψ₂₃`), `three_angle` (trigonometric form, any inner constant `c ≥ 8`),
  `three_angle_I` (`c = 9`), `three_angle_corner` (`F = √(1+c)` at (π/2, π/2, −π/2): `c = 8` sharp);
* the K_{2,m} averaging: `k2m_average`, `R_eq`, `k2m_rate`.
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


/-! ## The three-angle inequality (I) -/

/-- **Target 3, algebraic form.** The slice `σ_ji = −σ_ij` of (CL*) with
`σ12 = s1, σ13 = −s2, σ23 = s3` (so `σ21 = −s1, σ31 = s2, σ32 = −s3`, and `E = 0`):
`½ Σ_{i<j} √((c_i + c_j)² + K (s_i + s_j)²) ≥ 3` for every `K ≥ 9`. -/
theorem three_angle_alg {K : ℝ} (hK : 9 ≤ K) {s1 s2 s3 : ℝ}
    (h1 : |s1| ≤ 1) (h2 : |s2| ≤ 1) (h3 : |s3| ≤ 1) :
    3 ≤ (√((√(1 - s1^2) + √(1 - s2^2))^2 + K * (s1 + s2)^2)
         + √((√(1 - s1^2) + √(1 - s3^2))^2 + K * (s1 + s3)^2)
         + √((√(1 - s2^2) + √(1 - s3^2))^2 + K * (s2 + s3)^2)) / 2 := by
  have hn1 : |-s1| ≤ 1 := by rwa [abs_neg]
  have hn2 : |-s2| ≤ 1 := by rwa [abs_neg]
  have hn3 : |-s3| ≤ 1 := by rwa [abs_neg]
  have := clstar_gen (K := K) (t := 3) (by norm_num; exact hK) le_rfl h1 hn2 hn1 h3 h2 hn3
  unfold Phi at this
  have e : (-s1 - s3) ^ 2 = (s1 + s3) ^ 2 := by ring
  simp only [neg_sq, sub_neg_eq_add, e, add_neg_cancel, neg_add_cancel, abs_zero,
    add_zero, mul_zero] at this
  linarith

/-- The trigonometric form of one term: for `cos((a−b)/2) ≥ 0`,
`cos((a−b)/2)·√(1 + c·sin²((a+b)/2)) = ½√((cos a + cos b)² + (1+c)(sin a + sin b)²)`. -/
lemma trig_term {a b c : ℝ} (hC : 0 ≤ cos ((a - b) / 2)) :
    cos ((a - b) / 2) * √(1 + c * sin ((a + b) / 2) ^ 2)
      = √((cos a + cos b) ^ 2 + (1 + c) * (sin a + sin b) ^ 2) / 2 := by
  rw [cos_add_cos, sin_add_sin]
  have hcs := cos_sq' ((a + b) / 2)
  have e : (2 * cos ((a + b) / 2) * cos ((a - b) / 2)) ^ 2
      + (1 + c) * (2 * sin ((a + b) / 2) * cos ((a - b) / 2)) ^ 2
      = (2 * cos ((a - b) / 2)) ^ 2 * (1 + c * sin ((a + b) / 2) ^ 2) := by
    linear_combination (4 * cos ((a - b) / 2) ^ 2) * hcs
  rw [e, sqrt_mul (sq_nonneg _), sqrt_sq (by linarith)]
  ring

/-- `√(1 − sin²θ) = cos θ` on `[−π/2, π/2]`. -/
lemma sqrt_one_sub_sin_sq {θ : ℝ} (h : θ ∈ Set.Icc (-(π / 2)) (π / 2)) :
    √(1 - sin θ ^ 2) = cos θ := by
  rw [← cos_sq', sqrt_sq (cos_nonneg_of_mem_Icc h)]

lemma cos_half_diff_nonneg {a b : ℝ} (ha : a ∈ Set.Icc (-(π / 2)) (π / 2))
    (hb : b ∈ Set.Icc (-(π / 2)) (π / 2)) : 0 ≤ cos ((a - b) / 2) := by
  apply cos_nonneg_of_mem_Icc
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  constructor <;> linarith [pi_pos]

/-- **Target 3, trigonometric form.** The three-angle inequality (I) of note-k23-rate §3.3,
for every inner constant `c ≥ 8` (the note's (I) is `c = 9`; `c = 8` is the sharp member):
`F(θ) = Σ_{i<j} cos((θ_i−θ_j)/2)·√(1 + c·sin²((θ_i+θ_j)/2)) ≥ 3` on `[−π/2, π/2]³`.
It is `three_angle_alg` with `s_i = sin θ_i`, `K = 1 + c`. -/
theorem three_angle {c : ℝ} (hc : 8 ≤ c) {θ1 θ2 θ3 : ℝ}
    (h1 : θ1 ∈ Set.Icc (-(π / 2)) (π / 2)) (h2 : θ2 ∈ Set.Icc (-(π / 2)) (π / 2))
    (h3 : θ3 ∈ Set.Icc (-(π / 2)) (π / 2)) :
    3 ≤ cos ((θ1 - θ2) / 2) * √(1 + c * sin ((θ1 + θ2) / 2) ^ 2)
      + cos ((θ1 - θ3) / 2) * √(1 + c * sin ((θ1 + θ3) / 2) ^ 2)
      + cos ((θ2 - θ3) / 2) * √(1 + c * sin ((θ2 + θ3) / 2) ^ 2) := by
  rw [trig_term (cos_half_diff_nonneg h1 h2), trig_term (cos_half_diff_nonneg h1 h3),
    trig_term (cos_half_diff_nonneg h2 h3)]
  have := three_angle_alg (K := 1 + c) (by linarith) (abs_sin_le_one θ1) (abs_sin_le_one θ2)
    (abs_sin_le_one θ3)
  rw [sqrt_one_sub_sin_sq h1, sqrt_one_sub_sin_sq h2, sqrt_one_sub_sin_sq h3] at this
  linarith

/-- The note's (I) exactly (`c = 9`). -/
theorem three_angle_I {θ1 θ2 θ3 : ℝ}
    (h1 : θ1 ∈ Set.Icc (-(π / 2)) (π / 2)) (h2 : θ2 ∈ Set.Icc (-(π / 2)) (π / 2))
    (h3 : θ3 ∈ Set.Icc (-(π / 2)) (π / 2)) :
    3 ≤ cos ((θ1 - θ2) / 2) * √(1 + 9 * sin ((θ1 + θ2) / 2) ^ 2)
      + cos ((θ1 - θ3) / 2) * √(1 + 9 * sin ((θ1 + θ3) / 2) ^ 2)
      + cos ((θ2 - θ3) / 2) * √(1 + 9 * sin ((θ2 + θ3) / 2) ^ 2) :=
  three_angle (by norm_num) h1 h2 h3

/-- `c = 8` is optimal in (I): at θ = (π/2, π/2, −π/2), `F = √(1 + c)`. -/
theorem three_angle_corner (c : ℝ) :
    cos ((π/2 - π/2) / 2) * √(1 + c * sin ((π/2 + π/2) / 2) ^ 2)
      + cos ((π/2 - -(π/2)) / 2) * √(1 + c * sin ((π/2 + -(π/2)) / 2) ^ 2)
      + cos ((π/2 - -(π/2)) / 2) * √(1 + c * sin ((π/2 + -(π/2)) / 2) ^ 2) = √(1 + c) := by
  simp

/-! ## The K_{2,m} averaging arithmetic -/

section Averaging
open Finset

variable {m : ℕ}

/-- Indicator of pairwise distinct ordered triples. -/
noncomputable def dist3 (i j k : Fin m) : ℝ := if i ≠ j ∧ j ≠ k ∧ i ≠ k then 1 else 0

lemma count_k (i j : Fin m) : ∑ k, dist3 i j k = if i ≠ j then (m : ℝ) - 2 else 0 := by
  by_cases h : i = j
  · subst h; simp [dist3]
  · have e : ∀ k, dist3 i j k = 1 - (if i = k then 1 else 0) - (if j = k then 1 else 0) := by
      intro k; unfold dist3
      by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp_all
    simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ne_eq, h, not_false_eq_true]
    ring

lemma count_i (j k : Fin m) : ∑ i, dist3 i j k = if j ≠ k then (m : ℝ) - 2 else 0 := by
  rw [← count_k j k]
  refine sum_congr rfl fun i _ => ?_
  unfold dist3
  by_cases h1 : i = j <;> by_cases h2 : j = k <;> by_cases h3 : i = k <;> simp_all [eq_comm]

lemma count_j (i k : Fin m) : ∑ j, dist3 i j k = if i ≠ k then (m : ℝ) - 2 else 0 := by
  rw [← count_k i k]
  refine sum_congr rfl fun j _ => ?_
  unfold dist3
  by_cases h1 : i = j <;> by_cases h2 : j = k <;> by_cases h3 : i = k <;> simp_all [eq_comm]

/-- Sum over ordered pairs of distinct indices. -/
noncomputable def Q (f : Fin m → Fin m → ℝ) : ℝ := ∑ i, ∑ j, if i ≠ j then f i j else 0

lemma pat_ij (f : Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ k, dist3 i j k * f i j = ((m : ℝ) - 2) * Q f := by
  unfold Q; rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
  rw [← sum_mul, count_k]; split_ifs <;> ring

lemma pat_jk (f : Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ k, dist3 i j k * f j k = ((m : ℝ) - 2) * Q f := by
  unfold Q; rw [sum_comm, mul_sum]; refine sum_congr rfl fun j _ => ?_
  rw [sum_comm, mul_sum]; refine sum_congr rfl fun k _ => ?_
  rw [← sum_mul, count_i]; split_ifs <;> ring

lemma pat_ik (f : Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ k, dist3 i j k * f i k = ((m : ℝ) - 2) * Q f := by
  unfold Q; rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
  rw [sum_comm, mul_sum]; refine sum_congr rfl fun k _ => ?_
  rw [← sum_mul, count_j]; split_ifs <;> ring

lemma Q_smul (c : ℝ) (f : Fin m → Fin m → ℝ) : Q (fun i j => c * f i j) = c * Q f := by
  unfold Q; simp only [mul_sum, mul_ite, mul_zero]

lemma sum_ne_one (i : Fin m) : ∑ j : Fin m, (if i ≠ j then (1 : ℝ) else 0) = (m : ℝ) - 1 := by
  have e : ∀ j : Fin m, (if i ≠ j then (1 : ℝ) else 0) = 1 - (if i = j then 1 else 0) := by
    intro j; by_cases h : i = j <;> simp [h]
  simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma Q_left (S : Fin m → ℝ) : Q (fun i _ => S i) = ((m : ℝ) - 1) * ∑ i, S i := by
  unfold Q; rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
  rw [← sum_ne_one i, sum_mul]; refine sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

lemma Q_right (S : Fin m → ℝ) : Q (fun _ j => S j) = ((m : ℝ) - 1) * ∑ i, S i := by
  have : Q (fun _ j => S j) = Q (fun i _ => S i) := by
    unfold Q; rw [sum_comm]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp [ne_comm]
  rw [this, Q_left]

lemma Q_const (D : ℝ) : Q (fun (_ : Fin m) (_ : Fin m) => D) = (m : ℝ) * ((m : ℝ) - 1) * D := by
  rw [Q_left (fun _ => D)]; simp; ring

lemma Q_symm (T : Fin m → Fin m → ℝ) (hT : ∀ i j, T i j = T j i) :
    Q T = 2 * ∑ i, ∑ j, if i < j then T i j else 0 := by
  unfold Q
  have e : ∀ i j : Fin m, (if i ≠ j then T i j else 0)
      = (if i < j then T i j else 0) + (if j < i then T j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h, hT i j]
  simp only [e, sum_add_distrib]
  rw [sum_comm (f := fun i j => if j < i then T j i else 0)]
  ring

/-- **Target 4, the summation.** From the five-point inequality for every ordered triple of
distinct pages, `Σ_i S_i ≥ (2κ/(m−1))·(Σ_{i<j} T_ij + w′·m(m−1)/6·D)`.
(No sign conditions on `T`, `D`, `κ`, `w′` are needed for this step.) -/
theorem k2m_average (hm : 3 ≤ m) (S : Fin m → ℝ) (T : Fin m → Fin m → ℝ)
    (hT : ∀ i j, T i j = T j i) (κ w' D : ℝ)
    (h : ∀ i j k : Fin m, i ≠ j → j ≠ k → i ≠ k →
      κ * (T i j + T j k + T i k + w' * D) ≤ S i + S j + S k) :
    2 * κ / ((m : ℝ) - 1) * ((∑ i, ∑ j, if i < j then T i j else 0)
        + w' * (m * ((m : ℝ) - 1) / 6) * D) ≤ ∑ i, S i := by
  set P := ∑ i, ∑ j, if i < j then T i j else 0 with hP
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  -- sum the hypothesis over ordered distinct triples
  have hsum : 0 ≤ ∑ i, ∑ j, ∑ k, dist3 i j k *
      (S i + S j + S k - κ * T i j - κ * T j k - κ * T i k - κ * w' * D) := by
    refine sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => ?_
    unfold dist3
    split_ifs with hd
    · obtain ⟨h1, h2, h3⟩ := hd; have := h i j k h1 h2 h3; nlinarith
    · simp
  simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib] at hsum
  have a1 := pat_ij (fun i _ => S i)
  have a2 := pat_ij (fun _ j => S j)
  have a3 := pat_ik (fun _ k => S k)
  have a4 := pat_ij (fun i j => κ * T i j)
  have a5 := pat_jk (fun j k => κ * T j k)
  have a6 := pat_ik (fun i k => κ * T i k)
  have a7 := pat_ij (fun (_ : Fin m) (_ : Fin m) => κ * w' * D)
  rw [a1, a2, a3, a4, a5, a6, a7, Q_left, Q_right, Q_smul, Q_const, Q_symm T hT, ← hP] at hsum
  have hm2 : (0 : ℝ) < (m : ℝ) - 2 := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have key : 0 ≤ 3 * ((m : ℝ) - 1) * ∑ i, S i - 6 * κ * P - κ * w' * D * (m * ((m : ℝ) - 1)) := by
    have : 0 ≤ ((m : ℝ) - 2) *
        (3 * ((m : ℝ) - 1) * ∑ i, S i - 6 * κ * P - κ * w' * D * (m * ((m : ℝ) - 1))) := by
      linarith
    exact (mul_nonneg_iff_of_pos_left hm2).mp this
  rw [div_mul_eq_mul_div, div_le_iff₀ hm1]
  nlinarith

/-- `R = 2m/√(m²(m−1)² + 4w²) = (2/(m−1))·κ(w′)` with `w = w′·m(m−1)/6`, `κ(w′) = 3/√(9+w′²)`. -/
theorem R_eq {m w' : ℝ} (hm : 1 < m) :
    2 * m / √(m ^ 2 * (m - 1) ^ 2 + 4 * (w' * (m * (m - 1) / 6)) ^ 2)
      = 2 / (m - 1) * (3 / √(9 + w' ^ 2)) := by
  have hA : 0 ≤ m * (m - 1) / 3 := by apply div_nonneg _ (by norm_num); nlinarith
  have e : m ^ 2 * (m - 1) ^ 2 + 4 * (w' * (m * (m - 1) / 6)) ^ 2
      = (m * (m - 1) / 3) ^ 2 * (9 + w' ^ 2) := by ring
  have hs : 0 < √(9 + w' ^ 2) := sqrt_pos.mpr (by positivity)
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  rw [e, sqrt_mul (sq_nonneg _), sqrt_sq hA]
  field_simp

/-- **Target 4.** The K_{2,m} rate: from the weighted five-point inequality with
`κ(w′) = 3/√(9+w′²)` on every triple of pages,
`Σ_i S_i ≥ R·(Σ_{i<j} T_ij + w·D)` with `w = w′·m(m−1)/6`, `R = 2m/√(m²(m−1)² + 4w²)`. -/
theorem k2m_rate (hm : 3 ≤ m) (S : Fin m → ℝ) (T : Fin m → Fin m → ℝ)
    (hT : ∀ i j, T i j = T j i) (w' D : ℝ)
    (h : ∀ i j k : Fin m, i ≠ j → j ≠ k → i ≠ k →
      3 / √(9 + w' ^ 2) * (T i j + T j k + T i k + w' * D) ≤ S i + S j + S k) :
    let w := w' * (m * ((m : ℝ) - 1) / 6)
    2 * m / √((m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 + 4 * w ^ 2)
      * ((∑ i, ∑ j, if i < j then T i j else 0) + w * D) ≤ ∑ i, S i := by
  intro w
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (1 : ℝ) < m := by linarith
  have := k2m_average hm S T hT _ w' D h
  rw [R_eq hm']
  have e : w * D = w' * (m * ((m : ℝ) - 1) / 6) * D := rfl
  rw [e]
  convert this using 1
  ring

end Averaging

end PortsLean.CLStar
