import Mathlib
import PortsLean.CLStar

/-!
# The five-point theorem, part 1: the calibration (Prop. C₃)

Source: `research/ports/note-k23-rate.md` §3.2 (calibration, Prop. C₃ = weighted Prop. 3.2).

Planar data of a book with three pages: page `i` carries the point `v_i = (ρ_i, a_i)`
(distance `ρ_i` from the spine, height `a_i` along it), `u₁ = (0,0)`, `u₂ = (0,D)`, so that
`A_i = √(ρ_i² + a_i²)` and `B_i = √(ρ_i² + (a_i − D)²)`.

Exit data for the pair `{i,j}`: a hub height `y_ij` and two numbers `σ_ij, σ_ji ∈ [−1,1]`
(exit sines; `c = √(1 − σ²)`). The only facts used about them are
* `Z_ij ≤ ρ_i c_ij + (a_i − y_ij) σ_ij + ρ_j c_ji + (a_j − y_ij) σ_ji` (for the true hub data
  this is an equality with `Z_ij = f_i(y_ij) + f_j(y_ij)`, see `Hub.lean`);
* the first-order condition (3.2) in the combined form
  `(D/2)·|σ_ij + σ_ji| ≤ (y_ij − D/2)·(σ_ij + σ_ji)`.

The proof is the note's: Cauchy–Schwarz on each of the six supply distances, with calibrating
vectors chosen so that all `ρ_i`, `a_i` cancel. Instead of angles (`α_i = ν_i + μ_i`, …) the
vectors are written algebraically: with `P = c_ij + c_ik`, `Q = σ_ij + σ_ik`,
`M = (λw/6)·√(P² + K(σ_ij − σ_ik)²)`, `K = 1 + 9/w²`, one takes
`q = (λP/2 + z, λQ/2 − M)` for `B_i` and `p = λ(P,Q) − q` for `A_i`, where `P z = Q M`.
Only `|p|, |q| ≤ 1` is needed (not `= 1`), which also covers the degenerate case `P = 0`.
-/

namespace PortsLean.FivePoint

open Real PortsLean.CLStar

/-- Cauchy–Schwarz against a vector of norm `≤ 1`. -/
lemma cs_le {ρ a p q : ℝ} (h : p ^ 2 + q ^ 2 ≤ 1) : ρ * p + a * q ≤ √(ρ ^ 2 + a ^ 2) := by
  apply le_sqrt_of_sq_le
  nlinarith [sq_nonneg (ρ * q - a * p), mul_nonneg (sub_nonneg.2 h)
    (add_nonneg (sq_nonneg ρ) (sq_nonneg a))]

lemma sq_le_one_of_abs {s : ℝ} (h : |s| ≤ 1) : s ^ 2 ≤ 1 := by
  have := sq_abs s; nlinarith [abs_nonneg s]

lemma sq_sqrt_one_sub {s : ℝ} (h : |s| ≤ 1) : (√(1 - s ^ 2)) ^ 2 = 1 - s ^ 2 :=
  sq_sqrt (by linarith [sq_le_one_of_abs h])

/-- For unit vectors `e₁ = (c₁,s₁)`, `e₂ = (c₂,s₂)`: with `P = c₁+c₂`, `Q = s₁+s₂`, `R = s₁−s₂`,
`R²(P² + Q²) = (4 − P² − Q²) P²` (the sum and the difference of two unit vectors are orthogonal). -/
lemma unit_id {s1 s2 c1 c2 : ℝ} (hc1 : c1 ^ 2 = 1 - s1 ^ 2) (hc2 : c2 ^ 2 = 1 - s2 ^ 2) :
    (s1 - s2) ^ 2 * ((c1 + c2) ^ 2 + (s1 + s2) ^ 2)
      = (4 - (c1 + c2) ^ 2 - (s1 + s2) ^ 2) * (c1 + c2) ^ 2 := by
  linear_combination (s1 ^ 2 - s2 ^ 2 - c1 ^ 2 + c2 ^ 2 + 2 * (c1 + c2) ^ 2) * hc1
    + (-(s1 ^ 2 - s2 ^ 2 - c1 ^ 2 + c2 ^ 2) + 2 * (c1 + c2) ^ 2) * hc2

/-- The perpendicular component `z` of the calibrating vectors exists. -/
lemma exists_perp {w L s1 s2 M : ℝ} (hL : L ^ 2 * (9 + w ^ 2) = 9)
    (h1 : |s1| ≤ 1) (h2 : |s2| ≤ 1)
    (hM : M ^ 2 = L ^ 2 * (w ^ 2 * (√(1 - s1 ^ 2) + √(1 - s2 ^ 2)) ^ 2
      + (w ^ 2 + 9) * (s1 - s2) ^ 2) / 36) :
    ∃ z, (√(1 - s1 ^ 2) + √(1 - s2 ^ 2)) * z = (s1 + s2) * M ∧
      L ^ 2 * ((√(1 - s1 ^ 2) + √(1 - s2 ^ 2)) ^ 2 + (s1 + s2) ^ 2) / 4 + z ^ 2 + M ^ 2 ≤ 1 := by
  have hc1 := sq_sqrt_one_sub h1
  have hc2 := sq_sqrt_one_sub h2
  set c1 := √(1 - s1 ^ 2) with hc1d
  set c2 := √(1 - s2 ^ 2) with hc2d
  have c1n : 0 ≤ c1 := sqrt_nonneg _
  have c2n : 0 ≤ c2 := sqrt_nonneg _
  have hu := unit_id hc1 hc2
  rcases (add_nonneg c1n c2n).lt_or_eq with hP | hP
  · -- generic case `P > 0`
    refine ⟨(s1 + s2) * M / (c1 + c2), by field_simp, ?_⟩
    have key : L ^ 2 * ((c1 + c2) ^ 2 + (s1 + s2) ^ 2) * (c1 + c2) ^ 2 / 4
        + M ^ 2 * ((c1 + c2) ^ 2 + (s1 + s2) ^ 2) = (c1 + c2) ^ 2 := by
      linear_combination ((c1 + c2) ^ 2 + (s1 + s2) ^ 2) * hM
        + L ^ 2 * (w ^ 2 + 9) / 36 * hu + (c1 + c2) ^ 2 / 9 * hL
    have hP2 : 0 < (c1 + c2) ^ 2 := by positivity
    have e : L ^ 2 * ((c1 + c2) ^ 2 + (s1 + s2) ^ 2) / 4 + ((s1 + s2) * M / (c1 + c2)) ^ 2 + M ^ 2
        = (L ^ 2 * ((c1 + c2) ^ 2 + (s1 + s2) ^ 2) * (c1 + c2) ^ 2 / 4
          + M ^ 2 * ((c1 + c2) ^ 2 + (s1 + s2) ^ 2)) / (c1 + c2) ^ 2 := by
      field_simp; ring
    rw [e, key, div_self hP2.ne']
  · -- degenerate case `P = 0`: both exit vectors are vertical
    have e1 : c1 = 0 := by linarith
    have e2 : c2 = 0 := by linarith
    rw [e1] at hc1; rw [e2] at hc2
    have hs1 : s1 ^ 2 = 1 := by linarith
    have hs2 : s2 ^ 2 = 1 := by linarith
    rw [← hP] at hM ⊢
    have hM' : M ^ 2 = (s1 - s2) ^ 2 / 4 := by linear_combination hM + (s1 - s2) ^ 2 / 36 * hL
    have hQR : (s1 + s2) * (s1 - s2) = 0 := by linear_combination hs1 - hs2
    refine ⟨0, ?_, ?_⟩
    · rcases mul_eq_zero.1 hQR with hQ | hR
      · rw [hQ]; ring
      · have : M = 0 := by
          have : M ^ 2 = 0 := by rw [hM', hR]; ring
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        rw [this]; ring
    · rcases mul_eq_zero.1 hQR with hQ | hR
      · rw [hQ]
        have : s2 = -s1 := by linarith
        rw [hM', this]; nlinarith
      · have : s2 = s1 := by linarith
        rw [this] at hM' ⊢
        have hL1 : L ^ 2 ≤ 1 := by nlinarith [sq_nonneg w]
        nlinarith

/-- **Calibration of one page.** For every page `(ρ, a)` and exit sines `s1 = σ_ij`,
`s2 = σ_ik` of its two pairs:
`A + B ≥ λ(ρP + aQ) − (λD/2)Q + D·(λw/6)·√(P² + K(s1−s2)²)`, `K = 1 + 9/w²`,
where `λ² (9 + w²) = 9`. -/
lemma page_calib {w L ρ a D s1 s2 : ℝ} (hw : 0 < w) (hL0 : 0 ≤ L)
    (hL : L ^ 2 * (9 + w ^ 2) = 9) (h1 : |s1| ≤ 1) (h2 : |s2| ≤ 1) :
    L * (ρ * (√(1 - s1 ^ 2) + √(1 - s2 ^ 2)) + a * (s1 + s2)) - L * D / 2 * (s1 + s2)
      + D * (L * w / 6 * √((√(1 - s1 ^ 2) + √(1 - s2 ^ 2)) ^ 2 + (1 + 9 / w ^ 2) * (s1 - s2) ^ 2))
      ≤ √(ρ ^ 2 + a ^ 2) + √(ρ ^ 2 + (a - D) ^ 2) := by
  set P := √(1 - s1 ^ 2) + √(1 - s2 ^ 2) with hPd
  set M := L * w / 6 * √(P ^ 2 + (1 + 9 / w ^ 2) * (s1 - s2) ^ 2) with hMd
  have hK : 0 ≤ P ^ 2 + (1 + 9 / w ^ 2) * (s1 - s2) ^ 2 := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hM : M ^ 2 = L ^ 2 * (w ^ 2 * P ^ 2 + (w ^ 2 + 9) * (s1 - s2) ^ 2) / 36 := by
    rw [hMd, mul_pow, sq_sqrt hK]; field_simp; ring
  obtain ⟨z, hz, hzb⟩ := exists_perp hL h1 h2 hM
  set Q := s1 + s2
  have hp : (L * P / 2 - z) ^ 2 + (L * Q / 2 + M) ^ 2 ≤ 1 := by nlinarith
  have hq : (L * P / 2 + z) ^ 2 + (L * Q / 2 - M) ^ 2 ≤ 1 := by nlinarith
  have hA := cs_le (ρ := ρ) (a := a) hp
  have hB := cs_le (ρ := ρ) (a := a - D) hq
  nlinarith

/-- **Prop. C₃ in Lean (the calibration).** Book with three pages, given exit data.
Conclusion: `Σ_S − λ(Z₁₂ + Z₁₃ + Z₂₃ + wD) ≥ (λw/3)·D·Φ_w(σ)` with `λ = κ(w) = 3/√(9+w²)` and
`Φ_w = Phi (1 + 9/w²) (3/w)` of `CLStar.lean`. No sign condition on `ρ_i`, `a_i`, `D` is needed
for this identity-plus-Cauchy–Schwarz step. -/
theorem book_calibration {w D : ℝ} (hw : 0 < w)
    {ρ1 ρ2 ρ3 a1 a2 a3 s12 s13 s21 s23 s31 s32 y12 y13 y23 Z12 Z13 Z23 : ℝ}
    (h12 : |s12| ≤ 1) (h13 : |s13| ≤ 1) (h21 : |s21| ≤ 1) (h23 : |s23| ≤ 1)
    (h31 : |s31| ≤ 1) (h32 : |s32| ≤ 1)
    (hZ12 : Z12 ≤ ρ1 * √(1 - s12 ^ 2) + (a1 - y12) * s12 + (ρ2 * √(1 - s21 ^ 2) + (a2 - y12) * s21))
    (hZ13 : Z13 ≤ ρ1 * √(1 - s13 ^ 2) + (a1 - y13) * s13 + (ρ3 * √(1 - s31 ^ 2) + (a3 - y13) * s31))
    (hZ23 : Z23 ≤ ρ2 * √(1 - s23 ^ 2) + (a2 - y23) * s23 + (ρ3 * √(1 - s32 ^ 2) + (a3 - y23) * s32))
    (hy12 : D / 2 * |s12 + s21| ≤ (y12 - D / 2) * (s12 + s21))
    (hy13 : D / 2 * |s13 + s31| ≤ (y13 - D / 2) * (s13 + s31))
    (hy23 : D / 2 * |s23 + s32| ≤ (y23 - D / 2) * (s23 + s32)) :
    3 / √(9 + w ^ 2) * (Z12 + Z13 + Z23 + w * D)
      + 3 / √(9 + w ^ 2) * w / 3 * D * Phi (1 + 9 / w ^ 2) (3 / w) s12 s13 s21 s23 s31 s32
      ≤ (√(ρ1 ^ 2 + a1 ^ 2) + √(ρ2 ^ 2 + a2 ^ 2) + √(ρ3 ^ 2 + a3 ^ 2))
        + (√(ρ1 ^ 2 + (a1 - D) ^ 2) + √(ρ2 ^ 2 + (a2 - D) ^ 2) + √(ρ3 ^ 2 + (a3 - D) ^ 2)) := by
  set L := 3 / √(9 + w ^ 2) with hLd
  have hs : 0 < √(9 + w ^ 2) := sqrt_pos.2 (by positivity)
  have hL0 : 0 ≤ L := by positivity
  have hL : L ^ 2 * (9 + w ^ 2) = 9 := by
    rw [hLd, div_pow, sq_sqrt (by positivity)]; field_simp; norm_num
  have p1 := page_calib (ρ := ρ1) (a := a1) (D := D) hw hL0 hL h12 h13
  have p2 := page_calib (ρ := ρ2) (a := a2) (D := D) hw hL0 hL h21 h23
  have p3 := page_calib (ρ := ρ3) (a := a3) (D := D) hw hL0 hL h31 h32
  have z12 := mul_le_mul_of_nonneg_left hZ12 hL0
  have z13 := mul_le_mul_of_nonneg_left hZ13 hL0
  have z23 := mul_le_mul_of_nonneg_left hZ23 hL0
  have e12 := mul_le_mul_of_nonneg_left hy12 hL0
  have e13 := mul_le_mul_of_nonneg_left hy13 hL0
  have e23 := mul_le_mul_of_nonneg_left hy23 hL0
  have hPhi : L * w / 3 * D * Phi (1 + 9 / w ^ 2) (3 / w) s12 s13 s21 s23 s31 s32
      = D * (L * w / 6 * √((√(1 - s12 ^ 2) + √(1 - s13 ^ 2)) ^ 2 + (1 + 9 / w ^ 2) * (s12 - s13) ^ 2))
        + D * (L * w / 6 * √((√(1 - s21 ^ 2) + √(1 - s23 ^ 2)) ^ 2 + (1 + 9 / w ^ 2) * (s21 - s23) ^ 2))
        + D * (L * w / 6 * √((√(1 - s31 ^ 2) + √(1 - s32 ^ 2)) ^ 2 + (1 + 9 / w ^ 2) * (s31 - s32) ^ 2))
        - L * w * D + L * (D / 2 * |s12 + s21|) + L * (D / 2 * |s13 + s31|)
        + L * (D / 2 * |s23 + s32|) := by
    unfold Phi; field_simp; ring
  rw [hPhi]
  linarith

end PortsLean.FivePoint
