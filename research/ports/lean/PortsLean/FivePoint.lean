import Mathlib
import PortsLean.CLStar
import PortsLean.FivePoint.Calibration
import PortsLean.FivePoint.Hub

/-!
# The weighted five-point theorem (Theorem 5_w) from one comparison hypothesis

Source: `research/ports/note-k23-rate.md` §3 (§3.1 reduction to books, §3.2 calibration,
§3.3 Theorem D, proof of Theorem 5_w).

Setting: a pseudometric space `X`, points `u₁ u₂ v₁ v₂ v₃`, `D = dist u₁ u₂`, and a map
`c : ℝ → X` (meant to be the geodesic from `u₁` to `u₂`, parametrised by arc length on `[0, D]`).
The only geometric input is the comparison inequality (CMP) for each `v_i`:
`dist(v_i, c t)² ≤ (1 − t/D)·dist(v_i,u₁)² + (t/D)·dist(v_i,u₂)² − t(D − t)` for `t ∈ [0, D]`.
This is the note's C.4(a) for CAT(0) spaces. Mathlib has no CAT(0) spaces, so (CMP) stays a
hypothesis. `cmp_inner` proves (CMP) in every real inner product space (with `c` the segment),
which shows that the hypothesis can be satisfied.

Contents:
* `triangle_coords`: every triangle with sides `A, B, D > 0` has planar coordinates `(ρ, a)`, `ρ ≥ 0`;
  the comparison distance is `√(ρ² + (a − t)²)`.
* `five_point_weighted` (**Theorem 5_w**): for `0 < w ≤ 1`, (CMP) for `v₁, v₂, v₃` implies
  `3/√(9+w²)·(|v₁v₂| + |v₂v₃| + |v₁v₃| + w·D) ≤ Σ_{k,i} |u_k v_i|`.
* `five_point` (w = 1, κ = 3/√10), `five_point_inner` (inner product spaces),
  `k2m_five_point` (K_{2,m}, combined with `k2m_rate`).
-/

namespace PortsLean.FivePoint

open Real PortsLean.CLStar

/-- The comparison hypothesis (CMP) for the point `v` and the curve `c` from `u₁` to `u₂`. -/
def CMP {X : Type*} [PseudoMetricSpace X] (u1 u2 : X) (c : ℝ → X) (v : X) : Prop :=
  ∀ t, 0 ≤ t → t ≤ dist u1 u2 →
    dist v (c t) ^ 2 ≤ (1 - t / dist u1 u2) * dist v u1 ^ 2 + t / dist u1 u2 * dist v u2 ^ 2
      - t * (dist u1 u2 - t)

/-- Planar coordinates of a triangle with sides `A = |u₁v|`, `B = |u₂v|`, `D = |u₁u₂| > 0`:
`u₁ = (0,0)`, `u₂ = (0,D)`, `v = (ρ, a)` with `ρ ≥ 0`. The Euclidean distance from `v` to `(0,t)`
is the comparison distance (Stewart's theorem). -/
lemma triangle_coords {A B D : ℝ} (hD : 0 < D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : A ≤ B + D) (h2 : B ≤ A + D) (h3 : D ≤ A + B) :
    ∃ ρ a, 0 ≤ ρ ∧ √(ρ ^ 2 + a ^ 2) = A ∧ √(ρ ^ 2 + (a - D) ^ 2) = B ∧
      ∀ t, ρ ^ 2 + (a - t) ^ 2 = (1 - t / D) * A ^ 2 + t / D * B ^ 2 - t * (D - t) := by
  set a := (A ^ 2 - B ^ 2 + D ^ 2) / (2 * D) with ha
  have hpos : 0 ≤ A ^ 2 - a ^ 2 := by
    have key : (A ^ 2 - a ^ 2) * (4 * D ^ 2)
        = (B ^ 2 - (A - D) ^ 2) * ((A + D) ^ 2 - B ^ 2) := by
      rw [ha]; field_simp; ring
    have r : 0 ≤ (B ^ 2 - (A - D) ^ 2) * ((A + D) ^ 2 - B ^ 2) := by
      apply mul_nonneg <;> nlinarith
    have : 0 < 4 * D ^ 2 := by positivity
    nlinarith
  refine ⟨√(A ^ 2 - a ^ 2), a, sqrt_nonneg _, ?_, ?_, ?_⟩
  · rw [sq_sqrt hpos, show A ^ 2 - a ^ 2 + a ^ 2 = A ^ 2 by ring, sqrt_sq hA]
  · have : A ^ 2 - a ^ 2 + (a - D) ^ 2 = B ^ 2 := by rw [ha]; field_simp; ring
    rw [sq_sqrt hpos, this, sqrt_sq hB]
  · intro t; rw [sq_sqrt hpos, ha]; field_simp; ring

/-- From (CMP) and planar coordinates: `dist(v, c t) ≤ √(ρ² + (a − t)²)` on `[0, D]`. -/
lemma dist_le_page {X : Type*} [PseudoMetricSpace X] {u1 u2 v : X} {c : ℝ → X} {ρ a : ℝ}
    (hc : CMP u1 u2 c v)
    (hco : ∀ t, ρ ^ 2 + (a - t) ^ 2 = (1 - t / dist u1 u2) * dist v u1 ^ 2
      + t / dist u1 u2 * dist v u2 ^ 2 - t * (dist u1 u2 - t))
    {t : ℝ} (ht0 : 0 ≤ t) (htD : t ≤ dist u1 u2) :
    dist v (c t) ≤ √(ρ ^ 2 + (a - t) ^ 2) := by
  apply le_sqrt_of_sq_le
  rw [hco]; exact hc t ht0 htD

lemma kappa_le_one {w : ℝ} : 3 / √(9 + w ^ 2) ≤ 1 := by
  have h3 : (3 : ℝ) ≤ √(9 + w ^ 2) := by
    apply le_sqrt_of_sq_le; nlinarith [sq_nonneg w]
  rw [div_le_one (by linarith)]; exact h3

/-- **Theorem 5_w (weighted five-point theorem).** In a pseudometric space, if the comparison
inequality (CMP) holds for `v₁, v₂, v₃` along a curve `c` from `u₁` to `u₂`, then for `0 < w ≤ 1`
`κ(w)·(|v₁v₂| + |v₂v₃| + |v₁v₃| + w·|u₁u₂|) ≤ Σ_{k=1,2} Σ_{i=1..3} |u_k v_i|`, `κ(w) = 3/√(9+w²)`.
The degenerate case `D = 0` needs no hypothesis (CMP is not used there). -/
theorem five_point_weighted {X : Type*} [PseudoMetricSpace X] {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1)
    (u1 u2 v1 v2 v3 : X) (c : ℝ → X)
    (hc1 : CMP u1 u2 c v1) (hc2 : CMP u1 u2 c v2) (hc3 : CMP u1 u2 c v3) :
    3 / √(9 + w ^ 2) * (dist v1 v2 + dist v2 v3 + dist v1 v3 + w * dist u1 u2)
      ≤ dist u1 v1 + dist u1 v2 + dist u1 v3 + (dist u2 v1 + dist u2 v2 + dist u2 v3) := by
  set D := dist u1 u2 with hDd
  have hκ0 : 0 ≤ 3 / √(9 + w ^ 2) := by positivity
  have hκ1 := kappa_le_one (w := w)
  rcases (dist_nonneg : 0 ≤ D).lt_or_eq with hD | hD
  · -- the main case `D > 0`: reduction to a book, hubs, calibration, Theorem D
    obtain ⟨ρ1, a1, hρ1, hA1, hB1, hco1⟩ := triangle_coords (A := dist v1 u1) (B := dist v1 u2)
      hD dist_nonneg dist_nonneg (by linarith [dist_triangle v1 u2 u1, dist_comm u1 u2])
      (by linarith [dist_triangle v1 u1 u2]) (by linarith [dist_triangle u1 v1 u2, dist_comm u1 v1])
    obtain ⟨ρ2, a2, hρ2, hA2, hB2, hco2⟩ := triangle_coords (A := dist v2 u1) (B := dist v2 u2)
      hD dist_nonneg dist_nonneg (by linarith [dist_triangle v2 u2 u1, dist_comm u1 u2])
      (by linarith [dist_triangle v2 u1 u2]) (by linarith [dist_triangle u1 v2 u2, dist_comm u1 v2])
    obtain ⟨ρ3, a3, hρ3, hA3, hB3, hco3⟩ := triangle_coords (A := dist v3 u1) (B := dist v3 u2)
      hD dist_nonneg dist_nonneg (by linarith [dist_triangle v3 u2 u1, dist_comm u1 u2])
      (by linarith [dist_triangle v3 u1 u2]) (by linarith [dist_triangle u1 v3 u2, dist_comm u1 v3])
    obtain ⟨y12, s12, s21, y12a, y12b, b12, b21, e12, e21, k12⟩ :=
      hub_exists (ρi := ρ1) (ai := a1) (ρj := ρ2) (aj := a2) hρ1 hρ2 hD.le
    obtain ⟨y13, s13, s31, y13a, y13b, b13, b31, e13, e31, k13⟩ :=
      hub_exists (ρi := ρ1) (ai := a1) (ρj := ρ3) (aj := a3) hρ1 hρ3 hD.le
    obtain ⟨y23, s23, s32, y23a, y23b, b23, b32, e23, e32, k23⟩ :=
      hub_exists (ρi := ρ2) (ai := a2) (ρj := ρ3) (aj := a3) hρ2 hρ3 hD.le
    -- (3.1): |v_i v_j| ≤ f_i(y_ij) + f_j(y_ij)
    have Z : ∀ {vi vj : X} {ρi ai ρj aj y : ℝ}, CMP u1 u2 c vi → CMP u1 u2 c vj →
        (∀ t, ρi ^ 2 + (ai - t) ^ 2 = (1 - t / D) * dist vi u1 ^ 2 + t / D * dist vi u2 ^ 2
          - t * (D - t)) →
        (∀ t, ρj ^ 2 + (aj - t) ^ 2 = (1 - t / D) * dist vj u1 ^ 2 + t / D * dist vj u2 ^ 2
          - t * (D - t)) → 0 ≤ y → y ≤ D →
        dist vi vj ≤ √(ρi ^ 2 + (ai - y) ^ 2) + √(ρj ^ 2 + (aj - y) ^ 2) := by
      intro vi vj ρi ai ρj aj y hi hj hcoi hcoj hy0 hyD
      have := dist_triangle vi (c y) vj
      have h1 := dist_le_page hi hcoi hy0 hyD
      have h2 := dist_le_page hj hcoj hy0 hyD
      rw [dist_comm (c y) vj] at this
      linarith
    have Z12 := Z hc1 hc2 hco1 hco2 y12a y12b
    have Z13 := Z hc1 hc3 hco1 hco3 y13a y13b
    have Z23 := Z hc2 hc3 hco2 hco3 y23a y23b
    rw [e12, e21] at Z12; rw [e13, e31] at Z13; rw [e23, e32] at Z23
    have cal := book_calibration hw0 b12 b13 b21 b23 b31 b32 Z12 Z13 Z23 k12 k13 k23
    -- Theorem D: Φ_w ≥ 0
    have ht : 3 ≤ 3 / w := by rw [le_div_iff₀ hw0]; linarith
    have hK : (3 / w) ^ 2 ≤ 1 + 9 / w ^ 2 := by rw [div_pow]; norm_num
    have hPhi := clstar_gen hK ht b12 b13 b21 b23 b31 b32
    have hrest : 0 ≤ 3 / √(9 + w ^ 2) * w / 3 * D * Phi (1 + 9 / w ^ 2) (3 / w) s12 s13 s21 s23 s31 s32 := by
      have : 0 ≤ 3 / √(9 + w ^ 2) * w / 3 * D := by positivity
      exact mul_nonneg this hPhi
    rw [hA1, hA2, hA3, hB1, hB2, hB3] at cal
    simp only [dist_comm u1, dist_comm u2]
    linarith
  · -- `D = 0`: `B_i = A_i` and `|v_i v_j| ≤ A_i + A_j`
    have eq : ∀ v : X, dist u2 v = dist u1 v := by
      intro v
      have := dist_triangle u2 u1 v; have := dist_triangle u1 u2 v
      rw [dist_comm u2 u1] at *; apply le_antisymm <;> linarith
    have hD' : D = 0 := hD.symm
    rw [eq, eq, eq, hD']
    have t12 := dist_triangle v1 u1 v2
    have t23 := dist_triangle v2 u1 v3
    have t13 := dist_triangle v1 u1 v3
    rw [dist_comm v1 u1] at t12 t13; rw [dist_comm v2 u1] at t23
    have hs : 0 ≤ dist v1 v2 + dist v2 v3 + dist v1 v3 := by positivity
    nlinarith

/-- **Theorem 5 (w = 1).** `(3/√10)·(|v₁v₂| + |v₂v₃| + |v₁v₃| + |u₁u₂|) ≤ Σ_{k,i} |u_k v_i|`. -/
theorem five_point {X : Type*} [PseudoMetricSpace X] (u1 u2 v1 v2 v3 : X) (c : ℝ → X)
    (hc1 : CMP u1 u2 c v1) (hc2 : CMP u1 u2 c v2) (hc3 : CMP u1 u2 c v3) :
    3 / √10 * (dist v1 v2 + dist v2 v3 + dist v1 v3 + dist u1 u2)
      ≤ dist u1 v1 + dist u1 v2 + dist u1 v3 + (dist u2 v1 + dist u2 v2 + dist u2 v3) := by
  have := five_point_weighted (w := 1) one_pos le_rfl u1 u2 v1 v2 v3 c hc1 hc2 hc3
  norm_num at this ⊢; linarith

/-- The interpolation identity of an inner product space:
`‖x − s y‖² = (1−s)‖x‖² + s‖x − y‖² − s(1−s)‖y‖²`. -/
lemma interp_id {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) (s : ℝ) :
    ‖x - s • y‖ ^ 2 = (1 - s) * ‖x‖ ^ 2 + s * ‖x - y‖ ^ 2 - s * (1 - s) * ‖y‖ ^ 2 := by
  rw [norm_sub_sq_real x (s • y), norm_sub_sq_real x y, norm_smul, inner_smul_right,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- (CMP) holds in every real inner product space, with `c` the straight segment
(arc-length parametrisation). So the hypothesis of Theorem 5_w can be satisfied. -/
theorem cmp_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u1 u2 v : E) :
    CMP u1 u2 (fun t => u1 + (t / dist u1 u2) • (u2 - u1)) v := by
  intro t ht0 htD
  set D := dist u1 u2 with hDd
  rcases (dist_nonneg : 0 ≤ D).lt_or_eq with hD | hD
  · set s := t / D with hs
    have hy : ‖u2 - u1‖ = D := by rw [hDd, dist_eq_norm, norm_sub_rev]
    have key : ‖v - (u1 + s • (u2 - u1))‖ ^ 2 = (1 - s) * ‖v - u1‖ ^ 2 + s * ‖v - u2‖ ^ 2
        - s * (1 - s) * ‖u2 - u1‖ ^ 2 := by
      have e1 : v - (u1 + s • (u2 - u1)) = (v - u1) - s • (u2 - u1) := by abel
      have e2 : v - u2 = (v - u1) - (u2 - u1) := by abel
      rw [e1, e2]
      exact interp_id _ _ _
    simp only [dist_eq_norm]
    rw [key, hy]
    have : s * (1 - s) * D ^ 2 = t * (D - t) := by
      have hD0 : D ≠ 0 := hD.ne'
      rw [hs]; field_simp
    rw [this]
  · have ht : t = 0 := le_antisymm (by linarith) ht0
    subst ht; simp

/-- **Theorem 5_w in a Euclidean (inner product) space**, as a sanity check of non-vacuity. -/
theorem five_point_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) (u1 u2 v1 v2 v3 : E) :
    3 / √(9 + w ^ 2) * (dist v1 v2 + dist v2 v3 + dist v1 v3 + w * dist u1 u2)
      ≤ dist u1 v1 + dist u1 v2 + dist u1 v3 + (dist u2 v1 + dist u2 v2 + dist u2 v3) :=
  five_point_weighted hw0 hw1 u1 u2 v1 v2 v3 _ (cmp_inner u1 u2 v1) (cmp_inner u1 u2 v2)
    (cmp_inner u1 u2 v3)

/-- **K_{2,m} corollary.** If (CMP) holds for all `v_i` (`m ≥ 3`) and `0 < w′ ≤ 1`, then with
`w = w′·m(m−1)/6`: `2m/√(m²(m−1)² + 4w²)·(Σ_{i<j} |v_iv_j| + w·D) ≤ Σ_i (|u₁v_i| + |u₂v_i|)`. -/
theorem k2m_five_point {m : ℕ} (hm : 3 ≤ m) {X : Type*} [PseudoMetricSpace X] {w' : ℝ}
    (hw0 : 0 < w') (hw1 : w' ≤ 1) (u1 u2 : X) (v : Fin m → X) (c : ℝ → X)
    (hc : ∀ i, CMP u1 u2 c (v i)) :
    let w := w' * (m * ((m : ℝ) - 1) / 6)
    2 * m / √((m : ℝ) ^ 2 * ((m : ℝ) - 1) ^ 2 + 4 * w ^ 2)
      * ((∑ i, ∑ j, if i < j then dist (v i) (v j) else 0) + w * dist u1 u2)
      ≤ ∑ i, (dist u1 (v i) + dist u2 (v i)) := by
  apply k2m_rate hm (fun i => dist u1 (v i) + dist u2 (v i)) (fun i j => dist (v i) (v j))
    (fun i j => dist_comm _ _) w' (dist u1 u2)
  intro i j k _ _ _
  have := five_point_weighted hw0 hw1 u1 u2 (v i) (v j) (v k) c (hc i) (hc j) (hc k)
  linarith

end PortsLean.FivePoint
