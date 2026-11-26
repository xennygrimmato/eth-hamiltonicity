import Mathlib

/-!
# The five-point theorem, part 2: hubs and the first-order condition

Source: `research/ports/note-k23-rate.md` §3.2 ("Hubs and exit vectors", condition (3.2)).

For two pages `(ρ_i, a_i)`, `(ρ_j, a_j)` with `ρ ≥ 0`, and `D ≥ 0`, put
`f(y) = √(ρ² + (a − y)²)` (distance from `v = (ρ, a)` to the spine point `(0, y)`).
`hub_exists` produces a hub `y ∈ [0, D]` and exit sines `σ_i, σ_j ∈ [−1,1]` with
* `f_i(y) = ρ_i √(1−σ_i²) + (a_i − y) σ_i` (and the same for `j`), and
* `(D/2)·|σ_i + σ_j| ≤ (y − D/2)·(σ_i + σ_j)`, which is (3.2) in one line.

The hub is a minimiser of `f_i + f_j` on `[0,D]` (compactness). If both `f_i(y), f_j(y) > 0`,
then `σ = (a − y)/f(y)` and the one-sided optimality conditions are proved with no derivatives,
from the quadratic upper bound `f(y+h) ≤ f(y) − σh + h²/(2f(y))`. If `f_i(y) = 0` (the point
`v_i` lies on the spine at the hub), take `σ_i = −σ_j` (or both `0`). Then the condition holds
trivially and the identity for `f_i` reads `0 = 0`. So in that case minimality is not needed at all.
-/

namespace PortsLean.FivePoint

open Real Set

/-- Quadratic upper bound for `y ↦ √(ρ² + (u − y)²)` at `y = 0`, where `F = √(ρ² + u²) > 0`. -/
lemma sqrt_upper {ρ u F h : ℝ} (hF : 0 < F) (hF2 : F ^ 2 = ρ ^ 2 + u ^ 2) :
    √(ρ ^ 2 + (u - h) ^ 2) ≤ F - u / F * h + h ^ 2 / (2 * F) := by
  have hY : F - u / F * h + h ^ 2 / (2 * F) = (F ^ 2 + ρ ^ 2 + (u - h) ^ 2) / (2 * F) := by
    field_simp; linear_combination hF2
  rw [sqrt_le_left (by rw [hY]; positivity)]
  have hsq : (F - u / F * h + h ^ 2 / (2 * F)) ^ 2 - (ρ ^ 2 + (u - h) ^ 2)
      = (u / F * h - h ^ 2 / (2 * F)) ^ 2 := by
    field_simp; linear_combination (4 * F ^ 2) * hF2
  nlinarith [sq_nonneg (u / F * h - h ^ 2 / (2 * F))]

/-- Exit sine of a point off the spine: `f = ρ c + u σ` with `σ = u/f`, `c = √(1−σ²) = ρ/f`. -/
lemma exit_of_pos {ρ u : ℝ} (hρ : 0 ≤ ρ) (hF : 0 < √(ρ ^ 2 + u ^ 2)) :
    |u / √(ρ ^ 2 + u ^ 2)| ≤ 1 ∧
      √(ρ ^ 2 + u ^ 2) = ρ * √(1 - (u / √(ρ ^ 2 + u ^ 2)) ^ 2) + u * (u / √(ρ ^ 2 + u ^ 2)) := by
  set F := √(ρ ^ 2 + u ^ 2) with hFd
  have hF2 : F ^ 2 = ρ ^ 2 + u ^ 2 := sq_sqrt (by positivity)
  constructor
  · rw [abs_div, abs_of_pos hF, div_le_one hF]
    exact abs_le_sqrt (by nlinarith [sq_nonneg ρ])
  · have hc : √(1 - (u / F) ^ 2) = ρ / F := by
      rw [show 1 - (u / F) ^ 2 = (ρ / F) ^ 2 by field_simp; linarith]
      exact sqrt_sq (div_nonneg hρ hF.le)
    rw [hc]; field_simp; linarith

/-- **Hubs exist.** A hub `y ∈ [0,D]` of the pair `{i,j}` with exit sines satisfying the exit
identities and the first-order condition (3.2). -/
lemma hub_exists {ρi ai ρj aj D : ℝ} (hρi : 0 ≤ ρi) (hρj : 0 ≤ ρj) (hD : 0 ≤ D) :
    ∃ y si sj, 0 ≤ y ∧ y ≤ D ∧ |si| ≤ 1 ∧ |sj| ≤ 1 ∧
      √(ρi ^ 2 + (ai - y) ^ 2) = ρi * √(1 - si ^ 2) + (ai - y) * si ∧
      √(ρj ^ 2 + (aj - y) ^ 2) = ρj * √(1 - sj ^ 2) + (aj - y) * sj ∧
      D / 2 * |si + sj| ≤ (y - D / 2) * (si + sj) := by
  set g : ℝ → ℝ := fun y => √(ρi ^ 2 + (ai - y) ^ 2) + √(ρj ^ 2 + (aj - y) ^ 2) with hg
  have gc : ContinuousOn g (Icc 0 D) := by
    apply Continuous.continuousOn; rw [hg]; fun_prop
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hD) gc
  have hy0 := hy.1; have hyD := hy.2
  -- spine case: `f(y) = 0` forces `ρ = 0`, `a = y`
  have spine : ∀ {ρ a : ℝ}, √(ρ ^ 2 + (a - y) ^ 2) = 0 → ∀ s, |s| ≤ 1 →
      √(ρ ^ 2 + (a - y) ^ 2) = ρ * √(1 - s ^ 2) + (a - y) * s := by
    intro ρ a h0 s _
    have h1 : ρ ^ 2 + (a - y) ^ 2 ≤ 0 := sqrt_eq_zero'.1 h0
    have hr : ρ = 0 := by nlinarith [sq_nonneg ρ, sq_nonneg (a - y)]
    have ha : a - y = 0 := by nlinarith [sq_nonneg ρ, sq_nonneg (a - y)]
    rw [h0, hr, ha]; ring
  rcases (sqrt_nonneg (ρi ^ 2 + (ai - y) ^ 2)).lt_or_eq with hFi | hFi
  · rcases (sqrt_nonneg (ρj ^ 2 + (aj - y) ^ 2)).lt_or_eq with hFj | hFj
    · -- generic case: both pages off the spine at the hub
      obtain ⟨bi, ei⟩ := exit_of_pos hρi hFi
      obtain ⟨bj, ej⟩ := exit_of_pos hρj hFj
      set Fi := √(ρi ^ 2 + (ai - y) ^ 2) with hFid
      set Fj := √(ρj ^ 2 + (aj - y) ^ 2) with hFjd
      set si := (ai - y) / Fi
      set sj := (aj - y) / Fj
      refine ⟨y, si, sj, hy0, hyD, bi, bj, ei, ej, ?_⟩
      have hFi2 : Fi ^ 2 = ρi ^ 2 + (ai - y) ^ 2 := sq_sqrt (by positivity)
      have hFj2 : Fj ^ 2 = ρj ^ 2 + (aj - y) ^ 2 := sq_sqrt (by positivity)
      set C := 1 / (2 * Fi) + 1 / (2 * Fj) with hC
      have hC0 : 0 < C := by positivity
      -- `g(y + h) ≤ g(y) − ε h + C h²`
      have up : ∀ h, g (y + h) ≤ g y - (si + sj) * h + C * h ^ 2 := by
        intro h
        have u1 := sqrt_upper (ρ := ρi) (u := ai - y) (h := h) hFi hFi2
        have u2 := sqrt_upper (ρ := ρj) (u := aj - y) (h := h) hFj hFj2
        simp only [hg]
        rw [show ai - (y + h) = ai - y - h by ring, show aj - (y + h) = aj - y - h by ring]
        have : C * h ^ 2 = h ^ 2 / (2 * Fi) + h ^ 2 / (2 * Fj) := by rw [hC]; ring
        rw [← hFid, ← hFjd]; linarith
      have strict : ∀ h, y + h ∈ Icc 0 D → 0 < (si + sj) * h →
          C * h ^ 2 ≤ (si + sj) * h / 2 → False := by
        intro h hm hpos hq
        have h1 : g y ≤ g (y + h) := hmin hm
        have h2 := up h
        linarith
      -- one-sided conditions
      have right : y < D → si + sj ≤ 0 := by
        intro hlt; by_contra hε; push Not at hε
        set h := min (D - y) ((si + sj) / (2 * C))
        have hh : 0 < h := lt_min (by linarith) (by positivity)
        have hh1 : h ≤ D - y := min_le_left _ _
        have hh2 : h ≤ (si + sj) / (2 * C) := min_le_right _ _
        have hCh : C * h ≤ (si + sj) / 2 := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * C)] at hh2; linarith
        exact strict h ⟨by linarith, by linarith⟩ (mul_pos hε hh)
          (by nlinarith [mul_le_mul_of_nonneg_right hCh hh.le])
      have left : 0 < y → 0 ≤ si + sj := by
        intro hlt; by_contra hε; push Not at hε
        set m := min y (-(si + sj) / (2 * C))
        have hm : 0 < m := lt_min hlt (div_pos (by linarith) (by positivity))
        have hm1 : m ≤ y := min_le_left _ _
        have hm2 : m ≤ -(si + sj) / (2 * C) := min_le_right _ _
        have hCm : C * m ≤ -(si + sj) / 2 := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * C)] at hm2; linarith
        exact strict (-m) ⟨by linarith, by linarith⟩ (by nlinarith)
          (by nlinarith [mul_le_mul_of_nonneg_right hCm hm.le])
      by_cases h0 : 0 < y
      · by_cases h1 : y < D
        · have : si + sj = 0 := le_antisymm (right h1) (left h0)
          rw [this]; simp
        · have hyD' : y = D := le_antisymm hyD (not_lt.1 h1)
          have := left h0
          rw [abs_of_nonneg this, hyD']; linarith
      · have hy' : y = 0 := le_antisymm (not_lt.1 h0) hy0
        by_cases h1 : y < D
        · have := right h1
          rw [abs_of_nonpos this, hy']; nlinarith
        · have : D = 0 := by linarith [not_lt.1 h1]
          rw [this, hy']; simp
    · -- `v_j` on the spine at the hub
      obtain ⟨bi, ei⟩ := exit_of_pos hρi hFi
      refine ⟨y, (ai - y) / √(ρi ^ 2 + (ai - y) ^ 2), -((ai - y) / √(ρi ^ 2 + (ai - y) ^ 2)),
        hy0, hyD, bi, by rwa [abs_neg], ei, spine hFj.symm _ (by rwa [abs_neg]), ?_⟩
      simp
  · -- `v_i` on the spine at the hub
    rcases (sqrt_nonneg (ρj ^ 2 + (aj - y) ^ 2)).lt_or_eq with hFj | hFj
    · obtain ⟨bj, ej⟩ := exit_of_pos hρj hFj
      refine ⟨y, -((aj - y) / √(ρj ^ 2 + (aj - y) ^ 2)), (aj - y) / √(ρj ^ 2 + (aj - y) ^ 2),
        hy0, hyD, by rwa [abs_neg], bj, spine hFi.symm _ (by rwa [abs_neg]), ej, ?_⟩
      simp
    · refine ⟨y, 0, 0, hy0, hyD, by simp, by simp, spine hFi.symm _ (by simp),
        spine hFj.symm _ (by simp), by simp⟩

end PortsLean.FivePoint
