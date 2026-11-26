import Mathlib

/-!
# Theorem A, the arithmetic for large h

Graph: the Cayley graph of U_h(F₂) with the h−1 generators x_j = 1 + E_{j,j+1},
order n = 2^{h(h−1)/2}, so in OpenAI's `exists_logarithmic_placement`
(`OAI/Computability/MultitapeWeakETH/Cloud.lean`, line 83) we take

* `s = h(h−1)/2` (order `2^s`),
* `e = Nat.log 2 (h−1) + 1`, the least... (any `e` with `h−1 < 2^e ≤ 2(h−1)`; this one works),
  degree `h−1` is padded with `2^e − (h−1) ≥ 1` loops to degree `2^e`.

F.6 (Anthropic `thm_poincare`, `Paper/Groups.lean` line 1085) gives, after the translation in
`ThmA.lean`, the Poincaré bound `C₀ · 2^e` in OpenAI's normalisation
(`HasPoincareBound`, `OAI/Computability/VPVNP/WalkEnergy.lean` line 195).

The two conditions that must hold for one admissible `h = l·u` (`l ≥ 2`) are

* `large`  : `10000 * (e+3) ≤ s`                (Cloud.lean line 83, hypothesis `large`)
* `beats`  : `C₀ * 2^e ≤ s / (10000 * (e+3))`  (so that F.6 beats the threshold; also gives `scalar`)

Both follow from `40000 * (C₀ + 1) * (e + 3) ≤ h`, which holds for all large `h`
because `e + 3 ≤ log₂ h + 4`.
-/

namespace PortsLean.ThmA

open Filter Real

/-- The exponent of the degree after padding. -/
def degExp (h : ℕ) : ℕ := Nat.log 2 (h - 1) + 1

/-- log₂ of the order of U_h(F₂). -/
def ordExp (h : ℕ) : ℕ := h * (h - 1) / 2

lemma degExp_lt (h : ℕ) : h - 1 < 2 ^ degExp h := by
  simpa [degExp] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (h - 1)

lemma degExp_le (h : ℕ) (hh : 2 ≤ h) : 2 ^ degExp h ≤ 2 * (h - 1) := by
  have := Nat.pow_log_le_self 2 (show h - 1 ≠ 0 by omega)
  simp only [degExp, pow_succ]; omega

lemma two_mul_ordExp (h : ℕ) : 2 * ordExp h = h * (h - 1) := by
  unfold ordExp
  have : Even (h * (h - 1)) := by
    rcases Nat.even_or_odd h with he | ho
    · exact he.mul_right _
    · exact (Nat.Odd.sub_odd ho odd_one).mul_left _
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp this)

lemma degExp_le_logb (h : ℕ) (hh : 2 ≤ h) : (degExp h : ℝ) ≤ Real.logb 2 h + 1 := by
  have h1 : (Nat.log 2 (h - 1) : ℝ) ≤ Real.logb 2 ((h - 1 : ℕ) : ℝ) := Real.natLog_le_logb _ _
  have h2 : Real.logb 2 ((h - 1 : ℕ) : ℝ) ≤ Real.logb 2 h := by
    apply Real.logb_le_logb_of_le (by norm_num)
    · have : (1 : ℝ) ≤ ((h - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ h - 1)
      linarith
    · exact_mod_cast Nat.sub_le h 1
  simp only [degExp, Nat.cast_add, Nat.cast_one]; linarith

/-- Real-analysis core: `A (log₂ x + 4) ≤ x` for all large `x`. -/
lemma eventually_logb_le (A : ℝ) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, A * (Real.logb 2 x + 4) ≤ x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho := Real.isLittleO_log_id_atTop.def (c := Real.log 2 / (2 * A)) (by positivity)
  filter_upwards [ho, eventually_ge_atTop (8 * A), eventually_ge_atTop (1 : ℝ)] with x hx h8 h1
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg h1
  rw [Real.norm_of_nonneg hlog0, id, Real.norm_of_nonneg hx0] at hx
  have : A * Real.logb 2 x ≤ x / 2 := by
    rw [Real.logb, mul_div_assoc', div_le_iff₀ hl2]
    calc A * Real.log x ≤ A * (Real.log 2 / (2 * A) * x) := by gcongr
      _ = x / 2 * Real.log 2 := by field_simp
  nlinarith

/-- The single sufficient condition, for every large natural `h`. -/
lemma eventually_main (C₀ : ℝ) (hC : 0 ≤ C₀) :
    ∀ᶠ h : ℕ in atTop, 2 ≤ h ∧ 40000 * (C₀ + 1) * ((degExp h : ℝ) + 3) ≤ h := by
  have hev := (eventually_logb_le (40000 * (C₀ + 1)) (by positivity)).natCast_atTop
  filter_upwards [hev, eventually_ge_atTop 2] with h hh h2
  refine ⟨h2, le_trans ?_ hh⟩
  have := degExp_le_logb h h2
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- From the single condition to the two conditions `large` and `beats`. -/
lemma conditions_of_main (C₀ : ℝ) (hC : 0 ≤ C₀) (h : ℕ) (h2 : 2 ≤ h)
    (hm : 40000 * (C₀ + 1) * ((degExp h : ℝ) + 3) ≤ h) :
    10000 * (degExp h + 3) ≤ ordExp h ∧
      C₀ * 2 ^ degExp h ≤ (ordExp h : ℝ) / (10000 * (degExp h + 3)) := by
  have hs : (2 * ordExp h : ℝ) = h * (h - 1) := by
    have := two_mul_ordExp h
    have hc : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [← hc]; exact_mod_cast this
  have hpow : ((2 : ℝ) ^ degExp h) ≤ 2 * ((h : ℝ) - 1) := by
    have := degExp_le h h2
    have hc : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [← hc]; exact_mod_cast this
  have hh1 : (1 : ℝ) ≤ (h : ℝ) - 1 := by
    have : (2 : ℝ) ≤ h := by exact_mod_cast h2
    linarith
  have he0 : (0 : ℝ) ≤ degExp h := Nat.cast_nonneg _
  constructor
  · -- `large`
    have : (10000 * ((degExp h : ℝ) + 3)) ≤ ordExp h := by nlinarith
    exact_mod_cast this
  · rw [le_div_iff₀ (by positivity)]
    have hp0 : (0 : ℝ) ≤ 2 ^ degExp h := by positivity
    calc C₀ * 2 ^ degExp h * (10000 * ((degExp h : ℝ) + 3))
        ≤ C₀ * (2 * ((h : ℝ) - 1)) * (10000 * ((degExp h : ℝ) + 3)) := by gcongr
      _ = (h - 1) * (20000 * C₀ * ((degExp h : ℝ) + 3)) := by ring
      _ ≤ (h - 1) * (h / 2) := by gcongr; nlinarith
      _ = ordExp h := by linarith

/-- **Arithmetic lemma of Theorem A.** For every `C₀ ≥ 0` and every `u ≥ 1` there is
`l ≥ 2` such that `h = l·u` satisfies both `large` and `beats`. The constants `C₀`, `u`
are fixed *before* `l` (they come from F.6, which quantifies `∃ u C₀, ∀ l`). -/
theorem exists_good_multiple (C₀ : ℝ) (hC : 0 ≤ C₀) (u : ℕ) (hu : 1 ≤ u) :
    ∃ l : ℕ, 2 ≤ l ∧ 10000 * (degExp (l * u) + 3) ≤ ordExp (l * u) ∧
      C₀ * 2 ^ degExp (l * u) ≤ (ordExp (l * u) : ℝ) / (10000 * (degExp (l * u) + 3)) := by
  have hlu : Tendsto (fun l : ℕ => l * u) atTop atTop :=
    tendsto_id.atTop_mul_const' (by omega)
  obtain ⟨l, ⟨h2, hm⟩, hl⟩ := ((hlu.eventually (eventually_main C₀ hC)).and
    (eventually_ge_atTop 2)).exists
  exact ⟨l, hl, conditions_of_main C₀ hC _ h2 hm⟩

/-- The referee's condition `h / (log₂ h + 4) > 40000·C₀` alone does **not** give `large`
when `C₀` is small: here is an instance with `C₀ = 0` (allowed by F.6: `0 ≤ C₀`),
`h = 2`, where the referee's condition holds but `large` fails. -/
example : (0 : ℝ) * 40000 < 2 / (Real.logb 2 2 + 4) ∧ ¬ (10000 * (degExp 2 + 3) ≤ ordExp 2) := by
  refine ⟨by rw [Real.logb_self_eq_one (by norm_num)]; norm_num, ?_⟩
  decide

end PortsLean.ThmA
