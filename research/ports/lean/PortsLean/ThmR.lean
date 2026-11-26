import Mathlib

/-!
# Theorem R: parameter bookkeeping (rebase/notebook.md §2.2–2.3)

Inputs, as hypotheses (the notebook's citations):

* AN Thm J.4 (`Paper/Cuts.lean` `thm_cut`): `272 ≤ H`, `16 ∣ H`, `v ≥ v₀`, `(lg v)^{C_cut α} ≤ v`,
  `v^H ≤ τ ≤ v^{Hα}`, `s·v^48 ≤ τ`; lister of size `≤ v^H`, `≤ τ v²/v^H` pieces of size
  `≤ v^{H−32}` that are `v^H`-plain, accepting runs `≤ τ/v^24` steps.
* Lemma 1 [R-p, not in any Lean statement]: with `α = 2`, every run makes `≤ τ/v^235` guesses.

Choice of parameters (a slight variant of the notebook's, with no rounding):
`v := ⌈τ^{1/(H+187)}⌉₊`, `τ' := v^{H+235}`. Then every J.4 constraint holds *exactly*
and `τ'/v^235 = v^H`.
-/

namespace PortsLean.ThmR

open Real Filter

/-! ## 1. J.4's constraints are met by `v`, `τ' = v^{H+235}` -/

/-- With `τ' = v^{H+235}`: `v^H ≤ τ'`, `τ' ≤ v^{2H}` (needs only `H ≥ 235`, not 272),
and `|z| v^48 ≤ τ'` whenever `|z| ≤ v^{H+187}`; and `τ'/v^235 = v^H`, `τ'/v^24 = v^{H+211}`,
`τ' v² / v^H = v^237` exactly. -/
theorem j4_constraints (H v z : ℕ) (hH : 235 ≤ H) (hv : 1 ≤ v) (hz : z ≤ v ^ (H + 187)) :
    v ^ H ≤ v ^ (H + 235) ∧ v ^ (H + 235) ≤ v ^ (2 * H) ∧ z * v ^ 48 ≤ v ^ (H + 235) ∧
      v ^ (H + 235) / v ^ 235 = v ^ H ∧ v ^ (H + 235) / v ^ 24 = v ^ (H + 211) ∧
      v ^ (H + 235) * v ^ 2 / v ^ H = v ^ 237 := by
  have hv0 : 0 < v := hv
  refine ⟨Nat.pow_le_pow_right hv (by omega), Nat.pow_le_pow_right hv (by omega), ?_, ?_, ?_, ?_⟩
  · calc z * v ^ 48 ≤ v ^ (H + 187) * v ^ 48 := Nat.mul_le_mul_right _ hz
      _ = v ^ (H + 235) := by rw [← pow_add]
  · rw [pow_add, Nat.mul_div_cancel _ (by positivity)]
  · rw [show H + 235 = (H + 211) + 24 by omega, pow_add, Nat.mul_div_cancel _ (by positivity)]
  · rw [← pow_add, show H + 235 + 2 = 237 + H by omega, pow_add, Nat.mul_div_cancel _ (by positivity)]

/-- `v = ⌈τ^{1/(H+187)}⌉₊` satisfies `τ ≤ v^{H+187}` and `v ≤ 2 τ^{1/(H+187)}` for `τ ≥ 1`. -/
theorem v_choice (H : ℕ) (τ : ℝ) (hτ : 1 ≤ τ) :
    let v := ⌈τ ^ ((1 : ℝ) / (H + 187))⌉₊
    τ ≤ (v : ℝ) ^ (H + 187) ∧ (v : ℝ) ≤ 2 * τ ^ ((1 : ℝ) / (H + 187)) ∧ 1 ≤ v := by
  intro v
  have hpos : (0 : ℝ) < H + 187 := by positivity
  have hr : 1 ≤ τ ^ ((1 : ℝ) / (H + 187)) := Real.one_le_rpow hτ (by positivity)
  have hle : τ ^ ((1 : ℝ) / (H + 187)) ≤ v := Nat.le_ceil _
  refine ⟨?_, ?_, ?_⟩
  · have : τ = (τ ^ ((1 : ℝ) / (H + 187))) ^ (H + 187 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      push_cast
      rw [one_div_mul_cancel hpos.ne', Real.rpow_one]
    calc τ = _ := this
      _ ≤ (v : ℝ) ^ (H + 187) := by gcongr
  · have := Nat.ceil_lt_add_one (show 0 ≤ τ ^ ((1 : ℝ) / (H + 187)) by positivity)
    linarith
  · exact_mod_cast hr.trans hle

/-! ## 2. Operation count of Lemma 2 / Theorem 1 -/

/-- Cost model of Lemma 2: enumerate `≤ 2^g` runs of the lister (each of `≤ t` steps), and for each
accepting run brute-force its `≤ P` pieces, each by `≤ 2^{v^H}` runs of `≤ v^H` steps. -/
def lemma2Cost (g t P vH : ℕ) : ℕ := 2 ^ g * (t + P * (2 ^ vH * vH))

lemma pow_le_two_pow_mul (v k : ℕ) : v ^ k ≤ 2 ^ (k * v) := by
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _

/-- With J.4 + Lemma 1 at `τ' = v^{H+235}`: `g ≤ v^H`, `t ≤ v^{H+211}`, `P ≤ v^237`, the total is
`≤ 2^{(2H+241)·v^H}`. The piece brute force (`2^{v^H}` per piece) is of the *same* order as the
run enumeration (`2^{τ'/v^235} = 2^{v^H}`): it is not negligible, it is exactly balanced. -/
theorem lemma2_cost_le (H v g t P : ℕ) (hH : 1 ≤ H) (hv : 1 ≤ v)
    (hg : g ≤ v ^ H) (ht : t ≤ v ^ (H + 211)) (hP : P ≤ v ^ 237) :
    lemma2Cost g t P (v ^ H) ≤ 2 ^ ((2 * H + 241) * v ^ H) := by
  unfold lemma2Cost
  have hvH : v ≤ v ^ H := by
    calc v = v ^ 1 := (pow_one v).symm
      _ ≤ v ^ H := Nat.pow_le_pow_right hv hH
  have h1 : t + P * (2 ^ v ^ H * v ^ H) ≤ 2 * (v ^ (H + 237 + H) * 2 ^ v ^ H) := by
    have a : t ≤ v ^ (H + 237 + H) * 2 ^ v ^ H := by
      calc t ≤ v ^ (H + 211) := ht
        _ ≤ v ^ (H + 237 + H) := Nat.pow_le_pow_right hv (by omega)
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
    have b : P * (2 ^ v ^ H * v ^ H) ≤ v ^ (H + 237 + H) * 2 ^ v ^ H := by
      calc P * (2 ^ v ^ H * v ^ H) ≤ v ^ 237 * (2 ^ v ^ H * v ^ H) := Nat.mul_le_mul_right _ hP
        _ = v ^ (237 + H) * 2 ^ v ^ H := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hv (by omega))
    omega
  have h2 : v ^ (H + 237 + H) ≤ 2 ^ ((2 * H + 237) * v ^ H) := by
    calc v ^ (H + 237 + H) ≤ 2 ^ ((H + 237 + H) * v) := pow_le_two_pow_mul _ _
      _ ≤ 2 ^ ((2 * H + 237) * v ^ H) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h3 : 2 ^ g ≤ 2 ^ v ^ H := Nat.pow_le_pow_right (by norm_num) hg
  have hone : 1 ≤ v ^ H := Nat.one_le_pow _ _ hv
  calc 2 ^ g * (t + P * (2 ^ v ^ H * v ^ H))
      ≤ 2 ^ v ^ H * (2 * (2 ^ ((2 * H + 237) * v ^ H) * 2 ^ v ^ H)) :=
        Nat.mul_le_mul h3 (h1.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)))
    _ = 2 ^ (v ^ H + 1 + (2 * H + 237) * v ^ H + v ^ H) := by
        rw [pow_add, pow_add, pow_add, pow_one]; ring
    _ ≤ 2 ^ ((2 * H + 241) * v ^ H) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **Theorem 1 arithmetic.** For `τ ≥ 1`, with `v = ⌈τ^{1/(H+187)}⌉₊`, the exponent of the
operation count is `≤ K·τ^{H/(H+187)}` with `K = (2H+241)·2^H`, independent of `τ`. -/
theorem theorem1_exponent (H : ℕ) (τ : ℝ) (hτ : 1 ≤ τ) :
    let v := ⌈τ ^ ((1 : ℝ) / (H + 187))⌉₊
    (((2 * H + 241) * v ^ H : ℕ) : ℝ) ≤ ((2 * H + 241) * 2 ^ H : ℝ) * τ ^ ((H : ℝ) / (H + 187)) := by
  intro v
  obtain ⟨-, hv2, -⟩ := v_choice H τ hτ
  have hr0 : 0 ≤ τ ^ ((1 : ℝ) / (H + 187)) := by positivity
  have : (v : ℝ) ^ H ≤ 2 ^ H * τ ^ ((H : ℝ) / (H + 187)) := by
    calc (v : ℝ) ^ H ≤ (2 * τ ^ ((1 : ℝ) / (H + 187))) ^ H := by gcongr
      _ = 2 ^ H * τ ^ ((H : ℝ) / (H + 187)) := by
        rw [mul_pow, ← Real.rpow_natCast (τ ^ _), ← Real.rpow_mul (by linarith)]
        congr 2; ring
  push_cast
  rw [mul_assoc]
  gcongr

/-! ## 3. The 3-SAT exponent -/

/-- `ρ = H/(H+187)`, `α* = (1−ρ)/(1+4ρ)`: then `α* = 187/(5H+187)` and `1 − (1+4α*)ρ = α*`
(the balance point of the two terms). -/
theorem alpha_star (H : ℝ) (hH : 0 < H) :
    let ρ := H / (H + 187)
    (1 - ρ) / (1 + 4 * ρ) = 187 / (5 * H + 187) ∧
      1 - (1 + 4 * (187 / (5 * H + 187))) * ρ = 187 / (5 * H + 187) := by
  intro ρ
  have h1 : H + 187 ≠ 0 := by positivity
  have h2 : 5 * H + 187 ≠ 0 := by positivity
  constructor <;> (simp only [ρ]; field_simp; ring)

/-- Choice of the sparsification exponent: for every `0 < δ < 187/(5H+187)` there is `α` with
`0 < α < 1/4` (needs `H > 112.2`; true for `H ≥ 272`), `δ < α` and `(1+4α)ρ < 1 − δ`. -/
theorem choose_alpha (H δ : ℝ) (hH : 113 ≤ H) (hδ : 0 < δ) (hδ' : δ < 187 / (5 * H + 187)) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 4 ∧ δ < α ∧ (1 + 4 * α) * (H / (H + 187)) < 1 - δ := by
  set a := 187 / (5 * H + 187) with ha
  have hpos : 0 < 5 * H + 187 := by linarith
  have ha4 : a < 1 / 4 := by rw [ha, div_lt_iff₀ hpos]; linarith
  refine ⟨(δ + a) / 2, by linarith, by linarith, by linarith, ?_⟩
  have hρ : 0 < H / (H + 187) := by positivity
  have hbal := (alpha_star H (by linarith)).2
  rw [← ha] at hbal
  nlinarith

/-- Asymptotic core: `x^a · log x ≤ x^b` eventually, for `a < b`. -/
lemma eventually_rpow_log_le (a b C : ℝ) (hab : a < b) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, C * (x ^ a * Real.log x) ≤ x ^ b := by
  have ho := (isLittleO_log_rpow_atTop (r := b - a) (by linarith)).def (c := 1 / C)
    (by positivity)
  filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with x hx h1
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (Real.log_nonneg h1), Real.norm_of_nonneg (by positivity)] at hx
  calc C * (x ^ a * Real.log x) ≤ C * (x ^ a * (1 / C * x ^ (b - a))) := by gcongr
    _ = x ^ a * x ^ (b - a) := by field_simp
    _ = x ^ b := by rw [← Real.rpow_add hx0]; ring_nf

/-- **3-SAT exponent.** With `ρ = H/(H+187)`, `α` from `choose_alpha`, and any constants
`A, B, c > 0`, the total exponent `A n^{1−α} log n + B (c n^{1+4α} log n)^ρ` is `≤ 2 n^{1−δ}` for all
large `n`. (The first term: sparsification leaves; the second: Theorem 1 at `τ = L = c n^{1+4α} log n`.) -/
theorem sat_exponent (H δ A B c : ℝ) (hH : 113 ≤ H) (hδ : 0 < δ) (hδ' : δ < 187 / (5 * H + 187))
    (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 4 ∧ ∀ᶠ n : ℝ in atTop,
      A * (n ^ (1 - α) * Real.log n) + B * (c * n ^ (1 + 4 * α) * Real.log n) ^ (H / (H + 187)) ≤
        2 * n ^ (1 - δ) := by
  obtain ⟨α, hα0, hα4, hδα, hρ⟩ := choose_alpha H δ hH hδ hδ'
  refine ⟨α, hα0, hα4, ?_⟩
  set ρ := H / (H + 187) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρdef, div_le_one (by linarith)]; linarith
  -- second term: (c n^{1+4α} log n)^ρ ≤ (c n^{1+4α} · n)^ρ ... use log n ≤ n^ε
  set ε := (1 - δ - (1 + 4 * α) * ρ) / (2 * ρ) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hlog := (isLittleO_log_rpow_atTop hε0).def (c := 1) one_pos
  have hpow : ∀ᶠ n : ℝ in atTop, B * c ^ ρ * n ^ ((1 + 4 * α) * ρ + ε * ρ) ≤ n ^ (1 - δ) := by
    have hlt : (1 + 4 * α) * ρ + ε * ρ < 1 - δ := by
      rw [hε]; field_simp; nlinarith
    -- x^p ≤ x^q / K eventually when p < q
    have := tendsto_rpow_atTop (show 0 < (1 - δ) - ((1 + 4 * α) * ρ + ε * ρ) by linarith)
    filter_upwards [this.eventually_ge_atTop (B * c ^ ρ), eventually_ge_atTop (1 : ℝ)] with n hn h1
    have hn0 : 0 < n := by linarith
    calc B * c ^ ρ * n ^ ((1 + 4 * α) * ρ + ε * ρ)
        ≤ n ^ ((1 - δ) - ((1 + 4 * α) * ρ + ε * ρ)) * n ^ ((1 + 4 * α) * ρ + ε * ρ) := by gcongr
      _ = n ^ (1 - δ) := by rw [← Real.rpow_add hn0]; ring_nf
  have hfirst := eventually_rpow_log_le (1 - α) (1 - δ) A (by linarith) hA
  filter_upwards [hfirst, hpow, hlog, eventually_ge_atTop (1 : ℝ)] with n h1 h2 h3 hn1
  have hn0 : 0 < n := by linarith
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [Real.norm_of_nonneg hl0, Real.norm_of_nonneg (by positivity), one_mul] at h3
  have hsecond : B * (c * n ^ (1 + 4 * α) * Real.log n) ^ ρ ≤ n ^ (1 - δ) := by
    calc B * (c * n ^ (1 + 4 * α) * Real.log n) ^ ρ
        ≤ B * (c * n ^ (1 + 4 * α) * n ^ ε) ^ ρ := by gcongr
      _ = B * c ^ ρ * n ^ ((1 + 4 * α) * ρ + ε * ρ) := by
        rw [mul_assoc c, ← Real.rpow_add hn0, Real.mul_rpow hc.le (by positivity),
          ← Real.rpow_mul hn0.le]; ring_nf
      _ ≤ _ := h2
  linarith

/-! ## 4. The unstated side condition of J.4 at `α = 2` -/

/-- J.4 needs `(lg v)^{C_cut·α} ≤ v`; with `α = 2` fixed this holds for all large `v`
(so `v₀` must be enlarged depending on `C_cut`; the notebook folds this into "v ≥ v₀ large"). -/
theorem polylog_condition (C : ℝ) (hC : 0 < C) :
    ∀ᶠ v : ℝ in atTop, (Real.logb 2 v) ^ (C * 2) ≤ v := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho := (isLittleO_log_rpow_atTop (r := 1 / (C * 2)) (by positivity)).def
    (c := Real.log 2) hl2
  filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with v hv h1
  have hv0 : 0 < v := by linarith
  have hl0 : 0 ≤ Real.log v := Real.log_nonneg h1
  rw [Real.norm_of_nonneg hl0, Real.norm_of_nonneg (by positivity)] at hv
  have hb : Real.logb 2 v ≤ v ^ (1 / (C * 2)) := by
    rw [Real.logb, div_le_iff₀ hl2]; linarith
  have hb0 : 0 ≤ Real.logb 2 v := Real.logb_nonneg (by norm_num) h1
  calc Real.logb 2 v ^ (C * 2) ≤ (v ^ (1 / (C * 2))) ^ (C * 2) := by gcongr
    _ = v := by rw [← Real.rpow_mul hv0.le, one_div_mul_cancel (by positivity), Real.rpow_one]

/-! ## 5. Lemma 1's per-cut and composed arithmetic -/

/-- Per cut: `τΛ/v^256 + v^64·τΛ²/v^300 ≤ 2τΛ²/v^236` (for `Λ ≥ 1`, `v ≥ 1`). -/
theorem lemma1_per_cut (τ Λ v : ℝ) (hτ : 0 ≤ τ) (hΛ : 1 ≤ Λ) (hv : 1 ≤ v) :
    τ * Λ / v ^ 256 + v ^ 64 * (τ * Λ ^ 2 / v ^ 300) ≤ 2 * τ * Λ ^ 2 / v ^ 236 := by
  have hv0 : 0 < v := by linarith
  have e1 : v ^ 64 * (τ * Λ ^ 2 / v ^ 300) = τ * Λ ^ 2 / v ^ 236 := by
    field_simp
  have e2 : τ * Λ / v ^ 256 ≤ τ * Λ ^ 2 / v ^ 236 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : v ^ 236 ≤ v ^ 256 := pow_le_pow_right₀ hv (by norm_num)
    have h2 : Λ ≤ Λ ^ 2 := by nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hτ) h1 (by positivity) (by positivity)
  rw [e1]
  have : 2 * τ * Λ ^ 2 / v ^ 236 = τ * Λ ^ 2 / v ^ 236 + τ * Λ ^ 2 / v ^ 236 := by ring
  linarith

/-- Composition over `r` cuts with `P_i τ_i ≤ τ (4Λ²)^i`: total guesses `≤ τ/v^235` provided
`2 r (4Λ²)^r Λ² ≤ v` (the polylog-loss condition; notebook l.163–166). -/
theorem lemma1_composed (τ Λ v : ℝ) (r : ℕ) (P τs : ℕ → ℝ) (hτ : 0 ≤ τ) (hΛ : 1 ≤ Λ) (hv : 1 ≤ v)
    (hPτ : ∀ i, P i * τs i ≤ τ * (4 * Λ ^ 2) ^ i)
    (hloss : 2 * r * (4 * Λ ^ 2) ^ r * Λ ^ 2 ≤ v) :
    ∑ i ∈ Finset.range r, P i * (2 * τs i * Λ ^ 2 / v ^ 236) ≤ τ / v ^ 235 := by
  have hv0 : 0 < v := by linarith
  have hq : 1 ≤ 4 * Λ ^ 2 := by nlinarith
  have hterm : ∀ i ∈ Finset.range r, P i * (2 * τs i * Λ ^ 2 / v ^ 236) ≤
      2 * (τ * (4 * Λ ^ 2) ^ r) * Λ ^ 2 / v ^ 236 := by
    intro i hi
    have hi' : i ≤ r := (Finset.mem_range.mp hi).le
    rw [show P i * (2 * τs i * Λ ^ 2 / v ^ 236) = 2 * (P i * τs i) * Λ ^ 2 / v ^ 236 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : τ * (4 * Λ ^ 2) ^ i ≤ τ * (4 * Λ ^ 2) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hi') hτ
    linarith [hPτ i]
  calc _ ≤ ∑ _i ∈ Finset.range r, 2 * (τ * (4 * Λ ^ 2) ^ r) * Λ ^ 2 / v ^ 236 := Finset.sum_le_sum hterm
    _ = τ * (2 * r * (4 * Λ ^ 2) ^ r * Λ ^ 2) / v ^ 236 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ τ * v / v ^ 236 := by gcongr
    _ = τ / v ^ 235 := by field_simp

end PortsLean.ThmR
