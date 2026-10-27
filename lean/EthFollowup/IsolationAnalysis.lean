/-
# Analytic estimates for the isolation lemma

`isolation_count` gives an explicit fraction of isolating hashes. This file shows the fraction is
at least `exp(−δN)` for every `δ > 0`, with suitable parameters, for all large `N`.
-/
import EthFollowup.IsolationLemma
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace EthFollowup.Isolation

open Finset Real

/-- The classical bound `Σ_{i ≤ t} C(N, i) ≤ exp(N · H(p))` for `t ≤ pN`, `0 < p ≤ 1/2`. -/
theorem sum_choose_le_exp (N t : ℕ) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 1 / 2) (ht : (t : ℝ) ≤ p * N) :
    (∑ i ∈ range (t + 1), (N.choose i : ℝ)) ≤ exp (N * binEntropy p) := by
  have hp1 : 0 < 1 - p := by linarith
  have hlog : log p ≤ log (1 - p) := log_le_log hp (by linarith)
  -- each retained term has weight at least exp(-N H(p))
  have hweight : ∀ i ∈ range (t + 1), exp (-(N * binEntropy p)) ≤ p ^ i * (1 - p) ^ (N - i) := by
    intro i hi
    have hit : (i : ℝ) ≤ p * N := (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).trans ht
    by_cases hiN : i ≤ N
    · rw [← exp_log (by positivity : (0:ℝ) < p ^ i * (1 - p) ^ (N - i)), exp_le_exp,
        log_mul (by positivity) (by positivity), log_pow, log_pow, Nat.cast_sub hiN]
      rw [binEntropy, log_inv, log_inv]
      nlinarith [mul_le_mul_of_nonneg_right hit (sub_nonneg.2 hlog), log_nonpos hp.le (by linarith : p ≤ 1),
        log_nonpos hp1.le (by linarith : 1 - p ≤ 1)]
    · exfalso
      have : (N : ℝ) < i := by exact_mod_cast Nat.lt_of_not_le hiN
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hsum : (∑ i ∈ range (t + 1), (N.choose i : ℝ) * (p ^ i * (1 - p) ^ (N - i))) ≤ 1 := by
    have htot : (∑ i ∈ range (N + 1), (N.choose i : ℝ) * (p ^ i * (1 - p) ^ (N - i))) = 1 := by
      have h := add_pow p (1 - p) N
      rw [add_sub_cancel, one_pow] at h
      calc (∑ i ∈ range (N + 1), (N.choose i : ℝ) * (p ^ i * (1 - p) ^ (N - i)))
          = ∑ m ∈ range (N + 1), p ^ m * (1 - p) ^ (N - m) * (N.choose m : ℝ) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = 1 := h.symm
    by_cases htN : t + 1 ≤ N + 1
    · refine le_of_le_of_eq ?_ htot
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono htN)
        (fun i _ _ => by positivity)
    · -- t ≥ N + 1: the extra terms vanish
      have hsub : range (t + 1) = range (N + 1) ∪ (range (t + 1) \ range (N + 1)) := by
        rw [Finset.union_sdiff_of_subset (Finset.range_mono (by omega))]
      rw [hsub, Finset.sum_union Finset.disjoint_sdiff]
      have : ∑ i ∈ range (t + 1) \ range (N + 1),
          (N.choose i : ℝ) * (p ^ i * (1 - p) ^ (N - i)) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hi
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
      rw [this, add_zero]
      exact htot.le
  calc (∑ i ∈ range (t + 1), (N.choose i : ℝ))
      = exp (N * binEntropy p) * ∑ i ∈ range (t + 1), (N.choose i : ℝ) * exp (-(N * binEntropy p)) := by
        rw [← Finset.sum_mul, mul_comm, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ ≤ exp (N * binEntropy p) * ∑ i ∈ range (t + 1), (N.choose i : ℝ) * (p ^ i * (1 - p) ^ (N - i)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (exp_pos _).le
        exact mul_le_mul_of_nonneg_left (hweight i hi) (Nat.cast_nonneg _)
    _ ≤ exp (N * binEntropy p) * 1 := mul_le_mul_of_nonneg_left hsum (exp_pos _).le
    _ = _ := mul_one _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ballVol_eq (r : ℕ) : ballVol ι r = ∑ i ∈ range r, (Fintype.card ι).choose i := by
  rw [ballVol, Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := range r)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.filter_filter]
    have : ((univ : Finset (Finset ι)).filter fun T => T.card < r ∧ T.card = i) =
        Finset.powersetCard i univ := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨h ▸ Finset.mem_range.1 hi, h⟩
    rw [this, Finset.card_powersetCard, Finset.card_univ]
  · intro T hT
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hT
    exact Finset.mem_coe.2 (Finset.mem_range.2 hT)

/-- The union-bound condition, in real form. -/
theorem Hm_of_real {k m : ℕ} (s a b : ℕ) (ha : 0 < a)
    (h : (2 * s : ℝ) ≤ (2 * a / (a + b) : ℝ) ^ m) :
    2 * s * (2 ^ k * (a + b)) ^ m ≤ 2 ^ m * (a * 2 ^ k) ^ m := by
  have hab : (0 : ℝ) < a + b := by positivity
  have hpos : (0 : ℝ) < (2 ^ k * (a + b)) ^ m := by positivity
  have : ((2 * s * (2 ^ k * (a + b)) ^ m : ℕ) : ℝ) ≤ ((2 ^ m * (a * 2 ^ k) ^ m : ℕ) : ℝ) := by
    push_cast
    calc (2 * s : ℝ) * (2 ^ k * (a + b)) ^ m
        ≤ (2 * a / (a + b)) ^ m * (2 ^ k * (a + b)) ^ m := mul_le_mul_of_nonneg_right h hpos.le
      _ = 2 ^ m * (a * 2 ^ k) ^ m := by
          rw [← mul_pow, ← mul_pow]
          congr 1
          field_simp
  exact_mod_cast this

/-- Choice of `m`: the union-bound condition holds and `2^m` is not much larger than needed. -/
theorem exists_m {ρ : ℝ} (hρ : 1 < ρ) (s : ℝ) (hs : 1 ≤ s) :
    ∃ m : ℕ, 2 * s ≤ ρ ^ m ∧ (2 : ℝ) ^ m ≤ 2 * (2 * s) ^ (log 2 / log ρ) := by
  have hlρ : 0 < log ρ := log_pos hρ
  have h2s : 0 < 2 * s := by linarith
  refine ⟨⌈log (2 * s) / log ρ⌉₊, ?_, ?_⟩
  · have hc := Nat.le_ceil (log (2 * s) / log ρ)
    calc 2 * s = exp (log (2 * s)) := (exp_log h2s).symm
      _ = exp (log (2 * s) / log ρ * log ρ) := by rw [div_mul_cancel₀ _ hlρ.ne']
      _ ≤ exp (⌈log (2 * s) / log ρ⌉₊ * log ρ) :=
          exp_le_exp.2 (mul_le_mul_of_nonneg_right hc hlρ.le)
      _ = ρ ^ ⌈log (2 * s) / log ρ⌉₊ := by
          rw [← log_pow, exp_log (pow_pos (by linarith) _)]
  · have hl2s : 0 ≤ log (2 * s) := log_nonneg (by linarith)
    have hc := Nat.ceil_lt_add_one (div_nonneg hl2s hlρ.le)
    calc (2 : ℝ) ^ ⌈log (2 * s) / log ρ⌉₊ = exp (⌈log (2 * s) / log ρ⌉₊ * log 2) := by
          rw [← log_pow, exp_log (by positivity)]
      _ ≤ exp ((log (2 * s) / log ρ + 1) * log 2) :=
          exp_le_exp.2 (mul_le_mul_of_nonneg_right hc.le (log_nonneg (by norm_num)))
      _ = 2 * (2 * s) ^ (log 2 / log ρ) := by
          rw [rpow_def_of_pos h2s, add_mul, one_mul, exp_add, exp_log (by norm_num : (0:ℝ) < 2),
            mul_comm (exp _) 2]
          congr 2
          ring

/-- Small `ε` making the entropy terms small. -/
theorem exists_eps {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 8 ∧ binEntropy ε + binEntropy (4 * ε) + 4 * ε * log 2 < δ / 3 := by
  have hcont : Continuous fun ε : ℝ => binEntropy ε + binEntropy (4 * ε) + 4 * ε * log 2 := by
    fun_prop
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hcont.continuousAt (δ / 3) (by positivity)
  refine ⟨min (η / 2) (1 / 8), by positivity, min_le_right _ _, ?_⟩
  have hd : dist (min (η / 2) (1 / 8)) 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact (min_le_left _ _).trans_lt (by linarith)
  have := hball hd
  simp only [mul_zero, binEntropy_zero, add_zero, zero_mul, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-- Small `τ` making `log 2 / log (2/(1+τ))` close to 1. -/
theorem exists_tau {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ (log 2 / log (2 / (1 + τ)) - 1) * log 2 < δ / 3 := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hcont : ContinuousAt (fun τ : ℝ => log 2 / log (2 / (1 + τ))) 0 := by
    refine continuousAt_const.div ?_ (by norm_num)
    refine ContinuousAt.log (continuousAt_const.div (continuousAt_const.add continuousAt_id)
      (by norm_num)) (by norm_num)
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hcont (δ / 3 / log 2) (by positivity)
  refine ⟨min (η / 2) (1 / 2), by positivity, min_le_right _ _, ?_⟩
  have hd : dist (min (η / 2) (1 / 2)) 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact (min_le_left _ _).trans_lt (by linarith)
  have := hball hd
  simp only [add_zero, div_one, Real.dist_eq] at this
  rw [div_self hl2.ne'] at this
  have h1 := (le_abs_self _).trans_lt this
  rw [lt_div_iff₀ hl2] at h1
  exact h1

universe u

/-- **Isolation with success `exp(−δN)`.** For every `δ > 0` there are a sparsity `k` and a
threshold `N₀` such that for every `S ⊆ {0,1}^ι` with `N = |ι| ≥ N₀`, suitable `m, r, d`
satisfy the hypotheses of `isolation_count`, and the explicit fraction is at least `exp(−δN)`. -/
theorem isolation_fraction {δ : ℝ} (hδ : 0 < δ) :
    ∃ k N₀ : ℕ, ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool)),
      S.Nonempty → N₀ ≤ Fintype.card ι →
      ∃ m r d : ℕ, 2 * r ≤ d ∧ d ≤ Fintype.card ι ∧
        2 * S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m ≤
          2 ^ m * (Fintype.card ι ^ k * 2 ^ k) ^ m ∧
        exp (-(δ * Fintype.card ι)) *
            (2 * ballVol ι r * 2 ^ m * (Fintype.card ι).choose d * 2 ^ d : ℕ) ≤ S.card := by
  obtain ⟨ε, hε, hε8, hg⟩ := exists_eps hδ
  obtain ⟨τ, hτ, hτ2, hθ⟩ := exists_tau hδ
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  set θ₀ := log 2 / log (2 / (1 + τ)) with hθ₀
  have hlτ : 0 < log (2 / (1 + τ)) := log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hτ (by linarith : 1 - ε < 1)
  set k := max k₀ 1 with hk
  have hk1 : 1 ≤ k := le_max_right _ _
  have hpowk : (1 - ε) ^ k ≤ τ :=
    (pow_le_pow_of_le_one (by linarith) (by linarith) (le_max_left _ _)).trans hk₀.le
  set N₀ := ⌈1 / ε⌉₊ + ⌈3 * log (4 * 2 ^ θ₀) / δ⌉₊ + 8 with hN₀
  refine ⟨k, N₀, fun ι _ _ S hS hN => ?_⟩
  set N := Fintype.card ι with hNdef
  have hNR : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 / ε : ℝ) ≤ N := by
    refine (Nat.le_ceil _).trans (le_trans ?_ hNR); rw [hN₀]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈3 * log (4 * 2 ^ θ₀) / δ⌉₊]
  have hεN : 1 ≤ ε * N := by rw [div_le_iff₀ hε] at hN1; linarith
  have hNpos : (0 : ℝ) < N := by nlinarith
  -- radius, fixed-coordinate count
  set r := ⌊ε * N⌋₊ + 1 with hr
  set d := 2 * r with hd
  have hr_gt : ε * N < r := by rw [hr]; push_cast; exact Nat.lt_floor_add_one _
  have hr_le : (r : ℝ) ≤ ε * N + 1 := by rw [hr]; push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ ε * N)]
  have hd_le : (d : ℝ) ≤ 4 * ε * N := by rw [hd]; push_cast; linarith
  have hdN : d ≤ N := by
    have : (d : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hrN : r ≤ N := by omega
  -- the ratio ρ
  set a : ℕ := N ^ k with ha
  set b : ℕ := (N - r) ^ k with hb
  have haR : (0 : ℝ) < a := by rw [ha]; push_cast; positivity
  have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hba : (b : ℝ) / a ≤ τ := by
    rw [ha, hb]; push_cast
    rw [← div_pow, Nat.cast_sub hrN]
    have hrNR : (r : ℝ) ≤ N := by exact_mod_cast hrN
    refine (pow_le_pow_left₀ (div_nonneg (by linarith) hNpos.le) ?_ k).trans hpowk
    rw [div_le_iff₀ hNpos]; nlinarith
  set ρ : ℝ := 2 * a / (a + b) with hρ
  have hρ_ge : 2 / (1 + τ) ≤ ρ := by
    rw [hρ, div_le_div_iff₀ (by linarith) (by positivity)]
    have : (b : ℝ) ≤ τ * a := by rwa [div_le_iff₀ haR] at hba
    nlinarith
  have hρ_gt : 1 < ρ := lt_of_lt_of_le (by rw [lt_div_iff₀ (by linarith)]; linarith) hρ_ge
  have hρ_le : ρ ≤ 2 := by rw [hρ, div_le_iff₀ (by positivity)]; nlinarith
  -- choose m
  have hs1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  obtain ⟨m, hm1, hm2⟩ := exists_m hρ_gt (S.card : ℝ) hs1
  refine ⟨m, r, d, le_refl _, hdN, Hm_of_real S.card a b (by exact_mod_cast haR) hm1, ?_⟩
  -- the estimate
  set θ := log 2 / log ρ with hθdef
  have hlρ : 0 < log ρ := log_pos hρ_gt
  have hθ1 : 1 ≤ θ := by
    rw [hθdef, le_div_iff₀ hlρ, one_mul]; exact log_le_log (by linarith) hρ_le
  have hθθ₀ : θ ≤ θ₀ := by
    rw [hθdef, hθ₀]
    exact div_le_div_of_nonneg_left hl2.le hlτ (log_le_log (by positivity) hρ_ge)
  have hV : (ballVol ι r : ℝ) ≤ exp (N * binEntropy ε) := by
    rw [ballVol_eq, hr]; push_cast
    exact sum_choose_le_exp N _ hε (by linarith) (Nat.floor_le (by positivity))
  have hC : ((N.choose d : ℕ) : ℝ) ≤ exp (N * binEntropy (4 * ε)) := by
    refine le_trans ?_ (sum_choose_le_exp N d (by positivity) (by linarith) (by linarith))
    exact Finset.single_le_sum (f := fun i => (N.choose i : ℝ)) (fun i _ => Nat.cast_nonneg _)
      (Finset.self_mem_range_succ d)
  have h2d : ((2 : ℕ) : ℝ) ^ d ≤ exp (4 * ε * N * log 2) := by
    rw [← exp_log (by positivity : (0:ℝ) < ((2:ℕ):ℝ) ^ d), log_pow, exp_le_exp]
    push_cast
    exact mul_le_mul_of_nonneg_right hd_le hl2.le
  have hsN : (S.card : ℝ) ≤ 2 ^ N := by
    have := Finset.card_le_univ S
    rw [Fintype.card_fun, Fintype.card_bool] at this
    exact_mod_cast this
  have hpow : (2 * (S.card : ℝ)) ^ θ ≤ 2 ^ θ₀ * S.card * exp (N * ((θ₀ - 1) * log 2)) := by
    rw [mul_rpow (by norm_num) (by positivity)]
    have e1 : (S.card : ℝ) ^ θ = S.card * (S.card : ℝ) ^ (θ - 1) := by
      conv_lhs => rw [show θ = 1 + (θ - 1) by ring]
      rw [rpow_add (by positivity), rpow_one]
    rw [e1, ← mul_assoc]
    refine mul_le_mul (mul_le_mul_of_nonneg_right
      (rpow_le_rpow_of_exponent_le (by norm_num) hθθ₀) (by positivity)) ?_ (by positivity)
      (by positivity)
    calc (S.card : ℝ) ^ (θ - 1) ≤ (2 ^ N : ℝ) ^ (θ - 1) :=
          rpow_le_rpow (by positivity) hsN (by linarith)
      _ = exp (N * ((θ - 1) * log 2)) := by
          rw [rpow_def_of_pos (by positivity), log_pow]; ring_nf
      _ ≤ exp (N * ((θ₀ - 1) * log 2)) := by
          refine exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact mul_le_mul_of_nonneg_right (by linarith) hl2.le
  have hconst : 4 * (2 : ℝ) ^ θ₀ ≤ exp (δ / 3 * N) := by
    have hpos : (0 : ℝ) < 4 * 2 ^ θ₀ := by positivity
    rw [← exp_log hpos, exp_le_exp]
    have : 3 * log (4 * 2 ^ θ₀) / δ ≤ N := by
      refine (Nat.le_ceil _).trans (le_trans ?_ hNR); rw [hN₀]; push_cast
      linarith [Nat.cast_nonneg (α := ℝ) ⌈1 / ε⌉₊]
    rw [div_le_iff₀ hδ] at this
    linarith
  -- combine
  push_cast
  have hV0 : (0:ℝ) ≤ ballVol ι r := Nat.cast_nonneg _
  have hC0 : (0:ℝ) ≤ (N.choose d : ℝ) := Nat.cast_nonneg _
  calc exp (-(δ * N)) * (2 * ballVol ι r * 2 ^ m * N.choose d * 2 ^ d)
      ≤ exp (-(δ * N)) * (2 * exp (N * binEntropy ε) * (2 * (2 * (S.card : ℝ)) ^ θ) *
          exp (N * binEntropy (4 * ε)) * exp (4 * ε * N * log 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
        have h2d' : (2 : ℝ) ^ d ≤ exp (4 * ε * N * log 2) := by exact_mod_cast h2d
        gcongr
    _ ≤ exp (-(δ * N)) * (2 * exp (N * binEntropy ε) *
          (2 * (2 ^ θ₀ * S.card * exp (N * ((θ₀ - 1) * log 2)))) *
          exp (N * binEntropy (4 * ε)) * exp (4 * ε * N * log 2)) := by gcongr
    _ = (4 * 2 ^ θ₀) * S.card * exp (N * (binEntropy ε + binEntropy (4 * ε) + 4 * ε * log 2 +
          (θ₀ - 1) * log 2 - δ)) := by
        rw [show N * (binEntropy ε + binEntropy (4 * ε) + 4 * ε * log 2 + (θ₀ - 1) * log 2 - δ) =
          -(δ * N) + N * binEntropy ε + N * ((θ₀ - 1) * log 2) + N * binEntropy (4 * ε) +
            4 * ε * N * log 2 by ring]
        rw [exp_add, exp_add, exp_add, exp_add]; ring
    _ ≤ exp (δ / 3 * N) * S.card * exp (N * (-(δ / 3))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hconst (by positivity))
          (exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hNpos.le)) (exp_pos _).le
          (by positivity)
    _ = S.card := by
        rw [mul_comm (exp _) (S.card : ℝ), mul_assoc, ← exp_add]
        rw [show δ / 3 * N + N * -(δ / 3) = 0 by ring, exp_zero, mul_one]

end EthFollowup.Isolation
