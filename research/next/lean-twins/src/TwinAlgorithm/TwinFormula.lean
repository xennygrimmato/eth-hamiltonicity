import PrimeAlgorithm.PrimeCountInteger

/-! # The twin-prime formula and its exact integer reconstruction

For every `n ≥ 2`, Ni's identity writes the prime indicator as a finite sum of
four-factor amplitudes over the witnesses `(x, d, y)` of `n`:
`1_prime(n) = -∑_{x,d,y} log(n/d)/log n · e(x/n) · e(y/d)`.
The twin count is `∑_{2≤n≤N} 1_prime(n) 1_prime(n+2)`.  Replacing each of the
four factors by Ni's certified rational Cauchy approximations gives an
approximation whose total error is below `1/2` (`twin_round`), and whose value has
the single explicit denominator `commonScale b ^ 8` (`approximateTwin_spec`).
Hence pure integer division recovers the exact twin count (`twinResult_eq`). -/

noncomputable section
namespace TwinAlgorithm.TwinFormula
open Finset PrimeAlgorithm PrimeAlgorithm.DoubleRamanujan PrimeAlgorithm.CertifiedPrimeSum
  PrimeAlgorithm.CertifiedNumerator PrimeAlgorithm.IntegerPrimeSum PrimeAlgorithm.CertifiedCauchy
open scoped ArithmeticFunction.Moebius

/-- The twin-prime count, with the convention `p ≤ N` (the partner `p+2` may exceed `N`). -/
def twinCount (N : ℕ) : ℕ := ((range (N+1)).filter fun p => p.Prime ∧ (p+2).Prime).card

/-- The local (one-`n`) phase expansion with arbitrary amplitudes. -/
def localTerm (n : ℕ) (A : ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  -(∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ y ∈ unitsBelow d, A n d x y)

theorem primeIndicator_phase (n : ℕ) :
    ((if n.Prime then 1 else 0 : ℕ) : ℂ) = localTerm n amplitude := by
  have h := congrArg (fun t : ℝ => (t : ℂ)) (moebius_vonMangoldt_primeIndicator n)
  have h' : -(μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) =
      if n.Prime then 1 else 0 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_intCast, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h
  rw [localTerm, ← PrimeCountFormula.term_phase, h']
  split_ifs <;> simp

theorem twinCount_eq_sum (N : ℕ) :
    (twinCount N : ℂ) = ∑ n ∈ Icc 2 N,
      ((if n.Prime then 1 else 0 : ℕ) : ℂ) * ((if (n+2).Prime then 1 else 0 : ℕ) : ℂ) := by
  have h1 : twinCount N = ∑ n ∈ range (N+1),
      (if n.Prime then 1 else 0) * (if (n+2).Prime then 1 else 0) := by
    rw [twinCount, card_filter]
    apply sum_congr rfl
    intro n _
    by_cases ha : n.Prime <;> by_cases hb : (n+2).Prime <;> simp [ha, hb]
  have h2 : (∑ n ∈ range (N+1), (if n.Prime then 1 else 0) * (if (n+2).Prime then 1 else 0)) =
      ∑ n ∈ Icc 2 N, (if n.Prime then 1 else 0) * (if (n+2).Prime then 1 else 0) := by
    symm
    apply sum_subset
    · intro n hn
      exact mem_range.mpr (by have := (mem_Icc.mp hn).2; omega)
    · intro n hn hnot
      have hnN : n ≤ N := by have := mem_range.mp hn; omega
      have hsmall : n ≤ 1 := by
        have : ¬(2 ≤ n ∧ n ≤ N) := by simpa only [mem_Icc] using hnot
        omega
      interval_cases n <;> simp [Nat.not_prime_zero, Nat.not_prime_one]
  rw [h1, h2]
  push_cast
  rfl

/-- The approximate amplitude used by Ni's prime-counting algorithm. -/
def approxAmplitude (b : ℕ) (D : PrimeData) : ℕ → ℕ → ℕ → ℕ → ℂ :=
  fun n d x y => approximateLog b D (n/d) * approximateInvLog b D n *
    approximatePhase b D n x * approximatePhase b D d y

/-- The approximate prime indicator at one `n`. -/
def approxIndicator (b : ℕ) (D : PrimeData) (n : ℕ) : ℂ := localTerm n (approxAmplitude b D)

/-- The approximate twin count. -/
def approximateTwin (b : ℕ) (D : PrimeData) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 2 N, approxIndicator b D n * approxIndicator b D (n+2)

/-- One-`n` error: at most `n²` witnesses, each with error `ε`. -/
theorem localTerm_error (n : ℕ) (A B : ℕ → ℕ → ℕ → ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ x ∈ unitsBelow n, ∀ d ∈ n.divisors, ∀ y ∈ unitsBelow d,
      ‖A n d x y - B n d x y‖ ≤ ε) :
    ‖localTerm n A - localTerm n B‖ ≤ (n : ℝ) ^ 2 * ε := by
  have hid : localTerm n A - localTerm n B =
      -(∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ y ∈ unitsBelow d, (A n d x y - B n d x y)) := by
    simp only [localTerm, sum_sub_distrib, neg_sub_neg]
    ring
  rw [hid, norm_neg]
  have hcn : ((unitsBelow n).card : ℝ) ≤ n := by exact_mod_cast unitsBelow_card_le n
  calc
    _ ≤ ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ y ∈ unitsBelow d, ‖A n d x y - B n d x y‖ := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro x _
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro d _
      exact norm_sum_le _ _
    _ ≤ ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ _y ∈ unitsBelow d, ε := by
      apply sum_le_sum; intro x hx
      apply sum_le_sum; intro d hd
      exact sum_le_sum (fun y hy => herr x hx d hd y hy)
    _ = ((unitsBelow n).card : ℝ) * (n : ℝ) * ε := by
      simp only [sum_const, nsmul_eq_mul]
      rw [← sum_mul, ← Nat.cast_sum]
      change ((unitsBelow n).card : ℝ) *
        (((∑ d ∈ n.divisors, ((range d).filter (fun x => x.Coprime d)).card : ℕ) : ℝ) * ε) = _
      rw [Ramanujan.phase_witness_count]
      ring
    _ ≤ (n : ℝ) * n * ε := by gcongr
    _ = _ := by ring

/-- Each approximate indicator is within `n² (12+10b) δ_b` of the true indicator. -/
theorem approxIndicator_error {b : ℕ} {D : PrimeData} (hD : Certified b D) {n : ℕ}
    (hn : 2 ≤ n) (hnb : n ≤ 2 ^ b) :
    ‖approxIndicator b D n - ((if n.Prime then 1 else 0 : ℕ) : ℂ)‖ ≤
      (n : ℝ) ^ 2 * ((12 + 10 * (b : ℝ)) * componentTolerance b) := by
  rw [primeIndicator_phase, approxIndicator]
  apply localTerm_error n _ _ _ (mul_nonneg (by positivity) (componentTolerance_nonneg b))
  intro x hx d hd y hy
  apply amplitude_error x y _ _ _ _ _ hn hnb hd
    (componentTolerance_nonneg b) (componentTolerance_le_one b)
  · exact log_accuracy hD ((Nat.div_le_self n d).trans hnb)
  · exact invLog_accuracy hD hn hnb
  · exact phase_accuracy hD (by omega) (mem_range.mp (mem_filter.mp hx).1)
  · exact phase_accuracy hD (Nat.pos_of_mem_divisors hd) (mem_range.mp (mem_filter.mp hy).1)

theorem product_error (a a' c c' : ℂ) (e : ℝ) (he1 : e ≤ 1)
    (ha : ‖a - a'‖ ≤ e) (hc : ‖c - c'‖ ≤ e) (ha' : ‖a'‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) :
    ‖a * c - a' * c'‖ ≤ 3 * e := by
  have he0 : 0 ≤ e := (norm_nonneg _).trans ha
  have hcn : ‖c‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' c c'
    linarith [norm_sub_rev c c']
  have hid : a * c - a' * c' = (a - a') * c + a' * (c - c') := by ring
  rw [hid]
  calc
    _ ≤ ‖(a - a') * c‖ + ‖a' * (c - c')‖ := norm_add_le _ _
    _ = ‖a - a'‖ * ‖c‖ + ‖a'‖ * ‖c - c'‖ := by rw [norm_mul, norm_mul]
    _ ≤ e * 2 + 1 * e := by gcongr
    _ = 3 * e := by ring

theorem indicator_norm_le (n : ℕ) : ‖((if n.Prime then 1 else 0 : ℕ) : ℂ)‖ ≤ 1 := by
  split_ifs <;> simp

theorem twin_budget {N b : ℕ} (hN : N + 2 ≤ 2 ^ b) (hb : 1 ≤ b) :
    (N : ℝ) * (3 * ((((N + 2 : ℕ) : ℝ)) ^ 2 * ((12 + 10 * (b : ℝ)) * componentTolerance b))) <
      1 / 2 := by
  rw [componentTolerance]
  set t : ℝ := (2 : ℝ) ^ b with ht
  have ht2 : (2 : ℝ) ≤ t := by
    rw [ht]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
  have hbt : (b : ℝ) + 1 ≤ t := by
    rw [ht]
    exact_mod_cast (Nat.lt_two_pow_self : b < 2 ^ b)
  have hNt : ((N + 2 : ℕ) : ℝ) ≤ t := by rw [ht]; exact_mod_cast hN
  have hN0 : (N : ℝ) ≤ t := by
    have : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ N + 2)
    linarith
  have htpos : 0 < t := by linarith
  have hb' : (12 + 10 * (b : ℝ)) ≤ 11 * t := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hlhs : (N : ℝ) * (3 * (((N + 2 : ℕ) : ℝ) ^ 2 * ((12 + 10 * (b : ℝ)) *
      (1 / (64 * t ^ 6))))) ≤ t * (3 * (t ^ 2 * (11 * t * (1 / (64 * t ^ 6))))) := by
    have h0 : (0 : ℝ) ≤ 1 / (64 * t ^ 6) := by positivity
    have hN' : (0 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by positivity
    gcongr
  have hval : t * (3 * (t ^ 2 * (11 * t * (1 / (64 * t ^ 6))))) = 33 / (64 * t ^ 2) := by
    field_simp
    ring
  have hfin : 33 / (64 * t ^ 2) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The approximate twin count rounds to the exact twin count. -/
theorem twin_round {N b : ℕ} {D : PrimeData} (hN : N + 2 ≤ 2 ^ b) (hb : 1 ≤ b)
    (hD : Certified b D) :
    ⌊(approximateTwin b D N).re + 1 / 2⌋ = (twinCount N : ℤ) := by
  apply PhaseApproximation.floor_add_half_eq
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (12 + 10 * (b : ℝ)) * componentTolerance b := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := hε ▸ mul_nonneg (by positivity) (componentTolerance_nonneg b)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (((N + 2 : ℕ) : ℝ)) ^ 2 * ε := ⟨_, rfl⟩
  have hE1 : E ≤ 1 := by
    rw [hE, hε, componentTolerance]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (2 : ℝ) ^ b := ⟨_, rfl⟩
    rw [← ht]
    have ht2 : (2 : ℝ) ≤ t := by
      rw [ht]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
    have hbt : (b : ℝ) + 1 ≤ t := by rw [ht]; exact_mod_cast (Nat.lt_two_pow_self : b < 2 ^ b)
    have hNt : ((N + 2 : ℕ) : ℝ) ≤ t := by rw [ht]; exact_mod_cast hN
    have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hb' : (12 + 10 * (b : ℝ)) ≤ 11 * t := by nlinarith
    have h0 : (0 : ℝ) ≤ 1 / (64 * t ^ 6) := by positivity
    have hN' : (0 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by positivity
    calc _ ≤ t ^ 2 * (11 * t * (1 / (64 * t ^ 6))) := by gcongr
      _ = 11 / (64 * t ^ 3) := by field_simp
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ht2 3]
  have hmono : ∀ m, m ≤ N + 2 →
      (m : ℝ) ^ 2 * ((12 + 10 * (b : ℝ)) * componentTolerance b) ≤ E := by
    intro m hm
    rw [hE, ← hε]
    have : (m : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast hm
    gcongr
  have hterm : ∀ n ∈ Icc 2 N,
      ‖approxIndicator b D n * approxIndicator b D (n+2) -
        ((if n.Prime then 1 else 0 : ℕ) : ℂ) * ((if (n+2).Prime then 1 else 0 : ℕ) : ℂ)‖ ≤
        3 * E := by
    intro n hn
    obtain ⟨hn2, hnN⟩ := mem_Icc.mp hn
    have hnb : n ≤ 2 ^ b := le_trans (by omega) hN
    have e1 := le_trans (approxIndicator_error hD hn2 hnb) (hmono n (by omega))
    have e2 := le_trans (approxIndicator_error hD (by omega : 2 ≤ n + 2)
      (le_trans (by omega) hN)) (hmono (n+2) (by omega))
    exact product_error _ _ _ _ E hE1 e1 e2 (indicator_norm_le n) (indicator_norm_le (n+2))
  have hsum : ‖approximateTwin b D N - (twinCount N : ℂ)‖ ≤ (N : ℝ) * (3 * E) := by
    rw [twinCount_eq_sum, approximateTwin, ← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum hterm).trans
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
    apply mul_le_mul_of_nonneg_right _ (by rw [hE]; positivity)
    exact_mod_cast (by omega : N + 1 - 2 ≤ N)
  have hr := (Complex.abs_re_le_norm (approximateTwin b D N - (twinCount N : ℂ))).trans hsum
  have hb' := twin_budget hN hb
  rw [← hε, ← hE] at hb'
  simp only [Complex.sub_re, Complex.natCast_re] at hr
  push_cast at hr ⊢
  linarith

/-! ## Exact integer reconstruction -/

/-- The Gaussian-integer numerator of one approximate indicator. -/
def indicatorNumerator (b : ℕ) (D : PrimeData) (n : ℕ) : GaussianIntPair :=
  -(∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ y ∈ unitsBelow d, productNumerator b D n d x y)

/-- The Gaussian-integer numerator of the approximate twin count. -/
def twinNumerator (b : ℕ) (D : PrimeData) (N : ℕ) : GaussianIntPair :=
  ∑ n ∈ Icc 2 N, multiply (indicatorNumerator b D n) (indicatorNumerator b D (n+2))

/-- Integer division by `2 s^8`, with `s = commonScale b`. -/
def twinResult (b : ℕ) (z : ℤ) : ℤ :=
  (2 * z + (commonScale b : ℤ) ^ 8) / (2 * (commonScale b : ℤ) ^ 8)

theorem approxIndicator_spec (b : ℕ) (D : PrimeData) {n : ℕ} (hn : 0 < n) :
    approxIndicator b D n = embed (indicatorNumerator b D n) / (commonScale b : ℂ) ^ 4 := by
  unfold approxIndicator localTerm indicatorNumerator
  rw [embed_neg, neg_div]
  congr 1
  simp_rw [embed_sum, sum_div]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro y _
  simp only [approxAmplitude]
  rw [logNumerator_spec, invLogNumerator_spec, phaseNumerator_spec b D n x hn,
    phaseNumerator_spec b D d y (Nat.pos_of_mem_divisors hd)]
  simp only [productNumerator, embed_multiply]
  ring

theorem approximateTwin_spec (b : ℕ) (D : PrimeData) (N : ℕ) :
    approximateTwin b D N = embed (twinNumerator b D N) / (commonScale b : ℂ) ^ 8 := by
  unfold approximateTwin twinNumerator
  rw [embed_sum, sum_div]
  apply sum_congr rfl
  intro n hn
  have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
  rw [approxIndicator_spec b D hn0, approxIndicator_spec b D (by omega : 0 < n + 2),
    embed_multiply]
  ring

theorem twinResult_eq_round (b : ℕ) (D : PrimeData) (N : ℕ) :
    twinResult b (twinNumerator b D N).1 = ⌊(approximateTwin b D N).re + 1 / 2⌋ := by
  rw [approximateTwin_spec]
  have he : (embed (twinNumerator b D N) / (commonScale b : ℂ) ^ 8).re =
      ((twinNumerator b D N).1 : ℝ) / (commonScale b ^ 8 : ℕ) := by
    rw [show (commonScale b : ℂ) ^ 8 = (((commonScale b ^ 8 : ℕ) : ℝ) : ℂ) by
      simp only [Nat.cast_pow, Complex.ofReal_pow, Complex.ofReal_natCast]]
    simp only [Complex.div_ofReal_re, embed, Complex.add_re, Complex.intCast_re,
      Complex.mul_re, Complex.intCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
  rw [he, rational_round _ _ (pow_pos (commonScale_pos b) 8)]
  simp only [twinResult, Nat.cast_pow]

/-- Pure integer division recovers the exact twin count from any certified table. -/
theorem twinResult_eq {N b : ℕ} {D : PrimeData} (hN : N + 2 ≤ 2 ^ b) (hb : 1 ≤ b)
    (hD : Certified b D) : twinResult b (twinNumerator b D N).1 = (twinCount N : ℤ) := by
  rw [twinResult_eq_round]
  exact twin_round hN hb hD

end TwinAlgorithm.TwinFormula
