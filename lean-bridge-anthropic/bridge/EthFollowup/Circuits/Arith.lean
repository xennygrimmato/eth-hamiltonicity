/-
# Arithmetic for E^NP ⊄ i.o.-SIZE(ε·n·√log n)

The threshold lemma that replaces `CircuitLowerBound.Time.exists_threshold` (Anthropic,
proof/consequences/CircuitLowerBound/Alg/Time.lean) for the rate engine. The circuit has
n ≤ ε(m+1)√log₂(m+2) gates, the formula has Nv ≤ 3n + A(m+1) + B variables and M ≤ 4Nv + 1 clauses,
the pad exponent of the engine is E ≤ G·3·M·r(M) with r(M) = 1/√log₂(M+2), and the padded host
costs q·(X + 2^E + 1)^q steps on an input of length X. With ε = 1/(4608(qG+1)) — fixed before A, B —
the cost is at most 2^⌊m/8⌋ from some m₀(A, B) on (`exists_threshold_rate`).

Case split on (M+2)² ≥ m+2: then log₂(M+2) ≥ log₂(m+2)/2 and the 12εn-term dominates; otherwise
M < √(m+2) and the exponent is o(m).
-/
import CircuitLowerBound.Alg.Time
import ClauseBoundStatement

set_option linter.unusedSectionVars false

namespace EthFollowup.Circuits

open CircuitLowerBound

/-- The constant ε of the lower bound, for the host constant q and the rate constant G. -/
noncomputable def epsOf (q G : ℕ) : ℝ := 1 / (4608 * ((q : ℝ) * G + 1))

theorem epsOf_pos (q G : ℕ) : 0 < epsOf q G := by unfold epsOf; positivity

theorem epsOf_le_one (q G : ℕ) : epsOf q G ≤ 1 := by
  unfold epsOf
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ (q : ℝ) * G := by positivity
  nlinarith

/-- log₂(m+2) ≤ m+1. -/
theorem logb_le_succ (m : ℕ) : Real.logb 2 ((m : ℝ) + 2) ≤ m + 1 := by
  have h : ((m : ℝ) + 2) ≤ (2 : ℝ) ^ ((m + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    have : m + 2 ≤ 2 ^ (m + 1) := Nat.lt_two_pow_self
    exact_mod_cast this
  have h2 := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) h
  rw [Real.logb_rpow two_pos (by norm_num)] at h2
  exact_mod_cast h2

theorem one_le_logb_succ2 (M : ℕ) : 1 ≤ Real.logb 2 ((M : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_one]
  have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  linarith

theorem n_le_sq {ε : ℝ} (_hε0 : 0 ≤ ε) (hε : ε ≤ 1) {m n : ℕ}
    (hn : (n : ℝ) ≤ ε * (m + 1) * Real.sqrt (Real.logb 2 ((m : ℝ) + 2))) : n ≤ (m + 1) ^ 2 := by
  have h1 : Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) ≤ m + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have := logb_le_succ m
    have : (1 : ℝ) ≤ m + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
    nlinarith
  have h2 : (n : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
    have hs := Real.sqrt_nonneg (Real.logb 2 ((m : ℝ) + 2))
    have hm : (0 : ℝ) ≤ m + 1 := by positivity
    calc (n : ℝ) ≤ ε * (m + 1) * Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) := hn
      _ ≤ 1 * (m + 1) * (m + 1) := by gcongr
      _ = _ := by ring
  exact_mod_cast h2

/-- The length of the input is polynomial in m. -/
theorem X_le {m n : ℕ} (hn : n ≤ (m + 1) ^ 2) :
    m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n))) + 2 ≤ 16 * (m + 2) ^ 4 := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (m + 2) ^ 2 := ⟨_, rfl⟩
  have h1 : n ≤ Y := hn.trans (by rw [hY]; exact Nat.pow_le_pow_left (by omega) 2)
  have h2 : m + 2 ≤ Y := by rw [hY]; nlinarith
  have h4 : (m + 2) ^ 4 = Y * Y := by rw [hY]; ring
  have h5 : n * (4 + 2 * (m + n)) ≤ Y * (4 + 4 * Y) := Nat.mul_le_mul h1 (by omega)
  rw [h4]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The exponent: q·G·3·M·r(M) ≤ (m+1)/32 from some m₀ on, with ε = `epsOf q G`. -/
theorem exponent_le (q G A B : ℕ) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ n M : ℕ,
    (n : ℝ) ≤ epsOf q G * (m + 1) * Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) →
    M ≤ 12 * n + 4 * A * (m + 1) + 4 * B + 1 →
    (q : ℝ) * (G * (3 * M * SatM.rPow (1 / 2) M)) ≤ ((m : ℝ) + 1) / 32 := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 384 * (q * G) * (4 * A + 4 * B + 1) + 1 := ⟨_, rfl⟩
  refine ⟨2 ^ (T ^ 2) + (96 * (q * G)) ^ 2 + 32, fun m hm n M hn hM => ?_⟩
  have hqG : (0 : ℝ) ≤ (q : ℝ) * G := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.logb 2 ((M : ℝ) + 2) := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := hℓ ▸ one_le_logb_succ2 M
  have hr : SatM.rPow (1 / 2) M = 1 / Real.sqrt ℓ := by
    unfold SatM.rPow
    rw [Real.sqrt_eq_rpow, ← hℓ]
  rw [hr]
  have hsℓ : 1 ≤ Real.sqrt ℓ := Real.one_le_sqrt.2 hℓ1
  have hsℓ0 : 0 < Real.sqrt ℓ := by linarith
  rcases Nat.lt_or_ge ((M + 2) ^ 2) (m + 2) with hsm | hsm
  · -- few clauses: the exponent is at most 3qG·M < m/32
    have h1 : (q : ℝ) * (G * (3 * M * (1 / Real.sqrt ℓ))) ≤ 3 * ((q : ℝ) * G) * M := by
      have : 3 * M * (1 / Real.sqrt ℓ) ≤ 3 * (M : ℝ) := by
        rw [mul_one_div, div_le_iff₀ hsℓ0]; nlinarith
      calc (q : ℝ) * (G * (3 * M * (1 / Real.sqrt ℓ))) = ((q : ℝ) * G) * (3 * M * (1 / Real.sqrt ℓ)) := by ring
        _ ≤ ((q : ℝ) * G) * (3 * M) := mul_le_mul_of_nonneg_left this hqG
        _ = _ := by ring
    have h2 : 96 * (q * G) * M ≤ m + 1 := by
      rcases Nat.lt_or_ge (M + 2) (96 * (q * G)) with h | h
      · have : 96 * (q * G) * M ≤ (96 * (q * G)) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (by omega)
        have h2T : 0 < 2 ^ (T ^ 2) := by positivity
        calc 96 * (q * G) * M ≤ (96 * (q * G)) ^ 2 := this
          _ ≤ m + 1 := by omega
      · have : 96 * (q * G) * M ≤ (M + 2) * (M + 2) := Nat.mul_le_mul h (by omega)
        rw [sq] at hsm
        omega
    have h3 : (96 : ℝ) * ((q : ℝ) * G) * M ≤ m + 1 := by exact_mod_cast h2
    linarith
  · -- many clauses: log₂(M+2) ≥ log₂(m+2)/2
    obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 ((m : ℝ) + 2) := ⟨_, rfl⟩
    rw [← hL] at hn
    have hTL : ((T : ℝ)) ^ 2 ≤ L := by
      have h1 : (2 : ℝ) ^ (((T ^ 2 : ℕ)) : ℝ) ≤ (m : ℝ) + 2 := by
        rw [Real.rpow_natCast]
        have : 2 ^ (T ^ 2) ≤ m + 2 := by omega
        exact_mod_cast this
      have h2 := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) h1
      rw [Real.logb_rpow two_pos (by norm_num)] at h2
      rw [hL]
      exact_mod_cast h2
    have hT1 : (1 : ℝ) ≤ T := by
      have : 1 ≤ T := by omega
      exact_mod_cast this
    have hL1 : 1 ≤ L := by nlinarith
    have hsL : (T : ℝ) ≤ Real.sqrt L := Real.le_sqrt_of_sq_le hTL
    have hsL0 : 0 < Real.sqrt L := by linarith
    have hℓL : L ≤ 2 * ℓ := by
      have h1 : ((m : ℝ) + 2) ≤ ((M : ℝ) + 2) ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        have : m + 2 ≤ (M + 2) ^ 2 := hsm
        exact_mod_cast this
      have h2 := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) h1
      rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity)] at h2
      rw [hL, hℓ]; linarith
    have hsq : Real.sqrt L ≤ 2 * Real.sqrt ℓ := by
      rw [Real.sqrt_le_left (by positivity)]
      have := Real.sq_sqrt (show (0 : ℝ) ≤ ℓ by linarith)
      nlinarith
    -- the bound on M
    have hMr : (M : ℝ) ≤ 12 * (epsOf q G * (m + 1) * Real.sqrt L) + (4 * A + 4 * B + 1) * ((m : ℝ) + 1) := by
      have h1 : (M : ℝ) ≤ 12 * n + 4 * A * (m + 1) + 4 * B + 1 := by exact_mod_cast hM
      have h2 : (4 * (B : ℝ) + 1) ≤ (4 * B + 1) * ((m : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) B]
      nlinarith
    have hε : 72 * ((q : ℝ) * G) * epsOf q G ≤ 1 / 64 := by
      unfold epsOf
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hR : 6 * ((q : ℝ) * G) * ((4 * A + 4 * B + 1) * ((m : ℝ) + 1)) ≤ ((m : ℝ) + 1) / 64 * Real.sqrt L := by
      have h1 : 384 * ((q : ℝ) * G) * (4 * A + 4 * B + 1) ≤ Real.sqrt L := by
        have : (T : ℝ) = 384 * ((q : ℝ) * G) * (4 * A + 4 * B + 1) + 1 := by rw [hT]; push_cast; ring
        linarith
      have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      nlinarith
    -- assemble: qG·3M/√ℓ ≤ 6qG·M/√L
    have h1 : (q : ℝ) * (G * (3 * M * (1 / Real.sqrt ℓ))) ≤ 6 * ((q : ℝ) * G) * M / Real.sqrt L := by
      rw [le_div_iff₀ hsL0]
      have e : (q : ℝ) * (G * (3 * M * (1 / Real.sqrt ℓ))) * Real.sqrt L = 3 * ((q : ℝ) * G) * M * (Real.sqrt L / Real.sqrt ℓ) := by
        field_simp
      rw [e]
      have : Real.sqrt L / Real.sqrt ℓ ≤ 2 := by rw [div_le_iff₀ hsℓ0]; linarith
      have h3 : (0 : ℝ) ≤ 3 * ((q : ℝ) * G) * M := by positivity
      nlinarith
    have h2 : 6 * ((q : ℝ) * G) * M / Real.sqrt L ≤ ((m : ℝ) + 1) / 32 := by
      rw [div_le_iff₀ hsL0]
      have e1 : 6 * ((q : ℝ) * G) * (12 * (epsOf q G * (m + 1) * Real.sqrt L)) = 72 * ((q : ℝ) * G) * epsOf q G * ((m + 1) * Real.sqrt L) := by ring
      have h4 : 6 * ((q : ℝ) * G) * M ≤ 6 * ((q : ℝ) * G) * (12 * (epsOf q G * (m + 1) * Real.sqrt L) + (4 * A + 4 * B + 1) * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hMr (by positivity)
      have h5 : 72 * ((q : ℝ) * G) * epsOf q G * ((m + 1) * Real.sqrt L) ≤ 1 / 64 * ((m + 1) * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right hε (by positivity)
      calc 6 * ((q : ℝ) * G) * M ≤ 6 * ((q : ℝ) * G) * (12 * (epsOf q G * (m + 1) * Real.sqrt L) + (4 * A + 4 * B + 1) * ((m : ℝ) + 1)) := h4
        _ = 72 * ((q : ℝ) * G) * epsOf q G * ((m + 1) * Real.sqrt L) + 6 * ((q : ℝ) * G) * ((4 * A + 4 * B + 1) * ((m : ℝ) + 1)) := by ring
        _ ≤ 1 / 64 * ((m + 1) * Real.sqrt L) + ((m : ℝ) + 1) / 64 * Real.sqrt L := add_le_add h5 hR
        _ = ((m : ℝ) + 1) / 32 * Real.sqrt L := by ring
    linarith

/-- The threshold for the rate engine: from some m₀ on, the host's cost is at most 2^⌊m/8⌋. -/
theorem exists_threshold_rate (q G A B : ℕ) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ n Nv M E : ℕ,
    (n : ℝ) ≤ epsOf q G * (m + 1) * Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) →
    Nv ≤ 3 * n + A * (m + 1) + B → M ≤ 4 * Nv + 1 →
    (E : ℝ) ≤ G * (3 * M * SatM.rPow (1 / 2) M) →
    q * ((m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + 2 ^ E + 1) ^ q ≤ 2 ^ (m / 8) := by
  obtain ⟨m₁, hm₁⟩ := exponent_le q G A B
  obtain ⟨C₁, hC₁⟩ := Groundwork.exists_pow_le (4 * q) (ε := 1 / 32) (by norm_num)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 * (q * 16 ^ q * C₁) := ⟨_, rfl⟩
  refine ⟨m₁ + 16 * (K + 1), fun m hm n Nv M E hn hNv hM hE => ?_⟩
  have hn2 := n_le_sq (epsOf_pos q G).le (epsOf_le_one q G) hn
  have hX := X_le hn2
  obtain ⟨X, hXd⟩ : ∃ X, X = m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n))) := ⟨_, rfl⟩
  rw [← hXd] at hX ⊢
  have hqE : (q : ℝ) * E ≤ ((m : ℝ) + 1) / 32 := by
    have e4 : 4 * A * (m + 1) = 4 * (A * (m + 1)) := by ring
    have := hm₁ m (by omega) n M hn (by omega)
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  -- X + 2^E + 1 ≤ (X+2)·2^E
  have h1 : X + 2 ^ E + 1 ≤ (X + 2) * 2 ^ E := by
    have : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    nlinarith
  have h2 : q * (X + 2 ^ E + 1) ^ q ≤ q * (16 * (m + 2) ^ 4) ^ q * 2 ^ (q * E) := by
    calc q * (X + 2 ^ E + 1) ^ q ≤ q * ((X + 2) * 2 ^ E) ^ q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = q * (X + 2) ^ q * 2 ^ (q * E) := by rw [mul_pow, ← pow_mul, Nat.mul_comm E q, mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _))
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (2 : ℝ) ^ ((1 / 32 : ℝ) * m) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; positivity
  have h3 : ((2 ^ (q * E) : ℕ) : ℝ) ≤ 2 * p := by
    have e : ((2 ^ (q * E) : ℕ) : ℝ) = (2 : ℝ) ^ (((q * E : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    rw [e]
    have h4 : (((q * E : ℕ)) : ℝ) ≤ 1 + (1 / 32 : ℝ) * m := by push_cast; linarith
    calc (2 : ℝ) ^ (((q * E : ℕ)) : ℝ) ≤ (2 : ℝ) ^ (1 + (1 / 32 : ℝ) * m) := Real.rpow_le_rpow_of_exponent_le one_le_two h4
      _ = 2 * p := by rw [Real.rpow_add two_pos, Real.rpow_one, hp]
  have h5 : (((q * (16 * (m + 2) ^ 4) ^ q : ℕ)) : ℝ) ≤ ((q * 16 ^ q * C₁ : ℕ) : ℝ) * p := by
    have e : (((q * (16 * (m + 2) ^ 4) ^ q : ℕ)) : ℝ) = (q * 16 ^ q : ℝ) * (((m : ℝ) + 2) ^ (4 * q)) := by
      push_cast; rw [mul_pow, ← pow_mul]; ring
    rw [e]
    have := hC₁ m
    rw [← hp] at this
    push_cast
    have h6 : (0 : ℝ) ≤ q * 16 ^ q := by positivity
    calc (q * 16 ^ q : ℝ) * (((m : ℝ) + 2) ^ (4 * q)) ≤ (q * 16 ^ q : ℝ) * (C₁ * p) := mul_le_mul_of_nonneg_left this h6
      _ = _ := by ring
  have h7 : ((q * (X + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤ ((2 ^ (m / 8) : ℕ) : ℝ) := by
    calc ((q * (X + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤ (((q * (16 * (m + 2) ^ 4) ^ q * 2 ^ (q * E)) : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (((q * (16 * (m + 2) ^ 4) ^ q : ℕ)) : ℝ) * ((2 ^ (q * E) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((q * 16 ^ q * C₁ : ℕ) : ℝ) * p) * (2 * p) := by gcongr
      _ = (K : ℝ) * (p * p) := by rw [hK]; push_cast; ring
      _ ≤ (2 : ℝ) ^ (((m / 8 : ℕ) : ℝ)) := by rw [hp]; exact Time.final_le K (by omega)
      _ = _ := by rw [Real.rpow_natCast]; push_cast; rfl
  exact_mod_cast h7

end EthFollowup.Circuits
