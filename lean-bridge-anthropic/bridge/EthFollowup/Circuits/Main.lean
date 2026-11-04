/-
# E^NP ⊄ i.o.-SIZE(ε·n·√log n), on top of Anthropic's development

`enp_not_size_n_sqrt_log`: there are ε > 0 and a language L₀ in E^NP (Anthropic's `ENP.InENP`, the
class of their Section 7 result `ENP.CorCircuits`) such that for every N there is n ≥ N at which no
circuit with at most ε·n·√(log₂ n) gates (Anthropic's circuits: any of the 16 binary gates; size =
number of gates) decides L₀ on the words of length n. L₀ is Anthropic's `CircuitLowerBound.L0`.

Route (research/circuit-lower-bounds.md, referee report issues 1–4):
* `stAlgS_rate`: the interface statement of the algorithm (`StAlgS`, LowerBound.lean) for the size
  function s(m) = ⌊ε(m+1)√log₂(m+2)⌋, with the machine of `exists_tm_padded` on the padded function
  `aX`/`eX` (Engine.lean) built from Anthropic's rate engine `Tied.TopM` (Theorem A(c) at ρ = 1/√2,
  proved by Anthropic), Anthropic's formula F with the clause bound (FormCount.lean), and the
  threshold `exists_threshold_rate` (Arith.lean). ε = 1/(4608(qG+1)) with q the host constant of
  the padded machine and G the rate constant of `TopM`; both are fixed before the table e.
* `no_circuits_io` (LowerBound.lean): Anthropic's chain argument, infinitely often.
* membership: Anthropic's `CircuitLowerBound.stENP`.
-/
import EthFollowup.Circuits.LowerBound
import EthFollowup.Circuits.Engine
import EthFollowup.Circuits.Arith

set_option linter.unusedSectionVars false

namespace EthFollowup.Circuits

open ENP Groundwork Turing CircuitLowerBound PaddedDescent PaddedDescent.F ClauseBound.Alg

/-- The size function of the module, with the constant ε. -/
noncomputable def sizeFn (ε : ℝ) (m : ℕ) : ℕ := ⌊ε * ((m : ℝ) + 1) * Real.sqrt (Real.logb 2 ((m : ℝ) + 2))⌋₊

/-- The interface statement of the algorithm for circuits of size ε(m+1)√log₂(m+2). -/
theorem stAlgS_rate : ∃ ε : ℝ, 0 < ε ∧ StAlgS (sizeFn ε) := by
  obtain ⟨Idx, _, S, pick, hT⟩ := exists_topM
  obtain ⟨G, hG⟩ := hT.rate
  obtain ⟨a₀, g, F, hFp, hF, hcount⟩ := stFormCount
  obtain ⟨fb, hbp, hb⟩ := stFlip
  have hb' : Alg.FlipOK fb := hb
  have he := eX_polyT S pick F fb hT stCertSched hFp hbp
  have ha := aX_polyT S pick F fb hT stCertSched hFp hbp
  obtain ⟨N, q, hfin, hN⟩ := exists_tm_padded he ha
  refine ⟨epsOf q G, epsOf_pos q G, N, hfin, ?_, fun e => ?_⟩
  · rintro m T ⟨y, ⟨ev⟩⟩
    obtain ⟨ev'⟩ := hN (unary m ++ y)
    have h5 := Alg.outputs_unique ev ev'
    have h6 : aX S pick F fb (unary m ++ y, pad (eX S pick F fb (unary m ++ y))) = true := by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h5
      exact (N.outputAlphabet.symm.injective h5).symm
    have h7 := Alg.sat_Phi_of_pre hF hb' _ ((aX_spec S pick F fb hT hF _).1 h6)
    rwa [Parse.ones_unary_append] at h7
  · obtain ⟨m₀, hm₀⟩ := exists_threshold_rate q G a₀ (g e)
    refine ⟨max m₀ 1, fun m hm hce hpos C hCl hC => ?_⟩
    obtain ⟨y, hy, hns, hNv⟩ := Alg.exists_guess hF hb' stNorm (le_of_max_le_right hm) hpos C hC
    rw [hce] at hNv
    obtain ⟨x, hx⟩ : ∃ x, x = unary m ++ y := ⟨_, rfl⟩
    rw [← hx] at hns hNv
    have hsh := Alg.shaped_pre (fb := fb) hF x
    have hne : (Alg.pre F fb x).2 ≠ [] := fun h => hns (h ▸ Alg.sat_nil)
    have haX : aX S pick F fb (x, pad (eX S pick F fb x)) = true := (aX_spec S pick F fb hT hF x).2 hns
    obtain ⟨ev⟩ := hN x
    rw [haX] at ev
    -- the exponent
    have hE : (eX S pick F fb x : ℝ) ≤ G * (3 * (Alg.pre F fb x).2.length * SatM.rPow (1 / 2) (Alg.pre F fb x).2.length) := by
      have : eX S pick F fb x = eM S pick (fmlCode (Alg.pre F fb x).2) := by
        unfold eX
        have h0 : (Alg.pre F fb x).2.isEmpty = false := by
          cases h : (Alg.pre F fb x).2 with
          | nil => exact absurd h hne
          | cons _ _ => rfl
        rw [h0]; rfl
      rw [this]
      exact eM_le S pick hG hsh hne
    have hn : (C.length : ℝ) ≤ epsOf q G * (m + 1) * Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) := by
      have h1 : C.length ≤ sizeFn (epsOf q G) m := hCl
      unfold sizeFn at h1
      have h2 : (0 : ℝ) ≤ epsOf q G * ((m : ℝ) + 1) * Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) := by
        have := (epsOf_pos q G).le
        positivity
      exact (Nat.le_floor_iff h2).1 h1
    have h8 := hm₀ m (le_of_max_le_left hm) C.length _ _ _ hn hNv (pre_count F fb hcount x) hE
    have h9 : x.length = m + 1 + ((m + C.length) + 1 + C.length * (4 + 2 * (m + C.length))) := by
      rw [hx, List.length_append, hy]
      simp [unary]
    rw [← h9] at h8
    subst hx
    exact ⟨y, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans h8⟩⟩⟩

/-- The form with ε(n+1)√log₂(n+2). -/
theorem enp_not_size_n_sqrt_log_shifted : ∃ (L : Lang) (ε : ℝ), 0 < ε ∧ InENP L ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬DecidedAt L ⌊ε * ((n : ℝ) + 1) * Real.sqrt (Real.logb 2 ((n : ℝ) + 2))⌋₊ n := by
  obtain ⟨ε, hε, hA⟩ := stAlgS_rate
  exact ⟨L0, ε, hε, stENP, no_circuits_io stTab stCode stChain stVars stGreedy hA⟩

theorem decidedAt_mono {L : Lang} {s s' n : ℕ} (h : DecidedAt L s n) (hs : s ≤ s') : DecidedAt L s' n := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC.trans hs, h⟩

/-- **E^NP ⊄ i.o.-SIZE(ε·n·√log n).** Some language in E^NP (Anthropic's `InENP`) has, for some
ε > 0, at infinitely many lengths n no circuit with at most ε·n·√(log₂ n) gates over the full binary
basis. -/
theorem enp_not_size_n_sqrt_log : ∃ (L : Lang) (ε : ℝ), 0 < ε ∧ InENP L ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬DecidedAt L ⌊ε * n * Real.sqrt (Real.logb 2 n)⌋₊ n := by
  obtain ⟨L, ε, hε, hL, h⟩ := enp_not_size_n_sqrt_log_shifted
  refine ⟨L, ε, hε, hL, fun N => ?_⟩
  obtain ⟨n, hn, hd⟩ := h N
  refine ⟨n, hn, fun hd' => hd (decidedAt_mono hd' (Nat.floor_mono ?_))⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    have := Real.sqrt_nonneg (Real.logb 2 ((0 : ℝ) + 2))
    positivity
  · have h1 : Real.logb 2 n ≤ Real.logb 2 ((n : ℝ) + 2) :=
      Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast h0) (by linarith)
    have h2 := Real.sqrt_le_sqrt h1
    have h3 := Real.sqrt_nonneg (Real.logb 2 n)
    have h4 : ε * (n : ℝ) ≤ ε * ((n : ℝ) + 1) := by nlinarith
    exact mul_le_mul h4 h2 h3 (by positivity)

/-- The same as «not in SIZE»: L₀ is not decided by circuits of size ⌊ε·n·√log₂ n⌋ for all n. -/
theorem enp_not_hasCircuits_n_sqrt_log : ∃ (L : Lang) (ε : ℝ), 0 < ε ∧ InENP L ∧
    ¬HasCircuits L fun n => ⌊ε * n * Real.sqrt (Real.logb 2 n)⌋₊ := by
  obtain ⟨L, ε, hε, hL, h⟩ := enp_not_size_n_sqrt_log
  refine ⟨L, ε, hε, hL, fun hc => ?_⟩
  obtain ⟨n, -, hd⟩ := h 0
  exact hd (hc n)

end EthFollowup.Circuits
