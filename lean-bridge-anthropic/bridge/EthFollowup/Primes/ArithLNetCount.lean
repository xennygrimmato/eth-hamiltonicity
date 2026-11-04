/-
# ArithL, module 3d: the geometric cost bounds

* generic sums: `sum_div_c`, `spread_sum`, `spread_le`, `sum_div_pow_le`, `sum_fiber_mul`;
* shapes: `kl n k ≤ 2ℓ/2^k + 1`, `kL1 n k ≤ L1/2^{k/2} + 2`, hence `Σ_{k<K} kl ≤ 4ℓ + K`,
  `Σ_{k<K} kL1 ≤ 4 L1 + 2K`; `(ν + 3)·Wa ≤ 2^12 (n+2)` and `≤ 2 dg`;
* **`arithSys_U_le`**: `U ≤ 2^19 · c · (n + 2)` and **`arithSys_is`**: Definition 2 with
  `P = PL n c g := 2^22 · c · ((n+2)/g + dg n)`, `B = 1`, for well-formed `L` with `Spread c` and
  `nL ≤ ν n + 3` (`c ≥ 1`).

Standard axioms only.
-/
import EthFollowup.Primes.ArithLNetDeg
import EthFollowup.Primes.ArithLNetParsimony

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.ExactHC EthFollowup.Factoring EthFollowup.ModP

/-! ## Generic sums -/

theorem sum_div_c (f : ℕ → ℕ) {c : ℕ} (hc : 1 ≤ c) (K : ℕ) :
    ∑ i ∈ range (c * K), f (i / c) = c * ∑ k ∈ range K, f k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    rw [sum_congr rfl fun i hi => by
      rw [show (c * K + i) / c = K by
        rw [add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (mem_range.1 hi), zero_add]],
      sum_const, card_range, smul_eq_mul]

theorem spread_le {N c K : ℕ} (hc : 1 ≤ c) {lev : ℕ → ℕ} (hs : ∀ i < N, i / c ≤ lev i)
    (hK : ∀ i < N, lev i < K) : N ≤ c * K := by
  by_contra h
  have h1 := hs (c * K) (by omega)
  have h2 := hK (c * K) (by omega)
  rw [Nat.mul_div_cancel_left _ (by omega)] at h1
  omega

theorem spread_sum {f : ℕ → ℕ} (hf : Antitone f) {N c K : ℕ} (hc : 1 ≤ c) (lev : ℕ → ℕ)
    (hs : ∀ i < N, i / c ≤ lev i) (hK : ∀ i < N, lev i < K) :
    ∑ i ∈ range N, f (lev i) ≤ c * ∑ k ∈ range K, f k :=
  calc ∑ i ∈ range N, f (lev i) ≤ ∑ i ∈ range N, f (i / c) :=
        sum_le_sum fun i hi => hf (hs i (mem_range.1 hi))
    _ ≤ ∑ i ∈ range (c * K), f (i / c) := sum_le_sum_of_subset (range_mono (spread_le hc hs hK))
    _ = c * ∑ k ∈ range K, f k := sum_div_c f hc K

theorem sum_div_pow_le : ∀ (X K : ℕ), ∑ k ∈ range K, X / 2 ^ k ≤ 2 * X
  | X, 0 => by simp
  | X, K + 1 => by
    rw [sum_range_succ']
    have h := sum_div_pow_le (X / 2) K
    have e : ∀ k, X / 2 ^ (k + 1) = X / 2 / 2 ^ k := fun k => by rw [pow_succ', Nat.div_div_eq_div_mul]
    simp only [e, pow_zero, Nat.div_one]
    have := Nat.mul_div_le X 2
    omega

theorem sum_fiber_mul {N K : ℕ} (lev : ℕ → ℕ) (f : ℕ → ℕ) (h : ∀ i < N, lev i < K) :
    ∑ k ∈ range K, f k * #((range N).filter fun i => lev i = k) = ∑ i ∈ range N, f (lev i) := by
  rw [← sum_fiberwise_of_maps_to (s := range N) (t := range K) (g := lev)
    (fun i hi => mem_range.2 (h i (mem_range.1 hi)))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, smul_eq_mul, mul_comm]

/-! ## Geometric shapes -/

section Geo
variable (n : ℕ)

theorem kl_eq (k : ℕ) : kl n k = 2 ^ (2 * (m n - sh n k - 1)) := by
  unfold kl kl1; rw [← pow_add]; congr 1; ring

theorem ℓ_eq : ℓ n = 2 ^ (2 * (m n - 1)) := by
  unfold ℓ; rw [ℓ2_eq_ℓ1]; unfold ℓ1; rw [← pow_add]; congr 1; ring

theorem kl_le_geo (k : ℕ) : kl n k ≤ 2 * ℓ n / 2 ^ k + 1 := by
  by_cases h : k / 2 ≤ m n - 1
  · have hs : sh n k = k / 2 := min_eq_left h
    have : kl n k * 2 ^ k ≤ 2 * ℓ n := by
      rw [kl_eq, ℓ_eq, hs, ← pow_add, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (Nat.le_div_iff_mul_le (by positivity)).2 this
    omega
  · have hs : sh n k = m n - 1 := min_eq_right (by omega)
    rw [kl_eq, hs, show m n - (m n - 1) - 1 = 0 by omega]; simp

theorem kL1_le_geo (k : ℕ) : kL1 n k ≤ L1 n / 2 ^ (k / 2) + 2 := by
  by_cases h : k / 2 ≤ m n - 1
  · have hs : sh n k = k / 2 := min_eq_left h
    have : kL1 n k * 2 ^ (k / 2) ≤ L1 n := by
      unfold kL1 L1; rw [hs, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (Nat.le_div_iff_mul_le (by positivity)).2 this
    omega
  · have hs : sh n k = m n - 1 := min_eq_right (by omega)
    have := one_le_m n
    unfold kL1; rw [hs, show m n - (m n - 1) = 1 by omega, pow_one]; exact Nat.le_add_left _ _

theorem sum_kl_le (K : ℕ) : ∑ k ∈ range K, kl n k ≤ 4 * ℓ n + K := by
  calc ∑ k ∈ range K, kl n k ≤ ∑ k ∈ range K, (2 * ℓ n / 2 ^ k + 1) := sum_le_sum fun k _ => kl_le_geo n k
    _ = ∑ k ∈ range K, 2 * ℓ n / 2 ^ k + K := by rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
    _ ≤ 4 * ℓ n + K := by have := sum_div_pow_le (2 * ℓ n) K; omega

theorem sum_kL1_le (K : ℕ) : ∑ k ∈ range K, kL1 n k ≤ 4 * L1 n + 2 * K := by
  have h1 : ∑ k ∈ range K, L1 n / 2 ^ (k / 2) ≤ 4 * L1 n :=
    calc ∑ k ∈ range K, L1 n / 2 ^ (k / 2) ≤ ∑ k ∈ range (2 * K), L1 n / 2 ^ (k / 2) :=
          sum_le_sum_of_subset (range_mono (by omega))
      _ = 2 * ∑ j ∈ range K, L1 n / 2 ^ j := sum_div_c (fun j => L1 n / 2 ^ j) (by norm_num) K
      _ ≤ 4 * L1 n := by have := sum_div_pow_le (L1 n) K; omega
  calc ∑ k ∈ range K, kL1 n k ≤ ∑ k ∈ range K, (L1 n / 2 ^ (k / 2) + 2) := sum_le_sum fun k _ => kL1_le_geo n k
    _ = ∑ k ∈ range K, L1 n / 2 ^ (k / 2) + 2 * K := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_comm]
    _ ≤ 4 * L1 n + 2 * K := by omega

theorem kl_antitone : Antitone (kl n) := fun _ _ h => kl_anti n h
theorem kL1_antitone : Antitone (kL1 n) := fun _ _ h => by
  rw [kL1_eq, kL1_eq]; have := kl1_anti n h; omega

theorem four_mul_add_le : ∀ a : ℕ, 4 * a + 6 ≤ 16 * 2 ^ a
  | 0 => by norm_num
  | a + 1 => by have := four_mul_add_le a; rw [pow_succ]; omega

theorem ν_Wa_le : (ν n + 3) * Wa n ≤ 2 ^ 12 * (n + 2) ∧ (ν n + 3) * Wa n ≤ 2 * dg n := by
  have hW : Wa n ≤ 2 ^ (ν n / 2 + 8) := by
    have : 8 ≤ 2 ^ (ν n / 2 + 7) := by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ 2 ^ (ν n / 2 + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 ^ (ν n / 2 + 8) = 2 * 2 ^ (ν n / 2 + 7) := by rw [pow_succ]; ring
    unfold Wa J; omega
  have hν : ν n + 3 ≤ 16 * 2 ^ (ν n / 4) := by have := four_mul_add_le (ν n / 4); omega
  have hp : (ν n + 3) * Wa n ≤ 2 ^ (ν n / 4 + (ν n / 2 + 12)) := by
    calc (ν n + 3) * Wa n ≤ 16 * 2 ^ (ν n / 4) * 2 ^ (ν n / 2 + 8) := Nat.mul_le_mul hν hW
      _ = 2 ^ (ν n / 4 + (ν n / 2 + 12)) := by
          rw [pow_add 2 (ν n / 4), pow_add 2 (ν n / 2) 12, pow_add 2 (ν n / 2) 8]; ring
  refine ⟨hp.trans ?_, hp.trans ?_⟩
  · calc 2 ^ (ν n / 4 + (ν n / 2 + 12)) ≤ 2 ^ (ν n + 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ 12 * 2 ^ ν n := by rw [pow_add]; ring
      _ ≤ 2 ^ 12 * (n + 2) := Nat.mul_le_mul_left _ (two_pow_ν_le n)
  · calc 2 ^ (ν n / 4 + (ν n / 2 + 12)) ≤ 2 ^ (3 * ν n / 4 + 11 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * dg n := by unfold dg; rw [pow_succ]; ring

theorem L1_Wa_le : L1 n * Wa n ≤ 2 * dg n := by have := L1_mul_Wa_le n; omega

end Geo

/-! ## Layout sums -/

theorem LB.sum_fidx : ∀ (nO : List ℕ) (F : ℕ → ℕ),
    ∑ st ∈ range nO.sum, F st = ∑ κ ∈ range nO.length, ∑ o ∈ range (nO.getD κ 0), F (LB.fidx nO κ o)
  | [], _ => by simp
  | c :: cs, F => by
    have ih := LB.sum_fidx cs (fun st => F (c + st))
    rw [List.sum_cons, sum_range_add, ih, List.length_cons, sum_range_succ']
    simp only [LB.fidx, Blocks.off_cons_succ, Blocks.off_zero, List.getD_cons_zero, List.getD_cons_succ,
      zero_add, add_assoc]
    exact add_comm _ _

theorem total_lay (nO : List ℕ) (bx : ℕ → ℕ → List ℕ) :
    Blocks.total (LB.lay nO bx) = ∑ κ ∈ range nO.length, ∑ o ∈ range (nO.getD κ 0), (bx κ o).prod := by
  induction nO generalizing bx with
  | nil => rfl
  | cons c cs ih =>
    simp only [LB.lay, Blocks.total, Blocks.sizes, List.map_append, List.sum_append] at ih ⊢
    rw [ih, List.length_cons, sum_range_succ', add_comm]
    congr 1
    rw [List.map_map, ← MP.sum_range_list]
    rfl

/-! ## The stage sum and the wire count in terms of the description -/

section Bounds

variable {n : ℕ} {L : LDesc}

theorem stSz_fidx {κ o : ℕ} (h : o < (vObj L).getD κ 0) :
    stSz n L (LB.fidx (vObj L) κ o) = (vBox n L κ o).prod := by
  unfold stSz
  rw [Blocks.sizes_getD (by rw [vLay, LB.length_lay]; exact LB.fidx_lt h), vLay, LB.getD_lay h]

theorem degSt_fidx {κ o : ℕ} (h : o < (vObj L).getD κ 0) :
    degSt n L (LB.fidx (vObj L) κ o) = degS n L κ o := by
  unfold degSt; rw [LB.fam_fidx h, LB.loc_fidx h]

theorem aBSum_eq (g : ℕ) : aBSum n L g =
    ∑ κ ∈ range 7, ∑ o ∈ range ((vObj L).getD κ 0), ((vBox n L κ o).prod + g) * degS n L κ o := by
  rw [aBSum, LB.sum_fidx]
  exact sum_congr rfl fun κ _ => sum_congr rfl fun o ho => by
    rw [stSz_fidx (mem_range.1 ho), degSt_fidx (mem_range.1 ho)]

theorem numAW_eq : numAW n L = ∑ κ ∈ range 9, ∑ o ∈ range ((wObj L).getD κ 0), (wBox n L κ o).prod := by
  rw [numAW, wLay, total_lay]; rfl

/-- The description sums `Σ_obj f(level)`. -/
def SV (L : LDesc) (f : ℕ → ℕ) : ℕ := ∑ v ∈ range L.D.nV, f (L.lv v)
def SP (L : LDesc) (f : ℕ → ℕ) : ℕ := ∑ p ∈ range L.D.nP, f (L.lp p)
def SC (L : LDesc) (f : ℕ → ℕ) : ℕ := ∑ c ∈ range L.D.nC, f (L.lc c)
def SQ (L : LDesc) (f : ℕ → ℕ) : ℕ := ∑ q ∈ range L.D.nQ, f (L.lq q)

theorem SV_one : SV L (fun _ => 1) = L.D.nV := by simp [SV]
theorem SP_one : SP L (fun _ => 1) = L.D.nP := by simp [SP]
theorem SC_one : SC L (fun _ => 1) = L.D.nC := by simp [SC]
theorem SQ_one : SQ L (fun _ => 1) = L.D.nQ := by simp [SQ]

theorem oLev_ge (hL : L.WF n) {p : ℕ} (hp : p < L.D.nP) (σ : ℕ) : L.lp p ≤ L.oLev p σ := by
  have h := opnd_OK hL hp σ
  unfold LDesc.oLev
  split
  · rename_i w hw; rw [hw] at h; exact h.2
  · exact le_rfl

theorem oLev_lt (p σ : ℕ) : L.oLev p σ < L.nL := by
  unfold LDesc.oLev; split
  · exact L.lv_lt_nL _
  · exact L.lp_lt_nL _

theorem card_P_le (k : ℕ) : cntP L k ≤ #((range L.D.nP).filter fun p => L.lp p = k) +
    #((range L.D.nP).filter fun p => L.oLev p 0 = k) + #((range L.D.nP).filter fun p => L.oLev p 1 = k) := by
  unfold cntP
  rw [filter_or, filter_or]
  exact (card_union_le _ _).trans ((Nat.add_le_add_left (card_union_le _ _) _).trans
    (le_of_eq (add_assoc _ _ _).symm))

/-- The cells' part of the stage sum. -/
theorem cells_le (hL : L.WF n) (f : ℕ → ℕ) (hf : Antitone f) :
    ∑ k ∈ range L.nL, f k * (cntV L k + 2 * cntP L k + 2 * cntQ L k) ≤
      SV L f + 6 * SP L f + 2 * SQ L f := by
  have e1 := sum_fiber_mul (N := L.D.nV) (K := L.nL) L.lv f fun i _ => L.lv_lt_nL i
  have e2 := sum_fiber_mul (N := L.D.nP) (K := L.nL) L.lp f fun i _ => L.lp_lt_nL i
  have e3 := sum_fiber_mul (N := L.D.nP) (K := L.nL) (fun p => L.oLev p 0) f fun i _ => oLev_lt i 0
  have e4 := sum_fiber_mul (N := L.D.nP) (K := L.nL) (fun p => L.oLev p 1) f fun i _ => oLev_lt i 1
  have e5 := sum_fiber_mul (N := L.D.nQ) (K := L.nL) L.lq f fun i _ => L.lq_lt_nL i
  have h3 : ∑ p ∈ range L.D.nP, f (L.oLev p 0) ≤ SP L f :=
    sum_le_sum fun p hp => hf (oLev_ge hL (mem_range.1 hp) 0)
  have h4 : ∑ p ∈ range L.D.nP, f (L.oLev p 1) ≤ SP L f :=
    sum_le_sum fun p hp => hf (oLev_ge hL (mem_range.1 hp) 1)
  have hP : ∑ k ∈ range L.nL, f k * cntP L k ≤ 3 * SP L f := by
    calc ∑ k ∈ range L.nL, f k * cntP L k ≤ ∑ k ∈ range L.nL, (f k * #((range L.D.nP).filter fun p => L.lp p = k) +
          f k * #((range L.D.nP).filter fun p => L.oLev p 0 = k) +
          f k * #((range L.D.nP).filter fun p => L.oLev p 1 = k)) :=
          sum_le_sum fun k _ => by rw [← mul_add, ← mul_add]; exact Nat.mul_le_mul_left _ (card_P_le k)
      _ ≤ 3 * SP L f := by
          rw [sum_add_distrib, sum_add_distrib, e2, e3, e4]; unfold SP at *; omega
  have : ∑ k ∈ range L.nL, f k * (cntV L k + 2 * cntP L k + 2 * cntQ L k) =
      ∑ k ∈ range L.nL, f k * cntV L k + 2 * ∑ k ∈ range L.nL, f k * cntP L k +
        2 * ∑ k ∈ range L.nL, f k * cntQ L k := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [this]
  unfold cntV cntQ
  rw [e1, e5]
  unfold SV SQ at *
  omega

theorem carries_le (hL : L.WF n) (f : ℕ → ℕ) :
    ∑ c ∈ range L.D.nC, f (L.lc c) * cntC L c = SP L f := by
  unfold cntC SP
  have := sum_fiber_mul (N := L.D.nP) (K := L.D.nC) L.D.chainOf (fun c => f (L.lc c))
    fun p hp => (hL.prod_ok p hp).2.2.2
  exact this

/-- **The stage sum in terms of the description.** -/
theorem aBSum_le' (hL : L.WF n) (g : ℕ) : aBSum n L g ≤
    SV L (kl n) + 60 * SP L (kl n) + 8 * SC L (kl n) + 2 * SQ L (kl n) +
      g * (L.D.nV + 10 * L.D.nP + 2 * L.D.nC + 2 * L.D.nQ + 17 * SP L (kL1 n)) := by
  rw [aBSum_eq]
  simp only [sum_range_succ, sum_range_zero, zero_add, vObj, List.getD_cons_zero, List.getD_cons_succ, vBox,
    degS, List.prod_cons, List.prod_nil, mul_one]
  have hc0 := cells_le hL (kl n) (kl_antitone n)
  have hc1 := cells_le hL (fun _ => 1) (fun _ _ _ => le_rfl)
  rw [SV_one, SP_one, SQ_one] at hc1
  have hcC := carries_le hL (kl n)
  have hcC1 : ∑ c ∈ range L.D.nC, cntC L c = L.D.nP := by
    have := carries_le hL (fun _ => 1); simp only [one_mul] at this; rw [this, SP_one]
  have hK : ∀ k, kKc n k ≤ 4 * kl n k := fun k => by
    unfold kKc kl; rw [kL1_eq]; nlinarith [one_le_kl1 n k]
  have t0 : ∑ k ∈ range L.nL, (kl n k + g) * (cntV L k + 2 * cntP L k + 2 * cntQ L k) ≤
      SV L (kl n) + 6 * SP L (kl n) + 2 * SQ L (kl n) + g * (L.D.nV + 6 * L.D.nP + 2 * L.D.nQ) := by
    have : ∑ k ∈ range L.nL, (kl n k + g) * (cntV L k + 2 * cntP L k + 2 * cntQ L k) =
        ∑ k ∈ range L.nL, kl n k * (cntV L k + 2 * cntP L k + 2 * cntQ L k) +
          g * ∑ k ∈ range L.nL, 1 * (cntV L k + 2 * cntP L k + 2 * cntQ L k) := by
      rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
    rw [this]
    have := Nat.mul_le_mul_left g hc1
    omega
  have tP : ∀ p, (2 * kl1 n (L.lp p) + g) * (kl1 n (L.lp p) + kL1 n (L.lp p)) +
      (2 * kL1 n (L.lp p) + g) * (kl1 n (L.lp p) + kL1 n (L.lp p)) +
      (kL1 n (L.lp p) * kL1 n (L.lp p) + g) * 3 + (kL1 n (L.lp p) + g) * (2 * kL1 n (L.lp p)) +
      (kL1 n (L.lp p) + g) * (2 * kL1 n (L.lp p)) ≤ 46 * kl n (L.lp p) + g * 2 + g * (17 * kL1 n (L.lp p)) := by
    intro p
    have h1 := one_le_kl1 n (L.lp p)
    unfold kl; rw [kL1_eq]
    nlinarith
  have tPs : ∑ p ∈ range L.D.nP, (2 * kl1 n (L.lp p) + g) * (kl1 n (L.lp p) + kL1 n (L.lp p)) +
      ∑ p ∈ range L.D.nP, (2 * kL1 n (L.lp p) + g) * (kl1 n (L.lp p) + kL1 n (L.lp p)) +
      ∑ p ∈ range L.D.nP, (kL1 n (L.lp p) * kL1 n (L.lp p) + g) * 3 +
      ∑ p ∈ range L.D.nP, (kL1 n (L.lp p) + g) * (2 * kL1 n (L.lp p)) +
      ∑ p ∈ range L.D.nP, (kL1 n (L.lp p) + g) * (2 * kL1 n (L.lp p)) ≤
      46 * SP L (kl n) + g * (2 * L.D.nP) + g * (17 * SP L (kL1 n)) := by
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine (sum_le_sum fun p _ => tP p).trans (le_of_eq ?_)
    unfold SP
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, card_range, smul_eq_mul, ← mul_sum, ← mul_sum]
    ring
  have t6 : ∑ c ∈ range L.D.nC, (kKc n (L.lc c) + g) * (2 * cntC L c + 2) ≤
      8 * SP L (kl n) + 8 * SC L (kl n) + g * (2 * L.D.nP + 2 * L.D.nC) := by
    calc ∑ c ∈ range L.D.nC, (kKc n (L.lc c) + g) * (2 * cntC L c + 2)
        ≤ ∑ c ∈ range L.D.nC, (8 * (kl n (L.lc c) * cntC L c) + 8 * kl n (L.lc c) + g * (2 * cntC L c + 2)) :=
          sum_le_sum fun c _ => by have := hK (L.lc c); nlinarith
      _ = 8 * ∑ c ∈ range L.D.nC, kl n (L.lc c) * cntC L c + 8 * ∑ c ∈ range L.D.nC, kl n (L.lc c) +
            g * (2 * ∑ c ∈ range L.D.nC, cntC L c + 2 * L.D.nC) := by
          simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, smul_eq_mul]; ring
      _ = 8 * SP L (kl n) + 8 * SC L (kl n) + g * (2 * L.D.nP + 2 * L.D.nC) := by
          rw [hcC, hcC1]; rfl
  linarith [tPs, t0, t6]

end Bounds

/-! ## The bounds under `Spread` -/

section Spread

variable {n : ℕ} {L : LDesc} {c : ℕ} (hs : L.Spread c) (hc : 1 ≤ c)
include hs hc

theorem SV_le {f : ℕ → ℕ} (hf : Antitone f) : SV L f ≤ c * ∑ k ∈ range L.nL, f k :=
  spread_sum hf hc L.lv hs.var fun v _ => L.lv_lt_nL v
theorem SP_le {f : ℕ → ℕ} (hf : Antitone f) : SP L f ≤ c * ∑ k ∈ range L.nL, f k :=
  spread_sum hf hc L.lp hs.prod fun p _ => L.lp_lt_nL p
theorem SC_le {f : ℕ → ℕ} (hf : Antitone f) : SC L f ≤ c * ∑ k ∈ range L.nL, f k :=
  spread_sum hf hc L.lc hs.chain fun j _ => L.lc_lt_nL j
theorem SQ_le {f : ℕ → ℕ} (hf : Antitone f) : SQ L f ≤ c * ∑ k ∈ range L.nL, f k :=
  spread_sum hf hc L.lq hs.cmp fun q _ => L.lq_lt_nL q

theorem nV_le : L.D.nV ≤ c * L.nL := spread_le hc hs.var fun v _ => L.lv_lt_nL v
theorem nP_le : L.D.nP ≤ c * L.nL := spread_le hc hs.prod fun p _ => L.lp_lt_nL p
theorem nC_le : L.D.nC ≤ c * L.nL := spread_le hc hs.chain fun j _ => L.lc_lt_nL j
theorem nQ_le : L.D.nQ ≤ c * L.nL := spread_le hc hs.cmp fun q _ => L.lq_lt_nL q

/-- **The stage sum, geometric form**: `aBSum ≤ 71 c (4ℓ + nL) + g c (68 L1 + 49 nL)`. -/
theorem aBSum_le (hL : L.WF n) (g : ℕ) :
    aBSum n L g ≤ 71 * c * (4 * ℓ n + L.nL) + g * (c * (68 * L1 n + 49 * L.nL)) := by
  have h := aBSum_le' hL g
  have hk := sum_kl_le n L.nL
  have hk1 := sum_kL1_le n L.nL
  have a1 := SV_le hs hc (kl_antitone n)
  have a2 := SP_le hs hc (kl_antitone n)
  have a3 := SC_le hs hc (kl_antitone n)
  have a4 := SQ_le hs hc (kl_antitone n)
  have a5 := SP_le hs hc (kL1_antitone n)
  have b1 := nV_le hs hc; have b2 := nP_le hs hc; have b3 := nC_le hs hc; have b4 := nQ_le hs hc
  have k1 := Nat.mul_le_mul_left c hk
  have k2 := Nat.mul_le_mul_left c hk1
  have hA : SV L (kl n) + 60 * SP L (kl n) + 8 * SC L (kl n) + 2 * SQ L (kl n) ≤ 71 * c * (4 * ℓ n + L.nL) := by
    nlinarith
  have hB : L.D.nV + 10 * L.D.nP + 2 * L.D.nC + 2 * L.D.nQ + 17 * SP L (kL1 n) ≤ c * (68 * L1 n + 49 * L.nL) := by
    nlinarith
  exact h.trans (Nat.add_le_add hA (Nat.mul_le_mul_left g hB))

end Spread

/-! ## The node bound and Definition 2 -/

/-- The node bound `P` of the leveled network. -/
def PL (n c g : ℕ) : ℕ := 2 ^ 22 * c * ((n + 2) / g + dg n)

section Sys

variable {n : ℕ} {L : LDesc} {g c : ℕ} (hg : 2 ≤ g) (hL : L.WF n) (hs : L.Spread c) (hc : 1 ≤ c)
  (hK : L.nL ≤ ν n + 3)

include hL hs hc hK in
/-- **The label bits at a node**: `#(items at a) · Wa ≤ PL n c g`. -/
theorem card_inc_mul_Wa_le (a : Fin g) :
    #(univ.filter ((arithSys n L g hg).Inc a)) * Wa n ≤ PL n c g := by
  set X := #(univ.filter ((arithSys n L g hg).Inc a))
  have h1 := g_mul_card_inc_le' (n := n) (L := L) hg a
  have h2 := aBSum_le hs hc hL g
  have h3 := ℓ_mul_Wa_le n
  have h4 := L1_Wa_le n
  have h5 := (ν_Wa_le n).1
  have h6 := (ν_Wa_le n).2
  have hKW : L.nL * Wa n ≤ (ν n + 3) * Wa n := Nat.mul_le_mul_right _ hK
  have hdg : 1 ≤ dg n := Nat.one_le_two_pow
  have hgX : g * (X * Wa n) ≤ c * (2 ^ 21 * (n + 2)) + g * (c * (2 ^ 10 * dg n)) := by
    have e1 : g * (X * Wa n) ≤ 3 * (71 * c * (4 * ℓ n + L.nL) + g * (c * (68 * L1 n + 49 * L.nL))) * Wa n := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (h1.trans (Nat.mul_le_mul_left _ h2))
    have e2 : 3 * (71 * c * (4 * ℓ n + L.nL) + g * (c * (68 * L1 n + 49 * L.nL))) * Wa n =
        c * (852 * (ℓ n * Wa n) + 213 * (L.nL * Wa n)) + g * (c * (204 * (L1 n * Wa n) + 147 * (L.nL * Wa n))) := by
      ring
    have e3 : 852 * (ℓ n * Wa n) + 213 * (L.nL * Wa n) ≤ 2 ^ 21 * (n + 2) := by omega
    have e4 : 204 * (L1 n * Wa n) + 147 * (L.nL * Wa n) ≤ 2 ^ 10 * dg n := by omega
    rw [e2] at e1
    have := Nat.mul_le_mul_left c e3
    have := Nat.mul_le_mul_left g (Nat.mul_le_mul_left c e4)
    omega
  have hdiv := Nat.div_add_mod (n + 2) g
  have hmod := Nat.mod_lt (n + 2) (show 0 < g by omega)
  have hlt : g * (X * Wa n) < g * (c * 2 ^ 21 * ((n + 2) / g) + c * 2 ^ 21 + c * 2 ^ 10 * dg n) := by
    have : c * (2 ^ 21 * (n + 2)) = c * 2 ^ 21 * (g * ((n + 2) / g) + (n + 2) % g) := by rw [hdiv]; ring
    have h5 : c * 2 ^ 21 * ((n + 2) % g) < c * 2 ^ 21 * g := Nat.mul_lt_mul_of_pos_left hmod (by positivity)
    nlinarith
  have h7 := Nat.lt_of_mul_lt_mul_left hlt
  unfold PL
  have hcd : c * 1 ≤ c * dg n := Nat.mul_le_mul_left _ hdg
  have e : 2 ^ 22 * c * ((n + 2) / g + dg n) = 4194304 * (c * ((n + 2) / g)) + 4194304 * (c * dg n) := by ring
  have e' : c * 2 ^ 21 * ((n + 2) / g) + c * 2 ^ 21 + c * 2 ^ 10 * dg n =
      2097152 * (c * ((n + 2) / g)) + 2097152 * (c * 1) + 1024 * (c * dg n) := by ring
  rw [e]; rw [e'] at h7
  omega

include hL hs hc hK in
/-- The number of wires: `numAW ≤ 32 c (4ℓ + nL)`. -/
theorem numAW_le : numAW n L ≤ 32 * c * (4 * ℓ n + L.nL) := by
  rw [numAW_eq]
  simp only [sum_range_succ, sum_range_zero, zero_add, wObj, List.getD_cons_zero, List.getD_cons_succ, wBox,
    List.prod_cons, List.prod_nil, mul_one]
  have hk := sum_kl_le n L.nL
  have a1 := SV_le hs hc (kl_antitone n)
  have a2 := SP_le hs hc (kl_antitone n)
  have a3 := SC_le hs hc (kl_antitone n)
  have a4 := SQ_le hs hc (kl_antitone n)
  have k1 := Nat.mul_le_mul_left c hk
  have tP : ∑ p ∈ range L.D.nP, 2 * kl n (L.lp p) + ∑ p ∈ range L.D.nP, 2 * (kL1 n (L.lp p) * kl1 n (L.lp p)) +
      ∑ p ∈ range L.D.nP, 2 * (kL1 n (L.lp p) * kL1 n (L.lp p)) + ∑ p ∈ range L.D.nP, kL1 n (L.lp p) * kL1 n (L.lp p) +
      ∑ p ∈ range L.D.nP, kL1 n (L.lp p) * kL1 n (L.lp p) + ∑ p ∈ range L.D.nP, kL1 n (L.lp p) * kL1 n (L.lp p) =
      26 * SP L (kl n) := by
    unfold SP; rw [mul_sum]
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun p _ => by unfold kl; rw [kL1_eq]; ring
  have tC : ∑ j ∈ range L.D.nC, (kKc n (L.lc j) - 1) ≤ 4 * SC L (kl n) := by
    unfold SC; rw [mul_sum]
    exact sum_le_sum fun j _ => by
      have : kKc n (L.lc j) ≤ 4 * kl n (L.lc j) := by unfold kKc kl; rw [kL1_eq]; nlinarith [one_le_kl1 n (L.lc j)]
      omega
  have tQ : ∑ q ∈ range L.D.nQ, (kl n (L.lq q) - 1) ≤ SQ L (kl n) := sum_le_sum fun q _ => Nat.sub_le _ _
  have : SV L (kl n) + 26 * SP L (kl n) + 4 * SC L (kl n) + SQ L (kl n) ≤ 32 * c * (4 * ℓ n + L.nL) := by
    nlinarith
  unfold SV at this
  omega

include hL hs hc hK in
/-- **`U ≤ 2^19 · c · (n + 2)`.** -/
theorem arithSys_U_le : ((arithSys n L g hg).net (aLabCode n)).U ≤ 2 ^ 19 * c * (n + 2) := by
  rw [LabelSystem.U_eq, Fintype.card_fin, Fintype.card_eq_zero, clog_Wa, add_zero]
  have h1 := Nat.mul_le_mul_right (Wa n) (numAW_le hL hs hc hK)
  have h3 := ℓ_mul_Wa_le n
  have h5 := (ν_Wa_le n).1
  have hKW : L.nL * Wa n ≤ (ν n + 3) * Wa n := Nat.mul_le_mul_right _ hK
  have e : 32 * c * (4 * ℓ n + L.nL) * Wa n = 32 * c * (4 * (ℓ n * Wa n) + L.nL * Wa n) := by ring
  rw [e] at h1
  have : 4 * (ℓ n * Wa n) + L.nL * Wa n ≤ 2 ^ 13 * (n + 2) := by omega
  have := Nat.mul_le_mul_left (32 * c) this
  calc 2 * (numAW n L * Wa n) ≤ 2 * (32 * c * (2 ^ 13 * (n + 2))) := by omega
    _ = 2 ^ 19 * c * (n + 2) := by ring

include hL hs hc hK in
/-- **Definition 2 for the leveled network** with `P = PL n c g` and `B = 1`. -/
theorem arithSys_is : ((arithSys n L g hg).net (aLabCode n)).Is (PL n c g) 1 := by
  refine LabelSystem.net_is _ _ ?_ le_rfl (fun a => ?_) (fun a ℓ y => by rw [arithSys_T]; exact arithT_abs_lt (n := n) (L := L) a ℓ)
  · unfold PL
    have h1 : 1 ≤ dg n := Nat.one_le_two_pow
    have h2 : 1 ≤ (n + 2) / g + dg n := le_trans h1 (Nat.le_add_left _ _)
    exact le_trans h2 (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) (by omega)))
  · rw [arithSys_touch hg, add_zero, clog_Wa]
    exact card_inc_mul_Wa_le hg hL hs hc hK a

end Sys

end EthFollowup.Primes
