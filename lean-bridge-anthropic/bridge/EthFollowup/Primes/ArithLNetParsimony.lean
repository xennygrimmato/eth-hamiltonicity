/-
# ArithL, module 3b: parsimony and the value

Template: `ModP/ArithNetParsimony.lean`.
* `aValOf n L x`: the variable values read off the limb wires `L v i` (`i < ℓ_{lv v}`);
* `aEq_run`: for well-formed `L`, if all checks pass on `x`, then `x = aRun n L (aValOf n L x)` on
  every valid wire;
* `aRun_all_iff`: for `y` in the level boxes, the canonical assignment passes every check iff
  `L.D.Sat (b n) y`;
* **`arithNet_card`**, **`arithNet_value`**: the value of `arithSys n L g` is
  `LDesc.count n L = L.countB (b n) (lbox n)`.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLNetDefs
import EthFollowup.ModP.ArithNetParsimony

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.ExactHC EthFollowup.Factoring EthFollowup.ModP EthFollowup.Factoring.MP

/-- **The count** at top length `n`: level-`k` variables in `[0, 2^{b ℓ_k})`. -/
def LDesc.count (n : ℕ) (L : LDesc) : ℕ := L.countB (b n) (lbox n)

/-- **Well-formedness** at top length `n` (`ℓ_k` limbs at level `k`). -/
def LDesc.WF (n : ℕ) (L : LDesc) : Prop := L.WFB (b n) (kl n)

/-! ## Patterns and limbs -/

/-- The pattern cells of a level with `K` limbs. -/
theorem patOK_iff_patMatch' (n K : ℕ) {pt : List (Option Bool)} (hpt : pt.length ≤ b n * K) (y : ℕ) :
    (∀ i < K, patOK n pt i (limb (b n) y i) = true) ↔ patMatch pt y := by
  have hb := one_le_b n
  unfold patMatch
  constructor
  · intro h j hj
    have hj' : j < b n * K := lt_of_lt_of_le hj hpt
    obtain ⟨h1, h2⟩ := blk_dec hj'
    have := h (j / b n) h2
    simp only [patOK, List.all_eq_true, List.mem_range] at this
    have e := this (j % b n) h1
    rw [testBit_limb _ _ _ _ h1, Nat.mod_add_div, add_comm, Nat.mod_add_div, obit_eq_optBit] at e
    exact e
  · intro h i hi
    simp only [patOK, List.all_eq_true, List.mem_range]
    intro j hj
    rw [testBit_limb _ _ _ _ hj, show j + b n * i = b n * i + j by ring, obit_eq_optBit]
    by_cases hl : b n * i + j < pt.length
    · exact h _ hl
    · rw [List.getD_eq_default _ _ (by omega)]; rfl

/-- Limbs beyond the box vanish. -/
theorem limb_eq_zero {b x K i : ℕ} (hx : x < 2 ^ (b * K)) (hi : K ≤ i) : limb b x i = 0 := by
  unfold limb
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hi)))]
  simp

theorem lbox_anti (n : ℕ) {k k' : ℕ} (h : k ≤ k') : lbox n k' ≤ lbox n k :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (kl_anti n h))

/-! ## Operands under well-formedness -/

section Operands
variable {n : ℕ} {L : LDesc}

theorem LDesc.ch_mem {c : ℕ} (hc : c < L.D.nC) : L.D.ch c ∈ L.D.chains := by
  unfold Desc.ch; rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc
theorem LDesc.cq_mem {q : ℕ} (hq : q < L.D.nQ) : L.D.cq q ∈ L.D.cmps := by
  unfold Desc.cq; rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq

/-- The operands of a product: a variable of level `≥ lp p`, or a short constant. -/
theorem opnd_OK (hL : L.WF n) {p : ℕ} (hp : p < L.D.nP) (σ : ℕ) : L.OpOK (b n) (kl n) (L.lp p) (opnd L.D p σ) := by
  have h := hL.prod_ok p hp
  unfold opnd; split_ifs
  · exact ⟨h.1, h.2.1⟩
  · exact h.2.2.1

variable {y : ℕ → ℕ}

/-- In-box variable values. -/
def InBoxL (n : ℕ) (L : LDesc) (y : ℕ → ℕ) : Prop := ∀ v < L.D.nV, y v < lbox n (L.lv v)

theorem eval_lt_lbox (hy : InBoxL n L y) {k : ℕ} {o : Operand} (ho : L.OpOK (b n) (kl n) k o) :
    o.eval (b n) y < lbox n k := by
  cases o with
  | var w => exact lt_of_lt_of_le (hy w ho.1) (lbox_anti n ho.2)
  | const l => exact limbsVal_lt ho.2 ho.1

theorem opVal_lt (hL : L.WF n) (hy : InBoxL n L y) {p : ℕ} (hp : p < L.D.nP) (σ : ℕ) :
    opVal n L y p σ < lbox n (L.lp p) := eval_lt_lbox hy (opnd_OK hL hp σ)

theorem limb_opVal (hL : L.WF n) (hy : InBoxL n L y) {p : ℕ} (hp : p < L.D.nP) (σ i : ℕ) :
    limb (b n) (opVal n L y p σ) i = opLimbR n L (aRun n L y) p σ i := by
  have ho := opnd_OK hL hp σ
  unfold opVal opLimbR
  cases e : opnd L.D p σ with
  | var w =>
    rw [e] at ho
    simp only [Operand.eval]
    split_ifs with h
    · rfl
    · exact limb_eq_zero (hy w ho.1) (by have := ho.1; omega)
  | const l =>
    rw [e] at ho
    exact limb_limbsVal_all ho.2 i

theorem opLimbVC_lt' (k : ℕ) (o : Operand) (ho : ∀ l, o = .const l → ∀ y ∈ l, y < 2 ^ b n) (i : ℕ) :
    opLimbVC n L y k o i < 2 ^ b n := by
  cases o with
  | var w => simp only [opLimbVC]; split_ifs; exacts [limb_lt _ _ _, by positivity]
  | const l => exact getD_lt (ho l rfl) i

theorem sum_opLimbVC (hy : InBoxL n L y) {k : ℕ} {o : Operand} (ho : L.CmpOK (b n) (kl n) k o) :
    ∑ i ∈ range (kl n k), opLimbVC n L y k o i * 2 ^ (b n * i) = o.eval (b n) y := by
  cases o with
  | var w =>
    obtain ⟨hw, hk⟩ := ho
    simp only [opLimbVC, if_pos (show w < L.D.nV ∧ L.lv w = k from ⟨hw, hk⟩), Operand.eval]
    have := ofLimbs_limb (b n) (y w) (kl n k) (by have := hy w hw; rw [hk] at this; exact this)
    exact this
  | const l =>
    simp only [opLimbVC, Operand.eval]
    exact (limbsVal_eq_ofLimbs (b n) l ho.1).symm

end Operands

/-! ## Stage induction: all checks force the canonical assignment -/

/-- The variable values read off the limb wires (`0` beyond `nV`). -/
def aValOf (n : ℕ) (L : LDesc) (x : AWL → ℕ) (v : ℕ) : ℕ :=
  if v < L.D.nV then ofLimbs (b n) (fun i => x (.L v i)) (kl n (L.lv v)) else 0

section Stages

variable {n : ℕ} {L : LDesc} {x : AWL → ℕ} (hL : L.WF n) (hall : ∀ v, v.Valid n L → aChk n L x v = true)
include hall

theorem L_lt_of_all {v : ℕ} (hv : v < L.D.nV) : ∀ i < kl n (L.lv v), x (.L v i) < 2 ^ b n := fun i hi =>
  ((aChk_cell_iff.1 (hall (.cell (L.lv v) i) (valid_cell.2 ⟨L.lv_lt_nL v, hi⟩))).1 v hv rfl).1

theorem aValOf_lt (v : ℕ) : aValOf n L x v < lbox n (L.lv v) := by
  unfold aValOf lbox
  split_ifs with hv
  · exact ofLimbs_lt (b n) _ _ (L_lt_of_all hall hv)
  · positivity

theorem limb_aValOf {v i : ℕ} (hv : v < L.D.nV) (hi : i < kl n (L.lv v)) :
    limb (b n) (aValOf n L x v) i = x (.L v i) := by
  unfold aValOf; rw [if_pos hv, limb_ofLimbs _ _ _ (L_lt_of_all hall hv) _ hi]

theorem aEq_L {v i : ℕ} (hv : v < L.D.nV) (hi : i < kl n (L.lv v)) :
    x (.L v i) = aRun n L (aValOf n L x) (.L v i) :=
  (limb_aValOf hall hv hi).symm

theorem opLimbR_eq {p σ i : ℕ} : opLimbR n L x p σ i = opLimbR n L (aRun n L (aValOf n L x)) p σ i := by
  unfold opLimbR
  split
  · split_ifs with h
    · exact aEq_L hall h.1 h.2
    · rfl
  · rfl

include hL in
theorem aEq_R {p σ i : ℕ} (hp : p < L.D.nP) (hσ : σ < 2) (hi : i < kl n (L.lp p)) :
    x (.R p σ i) = limb (b n) (opVal n L (aValOf n L x) p σ) i := by
  obtain ⟨k, hk⟩ := cellR_eq n L p σ i
  have hc := hall _ (cellR_valid (σ := σ) hi)
  rw [hk] at hc
  rw [(aChk_cell_iff.1 hc).2.1 p hp σ hσ hi hk, opLimbR_eq hall,
    limb_opVal hL (fun v _ => aValOf_lt hall v) hp]

include hL in
theorem aPA {p σ i1 i2 : ℕ} (hp : p < L.D.nP) (hσ : σ < 2) (h1 : i1 < kl1 n (L.lp p)) (h2 : i2 < kl1 n (L.lp p)) :
    pAk n (L.lp p) (opVal n L (aValOf n L x) p σ) i1 i2 = x (.R p σ (i1 + kl1 n (L.lp p) * i2)) :=
  (aEq_R hL hall hp hσ (blk_lt h1 h2)).symm

include hL in
theorem aEq_A {p σ s i2 : ℕ} (hp : p < L.D.nP) (hσ : σ < 2) (hs : s < kL1 n (L.lp p)) (h2 : i2 < kl1 n (L.lp p)) :
    x (.A p σ s i2) = kA n (L.lp p) (opVal n L (aValOf n L x) p σ) s i2 := by
  rw [(aChk_row_iff.1 (hall _ (valid_row.2 ⟨hp, hσ, h2⟩))) s hs]
  exact rowE_congr' n _ (fun i1 hi1 => (aPA hL hall hp hσ hi1 h2).symm) s

include hL in
theorem aEq_F {p σ s t : ℕ} (hp : p < L.D.nP) (hσ : σ < 2) (hs : s < kL1 n (L.lp p)) (ht : t < kL1 n (L.lp p)) :
    x (.F p σ s t) = kF n (L.lp p) (opVal n L (aValOf n L x) p σ) s t := by
  rw [(aChk_col_iff.1 (hall _ (valid_col.2 ⟨hp, hσ, hs⟩))) t ht]
  exact colE_congr' n _ (fun i2 hi2 => aEq_A hL hall hp hσ hs hi2) t

include hL in
theorem aEq_C {p s t : ℕ} (hp : p < L.D.nP) (hs : s < kL1 n (L.lp p)) (ht : t < kL1 n (L.lp p)) :
    x (.C p s t) = kC n (L.lp p) (opVal n L (aValOf n L x) p 0) (opVal n L (aValOf n L x) p 1) s t := by
  rw [aChk_mul_iff.1 (hall _ (valid_mul.2 ⟨hp, hs, ht⟩)), aEq_F hL hall hp (by norm_num) hs ht,
    aEq_F hL hall hp (by norm_num) hs ht]
  rfl

include hL in
theorem aEq_Dd {p s u : ℕ} (hp : p < L.D.nP) (hs : s < kL1 n (L.lp p)) (hu : u < kL1 n (L.lp p)) :
    x (.Dd p s u) = kD n (L.lp p) (opVal n L (aValOf n L x) p 0) (opVal n L (aValOf n L x) p 1) s u := by
  rw [(aChk_icol_iff.1 (hall _ (valid_icol.2 ⟨hp, hs⟩))) u hu]
  exact invColE_congr' n _ (fun t ht => aEq_C hL hall hp hs ht) u

include hL in
theorem aEq_E {p a u : ℕ} (hp : p < L.D.nP) (ha : a < kL1 n (L.lp p)) (hu : u < kL1 n (L.lp p)) :
    x (.E p a u) = kE n (L.lp p) (opVal n L (aValOf n L x) p 0) (opVal n L (aValOf n L x) p 1) a u := by
  rw [(aChk_irow_iff.1 (hall _ (valid_irow.2 ⟨hp, hu⟩))) a ha]
  exact invRowE_congr' n _ (fun s hs => aEq_Dd hL hall hp hs hu) a

include hL in
theorem aEq_tDig (c : ℕ) (t : Term) (k : ℕ) : tDig n L x c t k = cDig n L (aValOf n L x) c t k := by
  obtain ⟨a, src⟩ := t
  cases src with
  | prod p =>
    simp only [tDig, cDig]
    split_ifs with hp
    · have hlp : L.lp p = L.lc c := by unfold LDesc.lp; rw [hp.2]
      unfold kc
      exact convE_congr n _ fun _ ha _ hu _ => by
        rw [aEq_E hL hall hp.1 (by rw [hlp]; exact ha) (by rw [hlp]; exact hu), hlp]
    · rfl
  | lin v => rfl
  | const l => rfl

include hL in
theorem aEq_sDig (c : ℕ) (ts : List Term) : sDig n L x c ts = cSide n L (aValOf n L x) c ts := by
  funext k; simp only [sDig, cSide, aEq_tDig hL hall c]

include hL in
theorem aEq_rr {c j : ℕ} (hc : c < L.D.nC) (hj : j + 1 < kKc n (L.lc c)) :
    x (.rr c j) = aRun n L (aValOf n L x) (.rr c j) := by
  have h : ∀ k < kKc n (L.lc c), carryChk (b n) (kKc n (L.lc c)) (aOFF n)
      (cSide n L (aValOf n L x) c (L.D.ch c).lhs)
      (cSide n L (aValOf n L x) c (L.D.ch c).rhs) (fun j => x (.rr c j)) k := fun k hk => by
    have := aChk_carry_iff.1 (hall _ (valid_carry.2 ⟨hc, hk⟩))
    rwa [aEq_sDig hL hall, aEq_sDig hL hall] at this
  exact carryChk_unique h j hj

theorem opLimbC_eq {k : ℕ} (o : Operand) {i : ℕ} (hi : i < kl n k) :
    opLimbC L x k o i = opLimbVC n L (aValOf n L x) k o i := by
  cases o with
  | var w =>
    simp only [opLimbC, opLimbVC]
    split_ifs with h
    · exact (limb_aValOf hall h.1 (by rw [h.2]; exact hi)).symm
    · rfl
  | const l => rfl

include hL in
theorem aEq_st {q j : ℕ} (hq : q < L.D.nQ) (hj : j + 1 < kl n (L.lq q)) :
    x (.st q j) = aRun n L (aValOf n L x) (.st q j) := by
  obtain ⟨h1, h2⟩ := hL.cmp_ok q hq
  have hcst : ∀ l, (L.D.cq q).rhs = .const l → ∀ y ∈ l, y < 2 ^ b n := fun l e => by
    unfold Desc.cq at e; rw [e] at h2; exact h2.2
  have hyl : ∀ i < kl n (L.lq q), opLimbC L x (L.lq q) (.var (L.D.cq q).v) i < 2 ^ b n := fun i hi => by
    rw [opLimbC_eq hall _ hi]; exact opLimbVC_lt' _ (.var (L.D.cq q).v) (fun l e => by cases e) i
  have hpl : ∀ i < kl n (L.lq q), opLimbC L x (L.lq q) (L.D.cq q).rhs i < 2 ^ b n := fun i hi => by
    rw [opLimbC_eq hall _ hi]; exact opLimbVC_lt' _ _ hcst i
  have hcell : ∀ i < kl n (L.lq q), cmpCell (L.D.cq q).rel (kl n (L.lq q)) (opLimbC L x (L.lq q) (.var (L.D.cq q).v))
      (opLimbC L x (L.lq q) (L.D.cq q).rhs) (fun j => x (.st q j)) i = true := fun i hi =>
    (aChk_cell_iff.1 (hall (.cell (L.lq q) i) (valid_cell.2 ⟨L.lq_lt_nL q, hi⟩))).2.2 q hq rfl
  rw [cmpChain_unique hyl hpl hcell j hj]
  exact cmpT_congr (fun i hi => opLimbC_eq hall _ hi) (fun i hi => opLimbC_eq hall _ hi) _

include hL in
/-- **Stage induction.** -/
theorem aEq_run : ∀ d, d.Valid n L → x d = aRun n L (aValOf n L x) d := by
  intro d hd
  cases d with
  | L v i => exact aEq_L hall (valid_L.1 hd).1 (valid_L.1 hd).2
  | R p σ i => exact aEq_R hL hall (valid_R.1 hd).1 (valid_R.1 hd).2.1 (valid_R.1 hd).2.2
  | A p σ s i2 => exact aEq_A hL hall (valid_A.1 hd).1 (valid_A.1 hd).2.1 (valid_A.1 hd).2.2.1 (valid_A.1 hd).2.2.2
  | F p σ s t => exact aEq_F hL hall (valid_F.1 hd).1 (valid_F.1 hd).2.1 (valid_F.1 hd).2.2.1 (valid_F.1 hd).2.2.2
  | C p s t => exact aEq_C hL hall (valid_C.1 hd).1 (valid_C.1 hd).2.1 (valid_C.1 hd).2.2
  | Dd p s u => exact aEq_Dd hL hall (valid_Dd.1 hd).1 (valid_Dd.1 hd).2.1 (valid_Dd.1 hd).2.2
  | E p a u => exact aEq_E hL hall (valid_E.1 hd).1 (valid_E.1 hd).2.1 (valid_E.1 hd).2.2
  | rr c j => exact aEq_rr hL hall (valid_rr.1 hd).1 (valid_rr.1 hd).2
  | st q j => exact aEq_st hL hall (valid_st.1 hd).1 (valid_st.1 hd).2

end Stages

/-! ## The canonical assignment passes all checks iff the variables satisfy `L.D` -/

section Canon

variable {n : ℕ} {L : LDesc} {y : ℕ → ℕ} (hL : L.WF n) (hy : InBoxL n L y)

theorem term_ok' (hL : L.WF n) {c : ℕ} (hc : c < L.D.nC) {t : Term} (ht : t ∈ (L.D.ch c).lhs ++ (L.D.ch c).rhs) :
    L.SrcOK (b n) (kl n) (L.lc c) t.src := hL.term_ok c hc t ht

include hL hy in
theorem sum_cDig {c : ℕ} (hc : c < L.D.nC) {t : Term} (ht : t ∈ (L.D.ch c).lhs ++ (L.D.ch c).rhs) :
    ∑ k ∈ range (kKc n (L.lc c)), cDig n L y c t k * 2 ^ (b n * k) = t.src.eval (b n) L.D.prods y := by
  have hok := term_ok' hL hc ht
  obtain ⟨a, src⟩ := t
  cases src with
  | prod p =>
    have hp : p < L.D.nP := hok
    have hcp : L.D.chainOf p = c := L.chainOf_eq hL hc ⟨_, ht, rfl⟩
    have hlp : L.lp p = L.lc c := by unfold LDesc.lp; rw [hcp]
    simp only [cDig, if_pos (show p < L.D.nP ∧ L.D.chainOf p = c from ⟨hp, hcp⟩)]
    rw [kc_eval n _ _ _ (hlp ▸ opVal_lt hL hy hp 0) (hlp ▸ opVal_lt hL hy hp 1)]
    simp [opVal, opnd, Src.eval, ProdD.eval, Operand.eval]
  | lin v => exact hok.elim
  | const l =>
    simp only [cDig, Src.eval]
    have hlen : l.length ≤ kKc n (L.lc c) := hok.1.trans (kl_le_kKc n _)
    rw [limbsVal_eq_ofLimbs (b n) l hlen]
    rfl

include hL hy in
theorem sum_cSide {c : ℕ} (hc : c < L.D.nC) {ts : List Term} (hts : ∀ t ∈ ts, t ∈ (L.D.ch c).lhs ++ (L.D.ch c).rhs) :
    ∑ k ∈ range (kKc n (L.lc c)), cSide n L y c ts k * 2 ^ (b n * k) = sideVal (b n) L.D.prods y ts := by
  unfold cSide sideVal
  rw [sum_lin ts Term.coeff (cDig n L y c) (b n) (kKc n (L.lc c))]
  congr 1
  exact List.map_congr_left fun t ht => by rw [sum_cDig hL hy hc (hts t ht)]

include hL in
theorem cSide_le {c : ℕ} (hc : c < L.D.nC) {ts : List Term} (hm : (ts.map Term.coeff).sum ≤ 32)
    (hts : ∀ t ∈ ts, t ∈ (L.D.ch c).lhs ++ (L.D.ch c).rhs) (k : ℕ) :
    cSide n L y c ts k ≤ aOFF n * (2 ^ b n - 1) := by
  refine side_le_OFF_terms n ts (fun t => cDig n L y c t k) hm fun t ht => ?_
  have hok := term_ok' hL hc (hts t ht)
  obtain ⟨a, src⟩ := t
  cases src with
  | prod p => simp only [cDig]; split_ifs; exacts [kc_le n _ _ _ k, Nat.zero_le _]
  | lin v => exact hok.elim
  | const l => exact getD_le_pow hok.2 k

include hL hy in
/-- **The carries of chain `c`.** -/
theorem carries_iff {c : ℕ} (hc : c < L.D.nC) :
    (∀ k < kKc n (L.lc c), aChk n L (aRun n L y) (.carry c k) = true) ↔
      sideVal (b n) L.D.prods y (L.D.ch c).lhs = sideVal (b n) L.D.prods y (L.D.ch c).rhs := by
  have hm := hL.coeff_le _ (LDesc.ch_mem hc)
  simp only [aChk_run_carry]
  rw [← sum_cSide hL hy hc mem_sides_l, ← sum_cSide hL hy hc mem_sides_r]
  constructor
  · intro h
    exact schain_sum ((schainW_iff _ _ _ _ _ _).1 h)
  · intro hs
    exact carryChk_sR (fun k _ => cSide_le hL hc hm.1 mem_sides_l k)
      (fun k _ => cSide_le hL hc hm.2 mem_sides_r k) hs

include hL hy in
/-- **Comparison `q`.** -/
theorem cmps_iff {q : ℕ} (hq : q < L.D.nQ) :
    (∀ i < kl n (L.lq q), cmpCell (L.D.cq q).rel (kl n (L.lq q)) (opLimbVC n L y (L.lq q) (.var (L.D.cq q).v))
      (opLimbVC n L y (L.lq q) (L.D.cq q).rhs)
      (fun j => cmpT (b n) (kl n (L.lq q)) (opLimbVC n L y (L.lq q) (.var (L.D.cq q).v))
        (opLimbVC n L y (L.lq q) (L.D.cq q).rhs) (j + 1)) i = true) ↔
      (L.D.cq q).rel.Holds (y (L.D.cq q).v) ((L.D.cq q).rhs.eval (b n) y) := by
  obtain ⟨h1, h2⟩ := hL.cmp_ok q hq
  have hcst : ∀ l, (L.D.cq q).rhs = .const l → ∀ y ∈ l, y < 2 ^ b n := fun l e => by
    unfold Desc.cq at e; rw [e] at h2; exact h2.2
  have h1' : L.CmpOK (b n) (kl n) (L.lq q) (.var (L.D.cq q).v) := ⟨h1, rfl⟩
  have hl := kl_pos n (L.lq q)
  have key := fun i (hi : i < kl n (L.lq q)) => cmpCell_canon (L.D.cq q).rel (b := b n) (L := kl n (L.lq q))
    (fun i _ => opLimbVC_lt' (L := L) (y := y) (n := n) (L.lq q) (.var (L.D.cq q).v) (fun l e => by cases e) i)
    (fun i _ => opLimbVC_lt' (L := L) (y := y) (n := n) (L.lq q) _ hcst i) hi
  rw [sum_opLimbVC hy h1', sum_opLimbVC hy h2] at key
  constructor
  · intro h; exact (key 0 hl).1 (h 0 hl) rfl
  · intro h i hi; exact (key i hi).2 fun _ => h

include hL hy in
/-- **Parsimony, canonical direction.** -/
theorem aRun_all_iff : (∀ v, v.Valid n L → aChk n L (aRun n L y) v = true) ↔ L.D.Sat (b n) y := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun q hq => ?_, fun ch hch => ?_⟩
    · exact (patOK_iff_patMatch' n (kl n (L.lv v)) (hL.pat_len v hv) (y v)).1 fun i hi =>
        (((aChk_cell_iff (x := aRun n L y)).1 (h _ (valid_cell.2 ⟨L.lv_lt_nL v, hi⟩))).1 v hv rfl).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
      have e : L.D.cq j = L.D.cmps[j] := List.getD_eq_getElem _ _ hj
      rw [← e]
      refine (cmps_iff hL hy hj).1 fun i hi => ?_
      have := ((aChk_cell_iff (x := aRun n L y)).1 (h _ (valid_cell.2 ⟨L.lq_lt_nL j, hi⟩))).2.2 j hj rfl
      unfold cmpOK at this
      simpa only [opLimbC_aRun', aRun] using this
    · obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hch
      have e : L.D.ch c = L.D.chains[c] := List.getD_eq_getElem _ _ hc
      rw [← e]
      exact (carries_iff hL hy hc).1 fun k hk => h _ (valid_carry.2 ⟨hc, hk⟩)
  · rintro ⟨hpat, hcmp, hch⟩ v hv
    cases v with
    | cell k i =>
      obtain ⟨hk, hi⟩ := valid_cell.1 hv
      refine aChk_cell_iff.2 ⟨fun w hw hwk => ⟨limb_lt _ _ _, ?_⟩, fun p hp σ _ _ _ => limb_opVal hL hy hp σ i,
        fun q hq hqk => ?_⟩
      · exact (patOK_iff_patMatch' n (kl n (L.lv w)) (hL.pat_len w hw) (y w)).2 (hpat w hw) i (hwk ▸ hi)
      · unfold cmpOK
        simp only [opLimbC_aRun', aRun]
        exact (cmps_iff hL hy hq).2 (hcmp _ (LDesc.cq_mem hq)) i (hqk ▸ hi)
    | row p σ i2 => exact aChk_run_row n L y p σ i2
    | col p σ s => exact aChk_run_col n L y p σ s
    | mul p s t => exact aChk_run_mul n L y p s t
    | icol p s => exact aChk_run_icol n L y p s
    | irow p u => exact aChk_run_irow n L y p u
    | carry c k =>
      obtain ⟨hc, hk⟩ := valid_carry.1 hv
      exact (carries_iff hL hy hc).2 (hch _ (LDesc.ch_mem hc)) k hk

include hL hy in
theorem aRun_lt_of_sat (hs : L.D.Sat (b n) y) {d : AWL} (hd : d.Valid n L) : aRun n L y d < 2 ^ Wa n := by
  by_cases h : ∃ c j, d = .rr c j
  · obtain ⟨c, j, rfl⟩ := h
    obtain ⟨hc, hj⟩ := valid_rr.1 hd
    have hm := hL.coeff_le _ (LDesc.ch_mem hc)
    have hsum := (sum_cSide hL hy hc mem_sides_l).trans ((hs.2.2 _ (LDesc.ch_mem hc)).trans
      (sum_cSide hL hy hc mem_sides_r).symm)
    have := sR_range (fun k _ => cSide_le hL hc hm.1 mem_sides_l k)
      (fun k _ => cSide_le hL hc hm.2 mem_sides_r k) hsum
      (show 0 < aOFF n by unfold aOFF; positivity) (k := j + 1) hj.le
    exact carry_lt_Wa n _ this.2
  · exact aRun_lt n L y d fun c j hj => h ⟨c, j, hj⟩

end Canon

/-! ## The canonical labelling and the value -/


/-- **The canonical labelling** of `y`. -/
def aRunL (n : ℕ) (L : LDesc) (y : ℕ → ℕ) : Fin (numAW n L) → ALab n := fun k =>
  ⟨aRun n L y (awOf n L k.val) % 2 ^ Wa n, by rw [two_pow_Wa_sub_add]; exact Nat.mod_lt _ (by positivity)⟩

theorem aVal_aRunL {n : ℕ} {L : LDesc} {y : ℕ → ℕ} {d : AWL} (hd : d.Valid n L) :
    aVal n L (aRunL n L y) d = aRun n L y d % 2 ^ Wa n := by
  rw [aVal_of_valid _ hd]
  show aRun n L y (awOf n L (awIdx n L d)) % _ = _
  rw [awOf_awIdx hd]

theorem extV_aValOf (n : ℕ) (L : LDesc) (x : AWL → ℕ) :
    extV L.D.nV (fun i : Fin L.D.nV => aValOf n L x i.val) = aValOf n L x := by
  funext v
  unfold extV
  split_ifs with hv
  · rfl
  · unfold aValOf; rw [if_neg hv]

/-- **Parsimony**: the labellings passing every check are in bijection with the tuples counted by
`LDesc.count n L`. -/
theorem arithNet_card {n : ℕ} {L : LDesc} (hL : L.WF n) :
    #(univ.filter fun ℓ : Fin (numAW n L) → ALab n => aAllOK n L (aVal n L ℓ) = true) = L.count n := by
  unfold LDesc.count LDesc.countB
  symm
  refine card_nbij' (fun x => aRunL n L (extV L.D.nV x)) (fun ℓ i => aValOf n L (aVal n L ℓ) i.val)
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hx
    obtain ⟨hbox, hs⟩ := hx
    have hy : InBoxL n L (extV L.D.nV x) := fun v hv => by
      simp only [extV, dif_pos hv]; exact hbox ⟨v, hv⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    refine aAllOK_iff.2 fun v hv => ?_
    rw [aChk_agree hv fun d hd _ => by
      rw [aVal_aRunL hd, Nat.mod_eq_of_lt (aRun_lt_of_sat hL hy hs hd)]]
    exact (aRun_all_iff hL hy).2 hs v hv
  · intro ℓ hℓ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    have hall := aAllOK_iff.1 hℓ
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq]
    refine ⟨fun i => aValOf_lt hall i.val, ?_⟩
    rw [extV_aValOf]
    refine (aRun_all_iff hL (fun v _ => aValOf_lt hall v)).1 fun v hv => ?_
    rw [← aChk_agree hv fun d hd _ => aEq_run hL hall d hd]
    exact hall v hv
  · intro x hx
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hx
    funext i
    have hi := i.2
    simp only [aValOf, if_pos hi]
    have e : ∀ j < kl n (L.lv i.val), aVal n L (aRunL n L (extV L.D.nV x)) (.L i.val j) = limb (b n) (x i) j :=
      fun j hj => by
        rw [aVal_aRunL (valid_L.2 ⟨hi, hj⟩), Nat.mod_eq_of_lt (aRun_lt n L _ _ (by simp))]
        simp only [aRun, extV, dif_pos hi]
    rw [ofLimbs_congr (b n) (kl n (L.lv i.val)) e]
    exact ofLimbs_limb _ _ _ (hx.1 i)
  · intro ℓ hℓ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    have hall := aAllOK_iff.1 hℓ
    funext k
    apply Fin.ext
    show aRun n L (extV L.D.nV fun i => aValOf n L (aVal n L ℓ) i.val) (awOf n L k.val) % 2 ^ Wa n = _
    rw [extV_aValOf, ← aEq_run hL hall _ (awOf_valid k.2), aVal_awOf]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (ℓ k).2 (two_pow_Wa_sub_add n).le)

/-- **The value of the leveled network**: `LDesc.count n L` for `g ≥ 2` and well-formed `L`. -/
theorem arithNet_value {n g : ℕ} {L : LDesc} (hg : 2 ≤ g) (hL : L.WF n) :
    ((arithSys n L g hg).net (aLabCode n)).value = (L.count n : ℤ) := by
  rw [arithSys_value', arithNet_card hL]

end EthFollowup.Primes
