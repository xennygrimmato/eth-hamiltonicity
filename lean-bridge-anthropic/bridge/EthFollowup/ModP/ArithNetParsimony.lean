/-
# ArithNet, module L2 (part 2): parsimony and the value

`scratchpad/plans/modp-plan.md`, ADDENDUM §B; interface `modp-interface.md` (L2). Template:
`Factoring/MulNetParsimony.lean`; the stage lemmas are uniform per wire family.

* `aValOf n D x`: the variable values read off the limb wires `L v i`.
* Stage induction (`aEq_run`): for a well-formed `D`, if all checks pass on `x`, then `x` is the
  canonical assignment `aRun n D (aValOf n D x)` on every valid wire (signed carries by
  `SignedCarry.carryChk_unique`, comparison states by `Compare.cmpChain_unique`).
* `aRun_all_iff`: for `y` in the box, the canonical assignment passes every check iff `D.Sat (b n) y`
  (products by `pipeline_eq_mul`, chains by `schain_sum`/`carryChk_sR`, comparisons by `cmpCell_canon`,
  patterns by `patOK_iff_patMatch`).
* `aRunL` (the canonical labelling), `arithNet_card`, **`arithNet_value`**: the value of
  `arithSys n D g` is `Desc.count n D`.

Standard axioms only.
-/
import EthFollowup.ModP.ArithNetDefs
import EthFollowup.ModP.ArithBounds

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset EthFollowup.ExactHC EthFollowup.Factoring

/-! ## Limbs of constants, truncated sums, patterns -/

/-- Limb `i` of a constant, for every `i` (`0` beyond its length). -/
theorem limb_limbsVal_all {b : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ b) (i : ℕ) :
    limb b (limbsVal b l) i = l.getD i 0 := by
  by_cases hi : i < l.length
  · exact limb_limbsVal hl le_rfl hi
  · rw [List.getD_eq_default _ _ (by omega)]
    unfold limb
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le (limbsVal_lt hl le_rfl)
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))))]
    simp

/-- A sum over `range K` of a function vanishing from `m ≤ K` on. -/
theorem sum_range_trunc {K m : ℕ} (hm : m ≤ K) (f : ℕ → ℕ) (hf : ∀ k, m ≤ k → f k = 0) :
    ∑ k ∈ range K, f k = ∑ k ∈ range m, f k := by
  rw [← Finset.sum_range_add_sum_Ico _ hm, Finset.sum_eq_zero (fun k hk => hf k (Finset.mem_Ico.1 hk).1),
    add_zero]

theorem obit_eq_optBit : obit = optBit := by
  funext o x; cases o <;> rfl

/-- **The pattern cells**: all limbs of `y` match `pt` iff `y` matches `pt` (`|pt| ≤ nB`). -/
theorem patOK_iff_patMatch (n : ℕ) {pt : List (Option Bool)} (hpt : pt.length ≤ nB n) (y : ℕ) :
    (∀ i < ℓ n, patOK n pt i (limb (b n) y i) = true) ↔ patMatch pt y := by
  have hb := one_le_b n
  unfold patMatch
  constructor
  · intro h j hj
    have hj' : j < b n * ℓ n := by have := lt_of_lt_of_le hj hpt; unfold nB at this; rw [mul_comm]; exact this
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

/-! ## Operands under well-formedness -/

section Operands

variable {n : ℕ} {D : Desc}

theorem Desc.prods_mem {p : ℕ} (hp : p < D.nP) : D.prods.getD p default ∈ D.prods := by
  rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp
theorem Desc.ch_mem {c : ℕ} (hc : c < D.nC) : D.ch c ∈ D.chains := by
  unfold Desc.ch; rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc
theorem Desc.cq_mem {q : ℕ} (hq : q < D.nQ) : D.cq q ∈ D.cmps := by
  unfold Desc.cq; rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq

theorem pat_len_le (hD : D.WF n) (v : ℕ) : (D.pat.getD v []).length ≤ nB n := by
  by_cases hv : v < D.pat.length
  · rw [List.getD_eq_getElem _ _ hv]; exact hD.pat_len _ (List.getElem_mem hv)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem opnd_OK (hD : D.WF n) {p : ℕ} (hp : p < D.nP) (σ : ℕ) : (opnd D p σ).OK (b n) (ℓ n) D.nV := by
  have h := hD.prod_ok _ (Desc.prods_mem hp)
  unfold opnd; split_ifs
  · exact h.1
  · exact h.2

theorem cq_OK (hD : D.WF n) {q : ℕ} (hq : q < D.nQ) :
    (Operand.var (D.cq q).v).OK (b n) (ℓ n) D.nV ∧ (D.cq q).rhs.OK (b n) (ℓ n) D.nV :=
  hD.cmp_ok _ (Desc.cq_mem hq)

variable {y : ℕ → ℕ}

theorem eval_lt (hy : ∀ v < D.nV, y v < 2 ^ nB n) {o : Operand} (ho : o.OK (b n) (ℓ n) D.nV) :
    o.eval (b n) y < 2 ^ nB n := by
  cases o with
  | var v => exact hy v ho
  | const l => exact limbsVal_lt_nB ho.2 ho.1

theorem limb_eval {o : Operand} (ho : o.OK (b n) (ℓ n) D.nV) (i : ℕ) :
    limb (b n) (o.eval (b n) y) i = opLimbV n D y o i := by
  cases o with
  | var v => simp only [Operand.eval, opLimbV, if_pos (show v < D.nV from ho)]
  | const l => exact limb_limbsVal_all ho.2 i

theorem opLimbV_lt {o : Operand} (ho : o.OK (b n) (ℓ n) D.nV) (i : ℕ) : opLimbV n D y o i < 2 ^ b n := by
  cases o with
  | var v => simp only [opLimbV, if_pos (show v < D.nV from ho)]; exact limb_lt _ _ _
  | const l => exact getD_lt ho.2 i

theorem sum_opLimbV (hy : ∀ v < D.nV, y v < 2 ^ nB n) {o : Operand} (ho : o.OK (b n) (ℓ n) D.nV) :
    ∑ i ∈ range (ℓ n), opLimbV n D y o i * 2 ^ (b n * i) = o.eval (b n) y := by
  have h := ofLimbs_limb (b n) (o.eval (b n) y) (ℓ n) (by rw [mul_comm]; exact eval_lt hy ho)
  unfold ofLimbs at h
  rw [← h]
  exact sum_congr rfl fun i _ => by rw [limb_eval ho]

theorem opVal_lt (hD : D.WF n) (hy : ∀ v < D.nV, y v < 2 ^ nB n) {p : ℕ} (hp : p < D.nP) (σ : ℕ) :
    opVal n D y p σ < 2 ^ nB n := eval_lt hy (opnd_OK hD hp σ)

end Operands

theorem cmpT_congr {b L : ℕ} {yl pl yl' pl' : ℕ → ℕ} (hy : ∀ i < L, yl i = yl' i)
    (hp : ∀ i < L, pl i = pl' i) (j : ℕ) : cmpT b L yl pl j = cmpT b L yl' pl' j := by
  unfold cmpT hsuf
  congr 1
  · exact sum_congr rfl fun i hi => by rw [hy (j + i) (by have := mem_range.1 hi; omega)]
  · exact sum_congr rfl fun i hi => by rw [hp (j + i) (by have := mem_range.1 hi; omega)]

/-! ## Stage induction: all checks force the canonical assignment -/

/-- The variable values read off the limb wires (`0` beyond `nV`). -/
def aValOf (n : ℕ) (D : Desc) (x : AW → ℕ) (v : ℕ) : ℕ :=
  if v < D.nV then ofLimbs (b n) (fun i => x (.L v i)) (ℓ n) else 0

section Stages

variable {n : ℕ} {D : Desc} {x : AW → ℕ} (hD : D.WF n) (hall : ∀ v, v.Valid n D → aChk n D x v = true)
include hall

theorem cell_of_all {i : ℕ} (hi : i < ℓ n) :
    (∀ v < D.nV, x (.L v i) < 2 ^ b n ∧ patOK n (D.pat.getD v []) i (x (.L v i)) = true) ∧
    (∀ c < D.nC, ∀ v < D.nV, x (.Lc c v i) = x (.L v i)) ∧
    (∀ p < D.nP, ∀ σ < 2, x (.Lr p σ i) = opLimb D x (opnd D p σ) i) ∧
    (∀ q < D.nQ, cmpOK n D x q i = true) :=
  aChk_cell_iff.1 (hall (.cell i) (valid_cell.2 hi))

theorem L_lt_of_all {v : ℕ} (hv : v < D.nV) : ∀ i < ℓ n, x (.L v i) < 2 ^ b n := fun _ hi =>
  ((cell_of_all hall hi).1 v hv).1

theorem aValOf_lt (v : ℕ) : aValOf n D x v < 2 ^ nB n := by
  unfold aValOf
  split_ifs with hv
  · have := ofLimbs_lt (b n) _ (ℓ n) (L_lt_of_all hall hv)
    rwa [mul_comm] at this
  · positivity

theorem limb_aValOf {v i : ℕ} (hv : v < D.nV) (hi : i < ℓ n) : limb (b n) (aValOf n D x v) i = x (.L v i) := by
  unfold aValOf; rw [if_pos hv, limb_ofLimbs _ _ _ (L_lt_of_all hall hv) _ hi]

theorem opLimb_eq_V {o : Operand} (ho : o.OK (b n) (ℓ n) D.nV) {i : ℕ} (hi : i < ℓ n) :
    opLimb D x o i = opLimbV n D (aValOf n D x) o i := by
  cases o with
  | var v =>
    simp only [opLimb, opLimbV, if_pos (show v < D.nV from ho)]
    exact (limb_aValOf hall ho hi).symm
  | const l => rfl

theorem aEq_L {v i : ℕ} (hv : v < D.nV) (hi : i < ℓ n) : x (.L v i) = aRun n D (aValOf n D x) (.L v i) :=
  (limb_aValOf hall hv hi).symm

theorem aEq_Lc {c v i : ℕ} (hc : c < D.nC) (hv : v < D.nV) (hi : i < ℓ n) :
    x (.Lc c v i) = aRun n D (aValOf n D x) (.Lc c v i) := by
  rw [(cell_of_all hall hi).2.1 c hc v hv]; exact aEq_L hall hv hi

include hD in
theorem aEq_Lr {p σ i : ℕ} (hp : p < D.nP) (hσ : σ < 2) (hi : i < ℓ n) :
    x (.Lr p σ i) = limb (b n) (opVal n D (aValOf n D x) p σ) i := by
  rw [(cell_of_all hall hi).2.2.1 p hp σ hσ, opLimb_eq_V hall (opnd_OK hD hp σ) hi, opVal,
    limb_eval (opnd_OK hD hp σ)]

include hD in
theorem aPA {p σ i1 i2 : ℕ} (hp : p < D.nP) (hσ : σ < 2) (h1 : i1 < ℓ1 n) (h2 : i2 < ℓ2 n) :
    pA n (opVal n D (aValOf n D x) p σ) i1 i2 = x (.Lr p σ (i1 + ℓ1 n * i2)) :=
  (aEq_Lr hD hall hp hσ (blk_lt h1 h2)).symm

include hD in
theorem aEq_A {p σ s i2 : ℕ} (hp : p < D.nP) (hσ : σ < 2) (hs : s < L1 n) (h2 : i2 < ℓ2 n) :
    x (.A p σ s i2) = stA n (opVal n D (aValOf n D x) p σ) s i2 := by
  rw [(aChk_row_iff.1 (hall _ (valid_row.2 ⟨hp, hσ, h2⟩))) s hs]
  exact rowDFT_congr n (fun i1 hi1 => (aPA hD hall hp hσ hi1 h2).symm) s

include hD in
theorem aEq_F {p σ s t : ℕ} (hp : p < D.nP) (hσ : σ < 2) (hs : s < L1 n) (ht : t < L2 n) :
    x (.F p σ s t) = stF n (opVal n D (aValOf n D x) p σ) s t := by
  rw [(aChk_col_iff.1 (hall _ (valid_col.2 ⟨hp, hσ, hs⟩))) t ht]
  exact colDFT_congr n (fun i2 hi2 => aEq_A hD hall hp hσ hs hi2) t

include hD in
theorem aEq_C {p s t : ℕ} (hp : p < D.nP) (hs : s < L1 n) (ht : t < L2 n) :
    x (.C p s t) = stC n (opVal n D (aValOf n D x) p 0) (opVal n D (aValOf n D x) p 1) s t := by
  rw [aChk_mul_iff.1 (hall _ (valid_mul.2 ⟨hp, hs, ht⟩)), aEq_F hD hall hp (by norm_num) hs ht,
    aEq_F hD hall hp (by norm_num) hs ht]
  rfl

include hD in
theorem aEq_Dd {p s u : ℕ} (hp : p < D.nP) (hs : s < L1 n) (hu : u < L2 n) :
    x (.Dd p s u) = stD n (opVal n D (aValOf n D x) p 0) (opVal n D (aValOf n D x) p 1) s u := by
  rw [(aChk_icol_iff.1 (hall _ (valid_icol.2 ⟨hp, hs⟩))) u hu]
  exact invCol_congr n (fun t ht => aEq_C hD hall hp hs ht) u

include hD in
theorem aEq_E {p a u : ℕ} (hp : p < D.nP) (ha : a < L1 n) (hu : u < L2 n) :
    x (.E p a u) = stE n (opVal n D (aValOf n D x) p 0) (opVal n D (aValOf n D x) p 1) a u := by
  rw [(aChk_irow_iff.1 (hall _ (valid_irow.2 ⟨hp, hu⟩))) a ha]
  exact invRow_congr n (fun s hs => aEq_Dd hD hall hp hs hu) a

include hD in
theorem aEq_tDig {c : ℕ} (hc : c < D.nC) (t : Term) (k : ℕ) :
    tDig n D x c t k = cDig n D (aValOf n D x) c t k := by
  obtain ⟨a, src⟩ := t
  cases src with
  | prod p =>
    simp only [tDig, cDig]
    split_ifs with hp
    · exact convCoeff_congr n fun _ ha _ hu _ => aEq_E hD hall hp.1 ha hu
    · rfl
  | lin v =>
    simp only [tDig, cDig]
    split_ifs with hv
    · exact aEq_Lc hall hc hv.1 hv.2
    · rfl
  | const l => rfl

include hD in
theorem aEq_sDig {c : ℕ} (hc : c < D.nC) (ts : List Term) :
    sDig n D x c ts = cSide n D (aValOf n D x) c ts := by
  funext k; simp only [sDig, cSide, aEq_tDig hD hall hc]

include hD in
theorem aEq_rr {c j : ℕ} (hc : c < D.nC) (hj : j + 1 < Kc n) :
    x (.rr c j) = aRun n D (aValOf n D x) (.rr c j) := by
  have h : ∀ k < Kc n, carryChk (b n) (Kc n) (aOFF n) (cSide n D (aValOf n D x) c (D.ch c).lhs)
      (cSide n D (aValOf n D x) c (D.ch c).rhs) (fun j => x (.rr c j)) k := fun k hk => by
    have := aChk_carry_iff.1 (hall _ (valid_carry.2 ⟨hc, hk⟩))
    rwa [aEq_sDig hD hall hc, aEq_sDig hD hall hc] at this
  exact carryChk_unique h j hj

include hD in
theorem aEq_st {q j : ℕ} (hq : q < D.nQ) (hj : j + 1 < ℓ n) :
    x (.st q j) = aRun n D (aValOf n D x) (.st q j) := by
  obtain ⟨h1, h2⟩ := cq_OK hD hq
  have hyl : ∀ i < ℓ n, opLimb D x (.var (D.cq q).v) i < 2 ^ b n := fun i hi => by
    rw [opLimb_eq_V hall h1 hi]; exact opLimbV_lt h1 i
  have hpl : ∀ i < ℓ n, opLimb D x (D.cq q).rhs i < 2 ^ b n := fun i hi => by
    rw [opLimb_eq_V hall h2 hi]; exact opLimbV_lt h2 i
  have hcell : ∀ i < ℓ n, cmpCell (D.cq q).rel (ℓ n) (opLimb D x (.var (D.cq q).v))
      (opLimb D x (D.cq q).rhs) (fun j => x (.st q j)) i = true := fun i hi =>
    (cell_of_all hall hi).2.2.2 q hq
  rw [cmpChain_unique hyl hpl hcell j hj]
  exact cmpT_congr (fun i hi => opLimb_eq_V hall h1 hi) (fun i hi => opLimb_eq_V hall h2 hi) _

include hD in
/-- **Stage induction**: if every check passes on `x`, then `x` is the canonical assignment of the
variable values read off its limb wires, on every valid wire. -/
theorem aEq_run : ∀ d, d.Valid n D → x d = aRun n D (aValOf n D x) d := by
  intro d hd
  cases d with
  | L v i => exact aEq_L hall (valid_L.1 hd).1 (valid_L.1 hd).2
  | Lc c v i => exact aEq_Lc hall (valid_Lc.1 hd).1 (valid_Lc.1 hd).2.1 (valid_Lc.1 hd).2.2
  | Lr p σ i => exact aEq_Lr hD hall (valid_Lr.1 hd).1 (valid_Lr.1 hd).2.1 (valid_Lr.1 hd).2.2
  | A p σ s i2 => exact aEq_A hD hall (valid_A.1 hd).1 (valid_A.1 hd).2.1 (valid_A.1 hd).2.2.1 (valid_A.1 hd).2.2.2
  | F p σ s t => exact aEq_F hD hall (valid_F.1 hd).1 (valid_F.1 hd).2.1 (valid_F.1 hd).2.2.1 (valid_F.1 hd).2.2.2
  | C p s t => exact aEq_C hD hall (valid_C.1 hd).1 (valid_C.1 hd).2.1 (valid_C.1 hd).2.2
  | Dd p s u => exact aEq_Dd hD hall (valid_Dd.1 hd).1 (valid_Dd.1 hd).2.1 (valid_Dd.1 hd).2.2
  | E p a u => exact aEq_E hD hall (valid_E.1 hd).1 (valid_E.1 hd).2.1 (valid_E.1 hd).2.2
  | rr c j => exact aEq_rr hD hall (valid_rr.1 hd).1 (valid_rr.1 hd).2
  | st q j => exact aEq_st hD hall (valid_st.1 hd).1 (valid_st.1 hd).2

end Stages

/-! ## The canonical assignment passes all checks iff the variables satisfy `D` -/

section Canon

variable {n : ℕ} {D : Desc} {y : ℕ → ℕ} (hD : D.WF n) (hy : ∀ v < D.nV, y v < 2 ^ nB n)

include hD hy in
/-- The positional sum of a canonical term digit is the value of the term. -/
theorem sum_cDig {c : ℕ} (hc : c < D.nC) {t : Term} (ht : t ∈ (D.ch c).lhs ++ (D.ch c).rhs) :
    ∑ k ∈ range (Kc n), cDig n D y c t k * 2 ^ (b n * k) = t.src.eval (b n) D.prods y := by
  have hok := hD.term_ok _ (Desc.ch_mem hc) t ht
  obtain ⟨a, src⟩ := t
  cases src with
  | prod p =>
    have hp : p < D.nP := hok
    have hcp : D.chainOf p = c := Desc.chainOf_eq hD hc ⟨_, ht, rfl⟩
    simp only [cDig, if_pos (show p < D.nP ∧ D.chainOf p = c from ⟨hp, hcp⟩)]
    rw [ofLimbs_stc n _ _ (opVal_lt hD hy hp 0) (opVal_lt hD hy hp 1)]
    simp [opVal, opnd, Src.eval, ProdD.eval, Operand.eval]
  | lin v =>
    have hv : v < D.nV := hok
    simp only [cDig, Src.eval, hv, true_and]
    exact sum_limb_pad n (y v) (hy v hv)
  | const l =>
    simp only [cDig, Src.eval]
    rw [sum_pad_eq n _ (fun k hk => List.getD_eq_default _ _ (by have := hok.1; omega)),
      limbsVal_eq_ofLimbs (b n) l hok.1]

include hD hy in
theorem sum_cSide {c : ℕ} (hc : c < D.nC) {ts : List Term} (hts : ∀ t ∈ ts, t ∈ (D.ch c).lhs ++ (D.ch c).rhs) :
    ∑ k ∈ range (Kc n), cSide n D y c ts k * 2 ^ (b n * k) = sideVal (b n) D.prods y ts := by
  unfold cSide sideVal
  rw [sum_lin ts Term.coeff (cDig n D y c) (b n) (Kc n)]
  congr 1
  exact List.map_congr_left fun t ht => by rw [sum_cDig hD hy hc (hts t ht)]

include hD in
theorem cSide_le {c : ℕ} (hc : c < D.nC) {ts : List Term} (hm : (ts.map Term.coeff).sum ≤ 32)
    (hts : ∀ t ∈ ts, t ∈ (D.ch c).lhs ++ (D.ch c).rhs) (k : ℕ) :
    cSide n D y c ts k ≤ aOFF n * (2 ^ b n - 1) := by
  refine side_le_OFF_terms n ts (fun t => cDig n D y c t k) hm fun t ht => ?_
  have hok := hD.term_ok _ (Desc.ch_mem hc) t (hts t ht)
  obtain ⟨a, src⟩ := t
  cases src with
  | prod p => simp only [cDig]; split_ifs; exacts [stc_le_pow n _ _ k, Nat.zero_le _]
  | lin v => simp only [cDig]; split_ifs; exacts [limb_le_pow n _ k, Nat.zero_le _]
  | const l => exact getD_le_pow hok.2 k

theorem mem_sides_l {ch : ChainD} : ∀ t ∈ ch.lhs, t ∈ ch.lhs ++ ch.rhs := fun _ h => List.mem_append_left _ h
theorem mem_sides_r {ch : ChainD} : ∀ t ∈ ch.rhs, t ∈ ch.lhs ++ ch.rhs := fun _ h => List.mem_append_right _ h

include hD hy in
/-- **The carries of chain `c`**: the canonical carry checks pass iff the chain holds. -/
theorem carries_iff {c : ℕ} (hc : c < D.nC) :
    (∀ k < Kc n, aChk n D (aRun n D y) (.carry c k) = true) ↔
      sideVal (b n) D.prods y (D.ch c).lhs = sideVal (b n) D.prods y (D.ch c).rhs := by
  have hm := hD.coeff_le _ (Desc.ch_mem hc)
  simp only [aChk_run_carry]
  rw [← sum_cSide hD hy hc mem_sides_l, ← sum_cSide hD hy hc mem_sides_r]
  constructor
  · intro h
    exact schain_sum ((schainW_iff _ _ _ _ _ _).1 h)
  · intro hs
    exact carryChk_sR (fun k _ => cSide_le hD hc hm.1 mem_sides_l k)
      (fun k _ => cSide_le hD hc hm.2 mem_sides_r k) hs

include hD hy in
/-- **Comparison `q`**: the canonical comparison steps pass at every cell iff the relation holds. -/
theorem cmps_iff {q : ℕ} (hq : q < D.nQ) :
    (∀ i < ℓ n, cmpCell (D.cq q).rel (ℓ n) (opLimbV n D y (.var (D.cq q).v)) (opLimbV n D y (D.cq q).rhs)
      (fun j => cmpT (b n) (ℓ n) (opLimbV n D y (.var (D.cq q).v)) (opLimbV n D y (D.cq q).rhs) (j + 1)) i = true) ↔
      (D.cq q).rel.Holds (y (D.cq q).v) ((D.cq q).rhs.eval (b n) y) := by
  obtain ⟨h1, h2⟩ := cq_OK hD hq
  have hl := ℓ_pos n
  have key := fun i (hi : i < ℓ n) => cmpCell_canon (D.cq q).rel (b := b n) (L := ℓ n)
    (fun i _ => opLimbV_lt (y := y) h1 i) (fun i _ => opLimbV_lt (y := y) h2 i) hi
  rw [sum_opLimbV hy h1, sum_opLimbV hy h2] at key
  constructor
  · intro h; exact (key 0 hl).1 (h 0 hl) rfl
  · intro h i hi; exact (key i hi).2 fun _ => h

include hD hy in
/-- **Parsimony, canonical direction**: for `y` in the box, the canonical assignment passes every
check iff `y` satisfies `D`. -/
theorem aRun_all_iff : (∀ v, v.Valid n D → aChk n D (aRun n D y) v = true) ↔ D.Sat (b n) y := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun q hq => ?_, fun ch hch => ?_⟩
    · exact (patOK_iff_patMatch n (pat_len_le hD v) (y v)).1 fun i hi =>
        (((aChk_run_cell n D y i).1 (h _ (valid_cell.2 hi))).1 v hv).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
      have e : D.cq j = D.cmps[j] := List.getD_eq_getElem _ _ hj
      rw [← e]
      exact (cmps_iff hD hy hj).1 fun i hi => ((aChk_run_cell n D y i).1 (h _ (valid_cell.2 hi))).2.2 j hj
    · obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hch
      have e : D.ch c = D.chains[c] := List.getD_eq_getElem _ _ hc
      rw [← e]
      exact (carries_iff hD hy hc).1 fun k hk => h _ (valid_carry.2 ⟨hc, hk⟩)
  · rintro ⟨hpat, hcmp, hch⟩ v hv
    cases v with
    | cell i =>
      have hi := valid_cell.1 hv
      refine (aChk_run_cell n D y i).2 ⟨fun w hw => ⟨limb_lt _ _ _,
        (patOK_iff_patMatch n (pat_len_le hD w) (y w)).2 (hpat w hw) i hi⟩,
        fun p hp σ _ => limb_eval (opnd_OK hD hp σ) i, fun q hq => ?_⟩
      exact (cmps_iff hD hy hq).2 (hcmp _ (Desc.cq_mem hq)) i hi
    | row p σ i2 => exact aChk_run_row n D y p σ i2
    | col p σ s => exact aChk_run_col n D y p σ s
    | mul p s t => exact aChk_run_mul n D y p s t
    | icol p s => exact aChk_run_icol n D y p s
    | irow p u => exact aChk_run_irow n D y p u
    | carry c k =>
      obtain ⟨hc, hk⟩ := valid_carry.1 hv
      exact (carries_iff hD hy hc).2 (hch _ (Desc.ch_mem hc)) k hk

include hD hy in
/-- For satisfying `y`, every canonical value fits in `Wa` bits (carries in `(0, 2 aOFF)`). -/
theorem aRun_lt_of_sat (hs : D.Sat (b n) y) {d : AW} (hd : d.Valid n D) : aRun n D y d < 2 ^ Wa n := by
  by_cases h : ∃ c j, d = .rr c j
  · obtain ⟨c, j, rfl⟩ := h
    obtain ⟨hc, hj⟩ := valid_rr.1 hd
    have hm := hD.coeff_le _ (Desc.ch_mem hc)
    have hsum := (sum_cSide hD hy hc mem_sides_l).trans ((hs.2.2 _ (Desc.ch_mem hc)).trans
      (sum_cSide hD hy hc mem_sides_r).symm)
    have := sR_range (fun k _ => cSide_le hD hc hm.1 mem_sides_l k)
      (fun k _ => cSide_le hD hc hm.2 mem_sides_r k) hsum
      (show 0 < aOFF n by unfold aOFF; positivity) (k := j + 1) hj.le
    exact carry_lt_Wa n _ this.2
  · exact aRun_lt n D y d fun c j hj => h ⟨c, j, hj⟩

end Canon

/-! ## The canonical labelling and the value -/

/-- **The canonical labelling** of `y` (values reduced mod `2^Wa`; exact for satisfying `y`). -/
def aRunL (n : ℕ) (D : Desc) (y : ℕ → ℕ) : Fin (numAW n D) → ALab n := fun k =>
  ⟨aRun n D y (awOf n D k.val) % 2 ^ Wa n, by rw [two_pow_Wa_sub_add]; exact Nat.mod_lt _ (by positivity)⟩

theorem aVal_aRunL {n : ℕ} {D : Desc} {y : ℕ → ℕ} {d : AW} (hd : d.Valid n D) :
    aVal n D (aRunL n D y) d = aRun n D y d % 2 ^ Wa n := by
  rw [aVal_of_valid _ hd]
  show aRun n D y (awOf n D (awIdx n D d)) % _ = _
  rw [awOf_awIdx hd]

theorem extV_aValOf (n : ℕ) (D : Desc) (x : AW → ℕ) :
    extV D.nV (fun i : Fin D.nV => aValOf n D x i.val) = aValOf n D x := by
  funext v
  unfold extV
  split_ifs with hv
  · rfl
  · unfold aValOf; rw [if_neg hv]

/-- **Parsimony**: for well-formed `D`, the labellings passing every check are in bijection with
the tuples counted by `Desc.count n D`. -/
theorem arithNet_card {n : ℕ} {D : Desc} (hD : D.WF n) :
    #(univ.filter fun ℓ : Fin (numAW n D) → ALab n => aAllOK n D (aVal n D ℓ) = true) = D.count n := by
  unfold Desc.count Desc.countB
  symm
  refine card_nbij' (fun x => aRunL n D (extV D.nV x)) (fun ℓ i => aValOf n D (aVal n D ℓ) i.val)
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hx
    obtain ⟨hbox, hs⟩ := hx
    have hy : ∀ v < D.nV, extV D.nV x v < 2 ^ nB n := fun v hv => by
      simp only [extV, dif_pos hv]; exact hbox _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    refine aAllOK_iff.2 fun v hv => ?_
    rw [aChk_agree hv fun d hd _ => by
      rw [aVal_aRunL hd, Nat.mod_eq_of_lt (aRun_lt_of_sat hD hy hs hd)]]
    exact (aRun_all_iff hD hy).2 hs v hv
  · intro ℓ hℓ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    have hall := aAllOK_iff.1 hℓ
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq]
    refine ⟨fun i => aValOf_lt hall i.val, ?_⟩
    rw [extV_aValOf]
    refine (aRun_all_iff hD (fun v _ => aValOf_lt hall v)).1 fun v hv => ?_
    rw [← aChk_agree hv fun d hd _ => aEq_run hD hall d hd]
    exact hall v hv
  · intro x hx
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hx
    funext i
    have hi := i.2
    simp only [aValOf, if_pos hi]
    have e : ∀ j < ℓ n, aVal n D (aRunL n D (extV D.nV x)) (.L i.val j) = limb (b n) (x i) j := fun j hj => by
      rw [aVal_aRunL (valid_L.2 ⟨hi, hj⟩), Nat.mod_eq_of_lt (aRun_lt n D _ _ (by simp))]
      simp only [aRun, extV, dif_pos hi]
    rw [ofLimbs_congr (b n) (ℓ n) e]
    exact ofLimbs_limb _ _ _ (by rw [mul_comm]; exact hx.1 i)
  · intro ℓ hℓ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    have hall := aAllOK_iff.1 hℓ
    funext k
    apply Fin.ext
    show aRun n D (extV D.nV fun i => aValOf n D (aVal n D ℓ) i.val) (awOf n D k.val) % 2 ^ Wa n = _
    rw [extV_aValOf, ← aEq_run hD hall _ (awOf_valid k.2), aVal_awOf]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (ℓ k).2 (two_pow_Wa_sub_add n).le)

/-- **The value of the arithmetic-constraint network**: for `g ≥ 2` and a well-formed description,
the network `arithSys n D g` has value `Desc.count n D = #{x ∈ [0, 2^{nB n})^{nV} : x satisfies D}`. -/
theorem arithNet_value {n g : ℕ} {D : Desc} (hg : 2 ≤ g) (hD : D.WF n) :
    ((arithSys n D g hg).net (aLabCode n)).value = (D.count n : ℤ) := by
  rw [arithSys_value', arithNet_card hD]

end EthFollowup.ModP
