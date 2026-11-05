/-
# The Horner-chain packages and machines (roots-plan.md §4, H6)

For a fixed degree `d ≥ 1`, the description reader `hornerDesc` at size `n = |w| / (d+2)` (or `/(d+3)` for
the next root), the modulus `m` read from block 0, the reduced coefficients `rdCo d w` (`rdCoN d w`),
and the lower bound `lo = 0` (resp. block 1), is an `ArithSpec` with `cD = 64(5d+2)(d+1)`:

* `rdBlk_polyT'`, `rdCo_polyT`, `rdCoN_polyT` (the readers of SpecHorner);
* `arithRoot d hd`, `arithNext d hd` (the root counts), with `arithRoot_Q`, `arithNext_Q`, `arithCnt_Q`;
* `polyRoot_TM_of`, `nextRoot_TM_of`, `rootCount_TM_of`: given the polynomial-time table and reader, the
  machine statements of `FinalRoots.lean` (plus totality: the machine halts in the bound on EVERY word).

Standard axioms only.
-/
import EthFollowup.ModP.ArithPkgs
import EthFollowup.ModP.HornerPoly
import EthFollowup.ModP.SpecHorner

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring

/-! ## Readers -/

theorem rdBlk_polyT' {α : Type} [Enc α] (nb : ℕ) {j : α → ℕ} {w : α → List Bool} (hj : PolyT j)
    (hw : PolyT w) : PolyT fun x => rdBlk nb (j x) (w x) := by
  unfold rdBlk
  exact blkVal_polyT hw (PolyT.const nb) hj

theorem rdCo_polyT (d : ℕ) : PolyT (rdCo d) := by
  unfold rdCo
  have hfst : PolyT fun q : List Bool × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : List Bool × ℕ => q.2 := PolyT.snd PolyT.id'
  exact PolyT.map (f := fun w i => rdBlk (d + 2) (i + 1) w % rdBlk (d + 2) 0 w)
    (PolyT.mod (rdBlk_polyT' (d + 2) (PolyT.add hs (PolyT.const 1)) hfst)
      (rdBlk_polyT' (d + 2) (PolyT.const 0) hfst))
    (PolyT.range (Unary.const (d + 1)))

theorem rdCoN_polyT (d : ℕ) : PolyT (rdCoN d) := by
  unfold rdCoN
  have hfst : PolyT fun q : List Bool × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : List Bool × ℕ => q.2 := PolyT.snd PolyT.id'
  exact PolyT.map (f := fun w i => rdBlk (d + 3) (i + 2) w % rdBlk (d + 3) 0 w)
    (PolyT.mod (rdBlk_polyT' (d + 3) (PolyT.add hs (PolyT.const 2)) hfst)
      (rdBlk_polyT' (d + 3) (PolyT.const 0) hfst))
    (PolyT.range (Unary.const (d + 1)))

theorem length_rdCo (d : ℕ) (w : List Bool) : (rdCo d w).length = d + 1 := by simp [rdCo]

theorem length_rdCoN (d : ℕ) (w : List Bool) : (rdCoN d w).length = d + 1 := by simp [rdCoN]

theorem rdCo_lt (d : ℕ) (w : List Bool) (hm : 0 < rdBlk (d + 2) 0 w) :
    ∀ c ∈ rdCo d w, c < rdBlk (d + 2) 0 w := by
  intro c hc
  simp only [rdCo, List.mem_map, List.mem_range] at hc
  obtain ⟨i, -, rfl⟩ := hc
  exact Nat.mod_lt _ hm

theorem rdCoN_lt (d : ℕ) (w : List Bool) (hm : 0 < rdBlk (d + 3) 0 w) :
    ∀ c ∈ rdCoN d w, c < rdBlk (d + 3) 0 w := by
  intro c hc
  simp only [rdCoN, List.mem_map, List.mem_range] at hc
  obtain ⟨i, -, rfl⟩ := hc
  exact Nat.mod_lt _ hm

/-! ## The shape constant -/

/-- `cA` of every Horner description of degree `d ≥ 1`. -/
def hornerCD (d : ℕ) : ℕ := 64 * ((5 * d + 2) * (d + 1))

theorem cA_hornerDesc_le {d : ℕ} (hd : 1 ≤ d) (b ℓ n m : ℕ) (a : List ℕ) (lo : ℕ) (π : List Bool) :
    cA (hornerDesc b ℓ n d m a lo π) ≤ hornerCD d := by
  simp only [cA, Desc.nP, Desc.nQ, Desc.nC, hornerDesc, hornerCD, List.length_map, List.length_range,
    List.length_append, List.length_cons, List.length_nil]
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_right
  omega

/-! ## The specifications -/

/-- **The least root**: `n = R = |w|/(d+2)`, `m` = block 0, coefficients `rdCo d w`, `lo = 0`. -/
def arithRoot (d : ℕ) (hd : 1 ≤ d) : ArithSpec where
  nf w := w.length / (d + 2)
  nf_le _ := Nat.div_le_self _ _
  nf_unary := blk_unary (d + 2)
  R w := w.length / (d + 2)
  R_le _ := Nat.div_le_self _ _
  R_poly := (blk_unary (d + 2)).poly
  desc y := hornerDesc (b (y.1.length / (d + 2))) (ℓ (y.1.length / (d + 2))) (y.1.length / (d + 2)) d
    (rdBlk (d + 2) 0 y.1) (rdCo d y.1) 0 y.2
  desc_poly := by
    have hn := blk_fst_unary (d + 2)
    exact hornerDesc_polyT d (b_unary hn) (ℓ_unary hn) hn
      ((rdBlk_polyT (d + 2) 0).comp (PolyT.fst PolyT.id')) ((rdCo_polyT d).comp (PolyT.fst PolyT.id'))
      (PolyT.const 0) (PolyT.snd PolyT.id')
  cD := hornerCD d
  cA_le _ := cA_hornerDesc_le hd _ _ _ _ _ _ _
  wf _ _ _ := hornerDesc_WF hd (le_nB _)

/-- **The least root `≥ lo`**: `n = R = |w|/(d+3)`, `m` = block 0, `lo` = block 1, coefficients `rdCoN d w`. -/
def arithNext (d : ℕ) (hd : 1 ≤ d) : ArithSpec where
  nf w := w.length / (d + 3)
  nf_le _ := Nat.div_le_self _ _
  nf_unary := blk_unary (d + 3)
  R w := w.length / (d + 3)
  R_le _ := Nat.div_le_self _ _
  R_poly := (blk_unary (d + 3)).poly
  desc y := hornerDesc (b (y.1.length / (d + 3))) (ℓ (y.1.length / (d + 3))) (y.1.length / (d + 3)) d
    (rdBlk (d + 3) 0 y.1) (rdCoN d y.1) (rdBlk (d + 3) 1 y.1) y.2
  desc_poly := by
    have hn := blk_fst_unary (d + 3)
    exact hornerDesc_polyT d (b_unary hn) (ℓ_unary hn) hn
      ((rdBlk_polyT (d + 3) 0).comp (PolyT.fst PolyT.id')) ((rdCoN_polyT d).comp (PolyT.fst PolyT.id'))
      ((rdBlk_polyT (d + 3) 1).comp (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id')
  cD := hornerCD d
  cA_le _ := cA_hornerDesc_le hd _ _ _ _ _ _ _
  wf _ _ _ := hornerDesc_WF hd (le_nB _)

/-- The root count uses the least-root reader (queried with the empty pattern). -/
abbrev arithCnt (d : ℕ) (hd : 1 ≤ d) : ArithSpec := arithRoot d hd

theorem blk_lt_bl (nb j : ℕ) (w : List Bool) :
    rdBlk nb j w < 2 ^ (b (w.length / nb) * ℓ (w.length / nb)) :=
  (rdBlk_lt nb j w).trans_le (two_pow_le_bl (lt_nB _).le)

theorem arithRoot_Q (d : ℕ) (hd : 1 ≤ d) (w π : List Bool) (hm : 0 < rdBlk (d + 2) 0 w)
    (hπ : π.length ≤ w.length / (d + 2)) :
    ((arithRoot d hd).desc (w, π)).count ((arithRoot d hd).nf w) =
      ((Finset.range (rdBlk (d + 2) 0 w)).filter fun x =>
        polyEvalMod (rdBlk (d + 2) 0 w) (rdCo d w) x = 0 ∧
          x / 2 ^ (w.length / (d + 2) - π.length) = Search.ofWord π).card := by
  have h := hornerDesc_count hd (length_rdCo d w) hm (rdCo_lt d w hm) (blk_lt_bl (d + 2) 0 w)
    (Nat.two_pow_pos _) (rdBlk_lt (d + 2) 0 w).le (le_nB (w.length / (d + 2))) hπ
  simp only [zero_le, true_and] at h
  exact h

theorem arithNext_Q (d : ℕ) (hd : 1 ≤ d) (w π : List Bool) (hm : 0 < rdBlk (d + 3) 0 w)
    (hπ : π.length ≤ w.length / (d + 3)) :
    ((arithNext d hd).desc (w, π)).count ((arithNext d hd).nf w) =
      ((Finset.range (rdBlk (d + 3) 0 w)).filter fun x => rdBlk (d + 3) 1 w ≤ x ∧
        polyEvalMod (rdBlk (d + 3) 0 w) (rdCoN d w) x = 0 ∧
          x / 2 ^ (w.length / (d + 3) - π.length) = Search.ofWord π).card :=
  hornerDesc_count hd (length_rdCoN d w) hm (rdCoN_lt d w hm) (blk_lt_bl (d + 3) 0 w)
    (blk_lt_bl (d + 3) 1 w) (rdBlk_lt (d + 3) 0 w).le (le_nB (w.length / (d + 3))) hπ

theorem arithCnt_Q (d : ℕ) (hd : 1 ≤ d) (w : List Bool) (hm : 0 < rdBlk (d + 2) 0 w) :
    ((arithCnt d hd).desc (w, [])).count ((arithCnt d hd).nf w) =
      (rootSetP (rdBlk (d + 2) 0 w) (rdCo d w)).card := by
  rw [arithRoot_Q d hd w [] hm (Nat.zero_le _), rootSetP]
  congr 1
  apply Finset.filter_congr
  intro x hx
  have hx' : x < 2 ^ (w.length / (d + 2)) := (Finset.mem_range.1 hx).trans (rdBlk_lt _ _ _)
  simp [Nat.div_eq_of_lt hx']

/-! ## The machines, given the polynomial-time table and reader -/

/-- **Least root modulo any `m` of a degree-`≤ d` polynomial**, given the table and reader; the machine
also halts within the bound on every word. -/
theorem polyRoot_TM_of (d : ℕ) (hd : 1 ≤ d) (hT : PolyT tabAF) (hp : PolyT (arithRoot d hd).prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ (m : ℕ) (a : List ℕ), a.length = d + 1 →
        GraphProblems.Outputs M (encodeList (m :: a)) (Computability.encodeNat (minRootP m a))
          ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodeList (m :: a)).length /
            Real.sqrt (Real.logb 2 ((encodeList (m :: a)).length + 2)))⌋₊) ∧
      ∀ w : List Bool, ∃ y, GraphProblems.Outputs M w y
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := (arithRoot d hd).pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.searchM_TM pk (specP d) (specP_pre_polyT d) (specP_small_polyT d)
    (specP_step_polyT d) (specP_fin_polyT d) (specP_step_length d) (fun w π _ => specP_fin_length d w π)
    (specP_small_length d) (fun w _ => hOk w)
  refine ⟨M, C, hfin, fun m a hlen => ?_, fun w => ⟨_, h w⟩⟩
  have e := specP_answer_list pk d m a hlen (hR _) fun hm2 π hπ => by
    rw [hQ, arithRoot_Q d hd _ _ (by rw [rdBlk_encodeList_zero d m a hlen]; omega)
      (by simp only [List.length_append, List.length_singleton]; omega),
      rdBlk_encodeList_zero d m a hlen, rdCo_encodeList d m a hlen]
  have := h (encodeList (m :: a))
  rwa [e] at this

/-- **Least root `≥ lo`**, given the table and reader (and totality). -/
theorem nextRoot_TM_of (d : ℕ) (hd : 1 ≤ d) (hT : PolyT tabAF) (hp : PolyT (arithNext d hd).prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ (m lo : ℕ) (a : List ℕ), a.length = d + 1 →
        GraphProblems.Outputs M (encodeList (m :: lo :: a)) (Computability.encodeNat (nextRootP m a lo))
          ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodeList (m :: lo :: a)).length /
            Real.sqrt (Real.logb 2 ((encodeList (m :: lo :: a)).length + 2)))⌋₊) ∧
      ∀ w : List Bool, ∃ y, GraphProblems.Outputs M w y
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := (arithNext d hd).pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.searchM_TM pk (specNext d) (specNext_pre_polyT d)
    (specNext_small_polyT d) (specNext_step_polyT d) (specNext_fin_polyT d) (specNext_step_length d)
    (fun w π _ => specNext_fin_length d w π) (specNext_small_length d) (fun w _ => hOk w)
  refine ⟨M, C, hfin, fun m lo a hlen => ?_, fun w => ⟨_, h w⟩⟩
  have e := specNext_answer_list pk d m lo a hlen (hR _) fun hm2 π hπ => by
    rw [hQ, arithNext_Q d hd _ _ (by rw [rdBlk_encodeList_zero' d m lo a hlen]; omega)
      (by simp only [List.length_append, List.length_singleton]; omega),
      rdBlk_encodeList_zero' d m lo a hlen, rdBlk_encodeList_one d m lo a hlen,
      rdCoN_encodeList d m lo a hlen]
  have := h (encodeList (m :: lo :: a))
  rwa [e] at this

/-- **Number of roots modulo `m`**, given the table and reader (and totality). -/
theorem rootCount_TM_of (d : ℕ) (hd : 1 ≤ d) (hT : PolyT tabAF) (hp : PolyT (arithCnt d hd).prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ (m : ℕ) (a : List ℕ), a.length = d + 1 →
        GraphProblems.Outputs M (encodeList (m :: a)) (Computability.encodeNat (rootSetP m a).card)
          ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodeList (m :: a)).length /
            Real.sqrt (Real.logb 2 ((encodeList (m :: a)).length + 2)))⌋₊) ∧
      ∀ w : List Bool, ∃ y, GraphProblems.Outputs M w y
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := (arithCnt d hd).pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk (specCnt d) (specCnt_pre_polyT d) (specCnt_small_polyT d)
    (specCnt_q1_polyT d) (specCnt_q2_polyT d) (specCnt_fin_polyT d)
    (fun w => specCnt_length pk d w (fun _ => hOk w)) (fun w _ => hOk w)
    (fun w _ => by simp [specCnt]) (fun w _ => by simp [specCnt])
  refine ⟨M, C, hfin, fun m a hlen => ?_, fun w => ⟨_, h w⟩⟩
  have e := specCnt_answer_list pk d m a hlen fun hm => by
    rw [hQ, arithCnt_Q d hd _ (by rw [rdBlk_encodeList_zero d m a hlen]; omega),
      rdBlk_encodeList_zero d m a hlen, rdCo_encodeList d m a hlen]
  have := h (encodeList (m :: a))
  rwa [e] at this

end EthFollowup.ModP
