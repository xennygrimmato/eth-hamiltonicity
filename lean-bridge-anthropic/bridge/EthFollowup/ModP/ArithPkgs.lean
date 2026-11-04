/-
# The instance packages: (E) class numbers, (A) square roots, (B) least non-residues, (F) lattice sums

`scratchpad/plans/modp-plan.md`, ADDENDUM §B (instances) and §2. Each instance is an `ArithSpec`
(`ArithPackage.lean`) built from E1's descriptions (`ArithInstances`, `ArithReaderPoly`); its
package answers the queries of E2's specifications (`SpecSq`, `SpecE`, `SpecLattice`), and
`GR.searchM_TM` / `GR.queryM_TM` give the machines. The polynomial-time table `tabAF` and reader
`A.prep` (module ArithPoly) are hypotheses here (`*_TM_of`); `Final.lean` discharges them.

* `arithE` (query `[0]` ↦ `hDesc1`, `[1]` ↦ `hDesc2`, `n = |w|`), `arithE_Q1/Q2`, `hForm_TM_of`;
* `arithA` (`n = |w|/2`, `sqDescA` of `rdM w`, `rdA w % rdM w`), `arithA_Q`, `sqrtMod_TM_of`;
* `arithB` (`sqDescB` of `ofWord w`), `arithB_Q`, `lqnr_TM_of`;
* `arithDiv`, `arithSig`, `arithCirc`, `arith*_Q`, `divisorSum_TM_of`, `sigmaSum_TM_of`, `circle_TM_of`.

Standard axioms only.
-/
import EthFollowup.ModP.ArithPackage
import EthFollowup.ModP.ArithReaderPoly
import EthFollowup.ModP.SpecE
import EthFollowup.ModP.SpecLattice

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring

/-! ## Common facts -/

theorem len_unary : Unary fun w : List Bool => w.length := Unary.of_length PolyT.id'

theorem len_fst_unary : Unary fun y : List Bool × List Bool => y.1.length :=
  Unary.of_length (PolyT.fst PolyT.id')

theorem half_unary : Unary fun w : List Bool => w.length / 2 :=
  Unary.of_le len_unary (PolyT.div len_unary.poly (PolyT.const 2)) fun _ => Nat.div_le_self _ _

theorem half_fst_unary : Unary fun y : List Bool × List Bool => y.1.length / 2 :=
  Unary.of_le len_fst_unary (PolyT.div len_fst_unary.poly (PolyT.const 2)) fun _ => Nat.div_le_self _ _

theorem gofWord_fst_polyT : PolyT fun y : List Bool × List Bool => Groundwork.ofWord y.1 :=
  PolyT.ofWord' (PolyT.fst PolyT.id')

theorem two_pow_le_bl {k n : ℕ} (h : k ≤ nB n) : 2 ^ k ≤ 2 ^ (b n * ℓ n) :=
  Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact h)

theorem gofWord_lt_bl (w : List Bool) : Groundwork.ofWord w < 2 ^ (b w.length * ℓ w.length) :=
  (Groundwork.ofWord_lt w).trans_le (two_pow_le_bl (le_nB _))

theorem gofWord_lt_nB (w : List Bool) : Groundwork.ofWord w < 2 ^ nB w.length :=
  (Groundwork.ofWord_lt w).trans_le (Nat.pow_le_pow_right (by norm_num) (le_nB _))

theorem lt_nB_encodeNat (x : ℕ) : x < 2 ^ nB (Computability.encodeNat x).length := by
  have h := gofWord_lt_nB (Computability.encodeNat x)
  rwa [gofWord_encodeNat] at h

theorem pos_length_of_ne {w : List Bool} (h : Groundwork.ofWord w ≠ 0) : 1 ≤ w.length := by
  rcases w with _ | ⟨x, w⟩
  · exact absurd rfl h
  · simp

/-! ## (E) class numbers -/

/-- **(E)**: `n = |w|`, `N = ofWord w`; query `[1]` ↦ `hDesc2`, every other query ↦ `hDesc1`. -/
def arithE : ArithSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc y := if y.2.getD 0 false = true then hDesc2 (b y.1.length) (ℓ y.1.length) (Groundwork.ofWord y.1)
    else hDesc1 (b y.1.length) (ℓ y.1.length) (Groundwork.ofWord y.1)
  desc_poly := by
    have hb := b_unary len_fst_unary
    have hℓ := ℓ_unary len_fst_unary
    have hc : PolyT fun y : List Bool × List Bool => decide (y.2.getD 0 false = true) :=
      (PolyT.getD (PolyT.snd PolyT.id') (PolyT.const 0) (PolyT.const false)).congr fun y => by
        cases y.2.getD 0 false <;> rfl
    exact PolyT.ite' hc (hDesc2_polyT hb hℓ gofWord_fst_polyT) (hDesc1_polyT hb hℓ gofWord_fst_polyT)
  cD := 1152
  cA_le y := by
    split_ifs <;> simp [cA, Desc.nP, Desc.nQ, Desc.nC, hDesc1, hDesc2, hProds, hChains]
  wf w π _ := by
    dsimp only
    split_ifs
    · exact hDesc2_WF _ _ _ _
    · exact hDesc1_WF _ _ _ _

theorem arithE_Q1 (N : ℕ) : (arithE.desc (Computability.encodeNat N, [false])).count
    (arithE.nf (Computability.encodeNat N)) = hQ1 (2 ^ nB (Computability.encodeNat N).length) N := by
  have h := gofWord_lt_bl (Computability.encodeNat N)
  show (hDesc1 (b (Computability.encodeNat N).length) (ℓ (Computability.encodeNat N).length)
    (Groundwork.ofWord (Computability.encodeNat N))).countB _ _ = _
  rw [gofWord_encodeNat] at h ⊢
  exact hDesc1_count h

theorem arithE_Q2 (N : ℕ) : (arithE.desc (Computability.encodeNat N, [true])).count
    (arithE.nf (Computability.encodeNat N)) = hQ2 (2 ^ nB (Computability.encodeNat N).length) N := by
  have h := gofWord_lt_bl (Computability.encodeNat N)
  show (hDesc2 (b (Computability.encodeNat N).length) (ℓ (Computability.encodeNat N).length)
    (Groundwork.ofWord (Computability.encodeNat N))).countB _ _ = _
  rw [gofWord_encodeNat] at h ⊢
  exact hDesc2_count h

/-- **(E) class numbers, given the polynomial-time table and reader.** -/
theorem hForm_TM_of (hT : PolyT tabAF) (hp : PolyT arithE.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, GraphProblems.Outputs M (Computability.encodeNat N)
        (Computability.encodeNat (hForm (-(N : ℤ))))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat N).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat N).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithE.pkg_exists hT hp
  have hR1 : ∀ w, specE.pre w = false → 1 ≤ pk.R w := fun w h => by
    rw [hR]
    exact pos_length_of_ne (by simpa [specE] using h)
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk specE specE_pre_polyT specE_small_polyT specE_q1_polyT
    specE_q2_polyT specE_fin_polyT (fun w => specE_length pk w (fun _ => hOk w) (hR1 w))
    (fun w _ => hOk w) (fun w hw => hR1 w hw) (fun w hw => hR1 w hw)
  refine ⟨M, C, hfin, fun N => ?_⟩
  have e := specE_answer_encodeNat pk N (lt_nB_encodeNat N)
    (fun _ => by rw [hQ]; exact arithE_Q1 N) (fun _ => by rw [hQ]; exact arithE_Q2 N)
  have := h (Computability.encodeNat N)
  rwa [e] at this

/-! ## (A) square roots modulo `m` -/

theorem rdM_polyT : PolyT rdM := by unfold rdM; fun_prop

theorem rdA_polyT : PolyT rdA := by unfold rdA; fun_prop

/-- **(A)**: `n = |w|/2`, modulus `m = rdM w`, residue `rdA w % m`, prefix `π` on `y`. -/
def arithA : ArithSpec where
  nf w := w.length / 2
  nf_le _ := Nat.div_le_self _ _
  nf_unary := half_unary
  R w := w.length / 2
  R_le _ := Nat.div_le_self _ _
  R_poly := half_unary.poly
  desc y := sqDescA (b (y.1.length / 2)) (ℓ (y.1.length / 2)) (y.1.length / 2) (rdM y.1)
    (rdA y.1 % rdM y.1) y.2
  desc_poly := by
    have hn := half_fst_unary
    have hm : PolyT fun y : List Bool × List Bool => rdM y.1 := rdM_polyT.comp (PolyT.fst PolyT.id')
    have ha : PolyT fun y : List Bool × List Bool => rdA y.1 := rdA_polyT.comp (PolyT.fst PolyT.id')
    exact sqDescA_polyT (b_unary hn) (ℓ_unary hn) hn hm (PolyT.mod ha hm) (PolyT.snd PolyT.id')
  cD := 1152
  cA_le y := by simp [cA, Desc.nP, Desc.nQ, Desc.nC, sqDescA]
  wf w π _ := sqDescA_WF (le_nB _)

theorem rdA_lt (w : List Bool) : rdA w < 2 ^ (w.length - w.length / 2) := by
  have := Groundwork.ofWord_lt (w.drop (w.length / 2))
  rwa [List.length_drop] at this

theorem arithA_Q (w π : List Bool) (hπ : π.length ≤ w.length / 2) :
    (arithA.desc (w, π)).count (arithA.nf w) =
      S3A (nB (w.length / 2)) (w.length / 2) (rdM w) (rdA w % rdM w) π := by
  have hm := rdM_lt w
  have hn := lt_nB (w.length / 2)
  have hm' : rdM w < 2 ^ (b (w.length / 2) * ℓ (w.length / 2)) := hm.trans_le (two_pow_le_bl hn.le)
  have ha : rdA w % rdM w < 2 ^ (b (w.length / 2) * ℓ (w.length / 2)) :=
    (Nat.mod_le _ _).trans_lt ((rdA_lt w).trans_le (two_pow_le_bl (by omega)))
  exact sqDescA_count hm' ha hm.le hπ

/-- **(A) square roots modulo any `m`, given the polynomial-time table and reader.** -/
theorem sqrtMod_TM_of (hT : PolyT tabAF) (hp : PolyT arithA.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ m a : ℕ, GraphProblems.Outputs M (encodePair m a) (Computability.encodeNat (minRoot m a))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodePair m a).length /
          Real.sqrt (Real.logb 2 ((encodePair m a).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithA.pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.searchM_TM pk specA specA_pre_polyT specA_small_polyT specA_step_polyT
    specA_fin_polyT stepPos_length (fun w π _ => finA_length w π) specA_small_length (fun w _ => hOk w)
  refine ⟨M, C, hfin, fun m a => ?_⟩
  have e := specA_answer_pair pk m a (hR _) (le_nB _) fun π hπ => by
    rw [hQ, arithA_Q _ _ (by simp only [List.length_append, List.length_singleton]; omega),
      rdM_encodePair, rdA_encodePair]
  have := h (encodePair m a)
  rwa [e] at this

/-! ## (B) the least quadratic non-residue -/

/-- **(B)**: `n = |w|`, `p = ofWord w`, prefix `π` on `x`. -/
def arithB : ArithSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc y := sqDescB (b y.1.length) (ℓ y.1.length) y.1.length (Groundwork.ofWord y.1) y.2
  desc_poly := by
    have hn := len_fst_unary
    exact sqDescB_polyT (b_unary hn) (ℓ_unary hn) hn gofWord_fst_polyT (PolyT.snd PolyT.id')
  cD := 1152
  cA_le y := by simp [cA, Desc.nP, Desc.nQ, Desc.nC, sqDescB]
  wf w π _ := sqDescB_WF (le_nB _)

theorem arithB_Q (w π : List Bool) (hπ : π.length ≤ w.length) :
    (arithB.desc (w, π)).count (arithB.nf w) =
      S3B (nB w.length) w.length (Groundwork.ofWord w) π :=
  sqDescB_count (gofWord_lt_bl w) (Groundwork.ofWord_lt w).le hπ

/-- **(B) the least quadratic non-residue, given the polynomial-time table and reader.** On a prime
`p` the output is `lqnr p`; on every `p` the machine halts within the bound with some `y ≤ p`. -/
theorem lqnr_TM_of (hT : PolyT tabAF) (hp : PolyT arithB.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ p : ℕ, p.Prime → GraphProblems.Outputs M (Computability.encodeNat p)
        (Computability.encodeNat (lqnr p))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat p).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat p).length + 2)))⌋₊) ∧
      (∀ p : ℕ, ∃ y ≤ p, GraphProblems.Outputs M (Computability.encodeNat p) (Computability.encodeNat y)
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat p).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat p).length + 2)))⌋₊) := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithB.pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.searchM_TM pk specB specB_pre_polyT specB_small_polyT specB_step_polyT
    specB_fin_polyT stepB_length (fun w π _ => finB_length w π) specB_small_length (fun w _ => hOk w)
  refine ⟨M, C, hfin, fun p hpr => ?_, fun p => ?_⟩
  · have e := specB_answer_prime pk hpr (hR _) (le_nB _) fun π hπ => by
      rw [hQ, arithB_Q _ _ (by simp only [List.length_append, List.length_singleton]; omega),
        gofWord_encodeNat]
    have := h (Computability.encodeNat p)
    rwa [e] at this
  · obtain ⟨y, hy, e⟩ := specB_answer_encodeNat_le pk p
    have := h (Computability.encodeNat p)
    rw [e] at this
    exact ⟨y, hy, this⟩

/-! ## (F) divisor sums, sums of divisors, the circle -/

/-- `n = |w|`, `x = ofWord w`, `a·b + s = x` with `a, b > 0` (the query word is ignored). -/
def arithDiv : ArithSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc y := divDesc (b y.1.length) (ℓ y.1.length) (Groundwork.ofWord y.1)
  desc_poly := by
    have hn := len_fst_unary
    exact divDesc_polyT (b_unary hn) (ℓ_unary hn) gofWord_fst_polyT
  cD := 1152
  cA_le y := by simp [cA, Desc.nP, Desc.nQ, Desc.nC, divDesc]
  wf _ _ _ := divDesc_WF _ _ _ _

/-- `a·b + s = x` with `b > 0`, `0 < c ≤ a`. -/
def arithSig : ArithSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc y := sigDesc (b y.1.length) (ℓ y.1.length) (Groundwork.ofWord y.1)
  desc_poly := by
    have hn := len_fst_unary
    exact sigDesc_polyT (b_unary hn) (ℓ_unary hn) gofWord_fst_polyT
  cD := 1152
  cA_le y := by simp [cA, Desc.nP, Desc.nQ, Desc.nC, sigDesc]
  wf _ _ _ := sigDesc_WF _ _ _ _

/-- `a·a + b·b + s = x` with `a > 0`. -/
def arithCirc : ArithSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc y := circDesc (b y.1.length) (ℓ y.1.length) (Groundwork.ofWord y.1)
  desc_poly := by
    have hn := len_fst_unary
    exact circDesc_polyT (b_unary hn) (ℓ_unary hn) gofWord_fst_polyT
  cD := 1152
  cA_le y := by simp [cA, Desc.nP, Desc.nQ, Desc.nC, circDesc]
  wf _ _ _ := circDesc_WF _ _ _ _

theorem arithDiv_Q (x : ℕ) (π : List Bool) : (arithDiv.desc (Computability.encodeNat x, π)).count
    (arithDiv.nf (Computability.encodeNat x)) = divQ (2 ^ nB (Computability.encodeNat x).length) x := by
  have h := gofWord_lt_bl (Computability.encodeNat x)
  show (divDesc _ _ (Groundwork.ofWord (Computability.encodeNat x))).countB _ _ = _
  rw [gofWord_encodeNat] at h ⊢
  exact divDesc_count h

theorem arithSig_Q (x : ℕ) (π : List Bool) : (arithSig.desc (Computability.encodeNat x, π)).count
    (arithSig.nf (Computability.encodeNat x)) = sigQ (2 ^ nB (Computability.encodeNat x).length) x := by
  have h := gofWord_lt_bl (Computability.encodeNat x)
  show (sigDesc _ _ (Groundwork.ofWord (Computability.encodeNat x))).countB _ _ = _
  rw [gofWord_encodeNat] at h ⊢
  exact sigDesc_count h

theorem arithCirc_Q (x : ℕ) (π : List Bool) : (arithCirc.desc (Computability.encodeNat x, π)).count
    (arithCirc.nf (Computability.encodeNat x)) = circQ (2 ^ nB (Computability.encodeNat x).length) x := by
  have h := gofWord_lt_bl (Computability.encodeNat x)
  show (circDesc _ _ (Groundwork.ofWord (Computability.encodeNat x))).countB _ _ = _
  rw [gofWord_encodeNat] at h ⊢
  exact circDesc_count h

/-- **(F) `Σ_{m ≤ x} τ(m)`, given the polynomial-time table and reader.** -/
theorem divisorSum_TM_of (hT : PolyT tabAF) (hp : PolyT arithDiv.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (∑ m ∈ Finset.Icc 1 x, (Nat.divisors m).card))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithDiv.pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk specDiv specDiv_pre_polyT specDiv_small_polyT
    specDiv_q1_polyT specDiv_q2_polyT specDiv_fin_polyT (fun w => specDiv_length pk w (fun _ => hOk w))
    (fun w _ => hOk w) (fun w _ => by simp [specDiv]) (fun w _ => by simp [specDiv])
  refine ⟨M, C, hfin, fun x => ?_⟩
  have e := specDiv_answer_encodeNat pk x (lt_nB_encodeNat x) fun _ => by rw [hQ]; exact arithDiv_Q x []
  have := h (Computability.encodeNat x)
  rwa [e] at this

/-- **(F) `Σ_{m ≤ x} σ(m)`, given the polynomial-time table and reader.** -/
theorem sigmaSum_TM_of (hT : PolyT tabAF) (hp : PolyT arithSig.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (∑ m ∈ Finset.Icc 1 x, ∑ d ∈ Nat.divisors m, d))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithSig.pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk specSig specSig_pre_polyT specSig_small_polyT
    specSig_q1_polyT specSig_q2_polyT specSig_fin_polyT (fun w => specSig_length pk w (fun _ => hOk w))
    (fun w _ => hOk w) (fun w _ => by simp [specSig]) (fun w _ => by simp [specSig])
  refine ⟨M, C, hfin, fun x => ?_⟩
  have e := specSig_answer_encodeNat pk x (lt_nB_encodeNat x) fun _ => by rw [hQ]; exact arithSig_Q x []
  have := h (Computability.encodeNat x)
  rwa [e] at this

/-- **(F) the Gauss circle count, given the polynomial-time table and reader.** -/
theorem circle_TM_of (hT : PolyT tabAF) (hp : PolyT arithCirc.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (((Finset.Icc (-(x : ℤ)) x ×ˢ Finset.Icc (-(x : ℤ)) x).filter
          fun q : ℤ × ℤ => q.1 ^ 2 + q.2 ^ 2 ≤ x).card))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithCirc.pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk specCirc specCirc_pre_polyT specCirc_small_polyT
    specCirc_q1_polyT specCirc_q2_polyT specCirc_fin_polyT (fun w => specCirc_length pk w (fun _ => hOk w))
    (fun w _ => hOk w) (fun w _ => by simp [specCirc]) (fun w _ => by simp [specCirc])
  refine ⟨M, C, hfin, fun x => ?_⟩
  have e := specCirc_answer_encodeNat pk x (lt_nB_encodeNat x) fun _ => by rw [hQ]; exact arithCirc_Q x []
  have := h (Computability.encodeNat x)
  rwa [e] at this

end EthFollowup.ModP
