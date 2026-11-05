/-
# The representation-number packages and machines (repnum-plan.md §4, B3)

A *family* of forms `F : Bool → Bool → Matrix (Fin k) (Fin k) ℤ` (`k ≥ 1`), selected by the parity of
`N = ofWord w` and by the query word (`[true]` or not), with a common coercivity constant `c` and entry
bound `cm`, gives the `ArithSpec` `repFam k F c hk`: `n = |w|`, `B = c N + 1`, the description
`repDesc (b n) (ℓ n) k (monoL F_pq) (monoR F_pq) B N`. Its count on a word with
`N + repK k cm · B² < 2^{nB n}` is `#(sols F_pq c N)` (`repFam_Q`). The box condition fails for the
input words themselves (`nf w ≤ |w|`), so the package is padded (`CntPackage.padded`, CntPad) with
the constant `padC k cm c` (`size_bound`): on the padded word every value fits for every `N`.

* `polyT_bool2`, `repFam`, `repFam_Q`, `padC`, `size_bound`, `repFam_Q_pad`;
* `specRep` (one query, output the count), `specTun` (two queries `[false]`, `[true]`, output
  `[count₁ = 2 count₂]`), `spec0` (no query; the `k = 0` answer `[N = 0]`), their PolyT and lengths;
* `tunF` (Tunnell's four forms), `tunF_coercive`, `tunF_natAbs_le`;
* **`repNum_TM_of`**, **`tunnell_TM_of`**, **`repNum_TM_zero`**: the machines, given the polynomial-time
  table and reader.

Standard axioms only.
-/
import EthFollowup.ModP.ArithPkgs
import EthFollowup.ModP.RepPoly
import EthFollowup.ModP.CntPad

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring

/-! ## The family specification -/

/-- A function of two polynomial-time booleans is polynomial-time. -/
theorem polyT_bool2 {α β : Type} [Enc α] [Enc β] (G : Bool → Bool → β) {p q : α → Bool} (hp : PolyT p)
    (hq : PolyT q) : PolyT fun x => G (p x) (q x) :=
  (PolyT.cond' hp (PolyT.cond' hq (PolyT.const (G true true)) (PolyT.const (G true false)))
    (PolyT.cond' hq (PolyT.const (G false true)) (PolyT.const (G false false)))).congr fun x => by
      cases p x <;> cases q x <;> rfl

/-- The parity selector `N odd`. -/
def selP (w : List Bool) : Bool := decide (Groundwork.ofWord w % 2 = 1)

/-- The query selector `π = [true]`. -/
def selQ (π : List Bool) : Bool := decide (π = [true])

theorem selP_polyT : PolyT fun y : List Bool × List Bool => selP y.1 :=
  PolyT.decide_eq (PolyT.mod gofWord_fst_polyT (PolyT.const 2)) (PolyT.const 1)

theorem selQ_polyT : PolyT fun y : List Bool × List Bool => selQ y.2 :=
  PolyT.decide_eq (PolyT.snd PolyT.id') (PolyT.const [true])

/-- **The family specification**: `n = R = |w|`, `N = ofWord w`, `B = c N + 1`, the form `F (selP w) (selQ π)`. -/
def repFam (k : ℕ) (F : Bool → Bool → Matrix (Fin k) (Fin k) ℤ) (c : ℕ) (hk : 0 < k) : ArithSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc y := repDesc (b y.1.length) (ℓ y.1.length) k (monoL (F (selP y.1) (selQ y.2)))
    (monoR (F (selP y.1) (selQ y.2))) (c * Groundwork.ofWord y.1 + 1) (Groundwork.ofWord y.1)
  desc_poly := by
    have hn := len_fst_unary
    exact repDesc_polyT (b_unary hn) (ℓ_unary hn) k
      (polyT_bool2 (fun p q => monoL (F p q)) selP_polyT selQ_polyT)
      (polyT_bool2 (fun p q => monoR (F p q)) selP_polyT selQ_polyT)
      (PolyT.add (PolyT.mul (PolyT.const c) gofWord_fst_polyT) (PolyT.const 1)) gofWord_fst_polyT
  cD := repCD k
  cA_le y := by
    unfold cA Desc.nP Desc.nQ Desc.nC
    rw [repDesc_cA_eq]
  wf _ _ _ := repDesc_WF _ hk _ _ _ _ _

/-- **The count of the family specification** on a word with `N + repK k cm · B² < 2^{nB |w|}`. -/
theorem repFam_Q {k c cm : ℕ} {F : Bool → Bool → Matrix (Fin k) (Fin k) ℤ} (hk : 0 < k)
    (hc : ∀ p q, Coercive (F p q) c) (hcm : ∀ p q i j, (F p q i j).natAbs ≤ cm) (w π : List Bool)
    (hsz : Groundwork.ofWord w + repK k cm * (c * Groundwork.ofWord w + 1) ^ 2 < 2 ^ nB w.length) :
    ((repFam k F c hk).desc (w, π)).count ((repFam k F c hk).nf w) =
      (sols (F (selP w) (selQ π)) c (Groundwork.ofWord w)).card :=
  repDesc_count hk (hc _ _) (hcm _ _) (Nat.lt_succ_self _) hsz (hsz.trans_le (two_pow_le_bl le_rfl))

/-! ## Padding -/

/-- The padding constant: all values `< 2^{2L + padC}` for `N < 2^L`. -/
def padC (k cm c : ℕ) : ℕ := Nat.log 2 (1 + repK k cm * (c + 1) ^ 2) + 1

theorem size_bound (k cm c L N : ℕ) (hN : N < 2 ^ L) :
    N + repK k cm * (c * N + 1) ^ 2 < 2 ^ (2 * L + padC k cm c) := by
  have hX := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (1 + repK k cm * (c + 1) ^ 2)
  rw [Nat.succ_eq_add_one] at hX
  have h1 : c * N + 1 ≤ (c + 1) * 2 ^ L := by
    have : c * N ≤ c * 2 ^ L := Nat.mul_le_mul_left _ hN.le
    have : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    nlinarith
  have h2 : (c * N + 1) ^ 2 ≤ (c + 1) ^ 2 * (2 ^ L) ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left h1 2
  have h3 : N ≤ (2 ^ L) ^ 2 := by
    have : 2 ^ L ≤ (2 ^ L) ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  have e : 2 ^ (2 * L + padC k cm c) = (2 ^ L) ^ 2 * 2 ^ (Nat.log 2 (1 + repK k cm * (c + 1) ^ 2) + 1) := by
    unfold padC; rw [pow_add, ← pow_mul, mul_comm L 2]
  have hY : 0 < (2 ^ L) ^ 2 := by positivity
  rw [e]
  generalize 2 ^ (Nat.log 2 (1 + repK k cm * (c + 1) ^ 2) + 1) = E at *
  generalize (2 ^ L) ^ 2 = Y at *
  generalize repK k cm = K at *
  have h4 : K * (c * N + 1) ^ 2 ≤ K * ((c + 1) ^ 2 * Y) := Nat.mul_le_mul_left _ h2
  have h5 : Y * (1 + K * (c + 1) ^ 2) < Y * E := Nat.mul_lt_mul_of_pos_left hX hY
  calc N + K * (c * N + 1) ^ 2 ≤ Y + K * ((c + 1) ^ 2 * Y) := Nat.add_le_add h3 h4
    _ = Y * (1 + K * (c + 1) ^ 2) := by ring
    _ < Y * E := h5
    _ = Y * E := rfl

/-- **The count on the padded word**: for every word `w₀`, the count of `repFam` on `padW (padC k cm c) w₀`
is `#(sols F_pq c N)` with `N = ofWord w₀`. -/
theorem repFam_Q_pad {k c cm : ℕ} {F : Bool → Bool → Matrix (Fin k) (Fin k) ℤ} (hk : 0 < k)
    (hc : ∀ p q, Coercive (F p q) c) (hcm : ∀ p q i j, (F p q i j).natAbs ≤ cm) (w₀ π : List Bool) :
    ((repFam k F c hk).desc (padW (padC k cm c) w₀, π)).count ((repFam k F c hk).nf (padW (padC k cm c) w₀)) =
      (sols (F (selP w₀) (selQ π)) c (Groundwork.ofWord w₀)).card := by
  have hsz : Groundwork.ofWord (padW (padC k cm c) w₀) + repK k cm *
      (c * Groundwork.ofWord (padW (padC k cm c) w₀) + 1) ^ 2 < 2 ^ nB (padW (padC k cm c) w₀).length := by
    rw [gofWord_padW, length_padW]
    refine (size_bound k cm c _ _ (Groundwork.ofWord_lt w₀)).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
    exact le_nB _
  rw [repFam_Q hk hc hcm _ π hsz]
  have hp : selP (padW (padC k cm c) w₀) = selP w₀ := by unfold selP; rw [gofWord_padW]
  rw [hp, gofWord_padW]

/-! ## The query specifications -/

/-- **The one-query specification**: output the count of `[]`. -/
def specRep : GR.QuerySpec where
  pre _ := false
  small _ := []
  q1 _ := []
  q2 _ := []
  fin q := Nat.bits q.2.1

theorem specRep_pre_polyT : PolyT specRep.pre := by show PolyT fun _ : List Bool => false; fun_prop
theorem specRep_small_polyT : PolyT specRep.small := nil_polyT
theorem specRep_q1_polyT : PolyT specRep.q1 := nil_polyT
theorem specRep_q2_polyT : PolyT specRep.q2 := nil_polyT
theorem specRep_fin_polyT : PolyT specRep.fin := by
  show PolyT fun q : List Bool × ℕ × ℕ => Nat.bits q.2.1; fun_prop

theorem specRep_length {c₀ : ℕ} (pk : CntPackage c₀) (hOk : ∀ w, pk.Ok w) (w : List Bool) :
    (GR.answerQ pk specRep w).length ≤ (pk.qb + 2) * (w.length + 2) := by
  have e := pk.Q_lt w [] (hOk w) (by simp)
  show (Nat.bits (pk.Q w [])).length ≤ _
  exact (bits_length_le e).trans (by nlinarith)

/-- **Tunnell's specification**: for `N = 0` output `[false]`; else the counts of `[false]` and `[true]`
and the output `[c₁ = 2 c₂]`. -/
def specTun : GR.QuerySpec where
  pre w := decide (Groundwork.ofWord w = 0)
  small _ := [false]
  q1 _ := [false]
  q2 _ := [true]
  fin q := [decide (q.2.1 = 2 * q.2.2)]

theorem specTun_pre_polyT : PolyT specTun.pre := pre0_polyT
theorem specTun_small_polyT : PolyT specTun.small := by show PolyT fun _ : List Bool => [false]; fun_prop
theorem specTun_q1_polyT : PolyT specTun.q1 := by show PolyT fun _ : List Bool => [false]; fun_prop
theorem specTun_q2_polyT : PolyT specTun.q2 := by show PolyT fun _ : List Bool => [true]; fun_prop
theorem specTun_fin_polyT : PolyT specTun.fin :=
  PolyT.cons' (PolyT.decide_eq (PolyT.fst (PolyT.snd PolyT.id'))
    (PolyT.mul (PolyT.const 2) (PolyT.snd (PolyT.snd PolyT.id')))) (PolyT.const [])

theorem specTun_length {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) :
    (GR.answerQ pk specTun w).length ≤ 1 * (w.length + 2) := by
  unfold GR.answerQ
  split_ifs
  · show [false].length ≤ _; simp
  · show [_].length ≤ _; simp

theorem specTun_q_length (w : List Bool) (h : specTun.pre w = false) : [false].length ≤ w.length ∧
    [true].length ≤ w.length := by
  have : Groundwork.ofWord w ≠ 0 := by simpa [specTun] using h
  have := pos_length_of_ne this
  simp only [List.length_singleton]; omega

/-- **The `k = 0` specification**: no query, the answer `[N = 0]` (`= encodeNat (if N = 0 then 1 else 0)`). -/
def spec0 : GR.QuerySpec where
  pre _ := true
  small w := if Groundwork.ofWord w = 0 then [true] else []
  q1 _ := []
  q2 _ := []
  fin _ := []

theorem spec0_pre_polyT : PolyT spec0.pre := by show PolyT fun _ : List Bool => true; fun_prop
theorem spec0_small_polyT : PolyT spec0.small :=
  PolyT.ite' pre0_polyT (PolyT.const [true]) (PolyT.const [])
theorem spec0_q1_polyT : PolyT spec0.q1 := nil_polyT
theorem spec0_q2_polyT : PolyT spec0.q2 := nil_polyT
theorem spec0_fin_polyT : PolyT spec0.fin := by
  show PolyT fun _ : List Bool × ℕ × ℕ => ([] : List Bool); fun_prop

theorem spec0_length {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) :
    (GR.answerQ pk spec0 w).length ≤ 1 * (w.length + 2) := by
  show (if Groundwork.ofWord w = 0 then [true] else []).length ≤ _
  split_ifs <;> simp

/-! ## The machines -/

/-- **Representation numbers of a coercive form with `k ≥ 1` variables**, given the table and reader. -/
theorem repNum_TM_of {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (c : ℕ) (hc : Coercive A c) (hk : 0 < k)
    (hT : PolyT tabAF) (hp : PolyT (repFam k (fun _ _ => A) c hk).prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : ℕ, GraphProblems.Outputs M (Computability.encodeNat n) (Computability.encodeNat (repNum A n))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat n).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat n).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := (repFam k (fun _ _ => A) c hk).pkg_exists hT hp
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, c₃ = padC k (cM A) c := ⟨_, rfl⟩
  have hR' : ∀ w, w.length ≤ pk.R (padW c₃ w) := fun w => by
    rw [hR]; show w.length ≤ (padW c₃ w).length; rw [length_padW]; omega
  have hOk' : ∀ w, (pk.padded c₃ hR').Ok w := fun w => hOk (padW c₃ w)
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM_padded pk c₃ hR' specRep specRep_pre_polyT
    specRep_small_polyT specRep_q1_polyT specRep_q2_polyT specRep_fin_polyT
    (specRep_length (pk.padded c₃ hR') hOk') (fun w _ => hOk (padW c₃ w)) (fun w _ => Nat.zero_le _)
    (fun w _ => Nat.zero_le _)
  refine ⟨M, C, hfin, fun n => ?_⟩
  have e : GR.answerQ (pk.padded c₃ hR') specRep (Computability.encodeNat n) =
      Computability.encodeNat (repNum A n) := by
    rw [GR.answerQ_padded]
    show Nat.bits (pk.Q (padW c₃ (Computability.encodeNat n)) []) = _
    rw [hQ, hc₃, repFam_Q_pad (cm := cM A) hk (fun _ _ => hc) (fun _ _ => natAbs_le_cM A), gofWord_encodeNat,
      ← repNum_eq_card_box hc, bits_eq_encodeNat]
  have := h (Computability.encodeNat n)
  rwa [e] at this

/-- **The `k = 0` machine** (`repNum A n = [n = 0]`), from any package. -/
theorem repNum_TM_zero (A : Matrix (Fin 0) (Fin 0) ℤ) (hT : PolyT tabAF) (hp : PolyT arithCirc.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : ℕ, GraphProblems.Outputs M (Computability.encodeNat n) (Computability.encodeNat (repNum A n))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat n).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat n).length + 2)))⌋₊ := by
  obtain ⟨pk, -, -, -, -⟩ := arithCirc.pkg_exists hT hp
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk spec0 spec0_pre_polyT spec0_small_polyT spec0_q1_polyT
    spec0_q2_polyT spec0_fin_polyT (spec0_length pk) (fun w hw => by simp [spec0] at hw)
    (fun w hw => by simp [spec0] at hw) (fun w hw => by simp [spec0] at hw)
  refine ⟨M, C, hfin, fun n => ?_⟩
  have e : GR.answerQ pk spec0 (Computability.encodeNat n) = Computability.encodeNat (repNum A n) := by
    show (if Groundwork.ofWord (Computability.encodeNat n) = 0 then [true] else []) = _
    rw [gofWord_encodeNat, repNum_zero_k]
    split_ifs <;> rfl
  have := h (Computability.encodeNat n)
  rwa [e] at this

/-! ## Tunnell's test -/

/-- Tunnell's four forms: odd `N` ↦ `x² + 2y² + 8z²` (`[false]`), `x² + 2y² + 32z²` (`[true]`);
even `N` ↦ `8x² + 2y² + 16z²`, `8x² + 2y² + 64z²`. -/
def tunF (p q : Bool) : Matrix (Fin 3) (Fin 3) ℤ :=
  if p then (if q then tForm 1 2 32 else tForm 1 2 8) else (if q then tForm 8 2 64 else tForm 8 2 16)

theorem tForm_coercive' {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : Coercive (tForm a b c) 1 :=
  coercive_diagonal fun i => by fin_cases i <;> simp <;> omega

theorem tunF_coercive (p q : Bool) : Coercive (tunF p q) 1 := by
  unfold tunF
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact tForm_coercive' (by norm_num) (by norm_num) (by norm_num)

theorem tForm_natAbs_le {a b c : ℕ} (ha : a ≤ 64) (hb : b ≤ 64) (hc : c ≤ 64) (i j : Fin 3) :
    (tForm a b c i j).natAbs ≤ 64 := by
  unfold tForm
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.diagonal_apply_eq]
    fin_cases i <;> simp <;> omega
  · rw [Matrix.diagonal_apply_ne _ hij]; simp

theorem tunF_natAbs_le (p q : Bool) (i j : Fin 3) : (tunF p q i j).natAbs ≤ 64 := by
  unfold tunF
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact tForm_natAbs_le (by norm_num) (by norm_num) (by norm_num) i j

/-- The specification of Tunnell's test (`c = 1`). -/
abbrev arithTun : ArithSpec := repFam 3 tunF 1 (by norm_num)

/-- **Tunnell's test**, given the table and reader. -/
theorem tunnell_TM_of (hT : PolyT tabAF) (hp : PolyT arithTun.prep) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : ℕ, GraphProblems.Outputs M (Computability.encodeNat n) [tunnellTest n]
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat n).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat n).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithTun.pkg_exists hT hp
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, c₃ = padC 3 64 1 := ⟨_, rfl⟩
  have hR' : ∀ w, w.length ≤ pk.R (padW c₃ w) := fun w => by
    rw [hR]; show w.length ≤ (padW c₃ w).length; rw [length_padW]; omega
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM_padded pk c₃ hR' specTun specTun_pre_polyT
    specTun_small_polyT specTun_q1_polyT specTun_q2_polyT specTun_fin_polyT
    (specTun_length (pk.padded c₃ hR')) (fun w _ => hOk (padW c₃ w)) (fun w hw => (specTun_q_length w hw).1)
    (fun w hw => (specTun_q_length w hw).2)
  refine ⟨M, C, hfin, fun n => ?_⟩
  have hQ' : ∀ π : List Bool, pk.Q (padW c₃ (Computability.encodeNat n)) π =
      repNum (tunF (decide (n % 2 = 1)) (selQ π)) n := fun π => by
    rw [hQ, hc₃, repFam_Q_pad (k := 3) (by norm_num) tunF_coercive tunF_natAbs_le, gofWord_encodeNat,
      ← repNum_eq_card_box (tunF_coercive _ _)]
    unfold selP; rw [gofWord_encodeNat]
  have e : GR.answerQ (pk.padded c₃ hR') specTun (Computability.encodeNat n) = [tunnellTest n] := by
    rw [GR.answerQ_padded]
    by_cases h0 : n = 0
    · subst h0
      rw [tunnellTest_zero]
      rfl
    · have hpre : specTun.pre (Computability.encodeNat n) = false := by
        simp only [specTun, gofWord_encodeNat, decide_eq_false_iff_not]; exact h0
      rw [if_neg (by simp [hpre])]
      show [decide (pk.Q (padW c₃ (Computability.encodeNat n)) [false] =
        2 * pk.Q (padW c₃ (Computability.encodeNat n)) [true])] = _
      rw [hQ', hQ']
      have e1 : selQ [false] = false := by decide
      have e2 : selQ [true] = true := by decide
      rw [e1, e2]
      unfold tunnellTest tunF
      by_cases hn : n % 2 = 1 <;> simp [hn]
  have := h (Computability.encodeNat n)
  rwa [e] at this

end EthFollowup.ModP
