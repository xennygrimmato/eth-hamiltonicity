/-
# ArithL, module 3c: degrees and the items of a node

Template: `ModP/ArithNetCount.lean` (first half). Every stage (= vertex family, one per object and
kind) has a degree bound `degS κ o`; cells of level `k` see the level-`k` variables, the product
slots of level `k` (`cntP`) and the level-`k` comparisons.
* `aInc`, `mem_aInc`, `length_aInc`, `card_aEndsAt_le`;
* `g_mul_card_stage_le'`, `aBSum n L g := Σ_st (stSz st + g)·degSt st`, **`g_mul_card_inc_le'`**:
  `g · #(items at a) ≤ 3 · aBSum`.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLNetDefs
import EthFollowup.ModP.ArithNetCount

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.ExactHC EthFollowup.Factoring EthFollowup.ModP

instance (n : ℕ) (L : LDesc) (v : AVL) : DecidablePred (AWInc n L v) := fun d => by
  unfold AWInc; infer_instance

/-! ## Counts per level -/

/-- The level of operand `σ` of product `p` (a constant: the product's level). -/
def LDesc.oLev (L : LDesc) (p σ : ℕ) : ℕ :=
  match opnd L.D p σ with
  | .var w => L.lv w
  | .const _ => L.lp p

/-- Variables of level `k`. -/
def cntV (L : LDesc) (k : ℕ) : ℕ := #((range L.D.nV).filter fun v => L.lv v = k)
/-- Products with a slot copy checked at level `k` (product level or operand level `k`). -/
def cntP (L : LDesc) (k : ℕ) : ℕ :=
  #((range L.D.nP).filter fun p => L.lp p = k ∨ L.oLev p 0 = k ∨ L.oLev p 1 = k)
/-- Comparisons of level `k`. -/
def cntQ (L : LDesc) (k : ℕ) : ℕ := #((range L.D.nQ).filter fun q => L.lq q = k)
/-- Products of chain `c`. -/
def cntC (L : LDesc) (c : ℕ) : ℕ := #((range L.D.nP).filter fun p => L.D.chainOf p = c)

/-- The degree bound of the stage of object `o` of vertex kind `κ`. -/
def degS (n : ℕ) (L : LDesc) : ℕ → ℕ → ℕ
  | 0, k => cntV L k + 2 * cntP L k + 2 * cntQ L k
  | 1, p => kl1 n (L.lp p) + kL1 n (L.lp p)
  | 2, p => kl1 n (L.lp p) + kL1 n (L.lp p)
  | 3, _ => 3
  | 4, p => 2 * kL1 n (L.lp p)
  | 5, p => 2 * kL1 n (L.lp p)
  | _, c => 2 * cntC L c + 2

/-- The degree bound of a stage (by its index). -/
def degSt (n : ℕ) (L : LDesc) (st : ℕ) : ℕ := degS n L (Blocks.fam (vObj L) st) (Blocks.loc (vObj L) st)

theorem degSt_stage {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) :
    degSt n L (v.stage L) = degS n L v.kind v.obj := by
  unfold degSt AVL.stage; rw [LB.fam_fidx hv.1, LB.loc_fidx hv.1]

/-! ## A list of the wires at a vertex -/

/-- A list containing all wires incident to a vertex (`mem_aInc`). -/
def aInc (n : ℕ) (L : LDesc) : AVL → List AWL
  | .cell k i => ((List.range L.D.nV).filter fun v => decide (L.lv v = k)).map (fun v => .L v i) ++
      ((List.range L.D.nP).filter fun p => decide (L.lp p = k ∨ L.oLev p 0 = k ∨ L.oLev p 1 = k)).flatMap
        (fun p => [.R p 0 i, .R p 1 i]) ++
      ((List.range L.D.nQ).filter fun q => decide (L.lq q = k)).flatMap (fun q => [.st q i, .st q (i - 1)])
  | .row p σ i2 => (List.range (kl1 n (L.lp p))).map (fun i1 => .R p σ (i1 + kl1 n (L.lp p) * i2)) ++
      (List.range (kL1 n (L.lp p))).map (fun s => .A p σ s i2)
  | .col p σ s => (List.range (kl1 n (L.lp p))).map (fun i2 => .A p σ s i2) ++
      (List.range (kL1 n (L.lp p))).map (fun t => .F p σ s t)
  | .mul p s t => [.F p 0 s t, .F p 1 s t, .C p s t]
  | .icol p s => (List.range (kL1 n (L.lp p))).map (fun t => .C p s t) ++
      (List.range (kL1 n (L.lp p))).map (fun u => .Dd p s u)
  | .irow p u => (List.range (kL1 n (L.lp p))).map (fun s => .Dd p s u) ++
      (List.range (kL1 n (L.lp p))).map (fun a => .E p a u)
  | .carry c k => ((List.range L.D.nP).filter fun p => decide (L.D.chainOf p = c)).flatMap (fun p =>
      [.E p (k % kl1 n (L.lc c)) (k / kl1 n (L.lc c)),
        .E p (k % kl1 n (L.lc c) + kl1 n (L.lc c)) (k / kl1 n (L.lc c) - 1)]) ++
      [.rr c (k - 1), .rr c k]

theorem length_flatMap_two {β : Type} (l : List ℕ) (f g : ℕ → β) :
    (l.flatMap fun p => [f p, g p]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; ring

theorem length_aInc (n : ℕ) (L : LDesc) (v : AVL) : (aInc n L v).length = degS n L v.kind v.obj := by
  cases v with
  | cell k i =>
    simp only [aInc, List.length_append, List.length_map, length_flatMap_two, degS, AVL.kind, AVL.obj]
    rfl
  | carry c k =>
    simp only [aInc, List.length_append, length_flatMap_two, degS, AVL.kind, AVL.obj, List.length_cons,
      List.length_nil]
    rfl
  | mul p s t => rfl
  | row p σ i2 => simp [aInc, degS, AVL.kind, AVL.obj]
  | col p σ s => simp [aInc, degS, AVL.kind, AVL.obj]
  | icol p s => simp [aInc, degS, AVL.kind, AVL.obj]; ring
  | irow p u => simp [aInc, degS, AVL.kind, AVL.obj]; ring

/-- Every valid wire incident to `v` is in `aInc n L v`. -/
theorem mem_aInc {n : ℕ} {L : LDesc} {d : AWL} {v : AVL} (hd : d.Valid n L) (he : AWInc n L v d) :
    d ∈ aInc n L v := by
  have hl1 := one_le_kl1 n
  cases d with
  | L w i =>
    simp only [valid_L] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.1]
  | R p σ i =>
    simp only [valid_R] at hd
    rcases he with he | he
    · simp only [aEnds] at he
      subst he
      obtain ⟨k, hk⟩ := cellR_eq n L p σ i
      have hlev : L.lp p = k ∨ L.oLev p σ = k := by
        unfold cellR at hk; unfold LDesc.oLev
        cases ho : opnd L.D p σ with
        | var w =>
          rw [ho] at hk; simp only at hk ⊢
          split_ifs at hk with h1
          · simp only [AVL.cell.injEq] at hk; exact Or.inr hk.1
          · simp only [AVL.cell.injEq] at hk; exact Or.inl hk.1
        | const l => rw [ho] at hk; simp only [AVL.cell.injEq] at hk; exact Or.inl hk.1
      rw [hk]
      simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
        List.mem_nil_iff, or_false, decide_eq_true_eq]
      refine Or.inl (Or.inr ⟨p, ⟨hd.1, ?_⟩, ?_⟩)
      · rcases two_cases hd.2.1 with rfl | rfl
        · rcases hlev with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases hlev with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      · rcases two_cases hd.2.1 with rfl | rfl <;> simp
    · simp only [aEnds] at he; subst he
      simp only [aInc, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨i % kl1 n (L.lp p), Nat.mod_lt _ (by have := hl1 (L.lp p); omega), by rw [Nat.mod_add_div]⟩
  | A p σ s i2 =>
    simp only [valid_A] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.2.2.1, hd.2.2.2]
  | F p σ s t =>
    simp only [valid_F] at hd
    rcases he with rfl | rfl <;> simp only [aEnds]
    · simp [aInc, hd.2.2.2]
    · rcases two_cases hd.2.1 with rfl | rfl <;> simp [aInc]
  | C p s t =>
    simp only [valid_C] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.2.2]
  | Dd p s u =>
    simp only [valid_Dd] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.2.1, hd.2.2]
  | E p a u =>
    simp only [valid_E] at hd
    have h1 : (aEnds n L (.E p a u)).1 = .irow p u := by simp only [aEnds]; split_ifs <;> rfl
    rcases he with he | he
    · rw [h1] at he; subst he; simp [aInc, hd.2.1]
    · simp only [aEnds] at he
      split_ifs at he with hc
      · subst he
        have hlp : L.lp p = L.lc (L.D.chainOf p) := rfl
        simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
          List.mem_nil_iff, or_false, decide_eq_true_eq]
        refine Or.inl ⟨p, ⟨hd.1, rfl⟩, ?_⟩
        rw [← hlp]
        have hL := kL1_eq n (L.lp p)
        have ha := hd.2.1
        rw [hL] at ha
        by_cases ha' : a < kl1 n (L.lp p)
        · left; rw [blk_mod _ ha', blk_div _ ha']
        · right
          have ha'' : a - kl1 n (L.lp p) < kl1 n (L.lp p) := by omega
          have e : a + kl1 n (L.lp p) * u = (a - kl1 n (L.lp p)) + kl1 n (L.lp p) * (u + 1) := by
            rw [mul_add]; omega
          rw [e, blk_mod _ ha'', blk_div _ ha'']
          simp only [AWL.E.injEq, true_and]; omega
      · subst he; simp [aInc, hd.2.1]
  | rr c j =>
    simp only [valid_rr] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds]
  | st q j =>
    simp only [valid_st] at hd
    rcases he with rfl | rfl <;> simp only [aEnds]
    · simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
        List.mem_nil_iff, or_false, decide_eq_true_eq]
      exact Or.inr ⟨q, ⟨hd.1, rfl⟩, Or.inr (by simp)⟩
    · simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
        List.mem_nil_iff, or_false, decide_eq_true_eq]
      exact Or.inr ⟨q, ⟨hd.1, rfl⟩, Or.inl rfl⟩

/-! ## Degrees and stages -/

/-- The indices of the wires with an end at `v`. -/
def aEndsAt (n : ℕ) (L : LDesc) (v : AVL) : Finset ℕ :=
  (range (numAW n L)).filter fun j => AWInc n L v (awOf n L j)

theorem card_aEndsAt_le (n : ℕ) (L : LDesc) {v : AVL} (hv : v.Valid n L) :
    #(aEndsAt n L v) ≤ degSt n L (v.stage L) := by
  calc #(aEndsAt n L v) ≤ #(((aInc n L v).map (awIdx n L)).toFinset) := by
        refine card_le_card fun j hj => ?_
        rw [aEndsAt, mem_filter, mem_range] at hj
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨awOf n L j, mem_aInc (awOf_valid hj.1) hj.2, awIdx_awOf hj.1⟩
    _ ≤ ((aInc n L v).map (awIdx n L)).length := List.toFinset_card_le _
    _ = degSt n L (v.stage L) := by rw [List.length_map, length_aInc, degSt_stage hv]

/-- **A cluster holds at most `stSz/g + 1` vertices of each stage.** -/
theorem g_mul_card_stage_le' (n : ℕ) (L : LDesc) (g st c : ℕ) (hg : 1 ≤ g) :
    g * #((range (numAV n L)).filter fun j => (avOf n L j).stage L = st ∧ aClus n L g (avOf n L j) = c) ≤
      stSz n L st + g := by
  have h1 : #((range (numAV n L)).filter fun j => (avOf n L j).stage L = st ∧ aClus n L g (avOf n L j) = c) ≤
      #((range (stSz n L st)).filter fun i => VB.vbN (stSz n L st) g i = c) := by
    apply card_le_card_of_injOn (fun j => (avOf n L j).idx n L)
    · intro j hj
      simp only [coe_filter, mem_range] at hj
      simp only [coe_filter, mem_range]
      obtain ⟨hj, hs, hc⟩ := hj
      have hv := avOf_valid hj
      refine ⟨hs ▸ AVL.idx_lt hv, ?_⟩
      rw [← hc, aClus, hs]
    · intro j hj j' hj' e
      simp only [coe_filter, mem_range] at hj hj'
      simp only at e
      rw [← avIdx_avOf hj.1, ← avIdx_avOf hj'.1, avIdx_eq (avOf_valid hj.1), avIdx_eq (avOf_valid hj'.1),
        hj.2.1, hj'.2.1, e]
  have h2 := ExactHC.VB.card_vb_le (stSz n L st) g c hg
  calc g * _ ≤ g * (stSz n L st / g + 1) := Nat.mul_le_mul_left _ (h1.trans h2)
    _ ≤ stSz n L st + g := by rw [mul_add, mul_one]; exact Nat.add_le_add_right (Nat.mul_div_le _ _) _

/-- The vertices (by index) of cluster `c`. -/
def aVClus (n : ℕ) (L : LDesc) (g c : ℕ) : Finset ℕ :=
  (range (numAV n L)).filter fun i => aClus n L g (avOf n L i) = c

/-- The stage sum `Σ_st (stSz st + g) · degSt st`. -/
def aBSum (n : ℕ) (L : LDesc) (g : ℕ) : ℕ :=
  ∑ st ∈ range (vObj L).sum, (stSz n L st + g) * degSt n L st

theorem g_mul_sum_deg_le (n : ℕ) (L : LDesc) (g c : ℕ) (hg : 1 ≤ g) :
    g * ∑ i ∈ aVClus n L g c, degSt n L ((avOf n L i).stage L) ≤ aBSum n L g := by
  rw [← sum_fiberwise_of_maps_to (s := aVClus n L g c) (t := range (vObj L).sum) (g := fun i => (avOf n L i).stage L)
    (fun i hi => mem_range.2 (stage_lt (avOf_valid (mem_range.1 (mem_filter.1 hi).1)))), mul_sum]
  unfold aBSum
  refine sum_le_sum fun st _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, smul_eq_mul, ← mul_assoc]
  refine Nat.mul_le_mul_right _ (le_trans (le_of_eq ?_) (g_mul_card_stage_le' n L g st c hg))
  congr 2
  unfold aVClus
  rw [filter_filter]
  exact filter_congr fun i _ => and_comm

section Sys

variable {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g)

/-- **`g · #(items at a) ≤ 3 · aBSum`.** -/
theorem g_mul_card_inc_le' (a : Fin g) :
    g * #(univ.filter ((arithSys n L g hg).Inc a)) ≤ 3 * aBSum n L g := by
  set Ca : Finset ℕ := {a.val, a.val - 1, g - 1}
  have hsub : #(univ.filter ((arithSys n L g hg).Inc a)) ≤
      #(Ca.biUnion fun c => (aVClus n L g c).biUnion fun i => aEndsAt n L (avOf n L i)) := by
    apply card_le_card_of_injOn Fin.val
    · intro k hk
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
      rw [arithSys_inc] at hk
      have hd := awOf_valid k.2
      have hev := aEnds_valid hd
      have hc := lohi_cases' hk (aClus_lt hev.1 (by omega))
      simp only [coe_biUnion, mem_coe, Set.mem_iUnion, exists_prop]
      have pick : ∀ (v : AVL), v.Valid n L → AWInc n L v (awOf n L k.val) →
          aClus n L g v ∈ Ca → ∃ c ∈ Ca, ∃ i ∈ aVClus n L g c, k.val ∈ aEndsAt n L (avOf n L i) := by
        intro v hv he hcv
        refine ⟨_, hcv, avIdx n L v, ?_, ?_⟩
        · simp only [aVClus, mem_filter, mem_range, avOf_avIdx hv]
          exact ⟨avIdx_lt hv, trivial⟩
        · simp only [aEndsAt, mem_filter, mem_range, avOf_avIdx hv]
          exact ⟨k.2, he⟩
      rcases hc with hc | hc | hc | hc
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.2 (Or.inr rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
    · intro k _ k' _ e; exact Fin.ext e
  have hdeg : ∀ c, #((aVClus n L g c).biUnion fun i => aEndsAt n L (avOf n L i)) ≤
      ∑ i ∈ aVClus n L g c, degSt n L ((avOf n L i).stage L) := fun c =>
    card_biUnion_le.trans (sum_le_sum fun i hi =>
      card_aEndsAt_le n L (avOf_valid (mem_range.1 (mem_filter.1 hi).1)))
  have hCa : #Ca ≤ 3 := card_le_three
  calc g * #(univ.filter ((arithSys n L g hg).Inc a))
      ≤ g * ∑ c ∈ Ca, ∑ i ∈ aVClus n L g c, degSt n L ((avOf n L i).stage L) :=
        Nat.mul_le_mul_left _ (hsub.trans (card_biUnion_le.trans (sum_le_sum fun c _ => hdeg c)))
    _ = ∑ c ∈ Ca, g * ∑ i ∈ aVClus n L g c, degSt n L ((avOf n L i).stage L) := mul_sum _ _ _
    _ ≤ ∑ _c ∈ Ca, aBSum n L g := sum_le_sum fun c _ => g_mul_sum_deg_le n L g c (by omega)
    _ = #Ca * aBSum n L g := by rw [sum_const, smul_eq_mul]
    _ ≤ 3 * aBSum n L g := Nat.mul_le_mul_right _ hCa

theorem arithSys_touch (a : Fin g) : #(univ.filter ((arithSys n L g hg).Touch a)) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]; intro j; exact j.elim

theorem arithT_abs_lt (a : Fin g) (ℓ : Fin (numAW n L) → ALab n) : |arithT n L g a ℓ| < 2 ^ 1 := by
  unfold arithT; split_ifs <;> norm_num

end Sys

end EthFollowup.Primes
