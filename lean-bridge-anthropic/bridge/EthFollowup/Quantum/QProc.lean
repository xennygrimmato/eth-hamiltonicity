/-
# Theorem Q1, bridge part 4: the layout, the context, the table procedure

* `layQ`: the layout of the circuit network (`layQ_describes`);
* `QCtx`, `qCtx`: the context (layout, the factor descriptors and internal-bit counts of every node,
  the modulus `M`);
* `qTp`: the table procedure (`Stepped.sumRange` over the `2^{N_a}` internal assignments, one term
  per step), `tableQ_runs`, `qSys_tspec` (Definition 2(iii) for the tables, `τ = 2·4^{G/g+1}`).
-/
import EthFollowup.Quantum.QNet
import StepMachines.Prog.Range

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Finset EthFollowup.ExactHC Groundwork Groundwork.Prog

/-! ### The layout -/

section Lay

variable (st : SS) (g : ℕ) [NeZero g] (n M z₁ z₂ z₃ : ℕ) (xs ys : List Bool)

def onPairN (a b k : ℕ) : Bool :=
  decide ((loN st g k = a ∧ hiN st g k = b) ∨ (loN st g k = b ∧ hiN st g k = a))

def pairN (a b : ℕ) : List ℕ :=
  ((List.range (clN st g).length).filter (onPairN st g a b)).map fun k => (incN st g a).idxOf k

/-- **The layout of the circuit network.** -/
def layQ (P B : ℕ) : Lay :=
  (((List.replicate P (), List.replicate B ()), ([()], [[false], [true]])),
    ((List.range g).map (fun a => (List.replicate (incN st g a).length (), [])),
      (List.range g).map (fun a => (List.range g).map (fun b => (pairN st g a b, [])))))

theorem idx_incList (a : Fin g) (k : Fin (cpart st g).cl.length) :
    @List.idxOf _ instBEqOfDecidableEq k ((qSys st g n M z₁ z₂ z₃ xs ys).incList a) =
      (incN st g a.val).idxOf k.val := by
  rw [← incList_val st g n M z₁ z₂ z₃ xs ys a]
  exact (idxOf_map_inj Fin.val_injective k _).symm

theorem layQ_describes (P B : ℕ) :
    (qSys st g n M z₁ z₂ z₃ xs ys).Describes boolCode P B (layQ st g P B) where
  P_eq := by simp [Lay.P, layQ]
  B_eq := by simp [Lay.B, layQ]
  w_eq := by simp [Lay.w, layQ]
  codes_iff u := by
    simp only [Lay.codes, layQ, List.mem_cons, List.mem_nil_iff, or_false, boolCode]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    · rintro ⟨l, rfl⟩; cases l <;> simp
  na_eq a := by
    simp only [Lay.na, Lay.node, layQ, getD_map_range _ a.2, List.length_replicate]
    rw [← incList_val st g n M z₁ z₂ z₃ xs ys a, List.length_map]
  nh_eq a := by
    simp only [Lay.nh, Lay.node, layQ, getD_map_range _ a.2]; rfl
  pair_eq a b _ := by
    simp only [Lay.pair, layQ, getD_map_range _ a.2, getD_map_range _ b.2, LabelSystem.pairData]
    refine Prod.ext ?_ rfl
    simp only
    have e : (List.finRange (cpart st g).cl.length).map Fin.val = List.range (clN st g).length := by
      rw [map_val_finRange, length_cl]
    unfold LabelSystem.pairItems pairN
    rw [List.map_congr_left fun k _ => idx_incList st g n M z₁ z₂ z₃ xs ys a k]
    rw [show (fun k : Fin (cpart st g).cl.length => (incN st g a.val).idxOf k.val) =
      (fun k => (incN st g a.val).idxOf k) ∘ Fin.val from rfl, ← List.map_map]
    congr 1
    symm
    show ((List.finRange _).filter _).map Fin.val = _
    rw [← e, List.filter_map]
    congr 1
    refine List.filter_congr fun k _ => ?_
    simp [qSys, LabelSystem.OnPair, onPairN, Fin.ext_iff]

end Lay

/-! ### The context and the table procedure -/

/-- The context: the layout, per node its factors and its number of internal bits (in unary), the
modulus `M`. -/
abbrev QCtx : Type := Lay × (List (List FDesc × List Unit) × ℕ)

def qCtx (st : SS) (g n M z₁ z₂ z₃ : ℕ) (xs ys : List Bool) (P B : ℕ) : QCtx :=
  (layQ st g P B, ((List.range g).map fun a =>
    (descN st g n M z₁ z₂ z₃ xs ys a, List.replicate (ilN st g a).length ()), M))

/-- The data of one table: `((M, factors), (N in unary, setting))`. -/
abbrev TDat : Type := (ℕ × List FDesc) × (List Unit × List Bool)

def rdT (q : QCtx × WQ) : TDat :=
  ((q.1.2.2, (q.1.2.1.getD q.2.1 ([], [])).1), ((q.1.2.1.getD q.2.1 ([], [])).2, q.2.2))

def termZ (p : TDat × ℕ) : ℤ := (termN p.1.1.1 p.1.1.2 p.1.2.2 p.2 : ℤ)

/-- The table machine: one term per step. -/
def tableQ : Stepped TDat ℤ := Stepped.sumRange (fun d => 2 ^ d.2.1.length) (Stepped.ofFun termZ)

/-- **The table procedure.** -/
def qTp : Stepped (QCtx × WQ) ℤ := Stepped.mapIn rdT tableQ

theorem size_nat_lt {y N : ℕ} (h : y < 2 ^ N) : size y ≤ N + 1 := by
  simp only [size_nat]; have := Nat.size_le.2 h; omega

theorem tableQ_runs (d : TDat) (hM : 0 < d.1.1) :
    tableQ.Runs d (2 * 2 ^ d.2.1.length) (2 * size d + 3 * d.2.1.length + 3 * size d.1.1 + 10)
      (streamN d.1.1 d.2.1.length d.1.2 d.2.2 : ℤ) := by
  have hM' : ∀ y < 2 ^ d.2.1.length, (Stepped.ofFun termZ).Runs (d, y) 1 (size d + (d.2.1.length + 1) + size d.1.1 + 1) (termZ (d, y)) := by
    intro y hy
    refine (Stepped.ofFun_runs termZ (d, y)).mono le_rfl ?_
    have h1 := size_nat_lt hy
    have h2 : size (termZ (d, y)) ≤ size d.1.1 := by
      simp only [termZ, size_int, Int.natAbs_natCast, size_nat]
      have := Nat.size_le_size (termN_lt hM d.1.2 d.2.2 y).le
      omega
    simp only [size_prod] at *
    omega
  have h := Stepped.sumRange_runs (N := fun d : TDat => 2 ^ d.2.1.length) (a := d) (fun _ => 1)
    (fun y => termZ (d, y)) d.1.1 _ hM' (fun y _ => by
      simp only [termZ, Int.natAbs_natCast]; exact (termN_lt hM d.1.2 d.2.2 y).le)
  have hv : ∑ y ∈ range (2 ^ d.2.1.length), termZ (d, y) = (streamN d.1.1 d.2.1.length d.1.2 d.2.2 : ℤ) := by
    simp only [termZ, streamN, Nat.cast_sum]
  rw [hv] at h
  refine h.mono (by simp [sum_const, card_range]; omega) ?_
  have h1 : size (2 ^ d.2.1.length) ≤ d.2.1.length + 2 := by
    simp only [size_nat]
    have := Nat.size_le.2 (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self d.2.1.length)); omega
  have h2 : size (2 ^ d.2.1.length * d.1.1) ≤ d.2.1.length + 1 + size d.1.1 := by
    simp only [size_nat]
    have := Nat.size_le.2 (show 2 ^ d.2.1.length * d.1.1 < 2 ^ (d.2.1.length + 1 + d.1.1.size) by
      rw [pow_add, pow_succ]
      have := Nat.lt_size_self d.1.1
      calc 2 ^ d.2.1.length * d.1.1 < 2 ^ d.2.1.length * 2 ^ d.1.1.size :=
            Nat.mul_lt_mul_of_pos_left this (by positivity)
        _ ≤ 2 ^ d.2.1.length * 2 * 2 ^ d.1.1.size := by
            nlinarith [Nat.one_le_two_pow (n := d.2.1.length), Nat.one_le_two_pow (n := d.1.1.size)])
    omega
  omega

theorem size_getD_le {α : Type} [HasSize α] : ∀ (l : List α) (i : ℕ) (d : α), size (l.getD i d) ≤ size l + size d
  | [], _, _ => by simp
  | a :: l, 0, d => by simp; omega
  | a :: l, i + 1, d => by
    have := size_getD_le l i d
    simp only [List.getD_cons_succ, size_list, List.map_cons, List.sum_cons] at this ⊢
    omega

theorem size_rdT (c : QCtx) (a : ℕ) (z : List Bool) : size (rdT (c, (a, z))) ≤ size c + size z + 4 := by
  have h := size_getD_le c.2.1 a ([], [])
  have h0 : size (([], []) : List FDesc × List Unit) = 2 := rfl
  simp only [rdT, size_prod] at *
  omega

section Spec

variable (st : SS) (g : ℕ) [NeZero g] (n M z₁ z₂ z₃ : ℕ) (xs ys : List Bool)

/-- The time bound of the tables. -/
def τQ : ℕ := 2 * 2 ^ (2 * (st.1.length / g + 1))

/-- The state bound of the tables. -/
def SQ (c : QCtx) (P : ℕ) : ℕ := 5 * size c + 4 * P + 6 * (st.1.length / g + 1) + 20

theorem qSys_tspec (hM : 0 < M) (P B : ℕ) (hP : ∀ a : Fin g, ((qSys st g n M z₁ z₂ z₃ xs ys).net boolCode).len a ≤ P) :
    (qSys st g n M z₁ z₂ z₃ xs ys).TSpec boolCode qTp (qCtx st g n M z₁ z₂ z₃ xs ys P B)
      (τQ st g) (SQ st g (qCtx st g n M z₁ z₂ z₃ xs ys P B) P) := by
  intro a x _
  set c := qCtx st g n M z₁ z₂ z₃ xs ys P B
  have hz := enc_eq st g n M z₁ z₂ z₃ xs ys a x
  have hd : rdT (c, (a.val, (qSys st g n M z₁ z₂ z₃ xs ys).enc boolCode a x)) =
      ((M, descN st g n M z₁ z₂ z₃ xs ys a.val), (List.replicate (ilN st g a.val).length (), zOf st g a.val x.1)) := by
    simp only [rdT, c, qCtx, getD_map_range _ a.2, hz]
  have h := tableQ_runs (rdT (c, (a.val, (qSys st g n M z₁ z₂ z₃ xs ys).enc boolCode a x))) (by rw [hd]; exact hM)
  rw [hd] at h
  simp only [List.length_replicate] at h
  have hT : (qSys st g n M z₁ z₂ z₃ xs ys).T a x.1 x.2 =
      (streamN M (ilN st g a.val).length (descN st g n M z₁ z₂ z₃ xs ys a.val) (zOf st g a.val x.1) : ℤ) := rfl
  rw [hT]
  refine (Stepped.mapIn_runs (f := rdT) (by rw [hd]; exact h)).mono ?_ ?_
  · unfold τQ
    have := length_ilN_le st g a.val
    have := card_blocksOf_le st g a.val
    refine Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) ?_)
    omega
  · have hs := size_rdT c a.val ((qSys st g n M z₁ z₂ z₃ xs ys).enc boolCode a x)
    rw [hd] at hs
    have hlen := (qSys st g n M z₁ z₂ z₃ xs ys).length_enc boolCode a x
    have hl := hP a
    have hzs : size ((qSys st g n M z₁ z₂ z₃ xs ys).enc boolCode a x) = 2 * ((qSys st g n M z₁ z₂ z₃ xs ys).enc boolCode a x).length + 1 :=
      LabelSystem.size_word _
    have hMc : size M ≤ size c := by
      have e : c.2.2 = M := rfl
      show size M ≤ size c.1 + (size c.2.1 + size c.2.2)
      rw [e]; omega
    have hN := length_ilN_le st g a.val
    have hb := card_blocksOf_le st g a.val
    have hlen' : (zOf st g a.val x.1).length ≤ P := by rw [← hz, hlen]; exact hl
    have hzs' : size (zOf st g a.val x.1) = 2 * (zOf st g a.val x.1).length + 1 := LabelSystem.size_word _
    rw [hz] at hs
    unfold SQ
    generalize st.1.length / g = y at hb ⊢
    generalize #(blocksOf st g a.val) = w at hN hb
    omega

end Spec

end EthFollowup.Quantum
