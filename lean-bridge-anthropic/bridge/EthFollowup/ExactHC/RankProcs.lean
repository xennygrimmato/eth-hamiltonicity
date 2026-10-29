/-
# Procedures for the network with per-pair codes (workstream A, file 4)

`PairCode.lean` builds, from a `LabelSystem X` and a per-pair code `C : X.PairCode` (for instance the
rank code `X.rankPC s hs hd`, `research/hc-degree-theorem.md` Definition 2.2), the network
`X.netP C : Net g`. Here `X.netP C` is given by procedures in Anthropic's cost model, and we prove
`Given.IsGivenNetwork (Given.ofProcs (procsP lay par Tp)) Given.noTable c (X.netP C) P B τ S'`
(the form consumed by `Given.stOnGiven` / `Given.onSteps`), exactly as `LabelProcs.lean` does for
the fixed-width network `X.net C`.

The procedures read a *layout* `LayP`, a plain data object carried by the context, which lists
(in unary where Definition 2(iii) needs unary numbers):

* `P`, `B`, `g`;
* for every node `a`: the total block width `sumCap a` and the number of held copy bits;
* for every ordered pair `(a, b)`: the offset `offP a b` and the width `cap a b` of block `b` in a
  setting of `a` (variable widths), the width `rw a b` of the rank field and the number `nr a b` of
  ranks (`C(e_ab, s_ab)` for the rank code), and the copy bits as in `LabelProcs`.

`Describes` says what the layout holds; its `valid` clause says that a block decodes iff it has the
right width and its rank field is `< nr a b` (for the rank code this is `Rank.decR_isSome_iff`,
`rank_valid`). Membership, `Ψ` and `f` are one-step machines: membership checks the length and every
block (width and rank-field range, no unranking), `Ψ` and `f` compare the shared bits
`blockAt a b z ++ copies` (the shared word is the block itself, no decoding). The node tables are
computed by an arbitrary T-procedure `Tp` (`TSpecP`), for instance `tableProcD` of
`DegTableProc.lean` after a reader that decodes the blocks (`Rank.rawCodes`).

Main results:

* `procsP_give`, `procsP_keeps`, **`procsP_given`**;
* `layoutP`, `layoutP_describes` (a canonical layout from `rw`, `nr` and the `valid` property);
* `rankLayout`, `rankLayout_describes` for the rank code.
-/
import EthFollowup.ExactHC.PairCode
import EthFollowup.ExactHC.LabelProcs

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog QueryMachines Eight.SecNetworks Finset

/-! ### The layout -/

/-- The data of an ordered pair: `((offset, width in unary), (rank-field width, number of ranks))`,
and the copy bits (`(true, i)`: held bit `i`; `(false, j)`: copy bit `j` computed at the node). -/
abbrev PairD : Type := ((ℕ × List Unit) × (ℕ × ℕ)) × List (Bool × ℕ)

/-- The layout: `((P, B), g)`, per node `(sumCap, held)` in unary, per ordered pair `PairD`. -/
abbrev LayP : Type :=
  ((List Unit × List Unit) × List Unit) × (List (List Unit × List Unit) × List (List PairD))

namespace LayP

/-- The bound `P`. -/
def P (d : LayP) : ℕ := d.1.1.1.length
/-- The bound `B`. -/
def B (d : LayP) : ℕ := d.1.1.2.length
/-- The number of nodes. -/
def g (d : LayP) : ℕ := d.1.2.length
/-- The data of the node `a`. -/
def node (d : LayP) (a : ℕ) : List Unit × List Unit := d.2.1.getD a ([], [])
/-- The total width of the blocks of `a`. -/
def sc (d : LayP) (a : ℕ) : ℕ := (d.node a).1.length
/-- The number of copy bits held by `a`. -/
def nh (d : LayP) (a : ℕ) : ℕ := (d.node a).2.length
/-- The data of the ordered pair `(a, b)`. -/
def pair (d : LayP) (a b : ℕ) : PairD := (d.2.2.getD a []).getD b (((0, []), (0, 0)), [])
/-- The offset of block `b` in a setting of `a`. -/
def off (d : LayP) (a b : ℕ) : ℕ := (d.pair a b).1.1.1
/-- The width of block `b`. -/
def wd (d : LayP) (a b : ℕ) : ℕ := (d.pair a b).1.1.2.length
/-- The width of the rank field. -/
def rw (d : LayP) (a b : ℕ) : ℕ := (d.pair a b).1.2.1
/-- The number of ranks. -/
def nr (d : LayP) (a b : ℕ) : ℕ := (d.pair a b).1.2.2
/-- The copy bits on `{a, b}`. -/
def cps (d : LayP) (a b : ℕ) : List (Bool × ℕ) := (d.pair a b).2
/-- `P_a`. -/
def len (d : LayP) (a : ℕ) : ℕ := d.sc a + d.nh a
/-- `c_{a,b}`. -/
def cap (d : LayP) (a b : ℕ) : ℕ := d.wd a b + (d.cps a b).length

end LayP

/-- Block `b` of a setting `z` of `a` (variable width). -/
def blkP (d : LayP) (a b : ℕ) (z : List Bool) : List Bool := (z.drop (d.off a b)).take (d.wd a b)

/-- A block is valid: the right width, and the rank field is in range. -/
def okBlk (d : LayP) (a b : ℕ) (z : List Bool) : Bool :=
  decide ((blkP d a b z).length = d.wd a b) && decide (ofWord ((blkP d a b z).take (d.rw a b)) < d.nr a b)

/-! ### The procedures -/

section Procs

variable {Ctx : Type} (lay : Ctx → LayP) (par : Ctx × (ℕ × List Bool) → Bool)

/-- The shared bits of the pair `(a, b)`, computed from a setting `z` of `a`: block `b`, then the
copy bits on `{a, b}`. -/
def projFP (c : Ctx) (a b : ℕ) (z : List Bool) : List Bool :=
  blkP (lay c) a b z ++ ((lay c).cps a b).map fun e =>
    if e.1 = true then z.getD ((lay c).sc a + e.2) false else par (c, (e.2, z))

/-- Membership: the right length, and every block `b ≠ a` is valid. -/
def memFP (x : Ctx × WQ) : Bool :=
  decide (x.2.2.length = (lay x.1).len x.2.1) &&
    (List.range (lay x.1).g).all fun b => decide (b = x.2.1) || okBlk (lay x.1) x.2.1 b x.2.2

/-- `Ψ_{a,b}(z, z') = [proj_{a,b} z = proj_{b,a} z']`. -/
def psiFP (x : Ctx × PsiQ) : ℤ :=
  if projFP lay par x.1 x.2.1.1 x.2.1.2 x.2.2.1 = projFP lay par x.1 x.2.1.2 x.2.1.1 x.2.2.2 then 1 else 0

/-- `f_{a,b}(z, θ) = [proj_{a,b} z = θ]`. -/
def fFP (x : Ctx × FQ) : ℤ :=
  if projFP lay par x.1 x.2.1.1 x.2.1.2 x.2.2.1 = x.2.2.2 then 1 else 0

variable [HasSize Ctx]

/-- **The procedures of the network with per-pair codes**; `Tp` is the procedure for the tables. -/
def procsP (Tp : Stepped (Ctx × WQ) ℤ) : Procs Ctx where
  P c := (lay c).P
  B c := (lay c).B
  len c a := (lay c).len a
  cap c a b := (lay c).cap a b
  mem := Stepped.ofFun (memFP lay)
  W := Tp
  Ψ := Stepped.ofFun (psiFP lay par)
  f := Stepped.ofFun (fFP lay par)

end Procs

/-! ### Polynomial time -/

section Poly

variable {α : Type} [Enc α]

@[fun_prop] theorem LayP.P_polyT {d : α → LayP} (hd : PolyT d) : PolyT fun x => (d x).P := by
  unfold LayP.P; fun_prop
@[fun_prop] theorem LayP.B_polyT {d : α → LayP} (hd : PolyT d) : PolyT fun x => (d x).B := by
  unfold LayP.B; fun_prop
@[fun_prop] theorem LayP.g_polyT {d : α → LayP} (hd : PolyT d) : PolyT fun x => (d x).g := by
  unfold LayP.g; fun_prop
@[fun_prop] theorem LayP.node_polyT {d : α → LayP} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).node (a x) := by
  unfold LayP.node; fun_prop
@[fun_prop] theorem LayP.sc_polyT {d : α → LayP} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).sc (a x) := by
  unfold LayP.sc; fun_prop
@[fun_prop] theorem LayP.nh_polyT {d : α → LayP} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).nh (a x) := by
  unfold LayP.nh; fun_prop
@[fun_prop] theorem LayP.pair_polyT {d : α → LayP} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => (d x).pair (a x) (b x) := by
  unfold LayP.pair; fun_prop
@[fun_prop] theorem LayP.off_polyT {d : α → LayP} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => (d x).off (a x) (b x) := by
  unfold LayP.off; fun_prop
@[fun_prop] theorem LayP.wd_polyT {d : α → LayP} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => (d x).wd (a x) (b x) := by
  unfold LayP.wd; fun_prop
@[fun_prop] theorem LayP.rw_polyT {d : α → LayP} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => (d x).rw (a x) (b x) := by
  unfold LayP.rw; fun_prop
@[fun_prop] theorem LayP.nr_polyT {d : α → LayP} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => (d x).nr (a x) (b x) := by
  unfold LayP.nr; fun_prop
@[fun_prop] theorem LayP.cps_polyT {d : α → LayP} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => (d x).cps (a x) (b x) := by
  unfold LayP.cps; fun_prop
@[fun_prop] theorem LayP.len_polyT {d : α → LayP} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).len (a x) := by
  unfold LayP.len; fun_prop
@[fun_prop] theorem blkP_polyT {d : α → LayP} {a b : α → ℕ} {z : α → List Bool} (hd : PolyT d)
    (ha : PolyT a) (hb : PolyT b) (hz : PolyT z) : PolyT fun x => blkP (d x) (a x) (b x) (z x) := by
  unfold blkP; fun_prop
@[fun_prop] theorem okBlk_polyT {d : α → LayP} {a b : α → ℕ} {z : α → List Bool} (hd : PolyT d)
    (ha : PolyT a) (hb : PolyT b) (hz : PolyT z) : PolyT fun x => okBlk (d x) (a x) (b x) (z x) := by
  have h0 := blkP_polyT hd ha hb hz
  have h1 : PolyT fun x => decide ((blkP (d x) (a x) (b x) (z x)).length = (d x).wd (a x) (b x)) :=
    PolyT.decide_eq (PolyT.length h0) (LayP.wd_polyT hd ha hb)
  have h2 : PolyT fun x => decide (ofWord ((blkP (d x) (a x) (b x) (z x)).take ((d x).rw (a x) (b x))) <
      (d x).nr (a x) (b x)) := by
    have := PolyT.ofWord' (PolyT.take (LayP.rw_polyT hd ha hb) h0)
    have := LayP.nr_polyT hd ha hb
    fun_prop
  unfold okBlk
  exact PolyT.and' h1 h2

theorem LayP.P_unary {d : α → LayP} (hd : PolyT d) : Unary fun x => (d x).P := by
  unfold LayP.P; exact Unary.of_length (w := fun x => (d x).1.1.1) (by fun_prop)
theorem LayP.B_unary {d : α → LayP} (hd : PolyT d) : Unary fun x => (d x).B := by
  unfold LayP.B; exact Unary.of_length (w := fun x => (d x).1.1.2) (by fun_prop)
theorem LayP.g_unary {d : α → LayP} (hd : PolyT d) : Unary fun x => (d x).g := by
  unfold LayP.g; exact Unary.of_length (w := fun x => (d x).1.2) (by fun_prop)
theorem LayP.len_unary {d : α → LayP} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    Unary fun x => (d x).len (a x) := by
  unfold LayP.len LayP.sc LayP.nh
  exact (Unary.of_length (w := fun x => ((d x).node (a x)).1) (by fun_prop)).add
    (Unary.of_length (w := fun x => ((d x).node (a x)).2) (by fun_prop))
theorem LayP.cap_unary {d : α → LayP} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a) (hb : PolyT b) :
    Unary fun x => (d x).cap (a x) (b x) := by
  unfold LayP.cap LayP.wd
  exact (Unary.of_length (w := fun x => ((d x).pair (a x) (b x)).1.1.2) (by fun_prop)).add
    (Unary.of_length (w := fun x => (d x).cps (a x) (b x)) (by fun_prop))

variable {Ctx : Type} [Enc Ctx] {lay : Ctx → LayP} {par : Ctx × (ℕ × List Bool) → Bool}

@[fun_prop] theorem projFP_polyT (hlay : PolyT lay) (hpar : PolyT par) {c : α → Ctx} {a b : α → ℕ}
    {z : α → List Bool} (hc : PolyT c) (ha : PolyT a) (hb : PolyT b) (hz : PolyT z) :
    PolyT fun x => projFP lay par (c x) (a x) (b x) (z x) := by
  unfold projFP
  fun_prop

theorem memFP_polyT (hlay : PolyT lay) : PolyT (memFP lay) := by
  have hr : PolyT fun x : Ctx × WQ => List.range (lay x.1).g := PolyT.range (LayP.g_unary (by fun_prop))
  unfold memFP
  fun_prop

theorem psiFP_polyT (hlay : PolyT lay) (hpar : PolyT par) : PolyT (psiFP lay par) := by
  unfold psiFP; fun_prop

theorem fFP_polyT (hlay : PolyT lay) (hpar : PolyT par) : PolyT (fFP lay par) := by
  unfold fFP; fun_prop

end Poly

/-! ### The layout described -/

namespace LabelSystem

variable {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L] {X : LabelSystem g K R L} (C : X.PairCode)

/-- The copy-bit data of the ordered pair `(a, b)` (as in `LabelSystem.pairData`). -/
def copyData (Y : LabelSystem g K R L) (a b : Fin g) : List (Bool × ℕ) :=
  (Y.pairCopies a b).map fun j =>
    if Y.holder j = a then (true, (Y.heldList a).idxOf j) else (false, Y.rord.idxOf j)

/-- **What the layout must hold** for the network `X.netP C` with parameters `P`, `B`. -/
structure DescribesP (P B : ℕ) (d : LayP) : Prop where
  P_eq : d.P = P
  B_eq : d.B = B
  g_eq : d.g = g
  sc_eq : ∀ a : Fin g, d.sc a.val = C.sumCap a
  nh_eq : ∀ a : Fin g, d.nh a.val = (X.heldList a).length
  off_eq : ∀ a b : Fin g, a ≠ b → d.off a.val b.val = C.offP a b
  wd_eq : ∀ a b : Fin g, a ≠ b → d.wd a.val b.val = C.cap a b
  cps_eq : ∀ a b : Fin g, a ≠ b → d.cps a.val b.val = copyData X a b
  /-- A block decodes iff it has the right width and its rank field is in range. -/
  valid : ∀ a b : Fin g, a ≠ b → ∀ w : List Bool,
    (C.dec a b w).isSome ↔ w.length = C.cap a b ∧ ofWord (w.take (d.rw a.val b.val)) < d.nr a.val b.val

/-- A canonical layout, from the rank-field widths `rwf` and the numbers of ranks `nrf`. -/
noncomputable def layoutP (P B : ℕ) (rwf nrf : Fin g → Fin g → ℕ) : LayP :=
  (((List.replicate P (), List.replicate B ()), List.replicate g ()),
    ((List.finRange g).map fun a => (List.replicate (C.sumCap a) (), List.replicate (X.heldList a).length ()),
      (List.finRange g).map fun a => (List.finRange g).map fun b =>
        (((C.offP a b, List.replicate (C.cap a b) ()), (rwf a b, nrf a b)), copyData X a b)))

theorem layoutP_describes (P B : ℕ) (rwf nrf : Fin g → Fin g → ℕ)
    (hv : ∀ a b : Fin g, a ≠ b → ∀ w : List Bool,
      (C.dec a b w).isSome ↔ w.length = C.cap a b ∧ ofWord (w.take (rwf a b)) < nrf a b) :
    DescribesP C P B (layoutP C P B rwf nrf) where
  P_eq := by simp [LayP.P, layoutP]
  B_eq := by simp [LayP.B, layoutP]
  g_eq := by simp [LayP.g, layoutP]
  sc_eq a := by simp [LayP.sc, LayP.node, layoutP, List.getD_eq_getElem?_getD]
  nh_eq a := by simp [LayP.nh, LayP.node, layoutP, List.getD_eq_getElem?_getD]
  off_eq a b _ := by simp [LayP.off, LayP.pair, layoutP, List.getD_eq_getElem?_getD]
  wd_eq a b _ := by simp [LayP.wd, LayP.pair, layoutP, List.getD_eq_getElem?_getD]
  cps_eq a b _ := by simp [LayP.cps, LayP.pair, layoutP, List.getD_eq_getElem?_getD]
  valid a b hab w := by
    simpa [LayP.rw, LayP.nr, LayP.pair, layoutP, List.getD_eq_getElem?_getD] using hv a b hab w

variable {C}

theorem blkP_eq {P B : ℕ} {d : LayP} (hD : DescribesP C P B d) {a b : Fin g} (hab : a ≠ b) (z : List Bool) :
    blkP d a.val b.val z = C.blockAt a b z := by
  unfold blkP PairCode.blockAt
  rw [hD.off_eq a b hab, hD.wd_eq a b hab]

theorem okBlk_iff {P B : ℕ} {d : LayP} (hD : DescribesP C P B d) {a b : Fin g} (hab : a ≠ b) (z : List Bool) :
    okBlk d a.val b.val z = true ↔ (C.dec a b (C.blockAt a b z)).isSome := by
  rw [hD.valid a b hab, okBlk, ← blkP_eq hD hab, hD.wd_eq a b hab]
  simp

variable (C)

/-- What the procedure for the copy bits must compute: copy bit `j` (numbered by its place in
`rord`) from a setting of its source. -/
def ParSpecP {Ctx : Type} (par : Ctx × (ℕ × List Bool) → Bool) (c : Ctx) : Prop :=
  ∀ j : R, ∀ x ∈ C.locSetP (X.source j), par (c, (X.rord.idxOf j, C.encP (X.source j) x)) = X.par j x.1

/-- **What the T-procedure must do**: on a setting of `a` it outputs the table entry within `τ`
steps on states of size at most `S`. -/
def TSpecP {Ctx : Type} [HasSize Ctx] (Tp : Stepped (Ctx × WQ) ℤ) (c : Ctx) (τ S : ℕ) : Prop :=
  ∀ a : Fin g, ∀ x ∈ C.locSetP a, Tp.Runs (c, (a.val, C.encP a x)) τ S (X.T a x.1 x.2)

variable {C} {Ctx : Type} {lay : Ctx → LayP} {par : Ctx × (ℕ × List Bool) → Bool}

theorem projFP_eq {c : Ctx} {P B : ℕ} (hD : DescribesP C P B (lay c)) (hp : ParSpecP C par c)
    {a b : Fin g} (hab : a ≠ b) {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) :
    projFP lay par c a.val b.val (C.encP a x) = C.projP a b x := by
  unfold projFP PairCode.projP
  rw [blkP_eq hD hab, C.blockAt_encP hx (Ne.symm hab), hD.cps_eq a b hab, hD.sc_eq a]
  congr 1
  unfold copyData
  rw [List.map_map]
  refine List.map_congr_left fun j hj => ?_
  rw [Function.comp_apply]
  by_cases h : X.holder j = a
  · simp only [h, ↓reduceIte]
    have hj' : j ∈ X.heldList a := X.mem_heldList.2 h
    rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, C.drop_sumCap_encP hx, List.getElem?_map,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hj'), List.getElem_idxOf]
    rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    have hs : X.source j = a := by
      rcases X.mem_pairCopies.1 hj with h' | h'
      · exact absurd h'.1 h
      · exact h'.2
    subst hs
    exact hp j x hx

theorem memFP_eq {c : Ctx} {P B : ℕ} (hD : DescribesP C P B (lay c)) (a : Fin g) (z : List Bool) :
    memFP lay (c, (a.val, z)) = decide (z ∈ (X.netP C).S a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, C.mem_SP_iff a z]
  unfold memFP
  have hl : (lay c).len a.val = (X.netP C).len a := by
    simp [LayP.len, hD.sc_eq a, hD.nh_eq a, netP]
  simp only [hl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    hD.g_eq]
  refine and_congr Iff.rfl ⟨fun h b hb => ?_, fun h b hb => ?_⟩
  · rcases h b.val b.2 with h' | h'
    · exact absurd (Fin.ext h') hb
    · exact (okBlk_iff hD (Ne.symm hb) z).1 h'
  · by_cases hba : b = a.val
    · exact Or.inl hba
    · have hne : (⟨b, hb⟩ : Fin g) ≠ a := fun h' => hba (congrArg Fin.val h')
      exact Or.inr ((okBlk_iff hD (Ne.symm hne) z).2 (h _ hne))

theorem cP_le {P B : ℕ} (hN : (X.netP C).Is P B) {a b : Fin g} (hab : a ≠ b) : (X.netP C).c a b ≤ P :=
  le_trans (Finset.single_le_sum (f := fun b => (X.netP C).c a b) (fun _ _ => Nat.zero_le _)
    (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)) (hN.i a)

variable [HasSize Ctx]

/-- **Definition 2(iii) for the procedures**: each answer within `τ` steps on states of size at
most `S + size c + 2g + 4P + 8`. -/
theorem procsP_give (Tp : Stepped (Ctx × WQ) ℤ) {c : Ctx} {P B τ S : ℕ}
    (hN : (X.netP C).Is P B) (hD : DescribesP C P B (lay c)) (hp : ParSpecP C par c)
    (hT : TSpecP C Tp c τ S) (hτ : 1 ≤ τ) :
    (procsP lay par Tp).Give c (X.netP C) P B τ (S + size c + 2 * g + 4 * P + 8) where
  P_eq := hD.P_eq
  B_eq := hD.B_eq
  len_eq a := by simp [procsP, LayP.len, hD.sc_eq a, hD.nh_eq a, netP]
  cap_eq a b hab := by
    simp [procsP, LayP.cap, hD.wd_eq a b hab, hD.cps_eq a b hab, netP, copyData]
  mem_runs a z hz := by
    have h := Stepped.ofFun_runs (memFP lay) (c, (a.val, z))
    rw [memFP_eq hD a z] at h
    refine h.mono hτ ?_
    have h1 := size_fin' a
    have h2 := hN.len_le a
    have h3 : size (decide (z ∈ (X.netP C).S a)) = 1 := rfl
    simp only [size_prod, size_word, hz, h3] at *
    omega
  W_runs a z hz := by
    obtain ⟨x, hx, rfl⟩ := C.mem_SP.1 hz
    have h := hT a x hx
    have e : (X.netP C).W a (C.encP a x) = X.T a x.1 x.2 := by
      simp only [netP, C.dec_encP hx]
    rw [e]
    exact h.mono le_rfl (by omega)
  Ψ_runs a b hab z hz z' hz' := by
    obtain ⟨x, hx, rfl⟩ := C.mem_SP.1 hz
    obtain ⟨x', hx', rfl⟩ := C.mem_SP.1 hz'
    have h := Stepped.ofFun_runs (psiFP lay par) (c, ((a.val, b.val), (C.encP a x, C.encP b x')))
    have e : psiFP lay par (c, ((a.val, b.val), (C.encP a x, C.encP b x'))) =
        (X.netP C).Ψ a b (C.encP a x) (C.encP b x') := by
      simp only [psiFP, netP, C.dec_encP hx, C.dec_encP hx', projFP_eq hD hp hab hx,
        projFP_eq hD hp (Ne.symm hab) hx']
    rw [e] at h
    refine h.mono hτ ?_
    have h1 := size_fin' a
    have h1' := size_fin' b
    have h2 := hN.len_le a
    have h2' := hN.len_le b
    have h3 : size ((X.netP C).Ψ a b (C.encP a x) (C.encP b x')) ≤ 2 := by
      simp only [netP]; exact size_boole _
    have h4 := C.length_encP hx
    have h4' := C.length_encP hx'
    simp only [size_prod, size_word] at *
    omega
  f_runs a b hab z hz θ hθ := by
    obtain ⟨x, hx, rfl⟩ := C.mem_SP.1 hz
    have h := Stepped.ofFun_runs (fFP lay par) (c, ((a.val, b.val), (C.encP a x, θ)))
    have e : fFP lay par (c, ((a.val, b.val), (C.encP a x, θ))) = (X.netP C).f a b (C.encP a x) θ := by
      simp only [fFP, netP, C.dec_encP hx, projFP_eq hD hp hab hx]
    rw [e] at h
    refine h.mono hτ ?_
    have h1 := size_fin' a
    have h1' := size_fin' b
    have h2 := hN.len_le a
    have h3 : size ((X.netP C).f a b (C.encP a x) θ) ≤ 2 := by
      simp only [netP]; exact size_boole _
    have h4 := C.length_encP hx
    have h5 : θ.length = (X.netP C).c a b := mem_words.1 hθ
    have h6 := cP_le hN hab
    simp only [size_prod, size_word] at *
    omega

end LabelSystem

/-! ### Polynomial-time steps and the network given by procedures -/

variable {Ctx : Type} [Enc Ctx] [HasSize Ctx] [Carried Ctx] {lay : Ctx → LayP}
  {par : Ctx × (ℕ × List Bool) → Bool}

/-- The numbers are given in unary and the four procedures have polynomial-time steps. -/
theorem procsP_keeps (hlay : PolyT lay) (hpar : PolyT par) {Tp : Stepped (Ctx × WQ) ℤ}
    (hT : Nonempty (IsPolyT Tp)) : (procsP lay par Tp).Keeps where
  len := LayP.len_unary (d := fun p : Ctx × ℕ => lay p.1) (by fun_prop) (by fun_prop)
  cap := LayP.cap_unary (d := fun p : Ctx × ℕ × ℕ => lay p.1) (by fun_prop) (by fun_prop) (by fun_prop)
  mem := ⟨IsPolyT.ofFun (memFP_polyT hlay)⟩
  W := hT
  Ψ := ⟨IsPolyT.ofFun (psiFP_polyT hlay hpar)⟩
  f := ⟨IsPolyT.ofFun (fFP_polyT hlay hpar)⟩

theorem procsP_poly (hlay : PolyT lay) (hpar : PolyT par) {Tp : Stepped (Ctx × WQ) ℤ}
    (hT : Nonempty (IsPolyT Tp)) : Given.PolyTimeProcs (Given.ofProcs (procsP lay par Tp)) := by
  have h := procsP_keeps hlay hpar hT
  obtain ⟨i1⟩ := h.mem
  obtain ⟨i2⟩ := h.W
  obtain ⟨i3⟩ := h.Ψ
  obtain ⟨i4⟩ := h.f
  exact ⟨LayP.P_unary hlay, LayP.B_unary hlay, h.len, h.cap, ⟨QueryMachine.IsPolyQ.lift _⟩,
    ⟨QueryMachine.IsPolyQ.lift _⟩, ⟨QueryMachine.IsPolyQ.lift _⟩, ⟨QueryMachine.IsPolyQ.lift _⟩⟩

/-- **The network with per-pair codes, given by procedures** (`Given.IsGivenNetwork`, the form
consumed by `Given.stOnGiven` / `Given.onSteps`). The only non-generic ingredient is the
T-procedure `Tp`; the state bound grows by `size c + 2g + 4P + 8`. -/
theorem procsP_given {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R]
    [DecidableEq R] [Fintype L] [DecidableEq L] {X : LabelSystem g K R L} (C : X.PairCode)
    (hlay : PolyT lay) (hpar : PolyT par) {Tp : Stepped (Ctx × WQ) ℤ} (hTp : Nonempty (IsPolyT Tp))
    {c : Ctx} {P B τ S : ℕ} (hN : (X.netP C).Is P B) (hD : LabelSystem.DescribesP C P B (lay c))
    (hp : LabelSystem.ParSpecP C par c) (hT : LabelSystem.TSpecP C Tp c τ S) (hτ : 1 ≤ τ) :
    Given.IsGivenNetwork (Given.ofProcs (procsP lay par Tp)) Given.noTable c (X.netP C) P B τ
      (S + size c + 2 * g + 4 * P + 8) :=
  ⟨⟨hN, hτ, LabelSystem.procsP_give Tp hN hD hp hT hτ⟩, procsP_poly hlay hpar hTp⟩

/-! ### The rank code -/

namespace LabelSystem

open Rank

variable {g : ℕ} {K R : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  {X : LabelSystem g K R Label} {s : Fin g → Fin g → ℕ} {hs : ∀ a b, s a b = s b a} {hd : X.dflt = Label.N}

/-- The rank-field widths `cw(e_ab, s_ab)` of the rank code. -/
def rankRw (X : LabelSystem g K R Label) (s : Fin g → Fin g → ℕ) (a b : Fin g) : ℕ :=
  cw (X.pairItems a b).length (s a b)

/-- The numbers of ranks `C(e_ab, s_ab)` of the rank code. -/
def rankNr (X : LabelSystem g K R Label) (s : Fin g → Fin g → ℕ) (a b : Fin g) : ℕ :=
  Nat.choose (X.pairItems a b).length (s a b)

/-- **The validity test of the rank code**: a block decodes iff it has width `cw(e,s) + 2s` and its
rank field is `< C(e,s)`. -/
theorem rank_valid (a b : Fin g) (w : List Bool) :
    ((X.rankPC s hs hd).dec a b w).isSome ↔
      w.length = (X.rankPC s hs hd).cap a b ∧ ofWord (w.take (rankRw X s a b)) < rankNr X s a b :=
  decR_isSome_iff _ _ _

/-- The canonical layout of the rank-encoded network. -/
noncomputable def rankLayout (X : LabelSystem g K R Label) (s : Fin g → Fin g → ℕ) (hs : ∀ a b, s a b = s b a)
    (hd : X.dflt = Label.N) (P B : ℕ) : LayP :=
  layoutP (X.rankPC s hs hd) P B (rankRw X s) (rankNr X s)

theorem rankLayout_describes (P B : ℕ) :
    DescribesP (X.rankPC s hs hd) P B (rankLayout X s hs hd P B) :=
  layoutP_describes _ P B _ _ fun a b _ w => rank_valid a b w

end LabelSystem

end EthFollowup.ExactHC
