/-
# Procedures for the label-sharing network (module C1b, generic part)

`LabelNetwork.lean` (C1a) builds, from a `LabelSystem X` and a label code `C`, the network
`X.net C : Eight.SecNetworks.Net g`. Here we give `X.net C` by procedures in Anthropic's cost model
and prove `Given.IsGivenNetwork (Given.ofProcs (labelProcs lay par Tp)) Given.noTable c (X.net C) P B τ S'`
(the form consumed by `Given.stOnGiven` / `Given.onSteps`, as in `Given.onFormula`).

Everything except the node tables `T a` is bit manipulation on a *layout* `Lay`, a plain data
object carried by the context, which lists (in unary where Definition 2(iii) needs unary numbers):

* `P`, `B`, the code width `w`, the list of all code words of `C`;
* for every node `a`: the number of incident items and the number of held copy bits;
* for every ordered pair `(a, b)`: the block indices (in a setting of `a`) of the items on `{a,b}`,
  and, for each copy bit on `{a,b}`, either `(true, i)` (held by `a`: bit `i` of the held part) or
  `(false, j)` (computed at `a`: the copy bit `j`, numbered by its place in `rord`).

Parameters of the procedures (`labelProcs lay par Tp`), over an arbitrary context type `Ctx`:

* `lay : Ctx → Lay`, polynomial-time (`PolyT lay`), with `Describes X C P B (lay c)`;
* `par : Ctx × (ℕ × List Bool) → Bool`, polynomial-time: `par (c, (j, z))` is the copy bit number
  `j`, computed from a setting `z` of its source (`ParSpec`);
* **the T-procedure** `Tp : Stepped (Ctx × WQ) ℤ` with `Nonempty (IsPolyT Tp)`: on `(c, (a, z))`
  with `z = X.enc C a x` a setting of `a` (labels of the items at `a`, copy bits held by `a`) it
  outputs `X.T a x.1 x.2` within `τ` steps on states of size `≤ S` (`TSpec`). It is used as the
  procedure for `W` unchanged.

Membership, `Ψ` and `f` are one-step machines (`Stepped.ofFun`) of polynomial-time functions.
Main results:

* `labelProcs_give` : `Procs.Give` with `τ` and `S' = S + size c + 2g + 4P + 8`;
* `labelProcs_keeps` : `Procs.Keeps` (unary numbers, polynomial-time steps);
* `labelProcs_given` : `Given.IsGivenNetwork (Given.ofProcs (labelProcs lay par Tp)) Given.noTable c
  (X.net C) P B τ (S + size c + 2 * g + 4 * P + 8)`;
* `layout_describes` : a canonical layout `X.layout C P B` satisfies `Describes`.
-/
import EthFollowup.ExactHC.LabelNetwork
import GivenStatement
import QueryMachines.Poly
import ToTuring.Poly.IsPoly

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog QueryMachines Eight.SecNetworks Finset

/-! ### The layout -/

/-- The layout data: `((P, B), (w, codes)), (nodes, pairs)`. -/
abbrev Lay : Type :=
  ((List Unit × List Unit) × (List Unit × List (List Bool))) ×
    (List (List Unit × List Unit) × List (List (List ℕ × List (Bool × ℕ))))

namespace Lay

/-- The bound `P`. -/
def P (d : Lay) : ℕ := d.1.1.1.length
/-- The bound `B`. -/
def B (d : Lay) : ℕ := d.1.1.2.length
/-- The code width `w`. -/
def w (d : Lay) : ℕ := d.1.2.1.length
/-- The code words. -/
def codes (d : Lay) : List (List Bool) := d.1.2.2
/-- The data of the node `a`. -/
def node (d : Lay) (a : ℕ) : List Unit × List Unit := d.2.1.getD a ([], [])
/-- The number of items at `a`. -/
def na (d : Lay) (a : ℕ) : ℕ := (d.node a).1.length
/-- The number of copy bits held by `a`. -/
def nh (d : Lay) (a : ℕ) : ℕ := (d.node a).2.length
/-- The data of the ordered pair `(a, b)`. -/
def pair (d : Lay) (a b : ℕ) : List ℕ × List (Bool × ℕ) := (d.2.2.getD a []).getD b ([], [])
/-- `P_a`. -/
def len (d : Lay) (a : ℕ) : ℕ := d.na a * d.w + d.nh a
/-- `c_{a,b}`. -/
def cap (d : Lay) (a b : ℕ) : ℕ := (d.pair a b).1.length * d.w + (d.pair a b).2.length

end Lay

/-- Block `i` (of width `w`) of a bit string. -/
def blk (w : ℕ) (z : List Bool) (i : ℕ) : List Bool := (z.drop (i * w)).take w

/-! ### The procedures -/

section Procs

variable {Ctx : Type} (lay : Ctx → Lay) (par : Ctx × (ℕ × List Bool) → Bool)

/-- The shared bits of the pair `(a, b)`, computed from a setting `z` of `a`. -/
def projF (c : Ctx) (a b : ℕ) (z : List Bool) : List Bool :=
  ((lay c).pair a b).1.flatMap (fun i => blk (lay c).w z i) ++
    ((lay c).pair a b).2.map fun e =>
      if e.1 = true then z.getD ((lay c).na a * (lay c).w + e.2) false else par (c, (e.2, z))

/-- Membership: the right length, and every label block is a code word. -/
def memF (x : Ctx × WQ) : Bool :=
  decide (x.2.2.length = (lay x.1).len x.2.1) &&
    (List.range ((lay x.1).na x.2.1)).all fun i => (lay x.1).codes.contains (blk (lay x.1).w x.2.2 i)

/-- `Ψ_{a,b}(z, z') = [proj_{a,b} z = proj_{b,a} z']`. -/
def psiF (x : Ctx × PsiQ) : ℤ :=
  if projF lay par x.1 x.2.1.1 x.2.1.2 x.2.2.1 = projF lay par x.1 x.2.1.2 x.2.1.1 x.2.2.2 then 1 else 0

/-- `f_{a,b}(z, θ) = [proj_{a,b} z = θ]`. -/
def fF (x : Ctx × FQ) : ℤ :=
  if projF lay par x.1 x.2.1.1 x.2.1.2 x.2.2.1 = x.2.2.2 then 1 else 0

variable [HasSize Ctx]

/-- **The procedures of the label-sharing network**; `Tp` is the procedure for the node tables. -/
def labelProcs (Tp : Stepped (Ctx × WQ) ℤ) : Procs Ctx where
  P c := (lay c).P
  B c := (lay c).B
  len c a := (lay c).len a
  cap c a b := (lay c).cap a b
  mem := Stepped.ofFun (memF lay)
  W := Tp
  Ψ := Stepped.ofFun (psiF lay par)
  f := Stepped.ofFun (fF lay par)

end Procs

/-! ### Polynomial time -/

section Poly

variable {α : Type} [Enc α]

@[fun_prop] theorem Lay.P_polyT {d : α → Lay} (hd : PolyT d) : PolyT fun x => (d x).P := by
  unfold Lay.P; fun_prop
@[fun_prop] theorem Lay.B_polyT {d : α → Lay} (hd : PolyT d) : PolyT fun x => (d x).B := by
  unfold Lay.B; fun_prop
@[fun_prop] theorem Lay.w_polyT {d : α → Lay} (hd : PolyT d) : PolyT fun x => (d x).w := by
  unfold Lay.w; fun_prop
@[fun_prop] theorem Lay.codes_polyT {d : α → Lay} (hd : PolyT d) : PolyT fun x => (d x).codes := by
  unfold Lay.codes; fun_prop
@[fun_prop] theorem Lay.node_polyT {d : α → Lay} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).node (a x) := by
  unfold Lay.node; fun_prop
@[fun_prop] theorem Lay.na_polyT {d : α → Lay} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).na (a x) := by
  unfold Lay.na; fun_prop
@[fun_prop] theorem Lay.nh_polyT {d : α → Lay} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).nh (a x) := by
  unfold Lay.nh; fun_prop
@[fun_prop] theorem Lay.pair_polyT {d : α → Lay} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => (d x).pair (a x) (b x) := by
  unfold Lay.pair; fun_prop
@[fun_prop] theorem Lay.len_polyT {d : α → Lay} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    PolyT fun x => (d x).len (a x) := by
  unfold Lay.len; fun_prop
@[fun_prop] theorem blk_polyT {w i : α → ℕ} {z : α → List Bool} (hw : PolyT w) (hz : PolyT z)
    (hi : PolyT i) : PolyT fun x => blk (w x) (z x) (i x) := by
  unfold blk; fun_prop

theorem Lay.na_unary {d : α → Lay} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    Unary fun x => (d x).na (a x) := by
  unfold Lay.na
  exact Unary.of_length (w := fun x => ((d x).node (a x)).1) (by fun_prop)

theorem Lay.nh_unary {d : α → Lay} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    Unary fun x => (d x).nh (a x) := by
  unfold Lay.nh
  exact Unary.of_length (w := fun x => ((d x).node (a x)).2) (by fun_prop)

theorem Lay.w_unary {d : α → Lay} (hd : PolyT d) : Unary fun x => (d x).w := by
  unfold Lay.w
  exact Unary.of_length (w := fun x => (d x).1.2.1) (by fun_prop)

theorem Lay.P_unary {d : α → Lay} (hd : PolyT d) : Unary fun x => (d x).P := by
  unfold Lay.P
  exact Unary.of_length (w := fun x => (d x).1.1.1) (by fun_prop)

theorem Lay.B_unary {d : α → Lay} (hd : PolyT d) : Unary fun x => (d x).B := by
  unfold Lay.B
  exact Unary.of_length (w := fun x => (d x).1.1.2) (by fun_prop)

theorem Lay.len_unary {d : α → Lay} {a : α → ℕ} (hd : PolyT d) (ha : PolyT a) :
    Unary fun x => (d x).len (a x) := by
  unfold Lay.len
  exact ((Lay.na_unary hd ha).mul (Lay.w_unary hd)).add (Lay.nh_unary hd ha)

theorem Lay.cap_unary {d : α → Lay} {a b : α → ℕ} (hd : PolyT d) (ha : PolyT a) (hb : PolyT b) :
    Unary fun x => (d x).cap (a x) (b x) := by
  unfold Lay.cap
  exact ((Unary.of_length (w := fun x => ((d x).pair (a x) (b x)).1) (by fun_prop)).mul
    (Lay.w_unary hd)).add (Unary.of_length (w := fun x => ((d x).pair (a x) (b x)).2) (by fun_prop))

variable {Ctx : Type} [Enc Ctx] {lay : Ctx → Lay} {par : Ctx × (ℕ × List Bool) → Bool}

@[fun_prop] theorem projF_polyT (hlay : PolyT lay) (hpar : PolyT par) {c : α → Ctx} {a b : α → ℕ}
    {z : α → List Bool} (hc : PolyT c) (ha : PolyT a) (hb : PolyT b) (hz : PolyT z) :
    PolyT fun x => projF lay par (c x) (a x) (b x) (z x) := by
  unfold projF
  fun_prop

theorem memF_polyT (hlay : PolyT lay) : PolyT (memF lay) := by
  have hr : PolyT fun x : Ctx × WQ => List.range ((lay x.1).na x.2.1) :=
    PolyT.range (Lay.na_unary (by fun_prop) (by fun_prop))
  unfold memF
  fun_prop

theorem psiF_polyT (hlay : PolyT lay) (hpar : PolyT par) : PolyT (psiF lay par) := by
  unfold psiF
  fun_prop

theorem fF_polyT (hlay : PolyT lay) (hpar : PolyT par) : PolyT (fF lay par) := by
  unfold fF
  fun_prop

end Poly

/-! ### List lemmas -/

section Lists

variable {L : Type} {w : ℕ} (C : LabelCode L w) {ι : Type} [DecidableEq ι]

theorem blk_succ (z : List Bool) (i : ℕ) : blk w z (i + 1) = blk w (z.drop w) i := by
  unfold blk
  rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]

theorem blk_zero (z : List Bool) : blk w z 0 = z.take w := by
  simp [blk]

theorem blk_encL (ℓ : ι → L) (rest : List Bool) :
    ∀ (ks : List ι) (i : ℕ) (hi : i < ks.length), blk w (encL C ks ℓ ++ rest) i = C.enc (ℓ ks[i])
  | [], i, hi => absurd hi (by simp)
  | k :: ks, 0, _ => by
    simp only [blk_zero, encL, List.flatMap_cons, List.append_assoc, List.getElem_cons_zero]
    exact List.take_left' (C.len _)
  | k :: ks, i + 1, hi => by
    rw [blk_succ]
    simp only [encL, List.flatMap_cons, List.append_assoc, List.drop_left' (C.len _),
      List.getElem_cons_succ]
    exact blk_encL ℓ rest ks i (by simpa using hi)

theorem decL_not_mem (d : L) : ∀ (ks : List ι) (z : List Bool) (k : ι), k ∉ ks → decL C d ks z k = d
  | [], _, _, _ => rfl
  | k' :: ks, z, k, hk => by
    have hk' : k ≠ k' ∧ k ∉ ks := by simpa using hk
    simp only [decL]
    rw [Function.update_of_ne hk'.1]
    exact decL_not_mem d ks _ k hk'.2

theorem decY_not_mem : ∀ (js : List ι) (z : List Bool) (j : ι), j ∉ js → decY js z j = false
  | [], _, _, _ => rfl
  | j' :: js, z, j, hj => by
    have hj' : j ≠ j' ∧ j ∉ js := by simpa using hj
    simp only [decY]
    rw [Function.update_of_ne hj'.1]
    exact decY_not_mem js _ j hj'.2

theorem encL_decL (d : L) :
    ∀ (ks : List ι), ks.Nodup → ∀ z : List Bool, (∀ i < ks.length, ∃ l, C.enc l = blk w z i) →
      encL C ks (decL C d ks z) = z.take (ks.length * w)
  | [], _, z, _ => by simp [encL]
  | k :: ks, hn, z, hb => by
    have hk := List.nodup_cons.1 hn
    have ih := encL_decL d ks hk.2 (z.drop w) fun i hi => by
      rw [← blk_succ]; exact hb (i + 1) (by simp; omega)
    obtain ⟨l, hl⟩ := hb 0 (by simp)
    rw [blk_zero] at hl
    simp only [encL, List.flatMap_cons, decL, Function.update_self]
    have e2 : (ks.flatMap fun k' => C.enc (Function.update (decL C d ks (z.drop w)) k
        (C.dec (z.take w)) k')) = encL C ks (decL C d ks (z.drop w)) := by
      refine encL_congr C fun k' hk' => ?_
      rw [Function.update_of_ne (fun h => hk.1 (h ▸ hk') : k' ≠ k)]
    rw [e2, ih, ← hl, C.dec_enc, hl, List.length_cons, Nat.succ_mul, Nat.add_comm _ w,
      List.take_add]

theorem map_decY : ∀ (js : List ι), js.Nodup → ∀ u : List Bool, u.length = js.length →
    js.map (decY js u) = u
  | [], _, u, hu => by simpa using (List.length_eq_zero_iff.1 hu).symm
  | j :: js, hn, u, hu => by
    have hj := List.nodup_cons.1 hn
    obtain ⟨b, u, rfl⟩ : ∃ b u', u = b :: u' := by
      cases u with
      | nil => simp at hu
      | cons b u' => exact ⟨b, u', rfl⟩
    simp only [List.map_cons, decY, Function.update_self, List.headD_cons, List.tail_cons]
    congr 1
    rw [List.map_congr_left fun j' hj' => Function.update_of_ne (fun h => hj.1 (h ▸ hj') : j' ≠ j) _ _]
    exact map_decY js hj.2 u (by simpa using hu)

end Lists

/-! ### The layout described -/

namespace LabelSystem

variable {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L] (X : LabelSystem g K R L) {w : ℕ} (C : LabelCode L w)

/-- The data of the ordered pair `(a, b)` in the layout. -/
def pairData (a b : Fin g) : List ℕ × List (Bool × ℕ) :=
  ((X.pairItems a b).map fun k => (X.incList a).idxOf k,
    (X.pairCopies a b).map fun j =>
      if X.holder j = a then (true, (X.heldList a).idxOf j) else (false, X.rord.idxOf j))

/-- **What the layout must hold** for the network `X.net C` with parameters `P`, `B`. -/
structure Describes (P B : ℕ) (d : Lay) : Prop where
  P_eq : d.P = P
  B_eq : d.B = B
  w_eq : d.w = w
  codes_iff : ∀ u, u ∈ d.codes ↔ ∃ l, C.enc l = u
  na_eq : ∀ a : Fin g, d.na a.val = (X.incList a).length
  nh_eq : ∀ a : Fin g, d.nh a.val = (X.heldList a).length
  pair_eq : ∀ a b : Fin g, a ≠ b → d.pair a.val b.val = X.pairData a b

/-- A canonical layout. -/
noncomputable def layout (P B : ℕ) : Lay :=
  (((List.replicate P (), List.replicate B ()), (List.replicate w (), (Finset.univ : Finset L).toList.map C.enc)),
    ((List.finRange g).map fun a => (List.replicate (X.incList a).length (), List.replicate (X.heldList a).length ()),
      (List.finRange g).map fun a => (List.finRange g).map fun b => X.pairData a b))

theorem layout_describes (P B : ℕ) : X.Describes C P B (X.layout C P B) where
  P_eq := by simp [Lay.P, layout]
  B_eq := by simp [Lay.B, layout]
  w_eq := by simp [Lay.w, layout]
  codes_iff u := by simp [Lay.codes, layout]
  na_eq a := by
    simp [Lay.na, Lay.node, layout, List.getD_eq_getElem?_getD]
  nh_eq a := by
    simp [Lay.nh, Lay.node, layout, List.getD_eq_getElem?_getD]
  pair_eq a b _ := by
    simp [Lay.pair, layout, List.getD_eq_getElem?_getD]

/-! ### Settings, membership, the shared bits -/

theorem mem_S {a : Fin g} {z : List Bool} :
    z ∈ (X.net C).S a ↔ ∃ x ∈ X.locSet a, X.enc C a x = z := by
  simp [net]

theorem mem_S_iff (a : Fin g) (z : List Bool) :
    z ∈ (X.net C).S a ↔ z.length = (X.net C).len a ∧
      ∀ i < (X.incList a).length, ∃ l, C.enc l = blk w z i := by
  rw [mem_S]
  constructor
  · rintro ⟨x, -, rfl⟩
    refine ⟨X.length_enc C a x, fun i hi => ⟨x.1 (X.incList a)[i], ?_⟩⟩
    unfold enc
    rw [blk_encL C x.1 _ _ i hi]
  · rintro ⟨hl, hb⟩
    refine ⟨X.dec C a z, ?_, ?_⟩
    · simp only [locSet, mem_filter, mem_univ, true_and, dec]
      refine ⟨fun k hk => decL_not_mem C _ _ _ k (fun h => hk (X.mem_incList.1 h)),
        fun j hj => decY_not_mem _ _ j (fun h => hj (X.mem_heldList.1 h))⟩
    · unfold enc dec
      simp only
      have hn1 : (X.incList a).Nodup := X.kord_nodup.filter _
      have hn2 : (X.heldList a).Nodup := X.rord_nodup.filter _
      rw [encL_decL C _ _ hn1 z hb, map_decY _ hn2 _ (by simp [hl, net]), List.take_append_drop]

variable {Ctx : Type} {lay : Ctx → Lay} {par : Ctx × (ℕ × List Bool) → Bool}

/-- What the procedure for the copy bits must compute: copy bit `j` (numbered by its place in
`rord`) from a setting of its source. -/
def ParSpec (par : Ctx × (ℕ × List Bool) → Bool) (c : Ctx) : Prop :=
  ∀ j : R, ∀ x ∈ X.locSet (X.source j), par (c, (X.rord.idxOf j, X.enc C (X.source j) x)) = X.par j x.1

/-- **What the T-procedure must do**: on a setting of `a` (labels of the items at `a`, copy bits held
by `a`) it outputs the table entry within `τ` steps on states of size at most `S`. -/
def TSpec [HasSize Ctx] (Tp : Stepped (Ctx × WQ) ℤ) (c : Ctx) (τ S : ℕ) : Prop :=
  ∀ a : Fin g, ∀ x ∈ X.locSet a, Tp.Runs (c, (a.val, X.enc C a x)) τ S (X.T a x.1 x.2)

theorem projF_eq {c : Ctx} {P B : ℕ} (hD : X.Describes C P B (lay c)) (hp : X.ParSpec C par c)
    {a b : Fin g} (hab : a ≠ b) {x : (K → L) × (R → Bool)} (hx : x ∈ X.locSet a) :
    projF lay par c a.val b.val (X.enc C a x) = X.proj C a b x := by
  unfold projF proj
  rw [hD.pair_eq a b hab, hD.w_eq, hD.na_eq a]
  simp only [pairData]
  congr 1
  · rw [List.flatMap_map]
    unfold encL
    refine List.flatMap_congr fun k hk => ?_
    have hk' : k ∈ X.incList a := by
      rw [X.mem_incList]
      rcases X.mem_pairItems.1 hk with h | h
      exacts [Or.inl h.1, Or.inr h.2]
    unfold enc
    rw [blk_encL C x.1 _ _ _ (List.idxOf_lt_length_of_mem hk'), List.getElem_idxOf]
  · rw [List.map_map]
    refine List.map_congr_left fun j hj => ?_
    rw [Function.comp_apply]
    by_cases h : X.holder j = a
    · simp only [h, ↓reduceIte]
      have hj' : j ∈ X.heldList a := X.mem_heldList.2 h
      unfold enc
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_encL]; omega)]
      rw [length_encL, Nat.add_sub_cancel_left, List.getElem?_map,
        List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hj'), List.getElem_idxOf]
      rfl
    · simp only [h, ↓reduceIte, Bool.false_eq_true]
      have hs : X.source j = a := by
        rcases X.mem_pairCopies.1 hj with h' | h'
        · exact absurd h'.1 h
        · exact h'.2
      subst hs
      exact hp j x hx

theorem memF_eq {c : Ctx} {P B : ℕ} (hD : X.Describes C P B (lay c)) (a : Fin g) (z : List Bool) : memF lay (c, (a.val, z)) = decide (z ∈ (X.net C).S a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, X.mem_S_iff C a z]
  unfold memF
  have hl : (lay c).len a.val = (X.net C).len a := by
    simp [Lay.len, hD.na_eq a, hD.nh_eq a, hD.w_eq, net]
  simp only [hl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.contains_iff_mem, hD.codes_iff, hD.na_eq a, hD.w_eq]

/-! ### Definition 2(iii) -/

theorem size_word (z : List Bool) : size z = 2 * z.length + 1 := by
  induction z with
  | nil => rfl
  | cons b z ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢
    omega

theorem size_fin' (a : Fin g) : size a.val ≤ g + 1 := by
  simp only [size_nat]
  exact Nat.add_le_add_right (Nat.size_le.2 (a.2.trans Nat.lt_two_pow_self)) 1

theorem size_boole (p : Prop) [Decidable p] : size (if p then (1 : ℤ) else 0) ≤ 2 := by
  simp only [size_int]
  refine Nat.add_le_add_right (Nat.size_le.2 ?_) 1
  split_ifs <;> simp

theorem c_le {P B : ℕ} (hN : (X.net C).Is P B) {a b : Fin g} (hab : a ≠ b) : (X.net C).c a b ≤ P :=
  le_trans (Finset.single_le_sum (f := fun b => (X.net C).c a b) (fun _ _ => Nat.zero_le _)
    (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)) (hN.i a)

variable [HasSize Ctx]

/-- **Definition 2(iii) for the procedures**: each answer within `τ` steps on states of size at
most `S + size c + 2g + 4P + 8`. -/
theorem labelProcs_give (Tp : Stepped (Ctx × WQ) ℤ) {c : Ctx} {P B τ S : ℕ}
    (hN : (X.net C).Is P B) (hD : X.Describes C P B (lay c)) (hp : X.ParSpec C par c)
    (hT : X.TSpec C Tp c τ S) (hτ : 1 ≤ τ) :
    (labelProcs lay par Tp).Give c (X.net C) P B τ (S + size c + 2 * g + 4 * P + 8) where
  P_eq := hD.P_eq
  B_eq := hD.B_eq
  len_eq a := by simp [labelProcs, Lay.len, hD.na_eq a, hD.nh_eq a, hD.w_eq, net]
  cap_eq a b hab := by
    simp [labelProcs, Lay.cap, hD.pair_eq a b hab, hD.w_eq, net, pairData]
  mem_runs a z hz := by
    have h := Stepped.ofFun_runs (memF lay) (c, (a.val, z))
    rw [X.memF_eq C hD a z] at h
    refine h.mono hτ ?_
    have h1 := size_fin' a
    have h2 := hN.len_le a
    have h3 : size (decide (z ∈ (X.net C).S a)) = 1 := rfl
    simp only [size_prod, size_word, hz, h3] at *
    omega
  W_runs a z hz := by
    obtain ⟨x, hx, rfl⟩ := (X.mem_S C).1 hz
    have h := hT a x hx
    have e : (X.net C).W a (X.enc C a x) = X.T a x.1 x.2 := by
      simp only [net, X.dec_enc C hx]
    rw [e]
    exact h.mono le_rfl (by omega)
  Ψ_runs a b hab z hz z' hz' := by
    obtain ⟨x, hx, rfl⟩ := (X.mem_S C).1 hz
    obtain ⟨x', hx', rfl⟩ := (X.mem_S C).1 hz'
    have h := Stepped.ofFun_runs (psiF lay par) (c, ((a.val, b.val), (X.enc C a x, X.enc C b x')))
    have e : psiF lay par (c, ((a.val, b.val), (X.enc C a x, X.enc C b x'))) =
        (X.net C).Ψ a b (X.enc C a x) (X.enc C b x') := by
      simp only [psiF, net, X.dec_enc C hx, X.dec_enc C hx', X.projF_eq C hD hp hab hx,
        X.projF_eq C hD hp (Ne.symm hab) hx']
    rw [e] at h
    refine h.mono hτ ?_
    have h1 := size_fin' a
    have h1' := size_fin' b
    have h2 := hN.len_le a
    have h2' := hN.len_le b
    have h3 : size ((X.net C).Ψ a b (X.enc C a x) (X.enc C b x')) ≤ 2 := size_boole _
    have h4 := X.length_enc C a x
    have h4' := X.length_enc C b x'
    simp only [size_prod, size_word] at *
    omega
  f_runs a b hab z hz θ hθ := by
    obtain ⟨x, hx, rfl⟩ := (X.mem_S C).1 hz
    have h := Stepped.ofFun_runs (fF lay par) (c, ((a.val, b.val), (X.enc C a x, θ)))
    have e : fF lay par (c, ((a.val, b.val), (X.enc C a x, θ))) = (X.net C).f a b (X.enc C a x) θ := by
      simp only [fF, net, X.dec_enc C hx, X.projF_eq C hD hp hab hx]
    rw [e] at h
    refine h.mono hτ ?_
    have h1 := size_fin' a
    have h1' := size_fin' b
    have h2 := hN.len_le a
    have h3 : size ((X.net C).f a b (X.enc C a x) θ) ≤ 2 := size_boole _
    have h4 := X.length_enc C a x
    have h5 : θ.length = (X.net C).c a b := mem_words.1 hθ
    have h6 := X.c_le C hN hab
    simp only [size_prod, size_word] at *
    omega

end LabelSystem

/-! ### Polynomial-time steps -/

variable {Ctx : Type} [Enc Ctx] [HasSize Ctx] [Carried Ctx] {lay : Ctx → Lay}
  {par : Ctx × (ℕ × List Bool) → Bool}

/-- The numbers are given in unary and the four procedures have polynomial-time steps. -/
theorem labelProcs_keeps (hlay : PolyT lay) (hpar : PolyT par) {Tp : Stepped (Ctx × WQ) ℤ}
    (hT : Nonempty (IsPolyT Tp)) : (labelProcs lay par Tp).Keeps where
  len := Lay.len_unary (d := fun p : Ctx × ℕ => lay p.1) (by fun_prop) (by fun_prop)
  cap := Lay.cap_unary (d := fun p : Ctx × ℕ × ℕ => lay p.1) (by fun_prop) (by fun_prop) (by fun_prop)
  mem := ⟨IsPolyT.ofFun (memF_polyT hlay)⟩
  W := hT
  Ψ := ⟨IsPolyT.ofFun (psiF_polyT hlay hpar)⟩
  f := ⟨IsPolyT.ofFun (fF_polyT hlay hpar)⟩

theorem labelProcs_poly (hlay : PolyT lay) (hpar : PolyT par) {Tp : Stepped (Ctx × WQ) ℤ}
    (hT : Nonempty (IsPolyT Tp)) : Given.PolyTimeProcs (Given.ofProcs (labelProcs lay par Tp)) := by
  have h := labelProcs_keeps hlay hpar hT
  obtain ⟨i1⟩ := h.mem
  obtain ⟨i2⟩ := h.W
  obtain ⟨i3⟩ := h.Ψ
  obtain ⟨i4⟩ := h.f
  exact ⟨Lay.P_unary hlay, Lay.B_unary hlay, h.len, h.cap, ⟨QueryMachine.IsPolyQ.lift _⟩,
    ⟨QueryMachine.IsPolyQ.lift _⟩, ⟨QueryMachine.IsPolyQ.lift _⟩, ⟨QueryMachine.IsPolyQ.lift _⟩⟩

/-- **The label-sharing network, given by procedures** (`Given.IsGivenNetwork`, the form consumed by
`Given.stOnGiven` / `Given.onSteps`). The only non-generic ingredient is the T-procedure `Tp`; the
state bound grows by `size c + 2g + 4P + 8`. -/
theorem labelProcs_given {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R]
    [DecidableEq R] [Fintype L] [DecidableEq L] (X : LabelSystem g K R L) {w : ℕ} (C : LabelCode L w)
    (hlay : PolyT lay) (hpar : PolyT par) {Tp : Stepped (Ctx × WQ) ℤ} (hTp : Nonempty (IsPolyT Tp))
    {c : Ctx} {P B τ S : ℕ} (hN : (X.net C).Is P B) (hD : X.Describes C P B (lay c))
    (hp : X.ParSpec C par c) (hT : X.TSpec C Tp c τ S) (hτ : 1 ≤ τ) :
    Given.IsGivenNetwork (Given.ofProcs (labelProcs lay par Tp)) Given.noTable c (X.net C) P B τ
      (S + size c + 2 * g + 4 * P + 8) :=
  ⟨⟨hN, hτ, X.labelProcs_give C Tp hN hD hp hT hτ⟩, labelProcs_poly hlay hpar hTp⟩

end EthFollowup.ExactHC
