/-
# The HC network packages, and Theorem 1 unconditionally (module C3, final glue)

`research/lean-blueprint.md`, module C3. We construct, for every `g ≥ 1`, a `LabelPackage g 6`
(Assembly.lean, C2) and conclude `theorem1` from `theorem1_TM_of_label`.

* **Context** `Ctx = GIn = List Unit × List Bool` (the graph as read by `read1` from `code G`);
  `prep = read1`. Everything else is recomputed by polynomial-time functions of the graph:
  * `bW`: the partition of Lemma 6.2 (greedy, identity order; `bW_aOf`: it is `balancedPartition`);
  * `cplW`: the crossing pairs `(u, v)`, `u ~ v`, `β u < β v`, in lexicographic order, which is the
    crossing order `crossF : Crossing G (βF g G) m` (root `0`);
  * `μ = muW = ⌊(2m + gΔ)/g⌋` (`mu_le_muW`: every blob degree sum is `≤ μ`; `g_muW_le`);
  * `layW`: the layout (`layW_describes`), `rdW`: the reader of the node-table machine
    (`rdW_desc : TDesc …`), `parW`: the copy bits via `parBit` (`parSpec_hc`).
  The `g`-only data (copy bits) are constant tables.
* **Parameters**: `w = 3`, `P = 3μ + g² + 1`, `B = 2μ + 1`, `τ = 2·8^μ`,
  `S = 2·cR(7(size G + g + 2P + 3) + 1)^{cR} + 9μ + 9` (`cR` from `PolyT rdW`, via `size ≤ len`).
* **Results**: `Pkg.labelPackage`, `exists_labelPackage : ∃ c₀, ∀ g ≥ 1, Nonempty (LabelPackage g c₀)`
  (with `c₀ = 6`), and `theorem1` (unconditional Theorem 1 at TM level). Standard axioms only.
-/
import EthFollowup.ExactHC.Assembly
import EthFollowup.ExactHC.HCNetwork
import EthFollowup.ExactHC.TableProc

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace Pkg

open Groundwork Groundwork.Prog GraphProblems Asm Finset

/-! ## The `g`-only data (constant tables) -/

section Const

variable (g : ℕ)

/-- The copy bits held by `a` (the `heldList` of `hcSystem`). -/
def heldF (a : Fin g) : List (CopyIdx g) := (copyList g).filter fun j => decide (j.1.1 = a)

/-- The copy part of the pair data of `(a, b)` (the second component of `pairData`). -/
def copyPairF (a b : Fin g) : List (Bool × ℕ) :=
  ((copyList g).filter fun j => decide ((j.1.1 = a ∧ j.1.2.1 = b) ∨ (j.1.1 = b ∧ j.1.2.1 = a))).map
    fun j => if j.1.1 = a then (true, @List.idxOf (CopyIdx g) instBEqOfDecidableEq j (heldF g a))
      else (false, @List.idxOf (CopyIdx g) instBEqOfDecidableEq j (copyList g))

def nhN (b : ℕ) : ℕ := if h : b < g then (heldF g ⟨b, h⟩).length else 0
def cpN (b c : ℕ) : List (Bool × ℕ) := if h : b < g ∧ c < g then copyPairF g ⟨b, h.1⟩ ⟨c, h.2⟩ else []
def hpN (b : ℕ) : List (ℕ × ℕ) :=
  if h : b < g then (heldF g ⟨b, h⟩).map fun j => (j.1.2.1.val, j.1.2.2.val) else []
def tv (j : CopyIdx g) : ℕ × ℕ × ℕ := (j.1.1.val, j.1.2.1.val, j.1.2.2.val)

def nhTab : List (List Unit) := (List.range g).map fun b => List.replicate (nhN g b) ()
def cpTab : List (List (List (Bool × ℕ))) := (List.range g).map fun b => (List.range g).map fun c => cpN g b c
def hpTab : List (List (ℕ × ℕ)) := (List.range g).map (hpN g)
def trTab : List (ℕ × ℕ × ℕ) := (copyList g).map (tv g)

/-- The five code words. -/
def codesL : List (List Bool) := [Label.N, .l0, .l1, .l2, .l3].map labelCode.enc

end Const

/-! ## The word-level reader -/

section Word

variable (g : ℕ)

def totW (a : GIn) : ℕ := ((List.range a.1.length).map (degW a)).sum
def psW (a : GIn) (t : ℕ) : ℕ :=
  (((List.range a.1.length).filter fun s => decide (s < t)).map (degW a)).sum
/-- The blob of the vertex `v` (Lemma 6.2, identity order), in `0, …, g-1`. -/
def bW (a : GIn) (v : ℕ) : ℕ := min g (g * psW a v / totW a + 1) - 1
def maxdW (a : GIn) : ℕ := ((List.range a.1.length).map (degW a)).foldr max 0
/-- `μ = ⌊(2m + gΔ)/g⌋`. -/
def muW (a : GIn) : ℕ := (totW a + g * maxdW a) / g
def PW (a : GIn) : ℕ := 3 * muW g a + g ^ 2 + 1
def BW (a : GIn) : ℕ := 2 * muW g a + 1

def pairsW (a : GIn) : List (ℕ × ℕ) := List.range a.1.length ×ˢ List.range a.1.length
/-- The crossing pairs `(u, v)`, `u ~ v`, `β u < β v`, in lexicographic order. -/
def cplW (a : GIn) : List (ℕ × ℕ) :=
  (pairsW a).filter fun p => adjW a p.1 p.2 && decide (bW g a p.1 < bW g a p.2)
def ceW (a : GIn) (k : ℕ) : ℕ × ℕ := (cplW g a).getD k (0, 0)
/-- The crossing edges at the blob `b`. -/
def incW (a : GIn) (b : ℕ) : List ℕ :=
  (List.range (cplW g a).length).filter fun k =>
    decide (bW g a (ceW g a k).1 = b ∨ bW g a (ceW g a k).2 = b)
def onPW (a : GIn) (b c k : ℕ) : Bool :=
  decide ((bW g a (ceW g a k).1 = b ∧ bW g a (ceW g a k).2 = c) ∨
    (bW g a (ceW g a k).1 = c ∧ bW g a (ceW g a k).2 = b))
def itemsW (a : GIn) (b c : ℕ) : List ℕ :=
  ((List.range (cplW g a).length).filter (onPW g a b c)).map fun k => (incW g a b).idxOf k

/-- **The layout** read from the graph. -/
def layW (a : GIn) : Lay :=
  (((List.replicate (PW g a) (), List.replicate (BW g a) ()), (List.replicate 3 (), codesL)),
    ((List.range g).map fun b => ((incW g a b).map fun _ => (), (nhTab g).getD b []),
      (List.range g).map fun b => (List.range g).map fun c =>
        (itemsW g a b c, ((cpTab g).getD b []).getD c [])))

def codeW (w : List Bool) : ℕ := min (ofWord w) 4

def ceAt (a : GIn) (b : ℕ) (z : List Bool) (i : ℕ) : CE :=
  ((((incW g a b).getD i 0), decide (bW g a (ceW g a ((incW g a b).getD i 0)).1 = b)),
    ceW g a ((incW g a b).getD i 0),
    (bW g a (ceW g a ((incW g a b).getD i 0)).1, bW g a (ceW g a ((incW g a b).getD i 0)).2),
    codeW (blk 3 z i))

/-- The crossing data at the blob `b`, with the label codes read from the setting `z`. -/
def clW (a : GIn) (b : ℕ) (z : List Bool) : List CE :=
  (List.range (incW g a b).length).map (ceAt g a b z)
def vaW (a : GIn) (b : ℕ) : List ℕ := (List.range a.1.length).filter fun v => decide (bW g a v = b)
def vrW (a : GIn) (b : ℕ) : List ℕ :=
  (List.range a.1.length).filter fun v => decide (bW g a v = b) && decide (v ≠ 0)
def esW (a : GIn) (b : ℕ) : List (ℕ × ℕ) :=
  (pairsW a).filter fun p =>
    decide (p.1 < p.2) && adjW a p.1 p.2 && decide (bW g a p.1 = b) && decide (bW g a p.2 = b)
def ylW (a : GIn) (b : ℕ) (z : List Bool) : List ((ℕ × ℕ) × Bool) :=
  ((hpTab g).getD b []).zip (z.drop ((incW g a b).length * 3))

/-- **The reader of the table procedure.** -/
def rdW (q : GIn × WQ) : TD :=
  ((0, q.2.1), (vaW g q.1 q.2.1, vrW g q.1 q.2.1), (esW g q.1 q.2.1, clW g q.1 q.2.1 q.2.2),
    ylW g q.1 q.2.1 q.2.2)

def trAt (j : ℕ) : ℕ × ℕ × ℕ := (trTab g).getD j (0, 0, 0)

/-- **The parity procedure**: copy bit number `j` is `P_{cd}` (`(a, c, d)` its triple). -/
def parW (q : GIn × (ℕ × List Bool)) : Bool :=
  parBit (trAt g q.2.1).2.1 (trAt g q.2.1).2.2 (clW g q.1 (trAt g q.2.1).2.1 q.2.2)

end Word

/-! ## Polynomial time -/

section Poly

variable (g : ℕ) {α : Type} [Enc α]

@[fun_prop] theorem totW_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => totW (a x) := by
  have := range_polyT ha; unfold totW; fun_prop

@[fun_prop] theorem psW_polyT {a : α → GIn} {t : α → ℕ} (ha : PolyT a) (ht : PolyT t) :
    PolyT fun x => psW (a x) (t x) := by
  have := range_polyT ha; unfold psW; fun_prop

@[fun_prop] theorem bW_polyT {a : α → GIn} {v : α → ℕ} (ha : PolyT a) (hv : PolyT v) :
    PolyT fun x => bW g (a x) (v x) := by
  unfold bW
  exact PolyT.pred (PolyT.min' (PolyT.const g) (PolyT.add (PolyT.div (PolyT.mul (PolyT.const g)
    (psW_polyT ha hv)) (totW_polyT ha)) (PolyT.const 1)))

@[fun_prop] theorem maxdW_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => maxdW (a x) := by
  have := range_polyT ha
  unfold maxdW
  exact NetE.foldr_max_polyT (by fun_prop)

@[fun_prop] theorem muW_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => muW g (a x) := by
  unfold muW
  exact PolyT.div (PolyT.add (totW_polyT ha) (PolyT.mul (PolyT.const g) (maxdW_polyT ha))) (PolyT.const g)

@[fun_prop] theorem pairsW_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => pairsW (a x) := by
  have := range_polyT ha; unfold pairsW; fun_prop

@[fun_prop] theorem cplW_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => cplW g (a x) := by
  unfold cplW; fun_prop

@[fun_prop] theorem ceW_polyT {a : α → GIn} {k : α → ℕ} (ha : PolyT a) (hk : PolyT k) :
    PolyT fun x => ceW g (a x) (k x) := by
  unfold ceW; fun_prop

theorem rangeM_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => List.range (cplW g (a x)).length :=
  PolyT.range (Unary.of_length (by fun_prop))

@[fun_prop] theorem incW_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => incW g (a x) (b x) := by
  have := rangeM_polyT g ha; unfold incW; fun_prop

@[fun_prop] theorem onPW_polyT {a : α → GIn} {b c k : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c)
    (hk : PolyT k) : PolyT fun x => onPW g (a x) (b x) (c x) (k x) := by
  unfold onPW; fun_prop

@[fun_prop] theorem itemsW_polyT {a : α → GIn} {b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => itemsW g (a x) (b x) (c x) := by
  have := rangeM_polyT g ha; unfold itemsW; fun_prop

theorem muW_le (a : GIn) : muW g a ≤ a.1.length * a.1.length + a.1.length := by
  have hd : ∀ v, degW a v ≤ a.1.length := fun v => by
    unfold degW
    exact (List.length_filter_le _ _).trans (by simp)
  have h1 : totW a ≤ a.1.length * a.1.length := by
    unfold totW
    have := List.sum_le_card_nsmul ((List.range a.1.length).map (degW a)) a.1.length (by
      intro x hx
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
      exact hd v)
    simpa using this
  have h2 : maxdW a ≤ a.1.length := by
    unfold maxdW
    have hl' : ∀ x ∈ (List.range a.1.length).map (degW a), x ≤ a.1.length := by
      intro x hx; obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx; exact hd v
    generalize (List.range a.1.length).map (degW a) = l at hl'
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.foldr_cons]
      exact max_le (hl' x List.mem_cons_self) (ih fun y hy => hl' y (List.mem_cons_of_mem _ hy))
  unfold muW
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · subst h0; simp
  · calc (totW a + g * maxdW a) / g ≤ (totW a) / g + maxdW a := by
          rw [Nat.add_mul_div_left _ _ hpos]
      _ ≤ totW a + maxdW a := Nat.add_le_add_right (Nat.div_le_self _ _) _
      _ ≤ _ := Nat.add_le_add h1 h2

theorem muW_unary : Unary (muW g) :=
  Unary.of_le ((Unary.mul (Unary.of_length (w := fun a : GIn => a.1) (by fun_prop))
      (Unary.of_length (w := fun a : GIn => a.1) (by fun_prop))).add
      (Unary.of_length (w := fun a : GIn => a.1) (by fun_prop)))
    (by fun_prop) (muW_le g)

theorem PW_unary : Unary (PW g) := by
  unfold PW
  exact (((Unary.const 3).mul (muW_unary g)).add (Unary.const _)).add (Unary.const _)

theorem BW_unary : Unary (BW g) := by
  unfold BW
  exact ((Unary.const 2).mul (muW_unary g)).add (Unary.const _)

theorem layW_polyT : PolyT (layW g) := by
  have hP : PolyT fun a => List.replicate (PW g a) () := PW_unary g
  have hB : PolyT fun a => List.replicate (BW g a) () := BW_unary g
  have hr : PolyT fun _ : GIn => List.range g := PolyT.const _
  have hr2 : PolyT fun _ : GIn × ℕ => List.range g := PolyT.const _
  unfold layW; fun_prop

@[fun_prop] theorem codeW_polyT {w : α → List Bool} (hw : PolyT w) : PolyT fun x => codeW (w x) := by
  unfold codeW; fun_prop

@[fun_prop] theorem ceAt_polyT {a : α → GIn} {b : α → ℕ} {z : α → List Bool} {i : α → ℕ} (ha : PolyT a)
    (hb : PolyT b) (hz : PolyT z) (hi : PolyT i) : PolyT fun x => ceAt g (a x) (b x) (z x) (i x) := by
  unfold ceAt; fun_prop

@[fun_prop] theorem clW_polyT {a : α → GIn} {b : α → ℕ} {z : α → List Bool} (ha : PolyT a)
    (hb : PolyT b) (hz : PolyT z) : PolyT fun x => clW g (a x) (b x) (z x) := by
  have : PolyT fun x => List.range (incW g (a x) (b x)).length := PolyT.range (Unary.of_length (by fun_prop))
  unfold clW; fun_prop

@[fun_prop] theorem vaW_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vaW g (a x) (b x) := by
  have := range_polyT ha; unfold vaW; fun_prop

@[fun_prop] theorem vrW_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vrW g (a x) (b x) := by
  have := range_polyT ha; unfold vrW; fun_prop

@[fun_prop] theorem esW_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => esW g (a x) (b x) := by
  unfold esW; fun_prop

@[fun_prop] theorem ylW_polyT {a : α → GIn} {b : α → ℕ} {z : α → List Bool} (ha : PolyT a)
    (hb : PolyT b) (hz : PolyT z) : PolyT fun x => ylW g (a x) (b x) (z x) := by
  unfold ylW
  exact PolyT.zip (PolyT.getD (PolyT.const _) hb (PolyT.const _))
    (PolyT.drop (PolyT.mul (PolyT.length (incW_polyT g ha hb)) (PolyT.const 3)) hz)

@[fun_prop] theorem trAt_polyT {j : α → ℕ} (hj : PolyT j) : PolyT fun x => trAt g (j x) := by
  unfold trAt; fun_prop

theorem rdW_polyT : PolyT (rdW g) := by
  unfold rdW; fun_prop

theorem parW_polyT : PolyT (parW g) := by
  have h : PolyT fun q : GIn × (ℕ × List Bool) =>
      (((trAt g q.2.1).2.1, (trAt g q.2.1).2.2), clW g q.1 (trAt g q.2.1).2.1 q.2.2) := by fun_prop
  exact (PolyT.comp parBit_polyT h).congr fun q => rfl

end Poly

/-! ## List lemmas -/

section Lists

theorem map_val_filter_finRange {m : ℕ} (p : Fin m → Bool) (q : ℕ → Bool) (h : ∀ k : Fin m, p k = q k.val) :
    ((List.finRange m).filter p).map Fin.val = (List.range m).filter q := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  congr 1
  exact List.filter_congr fun k _ => by simp [h]

theorem sort_eq_filter {m : ℕ} (s : Finset (Fin m)) :
    s.sort (· ≤ ·) = (List.finRange m).filter fun k => decide (k ∈ s) := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (Finset.sortedLT_sort s).pairwise
    ((List.sortedLT_finRange m).pairwise.filter _) fun k => ?_
  simp [List.mem_finRange]

theorem idxOf_map_of_injective {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x : α) : ∀ l : List α, (l.map f).idxOf (f x) = l.idxOf x
  | [] => rfl
  | y :: l => by
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, idxOf_map_of_injective hf x l]
    by_cases h : y = x
    · subst h; simp
    · have : f y ≠ f x := fun e => h (hf e)
      rw [beq_false_of_ne h, beq_false_of_ne this]

theorem getD_map_range {β : Type} (f : ℕ → β) {g i : ℕ} (hi : i < g) (d : β) :
    ((List.range g).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem filter_lt_range (t : ℕ) : ∀ n : ℕ,
    ((List.range n).filter fun s => decide (s < t)) = List.range (min t n)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, filter_lt_range t n]
    by_cases h : n < t
    · rw [min_eq_right h.le, min_eq_right (by omega : n + 1 ≤ t), List.range_succ]; simp [h]
    · rw [min_eq_left (by omega : t ≤ n), min_eq_left (by omega : t ≤ n + 1)]; simp [h]

theorem sum_range_list (w : ℕ → ℕ) : ∀ t : ℕ, ∑ s ∈ Finset.range t, w s = ((List.range t).map w).sum
  | 0 => by simp
  | t + 1 => by rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append,
      sum_range_list w t]; simp

theorem product_map {α β γ δ : Type} (f : α → γ) (h : β → δ) (l₁ : List α) (l₂ : List β) :
    (l₁.map f) ×ˢ (l₂.map h) = (l₁ ×ˢ l₂).map (Prod.map f h) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, SProd.sprod, List.product, List.flatMap_cons] at ih ⊢
    rw [ih, List.map_append, List.map_map, List.map_map]
    rfl

theorem getD_map_idxOf {α β : Type} {inst : BEq α} [@LawfulBEq α inst] (f : α → β) {l : List α} {x : α}
    (hx : x ∈ l) (d : β) : (l.map f).getD (@List.idxOf α inst x l) d = f x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]
  rfl

theorem foldr_max_le {l : List ℕ} {c : ℕ} (h : ∀ x ∈ l, x ≤ c) : l.foldr max 0 ≤ c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons]
    exact max_le (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

end Lists

/-! ## Sizes: `size ≤ len` for the data of the table procedure -/

section Sizes

/-- The size of a value is at most the length of its word. -/
class SL (α : Type) [Enc α] [HasSize α] : Prop where
  le : ∀ x : α, size x ≤ len x

instance : SL ℕ := ⟨fun k => by rw [len_nat]; show k.size + 1 ≤ _; omega⟩
instance : SL Bool := ⟨fun b => by rw [len_bool]; exact le_rfl⟩
instance {α β : Type} [Enc α] [HasSize α] [Enc β] [HasSize β] [SL α] [SL β] : SL (α × β) :=
  ⟨fun p => by
    rw [len_pair]; have := SL.le p.1; have := SL.le p.2
    show size p.1 + size p.2 ≤ _; omega⟩
instance {α : Type} [Enc α] [HasSize α] [SL α] : SL (List α) :=
  ⟨fun l => by
    induction l with
    | nil => rw [len_nil]; show 0 + 1 ≤ 2; omega
    | cons a l ih =>
      rw [len_cons]
      have := SL.le a
      have e : size (a :: l) = size a + 1 + size l := by
        show ((a :: l).map fun x => size x + 1).sum + 1 = size a + 1 + ((l.map fun x => size x + 1).sum + 1)
        rw [List.map_cons, List.sum_cons]; omega
      omega⟩

theorem size_le_len_TD (d : TD) : size d ≤ len d := SL.le d

variable (g : ℕ)

/-- The polynomial bound on the word of the data read by `rdW`. -/
noncomputable def cR : ℕ := (rdW_polyT g).choose_spec.choose

theorem len_rdW (q : GIn × WQ) : len (rdW g q) ≤ cR g * (len q + 1) ^ cR g :=
  (rdW_polyT g).choose_spec.choose_spec.2 q

theorem size_rdW (q : GIn × WQ) : size (rdW g q) ≤ cR g * (7 * size q + 1) ^ cR g := by
  refine (size_le_len_TD _).trans ((len_rdW g q).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)))
  have := Carried.le q
  omega

end Sizes

/-! ## The graph side: partition, crossing order, label system -/

noncomputable section Graph

variable {g : ℕ} [NeZero g]

theorem bW_lt (a : GIn) (v : ℕ) : bW g a v < g := by
  have h0 := NeZero.pos g
  have := min_le_left g (g * psW a v / totW a + 1)
  unfold bW; omega

variable (g) in
/-- The partition `β` (Lemma 6.2 with the identity order). -/
def βF {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Fin g := ⟨bW g (aOf G) v.val, bW_lt _ _⟩

theorem mem_pairsW {a : GIn} {p : ℕ × ℕ} : p ∈ pairsW a ↔ p.1 < a.1.length ∧ p.2 < a.1.length := by
  obtain ⟨u, v⟩ := p
  simp [pairsW, List.mem_product]

theorem pairsW_nodup (a : GIn) : (pairsW a).Nodup := List.nodup_range.product List.nodup_range

theorem cplW_nodup (a : GIn) : (cplW g a).Nodup := (pairsW_nodup a).filter _

theorem mem_cplW {a : GIn} {p : ℕ × ℕ} : p ∈ cplW g a ↔
    (p.1 < a.1.length ∧ p.2 < a.1.length) ∧ adjW a p.1 p.2 = true ∧ bW g a p.1 < bW g a p.2 := by
  simp [cplW, mem_pairsW]

variable {n : ℕ} (G : SimpleGraph (Fin n))

variable (g) in
abbrev mF : ℕ := (cplW g (aOf G)).length

variable (g) in
def sF (k : Fin (mF g G)) : Fin n :=
  ⟨((cplW g (aOf G))[k.val]).1, by
    have := (mem_cplW.1 (List.getElem_mem k.isLt)).1.1; simpa using this⟩

variable (g) in
def tF (k : Fin (mF g G)) : Fin n :=
  ⟨((cplW g (aOf G))[k.val]).2, by
    have := (mem_cplW.1 (List.getElem_mem k.isLt)).1.2; simpa using this⟩

theorem ceW_eq (k : Fin (mF g G)) : ceW g (aOf G) k.val = ((sF g G k).val, (tF g G k).val) := by
  simp [ceW, sF, tF, List.getD_eq_getElem?_getD, k.isLt]

@[simp] theorem βF_val (v : Fin n) : (βF g G v).val = bW g (aOf G) v.val := rfl

variable (g) in
/-- **The crossing order**: the crossing pairs in lexicographic order. -/
def crossF : Crossing G (βF g G) (mF g G) where
  s := sF g G
  t := tF g G
  lt k := by
    have h := (mem_cplW.1 (List.getElem_mem k.isLt)).2.2
    rw [Fin.lt_def]; exact h
  adj k := by
    have h := (mem_cplW.1 (List.getElem_mem k.isLt)).2.1
    exact (adjW_aOf G _ _).1 h
  inj k l h1 h2 := by
    have e := (cplW_nodup (g := g) (aOf G)).getElem_inj_iff.1
      (Prod.ext (congrArg Fin.val h1) (congrArg Fin.val h2))
    exact Fin.ext e
  exhaust u v huv hlt := by
    have hm : (u.val, v.val) ∈ cplW g (aOf G) :=
      mem_cplW.2 ⟨by simp, (adjW_aOf G u.2 v.2).2 huv, hlt⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
    exact ⟨⟨i, hi⟩, Fin.ext (by simp [sF, he]), Fin.ext (by simp [tF, he])⟩

@[simp] theorem crossF_s (k : Fin (mF g G)) : (crossF g G).s k = sF g G k := rfl
@[simp] theorem crossF_t (k : Fin (mF g G)) : (crossF g G).t k = tF g G k := rfl

section Sys

variable [DecidableRel G.Adj] (r : Fin n)

@[simp] theorem hc_lo (k : Fin (mF g G)) : ((crossF g G).hcSystem r).lo k = βF g G (sF g G k) := rfl
@[simp] theorem hc_hi (k : Fin (mF g G)) : ((crossF g G).hcSystem r).hi k = βF g G (tF g G k) := rfl
@[simp] theorem hc_holder (j : CopyIdx g) : ((crossF g G).hcSystem r).holder j = j.1.1 := rfl
@[simp] theorem hc_source (j : CopyIdx g) : ((crossF g G).hcSystem r).source j = j.1.2.1 := rfl
@[simp] theorem hc_kord : ((crossF g G).hcSystem r).kord = List.finRange (mF g G) := rfl
@[simp] theorem hc_rord : ((crossF g G).hcSystem r).rord = copyList g := rfl

theorem incList_val (a : Fin g) :
    (((crossF g G).hcSystem r).incList a).map Fin.val = incW g (aOf G) a.val := by
  unfold LabelSystem.incList incW
  rw [hc_kord]
  refine map_val_filter_finRange _ _ fun k => ?_
  simp only [LabelSystem.Inc, hc_lo, hc_hi, ceW_eq, Fin.ext_iff, βF_val]

theorem length_incW (a : Fin g) :
    (incW g (aOf G) a.val).length = (((crossF g G).hcSystem r).incList a).length := by
  rw [← incList_val G r a, List.length_map]

theorem pairItems_val (a b : Fin g) :
    (((crossF g G).hcSystem r).pairItems a b).map Fin.val =
      (List.range (mF g G)).filter (onPW g (aOf G) a.val b.val) := by
  unfold LabelSystem.pairItems
  rw [hc_kord]
  refine map_val_filter_finRange _ _ fun k => ?_
  simp only [onPW, LabelSystem.OnPair, hc_lo, hc_hi, ceW_eq, Fin.ext_iff, βF_val]

theorem itemsW_eq (a b : Fin g) :
    itemsW g (aOf G) a.val b.val = (((crossF g G).hcSystem r).pairData a b).1 := by
  unfold itemsW LabelSystem.pairData
  rw [← pairItems_val G r a b, List.map_map, ← incList_val G r a]
  refine List.map_congr_left fun k _ => ?_
  exact idxOf_map_of_injective Fin.val_injective k _

theorem heldList_eq (a : Fin g) : ((crossF g G).hcSystem r).heldList a = heldF g a := rfl

theorem copyPair_eq (a b : Fin g) : (((crossF g G).hcSystem r).pairData a b).2 = copyPairF g a b := by
  unfold LabelSystem.pairData LabelSystem.pairCopies copyPairF
  simp only [hc_rord, hc_holder, hc_source, LabelSystem.CopyOn, heldList_eq]
  congr

theorem sort_delta (a : Fin g) :
    ((crossF g G).chords.delta a).sort (· ≤ ·) = ((crossF g G).hcSystem r).incList a := by
  rw [sort_eq_filter]
  unfold LabelSystem.incList
  refine List.filter_congr fun k _ => ?_
  simp only [Crossing.mem_delta, decide_eq_decide]
  rfl

/-! ### The layout -/

theorem layW_describes :
    ((crossF g G).hcSystem r).Describes labelCode (PW g (aOf G)) (BW g (aOf G)) (layW g (aOf G)) where
  P_eq := by simp [Lay.P, layW]
  B_eq := by simp [Lay.B, layW]
  w_eq := by simp [Lay.w, layW]
  codes_iff u := by
    simp only [Lay.codes, layW, codesL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · rintro (h | h | h | h | h) <;> exact ⟨_, h.symm⟩
    · rintro ⟨l, rfl⟩; cases l <;> simp
  na_eq a := by
    unfold Lay.na Lay.node layW
    rw [getD_map_range _ a.2]
    simp [length_incW G r a]
  nh_eq a := by
    unfold Lay.nh Lay.node layW nhTab
    rw [getD_map_range _ a.2, getD_map_range _ a.2]
    simp [nhN, a.2, heldList_eq]
  pair_eq a b _ := by
    unfold Lay.pair layW cpTab
    rw [getD_map_range _ a.2, getD_map_range _ b.2, getD_map_range _ a.2, getD_map_range _ b.2]
    refine Prod.ext (itemsW_eq G r a b) ?_
    simp [cpN, a.2, b.2, copyPair_eq]

end Sys

/-! ### Degrees and the blob degree sums -/

section Deg

variable [DecidableRel G.Adj]

theorem sum_range_degW : ((List.range n).map (degW (aOf G))).sum = ∑ v : Fin n, G.degree v := by
  rw [← sum_range_list, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun v _ => degW_aOf G v

theorem totW_aOf : totW (aOf G) = 2 * G.edgeFinset.card := by
  rw [totW, aOf_len, sum_range_degW, G.sum_degrees_eq_twice_card_edges]

theorem psW_aOf (v : Fin n) : psW (aOf G) v.val = prefixSum (degSeq G (Equiv.refl _)) v.val := by
  rw [psW, aOf_len, filter_lt_range, min_eq_left v.2.le, ← sum_range_list, prefixSum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < n := (Finset.mem_range.1 hs).trans v.2
  rw [degSeq, dif_pos hs', Equiv.refl_apply, ← degW_aOf G ⟨s, hs'⟩]

theorem bW_aOf (v : Fin n) : bW g (aOf G) v.val = balancedPartition G g (Equiv.refl _) v - 1 := by
  rw [bW, psW_aOf, totW_aOf]; rfl

theorem mu_eq (a : Fin g) :
    mu G (βF g G) a = blobDegreeSum G (balancedPartition G g (Equiv.refl _)) (a.val + 1) := by
  unfold mu blobDegreeSum
  congr 1
  ext v
  have := balancedPartition_mem G g (NeZero.pos g) (Equiv.refl _) v
  simp only [mem_blob, mem_filter, mem_univ, true_and, Fin.ext_iff, βF_val, bW_aOf]
  omega

theorem degree_le_maxdW (v : Fin n) : G.degree v ≤ maxdW (aOf G) := by
  rw [← degW_aOf G v, maxdW]
  exact NetE.le_foldr_max (List.mem_map.2 ⟨v.val, by simp, rfl⟩)

theorem maxdW_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) : maxdW (aOf G) ≤ Δ := by
  rw [maxdW]
  refine foldr_max_le fun x hx => ?_
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
  have hv' : v < n := by simpa using hv
  rw [degW_aOf G ⟨v, hv'⟩]
  exact hΔ _

theorem mu_le_muW (a : Fin g) : mu G (βF g G) a ≤ muW g (aOf G) := by
  rw [mu_eq, muW, totW_aOf, Nat.le_div_iff_mul_le (NeZero.pos g), mul_comm]
  exact blob_degree_sum_le G g (Equiv.refl _) (degree_le_maxdW G) _

theorem g_muW_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    g * muW g (aOf G) ≤ 2 * G.edgeFinset.card + g * Δ := by
  rw [muW, totW_aOf]
  refine (Nat.mul_div_le _ _).trans ?_
  have := maxdW_le G hΔ
  have := Nat.mul_le_mul_left g this
  omega

end Deg

/-! ### The data of the table procedure and of the parity procedure -/

section Read

variable [DecidableRel G.Adj] (r : Fin n)

theorem codeW_enc (l : Label) : codeW (labelCode.enc l) = l.code := by
  cases l <;> decide

theorem clW_eq (a : Fin g) {x : (Fin (mF g G) → Label) × (CopyIdx g → Bool)} :
    clW g (aOf G) a.val (((crossF g G).hcSystem r).enc labelCode a x) =
      (((crossF g G).chords.delta a).sort (· ≤ ·)).map (ceOf (crossF g G) x.1 a) := by
  rw [sort_delta G r]
  set L := ((crossF g G).hcSystem r).incList a with hL
  unfold clW
  apply List.ext_getElem
  · simp [length_incW G r a, ← hL]
  intro i h1 h2
  have hi : i < L.length := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  have e1 : (incW g (aOf G) a.val).getD i 0 = (L[i]).val := by
    rw [← incList_val G r a, ← hL]
    simp [List.getD_eq_getElem?_getD, hi]
  have e2 : blk 3 (((crossF g G).hcSystem r).enc labelCode a x) i = labelCode.enc (x.1 L[i]) := by
    unfold LabelSystem.enc
    exact blk_encL labelCode x.1 _ _ i hi
  unfold ceAt ceOf
  rw [e1, ceW_eq, e2, codeW_enc]
  simp [Fin.ext_iff]

end Read

section TD

variable {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]

/-- The internal edges of the blob `a`, as ordered pairs `u < v`. -/
def esF (a : Fin g) : List (Fin (n + 1) × Fin (n + 1)) :=
  ((List.finRange (n + 1)) ×ˢ (List.finRange (n + 1))).filter fun p =>
    decide (p.1 < p.2) && decide (G.Adj p.1 p.2) && decide (βF g G p.1 = a) && decide (βF g G p.2 = a)

theorem esF_val (a : Fin g) : (esF G a).map valP = esW g (aOf G) a.val := by
  unfold esF esW pairsW
  rw [aOf_len, ← List.map_coe_finRange_eq_range, product_map, List.filter_map]
  have e : (Prod.map Fin.val Fin.val : Fin (n + 1) × Fin (n + 1) → ℕ × ℕ) = valP := by
    funext p; rfl
  rw [e]
  congr 1
  refine List.filter_congr fun p _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  simp only [valP, adjW_aOf G p.1.2 p.2.2, Fin.lt_def, Fin.ext_iff, βF_val]

theorem esF_nodup (a : Fin g) : ((esF G a).map symP).Nodup := by
  refine List.Nodup.map_on ?_ (((List.nodup_finRange _).product (List.nodup_finRange _)).filter _)
  intro p hp q hq h
  simp only [esF, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  simp only [symP, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · have h3 : p.1 < p.2 := hp.2.1.1.1
    have h4 : q.1 < q.2 := hq.2.1.1.1
    rw [h1, h2] at h3
    exact absurd (h3.trans h4) (lt_irrefl _)

theorem mem_esF (a : Fin g) (e : Sym2 (Fin (n + 1))) :
    e ∈ (esF G a).map symP ↔ e ∈ Crossing.Eint G (βF g G) a := by
  rw [Crossing.mem_Eint, List.mem_map]
  induction e using Sym2.ind with
  | _ u v =>
    constructor
    · rintro ⟨p, hp, he⟩
      simp only [esF, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
      rw [← he]
      refine ⟨by simpa [symP] using hp.2.1.1.2, fun w hw => ?_⟩
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact hp.2.1.2
      · exact hp.2.2
    · rintro ⟨he, hb⟩
      have hadj : G.Adj u v := by simpa using he
      have hu := hb u (Sym2.mem_mk_left u v)
      have hv := hb v (Sym2.mem_mk_right u v)
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
      · exact ⟨(u, v), by simp [esF, List.mem_finRange, h, hadj, hu, hv], rfl⟩
      · exact ⟨(v, u), by simp [esF, List.mem_finRange, h, hadj.symm, hu, hv], Sym2.eq_swap⟩

theorem heldF_nodup (a : Fin g) : (heldF g a).Nodup := (copyList_nodup g).filter _

theorem mem_heldF {a : Fin g} {j : CopyIdx g} : j ∈ heldF g a ↔ j.1.1 = a := by
  simp [heldF, mem_copyList]

/-- **The reader produces the data of the node table** (`TDesc`). -/
theorem rdW_desc (a : Fin g) (x : (Fin (mF g G) → Label) × (CopyIdx g → Bool)) :
    TDesc G (crossF g G) 0 a x.1 (copyVec a x.2)
      (rdW g (aOf G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))) where
  r_eq := rfl
  a_eq := rfl
  va := by
    refine ⟨(List.finRange (n + 1)).filter fun v => decide (βF g G v = a), fun v => by
      simp [List.mem_finRange], ?_⟩
    simp only [rdW, vaW, aOf_len]
    exact (map_val_filter_finRange _ _ fun v => by simp [Fin.ext_iff]).symm
  vr_eq := by
    simp only [rdW, vrW, aOf_len]
    rw [sort_eq_filter]
    refine (map_val_filter_finRange _ _ fun v => ?_).symm
    simp only [Finset.mem_erase, mem_blob, Fin.ext_iff, βF_val, Fin.val_zero, ne_eq]
    by_cases h1 : bW g (aOf G) v.val = a.val <;> by_cases h2 : v.val = 0 <;> simp [h1, h2]
  es := ⟨esF G a, esF_nodup G a, mem_esF G a, (esF_val G a).symm⟩
  cl_eq := clW_eq G 0 a
  yl := by
    refine ⟨(heldF g a).map fun j => (j.1.2.1, j.1.2.2), ?_, ?_, ?_⟩
    · refine List.Nodup.map_on ?_ (heldF_nodup a)
      intro j hj j' hj' h
      rw [mem_heldF] at hj hj'
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (hj.trans hj'.symm) (Prod.ext h.1 h.2))
    · intro p
      simp only [List.mem_map, mem_heldF, Chords.Q, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rw [← hj]; exact j.2
      · intro h
        exact ⟨⟨(a, p.1, p.2), h⟩, rfl, rfl⟩
    · simp only [rdW, ylW, hpTab]
      rw [getD_map_range _ a.2]
      simp only [hpN, dif_pos a.2]
      have hz : (((crossF g G).hcSystem 0).enc labelCode a x).drop
          ((incW g (aOf G) a.val).length * 3) = (heldF g a).map x.2 := by
        unfold LabelSystem.enc
        rw [length_incW G 0 a, List.drop_left' (length_encL labelCode _ _), heldList_eq]
      rw [hz, List.zip_map', List.map_map]
      refine List.map_congr_left fun j hj => ?_
      have hja : j.1.1 = a := mem_heldF.1 hj
      have h : a < j.1.2.1 ∧ j.1.2.1 < j.1.2.2 := by rw [← hja]; exact j.2
      have e : (⟨(a, j.1.2.1, j.1.2.2), h⟩ : CopyIdx g) = j := Subtype.ext (Prod.ext hja.symm rfl)
      simp only [Function.comp_apply, copyVec, dif_pos h, e, Prod.mk.injEq, true_and]
      cases x.2 j <;> rfl

end TD

/-! ### The bounds of the table procedure -/

section Bounds

variable {n : ℕ} (G : SimpleGraph (Fin n))

variable (g) in
/-- The time bound of the table procedure. -/
def τH : ℕ := 2 * 8 ^ muW g (aOf G)

variable (g) in
/-- The state bound of the table procedure. -/
def SH : ℕ :=
  2 * (cR g * (7 * (size (aOf G) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cR g) + 9 * muW g (aOf G) + 9

end Bounds

/-! ### The specifications -/

section Spec

variable {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]

theorem hP_hc (a : Fin g) :
    #(univ.filter (((crossF g G).hcSystem 0).Inc a)) * 3 +
      #(univ.filter (((crossF g G).hcSystem 0).Touch a)) ≤ PW g (aOf G) := by
  rw [Crossing.hcSystem_card_inc]
  have h1 := (crossF g G).card_delta_le_mu a
  have h2 := mu_le_muW G a
  have h3 := (crossF g G).hcSystem_card_touch_le 0 a
  unfold PW
  have := Nat.mul_le_mul_right 3 (h1.trans h2)
  omega

theorem hT_hc (a : Fin g) (ℓ : Fin (mF g G) → Label) (y : CopyIdx g → Bool) :
    |((crossF g G).hcSystem 0).T a ℓ y| < 2 ^ BW g (aOf G) := by
  refine ((crossF g G).abs_hcT_lt 0 a ℓ y).trans_le (pow_le_pow_right₀ (by norm_num) ?_)
  have := mu_le_muW G a
  unfold BW; omega

theorem isNet_hc : (((crossF g G).hcSystem 0).net labelCode).Is (PW g (aOf G)) (BW g (aOf G)) :=
  ((crossF g G).hcSystem 0).net_is labelCode (by unfold PW; omega) (by unfold BW; omega) (hP_hc G)
    (hT_hc G)

theorem parSpec_hc : ((crossF g G).hcSystem 0).ParSpec labelCode (parW g) (aOf G) := by
  intro j x _
  have hj := mem_copyList j
  simp only [parW, hc_rord, trAt, trTab]
  rw [getD_map_idxOf (inst := instBEqOfDecidableEq) (tv g) hj]
  simp only [tv, hc_source]
  rw [clW_eq G 0 j.1.2.1]
  show _ = zToBool ((crossF g G).chords.P (labelPar x.1) j.1.2.1 j.1.2.2)
  rw [P_eq_parBit]
  cases parBit _ _ _ <;> rfl

theorem tSpec_hc : ((crossF g G).hcSystem 0).TSpec labelCode (tableProc (rdW g)) (aOf G) (τH g G) (SH g G) := by
  intro a x _
  rw [Crossing.hcSystem_T]
  have h := tableProc_runs G (crossF g G) (rdW g) _ 0 a x.1 (copyVec a x.2) (rdW_desc G a x)
  have hmu := mu_le_muW G a
  refine h.mono ?_ ?_
  · unfold τH
    refine Nat.mul_le_mul_left 2 ((steps_le_mu (crossF g G) a).trans (Nat.pow_le_pow_right (by norm_num) ?_))
    exact hmu
  · have h2 := (crossF g G).two_Eint_add_delta_le a
    have hz : (((crossF g G).hcSystem 0).enc labelCode a x).length ≤ PW g (aOf G) := by
      rw [LabelSystem.length_enc]; exact (isNet_hc G).len_le a
    have hq := size_rdW g (aOf G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))
    have hs : size (aOf G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x)) ≤
        size (aOf G) + (g + 1) + (2 * PW g (aOf G) + 1) := by
      show size (aOf G) + (size a.val + size (((crossF g G).hcSystem 0).enc labelCode a x)) ≤ _
      rw [LabelSystem.size_word]
      have := LabelSystem.size_fin' a
      omega
    have hq' : size (rdW g (aOf G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))) ≤
        cR g * (7 * (size (aOf G) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cR g :=
      hq.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    unfold SH
    have : 12 * (Crossing.Eint G (βF g G) a).card + 9 * ((crossF g G).chords.delta a).card ≤
        9 * muW g (aOf G) := by
      omega
    omega

theorem value_hc :
    ∑ ℓ : Fin (mF g G) → Label, ∏ a, ((crossF g G).hcSystem 0).T a ℓ
      (fun j => ((crossF g G).hcSystem 0).par j ℓ) =
      ((n + 1 : ℕ) : ℤ) * ((Hamiltonian.hamCycles G).card : ℤ) := by
  rw [← LabelSystem.value_net (C := labelCode)]
  exact (crossF g G).hcNet_value 0 labelCode

theorem card_m_le : mF g G ≤ G.edgeFinset.card := by
  have := Finset.card_le_card_of_injOn (crossF g G).edge (s := (univ : Finset (Fin (mF g G))))
    (t := G.edgeFinset) (by intro k _; exact (crossF g G).edge_mem_edgeFinset k)
    (crossF g G).edge_injective.injOn
  simpa using this

end Spec

end Graph

/-! ## The package -/

section Package

variable (g : ℕ)

/-- A label system for the graphs without vertices (never used: the package only speaks of `n ≥ 3`). -/
def baseSys {n m : ℕ} {G : SimpleGraph (Fin n)} {β : Fin n → Fin g} (X : Crossing G β m) :
    LabelSystem g (Fin m) (CopyIdx g) Label where
  kord := List.finRange m
  kord_nodup := List.nodup_finRange m
  mem_kord := List.mem_finRange
  rord := copyList g
  rord_nodup := copyList_nodup g
  mem_rord := mem_copyList
  lo := X.chords.a
  hi := X.chords.b
  lo_lt := X.chords.a_lt_b
  holder j := j.1.1
  source j := j.1.2.1
  holder_ne j := j.2.1.ne
  dflt := Label.N
  par _ _ := false
  T _ _ _ := 0
  par_local _ _ _ _ := rfl
  T_local _ _ _ _ _ _ _ := rfl

variable [NeZero g]

/-- **The label system of a graph**: Definition 5.1 for the partition `βF`, the root `0` and the
crossing order `crossF`. -/
noncomputable def XS : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), LabelSystem g (Fin (mF g G)) (CopyIdx g) Label
  | 0, G => baseSys g (crossF g G)
  | _ + 1, G => letI := Classical.decRel G.Adj; (crossF g G).hcSystem 0

end Package

section Package2

variable (g : ℕ)

theorem size_bound : ∃ A : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    SH g G + 2 * size (aOf G) + 2 * g + 4 * PW g (aOf G) + 8 ≤ A * (n + 2) ^ A := by
  set c1 := 12 + g + 2 * g ^ 2 with hc1
  set c2 := 50 + 2 * g + 4 * g ^ 2 with hc2
  refine ⟨_, fun n G => le_trans ?_ (((((Pol.const 2).mul ((Pol.const (cR g)).mul
    ((((Pol.const 7).mul ((Pol.const c1).mul (Pol.pow_n 2))).add (Pol.const 1)).pow (cR g)))).add
    ((Pol.const c2).mul (Pol.pow_n 2))) : Pol _ n _))⟩
  have hmu : muW g (aOf G) ≤ n * n + n := by have := muW_le g (aOf G); simpa using this
  have hsz : size (aOf G) = (2 * n + 1) + (2 * (n * n) + 1) := size_aOf G
  have hY : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
  have e1 : c1 * (n + 2) ^ 2 = c1 * (n * n) + 4 * (c1 * n) + 4 * c1 := by rw [hY]; ring
  have e2 : c2 * (n + 2) ^ 2 = c2 * (n * n) + 4 * (c2 * n) + 4 * c2 := by rw [hY]; ring
  have a1 : 8 * (n * n) ≤ c1 * (n * n) := Nat.mul_le_mul_right _ (by omega)
  have a2 : 2 * n ≤ c1 * n := Nat.mul_le_mul_right _ (by omega)
  have b1 : 50 * (n * n) ≤ c2 * (n * n) := Nat.mul_le_mul_right _ (by omega)
  have b2 : 13 * n ≤ c2 * n := Nat.mul_le_mul_right _ (by omega)
  have hin : size (aOf G) + (g + 1) + (2 * PW g (aOf G) + 1) ≤ c1 * (n + 2) ^ 2 := by
    unfold PW; omega
  unfold SH
  have hp : (7 * (size (aOf G) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cR g ≤
      (7 * (c1 * (n + 2) ^ 2) + 1) ^ cR g := Nat.pow_le_pow_left (by omega) _
  have hp' := Nat.mul_le_mul_left (cR g) hp
  have hrest : 9 * muW g (aOf G) + 9 + 2 * size (aOf G) + 2 * g + 4 * PW g (aOf G) + 8 ≤
      c2 * (n + 2) ^ 2 := by
    unfold PW; omega
  omega

theorem B_bound : ∃ A : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), BW g (aOf G) ≤ A * (n + 2) ^ A := by
  refine ⟨_, fun n G => le_trans ?_ (((Pol.const 3).mul (Pol.pow_n 2) : Pol _ n _))⟩
  have hmu : muW g (aOf G) ≤ n * n + n := by have := muW_le g (aOf G); simpa using this
  have hY : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
  unfold BW; rw [hY]; omega

/-- **An HC network package in label-sharing form, for every `g ≥ 1`, with `c₀ = 6`.** -/
theorem labelPackage (hg : 1 ≤ g) : Nonempty (LabelPackage g 6) := by
  have : NeZero g := ⟨by omega⟩
  obtain ⟨A, hA⟩ := size_bound g
  obtain ⟨A', hA'⟩ := B_bound g
  refine ⟨{
    Ctx := GIn
    lay := layW g
    lay_poly := layW_polyT g
    par := parW g
    par_poly := parW_polyT g
    Tp := tableProc (rdW g)
    Tp_poly := tableProc_poly (rdW_polyT g)
    prep := read1
    prep_poly := stCertRead.1
    q := A + A' + 2 * g ^ 3 + g ^ 2 + 2
    K := fun G => Fin (mF g G)
    R := fun _ => CopyIdx g
    L := fun _ => Label
    fintypeK := fun _ => inferInstance
    decEqK := fun _ => inferInstance
    fintypeR := fun _ => inferInstance
    decEqR := fun _ => inferInstance
    fintypeL := fun _ => inferInstance
    decEqL := fun _ => inferInstance
    w := fun _ => 3
    X := fun G => XS g G
    C := fun _ => labelCode
    P := fun G => PW g (aOf G)
    B := fun G => BW g (aOf G)
    τ := fun G => τH g G
    S := fun G => SH g G
    mu := fun G => muW g (aOf G)
    P_pos := fun G _ _ _ => by unfold PW; omega
    B_pos := fun G _ _ _ => by unfold BW; omega
    τ_pos := fun G _ _ _ => by unfold τH; have := Nat.one_le_pow (muW g (aOf G)) 8 (by norm_num); omega
    hP := fun {n} G inst h3 _ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact hP_hc G
    hT := fun {n} G inst h3 _ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact hT_hc G
    describes := fun {n} G inst h3 _ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show ((crossF g G).hcSystem 0).Describes labelCode (PW g (aOf G)) (BW g (aOf G))
        (layW g (read1 (code G)))
      rw [read1_code]
      exact layW_describes G 0
    parSpec := fun {n} G inst h3 _ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show ((crossF g G).hcSystem 0).ParSpec labelCode (parW g) (read1 (code G))
      rw [read1_code]
      exact parSpec_hc G
    tSpec := fun {n} G inst h3 _ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show ((crossF g G).hcSystem 0).TSpec labelCode (tableProc (rdW g)) (read1 (code G)) (τH g G) (SH g G)
      rw [read1_code]
      exact tSpec_hc G
    value := fun {n} G inst h3 _ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact value_hc G
    mu_le := fun G _ _ _ Δ hΔ => g_muW_le G hΔ
    U_le := fun {n} G inst h3 _ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      have h1 := card_m_le (g := g) G
      have h2 := Crossing.card_copyIdx_le g
      show 2 * (Fintype.card (Fin (mF g G)) * 3 + Fintype.card (CopyIdx g)) ≤ _
      rw [Fintype.card_fin]
      omega
    P_le := fun G _ _ _ => by unfold PW; omega
    B_le := fun {n} G _ _ _ => Pol.mono (B := A + A' + 2 * g ^ 3 + g ^ 2 + 2) (hA' n G) (by omega)
    τ_le := fun {n} G _ _ _ => by
      unfold τH
      have h8 : 8 ^ muW g (aOf G) ≤ 2 ^ (6 * muW g (aOf G)) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ≤ (A + A' + 2 * g ^ 3 + g ^ 2 + 2) * (n + 2) ^ (A + A' + 2 * g ^ 3 + g ^ 2 + 2) :=
        le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
      calc 2 * 8 ^ muW g (aOf G) ≤ 2 * 2 ^ (6 * muW g (aOf G)) := Nat.mul_le_mul_left 2 h8
        _ ≤ _ := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h2
    S_le := fun {n} G _ _ _ => by
      show SH g G + 2 * size (read1 (code G)) + 2 * g + 4 * PW g (aOf G) + 8 ≤ _
      rw [read1_code]
      exact Pol.mono (B := A + A' + 2 * g ^ 3 + g ^ 2 + 2) (hA n G) (by omega) }⟩

end Package2

end Pkg

/-- **The hypothesis of Theorem 1 holds**: for `c₀ = 6` there is an HC network package in
label-sharing form for every number `g ≥ 1` of nodes. -/
theorem exists_labelPackage : ∃ c₀ : ℕ, ∀ g : ℕ, 1 ≤ g → Nonempty (LabelPackage g c₀) :=
  ⟨6, fun g hg => Pkg.labelPackage g hg⟩

/-- **Theorem 1 (exact #HC in time `2^{δn}` for sparse graphs), Turing-machine level,
unconditional.** For every `δ > 0` and every `D` there are a Turing machine of Mathlib with finite
alphabets and a constant `C` such that, on the code of any graph `G` on `n` vertices with at most
`D·n` edges (`n` in unary followed by the adjacency matrix, `GraphProblems.code`), the machine halts
within `⌊C·2^{δn}⌋` steps with `#HC(G)` in binary (`Nat.bits`). -/
theorem theorem1 (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (Hamiltonian.hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ :=
  theorem1_TM_of_label exists_labelPackage δ hδ D

end EthFollowup.ExactHC
