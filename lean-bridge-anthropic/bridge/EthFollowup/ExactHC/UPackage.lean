/-
# A uniform HC network package (Theorem 2), and Theorem 2 unconditionally

The readers of `Package.lean` with the number `g` of nodes read from the input (in unary) instead of
being a fixed parameter: one context type `List Unit × GIn` (`g` in unary, the graph), one layout
reader, one parity procedure, one table procedure, one `PolyT` certificate each, one absolute
constant `q`. The `g`-only tables of `Package.lean` (copy bits) are recomputed by word-level
functions of `g` (`copyW`, `heldW`, …; `nhTab_eq`, `hpTab_eq`, `cpTab_eq`, `trTab_eq`).

* `UPkg.ulabelPackage : Nonempty (ULabelPackage 6)`, `exists_ulabelPackage`;
* `theorem2`: Theorem 2 at TM level, unconditional (`theorem2_TM_of_label exists_ulabelPackage`).
-/
import EthFollowup.ExactHC.Package
import EthFollowup.ExactHC.Theorem2

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace UPkg

open Groundwork Groundwork.Prog GraphProblems Asm Finset Pkg

/-! ## The copy-bit tables as functions of `g` -/

section Tables

/-- All triples `a < c < d < g`, lexicographically. -/
def copyW (g : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range g ×ˢ (List.range g ×ˢ List.range g)).filter fun t => decide (t.1 < t.2.1 ∧ t.2.1 < t.2.2)
def heldW (g b : ℕ) : List (ℕ × ℕ × ℕ) := (copyW g).filter fun t => decide (t.1 = b)
def nhW (g : ℕ) : List (List Unit) := (List.range g).map fun b => (heldW g b).map fun _ => ()
def hpW (g : ℕ) : List (List (ℕ × ℕ)) := (List.range g).map fun b => (heldW g b).map fun t => (t.2.1, t.2.2)
def cpWN (g b c : ℕ) : List (Bool × ℕ) :=
  ((copyW g).filter fun t => decide ((t.1 = b ∧ t.2.1 = c) ∨ (t.1 = c ∧ t.2.1 = b))).map
    fun t => if t.1 = b then (true, (heldW g b).idxOf t) else (false, (copyW g).idxOf t)
def cpW (g : ℕ) : List (List (List (Bool × ℕ))) :=
  (List.range g).map fun b => (List.range g).map fun c => cpWN g b c

theorem filterMap_dite {α β : Type} (p : α → Prop) [DecidablePred p] (f : ∀ a, p a → β) (h : α → β)
    (hf : ∀ a ha, f a ha = h a) : ∀ l : List α,
    l.filterMap (fun a => if ha : p a then some (f a ha) else none) = (l.filter fun a => decide (p a)).map h
  | [] => rfl
  | a :: l => by
    by_cases ha : p a
    · rw [List.filterMap_cons, dif_pos ha, filterMap_dite p f h hf l,
        List.filter_cons_of_pos (by simpa using ha), List.map_cons, hf]
    · rw [List.filterMap_cons, dif_neg ha, filterMap_dite p f h hf l,
        List.filter_cons_of_neg (by simpa using ha)]

theorem idxOf_map_inj {α β : Type} {iα : BEq α} [@LawfulBEq α iα] {iβ : BEq β} [@LawfulBEq β iβ]
    {f : α → β} (hf : Function.Injective f) (x : α) :
    ∀ l : List α, @List.idxOf β iβ (f x) (l.map f) = @List.idxOf α iα x l
  | [] => rfl
  | y :: l => by
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, idxOf_map_inj hf x l]
    by_cases h : y = x
    · subst h; simp
    · have : f y ≠ f x := fun e => h (hf e)
      rw [beq_false_of_ne h, beq_false_of_ne this]

theorem tv_injective (g : ℕ) : Function.Injective (tv g) := by
  rintro ⟨⟨a, c, d⟩, h⟩ ⟨⟨a', c', d'⟩, h'⟩ e
  simp only [tv, Prod.mk.injEq] at e
  exact Subtype.ext (Prod.ext (Fin.ext e.1) (Prod.ext (Fin.ext e.2.1) (Fin.ext e.2.2)))

theorem copyList_map (g : ℕ) : (copyList g).map (tv g) = copyW g := by
  unfold copyList allTriples copyW
  rw [List.map_filterMap]
  have e1 : (fun j : Fin g × Fin g × Fin g => Option.map (tv g)
      (if h : j.1 < j.2.1 ∧ j.2.1 < j.2.2 then some ⟨j, h⟩ else none)) =
      fun j => if h : j.1 < j.2.1 ∧ j.2.1 < j.2.2 then some (tv g ⟨j, h⟩) else none := by
    funext j; split_ifs <;> rfl
  rw [e1, filterMap_dite (fun j : Fin g × Fin g × Fin g => j.1 < j.2.1 ∧ j.2.1 < j.2.2)
    (fun j h => tv g ⟨j, h⟩) (fun j => (j.1.val, j.2.1.val, j.2.2.val)) (fun _ _ => rfl)]
  rw [← List.map_coe_finRange_eq_range, product_map, product_map, List.filter_map]
  congr 1

theorem heldF_map (g : ℕ) (a : Fin g) : (heldF g a).map (tv g) = heldW g a.val := by
  unfold heldF heldW
  rw [← copyList_map, List.filter_map]
  congr 1
  refine List.filter_congr fun j _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Function.comp_apply]
  simp [tv, Fin.ext_iff]

theorem nhTab_eq (g : ℕ) : nhTab g = nhW g := by
  unfold nhTab nhW
  refine List.map_congr_left fun b hb => ?_
  have hb' := List.mem_range.1 hb
  rw [List.map_const', nhN, dif_pos hb', ← heldF_map g ⟨b, hb'⟩, List.length_map]

theorem hpTab_eq (g : ℕ) : hpTab g = hpW g := by
  unfold hpTab hpW
  refine List.map_congr_left fun b hb => ?_
  have hb' := List.mem_range.1 hb
  rw [hpN, dif_pos hb', ← heldF_map g ⟨b, hb'⟩, List.map_map]
  rfl

theorem trTab_eq (g : ℕ) : trTab g = copyW g := copyList_map g

theorem cpTab_eq (g : ℕ) : cpTab g = cpW g := by
  unfold cpTab cpW
  refine List.map_congr_left fun b hb => List.map_congr_left fun c hc => ?_
  have hb' := List.mem_range.1 hb
  have hc' := List.mem_range.1 hc
  rw [cpN, dif_pos ⟨hb', hc'⟩, copyPairF, cpWN, ← copyList_map, List.filter_map, List.map_map]
  have e : ((copyList g).filter ((fun t : ℕ × ℕ × ℕ =>
      decide ((t.1 = b ∧ t.2.1 = c) ∨ (t.1 = c ∧ t.2.1 = b))) ∘ tv g)) =
      (copyList g).filter fun j => decide ((j.1.1 = (⟨b, hb'⟩ : Fin g) ∧ j.1.2.1 = (⟨c, hc'⟩ : Fin g)) ∨
        (j.1.1 = (⟨c, hc'⟩ : Fin g) ∧ j.1.2.1 = (⟨b, hb'⟩ : Fin g))) := by
    refine List.filter_congr fun j _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Function.comp_apply]
    simp [tv, Fin.ext_iff]
  rw [e]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  by_cases h : j.1.1 = (⟨b, hb'⟩ : Fin g)
  · have h' : (tv g j).1 = b := by simp [tv, h]
    rw [if_pos h, if_pos h', ← heldF_map g ⟨b, hb'⟩,
      idxOf_map_inj (iα := instBEqOfDecidableEq) (tv_injective g)]
  · have h' : ¬ (tv g j).1 = b := by simp only [tv]; intro e; exact h (Fin.ext e)
    rw [if_neg h, if_neg h', idxOf_map_inj (iα := instBEqOfDecidableEq) (tv_injective g)]

end Tables

/-! ## Polynomial time, with `g` read from the input -/

section PolyU

variable {α : Type} [Enc α] {u : α → List Unit}

theorem rangeU (hu : PolyT u) : PolyT fun x => List.range (u x).length :=
  PolyT.range (Unary.of_length hu)

theorem copyW_polyT (hu : PolyT u) : PolyT fun x => copyW (u x).length := by
  have := rangeU hu; unfold copyW; fun_prop

theorem heldW_polyT (hu : PolyT u) {b : α → ℕ} (hb : PolyT b) :
    PolyT fun x => heldW (u x).length (b x) := by
  have := copyW_polyT hu; unfold heldW; fun_prop

theorem nhTab_polyT (hu : PolyT u) : PolyT fun x => nhTab (u x).length := by
  have := rangeU hu
  have h1 := heldW_polyT (u := fun p : α × ℕ => u p.1) (by fun_prop) (b := fun p => p.2) (by fun_prop)
  have h : PolyT fun x => nhW (u x).length := by unfold nhW; fun_prop
  exact h.congr fun _ => (nhTab_eq _).symm

theorem hpTab_polyT (hu : PolyT u) : PolyT fun x => hpTab (u x).length := by
  have := rangeU hu
  have h1 := heldW_polyT (u := fun p : α × ℕ => u p.1) (by fun_prop) (b := fun p => p.2) (by fun_prop)
  have h : PolyT fun x => hpW (u x).length := by unfold hpW; fun_prop
  exact h.congr fun _ => (hpTab_eq _).symm

theorem trTab_polyT (hu : PolyT u) : PolyT fun x => trTab (u x).length :=
  (copyW_polyT hu).congr fun _ => (trTab_eq _).symm

theorem cpWN_polyT (hu : PolyT u) {b c : α → ℕ} (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => cpWN (u x).length (b x) (c x) := by
  have h1 := copyW_polyT hu
  have h1' := copyW_polyT (u := fun p : α × (ℕ × ℕ × ℕ) => u p.1) (by fun_prop)
  have h2' := heldW_polyT (u := fun p : α × (ℕ × ℕ × ℕ) => u p.1) (by fun_prop) (b := fun p => b p.1)
    (by fun_prop)
  unfold cpWN; fun_prop

theorem cpTab_polyT (hu : PolyT u) : PolyT fun x => cpTab (u x).length := by
  have h0 := rangeU hu
  have h0' := rangeU (u := fun p : α × ℕ => u p.1) (by fun_prop)
  have h1 := cpWN_polyT (u := fun p : (α × ℕ) × ℕ => u p.1.1) (by fun_prop) (b := fun p => p.1.2)
    (c := fun p => p.2) (by fun_prop) (by fun_prop)
  have h : PolyT fun x => cpW (u x).length := by unfold cpW; fun_prop
  exact h.congr fun _ => (cpTab_eq _).symm

variable (hu : PolyT u)
include hu

theorem bW_polyU {a : α → GIn} {v : α → ℕ} (ha : PolyT a) (hv : PolyT v) :
    PolyT fun x => bW (u x).length (a x) (v x) := by
  unfold bW
  exact PolyT.pred (PolyT.min' (PolyT.length hu) (PolyT.add (PolyT.div (PolyT.mul (PolyT.length hu)
    (psW_polyT ha hv)) (totW_polyT ha)) (PolyT.const 1)))

theorem muW_polyU {a : α → GIn} (ha : PolyT a) : PolyT fun x => muW (u x).length (a x) := by
  unfold muW
  exact PolyT.div (PolyT.add (totW_polyT ha) (PolyT.mul (PolyT.length hu) (maxdW_polyT ha)))
    (PolyT.length hu)

theorem cplW_polyU {a : α → GIn} (ha : PolyT a) : PolyT fun x => cplW (u x).length (a x) := by
  have h := bW_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.1) (by fun_prop) (by fun_prop)
  have h' := bW_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.2) (by fun_prop) (by fun_prop)
  unfold cplW; fun_prop

theorem ceW_polyU {a : α → GIn} {k : α → ℕ} (ha : PolyT a) (hk : PolyT k) :
    PolyT fun x => ceW (u x).length (a x) (k x) := by
  have := cplW_polyU hu ha
  unfold ceW; fun_prop

theorem incW_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => incW (u x).length (a x) (b x) := by
  have h0 : PolyT fun x => List.range (cplW (u x).length (a x)).length :=
    PolyT.range (Unary.of_length (cplW_polyU hu ha))
  have hc := ceW_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (k := fun p => p.2) (by fun_prop) (by fun_prop)
  have h1 := bW_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => (ceW (u p.1).length (a p.1) p.2).1) (by fun_prop) (by fun_prop)
  have h2 := bW_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => (ceW (u p.1).length (a p.1) p.2).2) (by fun_prop) (by fun_prop)
  unfold incW; fun_prop

theorem onPW_polyU {a : α → GIn} {b c k : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c)
    (hk : PolyT k) : PolyT fun x => onPW (u x).length (a x) (b x) (c x) (k x) := by
  have hc' := ceW_polyU hu ha hk
  have h1 := bW_polyU hu ha (v := fun x => (ceW (u x).length (a x) (k x)).1) (by fun_prop)
  have h2 := bW_polyU hu ha (v := fun x => (ceW (u x).length (a x) (k x)).2) (by fun_prop)
  unfold onPW; fun_prop

theorem itemsW_polyU {a : α → GIn} {b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => itemsW (u x).length (a x) (b x) (c x) := by
  have h0 : PolyT fun x => List.range (cplW (u x).length (a x)).length :=
    PolyT.range (Unary.of_length (cplW_polyU hu ha))
  have h1 := onPW_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (b := fun p => b p.1) (c := fun p => c p.1) (k := fun p => p.2) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)
  have h2 := incW_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (b := fun p => b p.1) (by fun_prop) (by fun_prop)
  unfold itemsW; fun_prop

theorem ceAt_polyU {a : α → GIn} {b : α → ℕ} {z : α → List Bool} {i : α → ℕ} (ha : PolyT a)
    (hb : PolyT b) (hz : PolyT z) (hi : PolyT i) :
    PolyT fun x => ceAt (u x).length (a x) (b x) (z x) (i x) := by
  have h0 := incW_polyU hu ha hb
  have hk : PolyT fun x => (incW (u x).length (a x) (b x)).getD (i x) 0 := by fun_prop
  have hc := ceW_polyU hu ha hk
  have h1 := bW_polyU hu ha (v := fun x => (ceW (u x).length (a x) ((incW (u x).length (a x) (b x)).getD (i x) 0)).1)
    (by fun_prop)
  have h2 := bW_polyU hu ha (v := fun x => (ceW (u x).length (a x) ((incW (u x).length (a x) (b x)).getD (i x) 0)).2)
    (by fun_prop)
  unfold ceAt; fun_prop

theorem clW_polyU {a : α → GIn} {b : α → ℕ} {z : α → List Bool} (ha : PolyT a) (hb : PolyT b)
    (hz : PolyT z) : PolyT fun x => clW (u x).length (a x) (b x) (z x) := by
  have h0 : PolyT fun x => List.range (incW (u x).length (a x) (b x)).length :=
    PolyT.range (Unary.of_length (incW_polyU hu ha hb))
  have h1 := ceAt_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (b := fun p => b p.1) (z := fun p => z p.1) (i := fun p => p.2) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)
  unfold clW; fun_prop

theorem vaW_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vaW (u x).length (a x) (b x) := by
  have := range_polyT ha
  have h1 := bW_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2) (by fun_prop) (by fun_prop)
  unfold vaW; fun_prop

theorem vrW_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vrW (u x).length (a x) (b x) := by
  have := range_polyT ha
  have h1 := bW_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2) (by fun_prop) (by fun_prop)
  unfold vrW; fun_prop

theorem esW_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => esW (u x).length (a x) (b x) := by
  have := pairsW_polyT ha
  have h1 := bW_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.1) (by fun_prop) (by fun_prop)
  have h2 := bW_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.2) (by fun_prop) (by fun_prop)
  unfold esW; fun_prop

theorem ylW_polyU {a : α → GIn} {b : α → ℕ} {z : α → List Bool} (ha : PolyT a) (hb : PolyT b)
    (hz : PolyT z) : PolyT fun x => ylW (u x).length (a x) (b x) (z x) := by
  unfold ylW
  exact PolyT.zip (PolyT.getD (hpTab_polyT hu) hb (PolyT.const _))
    (PolyT.drop (PolyT.mul (PolyT.length (incW_polyU hu ha hb)) (PolyT.const 3)) hz)

theorem trAt_polyU {j : α → ℕ} (hj : PolyT j) : PolyT fun x => trAt (u x).length (j x) := by
  unfold trAt
  exact PolyT.getD (trTab_polyT hu) hj (PolyT.const _)

end PolyU

/-! ## The uniform readers -/

section Readers

/-- The context: `g` in unary and the graph. -/
abbrev UCtx : Type := List Unit × GIn

def prepU (p : List Unit × List Bool) : UCtx := (p.1, read1 p.2)
def layU (c : UCtx) : Lay := layW c.1.length c.2
def rdU (q : UCtx × WQ) : TD := rdW q.1.1.length (q.1.2, q.2)
def parU (q : UCtx × (ℕ × List Bool)) : Bool := parW q.1.1.length (q.1.2, q.2)

theorem prepU_polyT : PolyT prepU := by
  have := stCertRead.1
  unfold prepU; fun_prop

theorem muW_unaryU : Unary fun c : UCtx => muW c.1.length c.2 :=
  Unary.of_le ((Unary.mul (Unary.of_length (w := fun c : UCtx => c.2.1) (by fun_prop))
      (Unary.of_length (w := fun c : UCtx => c.2.1) (by fun_prop))).add
      (Unary.of_length (w := fun c : UCtx => c.2.1) (by fun_prop)))
    (muW_polyU (u := fun c : UCtx => c.1) (by fun_prop) (by fun_prop)) fun c => muW_le _ _

theorem gsq_unary : Unary fun c : UCtx => c.1.length ^ 2 := by
  have h := Unary.of_length (w := fun c : UCtx => c.1) (by fun_prop)
  exact (Unary.mul h h).congr fun c => by simp only [sq]

theorem layU_polyT : PolyT layU := by
  have hP : PolyT fun c : UCtx => List.replicate (PW c.1.length c.2) () := by
    unfold PW
    exact ((((Unary.const 3).mul muW_unaryU).add gsq_unary).add (Unary.const _))
  have hB : PolyT fun c : UCtx => List.replicate (BW c.1.length c.2) () := by
    unfold BW
    exact ((Unary.const 2).mul muW_unaryU).add (Unary.const _)
  have hr := rangeU (u := fun c : UCtx => c.1) (by fun_prop)
  have hr2 := rangeU (u := fun p : UCtx × ℕ => p.1.1) (by fun_prop)
  have h1 := incW_polyU (u := fun p : UCtx × ℕ => p.1.1) (by fun_prop) (a := fun p => p.1.2)
    (b := fun p => p.2) (by fun_prop) (by fun_prop)
  have h2 := nhTab_polyT (u := fun p : UCtx × ℕ => p.1.1) (by fun_prop)
  have h3 := itemsW_polyU (u := fun p : (UCtx × ℕ) × ℕ => p.1.1.1) (by fun_prop)
    (a := fun p => p.1.1.2) (b := fun p => p.1.2) (c := fun p => p.2) (by fun_prop) (by fun_prop)
    (by fun_prop)
  have h4 := cpTab_polyT (u := fun p : (UCtx × ℕ) × ℕ => p.1.1.1) (by fun_prop)
  unfold layU layW; fun_prop

theorem rdU_polyT : PolyT rdU := by
  have hu : PolyT fun q : UCtx × WQ => q.1.1 := by fun_prop
  have ha : PolyT fun q : UCtx × WQ => q.1.2 := by fun_prop
  have hb : PolyT fun q : UCtx × WQ => q.2.1 := by fun_prop
  have hz : PolyT fun q : UCtx × WQ => q.2.2 := by fun_prop
  have h1 := vaW_polyU hu ha hb
  have h2 := vrW_polyU hu ha hb
  have h3 := esW_polyU hu ha hb
  have h4 := clW_polyU hu ha hb hz
  have h5 := ylW_polyU hu ha hb hz
  unfold rdU rdW; fun_prop

theorem parU_polyT : PolyT parU := by
  have hu : PolyT fun q : UCtx × (ℕ × List Bool) => q.1.1 := by fun_prop
  have hj := trAt_polyU hu (j := fun q => q.2.1) (by fun_prop)
  have hc := clW_polyU hu (a := fun q => q.1.2) (b := fun q => (trAt q.1.1.length q.2.1).2.1)
    (z := fun q => q.2.2) (by fun_prop) (by fun_prop) (by fun_prop)
  have h : PolyT fun q : UCtx × (ℕ × List Bool) =>
      (((trAt q.1.1.length q.2.1).2.1, (trAt q.1.1.length q.2.1).2.2),
        clW q.1.1.length q.1.2 (trAt q.1.1.length q.2.1).2.1 q.2.2) := by fun_prop
  exact (PolyT.comp parBit_polyT h).congr fun q => rfl

end Readers

/-! ## The specifications in the uniform context -/

section USpec

/-- The polynomial bound on the word of the data read by `rdU`. -/
noncomputable def cRU : ℕ := rdU_polyT.choose_spec.choose

theorem size_rdU (q : UCtx × WQ) : size (rdU q) ≤ cRU * (7 * size q + 1) ^ cRU := by
  refine (size_le_len_TD _).trans ((rdU_polyT.choose_spec.choose_spec.2 q).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)))
  have := Carried.le q
  omega

/-- The context of the graph `G` for `g` nodes. -/
noncomputable def cG (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : UCtx := (Printed.unary g, aOf G)

theorem prepU_code (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    prepU (Printed.unary g, code G) = cG g G := by
  rw [prepU, read1_code]; rfl

@[simp] theorem cG_len (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : (cG g G).1.length = g := by
  simp [cG, Printed.unary]

theorem size_cG (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    size (cG g G) = (2 * g + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) := by
  show size (Printed.unary g) + size (aOf G) = _
  rw [size_units, size_aOf]; simp [Printed.unary]

/-- The state bound of the table procedure, uniform in `g`. -/
noncomputable def SHU (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  2 * (cRU * (7 * (size (cG g G) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cRU) +
    9 * muW g (aOf G) + 9

variable {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]

theorem tSpecU : ((crossF g G).hcSystem 0).TSpec labelCode (tableProc rdU) (cG g G) (τH g G)
    (SHU g G) := by
  intro a x _
  rw [Crossing.hcSystem_T]
  have e : rdU (cG g G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x)) =
      rdW g (aOf G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x)) := by
    simp only [rdU, cG_len]; rfl
  have hD := rdW_desc G a x
  rw [← e] at hD
  have h := tableProc_runs G (crossF g G) rdU _ 0 a x.1 (copyVec a x.2) hD
  have hmu := mu_le_muW G a
  refine h.mono ?_ ?_
  · unfold τH
    refine Nat.mul_le_mul_left 2 ((steps_le_mu (crossF g G) a).trans (Nat.pow_le_pow_right (by norm_num) ?_))
    exact hmu
  · have h2 := (crossF g G).two_Eint_add_delta_le a
    have hz : (((crossF g G).hcSystem 0).enc labelCode a x).length ≤ PW g (aOf G) := by
      rw [LabelSystem.length_enc]; exact (isNet_hc G).len_le a
    have hq := size_rdU (cG g G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))
    have hs : size (cG g G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x)) ≤
        size (cG g G) + (g + 1) + (2 * PW g (aOf G) + 1) := by
      show size (cG g G) + (size a.val + size (((crossF g G).hcSystem 0).enc labelCode a x)) ≤ _
      rw [LabelSystem.size_word]
      have := LabelSystem.size_fin' a
      omega
    have hq' : size (rdU (cG g G, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))) ≤
        cRU * (7 * (size (cG g G) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cRU :=
      hq.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    unfold SHU
    have : 12 * (Crossing.Eint G (βF g G) a).card + 9 * ((crossF g G).chords.delta a).card ≤
        9 * muW g (aOf G) := by
      omega
    omega

theorem parSpecU : ((crossF g G).hcSystem 0).ParSpec labelCode parU (cG g G) := by
  have e : ∀ w, parU (cG g G, w) = parW g (aOf G, w) := fun w => by simp only [parU, cG_len]; rfl
  intro j x hx
  rw [e]
  exact parSpec_hc G j x hx

theorem describesU : ((crossF g G).hcSystem 0).Describes labelCode (PW g (aOf G)) (BW g (aOf G))
    (layU (cG g G)) := by
  have e : layU (cG g G) = layW g (aOf G) := by simp only [layU, cG_len]; rfl
  rw [e]; exact layW_describes G 0

end USpec

/-! ## Uniform bounds -/

section UBounds

theorem size_boundU : ∃ A : ℕ, ∀ (g n : ℕ) (G : SimpleGraph (Fin n)),
    SHU g G + 2 * size (cG g G) + 2 * g + 4 * PW g (aOf G) + 8 ≤ A * (n + g + 2) ^ A := by
  refine ⟨_, fun g n G => le_trans ?_ (((((Pol.const 2).mul ((Pol.const cRU).mul
    ((((Pol.const 7).mul ((Pol.const 11).mul (Pol.pow_n 2))).add (Pol.const 1)).pow cRU))).add
    ((Pol.const 60).mul (Pol.pow_n 2))) : Pol _ (n + g) _))⟩
  have hmu : muW g (aOf G) ≤ n * n + n := by have := muW_le g (aOf G); simpa using this
  have hsz := size_cG g G
  set M := n + g with hM
  have hY : (M + 2) ^ 2 = M * M + 4 * M + 4 := by ring
  have hnn : n * n ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
  have hgg : g ^ 2 ≤ M * M := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hin : size (cG g G) + (g + 1) + (2 * PW g (aOf G) + 1) ≤ 11 * (M + 2) ^ 2 := by
    rw [hY]; unfold PW; omega
  unfold SHU
  have hp : (7 * (size (cG g G) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cRU ≤
      (7 * (11 * (M + 2) ^ 2) + 1) ^ cRU := Nat.pow_le_pow_left (by omega) _
  have hp' := Nat.mul_le_mul_left cRU hp
  have hrest : 9 * muW g (aOf G) + 9 + 2 * size (cG g G) + 2 * g + 4 * PW g (aOf G) + 8 ≤
      60 * (M + 2) ^ 2 := by
    rw [hY]; unfold PW; omega
  omega

theorem B_boundU : ∃ A : ℕ, ∀ (g n : ℕ) (G : SimpleGraph (Fin n)),
    BW g (aOf G) ≤ A * (n + g + 2) ^ A := by
  refine ⟨_, fun g n G => le_trans ?_ (((Pol.const 3).mul (Pol.pow_n 2) : Pol _ (n + g) _))⟩
  have hmu : muW g (aOf G) ≤ n * n + n := by have := muW_le g (aOf G); simpa using this
  have hY : (n + g + 2) ^ 2 = (n + g) * (n + g) + 4 * (n + g) + 4 := by ring
  have hnn : n * n ≤ (n + g) * (n + g) := Nat.mul_le_mul (by omega) (by omega)
  unfold BW; rw [hY]; omega

end UBounds

/-! ## The uniform package -/

section UPackage

theorem mF_zero {n : ℕ} (G : SimpleGraph (Fin n)) : mF 0 G = 0 := by
  simp [mF, cplW, bW]

/-- A label system for `g = 0` (never used). -/
noncomputable def zeroSys {n : ℕ} (G : SimpleGraph (Fin n)) : LabelSystem 0 (Fin (mF 0 G)) (CopyIdx 0) Label where
  kord := List.finRange _
  kord_nodup := List.nodup_finRange _
  mem_kord := List.mem_finRange
  rord := copyList 0
  rord_nodup := copyList_nodup 0
  mem_rord := mem_copyList
  lo k := absurd k.2 (by have := mF_zero G; omega)
  hi k := absurd k.2 (by have := mF_zero G; omega)
  lo_lt k := absurd k.2 (by have := mF_zero G; omega)
  holder j := j.1.1
  source j := j.1.2.1
  holder_ne j := j.2.1.ne
  dflt := Label.N
  par _ _ := false
  T _ _ _ := 0
  par_local _ _ _ _ := rfl
  T_local _ _ _ _ _ _ _ := rfl

/-- **The label system** for `g` nodes. -/
noncomputable def XU : (g : ℕ) → ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
    LabelSystem g (Fin (mF g G)) (CopyIdx g) Label
  | 0, _, G => zeroSys G
  | g + 1, _, G => XS (g + 1) G

/-- **The uniform HC network package in label-sharing form, with `c₀ = 6`.** -/
theorem ulabelPackage : Nonempty (ULabelPackage 6) := by
  obtain ⟨A, hA⟩ := size_boundU
  obtain ⟨A', hA'⟩ := B_boundU
  refine ⟨{
    Ctx := UCtx
    lay := layU
    lay_poly := layU_polyT
    par := parU
    par_poly := parU_polyT
    Tp := tableProc rdU
    Tp_poly := tableProc_poly rdU_polyT
    prep := prepU
    prep_poly := prepU_polyT
    q := A + A' + 2
    K := fun g _ G => Fin (mF g G)
    R := fun g _ _ => CopyIdx g
    L := fun _ _ _ => Label
    fintypeK := fun _ _ _ => inferInstance
    decEqK := fun _ _ _ => inferInstance
    fintypeR := fun _ _ _ => inferInstance
    decEqR := fun _ _ _ => inferInstance
    fintypeL := fun _ _ _ => inferInstance
    decEqL := fun _ _ _ => inferInstance
    w := fun _ _ _ => 3
    X := fun g _ G => XU g G
    C := fun _ _ _ => labelCode
    P := fun g _ G => PW g (aOf G)
    B := fun g _ G => BW g (aOf G)
    τ := fun g _ G => τH g G
    S := fun g _ G => SHU g G
    mu := fun g _ G => muW g (aOf G)
    P_pos := fun g _ G _ _ _ _ => by unfold PW; omega
    B_pos := fun g _ G _ _ _ _ => by unfold BW; omega
    τ_pos := fun g _ G _ _ _ _ => by
      unfold τH; have := Nat.one_le_pow (muW g (aOf G)) 8 (by norm_num); omega
    hP := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact hP_hc (g := g + 1) G
    hT := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact hT_hc (g := g + 1) G
    describes := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show ((crossF (g + 1) G).hcSystem 0).Describes labelCode (PW (g + 1) (aOf G)) (BW (g + 1) (aOf G))
        (layU (prepU (Printed.unary (g + 1), code G)))
      rw [prepU_code]
      exact describesU G
    parSpec := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show ((crossF (g + 1) G).hcSystem 0).ParSpec labelCode parU (prepU (Printed.unary (g + 1), code G))
      rw [prepU_code]
      exact parSpecU G
    tSpec := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show ((crossF (g + 1) G).hcSystem 0).TSpec labelCode (tableProc rdU)
        (prepU (Printed.unary (g + 1), code G)) (τH (g + 1) G) (SHU (g + 1) G)
      rw [prepU_code]
      exact tSpecU G
    value := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact value_hc (g := g + 1) G
    mu_le := fun g {n} G inst hg _ _ Δ hΔ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      exact g_muW_le G hΔ
    U_le := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      have h1 := card_m_le (g := g + 1) G
      have h2 := Crossing.card_copyIdx_le (g + 1)
      have h3 : 2 * (g + 1) ^ 3 ≤ (A + A' + 2) * (g + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
      show 2 * (Fintype.card (Fin (mF (g + 1) G)) * 3 + Fintype.card (CopyIdx (g + 1))) ≤ _
      rw [Fintype.card_fin]
      omega
    P_le := fun g _ G _ hg _ _ => by
      have h1 : 1 ≤ g ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h2 : 2 * g ^ 2 ≤ (A + A' + 2) * g ^ 2 := Nat.mul_le_mul_right _ (by omega)
      unfold PW; omega
    B_le := fun g {n} G _ _ _ _ => Pol.mono (B := A + A' + 2) (hA' g n G) (by omega)
    τ_le := fun g {n} G _ _ _ _ => by
      unfold τH
      have h8 : 8 ^ muW g (aOf G) ≤ 2 ^ (6 * muW g (aOf G)) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ≤ (A + A' + 2) * (n + g + 2) ^ (A + A' + 2) :=
        le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
      calc 2 * 8 ^ muW g (aOf G) ≤ 2 * 2 ^ (6 * muW g (aOf G)) := Nat.mul_le_mul_left 2 h8
        _ ≤ _ := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h2
    S_le := fun g {n} G _ _ _ _ => by
      show SHU g G + 2 * size (prepU (Printed.unary g, code G)) + 2 * g + 4 * PW g (aOf G) + 8 ≤ _
      rw [prepU_code]
      exact Pol.mono (B := A + A' + 2) (hA g n G) (by omega) }⟩

end UPackage

end UPkg

/-- **The hypothesis of Theorem 2 holds**: a uniform HC network package with `c₀ = 6`. -/
theorem exists_ulabelPackage : ∃ c₀ : ℕ, Nonempty (ULabelPackage c₀) := ⟨6, UPkg.ulabelPackage⟩

/-- **Theorem 2 (sharp rate), Turing-machine level, unconditional.** One Turing machine of Mathlib
with finite alphabets and one constant `C` such that, on the code of every graph `G` with `n`
vertices and `m` edges, the machine halts within `⌊C·2^{C(m+n)/√(log₂(n+2))}⌋` steps with `#HC(G)`
in binary (`Nat.bits`). -/
theorem theorem2 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (Hamiltonian.hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ :=
  theorem2_TM_of_label exists_ulabelPackage

end EthFollowup.ExactHC
