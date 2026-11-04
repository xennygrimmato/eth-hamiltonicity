/-
# Encodings of ArithNet descriptions (E1): `Enc`, `HasSize`, `Carried` for `Desc` and its parts

Bridge file (anth-build). Every syntax type of `ArithDesc` is encoded through a tuple type built from
`ℕ`, `List`, `×`, `⊕`, `Option Bool` (`Operand.toE`, `ProdD.toE`, `Src.toE`, `Term.toE`, `ChainD.toE`,
`CmpRel.toE`, `CmpD.toE`, `Desc.toE`); `Enc`, `HasSize` are those of the tuple, so `len x = len x.toE`,
`size x = size x.toE` by `rfl`, and `Carried` is inherited.

* `polyT_iff_toE` (and the same for every type): `f` into the type is PolyT iff `toE ∘ f` is;
* `polyT_of_toE'`: a function out of the type is PolyT if it factors through `toE` through a PolyT map;
* `toV_list_map`: the word of a list is the word of its list of codes;
* accessors: `Desc.nV/pat/prods/chains/cmps`, `ProdD.u/w`, `Term.coeff/src`, `ChainD.lhs/rhs`, `CmpD.v/rhs/rel`
  are PolyT (`fun_prop`).

Standard axioms only.
-/
import EthFollowup.ModP.ArithDesc
import ToTuring.PolyT
import ToTuring.EncLemmas
import ToTuring.Closure.Basic
import ToTuring.Closure.Cases
import ToTuring.Lib.List1

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork

/-! ## The code tuples -/

abbrev OperandE := ℕ ⊕ List ℕ
abbrev ProdE := ℕ × OperandE
abbrev SrcE := ℕ ⊕ (ℕ ⊕ List ℕ)
abbrev TermE := ℕ × SrcE
abbrev ChainE := List TermE × List TermE
abbrev CmpE := ℕ × (OperandE × ℕ)
abbrev DescE := ℕ × (List (List (Option Bool)) × (List ProdE × (List ChainE × List CmpE)))

def Operand.toE : Operand → OperandE
  | .var v => .inl v
  | .const l => .inr l

def ProdD.toE (p : ProdD) : ProdE := (p.u, p.w.toE)

def Src.toE : Src → SrcE
  | .prod p => .inl p
  | .lin v => .inr (.inl v)
  | .const l => .inr (.inr l)

def Term.toE (t : Term) : TermE := (t.coeff, t.src.toE)

def ChainD.toE (c : ChainD) : ChainE := (c.lhs.map Term.toE, c.rhs.map Term.toE)

def CmpRel.toE : CmpRel → ℕ
  | .lt => 0 | .le => 1 | .eq => 2 | .ge => 3 | .gt => 4

def CmpD.toE (q : CmpD) : CmpE := (q.v, (q.rhs.toE, q.rel.toE))

def Desc.toE (d : Desc) : DescE :=
  (d.nV, (d.pat, (d.prods.map ProdD.toE, (d.chains.map ChainD.toE, d.cmps.map CmpD.toE))))

/-! ## Instances -/

instance : Enc Operand := ⟨fun x => Enc.toV x.toE⟩
instance : Enc ProdD := ⟨fun x => Enc.toV x.toE⟩
instance : Enc Src := ⟨fun x => Enc.toV x.toE⟩
instance : Enc Term := ⟨fun x => Enc.toV x.toE⟩
instance : Enc ChainD := ⟨fun x => Enc.toV x.toE⟩
instance : Enc CmpRel := ⟨fun x => Enc.toV x.toE⟩
instance : Enc CmpD := ⟨fun x => Enc.toV x.toE⟩
instance : Enc Desc := ⟨fun x => Enc.toV x.toE⟩

instance : HasSize Operand := ⟨fun x => size x.toE⟩
instance : HasSize ProdD := ⟨fun x => size x.toE⟩
instance : HasSize Src := ⟨fun x => size x.toE⟩
instance : HasSize Term := ⟨fun x => size x.toE⟩
instance : HasSize ChainD := ⟨fun x => size x.toE⟩
instance : HasSize CmpRel := ⟨fun x => size x.toE⟩
instance : HasSize CmpD := ⟨fun x => size x.toE⟩
instance : HasSize Desc := ⟨fun x => size x.toE⟩

instance : Carried Operand := ⟨fun x => Carried.le x.toE⟩
instance : Carried ProdD := ⟨fun x => Carried.le x.toE⟩
instance : Carried Src := ⟨fun x => Carried.le x.toE⟩
instance : Carried Term := ⟨fun x => Carried.le x.toE⟩
instance : Carried ChainD := ⟨fun x => Carried.le x.toE⟩
instance : Carried CmpRel := ⟨fun x => Carried.le x.toE⟩
instance : Carried CmpD := ⟨fun x => Carried.le x.toE⟩
instance : Carried Desc := ⟨fun x => Carried.le x.toE⟩

/-! ## Transfer of PolyT through the codes -/

/-- The word of a list is that of its list of codes. -/
theorem toV_list_map {α β : Type} [Enc α] [Enc β] (f : α → β) (hf : ∀ a, Enc.toV a = Enc.toV (f a)) :
    ∀ l : List α, Enc.toV l = Enc.toV (l.map f)
  | [] => rfl
  | a :: l => by
    show TM.V.cons (Enc.toV a) (Enc.toV l) = TM.V.cons (Enc.toV (f a)) (Enc.toV (l.map f))
    rw [hf a, toV_list_map f hf l]

theorem wd_list_map {α β : Type} [Enc α] [Enc β] (f : α → β) (hf : ∀ a, Enc.toV a = Enc.toV (f a))
    (l : List α) : wd l = wd (l.map f) := by
  unfold wd; rw [toV_list_map f hf l]

section Transfer
variable {α γ : Type} [Enc α] [Enc γ]

/-- Into a coded type: PolyT iff PolyT on the codes (generic form). -/
theorem polyT_into {β βE : Type} [Enc β] [Enc βE] (toE : β → βE) (h : ∀ y, Enc.toV y = Enc.toV (toE y))
    {f : α → β} (hf : PolyT fun x => toE (f x)) : PolyT f :=
  PolyT.of_wd hf id (fun _ => rfl) fun x => by unfold wd; rw [h]; rfl

/-- Out of a coded type: PolyT if it factors through the codes. -/
theorem polyT_outof {β βE : Type} [Enc β] [Enc βE] (toE : β → βE) (h : ∀ y, Enc.toV y = Enc.toV (toE y))
    {g : β → γ} {g' : βE → γ} (hg : PolyT g') (e : ∀ y, g y = g' (toE y)) : PolyT g :=
  PolyT.of_wd hg toE (fun y => by unfold wd; rw [h]) fun y => by rw [e]

theorem Desc.polyT_of_toE {f : α → Desc} (hf : PolyT fun x => (f x).toE) : PolyT f :=
  polyT_into Desc.toE (fun _ => rfl) hf

theorem Desc.polyT_toE {f : α → Desc} (hf : PolyT f) : PolyT fun x => (f x).toE :=
  PolyT.of_wd hf id (fun _ => rfl) fun _ => rfl

theorem Desc.polyT_toE' : PolyT Desc.toE := Desc.polyT_toE PolyT.id'

end Transfer

/-! ## Accessors -/

theorem toV_list_toE_prod (l : List ProdD) : Enc.toV l = Enc.toV (l.map ProdD.toE) :=
  toV_list_map ProdD.toE (fun _ => rfl) l
theorem toV_list_toE_chain (l : List ChainD) : Enc.toV l = Enc.toV (l.map ChainD.toE) :=
  toV_list_map ChainD.toE (fun _ => rfl) l
theorem toV_list_toE_cmp (l : List CmpD) : Enc.toV l = Enc.toV (l.map CmpD.toE) :=
  toV_list_map CmpD.toE (fun _ => rfl) l
theorem toV_list_toE_term (l : List Term) : Enc.toV l = Enc.toV (l.map Term.toE) :=
  toV_list_map Term.toE (fun _ => rfl) l

section Acc
variable {α : Type} [Enc α] {d : α → Desc} (hd : PolyT d)
include hd

@[fun_prop] theorem Desc.nV_polyT : PolyT fun x => (d x).nV :=
  (PolyT.fst (Desc.polyT_toE hd)).congr fun _ => rfl
@[fun_prop] theorem Desc.pat_polyT : PolyT fun x => (d x).pat :=
  (PolyT.fst (PolyT.snd (Desc.polyT_toE hd))).congr fun _ => rfl
@[fun_prop] theorem Desc.prods_polyT : PolyT fun x => (d x).prods :=
  PolyT.of_wd (PolyT.fst (PolyT.snd (PolyT.snd (Desc.polyT_toE hd)))) id (fun _ => rfl)
    fun x => by unfold wd; rw [toV_list_toE_prod]; rfl
@[fun_prop] theorem Desc.chains_polyT : PolyT fun x => (d x).chains :=
  PolyT.of_wd (PolyT.fst (PolyT.snd (PolyT.snd (PolyT.snd (Desc.polyT_toE hd))))) id (fun _ => rfl)
    fun x => by unfold wd; rw [toV_list_toE_chain]; rfl
@[fun_prop] theorem Desc.cmps_polyT : PolyT fun x => (d x).cmps :=
  PolyT.of_wd (PolyT.snd (PolyT.snd (PolyT.snd (PolyT.snd (Desc.polyT_toE hd))))) id (fun _ => rfl)
    fun x => by unfold wd; rw [toV_list_toE_cmp]; rfl
end Acc

section Acc2
variable {α : Type} [Enc α]

@[fun_prop] theorem ProdD.u_polyT {p : α → ProdD} (hp : PolyT p) : PolyT fun x => (p x).u :=
  PolyT.of_wd (PolyT.fst hp) id (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem ProdD.w_polyT {p : α → ProdD} (hp : PolyT p) : PolyT fun x => (p x).w :=
  PolyT.of_wd (PolyT.snd (f := fun x => (p x).toE) (PolyT.of_wd hp id (fun _ => rfl) fun _ => rfl)) id
    (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem Term.coeff_polyT {t : α → Term} (ht : PolyT t) : PolyT fun x => (t x).coeff :=
  PolyT.fst (f := fun x => (t x).toE) (PolyT.of_wd ht id (fun _ => rfl) fun _ => rfl)
@[fun_prop] theorem Term.src_polyT {t : α → Term} (ht : PolyT t) : PolyT fun x => (t x).src :=
  PolyT.of_wd (PolyT.snd (f := fun x => (t x).toE) (PolyT.of_wd ht id (fun _ => rfl) fun _ => rfl)) id
    (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem ChainD.lhs_polyT {c : α → ChainD} (hc : PolyT c) : PolyT fun x => (c x).lhs :=
  PolyT.of_wd (PolyT.fst (f := fun x => (c x).toE) (PolyT.of_wd hc id (fun _ => rfl) fun _ => rfl)) id
    (fun _ => rfl) fun x => by unfold wd; rw [toV_list_toE_term]; rfl
@[fun_prop] theorem ChainD.rhs_polyT {c : α → ChainD} (hc : PolyT c) : PolyT fun x => (c x).rhs :=
  PolyT.of_wd (PolyT.snd (f := fun x => (c x).toE) (PolyT.of_wd hc id (fun _ => rfl) fun _ => rfl)) id
    (fun _ => rfl) fun x => by unfold wd; rw [toV_list_toE_term]; rfl
@[fun_prop] theorem CmpD.v_polyT {q : α → CmpD} (hq : PolyT q) : PolyT fun x => (q x).v :=
  PolyT.fst (f := fun x => (q x).toE) (PolyT.of_wd hq id (fun _ => rfl) fun _ => rfl)
@[fun_prop] theorem CmpD.rhs_polyT {q : α → CmpD} (hq : PolyT q) : PolyT fun x => (q x).rhs :=
  PolyT.of_wd (PolyT.fst (PolyT.snd (f := fun x => (q x).toE) (PolyT.of_wd hq id (fun _ => rfl) fun _ => rfl)))
    id (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem CmpD.rel_polyT {q : α → CmpD} (hq : PolyT q) : PolyT fun x => (q x).rel :=
  PolyT.of_wd (PolyT.snd (PolyT.snd (f := fun x => (q x).toE) (PolyT.of_wd hq id (fun _ => rfl) fun _ => rfl)))
    id (fun _ => rfl) fun _ => rfl
end Acc2

end EthFollowup.ModP
