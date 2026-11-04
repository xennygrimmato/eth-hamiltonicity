/-
# The description reader in polynomial time (E1)

Bridge file (anth-build). Everything the package reader computes from the input numbers and the query word:
* constructors of the syntax types are PolyT (`fun_prop` lemmas `Operand.var_polyT`, …, `Desc.mk_polyT`);
* `toLimbs_polyT` (`b`, `ℓ` in unary; `N` in binary), `prePat_polyT` (`n` in unary);
* the instance descriptions of `ArithInstances`: `hDesc1_polyT`, `hDesc2_polyT`, `sqDescA_polyT`,
  `sqDescB_polyT`, `divDesc_polyT`, `circDesc_polyT`, `sigDesc_polyT`.
Hypotheses: `Unary b`, `Unary ℓ` (from `MulPackage.b_unary`/`ℓ_unary` with `n = |w|` in unary), `Unary n`
for the pattern length, `PolyT` of the numbers and of `π`.

Standard axioms only.
-/
import EthFollowup.ModP.ArithEnc
import EthFollowup.ModP.ArithInstances
import EthFollowup.Factoring.Params
import ToTuring.Poly.Basic
import ToTuring.Lib.List3
import ToTuring.Lib.Nat2
import ToTuring.Lib.List2
import ToTuring.Lib.Nat1b
import ToTuring.Lib.List1b
import ToTuring.Lib.Unary

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork

variable {α : Type} [Enc α]

/-! ## Constructors -/

section Ctor

theorem polyT_list_toE {β βE : Type} [Enc β] [Enc βE] (toE : β → βE) (h : ∀ y, Enc.toV y = Enc.toV (toE y))
    {l : α → List β} (hl : PolyT l) : PolyT fun x => (l x).map toE :=
  PolyT.of_wd hl id (fun _ => rfl) fun x => by unfold wd; rw [toV_list_map toE h]; rfl

theorem polyT_toE_of {β βE : Type} [Enc β] [Enc βE] (toE : β → βE) (h : ∀ y, Enc.toV y = Enc.toV (toE y))
    {f : α → β} (hf : PolyT f) : PolyT fun x => toE (f x) :=
  PolyT.of_wd hf id (fun _ => rfl) fun x => by unfold wd; rw [h]; rfl

@[fun_prop] theorem Operand.var_polyT {v : α → ℕ} (hv : PolyT v) : PolyT fun x => Operand.var (v x) :=
  polyT_into Operand.toE (fun _ => rfl) (PolyT.inl' hv)
@[fun_prop] theorem Operand.const_polyT {l : α → List ℕ} (hl : PolyT l) : PolyT fun x => Operand.const (l x) :=
  polyT_into Operand.toE (fun _ => rfl) (PolyT.inr' hl)
@[fun_prop] theorem Src.prod_polyT {p : α → ℕ} (hp : PolyT p) : PolyT fun x => Src.prod (p x) :=
  polyT_into Src.toE (fun _ => rfl) (PolyT.inl' hp)
@[fun_prop] theorem Src.lin_polyT {v : α → ℕ} (hv : PolyT v) : PolyT fun x => Src.lin (v x) :=
  polyT_into Src.toE (fun _ => rfl) (PolyT.inr' (PolyT.inl' hv))
@[fun_prop] theorem Src.const_polyT {l : α → List ℕ} (hl : PolyT l) : PolyT fun x => Src.const (l x) :=
  polyT_into Src.toE (fun _ => rfl) (PolyT.inr' (PolyT.inr' hl))
@[fun_prop] theorem ProdD.mk_polyT {u : α → ℕ} {w : α → Operand} (hu : PolyT u) (hw : PolyT w) :
    PolyT fun x => ProdD.mk (u x) (w x) :=
  polyT_into ProdD.toE (fun _ => rfl) (PolyT.prodMk hu (polyT_toE_of Operand.toE (fun _ => rfl) hw))
@[fun_prop] theorem Term.mk_polyT {c : α → ℕ} {s : α → Src} (hc : PolyT c) (hs : PolyT s) :
    PolyT fun x => Term.mk (c x) (s x) :=
  polyT_into Term.toE (fun _ => rfl) (PolyT.prodMk hc (polyT_toE_of Src.toE (fun _ => rfl) hs))
@[fun_prop] theorem ChainD.mk_polyT {l r : α → List Term} (hl : PolyT l) (hr : PolyT r) :
    PolyT fun x => ChainD.mk (l x) (r x) :=
  polyT_into ChainD.toE (fun _ => rfl)
    (PolyT.prodMk (polyT_list_toE Term.toE (fun _ => rfl) hl) (polyT_list_toE Term.toE (fun _ => rfl) hr))
@[fun_prop] theorem CmpD.mk_polyT {v : α → ℕ} {w : α → Operand} {r : α → CmpRel} (hv : PolyT v)
    (hw : PolyT w) (hr : PolyT r) : PolyT fun x => CmpD.mk (v x) (w x) (r x) :=
  polyT_into CmpD.toE (fun _ => rfl) (PolyT.prodMk hv (PolyT.prodMk (polyT_toE_of Operand.toE (fun _ => rfl) hw)
    (polyT_toE_of CmpRel.toE (fun _ => rfl) hr)))
@[fun_prop] theorem Desc.mk_polyT {nV : α → ℕ} {pat : α → List (List (Option Bool))} {pr : α → List ProdD}
    {ch : α → List ChainD} {cm : α → List CmpD} (h1 : PolyT nV) (h2 : PolyT pat) (h3 : PolyT pr) (h4 : PolyT ch)
    (h5 : PolyT cm) : PolyT fun x => Desc.mk (nV x) (pat x) (pr x) (ch x) (cm x) :=
  polyT_into Desc.toE (fun _ => rfl) (PolyT.prodMk h1 (PolyT.prodMk h2 (PolyT.prodMk
    (polyT_list_toE ProdD.toE (fun _ => rfl) h3) (PolyT.prodMk (polyT_list_toE ChainD.toE (fun _ => rfl) h4)
      (polyT_list_toE CmpD.toE (fun _ => rfl) h5)))))

end Ctor

/-! ## Limbs and prefix patterns -/

theorem toLimbs_polyT {b ℓ N : α → ℕ} (hb : Unary b) (hℓ : Unary ℓ) (hN : PolyT N) :
    PolyT fun x => toLimbs (b x) (ℓ x) (N x) := by
  have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hbq : Unary fun q : α × ℕ => b q.1 := Unary.comp hb hfst
  have hNq : PolyT fun q : α × ℕ => N q.1 := PolyT.comp (f := N) hN hfst
  have hbody : PolyT fun q : α × ℕ => N q.1 / 2 ^ (b q.1 * q.2) % 2 ^ b q.1 :=
    PolyT.mod (PolyT.div_pow hNq (PolyT.const 2) (PolyT.mul hbq.poly hs)) (PolyT.two_pow hbq)
  exact PolyT.map (f := fun x i => N x / 2 ^ (b x * i) % 2 ^ b x) hbody (PolyT.range hℓ)

/-- The prefix pattern with the bits read off the reversed word. -/
theorem prePat_eq (n : ℕ) (π : List Bool) : prePat n π = (List.range n).map fun j =>
    if n - π.length ≤ j then some (π.reverse.getD (j - (n - π.length)) false) else none := by
  unfold prePat
  congr 1
  funext j
  have e : ∀ i, (Factoring.Search.ofWord π).testBit i = π.reverse.getD i false := fun i => by
    have : Factoring.Search.ofWord π = Factoring.bev π := rfl
    rw [this, Factoring.bev_eq_ofWord, Factoring.testBit_ofWord]
  split_ifs <;> simp [e]

theorem prePat_polyT {n : α → ℕ} {π : α → List Bool} (hn : Unary n) (hπ : PolyT π) :
    PolyT fun x => prePat (n x) (π x) := by
  have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hnq : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn.poly hfst
  have hπq : PolyT fun q : α × ℕ => π q.1 := PolyT.comp (f := π) hπ hfst
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hbody : PolyT fun q : α × ℕ => if n q.1 - (π q.1).length ≤ q.2 then
      some ((π q.1).reverse.getD (q.2 - (n q.1 - (π q.1).length)) false) else none :=
    PolyT.ite' (PolyT.decide_le (PolyT.sub hnq (PolyT.length hπq)) hs)
      (PolyT.some' (PolyT.getD (PolyT.reverse hπq) (PolyT.sub hs (PolyT.sub hnq (PolyT.length hπq)))
        (PolyT.const false))) (PolyT.const none)
  refine (PolyT.map (f := fun x j => if n x - (π x).length ≤ j then
      some ((π x).reverse.getD (j - (n x - (π x).length)) false) else none) hbody (PolyT.range hn)).congr
    fun x => ?_
  rw [prePat_eq]

/-! ## The instance descriptions -/

section Inst
variable {b ℓ : α → ℕ} (hb : Unary b) (hℓ : Unary ℓ)
include hb hℓ

theorem hDesc1_polyT {N : α → ℕ} (hN : PolyT N) : PolyT fun x => hDesc1 (b x) (ℓ x) (N x) := by
  have ht := toLimbs_polyT hb hℓ hN
  unfold hDesc1 hChains
  fun_prop

theorem hDesc2_polyT {N : α → ℕ} (hN : PolyT N) : PolyT fun x => hDesc2 (b x) (ℓ x) (N x) := by
  have ht := toLimbs_polyT hb hℓ hN
  unfold hDesc2 hChains
  fun_prop

theorem divDesc_polyT {X : α → ℕ} (hX : PolyT X) : PolyT fun x => divDesc (b x) (ℓ x) (X x) := by
  have ht := toLimbs_polyT hb hℓ hX
  unfold divDesc
  fun_prop

theorem circDesc_polyT {X : α → ℕ} (hX : PolyT X) : PolyT fun x => circDesc (b x) (ℓ x) (X x) := by
  have ht := toLimbs_polyT hb hℓ hX
  unfold circDesc
  fun_prop

theorem sigDesc_polyT {X : α → ℕ} (hX : PolyT X) : PolyT fun x => sigDesc (b x) (ℓ x) (X x) := by
  have ht := toLimbs_polyT hb hℓ hX
  unfold sigDesc
  fun_prop

theorem sqDescA_polyT {n m a : α → ℕ} {π : α → List Bool} (hn : Unary n) (hm : PolyT m) (ha : PolyT a)
    (hπ : PolyT π) : PolyT fun x => sqDescA (b x) (ℓ x) (n x) (m x) (a x) (π x) := by
  have htm := toLimbs_polyT hb hℓ hm
  have hta := toLimbs_polyT hb hℓ ha
  have hp := prePat_polyT hn hπ
  unfold sqDescA
  fun_prop

theorem sqDescB_polyT {n p : α → ℕ} {π : α → List Bool} (hn : Unary n) (hp : PolyT p) (hπ : PolyT π) :
    PolyT fun x => sqDescB (b x) (ℓ x) (n x) (p x) (π x) := by
  have htp := toLimbs_polyT hb hℓ hp
  have hpp := prePat_polyT hn hπ
  unfold sqDescB
  fun_prop

end Inst

end EthFollowup.ModP
