/-
# The Horner-chain description in polynomial time (roots-plan.md §4, H4)

PolyT of the pieces of `hornerDesc` (`HornerDesc.lean`), the degree `d` a fixed constant:
`hornerProd_polyT`, `hornerChain_polyT`, **`hornerDesc_polyT`** (`b`, `ℓ`, `n` in unary; `m`, `a`, `lo`, `π`
PolyT). Block readers: `blk_unary nb : Unary (|w| / nb)`, `blk_fst_unary`, `blkVal_polyT` (the value of the
`j`-th of `nb` equal blocks, i.e. the body of SpecHorner's `rdBlk`).

Standard axioms only.
-/
import EthFollowup.ModP.ArithReaderPoly
import EthFollowup.ModP.HornerDesc

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork

variable {α : Type} [Enc α]

section Horner
variable (d : ℕ) {b ℓ : α → ℕ} (hb : Unary b) (hℓ : Unary ℓ)
include hb hℓ

theorem hornerProd_polyT {m p : α → ℕ} {a : α → List ℕ} (hm : PolyT m) (ha : PolyT a) (hp : PolyT p) :
    PolyT fun x => hornerProd (b x) (ℓ x) d (m x) (a x) (p x) := by
  have h1 := toLimbs_polyT hb hℓ (PolyT.getD ha (PolyT.const d) (PolyT.const 0))
  have h2 := toLimbs_polyT hb hℓ hm
  unfold hornerProd
  fun_prop

theorem hornerChain_polyT {a : α → List ℕ} {i : α → ℕ} (ha : PolyT a) (hi : PolyT i) :
    PolyT fun x => hornerChain (b x) (ℓ x) d (a x) (i x) := by
  have h1 := toLimbs_polyT hb hℓ (PolyT.getD ha (PolyT.sub (PolyT.const (d - 1)) hi) (PolyT.const 0))
  unfold hornerChain
  fun_prop

theorem hornerDesc_polyT {n m lo : α → ℕ} {a : α → List ℕ} {π : α → List Bool} (hn : Unary n)
    (hm : PolyT m) (ha : PolyT a) (hlo : PolyT lo) (hπ : PolyT π) :
    PolyT fun x => hornerDesc (b x) (ℓ x) (n x) d (m x) (a x) (lo x) (π x) := by
  have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hbq : Unary fun q : α × ℕ => b q.1 := Unary.comp hb hfst
  have hℓq : Unary fun q : α × ℕ => ℓ q.1 := Unary.comp hℓ hfst
  have hP : PolyT fun x => (List.range (2 * d)).map (hornerProd (b x) (ℓ x) d (m x) (a x)) :=
    PolyT.map (f := fun x p => hornerProd (b x) (ℓ x) d (m x) (a x) p)
      (hornerProd_polyT d hbq hℓq (PolyT.comp (f := m) hm hfst) (PolyT.comp (f := a) ha hfst) hs)
      (PolyT.range (Unary.const (2 * d)))
  have hC : PolyT fun x => (List.range d).map (hornerChain (b x) (ℓ x) d (a x)) :=
    PolyT.map (f := fun x i => hornerChain (b x) (ℓ x) d (a x) i)
      (hornerChain_polyT d hbq hℓq (PolyT.comp (f := a) ha hfst) hs) (PolyT.range (Unary.const d))
  have htm := toLimbs_polyT hb hℓ hm
  have htlo := toLimbs_polyT hb hℓ hlo
  have hQ : PolyT fun x => (List.range (d - 1)).map fun j =>
      (⟨d + 1 + j, .const (toLimbs (b x) (ℓ x) (m x)), .lt⟩ : CmpD) :=
    PolyT.map (f := fun x j => (⟨d + 1 + j, .const (toLimbs (b x) (ℓ x) (m x)), .lt⟩ : CmpD))
      (by have := toLimbs_polyT hbq hℓq (PolyT.comp (f := m) hm hfst); fun_prop)
      (PolyT.range (Unary.const (d - 1)))
  have hpp := prePat_polyT hn hπ
  unfold hornerDesc
  fun_prop

end Horner

/-! ## Block readers -/

theorem blk_unary (nb : ℕ) : Unary fun w : List Bool => w.length / nb :=
  Unary.of_le (Unary.of_length PolyT.id') (PolyT.div (Unary.of_length PolyT.id').poly (PolyT.const nb))
    fun _ => Nat.div_le_self _ _

theorem blk_fst_unary (nb : ℕ) : Unary fun y : List Bool × List Bool => y.1.length / nb :=
  (blk_unary nb).comp (PolyT.fst PolyT.id')

/-- The value of the `j`-th of `nb` equal blocks (the unfolded body of `rdBlk`). -/
theorem blkVal_polyT {w : α → List Bool} {nb j : α → ℕ} (hw : PolyT w) (hnb : PolyT nb) (hj : PolyT j) :
    PolyT fun x => Groundwork.ofWord (((w x).drop (j x * ((w x).length / nb x))).take ((w x).length / nb x)) := by
  fun_prop

end EthFollowup.ModP
