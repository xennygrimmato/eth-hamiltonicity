/-
# The SLP and representation-number descriptions in polynomial time (repnum-plan.md §4, B2)

PolyT of the pieces of `slpDesc` (SlpDesc) and `repDesc` (RepDesc): `slpChain_polyT`, `slpDesc_polyT`,
`initStep_polyT`, `sumStep_polyT`, `sumProg_polyT`, `repProg_polyT`, `repFin_polyT`, **`repDesc_polyT`**
(`b`, `ℓ` in unary; the monomial lists, `B` and `n` PolyT; `k` a constant).

Standard axioms only.
-/
import EthFollowup.ModP.ArithReaderPoly
import EthFollowup.ModP.RepDesc

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork

variable {α : Type} [Enc α]

/-! ## SLP descriptions -/

theorem slpChain_polyT (k : ℕ) {P : α → List Step} {t : α → ℕ} (hP : PolyT P) (ht : PolyT t) :
    PolyT fun x => slpChain k (P x) (t x) := by
  have hs : PolyT fun x => (P x).getD (t x) default := PolyT.getD hP ht (PolyT.const default)
  have ha : PolyT fun x => (((P x).getD (t x) default).1.map fun a => [(⟨1, .lin a⟩ : Term)]).getD [] :=
    (PolyT.optionElim (f := fun _ a => [(⟨1, .lin a⟩ : Term)]) (PolyT.fst hs) (PolyT.const [])
      (by fun_prop)).congr fun x => by cases ((P x).getD (t x) default).1 <;> rfl
  have hc : PolyT fun x => ((P x).getD (t x) default).2.2.2 := PolyT.snd (PolyT.snd (PolyT.snd hs))
  unfold slpChain
  fun_prop

theorem slpDesc_polyT (k : ℕ) {P : α → List Step} {fin : α → List CmpD} (hP : PolyT P) (hfin : PolyT fin) :
    PolyT fun x => slpDesc k (P x) (fin x) := by
  have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hprods : PolyT fun x => slpProds (P x) := by
    unfold slpProds
    exact PolyT.map (f := fun _ s => (⟨s.2.1, s.2.2.1⟩ : ProdD)) (by fun_prop) hP
  have hchains : PolyT fun x => (List.range (P x).length).map (slpChain k (P x)) :=
    PolyT.map (f := fun x t => slpChain k (P x) t) (slpChain_polyT k (PolyT.comp (f := P) hP hfst) hs)
      (PolyT.range (Unary.of_length hP))
  have hlen : PolyT fun x => (P x).length := PolyT.length hP
  unfold slpDesc
  fun_prop

/-! ## Representation-number descriptions -/

section Rep
variable {b ℓ : α → ℕ} (hb : Unary b) (hℓ : Unary ℓ)
include hb hℓ

theorem initStep_polyT {C : α → ℕ} (hC : PolyT C) : PolyT fun x => initStep (b x) (ℓ x) (C x) := by
  have := toLimbs_polyT hb hℓ hC
  unfold initStep
  fun_prop

theorem sumStep_polyT {base p : α → ℕ} {ms : α → List Mono} (hbase : PolyT base) (hms : PolyT ms) (hp : PolyT p) :
    PolyT fun x => sumStep (b x) (ℓ x) (base x) (ms x) (p x) := by
  have hg : PolyT fun x => (ms x).getD (p x / 2) default :=
    PolyT.getD hms (PolyT.div hp (PolyT.const 2)) (PolyT.const default)
  have ht := toLimbs_polyT hb hℓ (PolyT.snd (PolyT.snd hg))
  have h1 : PolyT fun x => ((ms x).getD (p x / 2) default).1 := PolyT.fst hg
  have h2 : PolyT fun x => ((ms x).getD (p x / 2) default).2.1 := PolyT.fst (PolyT.snd hg)
  have hc : PolyT fun x => decide (p x % 2 = 0) := PolyT.decide_eq (PolyT.mod hp (PolyT.const 2)) (PolyT.const 0)
  have hf : PolyT fun x => ((none : Option ℕ), ((ms x).getD (p x / 2) default).1,
      Operand.const (toLimbs (b x) (ℓ x) ((ms x).getD (p x / 2) default).2.2), ([] : List ℕ)) :=
    PolyT.prodMk (PolyT.const none) (PolyT.prodMk h1 (PolyT.prodMk (Operand.const_polyT ht) (PolyT.const [])))
  have hg : PolyT fun x => (some (base x + (p x - 1)), ((ms x).getD (p x / 2) default).2.1,
      Operand.var (base x + p x), ([] : List ℕ)) :=
    PolyT.prodMk (PolyT.some' (PolyT.add hbase (PolyT.sub hp (PolyT.const 1))))
      (PolyT.prodMk h2 (PolyT.prodMk (Operand.var_polyT (PolyT.add hbase hp)) (PolyT.const [])))
  exact (PolyT.ite' (c := fun x => p x % 2 = 0) hc hf hg).congr fun x => rfl

theorem sumProg_polyT {base C : α → ℕ} {ms : α → List Mono} (hbase : PolyT base) (hC : PolyT C)
    (hms : PolyT ms) : PolyT fun x => sumProg (b x) (ℓ x) (base x) (C x) (ms x) := by
  have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hm : PolyT fun x => (List.range (2 * (ms x).length)).map (sumStep (b x) (ℓ x) (base x) (ms x)) :=
    PolyT.map (f := fun x p => sumStep (b x) (ℓ x) (base x) (ms x) p)
      (sumStep_polyT (Unary.comp hb hfst) (Unary.comp hℓ hfst) (PolyT.comp (f := base) hbase hfst)
        (PolyT.comp (f := ms) hms hfst) hs)
      (PolyT.range (Unary.mul (Unary.const 2) (Unary.of_length hms)))
  unfold sumProg
  exact PolyT.cons' (initStep_polyT hb hℓ hC) hm

theorem repProg_polyT (k : ℕ) {mL mR : α → List Mono} {B n : α → ℕ} (hmL : PolyT mL) (hmR : PolyT mR)
    (hB : PolyT B) (hn : PolyT n) : PolyT fun x => repProg (b x) (ℓ x) k (mL x) (mR x) (B x) (n x) := by
  have h1 := sumProg_polyT hb hℓ (PolyT.const (k + 1)) (PolyT.const 0) hmL
  have h2 := sumProg_polyT hb hℓ (PolyT.add (PolyT.const (k + 2)) (PolyT.mul (PolyT.const 2) (PolyT.length hmL)))
    hn hmR
  unfold repProg
  exact PolyT.cons' (initStep_polyT hb hℓ hB) (PolyT.append h1 h2)

omit hb hℓ in
theorem repFin_polyT (k : ℕ) {mL mR : α → List Mono} (hmL : PolyT mL) (hmR : PolyT mR) :
    PolyT fun x => repFin k (mL x) (mR x) := by
  have h1 := PolyT.length hmL
  have h2 := PolyT.length hmR
  unfold repFin
  fun_prop

/-- **The representation-number description is polynomial-time** (`k` fixed). -/
theorem repDesc_polyT (k : ℕ) {mL mR : α → List Mono} {B n : α → ℕ} (hmL : PolyT mL) (hmR : PolyT mR)
    (hB : PolyT B) (hn : PolyT n) : PolyT fun x => repDesc (b x) (ℓ x) k (mL x) (mR x) (B x) (n x) :=
  slpDesc_polyT k (repProg_polyT hb hℓ k hmL hmR hB hn) (repFin_polyT k hmL hmR)

end Rep

end EthFollowup.ModP
