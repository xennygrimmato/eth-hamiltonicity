/-
# Hashes of the isolation lemma as CNFs

A hash `(A, b, D, α)` over a finite coordinate type `ι` becomes a CNF on `ι` of width
`max k 1`: one constraint per sparse equation and one unit constraint per fixed coordinate.
-/
import EthFollowup.CNFKit
import EthFollowup.IsolationLemma

namespace EthFollowup.Isolation

open OAI.Algorithms.SubexponentialSAT
open EthFollowup
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Hashes as CNFs -/

/-- One sparse equation `Σ_l c_l x_{j_l} = b` as a CNF on its (at most `k`) coordinates. -/
def eqnCNF {k : ℕ} (q : Eqn ι k) (b : ZMod 2) : SAT.CNF ι :=
  constraintCNF (univ.image q.1) fun T => ∑ l, bit (q.2 l) * bit (decide (q.1 l ∈ T)) = b

/-- Fixing one coordinate. -/
def unitCNF (e : ι) (v : Bool) : SAT.CNF ι :=
  constraintCNF {e} fun T => decide (e ∈ T) = v

/-- The CNF of a full hash `(A, b, D, α)`. -/
def hashCNF {k m : ℕ} (A : Sys ι k m) (b : Fin m → ZMod 2) (D : Finset ι)
    (α : ι → Bool) : SAT.CNF ι :=
  univ.biUnion (fun i => eqnCNF (A i) (b i)) ∪ D.biUnion (fun e => unitCNF e (α e))

theorem decide_mem_filter' {α' : Type*} [DecidableEq α'] {S : Finset α'} {x : α'} (hx : x ∈ S)
    (a : α' → Bool) : decide (x ∈ S.filter fun y => a y = true) = a x := by
  by_cases h : a x = true <;> simp [Finset.mem_filter, hx, h]

theorem eqnCNF_eval {k : ℕ} (q : Eqn ι k) (b : ZMod 2) (z : SAT.Assignment ι) :
    SAT.CNF.eval z (eqnCNF q b) = true ↔ evalEqn q z = b := by
  rw [eqnCNF, constraintCNF_eval, evalEqn]
  have : ∀ l, decide (q.1 l ∈ (univ.image q.1).filter fun x => z x = true) = z (q.1 l) :=
    fun l => decide_mem_filter' (Finset.mem_image_of_mem _ (Finset.mem_univ l)) z
  simp_rw [this]

theorem unitCNF_eval (e : ι) (v : Bool) (z : SAT.Assignment ι) :
    SAT.CNF.eval z (unitCNF e v) = true ↔ z e = v := by
  rw [unitCNF, constraintCNF_eval, decide_mem_filter' (Finset.mem_singleton_self e) z]

theorem hashCNF_eval {k m : ℕ} (A : Sys ι k m) (b : Fin m → ZMod 2)
    (D : Finset ι) (α : ι → Bool) (z : SAT.Assignment ι) :
    SAT.CNF.eval z (hashCNF A b D α) = true ↔ applySys A z = b ∧ ∀ e ∈ D, z e = α e := by
  rw [hashCNF, CNF.eval_union, CNF.eval_biUnion, CNF.eval_biUnion]
  simp only [Finset.mem_univ, true_implies, eqnCNF_eval, unitCNF_eval]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨funext h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun i => congrFun h1 i, h2⟩

theorem hashCNF_width {k m : ℕ} (A : Sys ι k m) (b : Fin m → ZMod 2)
    (D : Finset ι) (α : ι → Bool) :
    SAT.WidthAtMost (max k 1) (hashCNF A b D α) := by
  refine width_union (width_biUnion fun i _ => constraintCNF_width _ _ ?_)
    (width_biUnion fun e _ => constraintCNF_width _ _ ?_)
  · exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]; exact le_max_left _ _)
  · rw [Finset.card_singleton]; exact le_max_right _ _

/-- The hash space and its size. -/
theorem card_hashSpace (k m d : ℕ) :
    ((univ : Finset (Sys ι k m × (Fin m → ZMod 2))) ×ˢ
        ((univ : Finset ι).powersetCard d ×ˢ (univ : Finset (ι → Bool)))).card =
      Fintype.card (Sys ι k m) * 2 ^ m * (Fintype.card ι).choose d * 2 ^ Fintype.card ι := by
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod, Finset.card_powersetCard,
    Fintype.card_fun, Fintype.card_bool, ZMod.card, Fintype.card_fin, Sys]
  ring

end EthFollowup.Isolation
