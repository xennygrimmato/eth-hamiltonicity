import Mathlib.Data.ZMod.Defs
import Mathlib.Data.List.Rotate
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# The turn-labelling invariant k*: basic definitions (`research/kstar.md` §1)

Copied from `EthFollowup/Scratch/Kstar/Basic.lean` (definitions unchanged; the list-level
definitions `cyclicPairs`, `turns`, `cycleSum`, `isDirCycle` are stated for an arbitrary vertex
type `α`, which for `α = Fin n` are literally the scratch definitions).

A graph on `Fin n` is given by a Boolean adjacency `adj` (it plays the role of `G − r`). A
*directed cycle* is a list `c = [v₀,…,v_{L-1}]` of distinct vertices, `L ≥ 3`, with `vᵢ ~ vᵢ₊₁`
cyclically. Its turns are `(vᵢ; vᵢ₋₁, vᵢ₊₁)`. A labelling is
`F : Fin n → Fin n → Fin n → (Fin k → ZMod 2)`, where `F v u w` is the label of the turn at `v`
from `u` to `w`. `F` is *good* if every directed cycle has nonzero label sum; `k*(G)` is the least
`k` admitting a good labelling.
-/

namespace Kstar

variable {α : Type*} {n k : ℕ}

/-- consecutive pairs `(cᵢ, cᵢ₊₁)` cyclically. -/
def cyclicPairs (c : List α) : List (α × α) := c.zip (c.rotate 1)

/-- Boolean test: `c` is a directed simple cycle of `adj`. -/
def isDirCycle [DecidableEq α] (adj : α → α → Bool) (c : List α) : Bool :=
  decide (3 ≤ c.length) && c.Nodup && (cyclicPairs c).all (fun p => adj p.1 p.2)

/-- the turns `(vᵢ; vᵢ₋₁, vᵢ₊₁)` of a cyclic list. -/
def turns (c : List α) : List (α × α × α) :=
  List.zip c (List.zip (c.rotate (c.length - 1)) (c.rotate 1))

/-- the label sum of a cycle. -/
def cycleSum (F : α → α → α → (Fin k → ZMod 2)) (c : List α) : Fin k → ZMod 2 :=
  ((turns c).map (fun t => F t.1 t.2.1 t.2.2)).sum

/-- `F` is good (nowhere-zero): the true definition, quantifying over all lists. -/
def Good (adj : Fin n → Fin n → Bool) (F : Fin n → Fin n → Fin n → (Fin k → ZMod 2)) : Prop :=
  ∀ c : List (Fin n), isDirCycle adj c = true → cycleSum F c ≠ 0

/-- **Subgraph monotonicity**: a good labelling of `G` is good for every subgraph. -/
theorem good_mono {adj adj' : Fin n → Fin n → Bool} (hsub : ∀ u v, adj' u v = true → adj u v = true)
    {F : Fin n → Fin n → Fin n → (Fin k → ZMod 2)} (hF : Good adj F) : Good adj' F := by
  intro c hc
  apply hF c
  simp only [isDirCycle, Bool.and_eq_true, List.all_eq_true] at hc ⊢
  exact ⟨hc.1, fun p hp => hsub _ _ (hc.2 p hp)⟩

end Kstar
