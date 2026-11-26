import Mathlib

/-!
# Pruned run-tree evaluation (referee fix to Lemma 2's cost model)

A run tree: binary `guess` nodes, leaves that either reject or accept with a weight in a
commutative ring and a step count. The evaluator prunes at `g` guesses (depth) and `t` steps.

* `leaves_prune_le` : the pruned tree has `≤ 2^g` leaves **by construction** (no hypothesis).
* `sum_prune_eq`    : the pruned sum equals the true sum whenever every **accepting** leaf has
  depth `≤ g` and cost `≤ t`; rejecting leaves are unconstrained (they contribute 0).

This matches Anthropic's semantics: `NS1.Ev` lists the accepting runs only (`fail` gives `[]`)
and `Does` bounds the cost of accepting runs only (`NS1/Comp.lean` l.69).
-/

namespace PortsLean.Pruned

variable {A : Type} [CommRing A]

inductive RTree (A : Type) where
  | reject : RTree A
  | accept (w : A) (cost : ℕ) : RTree A
  | guess (l r : RTree A) : RTree A

namespace RTree

/-- Sum of the weights of accepting leaves. -/
def sum : RTree A → A
  | reject => 0
  | accept w _ => w
  | guess l r => l.sum + r.sum

def leaves : RTree A → ℕ
  | reject => 1
  | accept _ _ => 1
  | guess l r => l.leaves + r.leaves

/-- Every accepting leaf is at depth `≤ g` and has cost `≤ t`. -/
def AccBounded : RTree A → ℕ → ℕ → Prop
  | reject, _, _ => True
  | accept _ c, _, t => c ≤ t
  | guess _ _, 0, _ => False
  | guess l r, g + 1, t => l.AccBounded g t ∧ r.AccBounded g t

/-- Prune at `g` guesses and `t` steps. -/
def prune : RTree A → ℕ → ℕ → RTree A
  | reject, _, _ => reject
  | accept w c, _, t => if c ≤ t then accept w c else reject
  | guess _ _, 0, _ => reject
  | guess l r, g + 1, t => guess (l.prune g t) (r.prune g t)

omit [CommRing A] in
theorem leaves_prune_le (T : RTree A) (g t : ℕ) : (T.prune g t).leaves ≤ 2 ^ g := by
  induction T generalizing g with
  | reject => simp [prune, leaves, Nat.one_le_two_pow]
  | accept w c => unfold prune; split_ifs <;> simp [leaves, Nat.one_le_two_pow]
  | guess l r ihl ihr =>
    cases g with
    | zero => simp [prune, leaves]
    | succ g =>
      simp only [prune, leaves, pow_succ]
      have := ihl g; have := ihr g; omega

theorem sum_prune_eq (T : RTree A) (g t : ℕ) (h : T.AccBounded g t) :
    (T.prune g t).sum = T.sum := by
  induction T generalizing g with
  | reject => rfl
  | accept w c => simp only [AccBounded] at h; simp [prune, h, sum]
  | guess l r ihl ihr =>
    cases g with
    | zero => exact h.elim
    | succ g => simp only [prune, sum, ihl g h.1, ihr g h.2]

end RTree
end PortsLean.Pruned
