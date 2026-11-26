import Mathlib

/-!
# Parsimony of Tseitin-style gate encodings

A circuit with `n` inputs and `g` gates is a snoc-list of gates; gate number `i` is an arbitrary
Boolean function of the `n + i` earlier wires. A full wire assignment `w : Fin (n+g) → Bool` is
*consistent* if every gate wire equals its gate applied to the earlier wires (the semantic content
of the Tseitin clauses). Consistent assignments are in bijection with input assignments.

We also check that, for a fan-in-2 gate `w = G(u, v)`, the four width-3 Tseitin clauses
`(u ≠ α) ∨ (v ≠ β) ∨ (w = G α β)` (one per `(α, β)`) are equivalent to `w = G u v`.
-/

namespace IsoLean

/-- A circuit with `n` inputs and `g` gates; each new gate reads all earlier wires. -/
inductive Circuit (n : ℕ) : ℕ → Type
  | nil : Circuit n 0
  | snoc {g : ℕ} : Circuit n g → ((Fin (n + g) → Bool) → Bool) → Circuit n (g + 1)

namespace Circuit

variable {n : ℕ}

/-- The wire assignment determined by an input assignment. -/
def eval : {g : ℕ} → Circuit n g → (Fin n → Bool) → Fin (n + g) → Bool
  | _, nil, x => x
  | _, snoc c f, x => Fin.snoc (α := fun _ => Bool) (eval c x) (f (eval c x))

/-- Every gate wire agrees with its gate. -/
def Consistent : {g : ℕ} → Circuit n g → (Fin (n + g) → Bool) → Prop
  | _, nil, _ => True
  | _, snoc c f, w => Consistent c (Fin.init w) ∧ w (Fin.last _) = f (Fin.init w)

/-- The input part of a wire assignment. -/
def inputs {g : ℕ} (w : Fin (n + g) → Bool) : Fin n → Bool := fun i => w (Fin.castAdd g i)

lemma inputs_init {g : ℕ} (w : Fin (n + (g + 1)) → Bool) :
    inputs (g := g) (Fin.init w) = inputs (g := g + 1) w := by
  funext i; rfl

lemma inputs_eval : {g : ℕ} → (c : Circuit n g) → (x : Fin n → Bool) → inputs (eval c x) = x
  | _, nil, x => by funext i; rfl
  | _, @snoc _ g c f, x => by
    funext i
    have h := congrFun (inputs_eval c x) i
    simp only [inputs] at h ⊢
    simp only [eval]
    have : (Fin.castAdd (g + 1) i : Fin (n + g + 1)) = (Fin.castAdd g i).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
    exact h

lemma consistent_iff : {g : ℕ} → (c : Circuit n g) → (w : Fin (n + g) → Bool) →
    (Consistent c w ↔ w = eval c (inputs w))
  | _, nil, w => by
    simp only [Consistent, eval, true_iff]
    funext i; rfl
  | _, snoc c f, w => by
    simp only [Consistent, eval]
    rw [consistent_iff c (Fin.init w), inputs_init]
    constructor
    · rintro ⟨h1, h2⟩
      conv_lhs => rw [← Fin.snoc_init_self (α := fun _ => Bool) w]
      rw [h2, ← h1]
    · intro h
      have hi : Fin.init w = eval c (inputs w) := by
        conv_lhs => rw [h]
        exact Fin.init_snoc (α := fun _ => Bool) _ _
      refine ⟨hi, ?_⟩
      rw [hi]
      conv_lhs => rw [h]
      exact Fin.snoc_last (α := fun _ => Bool) _ _

lemma eval_consistent {g : ℕ} (c : Circuit n g) (x : Fin n → Bool) : Consistent c (eval c x) := by
  rw [consistent_iff, inputs_eval]

/-- **Parsimony.** Consistent wire assignments ≃ input assignments. -/
def consistentEquiv {g : ℕ} (c : Circuit n g) : {w // Consistent c w} ≃ (Fin n → Bool) where
  toFun w := inputs w.1
  invFun x := ⟨eval c x, eval_consistent c x⟩
  left_inv w := Subtype.ext ((consistent_iff c w.1).mp w.2).symm
  right_inv x := inputs_eval c x

/-- **Parsimony with side conditions.** For any property `P` of wire assignments (e.g.
"`F` holds on the inputs and the output wires are `0`"),
`#{w : Consistent c w ∧ P w} = #{x : P (eval c x)}`. -/
def consistentEquivProp {g : ℕ} (c : Circuit n g) (P : (Fin (n + g) → Bool) → Prop) :
    {w // Consistent c w ∧ P w} ≃ {x : Fin n → Bool // P (eval c x)} where
  toFun w := ⟨inputs w.1, by
    have h := (consistent_iff c w.1).mp w.2.1
    rw [← h]; exact w.2.2⟩
  invFun x := ⟨eval c x, eval_consistent c x, x.2⟩
  left_inv w := Subtype.ext ((consistent_iff c w.1).mp w.2.1).symm
  right_inv x := Subtype.ext (inputs_eval c x.1)

theorem card_consistent {g : ℕ} (c : Circuit n g) (P : (Fin (n + g) → Bool) → Prop) :
    Nat.card {w // Consistent c w ∧ P w} = Nat.card {x : Fin n → Bool // P (eval c x)} :=
  Nat.card_congr (consistentEquivProp c P)

/-- The Tseitin / F ∧ C(x) = 0 instance: `F` a predicate on inputs, `out` a set of wires
required to be `false`. -/
theorem card_tseitin {g : ℕ} (c : Circuit n g) (F : (Fin n → Bool) → Prop)
    (out : Finset (Fin (n + g))) :
    Nat.card {w // Consistent c w ∧ (F (inputs w) ∧ ∀ o ∈ out, w o = false)}
      = Nat.card {x : Fin n → Bool // F x ∧ ∀ o ∈ out, eval c x o = false} := by
  rw [card_consistent]
  simp only [inputs_eval]

end Circuit

/-- The four width-3 Tseitin clauses of a fan-in-2 gate `w = G(u,v)`:
for each `(α, β)`, the clause `(u ≠ α) ∨ (v ≠ β) ∨ (w = G α β)`. -/
def gateClauses (G : Bool → Bool → Bool) (u v w : Bool) : Prop :=
  ∀ α β : Bool, u ≠ α ∨ v ≠ β ∨ w = G α β

theorem gateClauses_iff (G : Bool → Bool → Bool) (u v w : Bool) :
    gateClauses G u v w ↔ w = G u v := by
  constructor
  · intro h
    rcases h u v with h | h | h
    · exact absurd rfl h
    · exact absurd rfl h
    · exact h
  · rintro rfl α β
    by_cases hu : u = α
    · by_cases hv : v = β
      · subst hu; subst hv; exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl hv)
    · exact Or.inl hu

end IsoLean
