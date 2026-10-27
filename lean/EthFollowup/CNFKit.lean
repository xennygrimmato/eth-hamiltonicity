/-
A small toolkit for building CNF encodings in the comparator's `SAT` vocabulary.

* `constraintCNF S good`: the CNF on scope `S` whose models are exactly the assignments whose
  set of true variables inside `S` satisfies `good`. One clause per bad local pattern, each of
  width `≤ |S|` (the encoding used in the manuscript's Corollary C.2).
* evaluation lemmas for unions and indexed unions of CNFs;
* `CNF.relabel`: transport a CNF along an equivalence of variable types, preserving the model
  count and the width. This lets encodings over structured types feed the comparator statement,
  which is phrased over `Fin n`.
-/
import EthFollowup.Comparator

namespace EthFollowup

open OAI.Algorithms.SubexponentialSAT

universe u v

section Kit

variable {α : Type u} [DecidableEq α]

theorem Clause.eval_iff (a : SAT.Assignment α) (C : SAT.Clause α) :
    C.eval a = true ↔ ∃ l ∈ C, l.eval a = true := by
  unfold SAT.Clause.eval; exact decide_eq_true_iff

theorem CNF.eval_iff (a : SAT.Assignment α) (F : SAT.CNF α) :
    SAT.CNF.eval a F = true ↔ ∀ C ∈ F, C.eval a = true := by
  unfold SAT.CNF.eval; exact decide_eq_true_iff

/-- The clause on scope `S` that is falsified exactly when the true variables in `S` are `T`. -/
def clauseOf (S T : Finset α) : SAT.Clause α :=
  S.image fun x => (⟨x, decide (x ∉ T)⟩ : SAT.Literal α)

theorem clauseOf_eval (S T : Finset α) (hT : T ⊆ S) (a : SAT.Assignment α) :
    (clauseOf S T).eval a = true ↔ S.filter (fun x => a x = true) ≠ T := by
  rw [Clause.eval_iff]
  simp only [clauseOf, Finset.mem_image]
  constructor
  · rintro ⟨l, ⟨x, hx, rfl⟩, hl⟩ hEq
    simp only [SAT.Literal.eval, beq_iff_eq] at hl
    by_cases hxT : x ∈ T
    · have : x ∈ S.filter (fun x => a x = true) := hEq ▸ hxT
      simp only [Finset.mem_filter] at this
      simp [hxT, this.2] at hl
    · have hfx : x ∉ S.filter (fun x => a x = true) := hEq ▸ hxT
      simp only [Finset.mem_filter, not_and] at hfx
      have := hfx hx
      simp [hxT] at hl
      exact this hl
  · intro hne
    by_contra hcon
    apply hne
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hax⟩
      by_contra hxT
      exact hcon ⟨⟨x, decide (x ∉ T)⟩, ⟨x, hx, rfl⟩, by simp [SAT.Literal.eval, hxT, hax]⟩
    · intro hxT
      refine ⟨hT hxT, ?_⟩
      by_contra hax
      exact hcon ⟨⟨x, decide (x ∉ T)⟩, ⟨x, hT hxT, rfl⟩, by simp [SAT.Literal.eval, hxT, hax]⟩

theorem clauseOf_card_le (S T : Finset α) : (clauseOf S T).card ≤ S.card :=
  Finset.card_image_le

/-- The CNF expressing the local constraint `good` on the scope `S`. -/
def constraintCNF (S : Finset α) (good : Finset α → Prop) [DecidablePred good] : SAT.CNF α :=
  (S.powerset.filter fun T => ¬ good T).image (clauseOf S)

theorem constraintCNF_eval (S : Finset α) (good : Finset α → Prop) [DecidablePred good]
    (a : SAT.Assignment α) :
    SAT.CNF.eval a (constraintCNF S good) = true ↔ good (S.filter fun x => a x = true) := by
  rw [CNF.eval_iff]
  simp only [constraintCNF, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset,
    forall_exists_index, and_imp]
  constructor
  · intro h
    by_contra hbad
    have := h _ _ (Finset.filter_subset _ S) hbad rfl
    exact ((clauseOf_eval S _ (Finset.filter_subset _ S) a).1 this) rfl
  · rintro hgood C T hTS hT rfl
    rw [clauseOf_eval S T hTS a]
    rintro rfl
    exact hT hgood

theorem constraintCNF_width (S : Finset α) (good : Finset α → Prop) [DecidablePred good]
    {k : ℕ} (hk : S.card ≤ k) : SAT.WidthAtMost k (constraintCNF S good) := by
  intro C hC
  simp only [constraintCNF, Finset.mem_image] at hC
  obtain ⟨T, -, rfl⟩ := hC
  exact (clauseOf_card_le S T).trans hk

theorem CNF.eval_union (F G : SAT.CNF α) (a : SAT.Assignment α) :
    SAT.CNF.eval a (F ∪ G) = true ↔ SAT.CNF.eval a F = true ∧ SAT.CNF.eval a G = true := by
  simp only [CNF.eval_iff, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun C hC => h C (Or.inl hC), fun C hC => h C (Or.inr hC)⟩
  · rintro ⟨h1, h2⟩ C (hC | hC)
    exacts [h1 C hC, h2 C hC]

theorem CNF.eval_biUnion {ι : Type v} (s : Finset ι) (F : ι → SAT.CNF α)
    (a : SAT.Assignment α) :
    SAT.CNF.eval a (s.biUnion F) = true ↔ ∀ i ∈ s, SAT.CNF.eval a (F i) = true := by
  simp only [CNF.eval_iff, Finset.mem_biUnion, forall_exists_index, and_imp]
  constructor
  · intro h i hi C hC; exact h C i hi hC
  · intro h C i hi hC; exact h i hi C hC

theorem width_union {F G : SAT.CNF α} {k : ℕ} (hF : SAT.WidthAtMost k F)
    (hG : SAT.WidthAtMost k G) : SAT.WidthAtMost k (F ∪ G) := by
  intro C hC
  rcases Finset.mem_union.1 hC with h | h
  exacts [hF C h, hG C h]

theorem width_biUnion {ι : Type v} {s : Finset ι} {F : ι → SAT.CNF α} {k : ℕ}
    (h : ∀ i ∈ s, SAT.WidthAtMost k (F i)) : SAT.WidthAtMost k (s.biUnion F) := by
  intro C hC
  obtain ⟨i, hi, hC⟩ := Finset.mem_biUnion.1 hC
  exact h i hi C hC

end Kit

section Relabel

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Rename the variables of a literal along an equivalence. -/
def Literal.relabel (e : α ≃ β) (l : SAT.Literal α) : SAT.Literal β :=
  ⟨e l.variable, l.positive⟩

/-- Rename the variables of a CNF along an equivalence. -/
def CNF.relabel (e : α ≃ β) (F : SAT.CNF α) : SAT.CNF β :=
  F.image fun C => C.image (Literal.relabel e)

theorem CNF.relabel_eval (e : α ≃ β) (F : SAT.CNF α) (a : SAT.Assignment β) :
    SAT.CNF.eval a (CNF.relabel e F) = SAT.CNF.eval (a ∘ e) F := by
  rw [Bool.eq_iff_iff, CNF.eval_iff, CNF.eval_iff]
  simp only [CNF.relabel, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Clause.eval_iff, exists_exists_and_eq_and, Literal.relabel,
    SAT.Literal.eval, Function.comp]

theorem CNF.relabel_width (e : α ≃ β) {F : SAT.CNF α} {k : ℕ} (h : SAT.WidthAtMost k F) :
    SAT.WidthAtMost k (CNF.relabel e F) := by
  intro C hC
  simp only [CNF.relabel, Finset.mem_image] at hC
  obtain ⟨C', hC', rfl⟩ := hC
  exact Finset.card_image_le.trans (h C' hC')

theorem CNF.relabel_count [Fintype α] [Fintype β] (e : α ≃ β) (F : SAT.CNF α) :
    SAT.count (CNF.relabel e F) = SAT.count F := by
  unfold SAT.count SAT.satisfyingAssignments
  refine Finset.card_bij' (fun a _ => a ∘ e) (fun b _ => b ∘ e.symm) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rwa [CNF.relabel_eval] at ha
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [CNF.relabel_eval]
    have : (b ∘ e.symm) ∘ e = b := by funext x; simp
    rwa [this]
  · intro a _; funext x; simp
  · intro b _; funext x; simp

end Relabel

end EthFollowup

namespace EthFollowup

open OAI.Algorithms.SubexponentialSAT

section Map

universe u' v'
variable {α : Type u'} {β : Type v'} [DecidableEq α] [DecidableEq β]

/-- Rename the variables of a CNF along an arbitrary function. -/
def CNF.map (f : α → β) (F : SAT.CNF α) : SAT.CNF β :=
  F.image fun C => C.image fun l => (⟨f l.variable, l.positive⟩ : SAT.Literal β)

theorem CNF.map_eval (f : α → β) (F : SAT.CNF α) (a : SAT.Assignment β) :
    SAT.CNF.eval a (CNF.map f F) = SAT.CNF.eval (a ∘ f) F := by
  rw [Bool.eq_iff_iff, CNF.eval_iff, CNF.eval_iff]
  simp only [CNF.map, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Clause.eval_iff, exists_exists_and_eq_and,
    SAT.Literal.eval, Function.comp]

omit [DecidableEq α] in
theorem CNF.map_width (f : α → β) {F : SAT.CNF α} {k : ℕ} (h : SAT.WidthAtMost k F) :
    SAT.WidthAtMost k (CNF.map f F) := by
  classical
  intro C hC
  simp only [CNF.map, Finset.mem_image] at hC
  obtain ⟨C', hC', rfl⟩ := hC
  exact Finset.card_image_le.trans (h C' hC')

end Map

end EthFollowup
