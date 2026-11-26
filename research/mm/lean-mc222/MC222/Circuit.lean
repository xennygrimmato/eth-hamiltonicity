import MC222.Statement

/-!
# General facts about circuits (Lemma 4.1(a) of the paper, in the form used here)
-/

namespace MC222

open Submodule

variable {k : ℕ}

theorem one_mem_S (g : Fin k → Fn) (j : ℕ) : (1 : Fn) ∈ S g j :=
  subset_span (Set.mem_insert _ _)

theorem x_mem_S (g : Fin k → Fn) (j : ℕ) (i : Fin 8) : x i ∈ S g j :=
  subset_span (Set.mem_insert_of_mem _ (Or.inl ⟨i, rfl⟩))

theorem g_mem_S (g : Fin k → Fn) {j : ℕ} (i : Fin k) (h : i.val < j) : g i ∈ S g j :=
  subset_span (Set.mem_insert_of_mem _ (Or.inr ⟨i, h, rfl⟩))

theorem S_le (g : Fin k → Fn) (j : ℕ) (M : Submodule (ZMod 2) Fn) (h1 : (1 : Fn) ∈ M)
    (hx : ∀ i, x i ∈ M) (hg : ∀ i : Fin k, i.val < j → g i ∈ M) : S g j ≤ M := by
  refine span_le.mpr ?_
  rintro f (rfl | ⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
  · exact h1
  · exact hx i
  · exact hg i hi

theorem S_mono (g : Fin k → Fn) {j j' : ℕ} (h : j ≤ j') : S g j ≤ S g j' :=
  S_le g j _ (one_mem_S _ _) (x_mem_S _ _) fun i hi => g_mem_S g i (by omega)

theorem S_congr (g g' : Fin k → Fn) (j : ℕ) (h : ∀ i : Fin k, i.val < j → g i = g' i) :
    S g j = S g' j :=
  le_antisymm (S_le g j _ (one_mem_S _ _) (x_mem_S _ _) fun i hi => h i hi ▸ g_mem_S g' i hi)
    (S_le g' j _ (one_mem_S _ _) (x_mem_S _ _) fun i hi => (h i hi).symm ▸ g_mem_S g i hi)

/-- Comparison lemma: if each gate of `g` lies in the corresponding space of `g'`, the spaces
of `g` are contained in those of `g'`. -/
theorem S_le_of (g g' : Fin k → Fn) (h : ∀ i : Fin k, g i ∈ S g' (i.val + 1)) (j : ℕ) :
    S g j ≤ S g' j :=
  S_le g j _ (one_mem_S _ _) (x_mem_S _ _) fun i hi => S_mono g' (by omega) (h i)

/-- Replacing gate `m` by a product `u * v` of two elements of `S g m` such that the old gate
lies in `S g m + span{u * v}` gives a circuit whose spaces contain the old ones. -/
theorem update_circuit (g : Fin k → Fn) (hg : IsCircuit g) (m : Fin k) (u v : Fn)
    (hu : u ∈ S g m) (hv : v ∈ S g m) (hm : g m ∈ S g m ⊔ span (ZMod 2) {u * v}) :
    IsCircuit (Function.update g m (u * v)) ∧ (∀ j, S g j ≤ S (Function.update g m (u * v)) j) ∧
      (∀ i : Fin k, i ≠ m → Function.update g m (u * v) i = g i) := by
  set g' := Function.update g m (u * v)
  have hsame : ∀ i : Fin k, i ≠ m → g' i = g i := fun i hi => Function.update_of_ne hi _ _
  have hSm : S g m = S g' m :=
    S_congr g g' m fun i hi => (hsame i (fun h => by subst h; omega)).symm
  have hgm : g' m = u * v := Function.update_self _ _ _
  have hle : ∀ i : Fin k, g i ∈ S g' (i.val + 1) := by
    intro i
    by_cases him : i = m
    · subst him
      have h1 : S g i ≤ S g' (i.val + 1) := hSm ▸ S_mono g' (Nat.le_succ _)
      have h2 : span (ZMod 2) {u * v} ≤ S g' (i.val + 1) :=
        (span_singleton_le_iff_mem _ _).mpr (hgm ▸ g_mem_S g' i (Nat.lt_succ_self _))
      exact sup_le h1 h2 hm
    · rw [← hsame i him]; exact g_mem_S g' i (Nat.lt_succ_self _)
  refine ⟨?_, S_le_of g g' hle, hsame⟩
  intro i
  by_cases him : i = m
  · subst him; exact ⟨u, hSm ▸ hu, v, hSm ▸ hv, hgm⟩
  · obtain ⟨u', hu', v', hv', he⟩ := hg i
    exact ⟨u', S_le_of g g' hle i hu', v', S_le_of g g' hle i hv', (hsame i him).trans he⟩

/-- Padding: a circuit with `k` gates gives one with `k + 1` gates (append `x 0 * x 0`). -/
theorem HasCircuit.succ {k : ℕ} (h : HasCircuit k) : HasCircuit (k + 1) := by
  obtain ⟨g, hg, hc⟩ := h
  refine ⟨Fin.snoc g (x 0 * x 0), ?_, ?_⟩
  · have hS : ∀ i : Fin k, S g i ≤ S (Fin.snoc g (x 0 * x 0) : Fin (k + 1) → Fn) i := fun i =>
      S_le g i _ (one_mem_S _ _) (x_mem_S _ _) fun i' hi' => by
        have := g_mem_S (Fin.snoc g (x 0 * x 0) : Fin (k + 1) → Fn) i'.castSucc hi'
        simpa using this
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact ⟨x 0, x_mem_S _ _ _, x 0, x_mem_S _ _ _, by simp⟩
    · obtain ⟨u, hu, v, hv, he⟩ := hg i
      exact ⟨u, by simpa using hS i hu, v, by simpa using hS i hv, by simpa using he⟩
  · intro i j
    refine S_le g k _ (one_mem_S _ _) (x_mem_S _ _) (fun i' hi' => ?_) (hc i j)
    have := g_mem_S (j := k + 1) (Fin.snoc g (x 0 * x 0) : Fin (k + 1) → Fn) i'.castSucc
      (by simp)
    simpa using this

theorem HasCircuit.mono {k k' : ℕ} (h : HasCircuit k) (hk : k ≤ k') : HasCircuit k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

end MC222
