/-
# Parity of Hamiltonian cycles via Anthropic's Main Theorem

`HamiltonianAllGraphs.lean` builds, for every graph `G` on `Fin n` with root `r`, a width-5 CNF
`bigCNF G r` (in OpenAI's Finset-based `SAT.CNF` vocabulary) on `5|E| + 3n` variables whose model
count is congruent mod 2 to the number of Hamiltonian cycles of `G`.

Here that formula is fed to Anthropic's `MainResults.MainTheorem` (vendored, unchanged, in
`AnthropicStatement.lean`), which is phrased over list CNFs `List (List (Fin N × Bool))`:

* `cnfToList`: Finset CNF ↦ list CNF (`Finset.toList` on clauses and on the formula). It keeps the
  model count (`numSat_cnfToList`), the width (`cnfToList_width`) and is duplicate-free
  (`cnfToList_nodup`); its length is the number of clauses (`length_cnfToList`).
* `pad`: appends the tautological clause `[(i,true),(i,false)]` for every variable `i` not already
  present as such a clause, so that every variable occurs (`pad_allOccur`). This keeps `Nodup`,
  the model count, width `≤ max k 2`, adds at most `N` clauses and gives at least `N` clauses.
* `card_bigCNF_le`: `bigCNF G r` has at most `80|E| + 8n + 2` clauses.

Headline (`hamParity_allGraphs_anthropic`): conditional on `MainTheorem`, one machine `M` with
finite alphabets and one constant `C` such that for every graph on `n ≥ 2` vertices there is a
5-CNF `φ` on `N = 5|E| + 3n` variables with `N ≤ m := φ.length ≤ 85|E| + 11n + 2`, satisfying all
hypotheses of `MainTheorem`, whose model count is ≡ #Hamiltonian cycles (mod 2), and on which `M`
outputs the model count within `timeMin C 5 m N ≤ 2^{C·5m/√(lg m)}` steps (`timeMin_le_expM`).
-/
import EthFollowup.AnthropicStatement
import EthFollowup.HamiltonianAllGraphs

namespace EthFollowup.Anthropic

open OAI.Algorithms.SubexponentialSAT
open EthFollowup

/-! ### Finset CNF to list CNF -/

section Translate

variable {N : ℕ}

/-- A literal of the comparator vocabulary as a pair. -/
def litToPair (l : SAT.Literal (Fin N)) : MainResults.Lit N := (l.variable, l.positive)

theorem litToPair_injective : Function.Injective (litToPair (N := N)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [litToPair, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- A clause as a list of pairs. -/
noncomputable def clauseToList (C : SAT.Clause (Fin N)) : List (MainResults.Lit N) :=
  C.toList.map litToPair

theorem mem_clauseToList {C : SAT.Clause (Fin N)} {p : MainResults.Lit N} :
    p ∈ clauseToList C ↔ ∃ l ∈ C, litToPair l = p := by
  simp [clauseToList]

theorem clauseToList_injective : Function.Injective (clauseToList (N := N)) := by
  intro C D h
  ext l
  have : litToPair l ∈ clauseToList C ↔ litToPair l ∈ clauseToList D := by rw [h]
  simpa [mem_clauseToList, litToPair_injective.eq_iff] using this

theorem length_clauseToList (C : SAT.Clause (Fin N)) : (clauseToList C).length = C.card := by
  simp [clauseToList]

/-- A Finset CNF as a list CNF. -/
noncomputable def cnfToList (F : SAT.CNF (Fin N)) : MainResults.CNF N :=
  F.toList.map clauseToList

theorem cnfToList_nodup (F : SAT.CNF (Fin N)) : (cnfToList F).Nodup :=
  (Finset.nodup_toList F).map clauseToList_injective

theorem length_cnfToList (F : SAT.CNF (Fin N)) : (cnfToList F).length = F.card := by
  simp [cnfToList]

theorem cnfToList_width {F : SAT.CNF (Fin N)} {k : ℕ} (h : SAT.WidthAtMost k F) :
    ∀ C ∈ cnfToList F, C.length ≤ k := by
  intro C hC
  simp only [cnfToList, List.mem_map, Finset.mem_toList] at hC
  obtain ⟨D, hD, rfl⟩ := hC
  rw [length_clauseToList]
  exact h D hD

theorem cnfToList_sat_iff (F : SAT.CNF (Fin N)) (a : Fin N → Bool) :
    (∀ C ∈ cnfToList F, ∃ l ∈ C, a l.1 = l.2) ↔ SAT.CNF.eval a F = true := by
  rw [CNF.eval_iff]
  simp only [cnfToList, List.mem_map, Finset.mem_toList, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_clauseToList, Clause.eval_iff, SAT.Literal.eval, beq_iff_eq,
    litToPair]
  constructor
  · intro h C hC
    obtain ⟨p, ⟨l, hl, rfl⟩, hp⟩ := h C hC
    exact ⟨l, hl, hp⟩
  · intro h C hC
    obtain ⟨l, hl, hp⟩ := h C hC
    exact ⟨_, ⟨l, hl, rfl⟩, hp⟩

/-- The translation keeps the model count. -/
theorem numSat_cnfToList (F : SAT.CNF (Fin N)) :
    MainResults.numSat (cnfToList F) = SAT.count F := by
  unfold MainResults.numSat SAT.count SAT.satisfyingAssignments
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact cnfToList_sat_iff F a

end Translate

/-! ### Padding so that every variable occurs -/

section Pad

variable {N : ℕ}

/-- The tautological clause `xᵢ ∨ ¬xᵢ`. -/
def taut (i : Fin N) : List (MainResults.Lit N) := [(i, true), (i, false)]

theorem taut_injective : Function.Injective (taut (N := N)) := by
  intro i j h
  simp only [taut, List.cons.injEq, Prod.mk.injEq] at h
  exact h.1.1

/-- Append the tautological clause of every variable that is not already a clause. -/
def pad (φ : MainResults.CNF N) : MainResults.CNF N :=
  φ ++ ((List.finRange N).map taut).filter fun C => C ∉ φ

theorem taut_mem_pad (φ : MainResults.CNF N) (i : Fin N) : taut i ∈ pad φ := by
  by_cases h : taut i ∈ φ
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ (List.mem_filter.2 ⟨?_, by simpa using h⟩)
    exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩

theorem pad_nodup {φ : MainResults.CNF N} (h : φ.Nodup) : (pad φ).Nodup := by
  refine List.nodup_append.2 ⟨h, ((List.nodup_finRange N).map taut_injective).filter _, ?_⟩
  intro a ha b hb hab
  subst hab
  have := (List.mem_filter.1 hb).2
  simp only [decide_eq_true_eq] at this
  exact this ha

theorem pad_width {φ : MainResults.CNF N} {k : ℕ} (h : ∀ C ∈ φ, C.length ≤ k) (hk : 2 ≤ k) :
    ∀ C ∈ pad φ, C.length ≤ k := by
  intro C hC
  rcases List.mem_append.1 hC with hC | hC
  · exact h C hC
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hC).1
    simpa [taut] using hk

theorem pad_allOccur (φ : MainResults.CNF N) : MainResults.AllOccur (pad φ) :=
  fun i => ⟨taut i, taut_mem_pad φ i, (i, true), by simp [taut], rfl⟩

theorem pad_sat_iff (φ : MainResults.CNF N) (a : Fin N → Bool) :
    (∀ C ∈ pad φ, ∃ l ∈ C, a l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2) := by
  constructor
  · intro h C hC
    exact h C (List.mem_append_left _ hC)
  · intro h C hC
    rcases List.mem_append.1 hC with hC | hC
    · exact h C hC
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hC).1
      exact ⟨(i, a i), by cases a i <;> simp [taut], rfl⟩

theorem numSat_pad (φ : MainResults.CNF N) : MainResults.numSat (pad φ) = MainResults.numSat φ := by
  unfold MainResults.numSat
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact pad_sat_iff φ a

theorem length_pad_le (φ : MainResults.CNF N) : (pad φ).length ≤ φ.length + N := by
  rw [pad, List.length_append]
  refine Nat.add_le_add_left ((List.length_filter_le _ _).trans ?_) _
  simp

theorem le_length_pad (φ : MainResults.CNF N) : N ≤ (pad φ).length := by
  have h := ((List.nodup_finRange N).map (taut_injective (N := N))).length_le_of_subset
    (l₂ := pad φ) (by
      intro C hC
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hC
      exact taut_mem_pad φ i)
  simpa using h

end Pad

/-! ### The time bound -/

/-- `timeMin` is at most the `m`-branch of the minimum: `2^{C·k·m/√(lg m)}`. -/
theorem timeMin_le_expM (C k m n : ℕ) :
    (MainResults.timeMin C k m n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * MainResults.expM k m) := by
  unfold MainResults.timeMin
  refine (Nat.floor_le (by positivity)).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _))

/-! ### Number of clauses of `bigCNF` -/

section Count

open EthFollowup.Hamiltonian

theorem constraintCNF_card_le {α : Type*} [DecidableEq α] (S : Finset α)
    (good : Finset α → Prop) [DecidablePred good] {k : ℕ} (hk : S.card ≤ k) :
    (constraintCNF S good).card ≤ 2 ^ k :=
  Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans
    ((Finset.card_powerset S).le.trans (Nat.pow_le_pow_right (by norm_num) hk)))

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem card_adjPairs : (adjPairs G).card = 2 * G.edgeFinset.card := by
  rw [← SimpleGraph.dart_card_eq_twice_card_edges, ← Finset.card_univ]
  refine Finset.card_bij (fun p hp => (⟨p, (Finset.mem_filter.1 hp).2⟩ : G.Dart))
    (by simp) ?_ ?_
  · intro a _ b _ h
    exact congrArg SimpleGraph.Dart.toProd h
  · intro d _
    exact ⟨d.toProd, by simp [adjPairs, d.adj], rfl⟩

theorem card_restCNF_le (r : Fin n) : (restCNF G r).card ≤ 2 + 16 * G.edgeFinset.card := by
  unfold restCNF
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact constraintCNF_card_le _ _ (k := 1) (by simp)
  · refine (Finset.card_biUnion_le_card_mul _ _ (2 ^ 3) fun p _ =>
      constraintCNF_card_le _ _ Finset.card_le_three).trans ?_
    rw [Finset.card_attach, card_adjPairs]
    omega

theorem card_chainCNF_le (v : Fin n) : (chainCNF G v).card ≤ 8 + 32 * G.degree v := by
  unfold chainCNF
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (constraintCNF_card_le _ _ (k := 2) Finset.card_le_two)
      (constraintCNF_card_le _ _ (k := 2) Finset.card_le_two))) ?_)
  refine (Finset.card_biUnion_le_card_mul _ _ (2 ^ 5) fun i _ =>
    constraintCNF_card_le _ _ (by unfold stepScope; exact card_le_five _ _ _ _ _)).trans ?_
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- `bigCNF G r` has at most `80|E| + 8n + 2` clauses. -/
theorem card_bigCNF_le (r : Fin n) : (bigCNF G r).card ≤ 80 * G.edgeFinset.card + 8 * n + 2 := by
  unfold bigCNF
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (CNF.map Sum.inl (restCNF G r) : SAT.CNF (BVar G)).card ≤
      2 + 16 * G.edgeFinset.card :=
    Finset.card_image_le.trans (card_restCNF_le G r)
  have h2 : (Finset.univ.biUnion (chainCNF G)).card ≤ ∑ v : Fin n, (8 + 32 * G.degree v) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun v _ => card_chainCNF_le G v)
  have h3 : ∑ v : Fin n, (8 + 32 * G.degree v) = 8 * n + 64 * G.edgeFinset.card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp
    ring
  omega

theorem card_bigCNFFin_le (r : Fin n) :
    (bigCNFFin G r).card ≤ 80 * G.edgeFinset.card + 8 * n + 2 :=
  Finset.card_image_le.trans (card_bigCNF_le G r)

/-! ### The list formula -/

/-- The list CNF fed to the Main Theorem: `bigCNF` on `Fin (5|E| + 3n)`, translated and padded. -/
noncomputable def hamCNF (r : Fin n) : MainResults.CNF (Fintype.card (BVar G)) :=
  pad (cnfToList (bigCNFFin G r))

theorem hamCNF_isKCNF (r : Fin n) : MainResults.IsKCNF 5 (hamCNF G r) :=
  ⟨pad_width (cnfToList_width (CNF.relabel_width _ (bigCNF_width G r))) (by norm_num),
    pad_nodup (cnfToList_nodup _)⟩

theorem hamCNF_allOccur (r : Fin n) : MainResults.AllOccur (hamCNF G r) := pad_allOccur _

theorem numSat_hamCNF (r : Fin n) :
    (MainResults.numSat (hamCNF G r) : ZMod 2) = ((hamCycles G).card : ZMod 2) := by
  rw [hamCNF, numSat_pad, numSat_cnfToList, bigCNFFin, CNF.relabel_count, count_bigCNF_mod_two]

theorem length_hamCNF_le (r : Fin n) :
    (hamCNF G r).length ≤ 85 * G.edgeFinset.card + 11 * n + 2 := by
  have h1 := length_pad_le (cnfToList (bigCNFFin G r))
  rw [length_cnfToList] at h1
  have h2 := card_bigCNFFin_le G r
  have h3 := card_bvar G
  rw [hamCNF]
  omega

theorem le_length_hamCNF (r : Fin n) :
    5 * G.edgeFinset.card + 3 * n ≤ (hamCNF G r).length := by
  rw [← card_bvar]; exact le_length_pad _

end Count

/-! ### Headline -/

open EthFollowup.Hamiltonian in
/-- **Parity of Hamiltonian cycles from Anthropic's Main Theorem.** Conditional on
`MainResults.MainTheorem`, there are one machine `M` (finite stack alphabets) and one constant `C`
such that for every graph `G` on `n ≥ 2` vertices there is a list 5-CNF `φ` (namely
`hamCNF G 0`) on
`N = 5|E| + 3n` variables, with `N ≤ m ≤ 85|E| + 11n + 2` clauses (`m = φ.length`), every
variable occurring and no clause repeated, whose number of models is ≡ #Hamiltonian cycles of
`G` (mod 2), and on which `M` (started on `encInput 5 φ`) outputs the number of models within
`timeMin C 5 m N` steps; this is at most `2^{C·5m/√(lg m)}` (`timeMin_le_expM`). -/
theorem hamParity_allGraphs_anthropic (h : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n →
        ∃ (N : ℕ) (φ : MainResults.CNF N),
          N = 5 * G.edgeFinset.card + 3 * n ∧
          MainResults.IsKCNF 5 φ ∧ MainResults.AllOccur φ ∧
          N ≤ φ.length ∧ φ.length ≤ 85 * G.edgeFinset.card + 11 * n + 2 ∧
          (MainResults.numSat φ : ZMod 2) = ((hamCycles G).card : ZMod 2) ∧
          MainResults.CountsWithin M 5 φ (MainResults.timeMin C 5 φ.length N) ∧
          (MainResults.timeMin C 5 φ.length N : ℝ) ≤
            (2 : ℝ) ^ ((C : ℝ) * MainResults.expM 5 φ.length) := by
  obtain ⟨M, C, hfin, hrun⟩ := h
  refine ⟨M, C, hfin, fun n G _ hn => ?_⟩
  let r : Fin n := ⟨0, by omega⟩
  have hN := card_bvar G
  have hlen := le_length_hamCNF G r
  refine ⟨Fintype.card (BVar G), hamCNF G r, hN, hamCNF_isKCNF G r, hamCNF_allOccur G r,
    by omega, length_hamCNF_le G r, numSat_hamCNF G r, ?_, timeMin_le_expM _ _ _ _⟩
  exact hrun 5 _ (hamCNF G r) (by norm_num) (hamCNF_isKCNF G r) (by omega) (by omega)
    (hamCNF_allOccur G r)

end EthFollowup.Anthropic
