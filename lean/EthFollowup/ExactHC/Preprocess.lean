/-
# Preprocessing for exact #HC: degree reduction and degree-balanced partition

Module M4 of `research/lean-blueprint.md`; §6.1 of `research/exact-hc-theorem.md`.

* **Lemma 6.1 (degree reduction).** Let `H := {v : Θ < deg v}`. A choice `π` assigns to each
  `v ∈ H` a 2-element subset `π v` of the edges at `v` (and `∅` to `v ∉ H`); no consistency
  between different vertices is required. `reduced G Θ π` is `G` minus every edge `e` at a vertex
  `v ∈ H` with `e ∉ π v`. Then
  - `#HC(G) = Σ_π #HC(G_π)`                               (`card_hamCycles_eq_sum_reduced`);
  - the number of choices is `Π_{v∈H} C(deg v, 2) ≤ n^{2|H|}` (`card_choices`,
    `card_choices_le`), and `|H|·Θ ≤ 2m`, strictly if `H ≠ ∅` (`card_high_mul_le`,
    `card_high_mul_lt`);
  - every `G_π` is a subgraph of `G` on the same vertex set, so has at most `m` edges, and for
    `Θ ≥ 2` it has maximum degree `≤ Θ` (`reduced_le`, `card_edgeFinset_reduced_le`,
    `degree_reduced_le`).
* **Lemma 6.2 (degree-balanced partition).** List the vertices as `v_t = σ t`, let
  `S_t := Σ_{s<t} deg v_s` and `β(v_t) := min(g, ⌊g S_t/(2m)⌋ + 1)`. Then `1 ≤ β ≤ g` and every
  blob has `g · μ_a ≤ 2m + g · Δ`, i.e. `μ_a ≤ 2m/g + Δ` (`blob_degree_sum_le`,
  `blob_degree_sum_le_rat`, `exists_balanced_partition`).
-/
import EthFollowup.HamiltonianParity

namespace EthFollowup.ExactHC

open Finset EthFollowup.Hamiltonian

/-! ## Lemma 6.1: degree reduction -/

section DegreeReduction

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The edges of `G` at `v`. -/
def incEdges (v : Fin n) : Finset (Sym2 (Fin n)) := G.edgeFinset.filter fun e => v ∈ e

theorem card_incEdges (v : Fin n) : (incEdges G v).card = G.degree v := by
  rw [incEdges, ← G.incidenceFinset_eq_filter, G.card_incidenceFinset_eq_degree]

/-- The high-degree vertices `H = {v : deg v > Θ}`. -/
def high (Θ : ℕ) : Finset (Fin n) := univ.filter fun v => Θ < G.degree v

/-- The admissible choices `π`: a 2-subset of the edges at each `v ∈ H`, and `∅` elsewhere. -/
def choices (Θ : ℕ) : Finset (Fin n → Finset (Sym2 (Fin n))) :=
  Fintype.piFinset fun v => if Θ < G.degree v then (incEdges G v).powersetCard 2 else {∅}

/-- The edge `e` survives in `G_π`: at every endpoint `v ∈ H`, `e ∈ π v`. -/
def Keep (Θ : ℕ) (π : Fin n → Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Prop :=
  ∀ v ∈ e, Θ < G.degree v → e ∈ π v

instance (Θ : ℕ) (π : Fin n → Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    Decidable (Keep G Θ π e) := by
  unfold Keep; infer_instance

/-- `G_π`: delete every edge at a vertex `v ∈ H` that is not in `π v`. -/
def reduced (Θ : ℕ) (π : Fin n → Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u w => G.Adj u w ∧ Keep G Θ π s(u, w)

instance (Θ : ℕ) (π : Fin n → Finset (Sym2 (Fin n))) : DecidableRel (reduced G Θ π).Adj :=
  fun u w => decidable_of_iff (u ≠ w ∧ ((G.Adj u w ∧ Keep G Θ π s(u, w)) ∨
    (G.Adj w u ∧ Keep G Θ π s(w, u)))) (by simp [reduced])

theorem reduced_adj {Θ : ℕ} {π : Fin n → Finset (Sym2 (Fin n))} {u w : Fin n} :
    (reduced G Θ π).Adj u w ↔ G.Adj u w ∧ Keep G Θ π s(u, w) := by
  simp only [reduced, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · rw [Sym2.eq_swap]; exact ⟨h.1.symm, h.2⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

variable {G}

theorem mem_edgeFinset_reduced {Θ : ℕ} {π : Fin n → Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)} :
    e ∈ (reduced G Θ π).edgeFinset ↔
      e ∈ G.edgeFinset ∧ ∀ v ∈ e, Θ < G.degree v → e ∈ π v := by
  induction e using Sym2.ind with
  | _ u w =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact reduced_adj G

theorem mem_choices {Θ : ℕ} {π : Fin n → Finset (Sym2 (Fin n))} :
    π ∈ choices G Θ ↔ ∀ v, if Θ < G.degree v then π v ⊆ incEdges G v ∧ (π v).card = 2
      else π v = ∅ := by
  simp only [choices, Fintype.mem_piFinset]
  refine forall_congr' fun v => ?_
  split_ifs <;> simp [mem_powersetCard]

variable (G)

/-- `G_π` is a subgraph of `G` on the same vertex set. -/
theorem reduced_le (Θ : ℕ) (π : Fin n → Finset (Sym2 (Fin n))) : reduced G Θ π ≤ G :=
  fun _ _ h => ((reduced_adj G).1 h).1

theorem edgeFinset_reduced_subset (Θ : ℕ) (π : Fin n → Finset (Sym2 (Fin n))) :
    (reduced G Θ π).edgeFinset ⊆ G.edgeFinset := fun _ he => (mem_edgeFinset_reduced.1 he).1

/-- `G_π` has at most `m` edges. -/
theorem card_edgeFinset_reduced_le (Θ : ℕ) (π : Fin n → Finset (Sym2 (Fin n))) :
    (reduced G Θ π).edgeFinset.card ≤ G.edgeFinset.card :=
  card_le_card (edgeFinset_reduced_subset G Θ π)

/-- For `Θ ≥ 2`, every `G_π` has maximum degree `≤ Θ`. -/
theorem degree_reduced_le {Θ : ℕ} (hΘ : 2 ≤ Θ) {π : Fin n → Finset (Sym2 (Fin n))}
    (hπ : π ∈ choices G Θ) (v : Fin n) : (reduced G Θ π).degree v ≤ Θ := by
  rw [← card_incEdges]
  have hv := mem_choices.1 hπ v
  split_ifs at hv with h
  · calc (incEdges (reduced G Θ π) v).card ≤ (π v).card := by
          apply card_le_card
          intro e he
          simp only [incEdges, mem_filter] at he
          exact (mem_edgeFinset_reduced.1 he.1).2 v he.2 h
      _ ≤ Θ := by omega
  · calc (incEdges (reduced G Θ π) v).card ≤ (incEdges G v).card := by
          apply card_le_card
          intro e he
          simp only [incEdges, mem_filter] at he ⊢
          exact ⟨edgeFinset_reduced_subset G Θ π he.1, he.2⟩
      _ ≤ Θ := by rw [card_incEdges]; omega

/-- The choice made by a Hamiltonian cycle: its two edges at each `v ∈ H`. -/
def cycleChoice (Θ : ℕ) (X : Finset (Sym2 (Fin n))) : Fin n → Finset (Sym2 (Fin n)) :=
  fun v => if Θ < G.degree v then X.filter fun e => v ∈ e else ∅

theorem mem_hamCycles_iff (X : Finset (Sym2 (Fin n))) :
    X ∈ hamCycles G ↔ X ⊆ G.edgeFinset ∧ TwoRegular X ∧ (graphOf X).Connected := by
  simp [hamCycles, twoFactors, and_assoc]

theorem cycleChoice_mem_choices (Θ : ℕ) {X : Finset (Sym2 (Fin n))} (hX : X ∈ hamCycles G) :
    cycleChoice G Θ X ∈ choices G Θ := by
  obtain ⟨hsub, hreg, -⟩ := (mem_hamCycles_iff G X).1 hX
  refine mem_choices.2 fun v => ?_
  simp only [cycleChoice]
  split_ifs
  · refine ⟨fun e he => ?_, hreg v⟩
    simp only [mem_filter, incEdges] at he ⊢
    exact ⟨hsub he.1, he.2⟩
  · rfl

/-- The Hamiltonian cycles of `G_π` are exactly the Hamiltonian cycles `C` of `G` with
`π(C) = π`. -/
theorem mem_hamCycles_reduced_iff {Θ : ℕ} {π : Fin n → Finset (Sym2 (Fin n))}
    (hπ : π ∈ choices G Θ) (X : Finset (Sym2 (Fin n))) :
    X ∈ hamCycles (reduced G Θ π) ↔ X ∈ hamCycles G ∧ cycleChoice G Θ X = π := by
  rw [mem_hamCycles_iff, mem_hamCycles_iff]
  constructor
  · rintro ⟨hsub, hreg, hcon⟩
    refine ⟨⟨hsub.trans (edgeFinset_reduced_subset G Θ π), hreg, hcon⟩, funext fun v => ?_⟩
    have hv := mem_choices.1 hπ v
    simp only [cycleChoice]
    split_ifs at hv ⊢ with h
    · refine eq_of_subset_of_card_le (fun e he => ?_) (by rw [hv.2, hreg v])
      rw [mem_filter] at he
      exact (mem_edgeFinset_reduced.1 (hsub he.1)).2 v he.2 h
    · exact hv.symm
  · rintro ⟨⟨hsub, hreg, hcon⟩, rfl⟩
    refine ⟨fun e he => mem_edgeFinset_reduced.2 ⟨hsub he, fun v hv h => ?_⟩, hreg, hcon⟩
    simp only [cycleChoice, h, ↓reduceIte, mem_filter]
    exact ⟨he, hv⟩

/-- **Lemma 6.1, counting identity.** `#HC(G) = Σ_π #HC(G_π)` (for every `Θ`). -/
theorem card_hamCycles_eq_sum_reduced (Θ : ℕ) :
    (hamCycles G).card = ∑ π ∈ choices G Θ, (hamCycles (reduced G Θ π)).card := by
  rw [card_eq_sum_card_fiberwise (f := cycleChoice G Θ) (t := choices G Θ)
    fun X hX => cycleChoice_mem_choices G Θ hX]
  refine sum_congr rfl fun π hπ => ?_
  congr 1
  ext X
  rw [mem_filter, mem_hamCycles_reduced_iff G hπ]

/-- **Lemma 6.1, number of branches.** `#choices = Π_{v ∈ H} C(deg v, 2)`. -/
theorem card_choices (Θ : ℕ) :
    (choices G Θ).card = ∏ v ∈ high G Θ, (G.degree v).choose 2 := by
  rw [choices, Fintype.card_piFinset, high, prod_filter]
  refine prod_congr rfl fun v _ => ?_
  split_ifs <;> simp [card_powersetCard, card_incEdges]

theorem card_choices_le (Θ : ℕ) : (choices G Θ).card ≤ n ^ (2 * (high G Θ).card) := by
  rw [card_choices, pow_mul]
  refine prod_le_pow_card _ _ _ fun v _ => ?_
  have h1 := G.degree_lt_card_verts v
  rw [Fintype.card_fin] at h1
  exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left h1.le 2)

/-- `|H| · Θ ≤ 2m`. -/
theorem card_high_mul_le (Θ : ℕ) : (high G Θ).card * Θ ≤ 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges, ← smul_eq_mul, ← sum_const]
  calc ∑ _v ∈ high G Θ, Θ ≤ ∑ v ∈ high G Θ, G.degree v :=
        sum_le_sum fun v hv => (mem_filter.1 hv).2.le
    _ ≤ ∑ v, G.degree v := sum_le_sum_of_subset (subset_univ _)

/-- `|H| · Θ < 2m` when `H ≠ ∅`, i.e. `|H| < 2m/Θ`. -/
theorem card_high_mul_lt (Θ : ℕ) (hH : (high G Θ).Nonempty) :
    (high G Θ).card * Θ < 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges, ← smul_eq_mul, ← sum_const]
  calc ∑ _v ∈ high G Θ, Θ < ∑ v ∈ high G Θ, G.degree v :=
        sum_lt_sum_of_nonempty hH fun v hv => (mem_filter.1 hv).2
    _ ≤ ∑ v, G.degree v := sum_le_sum_of_subset (subset_univ _)

end DegreeReduction

/-! ## Lemma 6.2: degree-balanced partition

First an abstract version for a weight sequence `w : ℕ → ℕ` on positions `0, …, n-1`. -/

section Partition

/-- `S_t = Σ_{s<t} w s`. -/
def prefixSum (w : ℕ → ℕ) (t : ℕ) : ℕ := ∑ s ∈ range t, w s

/-- The greedy blob index `min(g, ⌊g S_t / M⌋ + 1)`. -/
def blobIdx (g M : ℕ) (w : ℕ → ℕ) (t : ℕ) : ℕ := min g (g * prefixSum w t / M + 1)

theorem one_le_blobIdx {g : ℕ} (hg : 1 ≤ g) (M : ℕ) (w : ℕ → ℕ) (t : ℕ) :
    1 ≤ blobIdx g M w t := le_min hg (Nat.succ_pos _)

theorem blobIdx_le (g M : ℕ) (w : ℕ → ℕ) (t : ℕ) : blobIdx g M w t ≤ g := min_le_left _ _

theorem prefixSum_mono (w : ℕ → ℕ) {s t : ℕ} (h : s ≤ t) : prefixSum w s ≤ prefixSum w t :=
  sum_le_sum_of_subset (range_subset_range.2 h)

theorem blobIdx_mono (g M : ℕ) (w : ℕ → ℕ) {s t : ℕ} (h : s ≤ t) :
    blobIdx g M w s ≤ blobIdx g M w t :=
  min_le_min_left _ (Nat.succ_le_succ (Nat.div_le_div_right
    (Nat.mul_le_mul_left _ (prefixSum_mono w h))))

theorem prefixSum_add_sum_Ico (w : ℕ → ℕ) {s t : ℕ} (h : s ≤ t) :
    prefixSum w s + ∑ i ∈ Ico s t, w i = prefixSum w t :=
  sum_range_add_sum_Ico w h

/-- **Lemma 6.2, abstract form.** With `M = Σ_{t<n} w t` and `w t ≤ Δ` for `t < n`, every blob
`a` satisfies `g · Σ_{t<n, β t = a} w t ≤ M + g · Δ`. -/
theorem blob_sum_le (w : ℕ → ℕ) (n g Δ : ℕ) (hΔ : ∀ t < n, w t ≤ Δ) (a : ℕ) :
    g * ∑ t ∈ (range n).filter (fun t => blobIdx g (prefixSum w n) w t = a), w t ≤
      prefixSum w n + g * Δ := by
  set M := prefixSum w n with hMdef
  set T := (range n).filter (fun t => blobIdx g M w t = a) with hTdef
  have hTsub : T ⊆ range n := filter_subset _ _
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, sum_empty]; omega
  have hle : ∑ t ∈ T, w t ≤ M := sum_le_sum_of_subset hTsub
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · have : ∑ t ∈ T, w t = 0 := by omega
    rw [this]; omega
  set i0 := T.min' hT
  set i1 := T.max' hT
  have hi0 : i0 ∈ T := min'_mem T hT
  have hi1 : i1 ∈ T := max'_mem T hT
  have hb0 : blobIdx g M w i0 = a := (mem_filter.1 hi0).2
  have hb1 : blobIdx g M w i1 = a := (mem_filter.1 hi1).2
  have hi1n : i1 < n := mem_range.1 (hTsub hi1)
  have h01 : i0 ≤ i1 := min'_le T i1 hi1
  -- floor facts
  have hfl : ∀ t, g * prefixSum w t / M * M ≤ g * prefixSum w t := fun t => Nat.div_mul_le_self _ _
  have hcl : ∀ t, g * prefixSum w t < M * (g * prefixSum w t / M + 1) :=
    fun t => Nat.lt_mul_div_succ _ hMpos
  set S0 := prefixSum w i0
  set S1 := prefixSum w i1
  set q0 := g * S0 / M
  set q1 := g * S1 / M
  set X := ∑ t ∈ T, w t
  have hS01 : S0 ≤ S1 := prefixSum_mono w h01
  by_cases ha : a < g
  · -- a < g: both ends have `⌊g S/M⌋ + 1 = a`
    have e0 : q0 + 1 = a := by
      simp only [blobIdx, min_def] at hb0; split_ifs at hb0 <;> omega
    have e1 : q1 + 1 = a := by
      simp only [blobIdx, min_def] at hb1; split_ifs at hb1 <;> omega
    have hX : X + S0 ≤ S1 + w i1 := by
      have hsub : T ⊆ Ico i0 (i1 + 1) := fun t ht =>
        mem_Ico.2 ⟨min'_le T t ht, Nat.lt_succ_of_le (le_max' T t ht)⟩
      have h1 : X ≤ ∑ i ∈ Ico i0 (i1 + 1), w i := sum_le_sum_of_subset hsub
      have h2 : S0 + ∑ i ∈ Ico i0 (i1 + 1), w i = prefixSum w (i1 + 1) :=
        prefixSum_add_sum_Ico w (Nat.le_succ_of_le h01)
      have h3 : prefixSum w (i1 + 1) = S1 + w i1 := sum_range_succ w i1
      omega
    have hw1 : w i1 ≤ Δ := hΔ i1 hi1n
    have f0 : q0 * M ≤ g * S0 := hfl i0
    have c1 : g * S1 < M * (q1 + 1) := hcl i1
    have hq : q1 = q0 := by omega
    rw [hq] at c1
    have m1 : g * X + g * S0 ≤ g * S1 + g * Δ := by
      have := Nat.mul_le_mul_left g (hX.trans (Nat.add_le_add_left hw1 S1))
      simpa [mul_add] using this
    nlinarith
  · -- a = g: the last blob runs to the end
    have hag : a = g := le_antisymm (hb0 ▸ blobIdx_le _ _ _ _) (not_lt.1 ha)
    have e0 : g ≤ q0 + 1 := by
      simp only [blobIdx, min_def] at hb0; split_ifs at hb0 <;> omega
    have hX : X + S0 ≤ M := by
      have hsub : T ⊆ Ico i0 n := fun t ht =>
        mem_Ico.2 ⟨min'_le T t ht, mem_range.1 (hTsub ht)⟩
      have h1 : X ≤ ∑ i ∈ Ico i0 n, w i := sum_le_sum_of_subset hsub
      have h2 : S0 + ∑ i ∈ Ico i0 n, w i = M := prefixSum_add_sum_Ico w (h01.trans hi1n.le)
      omega
    have f0 : q0 * M ≤ g * S0 := hfl i0
    have m1 : g * X + g * S0 ≤ g * M := by
      have := Nat.mul_le_mul_left g hX
      simpa [mul_add] using this
    have m2 : g * M ≤ q0 * M + M := by
      have := Nat.mul_le_mul_right M e0
      simpa [add_mul] using this
    have : g * X ≤ M := by omega
    exact this.trans (Nat.le_add_right _ _)

/-! ### The graph version -/

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Degrees listed in the order `σ`: `w t = deg (σ t)` for `t < n`, and `0` beyond. -/
def degSeq (σ : Fin n ≃ Fin n) (t : ℕ) : ℕ := if h : t < n then G.degree (σ ⟨t, h⟩) else 0

/-- **Lemma 6.2, the partition.** `β(v_t) = min(g, ⌊g S_t / (2m)⌋ + 1)` where `v_t = σ t`. -/
def balancedPartition (g : ℕ) (σ : Fin n ≃ Fin n) (v : Fin n) : ℕ :=
  blobIdx g (2 * G.edgeFinset.card) (degSeq G σ) (σ.symm v : ℕ)

/-- The degree sum `μ_a` of blob `a`. -/
def blobDegreeSum (β : Fin n → ℕ) (a : ℕ) : ℕ := ∑ v ∈ univ.filter (fun v => β v = a), G.degree v

theorem balancedPartition_mem (g : ℕ) (hg : 1 ≤ g) (σ : Fin n ≃ Fin n) (v : Fin n) :
    1 ≤ balancedPartition G g σ v ∧ balancedPartition G g σ v ≤ g :=
  ⟨one_le_blobIdx hg _ _ _, blobIdx_le _ _ _ _⟩

theorem prefixSum_degSeq (σ : Fin n ≃ Fin n) :
    prefixSum (degSeq G σ) n = 2 * G.edgeFinset.card := by
  rw [prefixSum, ← G.sum_degrees_eq_twice_card_edges, ← Fin.sum_univ_eq_sum_range,
    ← Equiv.sum_comp σ (fun v => G.degree v)]
  refine sum_congr rfl fun i _ => ?_
  simp [degSeq]

/-- **Lemma 6.2.** Every blob of `balancedPartition` has `g · μ_a ≤ 2m + g · Δ`. -/
theorem blob_degree_sum_le (g : ℕ) (σ : Fin n ≃ Fin n) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (a : ℕ) :
    g * blobDegreeSum G (balancedPartition G g σ) a ≤ 2 * G.edgeFinset.card + g * Δ := by
  have key := blob_sum_le (degSeq G σ) n g Δ
    (fun t ht => by simp only [degSeq, ht, ↓reduceDIte]; exact hΔ _) a
  rw [prefixSum_degSeq] at key
  convert key using 2
  rw [blobDegreeSum, sum_filter, sum_filter, ← Fin.sum_univ_eq_sum_range, ← Equiv.sum_comp σ]
  refine sum_congr rfl fun i _ => ?_
  simp [balancedPartition, degSeq]

/-- **Lemma 6.2**, as stated: `μ_a ≤ 2m/g + Δ`. -/
theorem blob_degree_sum_le_rat (g : ℕ) (hg : 1 ≤ g) (σ : Fin n ≃ Fin n) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (a : ℕ) :
    (blobDegreeSum G (balancedPartition G g σ) a : ℚ) ≤
      (2 * G.edgeFinset.card : ℚ) / g + Δ := by
  have h := blob_degree_sum_le G g σ hΔ a
  have hg' : (0 : ℚ) < g := by exact_mod_cast hg
  rw [div_add' _ _ _ hg'.ne', le_div_iff₀ hg']
  have : ((g * blobDegreeSum G (balancedPartition G g σ) a : ℕ) : ℚ) ≤
      ((2 * G.edgeFinset.card + g * Δ : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at this
  linarith

/-- **Lemma 6.2**, existence form with blobs indexed by `Fin g`. -/
theorem exists_balanced_partition (g : ℕ) (hg : 1 ≤ g) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ β : Fin n → Fin g, ∀ a : Fin g,
      g * ∑ v ∈ univ.filter (fun v => β v = a), G.degree v ≤ 2 * G.edgeFinset.card + g * Δ := by
  have hβ₀ := balancedPartition_mem G g hg (Equiv.refl _)
  refine ⟨fun v => ⟨balancedPartition G g (Equiv.refl _) v - 1, by have := hβ₀ v; omega⟩,
    fun a => ?_⟩
  have key := blob_degree_sum_le G g (Equiv.refl _) hΔ (a + 1)
  refine (le_of_eq ?_).trans key
  rw [blobDegreeSum]
  congr 2
  ext v
  simp only [Fin.ext_iff, mem_filter, mem_univ, true_and]
  have := hβ₀ v
  constructor <;> intro h <;> omega

end Partition

end EthFollowup.ExactHC
