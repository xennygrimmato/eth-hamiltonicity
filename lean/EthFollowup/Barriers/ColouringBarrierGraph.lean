/-
# The colouring barrier, graph level (paper `prop:colouring-barrier`)

Source (paper/main.tex, `\label{prop:colouring-barrier}`):

> Work over a field of characteristic `0`. Suppose that weights `z_0,…,z_{q-1}` on `q` colours,
> with the root coloured `0` and every component `C ∌ r` of a `2`-factor contributing
> `h(C) = ∑_j z_j^{|C|}`, give a sum equal to `HC(G)` up to a nonzero factor, for every graph `G`
> on `n` vertices. Then `q ≥ n-4`.

(`hamiltonicity.md` §8 describes the same filter as the colouring sum
`Σ_{c consistent} Π_v z_{c_v}`, which "componentwise" gives `Π_{C ∌ r} h(C)`.)

## The model

Graphs are `G : SimpleGraph (Fin n)`; 2-factors and Hamiltonian cycles are
`EthFollowup.Hamiltonian.twoFactors G` / `hamCycles G` (spanning 2-regular edge sets; connected
ones). For a 2-factor `X` with components `C` of `graphOf X` (`C_r` the root's):

* `compValue z r c₀ X = z_{c₀}^{|C_r|} · Π_{C ≠ C_r} h(|C|)`, `h(m) = Σ_j z_j^m` — the paper's
  description (root coloured `c₀ = 0`, so the root's component contributes `z_0^{|C_r|}`);
* `colourSum z r c₀ X = Σ_{c : V → [q], every edge of X monochromatic, c(r) = c₀} Π_v z_{c(v)}`
  — the colouring sum of §8. `colourSum_eq_compValue` proves the two agree.

`ExactFilter z r c₀`: for every graph `G` on `Fin n` there is `μ ≠ 0` with
`Σ_{X ∈ 2F(G)} compValue z r c₀ X = μ · #HC(G)` (the factor may depend on `G`).

## Results

* `colouring_barrier_graph` — **`prop:colouring-barrier` as stated**: in characteristic `0`,
  `ExactFilter z r 0` implies `n ≤ q + 4`. The proof follows the paper: `z_0 ≠ 0` from the
  `n`-cycle (one 2-factor, Hamiltonian), and `Σ_j z_j^k = 0` for `3 ≤ k ≤ n − 3` from
  `C_{n−k} ⊔ C_k` (one 2-factor, disconnected, value `z_0^{n−k} Σ_j z_j^k`), then
  `Colouring.colouring_barrier`.
* `colouring_barrier_graph_colourings` — the same for the colouring-sum model of §8.
-/
import EthFollowup.HamiltonianParity
import EthFollowup.Barriers.ColouringBarrier

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.ColouringGraph

open Finset EthFollowup.Hamiltonian

variable {n : ℕ} {K : Type*} [Field K]

/-! ### The filter model -/

/-- Every edge of `X` is monochromatic under `c : V → [q]`. -/
def ConsistentQ {q : ℕ} (X : Finset (Sym2 (Fin n))) (c : Fin n → Fin q) : Prop :=
  ∀ u w : Fin n, s(u, w) ∈ X → c u = c w

instance {q : ℕ} (X : Finset (Sym2 (Fin n))) (c : Fin n → Fin q) : Decidable (ConsistentQ X c) := by
  unfold ConsistentQ; infer_instance

/-- The colouring sum of `hamiltonicity.md` §8 for one 2-factor `X`. -/
def colourSum {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q) (X : Finset (Sym2 (Fin n))) : K :=
  ∑ c ∈ univ.filter (fun c : Fin n → Fin q => ConsistentQ X c ∧ c r = c₀), ∏ v, z (c v)

/-- `h(m) = Σ_j z_j^m`, the contribution of a non-root cycle with `m` vertices. -/
def hWeight {q : ℕ} (z : Fin q → K) (m : ℕ) : K := ∑ j, z j ^ m

open Classical in
/-- Number of vertices of a component of `graphOf X`. -/
noncomputable def compSize (X : Finset (Sym2 (Fin n))) (C : (graphOf X).ConnectedComponent) : ℕ :=
  #(univ.filter fun v => (graphOf X).connectedComponentMk v = C)

open Classical in
/-- The paper's contribution of a 2-factor: `z_{c₀}^{|C_r|} · Π_{C ∌ r} h(|C|)`. -/
noncomputable def compValue {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q)
    (X : Finset (Sym2 (Fin n))) : K :=
  z c₀ ^ compSize X ((graphOf X).connectedComponentMk r) *
    ∏ C ∈ univ.erase ((graphOf X).connectedComponentMk r), hWeight z (compSize X C)

/-- The filter value of `G`: the sum over its 2-factors. -/
noncomputable def filterValue {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : K :=
  ∑ X ∈ twoFactors G, compValue z r c₀ X

/-- The hypothesis of `prop:colouring-barrier`: the filter gives `#HC(G)` up to a nonzero factor,
for every graph `G` on `n` vertices. -/
def ExactFilter {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ∃ μ : K, μ ≠ 0 ∧ filterValue z r c₀ G = μ * (hamCycles G).card

/-- The same hypothesis for the colouring-sum model of `hamiltonicity.md` §8. -/
def ExactColouringFilter {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ∃ μ : K, μ ≠ 0 ∧ ∑ X ∈ twoFactors G, colourSum z r c₀ X = μ * (hamCycles G).card

/-! ### Colouring sum = product over components -/

/-- Sum over maps with one value pinned of a product. -/
theorem sum_pinned_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} (g : ι → Fin q → K)
    (i₀ : ι) (j₀ : Fin q) :
    ∑ c ∈ univ.filter (fun c : ι → Fin q => c i₀ = j₀), ∏ i, g i (c i) =
      g i₀ j₀ * ∏ i ∈ univ.erase i₀, ∑ j, g i j := by
  let F : ι → Fin q → K := fun i j => if i = i₀ then (if j = j₀ then g i j else 0) else g i j
  have h1 : ∏ i, ∑ j, F i j = g i₀ j₀ * ∏ i ∈ univ.erase i₀, ∑ j, g i j := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ i₀)]
    congr 1
    · simp [F]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [F, Finset.ne_of_mem_erase hi]
  rw [← h1, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = i₀
    · subst hi; simp [F, hc]
    · simp [F, hi]
  · symm
    exact Finset.prod_eq_zero (mem_univ i₀) (by simp [F, hc])

theorem consistentQ_iff_reachable {q : ℕ} (X : Finset (Sym2 (Fin n))) (c : Fin n → Fin q) :
    ConsistentQ X c ↔ ∀ u w, (graphOf X).Reachable u w → c u = c w := by
  constructor
  · intro hc u w ⟨p⟩
    induction p with
    | nil => rfl
    | cons hadj _ ih =>
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      exact (hc _ _ hadj.1).trans ih
  · intro h u w hmem
    by_cases huw : u = w
    · rw [huw]
    · exact h u w (SimpleGraph.Adj.reachable (by
        rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨hmem, huw⟩))

/-- The colouring sum of a 2-factor equals the paper's product over its components. -/
theorem colourSum_eq_compValue {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q)
    (X : Finset (Sym2 (Fin n))) : colourSum z r c₀ X = compValue z r c₀ X := by
  classical
  set H := graphOf X
  let mk := H.connectedComponentMk
  have hout : ∀ C : H.ConnectedComponent, mk (Quot.out C) = C := fun C => Quot.out_eq C
  -- step 1: colourings consistent with `X` = colourings of the components
  have step1 : colourSum z r c₀ X =
      ∑ c' ∈ univ.filter (fun c' : H.ConnectedComponent → Fin q => c' (mk r) = c₀),
        ∏ v, z (c' (mk v)) := by
    unfold colourSum
    refine Finset.sum_nbij' (fun c C => c (Quot.out C)) (fun c' v => c' (mk v)) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      rw [← hc.2]
      exact ((consistentQ_iff_reachable X c).1 hc.1 _ _
        (SimpleGraph.ConnectedComponent.exact (hout (mk r))))
    · intro c' hc'
      simp only [mem_filter, mem_univ, true_and] at hc' ⊢
      refine ⟨(consistentQ_iff_reachable X _).2 fun u w huw => ?_, hc'⟩
      exact congrArg c' (SimpleGraph.ConnectedComponent.sound huw)
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc
      funext v
      exact (consistentQ_iff_reachable X c).1 hc.1 _ _
        (SimpleGraph.ConnectedComponent.exact (hout (mk v)))
    · intro c' _
      funext C
      simp only
      rw [hout]
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc
      refine Finset.prod_congr rfl fun v _ => ?_
      exact congrArg z ((consistentQ_iff_reachable X c).1 hc.1 _ _
        (SimpleGraph.ConnectedComponent.exact (hout (mk v)))).symm
  -- step 2: group the product by components
  have step2 : ∀ c' : H.ConnectedComponent → Fin q,
      ∏ v, z (c' (mk v)) = ∏ C, z (c' C) ^ compSize X C := by
    intro c'
    rw [← Finset.prod_fiberwise univ mk (fun v => z (c' (mk v)))]
    refine Finset.prod_congr rfl fun C _ => ?_
    rw [Finset.prod_congr rfl fun v hv => by rw [(mem_filter.1 hv).2], Finset.prod_const]
    unfold compSize
    congr
  rw [step1, Finset.sum_congr rfl fun c' _ => step2 c',
    sum_pinned_prod (fun C j => z j ^ compSize X C) (mk r) c₀]
  unfold compValue hWeight
  congr 1

theorem filterValue_eq_colourSum {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    filterValue z r c₀ G = ∑ X ∈ twoFactors G, colourSum z r c₀ X := by
  unfold filterValue
  exact Finset.sum_congr rfl fun X _ => (colourSum_eq_compValue z r c₀ X).symm

theorem exactFilter_iff {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q) :
    ExactFilter z r c₀ ↔ ExactColouringFilter z r c₀ := by
  unfold ExactFilter ExactColouringFilter
  simp only [filterValue_eq_colourSum]

/-! ### Graphs given by a fixed-point-free permutation: disjoint unions of cycles -/

section PermGraph

variable (σ : Equiv.Perm (Fin n))

/-- The edge set `{v σ(v)}`; for `σ` without fixed points or 2-cycles this is a disjoint union of
the cycles of `σ`. -/
def cycEdges : Finset (Sym2 (Fin n)) := univ.image fun v => s(v, σ v)

theorem mem_cycEdges {e : Sym2 (Fin n)} : e ∈ cycEdges σ ↔ ∃ v, s(v, σ v) = e := by
  simp [cycEdges]

variable {σ}

theorem twoRegular_cycEdges (h1 : ∀ v, σ v ≠ v) (h2 : ∀ v, σ (σ v) ≠ v) :
    TwoRegular (cycEdges σ) := by
  intro v
  have hfil : (cycEdges σ).filter (fun e => v ∈ e) = {s(v, σ v), s(σ.symm v, v)} := by
    ext e
    simp only [mem_filter, mem_cycEdges, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨u, rfl⟩, hv⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact Or.inl rfl
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨⟨v, rfl⟩, Sym2.mem_mk_left _ _⟩
      · exact ⟨⟨σ.symm v, by simp⟩, Sym2.mem_mk_right _ _⟩
  rw [hfil, Finset.card_pair]
  intro heq
  rcases Sym2.eq_iff.1 heq with ⟨h, h'⟩ | ⟨_, h'⟩
  · exact h1 v h'
  · apply h2 v
    rw [h', Equiv.apply_symm_apply]

theorem not_isDiag_cycEdges (h1 : ∀ v, σ v ≠ v) {e : Sym2 (Fin n)} (he : e ∈ cycEdges σ) :
    ¬ e.IsDiag := by
  obtain ⟨v, rfl⟩ := (mem_cycEdges σ).1 he
  simpa [Sym2.mk_isDiag_iff] using (h1 v).symm

theorem twoFactors_cycEdges (h1 : ∀ v, σ v ≠ v) (h2 : ∀ v, σ (σ v) ≠ v) :
    twoFactors (graphOf (cycEdges σ)) = {cycEdges σ} := by
  ext X
  simp only [twoFactors, mem_filter, mem_powerset, mem_singleton, Finset.subset_iff,
    SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe]
  constructor
  · rintro ⟨hsub', hreg⟩
    have hsub : X ⊆ cycEdges σ := fun e he => (hsub' he).1
    refine Finset.Subset.antisymm hsub fun e he => ?_
    obtain ⟨v, rfl⟩ := (mem_cycEdges σ).1 he
    have hle : X.filter (fun e => v ∈ e) ⊆ (cycEdges σ).filter (fun e => v ∈ e) :=
      Finset.filter_subset_filter _ hsub
    have heq := Finset.eq_of_subset_of_card_le hle
      (by rw [hreg v, twoRegular_cycEdges h1 h2 v])
    have : s(v, σ v) ∈ (cycEdges σ).filter (fun e => v ∈ e) :=
      mem_filter.2 ⟨he, Sym2.mem_mk_left _ _⟩
    rw [← heq] at this
    exact (mem_filter.1 this).1
  · rintro rfl
    exact ⟨fun e he => ⟨he, not_isDiag_cycEdges h1 he⟩, twoRegular_cycEdges h1 h2⟩

theorem adj_cycEdges {u w : Fin n} (h : (graphOf (cycEdges σ)).Adj u w) : w = σ u ∨ u = σ w := by
  rw [SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨v, hv⟩ := (mem_cycEdges σ).1 h.1
  rcases Sym2.eq_iff.1 hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem adj_cycEdges_self (h1 : ∀ v, σ v ≠ v) (v : Fin n) :
    (graphOf (cycEdges σ)).Adj v (σ v) := by
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨(mem_cycEdges σ).2 ⟨v, rfl⟩, (h1 v).symm⟩

theorem consistentQ_cycEdges {q : ℕ} (c : Fin n → Fin q) :
    ConsistentQ (cycEdges σ) c ↔ ∀ v, c (σ v) = c v := by
  constructor
  · intro hc v; exact (hc v (σ v) ((mem_cycEdges σ).2 ⟨v, rfl⟩)).symm
  · intro hc u w hmem
    obtain ⟨v, hv⟩ := (mem_cycEdges σ).1 hmem
    rcases Sym2.eq_iff.1 hv with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]; exact (hc v).symm
    · rw [← e1, ← e2]; exact hc v

theorem pow_invariant {q : ℕ} {c : Fin n → Fin q} (hc : ∀ v, c (σ v) = c v) (j : ℕ) (x : Fin n) :
    c ((σ ^ j) x) = c x := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Equiv.Perm.mul_apply, hc, ih]

/-- An invariant set `A` with `r ∈ A`, `b ∉ A` disconnects the cycle graph. -/
theorem not_connected_cycEdges (A : Finset (Fin n)) (hA : ∀ v, σ v ∈ A ↔ v ∈ A) {r b : Fin n}
    (hr : r ∈ A) (hb : b ∉ A) : ¬ (graphOf (cycEdges σ)).Connected := by
  intro hconn
  obtain ⟨p⟩ := hconn.preconnected r b
  have key : ∀ {u w : Fin n} (p : (graphOf (cycEdges σ)).Walk u w), u ∈ A → w ∈ A := by
    intro u w p
    induction p with
    | nil => exact id
    | cons hadj _ ih =>
      intro hu
      apply ih
      rcases adj_cycEdges hadj with rfl | rfl
      · exact (hA _).2 hu
      · exact (hA _).1 hu
  exact hb (key p hr)

/-- If every vertex is `σ^j r`, the cycle graph is connected. -/
theorem connected_cycEdges (h1 : ∀ v, σ v ≠ v) (r : Fin n) (hreach : ∀ w, ∃ j : ℕ, (σ ^ j) r = w) :
    (graphOf (cycEdges σ)).Connected := by
  have hr : ∀ j : ℕ, (graphOf (cycEdges σ)).Reachable r ((σ ^ j) r) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (adj_cycEdges_self h1 _).reachable
  have hall : ∀ w, (graphOf (cycEdges σ)).Reachable r w := fun w => by
    obtain ⟨j, rfl⟩ := hreach w; exact hr j
  rw [SimpleGraph.connected_iff]
  exact ⟨fun u w => (hall u).symm.trans (hall w), ⟨r⟩⟩

/-- The colouring sum of a single cycle through `r`: only the constant colouring survives. -/
theorem colourSum_one_orbit {q : ℕ} (z : Fin q → K) (r : Fin n) (c₀ : Fin q)
    (hreach : ∀ w, ∃ j : ℕ, (σ ^ j) r = w) : colourSum z r c₀ (cycEdges σ) = z c₀ ^ n := by
  unfold colourSum
  have : univ.filter (fun c : Fin n → Fin q => ConsistentQ (cycEdges σ) c ∧ c r = c₀) =
      {fun _ => c₀} := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_singleton, consistentQ_cycEdges]
    constructor
    · rintro ⟨hc, hcr⟩
      funext w
      obtain ⟨j, rfl⟩ := hreach w
      rw [pow_invariant hc, hcr]
    · rintro rfl; exact ⟨fun _ => rfl, rfl⟩
  rw [this, Finset.sum_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The colouring sum of two cycles `A ∋ r` and `Aᶜ ∋ b`: `z_{c₀}^{|A|} · Σ_j z_j^{n − |A|}`. -/
theorem colourSum_two_orbits {q : ℕ} (z : Fin q → K) (c₀ : Fin q) (A : Finset (Fin n))
    (hA : ∀ v, σ v ∈ A ↔ v ∈ A) {r b : Fin n} (hr : r ∈ A) (hb : b ∉ A)
    (hreachA : ∀ w ∈ A, ∃ j : ℕ, (σ ^ j) r = w) (hreachB : ∀ w ∉ A, ∃ j : ℕ, (σ ^ j) b = w) :
    colourSum z r c₀ (cycEdges σ) = z c₀ ^ A.card * ∑ j, z j ^ (n - A.card) := by
  unfold colourSum
  let col : Fin q → Fin n → Fin q := fun j v => if v ∈ A then c₀ else j
  have hinj : Function.Injective col := fun j j' h => by
    have := congrFun h b; simpa [col, hb] using this
  have hset : univ.filter (fun c : Fin n → Fin q => ConsistentQ (cycEdges σ) c ∧ c r = c₀) =
      univ.image col := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_image, consistentQ_cycEdges]
    constructor
    · rintro ⟨hc, hcr⟩
      refine ⟨c b, funext fun w => ?_⟩
      by_cases hw : w ∈ A
      · obtain ⟨j, rfl⟩ := hreachA w hw
        simp only [col, hw, ite_true]; rw [pow_invariant hc, hcr]
      · obtain ⟨j, rfl⟩ := hreachB w hw
        simp only [col, hw, ite_false]; rw [pow_invariant hc]
    · rintro ⟨j, rfl⟩
      refine ⟨fun v => ?_, by simp [col, hr]⟩
      simp only [col, hA]
  rw [hset, Finset.sum_image fun j _ j' _ h => hinj h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [col, apply_ite z]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  · congr 1; ext v; simp
  · rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin]
    congr 2; ext v; simp

end PermGraph

/-! ### The concrete graphs `C_n` and `C_{n−k} ⊔ C_k` -/

section Concrete

/-- Successor in the cycles `(0 1 … m−1)` and `(m m+1 … n−1)`. -/
def blockSucc (m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) (i : Fin n) : Fin n :=
  ⟨if i.val + 1 = m then 0 else if i.val + 1 = n then m else i.val + 1, by
    have := i.isLt; split_ifs <;> omega⟩

/-- Predecessor in the same cycles. -/
def blockPred (m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) (i : Fin n) : Fin n :=
  ⟨if i.val = 0 then m - 1 else if i.val = m then n - 1 else i.val - 1, by
    have := i.isLt; split_ifs <;> omega⟩

theorem blockPred_succ (m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) (i : Fin n) :
    blockPred m hm hmn (blockSucc m hm hmn i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [blockPred, blockSucc]
  split_ifs <;> first | omega | simp_all

theorem blockSucc_pred (m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) (i : Fin n) :
    blockSucc m hm hmn (blockPred m hm hmn i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [blockPred, blockSucc]
  split_ifs <;> omega

/-- The permutation with cycles `(0 1 … m−1)` and `(m m+1 … n−1)` (only the first if `m = n`). -/
def blockPerm (m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) : Equiv.Perm (Fin n) where
  toFun := blockSucc m hm hmn
  invFun := blockPred m hm hmn
  left_inv := blockPred_succ m hm hmn
  right_inv := blockSucc_pred m hm hmn

theorem blockPerm_val (m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) (i : Fin n) :
    (blockPerm m hm hmn i).val = if i.val + 1 = m then 0 else if i.val + 1 = n then m else i.val + 1 :=
  rfl

variable {m : ℕ} {hm : 3 ≤ m} {hmn : m ≤ n}

theorem blockPerm_ne (hk : n = m ∨ m + 3 ≤ n) (v : Fin n) : blockPerm m hm hmn v ≠ v := by
  intro h
  have h' := congrArg Fin.val h
  rw [blockPerm_val] at h'
  have hv := v.isLt
  split_ifs at h' <;> omega

theorem blockPerm_ne2 (hk : n = m ∨ m + 3 ≤ n) (v : Fin n) :
    blockPerm m hm hmn (blockPerm m hm hmn v) ≠ v := by
  intro h
  have h' := congrArg Fin.val h
  rw [blockPerm_val, blockPerm_val] at h'
  have hv := v.isLt
  split_ifs at h' <;> omega

theorem blockPerm_lt_iff (v : Fin n) : (blockPerm m hm hmn v).val < m ↔ v.val < m := by
  rw [blockPerm_val]
  have := v.isLt
  split_ifs <;> omega

theorem blockPerm_pow_zero (h0 : 0 < n) (j : ℕ) (hj : j < m) :
    ((blockPerm m hm hmn ^ j) ⟨0, h0⟩).val = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, blockPerm_val, ih (by omega)]
    split_ifs <;> omega

theorem blockPerm_pow_m (hmn' : m < n) (j : ℕ) (hj : m + j < n) :
    ((blockPerm m hm hmn ^ j) ⟨m, hmn'⟩).val = m + j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, blockPerm_val, ih (by omega)]
    split_ifs <;> omega

/-- Conjugating by an involution `e`. -/
def conjBy (e σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := (e.trans σ).trans e

theorem conjBy_apply (e σ : Equiv.Perm (Fin n)) (v : Fin n) : conjBy e σ v = e (σ (e v)) := rfl

theorem conjBy_pow {e : Equiv.Perm (Fin n)} (he : ∀ x, e (e x) = x) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (v : Fin n) : (conjBy e σ ^ j) v = e ((σ ^ j) (e v)) := by
  induction j with
  | zero => simp [he]
  | succ j ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, conjBy_apply, he, pow_succ',
      Equiv.Perm.mul_apply]

end Concrete

/-! ### `prop:colouring-barrier` -/

theorem hamCycles_card_of_twoFactors {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {E : Finset (Sym2 (Fin n))} (h : twoFactors G = {E}) :
    (hamCycles G).card = if (graphOf E).Connected then 1 else 0 := by
  unfold hamCycles
  rw [h, Finset.filter_singleton]
  split_ifs <;> simp

/-- **`prop:colouring-barrier`** (paper), graph level: over a field of characteristic `0`, if the
weights `z_0, …, z_{q−1}` with the root `r` coloured `0` give an exact filter for `#HC` on every
graph on `n` vertices (`ExactFilter`), then `q ≥ n − 4`. -/
theorem colouring_barrier_graph [CharZero K] {q : ℕ} (hq : 0 < q) (z : Fin q → K) (r : Fin n)
    (hex : ExactFilter z r ⟨0, hq⟩) : n ≤ q + 4 := by
  classical
  by_cases hn3 : n < 3
  · omega
  push Not at hn3
  have h0 : 0 < n := by omega
  let o : Fin n := ⟨0, h0⟩
  let e : Equiv.Perm (Fin n) := Equiv.swap o r
  have he : ∀ x, e (e x) = x := fun x => Equiv.swap_apply_self _ _ _
  have her : e r = o := Equiv.swap_apply_right _ _
  -- the value of the filter on the cycle graph of a conjugated block permutation
  have hval : ∀ (m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) (hk : n = m ∨ m + 3 ≤ n),
      let σ := conjBy e (blockPerm m hm hmn)
      (∀ v, σ v ≠ v) ∧ (∀ v, σ (σ v) ≠ v) ∧
        filterValue z r ⟨0, hq⟩ (graphOf (cycEdges σ)) = colourSum z r ⟨0, hq⟩ (cycEdges σ) := by
    intro m hm hmn hk σ
    have h1 : ∀ v, σ v ≠ v := fun v h => blockPerm_ne (hm := hm) (hmn := hmn) hk (e v) (by
      have := congrArg e h; rwa [conjBy_apply, he] at this)
    have h2 : ∀ v, σ (σ v) ≠ v := fun v h => blockPerm_ne2 (hm := hm) (hmn := hmn) hk (e v) (by
      have := congrArg e h; rwa [conjBy_apply, conjBy_apply, he, he] at this)
    refine ⟨h1, h2, ?_⟩
    rw [filterValue, twoFactors_cycEdges h1 h2, Finset.sum_singleton, colourSum_eq_compValue]
  -- `z_0 ≠ 0`, from the `n`-cycle
  have hz0 : z ⟨0, hq⟩ ≠ 0 := by
    obtain ⟨h1, h2, hv⟩ := hval n hn3 le_rfl (Or.inl rfl)
    set σ := conjBy e (blockPerm n hn3 le_rfl)
    have hreach : ∀ w, ∃ j : ℕ, (σ ^ j) r = w := by
      intro w
      refine ⟨(e w).val, ?_⟩
      rw [conjBy_pow he, her]
      have : (blockPerm n hn3 le_rfl ^ (e w).val) o = e w :=
        Fin.ext (blockPerm_pow_zero h0 _ (e w).isLt)
      rw [this, he]
    obtain ⟨μ, hμ, hμeq⟩ := hex (graphOf (cycEdges σ))
    rw [hv, colourSum_one_orbit z r _ hreach,
      hamCycles_card_of_twoFactors (twoFactors_cycEdges h1 h2),
      ite_eq_left (connected_cycEdges h1 r hreach)] at hμeq
    intro hz
    rw [hz, zero_pow (by omega)] at hμeq
    simp at hμeq
    exact hμ hμeq.symm
  -- `Σ_j z_j^k = 0` for `3 ≤ k ≤ n − 3`, from `C_{n−k} ⊔ C_k`
  have hvan : ∀ k, 3 ≤ k → k + 3 ≤ n → ∑ j, z j ^ k = 0 := by
    intro k hk1 hk2
    have hm : 3 ≤ n - k := by omega
    have hmn : n - k ≤ n := by omega
    have hmn' : n - k < n := by omega
    obtain ⟨h1, h2, hv⟩ := hval (n - k) hm hmn (Or.inr (by omega))
    set σ := conjBy e (blockPerm (n - k) hm hmn)
    let A : Finset (Fin n) := univ.filter fun v => (e v).val < n - k
    let b : Fin n := e ⟨n - k, hmn'⟩
    have hA : ∀ v, σ v ∈ A ↔ v ∈ A := by
      intro v
      simp only [A, mem_filter, mem_univ, true_and]
      rw [show σ v = e (blockPerm (n - k) hm hmn (e v)) from rfl, he]
      exact blockPerm_lt_iff _
    have hrA : r ∈ A := by simp [A, her, o]; omega
    have hbA : b ∉ A := by simp [A, b, he]
    have hreachA : ∀ w ∈ A, ∃ j : ℕ, (σ ^ j) r = w := by
      intro w hw
      have hw' : (e w).val < n - k := by simpa [A] using hw
      refine ⟨(e w).val, ?_⟩
      rw [conjBy_pow he, her]
      have : (blockPerm (n - k) hm hmn ^ (e w).val) o = e w :=
        Fin.ext (blockPerm_pow_zero h0 _ hw')
      rw [this, he]
    have hreachB : ∀ w ∉ A, ∃ j : ℕ, (σ ^ j) b = w := by
      intro w hw
      have hw' : n - k ≤ (e w).val := by simpa [A] using hw
      refine ⟨(e w).val - (n - k), ?_⟩
      rw [conjBy_pow he]
      simp only [b, he]
      have : (blockPerm (n - k) hm hmn ^ ((e w).val - (n - k))) ⟨n - k, hmn'⟩ = e w :=
        Fin.ext (by rw [blockPerm_pow_m hmn' _ (by have := (e w).isLt; omega)]; omega)
      rw [this, he]
    have hcardA : A.card = n - k := by
      have : A = (univ.filter fun v : Fin n => v.val < n - k).map e.toEmbedding := by
        ext v
        simp only [A, mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
        exact ⟨fun h => ⟨e v, h, he v⟩, fun ⟨u, hu, huv⟩ => by rw [← huv, he]; exact hu⟩
      rw [this, Finset.card_map, Fin.card_filter_val_lt]
      omega
    obtain ⟨μ, hμ, hμeq⟩ := hex (graphOf (cycEdges σ))
    rw [hv, colourSum_two_orbits z _ A hA hrA hbA hreachA hreachB,
      hamCycles_card_of_twoFactors (twoFactors_cycEdges h1 h2),
      ite_eq_right (not_connected_cycEdges A hA hrA hbA), hcardA,
      show n - (n - k) = k by omega] at hμeq
    simp only [Nat.cast_zero, mul_zero, mul_eq_zero] at hμeq
    exact hμeq.resolve_left (pow_ne_zero _ hz0)
  exact Colouring.colouring_barrier z ⟨0, hq⟩ hz0 hvan

/-- The same for the colouring-sum model of `hamiltonicity.md` §8. -/
theorem colouring_barrier_graph_colourings [CharZero K] {q : ℕ} (hq : 0 < q) (z : Fin q → K)
    (r : Fin n) (hex : ExactColouringFilter z r ⟨0, hq⟩) : n ≤ q + 4 :=
  colouring_barrier_graph hq z r ((exactFilter_iff z r _).2 hex)

end EthFollowup.Barriers.ColouringGraph
