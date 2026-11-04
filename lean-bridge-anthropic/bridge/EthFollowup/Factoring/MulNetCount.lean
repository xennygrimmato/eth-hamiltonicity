/-
# Factoring, module F2 (part 3): the counts of the multiplication network

`scratchpad/plans/factoring-plan.md` §2 (clusters), §3 (U, P, B); interface `facM-interface.md` (F2).

* `endsAt n v`: the wire indices with an end at `v`; `card_endsAt_le`: at most `degSt n v.stage`
  (`1` for cells, `ℓ1 + L1` for rows, `ℓ2 + L2` for columns, `3` for products, `2 L2`, `2 L1` for the
  inverse transforms, `4` for carries).
* `g_mul_card_stage_le`: a cluster holds at most `stSize/g + 1` vertices of each stage.
* `g_mul_card_inc_le`: `g · #(items at node a) ≤ 3 (64 ℓ + 15 g L1)` (an item at `a` has an end in
  cluster `a`, `a − 1` or `g − 1`).
* `card_inc_mul_W_le`: `#(items at a) · W ≤ PM n g := 2^16 ((n+2)/g + dg n)`.
* `mulSys_U_le`: `U ≤ 2^15 (n+2)`; `mulSys_is`: Definition 2 with `P = PM n g`, `B = 1`.

Standard axioms only.
-/
import EthFollowup.Factoring.MulNetDefs

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Finset EthFollowup.ExactHC

/-! ## Degrees -/

/-- The degree bound of the vertices of a stage. -/
def degSt (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => ℓ1 n + L1 n
  | 3 => ℓ1 n + L1 n
  | 4 => ℓ2 n + L2 n
  | 5 => ℓ2 n + L2 n
  | 6 => 3
  | 7 => L2 n + L2 n
  | 8 => L1 n + L1 n
  | _ => 4

/-- The indices of the wires with an end at `v`. -/
def endsAt (n : ℕ) (v : VD) : Finset ℕ :=
  (range (numWires n)).filter fun j => (ends n (wireOf n j)).1 = v ∨ (ends n (wireOf n j)).2 = v

theorem card_endsAt_le_of_sub {n : ℕ} {v : VD} (S : Finset WD)
    (hS : ∀ d, d.Valid n → ((ends n d).1 = v ∨ (ends n d).2 = v) → d ∈ S) : #(endsAt n v) ≤ #S := by
  refine (card_le_card (t := S.image (wireIdx n)) fun j hj => ?_).trans card_image_le
  rw [endsAt, mem_filter, mem_range] at hj
  exact mem_image.2 ⟨wireOf n j, hS _ (wireOf_valid hj.1) hj.2, wireIdx_wireOf n j⟩

/-- The wires at a carry vertex: two coefficient wires and two carry wires. -/
theorem carry_ends_mem {n k : ℕ} {d : WD} (hd : d.Valid n)
    (he : (ends n d).1 = .carry k ∨ (ends n d).2 = .carry k) :
    d ∈ ({.Cc (k % ℓ1 n) (k / ℓ1 n), .Cc (k % ℓ1 n + ℓ1 n) (k / ℓ1 n - 1), .rr (k - 1), .rr k} :
      Finset WD) := by
  cases d <;> simp only [ends, reduceCtorEq, false_or, or_false, VD.carry.injEq] at he
  case Cc a u =>
    simp only [WD.Valid] at hd
    subst he
    have hl := one_le_ℓ1 n
    rw [L1_eq_two_mul] at hd
    by_cases ha : a < ℓ1 n
    · simp only [blk_mod _ ha, blk_div _ ha, mem_insert, mem_singleton, true_or]
    · have ha' : a - ℓ1 n < ℓ1 n := by omega
      have e : a + ℓ1 n * u = (a - ℓ1 n) + ℓ1 n * (u + 1) := by rw [mul_add]; omega
      rw [e, blk_mod _ ha', blk_div _ ha']
      simp only [mem_insert, mem_singleton, WD.Cc.injEq, reduceCtorEq, or_false]
      omega
  case rr j =>
    rcases he with rfl | rfl
    · simp
    · simp

/-- **The degree of a vertex.** -/
theorem card_endsAt_le {n : ℕ} {v : VD} (hv : v.Valid n) : #(endsAt n v) ≤ degSt n v.stage := by
  cases v
  case carry k =>
    exact (card_endsAt_le_of_sub _ fun d hd he => carry_ends_mem hd he).trans card_le_four
  all_goals
    exact (card_endsAt_le_of_sub _ fun d hd he => List.mem_toFinset.2 (mem_incW hd he)).trans
      ((List.toFinset_card_le _).trans (by simp [incW, degSt, VD.stage]))

theorem stage_lt (v : VD) : v.stage < 10 := by cases v <;> simp [VD.stage]

/-! ## Vertices of a stage in a cluster -/

/-- The offset of a stage in the vertex enumeration. -/
def stOff (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => ℓ n
  | 2 => 2 * ℓ n
  | 3 => 2 * ℓ n + ℓ2 n
  | 4 => 2 * ℓ n + 2 * ℓ2 n
  | 5 => 2 * ℓ n + 2 * ℓ2 n + L1 n
  | 6 => 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n
  | 7 => 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n
  | 8 => 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n
  | _ => 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n

theorem vertIdx_eq (n : ℕ) (v : VD) : vertIdx n v = stOff n v.stage + v.idx n := by
  cases v <;> simp [vertIdx, stOff, VD.stage, VD.idx]

/-- **A cluster holds at most `stSize/g + 1` vertices of each stage.** -/
theorem g_mul_card_stage_le (n g st c : ℕ) (hg : 1 ≤ g) :
    g * #((range (numVerts n)).filter fun j => (vertOf n j).stage = st ∧ clus n g (vertOf n j) = c) ≤
      stSize n st + g := by
  have h1 : #((range (numVerts n)).filter fun j => (vertOf n j).stage = st ∧ clus n g (vertOf n j) = c) ≤
      #((range (stSize n st)).filter fun i => VB.vbN (stSize n st) g i = c) := by
    apply card_le_card_of_injOn (fun j => (vertOf n j).idx n)
    · intro j hj
      simp only [coe_filter, mem_range] at hj
      simp only [coe_filter, mem_range]
      obtain ⟨hj, hs, hc⟩ := hj
      have hv := vertOf_valid hj
      refine ⟨hs ▸ VD.idx_lt hv, ?_⟩
      rw [← hc, clus, hs]
    · intro j hj j' hj' e
      simp only [coe_filter, mem_range] at hj hj'
      simp only at e
      rw [← vertIdx_vertOf n j, ← vertIdx_vertOf n j', vertIdx_eq, vertIdx_eq, hj.2.1, hj'.2.1, e]
  have h2 := ExactHC.VB.card_vb_le (stSize n st) g c hg
  calc g * _ ≤ g * (stSize n st / g + 1) := Nat.mul_le_mul_left _ (h1.trans h2)
    _ ≤ stSize n st + g := by rw [mul_add, mul_one]; exact Nat.add_le_add_right (Nat.mul_div_le _ _) _

/-- The vertices (by index) of cluster `c`. -/
def vClus (n g c : ℕ) : Finset ℕ := (range (numVerts n)).filter fun i => clus n g (vertOf n i) = c

/-- The stage sum `Σ_{st<10} (stSize st + g) · degSt st`. -/
def bSum (n g : ℕ) : ℕ := ∑ st ∈ range 10, (stSize n st + g) * degSt n st

/-- The incident wires of the vertices of one cluster. -/
theorem g_mul_sum_deg_le (n g c : ℕ) (hg : 1 ≤ g) :
    g * ∑ i ∈ vClus n g c, degSt n (vertOf n i).stage ≤ bSum n g := by
  rw [← sum_fiberwise_of_maps_to (t := range 10) (g := fun i => (vertOf n i).stage)
    (fun i _ => mem_range.2 (stage_lt _)), mul_sum]
  unfold bSum
  refine sum_le_sum fun st _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, smul_eq_mul, ← mul_assoc]
  refine Nat.mul_le_mul_right _ (le_trans (le_of_eq ?_) (g_mul_card_stage_le n g st c hg))
  congr 2
  unfold vClus
  rw [filter_filter]
  exact filter_congr fun i _ => and_comm

theorem bSum_le (n g : ℕ) : bSum n g ≤ 64 * ℓ n + g * (15 * L1 n) := by
  obtain ⟨y, Z, a, h1, h2, h3, h4, -, -, -, -, hy, -⟩ := shape n
  simp only [bSum, sum_range_succ, sum_range_zero, stSize, degSt]
  unfold ℓ nF Kc
  rw [h1, h2, h3, h4]
  nlinarith

/-- The clusters whose vertices carry the items of node `a`. -/
theorem lohi_cases {g x y a : ℕ} (h : (lohi g x y).1 = a ∨ (lohi g x y).2 = a) (hx : x < g) :
    x = a ∨ y = a ∨ x = a - 1 ∨ x = g - 1 := by
  unfold lohi at h
  split_ifs at h <;> simp only at h <;> omega

/-! ## The items of a node -/

section Sys

variable {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (hg : 2 ≤ g)

/-- **`g · #(items at a) ≤ 3 · bSum`.** -/
theorem g_mul_card_inc_le (a : Fin g) :
    g * #(univ.filter ((mulSys n N pt g hg).Inc a)) ≤ 3 * bSum n g := by
  set Ca : Finset ℕ := {a.val, a.val - 1, g - 1}
  have hsub : #(univ.filter ((mulSys n N pt g hg).Inc a)) ≤
      #(Ca.biUnion fun c => (vClus n g c).biUnion fun i => endsAt n (vertOf n i)) := by
    apply card_le_card_of_injOn Fin.val
    · intro k hk
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
      rw [mulSys_inc] at hk
      have hd := wireOf_valid k.2
      have hev := ends_valid hd
      have hc := lohi_cases hk (clus_lt hev.1 (by omega))
      simp only [coe_biUnion, mem_coe, Set.mem_iUnion, exists_prop]
      have pick : ∀ (v : VD), v.Valid n → (ends n (wireOf n k.val)).1 = v ∨ (ends n (wireOf n k.val)).2 = v →
          clus n g v ∈ Ca → ∃ c ∈ Ca, ∃ i ∈ vClus n g c, k.val ∈ endsAt n (vertOf n i) := by
        intro v hv he hcv
        refine ⟨_, hcv, vertIdx n v, ?_, ?_⟩
        · simp only [vClus, mem_filter, mem_range, vertOf_vertIdx hv]
          exact ⟨vertIdx_lt hv, trivial⟩
        · simp only [endsAt, mem_filter, mem_range, vertOf_vertIdx hv]
          exact ⟨k.2, he⟩
      rcases hc with hc | hc | hc | hc
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.2 (Or.inr rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
    · intro k _ k' _ e; exact Fin.ext e
  have hdeg : ∀ c, #((vClus n g c).biUnion fun i => endsAt n (vertOf n i)) ≤
      ∑ i ∈ vClus n g c, degSt n (vertOf n i).stage := fun c =>
    card_biUnion_le.trans (sum_le_sum fun i hi =>
      card_endsAt_le (vertOf_valid (mem_range.1 (mem_filter.1 hi).1)))
  have hCa : #Ca ≤ 3 := card_le_three
  calc g * #(univ.filter ((mulSys n N pt g hg).Inc a))
      ≤ g * ∑ c ∈ Ca, ∑ i ∈ vClus n g c, degSt n (vertOf n i).stage :=
        Nat.mul_le_mul_left _ (hsub.trans (card_biUnion_le.trans (sum_le_sum fun c _ => hdeg c)))
    _ = ∑ c ∈ Ca, g * ∑ i ∈ vClus n g c, degSt n (vertOf n i).stage := mul_sum _ _ _
    _ ≤ ∑ _c ∈ Ca, bSum n g := sum_le_sum fun c _ => g_mul_sum_deg_le n g c (by omega)
    _ = #Ca * bSum n g := by rw [sum_const, smul_eq_mul]
    _ ≤ 3 * bSum n g := Nat.mul_le_mul_right _ hCa

/-- The node bound `P` of the multiplication network. -/
def PM (n g : ℕ) : ℕ := 2 ^ 16 * ((n + 2) / g + dg n)

/-- **The label bits at a node**: `#(items at a) · W ≤ PM n g = 2^16 ((n+2)/g + dg n)`. -/
theorem card_inc_mul_W_le (a : Fin g) :
    #(univ.filter ((mulSys n N pt g hg).Inc a)) * W n ≤ PM n g := by
  set X := #(univ.filter ((mulSys n N pt g hg).Inc a))
  have h1 := g_mul_card_inc_le (n := n) (N := N) (pt := pt) hg a
  have h2 := bSum_le n g
  have h3 := ℓ_mul_W_le n
  have h4 := deg_le n
  have hdg : 1 ≤ dg n := Nat.one_le_two_pow
  have hgX : g * (X * W n) ≤ 49152 * (n + 2) + g * (23 * dg n) := by
    have e1 : g * (X * W n) ≤ 3 * (64 * ℓ n + g * (15 * L1 n)) * W n := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (h1.trans (Nat.mul_le_mul_left _ h2))
    have e2 : 3 * (64 * ℓ n + g * (15 * L1 n)) * W n = 192 * (ℓ n * W n) + g * (45 * (L1 n * W n)) := by
      ring
    have e3 : 45 * (L1 n * W n) ≤ 23 * dg n := by nlinarith
    rw [e2] at e1
    have := Nat.mul_le_mul_left g e3
    nlinarith
  have hdiv := Nat.div_add_mod (n + 2) g
  have hmod := Nat.mod_lt (n + 2) (show 0 < g by omega)
  have hlt : g * (X * W n) < g * (49152 * ((n + 2) / g) + 49152 + 23 * dg n) := by
    nlinarith
  have := Nat.lt_of_mul_lt_mul_left hlt
  unfold PM
  omega

theorem mulSys_touch (a : Fin g) : #(univ.filter ((mulSys n N pt g hg).Touch a)) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]; intro j; exact j.elim

/-- **`U ≤ 2^15 (n+2)`.** -/
theorem mulSys_U_le : ((mulSys n N pt g hg).net (labCode n)).U ≤ 2 ^ 15 * (n + 2) := by
  rw [LabelSystem.U_eq, Fintype.card_fin, Fintype.card_eq_zero, clog_W, add_zero]
  have := numWires_mul_W_le n
  omega

theorem mulT_abs_lt (a : Fin g) (ℓ : Fin (numWires n) → Lab n) : |mulT n N pt g a ℓ| < 2 ^ 1 := by
  unfold mulT; split_ifs <;> norm_num

/-- **Definition 2 for the multiplication network** with `P = PM n g` and `B = 1`. -/
theorem mulSys_is : ((mulSys n N pt g hg).net (labCode n)).Is (PM n g) 1 := by
  refine LabelSystem.net_is _ _ ?_ le_rfl (fun a => ?_) (fun a ℓ y => mulT_abs_lt a ℓ)
  · unfold PM
    have : 1 ≤ dg n := Nat.one_le_two_pow
    calc 1 ≤ (n + 2) / g + dg n := le_trans this (Nat.le_add_left _ _)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by norm_num)
  · rw [mulSys_touch, add_zero, clog_W]
    exact card_inc_mul_W_le hg a

end Sys

end EthFollowup.Factoring
