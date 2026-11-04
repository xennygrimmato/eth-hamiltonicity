/-
# ArithNet, module L2 (part 3): the counts of the network

`scratchpad/plans/modp-plan.md`, ADDENDUM §B (Bounds); interface `modp-interface.md` (L2). Template:
`Factoring/MulNetCount.lean`.

* `aEndsAt n D v`: the wire indices with an end at `v`; `card_aEndsAt_le`: at most `degA n D v.stage`.
* `g_mul_card_stage_le'`: a cluster holds at most `stSz/g + 1` vertices of each stage.
* `aBSum_le`: `Σ_st (stSz st + g)·degA st ≤ cA·ℓ + g·(cA·L1)` with the description constant
  `cA D = 64 (nV + nP + nQ + 1)(nC + 1)`.
* `card_inc_mul_Wa_le`: `#(items at a) · Wa ≤ PA n D g := 2^12 · cA D · ((n+2)/g + dg n)`.
* `arithSys_U_le`: `U ≤ 2^11 · cA D · (n+2)`; **`arithSys_is`**: Definition 2 with `P = PA n D g`, `B = 1`.

Standard axioms only.
-/
import EthFollowup.ModP.ArithNetDefs

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset EthFollowup.ExactHC EthFollowup.Factoring

instance (n : ℕ) (D : Desc) (v : AV) : DecidablePred (AWInc n D v) := fun d => by
  unfold AWInc; infer_instance

/-- The description constant: `64 (nV + nP + nQ + 1)(nC + 1)`. -/
def cA (D : Desc) : ℕ := 64 * ((D.nV + D.nP + D.nQ + 1) * (D.nC + 1))

theorem cA_pos (D : Desc) : 0 < cA D := by unfold cA; positivity

/-! ## Degrees -/

/-- The indices of the wires with an end at `v`. -/
def aEndsAt (n : ℕ) (D : Desc) (v : AV) : Finset ℕ :=
  (range (numAW n D)).filter fun j => AWInc n D v (awOf n D j)

/-- **The degree of a vertex.** -/
theorem card_aEndsAt_le (n : ℕ) (D : Desc) (v : AV) : #(aEndsAt n D v) ≤ degA n D v.stage := by
  calc #(aEndsAt n D v) ≤ #(((aInc n D v).map (awIdx n D)).toFinset) := by
        refine card_le_card fun j hj => ?_
        rw [aEndsAt, mem_filter, mem_range] at hj
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨awOf n D j, mem_aInc (awOf_valid hj.1) hj.2, awIdx_awOf hj.1⟩
    _ ≤ ((aInc n D v).map (awIdx n D)).length := List.toFinset_card_le _
    _ = degA n D v.stage := by rw [List.length_map, length_aInc]

/-! ## Vertices of a stage in a cluster -/

/-- **A cluster holds at most `stSz/g + 1` vertices of each stage.** -/
theorem g_mul_card_stage_le' (n : ℕ) (D : Desc) (g st c : ℕ) (hg : 1 ≤ g) :
    g * #((range (numAV n D)).filter fun j => (avOf n D j).stage = st ∧ aClus n D g (avOf n D j) = c) ≤
      stSz n D st + g := by
  have h1 : #((range (numAV n D)).filter fun j => (avOf n D j).stage = st ∧ aClus n D g (avOf n D j) = c) ≤
      #((range (stSz n D st)).filter fun i => VB.vbN (stSz n D st) g i = c) := by
    apply card_le_card_of_injOn (fun j => (avOf n D j).idx n D)
    · intro j hj
      simp only [coe_filter, mem_range] at hj
      simp only [coe_filter, mem_range]
      obtain ⟨hj, hs, hc⟩ := hj
      have hv := avOf_valid hj
      refine ⟨hs ▸ AV.idx_lt hv, ?_⟩
      rw [← hc, aClus, hs]
    · intro j hj j' hj' e
      simp only [coe_filter, mem_range] at hj hj'
      simp only at e
      rw [← avIdx_avOf hj.1, ← avIdx_avOf hj'.1, avIdx_eq, avIdx_eq, hj.2.1, hj'.2.1, e]
  have h2 := ExactHC.VB.card_vb_le (stSz n D st) g c hg
  calc g * _ ≤ g * (stSz n D st / g + 1) := Nat.mul_le_mul_left _ (h1.trans h2)
    _ ≤ stSz n D st + g := by rw [mul_add, mul_one]; exact Nat.add_le_add_right (Nat.mul_div_le _ _) _

/-- The vertices (by index) of cluster `c`. -/
def aVClus (n : ℕ) (D : Desc) (g c : ℕ) : Finset ℕ :=
  (range (numAV n D)).filter fun i => aClus n D g (avOf n D i) = c

/-- The stage sum `Σ_{st<7} (stSz st + g) · degA st`. -/
def aBSum (n : ℕ) (D : Desc) (g : ℕ) : ℕ := ∑ st ∈ range 7, (stSz n D st + g) * degA n D st

theorem g_mul_sum_degA_le (n : ℕ) (D : Desc) (g c : ℕ) (hg : 1 ≤ g) :
    g * ∑ i ∈ aVClus n D g c, degA n D (avOf n D i).stage ≤ aBSum n D g := by
  rw [← sum_fiberwise_of_maps_to (t := range 7) (g := fun i => (avOf n D i).stage)
    (fun i _ => mem_range.2 (stage_lt _)), mul_sum]
  unfold aBSum
  refine sum_le_sum fun st _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, smul_eq_mul, ← mul_assoc]
  refine Nat.mul_le_mul_right _ (le_trans (le_of_eq ?_) (g_mul_card_stage_le' n D g st c hg))
  congr 2
  unfold aVClus
  rw [filter_filter]
  exact filter_congr fun i _ => and_comm

/-- **The stage sum**: `aBSum ≤ cA·ℓ + g·(cA·L1)`. -/
theorem aBSum_le (n : ℕ) (D : Desc) (g : ℕ) : aBSum n D g ≤ cA D * ℓ n + g * (cA D * L1 n) := by
  obtain ⟨y, Z, a, h1, h2, h3, h4, -, -, -, -, hy, -⟩ := shape n
  simp only [aBSum, sum_range_succ, sum_range_zero, stSz, Blocks.sizes, vDims, degA, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ, List.prod_cons, List.prod_nil, mul_one, zero_add]
  unfold ℓ Kc cA
  rw [h1, h2, h3, h4]
  set V := D.nV; set P := D.nP; set Q := D.nQ; set C := D.nC
  -- stage terms, one by one
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  have eq0 : (y * y + g) * (V + C * V + 2 * P + 2 * Q) = y * y * (V + C * V + 2 * P + 2 * Q) +
      g * (V + C * V + 2 * P + 2 * Q) := by ring
  have hXY : V + C * V + 2 * P + 2 * Q ≤ (V + P + Q + 1) * (C + 1) * 2 := by nlinarith
  have hXY' : V + 2 * P + 2 ≤ (V + P + Q + 1) * (C + 1) * 2 := by nlinarith
  have hP : P ≤ (V + P + Q + 1) * (C + 1) := by nlinarith
  have hC : C * (V + 2 * P + 2) ≤ (V + P + Q + 1) * (C + 1) * 2 := by nlinarith
  set X := (V + P + Q + 1) * (C + 1) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have k0 := Nat.mul_le_mul_left (y * y) hXY
  have k0' := Nat.mul_le_mul_left g hXY
  have k1 := Nat.mul_le_mul_left (y * y) hP
  have k6 := Nat.mul_le_mul_left (y * y) hC
  have k6' := Nat.mul_le_mul_left g hXY'
  have gy : g ≤ g * y := Nat.le_mul_of_pos_right g hy
  have gX := Nat.mul_le_mul_left g hX1
  have gyX := Nat.mul_le_mul_left (g * y) hX1
  have gyX2 : g * X ≤ g * y * X := Nat.mul_le_mul_right X gy
  have yyX := Nat.mul_le_mul_left (y * y) hX1
  have yP : P * y ≤ P * (y * y) := Nat.mul_le_mul_left P yy
  have yC6 : C * (V + 2 * P + 2) * y ≤ C * (V + 2 * P + 2) * (y * y) := Nat.mul_le_mul_left _ yy
  have gXX : g * (X * 2) ≤ g * y * (X * 2) := Nat.mul_le_mul_right _ gy
  nlinarith

/-- The clusters whose vertices carry the items of node `a`. -/
theorem lohi_cases' {g x y a : ℕ} (h : (lohi g x y).1 = a ∨ (lohi g x y).2 = a) (hx : x < g) :
    x = a ∨ y = a ∨ x = a - 1 ∨ x = g - 1 := by
  unfold lohi at h
  split_ifs at h <;> simp only at h <;> omega

/-! ## The items of a node -/

section Sys

variable {n : ℕ} {D : Desc} {g : ℕ} (hg : 2 ≤ g)

/-- **`g · #(items at a) ≤ 3 · aBSum`.** -/
theorem g_mul_card_inc_le' (a : Fin g) :
    g * #(univ.filter ((arithSys n D g hg).Inc a)) ≤ 3 * aBSum n D g := by
  set Ca : Finset ℕ := {a.val, a.val - 1, g - 1}
  have hsub : #(univ.filter ((arithSys n D g hg).Inc a)) ≤
      #(Ca.biUnion fun c => (aVClus n D g c).biUnion fun i => aEndsAt n D (avOf n D i)) := by
    apply card_le_card_of_injOn Fin.val
    · intro k hk
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
      rw [arithSys_inc] at hk
      have hd := awOf_valid k.2
      have hev := aEnds_valid hd
      have hc := lohi_cases' hk (aClus_lt hev.1 (by omega))
      simp only [coe_biUnion, mem_coe, Set.mem_iUnion, exists_prop]
      have pick : ∀ (v : AV), v.Valid n D → AWInc n D v (awOf n D k.val) →
          aClus n D g v ∈ Ca → ∃ c ∈ Ca, ∃ i ∈ aVClus n D g c, k.val ∈ aEndsAt n D (avOf n D i) := by
        intro v hv he hcv
        refine ⟨_, hcv, avIdx n D v, ?_, ?_⟩
        · simp only [aVClus, mem_filter, mem_range, avOf_avIdx hv]
          exact ⟨avIdx_lt hv, trivial⟩
        · simp only [aEndsAt, mem_filter, mem_range, avOf_avIdx hv]
          exact ⟨k.2, he⟩
      rcases hc with hc | hc | hc | hc
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.2 (Or.inr rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
      · exact pick _ hev.1 (Or.inl rfl) (by rw [hc]; simp [Ca])
    · intro k _ k' _ e; exact Fin.ext e
  have hdeg : ∀ c, #((aVClus n D g c).biUnion fun i => aEndsAt n D (avOf n D i)) ≤
      ∑ i ∈ aVClus n D g c, degA n D (avOf n D i).stage := fun c =>
    card_biUnion_le.trans (sum_le_sum fun i _ => card_aEndsAt_le n D _)
  have hCa : #Ca ≤ 3 := card_le_three
  calc g * #(univ.filter ((arithSys n D g hg).Inc a))
      ≤ g * ∑ c ∈ Ca, ∑ i ∈ aVClus n D g c, degA n D (avOf n D i).stage :=
        Nat.mul_le_mul_left _ (hsub.trans (card_biUnion_le.trans (sum_le_sum fun c _ => hdeg c)))
    _ = ∑ c ∈ Ca, g * ∑ i ∈ aVClus n D g c, degA n D (avOf n D i).stage := mul_sum _ _ _
    _ ≤ ∑ _c ∈ Ca, aBSum n D g := sum_le_sum fun c _ => g_mul_sum_degA_le n D g c (by omega)
    _ = #Ca * aBSum n D g := by rw [sum_const, smul_eq_mul]
    _ ≤ 3 * aBSum n D g := Nat.mul_le_mul_right _ hCa

/-- The node bound `P` of the network. -/
def PA (n : ℕ) (D : Desc) (g : ℕ) : ℕ := 2 ^ 12 * cA D * ((n + 2) / g + dg n)

theorem ℓ_mul_Wa_le (n : ℕ) : ℓ n * Wa n ≤ 2 ^ 10 * (n + 2) := by
  have h := ℓ_mul_W_le n
  have hW : Wa n ≤ 4 * W n := by unfold Wa W; omega
  calc ℓ n * Wa n ≤ ℓ n * (4 * W n) := Nat.mul_le_mul_left _ hW
    _ = 4 * (ℓ n * W n) := by ring
    _ ≤ 2 ^ 10 * (n + 2) := by omega

theorem L1_mul_Wa_le (n : ℕ) : 2 * (L1 n * Wa n) ≤ 4 * dg n := by
  have h := deg_le n
  have hW : Wa n ≤ 4 * W n := by unfold Wa W; omega
  have : L1 n * Wa n ≤ L1 n * (4 * W n) := Nat.mul_le_mul_left _ hW
  nlinarith

/-- **The label bits at a node**: `#(items at a) · Wa ≤ PA n D g`. -/
theorem card_inc_mul_Wa_le (a : Fin g) :
    #(univ.filter ((arithSys n D g hg).Inc a)) * Wa n ≤ PA n D g := by
  set X := #(univ.filter ((arithSys n D g hg).Inc a))
  have h1 := g_mul_card_inc_le' (n := n) (D := D) hg a
  have h2 := aBSum_le n D g
  have h3 := ℓ_mul_Wa_le n
  have h4 := L1_mul_Wa_le n
  have hdg : 1 ≤ dg n := Nat.one_le_two_pow
  set K := cA D
  have hgX : g * (X * Wa n) ≤ 3 * K * (2 ^ 10 * (n + 2)) + g * (6 * K * dg n) := by
    have e1 : g * (X * Wa n) ≤ 3 * (K * ℓ n + g * (K * L1 n)) * Wa n := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (h1.trans (Nat.mul_le_mul_left _ h2))
    have e2 : 3 * (K * ℓ n + g * (K * L1 n)) * Wa n = 3 * K * (ℓ n * Wa n) + g * (3 * K * (L1 n * Wa n)) := by
      ring
    have e3 : 3 * K * (ℓ n * Wa n) ≤ 3 * K * (2 ^ 10 * (n + 2)) := Nat.mul_le_mul_left _ h3
    have e4 : 3 * K * (L1 n * Wa n) ≤ 6 * K * dg n := by nlinarith
    have := Nat.mul_le_mul_left g e4
    omega
  have hdiv := Nat.div_add_mod (n + 2) g
  have hmod := Nat.mod_lt (n + 2) (show 0 < g by omega)
  have hK : 1 ≤ K := cA_pos D
  have hlt : g * (X * Wa n) < g * (3 * K * 2 ^ 10 * ((n + 2) / g) + 3 * K * 2 ^ 10 + 6 * K * dg n) := by
    have : 3 * K * (2 ^ 10 * (n + 2)) = 3 * K * 2 ^ 10 * (g * ((n + 2) / g) + (n + 2) % g) := by
      rw [hdiv]; ring
    have h5 : 3 * K * 2 ^ 10 * ((n + 2) % g) < 3 * K * 2 ^ 10 * g :=
      Nat.mul_lt_mul_of_pos_left hmod (by positivity)
    nlinarith
  have h6 := Nat.lt_of_mul_lt_mul_left hlt
  unfold PA
  show X * Wa n ≤ 2 ^ 12 * K * ((n + 2) / g + dg n)
  have hKB : K * 1 ≤ K * dg n := Nat.mul_le_mul_left _ hdg
  have hq : 0 ≤ K * ((n + 2) / g) := Nat.zero_le _
  have e : 2 ^ 12 * K * ((n + 2) / g + dg n) = 4096 * (K * ((n + 2) / g)) + 4096 * (K * dg n) := by ring
  have e' : 3 * K * 2 ^ 10 * ((n + 2) / g) + 3 * K * 2 ^ 10 + 6 * K * dg n =
      3072 * (K * ((n + 2) / g)) + 3072 * (K * 1) + 6 * (K * dg n) := by ring
  rw [e]; rw [e'] at h6
  omega

theorem arithSys_touch (a : Fin g) : #(univ.filter ((arithSys n D g hg).Touch a)) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]; intro j; exact j.elim

/-- The number of wires: `numAW ≤ cA · ℓ`. -/
theorem numAW_le (n : ℕ) (D : Desc) : numAW n D ≤ cA D * ℓ n := by
  obtain ⟨y, Z, a, h1, h2, h3, h4, -, -, -, -, hy, -⟩ := shape n
  simp only [numAW, Blocks.total, Blocks.sizes, wDims, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, List.sum_cons, List.sum_nil, add_zero]
  unfold ℓ Kc cA
  rw [h1, h2, h3, h4]
  set V := D.nV; set P := D.nP; set Q := D.nQ; set C := D.nC
  have hyy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  have hk : 2 * y + y * (2 * y) - 1 ≤ 4 * (y * y) := by
    have : y * (2 * y) = 2 * (y * y) := by ring
    omega
  have hl : y * y - 1 ≤ y * y := Nat.sub_le _ _
  have e1 := Nat.mul_le_mul_left C hk
  have e2 := Nat.mul_le_mul_left Q hl
  have hlin : V + C * V + 26 * P + 4 * C + Q ≤ 64 * ((V + P + Q + 1) * (C + 1)) := by nlinarith
  have e3 := Nat.mul_le_mul_right (y * y) hlin
  nlinarith

/-- **`U ≤ 2^11 · cA D · (n + 2)`.** -/
theorem arithSys_U_le : ((arithSys n D g hg).net (aLabCode n)).U ≤ 2 ^ 11 * cA D * (n + 2) := by
  rw [LabelSystem.U_eq, Fintype.card_fin, Fintype.card_eq_zero, clog_Wa, add_zero]
  have h1 : numAW n D * Wa n ≤ cA D * ℓ n * Wa n := Nat.mul_le_mul_right _ (numAW_le n D)
  have h2 : cA D * ℓ n * Wa n ≤ cA D * (2 ^ 10 * (n + 2)) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (ℓ_mul_Wa_le n)
  calc 2 * (numAW n D * Wa n) ≤ 2 * (cA D * (2 ^ 10 * (n + 2))) := Nat.mul_le_mul_left _ (h1.trans h2)
    _ = 2 ^ 11 * cA D * (n + 2) := by ring

theorem arithT_abs_lt (a : Fin g) (ℓ : Fin (numAW n D) → ALab n) : |arithT n D g a ℓ| < 2 ^ 1 := by
  unfold arithT; split_ifs <;> norm_num

/-- **Definition 2 for the arithmetic-constraint network** with `P = PA n D g` and `B = 1`. -/
theorem arithSys_is : ((arithSys n D g hg).net (aLabCode n)).Is (PA n D g) 1 := by
  refine LabelSystem.net_is _ _ ?_ le_rfl (fun a => ?_) (fun a ℓ y => by rw [arithSys_T]; exact arithT_abs_lt a ℓ)
  · unfold PA
    have h1 : 1 ≤ dg n := Nat.one_le_two_pow
    have h2 : 1 ≤ (n + 2) / g + dg n := le_trans h1 (Nat.le_add_left _ _)
    exact le_trans h2 (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) (cA_pos D)))
  · rw [arithSys_touch, add_zero, clog_Wa]
    exact card_inc_mul_Wa_le hg a

end Sys

end EthFollowup.ModP
