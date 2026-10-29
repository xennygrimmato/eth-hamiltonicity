/-
# Theorem Q1, bridge part 3: the circuit network in label-sharing form

For a scan state `st` (of valid gate codes), `g ≥ 1` nodes and the residue data `(M, z₁, z₂, z₃)`:

* `qSys`: the `LabelSystem` (`LabelNetwork.lean`) whose items are the crossing legs of `cpart st g`,
  with one-bit labels and no copy bits; the table of node `a` is the stream `streamN` of its factor
  descriptors (`descN`) on the setting.
* `qSys_value`: the value of the network is, in `ZMod M`, the merged path sum of the circuit
  (`cmat_factor`, `streamN_eq`).
* Counting: `card_inc_le` (a node sees at most `4(G/g + 1)` crossing legs), `length_ilN_le`
  (at most `2(G/g + 1)` internal legs), `qSys_is` (Definition 2 with `P = 4(G/g+1)`,
  `B = 2G + 4b + 2`).
-/
import EthFollowup.Quantum.QData
import EthFollowup.ExactHC.LabelProcs

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Finset EthFollowup.ExactHC

/-- Labels are single bits. -/
def boolCode : LabelCode Bool 1 where
  enc b := [b]
  dec z := z.headD false
  len _ := rfl
  dec_enc _ := rfl

section Sys

variable (st : SS) (g : ℕ) [NeZero g] (n M z₁ z₂ z₃ : ℕ) (xs ys : List Bool)

theorem itemV_mem (k : Fin (cpart st g).cl.length) : itemV st g k.val ∈ clN st g := by
  have hk : k.val < (clN st g).length := by rw [← length_cl]; exact k.2
  simp only [itemV, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

theorem itemV_cross (k : Fin (cpart st g).cl.length) :
    (itemV st g k.val).1 % g ≠ rgN st g (itemV st g k.val) := by
  have h := itemV_mem st g k
  simp only [clN, List.mem_filter, crossN, decide_eq_true_eq] at h
  exact h.2

theorem rgN_lt (v : ℕ × Bool) : rgN st g v < g := by
  unfold rgN; cases reader st v <;> exact Nat.mod_lt _ (NeZero.pos g)

theorem loN_lt_hiN (k : Fin (cpart st g).cl.length) : loN st g k.val < hiN st g k.val := by
  have := itemV_cross st g k
  unfold loN hiN; omega

theorem hiN_lt (k : Fin (cpart st g).cl.length) : hiN st g k.val < g := by
  have h1 := rgN_lt st g (itemV st g k.val)
  have h2 := Nat.mod_lt (itemV st g k.val).1 (NeZero.pos g)
  unfold hiN; omega

/-- The table of node `a`. -/
def qT (a : Fin g) (ℓ : Fin (cpart st g).cl.length → Bool) : ℤ :=
  (streamN M (ilN st g a.val).length (descN st g n M z₁ z₂ z₃ xs ys a.val) (zOf st g a.val ℓ) : ℤ)

/-- **The label system of the circuit network.** -/
def qSys : LabelSystem g (Fin (cpart st g).cl.length) Empty Bool where
  kord := List.finRange _
  kord_nodup := List.nodup_finRange _
  mem_kord := List.mem_finRange
  rord := []
  rord_nodup := List.nodup_nil
  mem_rord j := j.elim
  lo k := ⟨loN st g k.val, (loN_lt_hiN st g k).trans (hiN_lt st g k)⟩
  hi k := ⟨hiN st g k.val, hiN_lt st g k⟩
  lo_lt k := loN_lt_hiN st g k
  holder j := j.elim
  source j := j.elim
  holder_ne j := j.elim
  dflt := false
  par j _ := j.elim
  T a ℓ _ := qT st g n M z₁ z₂ z₃ xs ys a ℓ
  par_local j := j.elim
  T_local a ℓ ℓ' y y' hℓ _ := by
    have e : zOf st g a.val ℓ = zOf st g a.val ℓ' := by
      unfold zOf
      refine List.map_congr_left fun k hk => ?_
      split_ifs with h
      · refine hℓ ⟨k, h⟩ ?_
        have := (List.mem_filter.1 hk).2
        simp only [decide_eq_true_eq] at this
        rcases this with e | e
        · exact Or.inl (Fin.ext e)
        · exact Or.inr (Fin.ext e)
      · rfl
    unfold qT; rw [e]

theorem incList_val (a : Fin g) :
    ((qSys st g n M z₁ z₂ z₃ xs ys).incList a).map Fin.val = incN st g a.val := by
  have e : (List.finRange (cpart st g).cl.length).map Fin.val = List.range (clN st g).length := by
    rw [map_val_finRange, length_cl]
  show ((List.finRange _).filter _).map Fin.val = _
  unfold incN
  rw [← e, List.filter_map]
  congr 1
  refine List.filter_congr fun k _ => ?_
  simp [qSys, LabelSystem.Inc, Fin.ext_iff]

theorem enc_eq (a : Fin g) (x : (Fin (cpart st g).cl.length → Bool) × (Empty → Bool)) :
    (qSys st g n M z₁ z₂ z₃ xs ys).enc boolCode a x = zOf st g a.val x.1 := by
  unfold LabelSystem.enc zOf
  have hh : (qSys st g n M z₁ z₂ z₃ xs ys).heldList a = [] := rfl
  rw [hh, List.map_nil, List.append_nil, ← incList_val st g n M z₁ z₂ z₃ xs ys a, List.map_map]
  unfold encL
  simp only [boolCode]
  induction ((qSys st g n M z₁ z₂ z₃ xs ys).incList a) with
  | nil => rfl
  | cons k l ih =>
    simp only [List.flatMap_cons, List.map_cons, List.singleton_append, Function.comp_apply, dif_pos k.2]
    exact congrArg _ ih

/-- **The value of the circuit network** in `ZMod M`. -/
theorem qSys_value (cs : List GC) (hv : ∀ c ∈ cs, ValidC n c) {b : ℕ} [NeZero M] (hz : ZP M b z₁ z₂ z₃)
    (x y : Basis n) :
    ((((qSys (scan n cs) g n M z₁ z₂ z₃ (List.ofFn x) (List.ofFn y)).net boolCode).value : ℤ) : ZMod M) =
      cmat (n := n) (IM M b) cs y x := by
  rw [LabelSystem.value_net, cmat_factor (IM M b) g cs hv x y]
  push_cast
  refine Finset.sum_congr rfl fun ℓ _ => Finset.prod_congr rfl fun a _ => ?_
  show ((qT (scan n cs) g n M z₁ z₂ z₃ (List.ofFn x) (List.ofFn y) a ℓ : ℤ) : ZMod M) = _
  unfold qT
  rw [Int.cast_natCast]
  exact streamN_eq (scan n cs) g (good_scan cs hv) (good2_scan n cs hv) hz x y a ℓ

end Sys

/-! ### Counting the legs of a node -/

section Count

variable (st : SS) (g : ℕ) [NeZero g] (n M z₁ z₂ z₃ : ℕ) (xs ys : List Bool)

/-- The blocks of node `a`. -/
def blocksOf (a : ℕ) : Finset ℕ := (range st.1.length).filter fun t => t % g = a

theorem card_blocksOf_le (a : ℕ) : #(blocksOf st g a) ≤ st.1.length / g + 1 := by
  have h := Finset.card_le_card_of_injOn (fun t => t / g) (s := blocksOf st g a)
    (t := range (st.1.length / g + 1)) (fun t ht => by
      simp only [blocksOf, Finset.mem_filter, Finset.mem_range, Finset.mem_coe] at ht ⊢
      have := Nat.div_le_div_right (c := g) ht.1.le
      omega) (fun t ht t' ht' e => by
      simp only [blocksOf, Finset.mem_filter, Finset.mem_coe] at ht ht'
      simp only at e
      rw [← Nat.div_add_mod t g, ← Nat.div_add_mod t' g, e, ht.2, ht'.2])
  simpa using h

theorem allN_nodup (G : ℕ) : (allN G).Nodup := by
  rw [← allV_map]; exact (allV_nodup G).map vval_inj

theorem clN_nodup : (clN st g).Nodup := (allN_nodup _).filter _

theorem ilN_nodup (a : ℕ) : (ilN st g a).Nodup := (allN_nodup _).filter _

theorem length_ilN_le (a : ℕ) : (ilN st g a).length ≤ 2 * #(blocksOf st g a) := by
  rw [← List.toFinset_card_of_nodup (ilN_nodup st g a)]
  have hsub : (ilN st g a).toFinset ⊆ blocksOf st g a ×ˢ (Finset.univ : Finset Bool) := by
    intro v hv
    simp only [List.mem_toFinset, ilN, List.mem_filter, mem_allN, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [Finset.mem_product, blocksOf, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, and_true]
    exact ⟨hv.1, hv.2.2⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]

theorem length_ilN_le' (a : ℕ) : (ilN st g a).length ≤ 2 * st.1.length := by
  have h1 : (ilN st g a).length ≤ (allN st.1.length).length := List.length_filter_le _ _
  have h2 : ∀ G, (allN G).length = 2 * G := by
    intro G
    induction G with
    | zero => rfl
    | succ G ih =>
      simp only [allN, List.range_succ, List.flatMap_append, List.length_append] at ih ⊢
      rw [ih]; simp; ring
  have h2 := h2 st.1.length
  omega

theorem itemV_inj {k k' : ℕ} (hk : k < (clN st g).length) (hk' : k' < (clN st g).length)
    (e : itemV st g k = itemV st g k') : k = k' := by
  simp only [itemV, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk',
    Option.getD_some] at e
  exact (List.Nodup.getElem_inj_iff (clN_nodup st g)).1 e

theorem itemV_lt (k : Fin (cpart st g).cl.length) : (itemV st g k.val).1 < st.1.length := by
  have h := itemV_mem st g k
  simp only [clN, List.mem_filter, mem_allN] at h
  exact h.1

/-- **A node sees at most `4(G/g + 1)` crossing legs.** -/
theorem card_inc_le (hg2 : Good2 st.1.length st) (a : Fin g) :
    #(Finset.univ.filter ((qSys st g n M z₁ z₂ z₃ xs ys).Inc a)) ≤ 4 * #(blocksOf st g a.val) := by
  set X := qSys st g n M z₁ z₂ z₃ xs ys
  have hsplit : Finset.univ.filter (X.Inc a) ⊆
      Finset.univ.filter (fun k : Fin (cpart st g).cl.length => (itemV st g k.val).1 % g = a.val) ∪
        Finset.univ.filter (fun k : Fin (cpart st g).cl.length => rgN st g (itemV st g k.val) = a.val) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, X, qSys,
      LabelSystem.Inc, Fin.ext_iff] at hk ⊢
    unfold loN hiN at hk
    omega
  refine (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans ?_)
  have hm : ∀ k : Fin (cpart st g).cl.length, k.val < (clN st g).length := fun k => by
    rw [← length_cl]; exact k.2
  have hA : #(Finset.univ.filter (fun k : Fin (cpart st g).cl.length => (itemV st g k.val).1 % g = a.val)) ≤
      2 * #(blocksOf st g a.val) := by
    have h := Finset.card_le_card_of_injOn (fun k : Fin (cpart st g).cl.length => itemV st g k.val)
      (s := Finset.univ.filter (fun k : Fin (cpart st g).cl.length => (itemV st g k.val).1 % g = a.val))
      (t := blocksOf st g a.val ×ˢ (Finset.univ : Finset Bool)) (fun k hk => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp only [Finset.mem_coe, Finset.mem_product, blocksOf, Finset.mem_filter, Finset.mem_range,
          Finset.mem_univ, and_true]
        exact ⟨itemV_lt st g k, hk⟩) (fun k _ k' _ e => Fin.ext (itemV_inj st g (hm k) (hm k') e))
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h
    omega
  have hB : #(Finset.univ.filter (fun k : Fin (cpart st g).cl.length => rgN st g (itemV st g k.val) = a.val)) ≤
      2 * #(blocksOf st g a.val) := by
    -- the reader of a crossing leg
    have hr : ∀ k : Fin (cpart st g).cl.length, ∃ t, reader st (itemV st g k.val) = some t := by
      intro k
      have hc := itemV_cross st g k
      unfold rgN at hc
      cases h : reader st (itemV st g k.val) with
      | none => rw [h] at hc; exact absurd rfl hc
      | some t => exact ⟨t, rfl⟩
    choose rt hrt using hr
    have hrt' : ∀ k, rt k < st.1.length ∧ readsB (blkAt st (rt k)) (itemV st g k.val) = true := fun k => by
      have h := hrt k
      unfold reader at h
      have h' := List.find?_some h
      exact ⟨List.mem_range.1 (List.mem_of_find?_eq_some h), h'⟩
    set jt : Fin (cpart st g).cl.length → Bool := fun k =>
      !decide (srcOf (blkAt st (rt k)) false = some (itemV st g k.val))
    have hjt : ∀ k, srcOf (blkAt st (rt k)) (jt k) = some (itemV st g k.val) := fun k => by
      have h := (hrt' k).2
      simp only [readsB, Bool.or_eq_true, decide_eq_true_eq] at h
      by_cases h0 : srcOf (blkAt st (rt k)) false = some (itemV st g k.val)
      · have e : jt k = false := by simp [jt, h0]
        rw [e]; exact h0
      · have e : jt k = true := by simp [jt, h0]
        rw [e]; exact h.resolve_left h0
    have h := Finset.card_le_card_of_injOn (fun k : Fin (cpart st g).cl.length => (rt k, jt k))
      (s := Finset.univ.filter (fun k : Fin (cpart st g).cl.length => rgN st g (itemV st g k.val) = a.val))
      (t := blocksOf st g a.val ×ˢ (Finset.univ : Finset Bool)) (fun k hk => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp only [Finset.mem_coe, Finset.mem_product, blocksOf, Finset.mem_filter, Finset.mem_range,
          Finset.mem_univ, and_true]
        refine ⟨(hrt' k).1, ?_⟩
        rw [← hk]; unfold rgN; rw [hrt k]; rfl) (fun k _ k' _ e => by
        simp only [Prod.mk.injEq] at e
        have h1 := hjt k
        have h2 := hjt k'
        rw [e.1, e.2, h2] at h1
        exact Fin.ext (itemV_inj st g (hm k) (hm k') (Option.some.inj h1).symm))
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h
    omega
  omega

/-- The parameter `P` of the circuit network. -/
def PQ : ℕ := 4 * (st.1.length / g + 1)

/-- The parameter `B` of the circuit network. -/
def BQ (b : ℕ) : ℕ := 2 * st.1.length + 4 * b + 2

theorem termN_lt {M : ℕ} (hM : 0 < M) (fs : List FDesc) (z : List Bool) (i : ℕ) : termN M fs z i < M :=
  Nat.mod_lt _ hM

theorem streamN_lt {M N : ℕ} (hM : 0 < M) (fs : List FDesc) (z : List Bool) : streamN M N fs z < 2 ^ N * M := by
  unfold streamN
  calc ∑ i ∈ range (2 ^ N), termN M fs z i < ∑ _i ∈ range (2 ^ N), M :=
        Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun i _ => termN_lt hM fs z i
    _ = 2 ^ N * M := by simp

/-- **Definition 2 for the circuit network.** -/
theorem qSys_is (hg2 : Good2 st.1.length st) {b : ℕ} (hM : M = Mb b) :
    ((qSys st g n M z₁ z₂ z₃ xs ys).net boolCode).Is (PQ st g) (BQ st b) := by
  have hP1 : 1 ≤ PQ st g := by unfold PQ; generalize st.1.length / g = y; omega
  have hB1 : 1 ≤ BQ st b := by unfold BQ; omega
  refine LabelSystem.net_is _ boolCode hP1 hB1 (fun a => ?_) (fun a ℓ y => ?_)
  · have h1 := card_inc_le st g n M z₁ z₂ z₃ xs ys hg2 a
    have h2 := card_blocksOf_le st g a.val
    have h3 : #(Finset.univ.filter ((qSys st g n M z₁ z₂ z₃ xs ys).Touch a)) = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro j; exact j.elim
    rw [h3, mul_one, add_zero]
    unfold PQ; generalize st.1.length / g = y at h2; generalize #(blocksOf st g a.val) = z at h1 h2; omega
  · show |(qT st g n M z₁ z₂ z₃ xs ys a ℓ)| < 2 ^ BQ st b
    unfold qT
    rw [abs_of_nonneg (by positivity)]
    have hM0 : 0 < M := by rw [hM]; unfold Mb; positivity
    have h1 := streamN_lt hM0 (descN st g n M z₁ z₂ z₃ xs ys a.val) (zOf st g a.val ℓ)
      (N := (ilN st g a.val).length)
    have h2 := length_ilN_le' st g a.val
    have h3 : M ≤ 2 ^ (4 * b + 1) := by
      subst hM; unfold Mb; rw [pow_succ]; have : 1 ≤ 2 ^ (4 * b) := Nat.one_le_two_pow; omega
    have h4 : 2 ^ (ilN st g a.val).length * M ≤ 2 ^ (2 * st.1.length) * 2 ^ (4 * b + 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h2) h3
    have h5 : 2 ^ (2 * st.1.length) * 2 ^ (4 * b + 1) < 2 ^ BQ st b := by
      rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by unfold BQ; omega)
    exact_mod_cast (h1.trans_le h4).trans h5

end Count

end EthFollowup.Quantum
