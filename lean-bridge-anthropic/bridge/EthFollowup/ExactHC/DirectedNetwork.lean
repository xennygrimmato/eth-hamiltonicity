/-
# The directed (ATSP) network in Anthropic's `Net g` format

`research/tsp-theorem.md` §3.3 (network of Theorem TSP-2). This mirrors `HCNetwork.lean` and
`WeightedNetwork.lean` with the directed tables of `DirectedBlobs.lean`: the node table of blob `a`
is `T_a(ℓ, y) = σ_a(ℓ) · χ_a(ℓ, y^{(a)}) · I^w_a(ℓ)` over the three labels `L_d = {N, 0, 2}`.

For a digraph `A` on `Fin n`, a root `r`, a partition `β : Fin n → Fin g`, a directed crossing
order `X : DCrossing A β m`, an integer `z` (the Kronecker point `z = 2^b`) and arc weights `w`:

* `X.dSystemW r z w : LabelSystem g (Fin m) (CopyIdx g) DLabel` (items: the crossing arcs on their
  chords `a_k < b_k`; copy bits `(a, c, d)` as in `HCNetwork.lean`);
* `dlabelCode : LabelCode DLabel 2` (`λ = 3`, `⌈log₂ 3⌉ = 2`);
* **Value** `dNetW_value : ((X.dSystemW r z w).net C).value = Σ_{H ∈ DHC(A)} z^{w(H)}` (no factor `n`);
  `dNetW_kron`: at `z = 2^b` the value is `Σ_H 2^{b·w(H)}`, whose base-`2^b` digits are the numbers
  of directed tours of each weight (`dkronecker_decode`);
* **Size**: `abs_dIw_le : |I^w_a| ≤ 2^{bW(|δ(a)| + |A_int(a)|)} · 4^{|A_int(a)|} · 2^{|δ(a)|}`;
  `dmu A β a = Σ_{v∈V_a} (d⁺(v) + d⁻(v))`, `two_Aint_add_delta_le : 2|A_int(a)| + |δ(a)| ≤ μ_a`;
  `abs_dTW_lt : |T_a| < 2^{bWμ + 2μ + 1}`;
* **Definition 2**: `dNetW_is : Is (q·μ + g² + 1) (bWμ + 2μ + 1)`, `dNetW_is_labelCode`
  (`q = 2`), `dNetW_U : U = 2(q·m + #CopyIdx g)`, `dNetW_U_le`.
-/
import EthFollowup.ExactHC.DirectedWeighted
import EthFollowup.ExactHC.WeightedNetwork

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset Grass

noncomputable section

/-! ### `ℓ¹`-norms of the directed factors and pieces -/

section Norms

variable {n : ℕ}

theorem norm1_pArc_le (r : Fin n) (a : Fin n × Fin n) : norm1 (pArc r a) ≤ 2 := by
  unfold pArc
  refine (norm1_mul_le _ _).trans ?_
  have h1 := norm1_psibar_le r a.1
  have h2 := (norm1_sub_le (psi r a.1) (psi r a.2)).trans
    (add_le_add (norm1_psi_le r a.1) (norm1_psi_le r a.2))
  have := norm1_nonneg (psibar r a.1)
  have := norm1_nonneg (psi r a.1 - psi r a.2)
  nlinarith

theorem norm1_one_add_pArc_le (r : Fin n) (a : Fin n × Fin n) : norm1 (1 + pArc r a) ≤ 3 := by
  refine (norm1_add_le _ _).trans ?_
  rw [norm1_one]
  have := norm1_pArc_le r a
  linarith

theorem norm1_arcProd_le (r : Fin n) (x : Finset (Fin n × Fin n)) :
    norm1 (arcProd r x) ≤ 3 ^ x.card := by
  unfold arcProd
  have := norm1_list_prod_le 3 (x.toList.map fun a => 1 + pArc r a) (by
    intro y hy
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
    exact norm1_one_add_pArc_le r a)
  rwa [List.length_map, length_toList] at this

theorem norm1_dpieceA_le (r : Fin n) (tl : Bool) (s : Fin n) (ℓ : DLabel) :
    norm1 (dpieceA r tl s ℓ) ≤ 2 := by
  cases ℓ <;> cases tl <;> simp only [dpieceA, Bool.false_eq_true, if_false, if_true]
  · rw [norm1_one]; norm_num
  · rw [norm1_one]; norm_num
  · rw [norm1_one]; norm_num
  · refine (norm1_add_le _ _).trans ?_
    rw [norm1_one]; have := norm1_omega_le r s; unfold omega at this; linarith
  · exact (norm1_psi_le r s).trans (by norm_num)
  · exact (norm1_psibar_le r s).trans (by norm_num)

theorem norm1_dpieceB_le (r : Fin n) (tl : Bool) (t : Fin n) (ℓ : DLabel) :
    norm1 (dpieceB r tl t ℓ) ≤ 2 := by
  cases ℓ <;> cases tl <;> simp only [dpieceB, Bool.false_eq_true, if_false, if_true]
  · rw [norm1_one]; norm_num
  · rw [norm1_one]; norm_num
  · refine (norm1_add_le _ _).trans ?_
    rw [norm1_one]; have := norm1_omega_le r t; unfold omega at this; linarith
  · rw [norm1_one]; norm_num
  · exact (norm1_psibar_le r t).trans (by norm_num)
  · rw [norm1_neg]; exact (norm1_psi_le r t).trans (by norm_num)

end Norms

/-! ### Degree sums -/

section Degrees

variable {n g m : ℕ} {A : Finset (Fin n × Fin n)} {β : Fin n → Fin g}

/-- `μ_a = Σ_{v ∈ V_a} (d⁺(v) + d⁻(v))` (in- plus out-degrees). -/
def dmu (A : Finset (Fin n × Fin n)) (β : Fin n → Fin g) (a : Fin g) : ℕ :=
  ∑ v ∈ blob β a, (DCrossing.pdeg Prod.fst A v + DCrossing.pdeg Prod.snd A v)

theorem dmu_eq_sum_arcs (a : Fin g) :
    dmu A β a = ∑ e ∈ A, ((if e.1 ∈ blob β a then 1 else 0) + (if e.2 ∈ blob β a then 1 else 0)) := by
  unfold dmu DCrossing.pdeg
  simp only [card_filter, sum_add_distrib]
  rw [sum_comm, sum_comm (s := blob β a)]
  congr 1 <;> refine sum_congr rfl fun e _ => ?_ <;> rw [sum_ite_eq]

namespace DCrossing

variable (X : DCrossing A β m)

/-- Each internal arc has both ends in `V_a`, each crossing arc at `a` exactly one. -/
theorem two_Aint_add_delta_le (a : Fin g) :
    2 * (Aint A β a).card + (X.chords.delta a).card ≤ dmu A β a := by
  classical
  rw [dmu_eq_sum_arcs]
  set N : Fin n × Fin n → ℕ :=
    fun e => (if e.1 ∈ blob β a then 1 else 0) + (if e.2 ∈ blob β a then 1 else 0)
  have hdisj : Disjoint (Aint A β a) ((X.chords.delta a).image X.arc) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.arc_not_mem_Aint k a he
  have hsub : Aint A β a ∪ (X.chords.delta a).image X.arc ⊆ A := by
    intro e he
    rcases mem_union.1 he with he | he
    · exact Aint_subset a he
    · obtain ⟨k, -, rfl⟩ := mem_image.1 he
      exact X.arc_mem k
  have h1 : ∀ e ∈ Aint A β a, 2 ≤ N e := by
    intro e he
    obtain ⟨-, h1, h2⟩ := mem_Aint.1 he
    simp [N, mem_blob, h1, h2]
  have h2 : ∀ k ∈ X.chords.delta a, 1 ≤ N (X.arc k) := by
    intro k hk
    rw [X.mem_delta] at hk
    have : (X.arc k).1 ∈ blob β a ∨ (X.arc k).2 ∈ blob β a := by
      rw [mem_blob, mem_blob]
      rcases X.arc_ends k with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hk with hk | hk
      · exact Or.inl (by rw [e1, hk])
      · exact Or.inr (by rw [e2, hk])
      · exact Or.inr (by rw [e2, hk])
      · exact Or.inl (by rw [e1, hk])
    rcases this with h | h <;> simp only [N, h, if_true] <;> omega
  calc 2 * (Aint A β a).card + (X.chords.delta a).card
      = ∑ _e ∈ Aint A β a, 2 + ∑ _k ∈ X.chords.delta a, 1 := by
        simp [mul_comm]
    _ ≤ ∑ e ∈ Aint A β a, N e + ∑ k ∈ X.chords.delta a, N (X.arc k) :=
        add_le_add (sum_le_sum h1) (sum_le_sum h2)
    _ = ∑ e ∈ Aint A β a ∪ (X.chords.delta a).image X.arc, N e := by
        rw [sum_union hdisj, sum_image fun k _ l _ h => X.arc_injective h]
    _ ≤ ∑ e ∈ A, N e := sum_le_sum_of_subset hsub

theorem card_delta_le_dmu (a : Fin g) : (X.chords.delta a).card ≤ dmu A β a :=
  le_trans (Nat.le_add_left _ _) (X.two_Aint_add_delta_le a)

end DCrossing

end Degrees

/-! ### The size of the directed blob sum -/

namespace DCrossing

variable {n g m : ℕ} {A : Finset (Fin n × Fin n)} {β : Fin n → Fin g} (X : DCrossing A β m)
  (r : Fin n) (z : ℤ) (w : Fin n × Fin n → ℕ)

theorem norm1_Gam_le (ℓ : Fin m → DLabel) (a : Fin g) :
    norm1 (X.Gam r ℓ a) ≤ 2 ^ (X.chords.delta a).card := by
  unfold Gam
  have := norm1_list_prod_le 2 (((X.chords.delta a).sort (· ≤ ·)).map fun k => X.piece r ℓ k a) (by
    intro y hy
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy
    unfold piece; split_ifs
    · exact norm1_dpieceA_le _ _ _ _
    · exact norm1_dpieceB_le _ _ _ _)
  rwa [List.length_map, length_sort] at this

theorem arcWt_le_of_subset {W : ℕ} (hw : ∀ e, w e ≤ W) {x Y : Finset (Fin n × Fin n)}
    (hx : x ⊆ Y) : arcWt w x ≤ Y.card * W :=
  (arcWt_le_card_mul hw x).trans (Nat.mul_le_mul_right W (card_le_card hx))

/-- **The size of the directed blob sum**: with `|z| ≤ 2^b` and all weights `≤ W`,
`|I^w_a(ℓ)| ≤ 2^{bW(|δ(a)| + |A_int(a)|)} · 4^{|A_int(a)|} · 2^{|δ(a)|}`. -/
theorem abs_Iw_le {W b : ℕ} (hw : ∀ e, w e ≤ W) (hz : |z| ≤ 2 ^ b) (ℓ : Fin m → DLabel)
    (a : Fin g) :
    |X.Iw r z w ℓ a| ≤
      2 ^ (b * (W * ((X.chords.delta a).card + (Aint A β a).card))) *
        (4 ^ (Aint A β a).card * 2 ^ (X.chords.delta a).card) := by
  unfold Iw
  rw [abs_mul]
  have hA : |z ^ X.wtL w ℓ a| ≤ 2 ^ (b * ((X.chords.delta a).card * W)) :=
    abs_pow_le_two_pow hz (X.wtL_le w hw ℓ a)
  have hB : |∑ x ∈ (Aint A β a).powerset, X.degInd ℓ a x * z ^ arcWt w x *
        topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (arcProd r x * X.Gam r ℓ a)| ≤
      2 ^ (b * ((Aint A β a).card * W)) *
        (4 ^ (Aint A β a).card * 2 ^ (X.chords.delta a).card) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ (Aint A β a).powerset, |X.degInd ℓ a x * z ^ arcWt w x *
          topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (arcProd r x * X.Gam r ℓ a)|
        ≤ ∑ x ∈ (Aint A β a).powerset, (2 : ℤ) ^ (b * ((Aint A β a).card * W)) *
            ((3 : ℤ) ^ x.card * 2 ^ (X.chords.delta a).card) := by
          refine sum_le_sum fun x hx => ?_
          rw [abs_mul, abs_mul]
          have h1 : |X.degInd ℓ a x| ≤ 1 := by unfold degInd; split_ifs <;> simp
          have h2 : |z ^ arcWt w x| ≤ 2 ^ (b * ((Aint A β a).card * W)) :=
            abs_pow_le_two_pow hz (arcWt_le_of_subset w hw (mem_powerset.1 hx))
          have h3 := (abs_topCoeff_le (isSignedBasis_OmegaSet r (blob β a)) _).trans
            ((norm1_mul_le _ _).trans (mul_le_mul (norm1_arcProd_le r x) (X.norm1_Gam_le r ℓ a)
              (norm1_nonneg _) (by positivity)))
          calc |X.degInd ℓ a x| * |z ^ arcWt w x| * |topCoeff (genSet r (blob β a))
                (OmegaSet r (blob β a)) (arcProd r x * X.Gam r ℓ a)|
              ≤ 1 * 2 ^ (b * ((Aint A β a).card * W)) *
                  ((3 : ℤ) ^ x.card * 2 ^ (X.chords.delta a).card) :=
                mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3 (abs_nonneg _)
                  (by positivity)
            _ = _ := by ring
      _ = 2 ^ (b * ((Aint A β a).card * W)) *
            (4 ^ (Aint A β a).card * 2 ^ (X.chords.delta a).card) := by
          rw [← mul_sum, ← sum_mul]
          congr 2
          have := sum_pow_mul_eq_add_pow (3 : ℤ) 1 (Aint A β a)
          simp only [one_pow, mul_one] at this
          rw [this]; norm_num
  calc |z ^ X.wtL w ℓ a| * |∑ x ∈ (Aint A β a).powerset, X.degInd ℓ a x * z ^ arcWt w x *
        topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (arcProd r x * X.Gam r ℓ a)|
      ≤ 2 ^ (b * ((X.chords.delta a).card * W)) * (2 ^ (b * ((Aint A β a).card * W)) *
          (4 ^ (Aint A β a).card * 2 ^ (X.chords.delta a).card)) :=
        mul_le_mul hA hB (abs_nonneg _) (by positivity)
    _ = _ := by
        rw [show b * (W * ((X.chords.delta a).card + (Aint A β a).card)) =
          b * ((X.chords.delta a).card * W) + b * ((Aint A β a).card * W) by ring, pow_add]
        ring

/-! ### The directed label system -/

/-- **The directed network** (§3.3): items are the crossing arcs `k` (on the chord `a_k < b_k`),
labels `L_d`, copy bit `(a,c,d)` held by `a`, computed by `c`, equal to `P_{cd}(ℓ)`; node tables
`T_a(ℓ, y) = σ_a(ℓ) · χ_a(ℓ, y^{(a)}) · I^w_a(ℓ)`. -/
def dSystemW : LabelSystem g (Fin m) (CopyIdx g) DLabel where
  kord := List.finRange m
  kord_nodup := List.nodup_finRange m
  mem_kord := List.mem_finRange
  rord := copyList g
  rord_nodup := copyList_nodup g
  mem_rord := mem_copyList
  lo := X.chords.a
  hi := X.chords.b
  lo_lt := X.chords.a_lt_b
  holder j := j.1.1
  source j := j.1.2.1
  holder_ne j := j.2.1.ne
  dflt := DLabel.N
  par j ℓ := zToBool (X.chords.P (dlabelPar ℓ) j.1.2.1 j.1.2.2)
  T a ℓ y := X.chords.sigma (dlabelPar ℓ) a * X.chords.chi (dlabelPar ℓ) a (copyVec a y) *
    X.Iw r z w ℓ a
  par_local j ℓ ℓ' h := by
    rw [X.P_congr (c := j.1.2.1) (ℓ' := ℓ') (fun k hk => h k (X.mem_delta.1 hk))]
  T_local a ℓ ℓ' y y' hℓ hy := by
    have hd : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k := fun k hk => hℓ k (X.mem_delta.1 hk)
    have hc : ∀ p ∈ Chords.Q a, copyVec a y p = copyVec a y' p := by
      intro p hp
      simp only [Chords.Q, mem_filter, mem_univ, true_and] at hp
      simp only [copyVec, dif_pos hp]
      rw [hy _ rfl]
    rw [X.sigma_congr hd, X.chi_congr hd hc, X.Iw_congr r z w hd]

@[simp] theorem dSystemW_T (a : Fin g) (ℓ : Fin m → DLabel) (y : CopyIdx g → Bool) :
    (X.dSystemW r z w).T a ℓ y =
      X.chords.sigma (dlabelPar ℓ) a * X.chords.chi (dlabelPar ℓ) a (copyVec a y) *
        X.Iw r z w ℓ a := rfl

/-- The node table fed the correct copy bits is `σ_a χ_a(P) I^w_a`. -/
theorem dSystemW_T_par (a : Fin g) (ℓ : Fin m → DLabel) :
    (X.dSystemW r z w).T a ℓ (fun j => (X.dSystemW r z w).par j ℓ) =
      X.chords.sigma (dlabelPar ℓ) a *
        X.chords.chi (dlabelPar ℓ) a (fun p => X.chords.P (dlabelPar ℓ) p.1 p.2) *
        X.Iw r z w ℓ a := by
  rw [dSystemW_T]
  congr 2
  refine X.chi_congr (fun _ _ => rfl) fun p hp => ?_
  simp only [Chords.Q, mem_filter, mem_univ, true_and] at hp
  simp only [copyVec, dif_pos hp]
  exact boolToZ_zToBool _

variable {q : ℕ} (C : LabelCode DLabel q)

/-- **The value of the directed network** is `Σ_{H ∈ DHC(A)} z^{w(H)}` (Theorem 1.4 with the
directed data; no factor `n`). -/
theorem dNetW_value :
    ((X.dSystemW r z w).net C).value =
      ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H := by
  rw [LabelSystem.value_net, ← dblob_factorisation_w X r z w]
  exact sum_congr rfl fun ℓ _ => prod_congr rfl fun a _ => X.dSystemW_T_par r z w a ℓ

/-! ### The parameters -/

theorem abs_dTW_le {W b : ℕ} (hw : ∀ e, w e ≤ W) (hz : |z| ≤ 2 ^ b) (a : Fin g)
    (ℓ : Fin m → DLabel) (y : CopyIdx g → Bool) :
    |(X.dSystemW r z w).T a ℓ y| ≤
      2 ^ (b * (W * ((X.chords.delta a).card + (Aint A β a).card)) +
        (2 * (Aint A β a).card + (X.chords.delta a).card)) := by
  rw [dSystemW_T, abs_mul, abs_mul]
  have hs : ∀ x : ZMod 2, |sgn x| = 1 := fun x => by
    rcases sgn_eq_one_or_neg_one x with h | h <;> simp [h]
  rw [Chords.sigma, Chords.chi, hs, hs, one_mul, one_mul, pow_add]
  refine (X.abs_Iw_le r z w hw hz ℓ a).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [pow_add, pow_mul]
  norm_num

/-- **The bound `B = bWμ + 2μ + 1`**: `|T_a(ℓ, y)| < 2^{bWμ + 2μ + 1}` for `μ ≥ max_a μ_a`. -/
theorem abs_dTW_lt (μ W b : ℕ) (hμ : ∀ a, dmu A β a ≤ μ) (hw : ∀ e, w e ≤ W)
    (hz : |z| ≤ 2 ^ b) (a : Fin g) (ℓ : Fin m → DLabel) (y : CopyIdx g → Bool) :
    |(X.dSystemW r z w).T a ℓ y| < 2 ^ (b * W * μ + 2 * μ + 1) := by
  refine (X.abs_dTW_le r z w hw hz a ℓ y).trans_lt (pow_lt_pow_right₀ (by norm_num) ?_)
  have h1 := X.two_Aint_add_delta_le a
  have h2 := hμ a
  have h3 : b * (W * ((X.chords.delta a).card + (Aint A β a).card)) ≤ b * W * μ := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have h4 : 2 * (Aint A β a).card + (X.chords.delta a).card < 2 * μ + 1 := by omega
  linarith

/-- The items incident to `a` are the crossing arcs `δ(a)`. -/
theorem dSystemW_card_inc (a : Fin g) :
    #(univ.filter ((X.dSystemW r z w).Inc a)) = (X.chords.delta a).card := rfl

/-- The copy bits touching `a` (held by `a`, or computed at `a`) number at most `g²`. -/
theorem dSystemW_card_touch_le (a : Fin g) :
    #(univ.filter ((X.dSystemW r z w).Touch a)) ≤ g ^ 2 := by
  have h := card_le_card_of_injOn
    (fun j : CopyIdx g => if j.1.1 = a then (j.1.2.1, j.1.2.2) else (j.1.1, j.1.2.2))
    (s := univ.filter ((X.dSystemW r z w).Touch a)) (t := (univ : Finset (Fin g × Fin g)))
    (fun _ _ => by simp) ?_
  · rwa [card_univ, Fintype.card_prod, Fintype.card_fin, ← sq] at h
  · rintro ⟨⟨a1, c1, d1⟩, h1⟩ hj ⟨⟨a2, c2, d2⟩, h2⟩ hj' heq
    replace hj : a1 = a ∨ c1 = a := (mem_filter.1 (mem_coe.1 hj)).2
    replace hj' : a2 = a ∨ c2 = a := (mem_filter.1 (mem_coe.1 hj')).2
    simp only at h1 h2 heq
    refine Subtype.ext ?_
    simp only [Fin.lt_def, Fin.ext_iff] at h1 h2 hj hj' ⊢
    split_ifs at heq with ha1 ha2 ha2 <;>
      simp only [Prod.mk.injEq, Fin.ext_iff] at heq ha1 ha2 <;>
      simp only [Prod.mk.injEq, Fin.ext_iff] <;> omega

/-- **Definition 2 for the directed network**: `Is (q·μ + g² + 1) (b·W·μ + 2μ + 1)` for a `q`-bit
label code, `μ ≥ max_a μ_a`, weights `≤ W` and `|z| ≤ 2^b`. -/
theorem dNetW_is (μ W b : ℕ) (hμ : ∀ a, dmu A β a ≤ μ) (hw : ∀ e, w e ≤ W)
    (hz : |z| ≤ 2 ^ b) :
    ((X.dSystemW r z w).net C).Is (q * μ + g ^ 2 + 1) (b * W * μ + 2 * μ + 1) :=
  (X.dSystemW r z w).net_is C (by omega) (by omega)
    (fun a => by
      rw [dSystemW_card_inc]
      have h2 := X.dSystemW_card_touch_le r z w a
      have h3 := Nat.mul_le_mul_right q ((X.card_delta_le_dmu a).trans (hμ a))
      linarith)
    fun a ℓ y => X.abs_dTW_lt r z w μ W b hμ hw hz a ℓ y

/-- **Kronecker substitution** `z = 2^b`: value `Σ_H 2^{b·w(H)}` (as the cast of a natural number)
and `Is (q·μ + g² + 1) (bWμ + 2μ + 1)`. -/
theorem dNetW_kron (μ W b : ℕ) (hμ : ∀ a, dmu A β a ≤ μ) (hw : ∀ e, w e ≤ W) :
    ((X.dSystemW r (2 ^ b) w).net C).value =
        ((∑ H ∈ DirectedHamiltonian.dirHamCycles A, 2 ^ (b * arcWt w H) : ℕ) : ℤ) ∧
      ((X.dSystemW r (2 ^ b) w).net C).Is (q * μ + g ^ 2 + 1) (b * W * μ + 2 * μ + 1) := by
  refine ⟨?_, X.dNetW_is r (2 ^ b) w C μ W b hμ hw (Crossing.abs_two_pow_le b)⟩
  rw [X.dNetW_value r (2 ^ b) w C]
  push_cast
  simp only [pow_mul]

/-- The total `U = 2(q·m + #copy bits)`. -/
theorem dNetW_U : ((X.dSystemW r z w).net C).U = 2 * (m * q + Fintype.card (CopyIdx g)) := by
  rw [LabelSystem.U_eq, Fintype.card_fin]

theorem dNetW_U_le : ((X.dSystemW r z w).net C).U ≤ 2 * (m * q + g ^ 3) := by
  rw [dNetW_U]; have := Crossing.card_copyIdx_le g; omega

end DCrossing

/-! ### The 2-bit label code -/

namespace DLabel

/-- `κ : L_d → {0,1,2}`, `κ(N) = 0`. -/
def toFin : DLabel → Fin 3
  | N => 0
  | d0 => 1
  | d2 => 2

/-- The inverse of `κ`. -/
def ofFin (i : Fin 3) : DLabel :=
  match i with
  | 0 => N
  | 1 => d0
  | 2 => d2

theorem ofFin_toFin (l : DLabel) : ofFin (toFin l) = l := by cases l <;> rfl

end DLabel

theorem clog_two_three : Nat.clog 2 3 = 2 := by decide

/-- The 2-bit binary code of the directed labels (via `κ`). -/
def dlabelCode : LabelCode DLabel 2 where
  enc l := (finCode 2).enc l.toFin
  dec z := DLabel.ofFin ((finCode 2).dec z)
  len l := by rw [(finCode 2).len]; exact clog_two_three
  dec_enc l := by rw [(finCode 2).dec_enc, DLabel.ofFin_toFin]

namespace DCrossing

variable {n g m : ℕ} {A : Finset (Fin n × Fin n)} {β : Fin n → Fin g} (X : DCrossing A β m)
  (r : Fin n) (z : ℤ) (w : Fin n × Fin n → ℕ)

/-- **Definition 2** for the 2-bit code: `Is (2μ + g² + 1) (bWμ + 2μ + 1)`. -/
theorem dNetW_is_labelCode (μ W b : ℕ) (hμ : ∀ a, dmu A β a ≤ μ) (hw : ∀ e, w e ≤ W)
    (hz : |z| ≤ 2 ^ b) :
    ((X.dSystemW r z w).net dlabelCode).Is (2 * μ + g ^ 2 + 1) (b * W * μ + 2 * μ + 1) :=
  X.dNetW_is r z w dlabelCode μ W b hμ hw hz

/-- The value for the 2-bit code. -/
theorem dNetW_value_labelCode :
    ((X.dSystemW r z w).net dlabelCode).value =
      ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H :=
  X.dNetW_value r z w dlabelCode

end DCrossing

end

end EthFollowup.ExactHC
