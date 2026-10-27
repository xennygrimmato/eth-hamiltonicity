/-
# The Hamiltonian-cycle network of §5 (module M7)

Write-up: `research/exact-hc-theorem.md`, Definition 5.1, Lemma 5.2, Theorem 5.3, Proposition 5.4.
We instantiate the generic label-sharing network of C1a (`LabelNetwork.lean`) with the tables of
§4 (`Blobs.lean`, `Main.lean`).

For a graph `G` on `Fin n` (`DecidableRel G.Adj`), a root `r`, a partition `β : Fin n → Fin g` and a
crossing order `X : Crossing G β m`:

* `X.hcSystem r : LabelSystem g (Fin m) (CopyIdx g) Label`: item `k` sits on `a_k = β (s k) <
  b_k = β (t k)`; copy bit `(a,c,d)` (`a < c < d`) is held by `a`, computed by `c`, with value
  `zToBool (P_{cd}(ℓ))`; `T a ℓ y = σ_a(ℓ) · χ_a(ℓ, copyVec a y) · I_a(ℓ)`.
  The copy bits held by `a` are exactly the triples `(a,c,d)` with `(c,d) ∈ Q_a`
  (`held_iff_mem_Q`), and `copyVec a y` reads them on `Q_a`.
* `labelCode : LabelCode Label 3` (`κ : Label → Fin 5`, then `finCode 4`; `Nat.clog 2 5 = 3`).

## Results
* **Theorem 5.3** `hcNet_value : ((X.hcSystem r).net C).value = n * #(hamCycles G)` for every code
  `C : LabelCode Label w` (and `hcNet_value_labelCode`).
* `Grass.norm1` (`ℓ¹`-norm of coefficients), `norm1_mul_le` (submultiplicative),
  `norm1_list_prod_le`, `abs_topCoeff_le`; `abs_I_le : |I_a(ℓ)| ≤ 6^{|E_int(a)|} · 2^{|δ(a)|}`.
* `mu G β a = Σ_{v ∈ V_a} deg_G v`, `two_Eint_add_delta_le : 2|E_int(a)| + |δ(a)| ≤ μ_a`.
* `abs_hcT_le : |T a ℓ y| ≤ 2^{3|E_int(a)| + |δ(a)|}`, `abs_hcT_lt : |T a ℓ y| < 2^{2μ_a + 1}`.
* `hcNet_sum_c : Σ_{b≠a} c a b = |δ(a)|·w + #(copy bits touching a)`,
  `hcSystem_card_touch_le : #(copy bits touching a) ≤ g²`, `hcNet_sum_c_le : … ≤ w·μ_a + g²`.
* **Proposition 5.4** `hcNet_is (μ) (hμ : ∀ a, mu G β a ≤ μ) : (net C).Is (w·μ + g² + 1) (2μ + 1)`,
  `hcNet_is_labelCode : … Is (3μ + g² + 1) (2μ + 1)`, and the general `hcNet_is'`.
* `hcNet_U : U = 2(m·w + #CopyIdx g)`, `card_copyIdx_le : #CopyIdx g ≤ g³`, `hcNet_U_le`.
-/
import EthFollowup.ExactHC.Main
import EthFollowup.ExactHC.LabelNetwork

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

noncomputable section

namespace Grass

variable {Γ : Type*} [Fintype Γ] [LinearOrder Γ]

/-- The `ℓ¹`-norm of the coefficient vector. -/
def norm1 (x : Grass Γ) : ℤ := ∑ S, |x.coeff S|

theorem norm1_nonneg (x : Grass Γ) : 0 ≤ norm1 x := sum_nonneg fun _ _ => abs_nonneg _

theorem abs_coeff_le_norm1 (x : Grass Γ) (S : Finset Γ) : |x.coeff S| ≤ norm1 x :=
  single_le_sum (f := fun S => |x.coeff S|) (fun _ _ => abs_nonneg _) (mem_univ S)

theorem norm1_add_le (x y : Grass Γ) : norm1 (x + y) ≤ norm1 x + norm1 y := by
  unfold norm1
  rw [← sum_add_distrib]
  exact sum_le_sum fun S _ => by rw [coeff_add]; exact abs_add_le _ _

theorem norm1_neg (x : Grass Γ) : norm1 (-x) = norm1 x := by
  simp [norm1]

theorem norm1_sub_le (x y : Grass Γ) : norm1 (x - y) ≤ norm1 x + norm1 y := by
  rw [sub_eq_add_neg, ← norm1_neg y]; exact norm1_add_le _ _

theorem norm1_zero : norm1 (0 : Grass Γ) = 0 := by simp [norm1]

theorem norm1_e (S : Finset Γ) : norm1 (e S) = 1 := by
  unfold norm1
  rw [sum_eq_single S (fun U _ hU => by rw [coeff_e_of_ne (Ne.symm hU), abs_zero])
    (fun h => absurd (mem_univ S) h), coeff_e_self, abs_one]

theorem norm1_one : norm1 (1 : Grass Γ) = 1 := norm1_e ∅

theorem norm1_gen (γ : Γ) : norm1 (gen γ) = 1 := norm1_e _

theorem sum_abs_structConst_le (S T : Finset Γ) : ∑ U, |structConst S T U| ≤ 1 := by
  rw [sum_eq_single (S ∪ T)]
  · unfold structConst
    split_ifs
    · rcases mergeSign_eq_or S T with h | h <;> simp [h]
    · simp
  · intro U _ hU
    unfold structConst
    rw [if_neg (fun h => hU h.2.symm), abs_zero]
  · exact fun h => absurd (mem_univ _) h

/-- **Submultiplicativity of the `ℓ¹`-norm** in the Grassmann algebra. -/
theorem norm1_mul_le (x y : Grass Γ) : norm1 (x * y) ≤ norm1 x * norm1 y := by
  unfold norm1
  calc ∑ U, |(x * y).coeff U|
      ≤ ∑ U, ∑ S, ∑ T, |structConst S T U| * (|x.coeff S| * |y.coeff T|) := by
        refine sum_le_sum fun U _ => ?_
        rw [coeff_mul]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun S _ =>
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun T _ => ?_))
        rw [abs_mul, abs_mul]
    _ = ∑ S, ∑ T, (∑ U, |structConst S T U|) * (|x.coeff S| * |y.coeff T|) := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        rw [sum_comm]
        simp only [sum_mul]
    _ ≤ ∑ S, ∑ T, |x.coeff S| * |y.coeff T| := by
        refine sum_le_sum fun S _ => sum_le_sum fun T _ => ?_
        exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (sum_abs_structConst_le S T)
    _ = (∑ S, |x.coeff S|) * ∑ T, |y.coeff T| := by rw [sum_mul_sum]

theorem norm1_list_prod_le (c : ℤ) :
    ∀ l : List (Grass Γ), (∀ x ∈ l, norm1 x ≤ c) → norm1 l.prod ≤ c ^ l.length
  | [], _ => by simp [norm1_one]
  | x :: l, h => by
    rw [List.prod_cons, List.length_cons, pow_succ]
    have hx := h x List.mem_cons_self
    have hl := norm1_list_prod_le c l fun y hy => h y (List.mem_cons_of_mem _ hy)
    calc norm1 (x * l.prod) ≤ norm1 x * norm1 l.prod := norm1_mul_le _ _
      _ ≤ c * c ^ l.length :=
        mul_le_mul hx hl (norm1_nonneg _) ((norm1_nonneg x).trans hx)
      _ = c ^ l.length * c := mul_comm _ _

theorem abs_topCoeff_le {A : Finset Γ} {ω : Grass Γ} (hω : IsSignedBasis A ω) (x : Grass Γ) :
    |topCoeff A ω x| ≤ norm1 x := by
  unfold topCoeff
  have h1 : |ω.coeff A| = 1 := by
    rcases hω with rfl | rfl <;> simp
  rw [abs_mul, h1, mul_one]
  exact abs_coeff_le_norm1 x A

end Grass

open Grass

/-! ### `ℓ¹`-norms of the generators, the edge factors and the pieces -/

section Norms

variable {n : ℕ}

theorem norm1_psibar_le (r v : Fin n) : norm1 (psibar r v) ≤ 1 := by
  unfold psibar; split_ifs
  · rw [norm1_zero]; norm_num
  · rw [norm1_gen]

theorem norm1_psi_le (r v : Fin n) : norm1 (psi r v) ≤ 1 := by
  unfold psi; split_ifs
  · rw [norm1_zero]; norm_num
  · rw [norm1_gen]

theorem norm1_omega_le (r v : Fin n) : norm1 (omega r v) ≤ 1 :=
  (norm1_mul_le _ _).trans (by
    have := norm1_psibar_le r v; have := norm1_psi_le r v
    have := norm1_nonneg (psibar r v); have := norm1_nonneg (psi r v); nlinarith)

theorem norm1_qPair_le (r i j : Fin n) : norm1 (qPair r i j) ≤ 4 := by
  unfold qPair
  refine (norm1_mul_le _ _).trans ?_
  have h1 := (norm1_sub_le (psibar r i) (psibar r j)).trans
    (add_le_add (norm1_psibar_le r i) (norm1_psibar_le r j))
  have h2 := (norm1_sub_le (psi r i) (psi r j)).trans
    (add_le_add (norm1_psi_le r i) (norm1_psi_le r j))
  have := norm1_nonneg (psibar r i - psibar r j)
  have := norm1_nonneg (psi r i - psi r j)
  nlinarith

theorem norm1_one_add_qEdge_le (r : Fin n) (e : Sym2 (Fin n)) : norm1 (1 + qEdge r e) ≤ 5 := by
  refine (norm1_add_le _ _).trans ?_
  rw [norm1_one]
  induction e using Sym2.ind with
  | _ i j => have := norm1_qPair_le r i j; rw [qEdge_mk]; linarith

theorem norm1_pieceA_le (r s : Fin n) (ℓ : Label) : norm1 (pieceA r s ℓ) ≤ 2 := by
  cases ℓ <;> simp only [pieceA]
  · rw [norm1_one]; norm_num
  · rw [norm1_one]; norm_num
  · exact (norm1_omega_le r s).trans (by norm_num)
  · exact (norm1_psibar_le r s).trans (by norm_num)
  · exact (norm1_psi_le r s).trans (by norm_num)

theorem norm1_pieceB_le (r t : Fin n) (ℓ : Label) : norm1 (pieceB r t ℓ) ≤ 2 := by
  cases ℓ <;> simp only [pieceB]
  · rw [norm1_one]; norm_num
  · refine (norm1_add_le _ _).trans ?_
    rw [norm1_one]; have := norm1_omega_le r t; unfold omega at this; linarith
  · rw [norm1_one]; norm_num
  · rw [norm1_neg]; exact (norm1_psi_le r t).trans (by norm_num)
  · exact (norm1_psibar_le r t).trans (by norm_num)

theorem norm1_edgeProd_le (r : Fin n) (x : Finset (Sym2 (Fin n))) :
    norm1 (edgeProd r x) ≤ 5 ^ x.card := by
  unfold edgeProd
  have := norm1_list_prod_le 5 (x.toList.map fun e => 1 + qEdge r e) (by
    intro y hy
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    exact norm1_one_add_qEdge_le r e)
  rwa [List.length_map, length_toList] at this

end Norms

namespace Crossing

variable {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
  (X : Crossing G β m) (r : Fin n)

theorem norm1_Gam_le (ℓ : Fin m → Label) (a : Fin g) :
    norm1 (X.Gam r ℓ a) ≤ 2 ^ (X.chords.delta a).card := by
  unfold Gam
  have := norm1_list_prod_le 2 (((X.chords.delta a).sort (· ≤ ·)).map fun k => X.piece r ℓ k a) (by
    intro y hy
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy
    unfold piece; split_ifs
    · exact norm1_pieceA_le _ _ _
    · exact norm1_pieceB_le _ _ _)
  rwa [List.length_map, length_sort] at this

/-- **The size of the blob sum**: `|I_a(ℓ)| ≤ 6^{|E_int(a)|} · 2^{|δ(a)|}`. -/
theorem abs_I_le (ℓ : Fin m → Label) (a : Fin g) :
    |X.I r ℓ a| ≤ 6 ^ (Eint G β a).card * 2 ^ (X.chords.delta a).card := by
  unfold I
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x ∈ (Eint G β a).powerset, |X.degInd ℓ a x *
        topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)|
      ≤ ∑ x ∈ (Eint G β a).powerset, (5 : ℤ) ^ x.card * 2 ^ (X.chords.delta a).card := by
        refine sum_le_sum fun x _ => ?_
        rw [abs_mul]
        have h1 : |X.degInd ℓ a x| ≤ 1 := by unfold degInd; split_ifs <;> simp
        have h2 := (abs_topCoeff_le (isSignedBasis_OmegaSet r (blob β a)) _).trans
          ((norm1_mul_le _ _).trans (mul_le_mul (norm1_edgeProd_le r x) (X.norm1_Gam_le r ℓ a)
            (norm1_nonneg _) (by positivity)))
        calc |X.degInd ℓ a x| * |topCoeff _ _ _| ≤ 1 * |topCoeff (genSet r (blob β a))
              (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact h2
    _ = 6 ^ (Eint G β a).card * 2 ^ (X.chords.delta a).card := by
        rw [← sum_mul]
        congr 1
        have := sum_pow_mul_eq_add_pow (5 : ℤ) 1 (Eint G β a)
        simp only [one_pow, mul_one] at this
        rw [this]; norm_num

end Crossing

/-! ### Degree count: `2|E_int(a)| + |δ(a)| ≤ μ_a` -/

section Degrees

variable {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}

/-- `μ_a = Σ_{v ∈ V_a} deg_G(v)`. -/
def mu (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (β : Fin n → Fin g) (a : Fin g) : ℕ :=
  ∑ v ∈ blob β a, G.degree v

theorem mu_eq_sum_edges (a : Fin g) :
    mu G β a = ∑ e ∈ G.edgeFinset, #((blob β a).filter fun v => v ∈ e) := by
  unfold mu
  have h : ∀ v, G.degree v = ∑ e ∈ G.edgeFinset, if v ∈ e then 1 else 0 := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter, card_filter]
  simp only [h, card_filter]
  exact sum_comm

namespace Crossing

variable (X : Crossing G β m)

/-- Each internal edge has both ends in `V_a`, each crossing edge at `a` one end. -/
theorem two_Eint_add_delta_le (a : Fin g) :
    2 * (Eint G β a).card + (X.chords.delta a).card ≤ mu G β a := by
  classical
  rw [mu_eq_sum_edges]
  set N : Sym2 (Fin n) → ℕ := fun e => #((blob β a).filter fun v => v ∈ e)
  have hdisj : Disjoint (Eint G β a) ((X.chords.delta a).image X.edge) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.edge_not_mem_Eint k a he
  have hsub : Eint G β a ∪ (X.chords.delta a).image X.edge ⊆ G.edgeFinset := by
    intro e he
    rcases mem_union.1 he with he | he
    · exact Eint_subset a he
    · obtain ⟨k, -, rfl⟩ := mem_image.1 he
      exact X.edge_mem_edgeFinset k
  have h1 : ∀ e ∈ Eint G β a, 2 ≤ N e := by
    intro e he
    have he' := mem_Eint.1 he
    induction e using Sym2.ind with
    | _ u w =>
      have huw : u ≠ w := by
        intro h; subst h
        exact (SimpleGraph.mem_edgeFinset.1 he'.1 |> G.not_isDiag_of_mem_edgeSet) (Sym2.mk_isDiag_iff.2 rfl)
      have : ({u, w} : Finset (Fin n)) ⊆ (blob β a).filter fun v => v ∈ s(u, w) := by
        intro v hv
        rcases mem_insert.1 hv with rfl | hv
        · exact mem_filter.2 ⟨mem_blob.2 (he'.2 _ (Sym2.mem_mk_left _ _)), Sym2.mem_mk_left _ _⟩
        · rw [mem_singleton] at hv; subst hv
          exact mem_filter.2 ⟨mem_blob.2 (he'.2 _ (Sym2.mem_mk_right _ _)), Sym2.mem_mk_right _ _⟩
      have := card_le_card this
      rwa [card_pair huw] at this
  have h2 : ∀ k ∈ X.chords.delta a, 1 ≤ N (X.edge k) := by
    intro k hk
    rw [X.mem_delta] at hk
    refine card_pos.2 ?_
    rcases hk with hk | hk
    · exact ⟨X.s k, mem_filter.2 ⟨mem_blob.2 hk, X.mem_edge.2 (Or.inl rfl)⟩⟩
    · exact ⟨X.t k, mem_filter.2 ⟨mem_blob.2 hk, X.mem_edge.2 (Or.inr rfl)⟩⟩
  calc 2 * (Eint G β a).card + (X.chords.delta a).card
      = ∑ _e ∈ Eint G β a, 2 + ∑ _k ∈ X.chords.delta a, 1 := by
        simp [mul_comm]
    _ ≤ ∑ e ∈ Eint G β a, N e + ∑ k ∈ X.chords.delta a, N (X.edge k) :=
        add_le_add (sum_le_sum h1) (sum_le_sum h2)
    _ = ∑ e ∈ Eint G β a ∪ (X.chords.delta a).image X.edge, N e := by
        rw [sum_union hdisj, sum_image fun k _ l _ h => X.edge_injective h]
    _ ≤ ∑ e ∈ G.edgeFinset, N e := sum_le_sum_of_subset hsub

theorem card_delta_le_mu (a : Fin g) : (X.chords.delta a).card ≤ mu G β a :=
  le_trans (Nat.le_add_left _ _) (X.two_Eint_add_delta_le a)

end Crossing

end Degrees

/-! ### The label code -/

namespace Label

/-- `κ : L → {0,…,4}`, `κ(N) = 0`, `κ(j) = j + 1`. -/
def toFin : Label → Fin 5
  | N => 0
  | l0 => 1
  | l1 => 2
  | l2 => 3
  | l3 => 4

/-- The inverse of `κ`. -/
def ofFin (i : Fin 5) : Label :=
  match i with
  | 0 => N
  | 1 => l0
  | 2 => l1
  | 3 => l2
  | 4 => l3

theorem ofFin_toFin (l : Label) : ofFin (toFin l) = l := by cases l <;> rfl

end Label

theorem clog_two_five : Nat.clog 2 5 = 3 := by decide

/-- The 3-bit binary code of the labels (via `κ`). -/
def labelCode : LabelCode Label 3 where
  enc l := (finCode 4).enc l.toFin
  dec z := Label.ofFin ((finCode 4).dec z)
  len l := by rw [(finCode 4).len]; exact clog_two_five
  dec_enc l := by rw [(finCode 4).dec_enc, Label.ofFin_toFin]

/-! ### The copy bits -/

/-- Copy bits `(a, c, d)` with `a < c < d`: node `a` holds a copy of `P_{cd}`, computed by `c`. -/
abbrev CopyIdx (g : ℕ) : Type := {j : Fin g × Fin g × Fin g // j.1 < j.2.1 ∧ j.2.1 < j.2.2}

/-- `ZMod 2 → Bool`. -/
def zToBool (x : ZMod 2) : Bool := decide (x = 1)

/-- `Bool → ZMod 2`. -/
def boolToZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem boolToZ_zToBool (x : ZMod 2) : boolToZ (zToBool x) = x := by
  fin_cases x <;> rfl

/-- The copy vector `y^{(a)} : Fin g × Fin g → ZMod 2` of node `a` (zero off `Q_a`). -/
def copyVec {g : ℕ} (a : Fin g) (y : CopyIdx g → Bool) : Fin g × Fin g → ZMod 2 := fun p =>
  if h : a < p.1 ∧ p.1 < p.2 then boolToZ (y ⟨(a, p.1, p.2), h⟩) else 0

/-- All triples, lexicographically. -/
def allTriples (g : ℕ) : List (Fin g × Fin g × Fin g) :=
  List.finRange g ×ˢ (List.finRange g ×ˢ List.finRange g)

/-- The copy bits in lexicographic order of `(a, c, d)`. -/
def copyList (g : ℕ) : List (CopyIdx g) :=
  (allTriples g).filterMap fun j => if h : j.1 < j.2.1 ∧ j.2.1 < j.2.2 then some ⟨j, h⟩ else none

theorem copyList_nodup (g : ℕ) : (copyList g).Nodup := by
  refine List.Nodup.filterMap ?_ ((List.nodup_finRange g).product
    ((List.nodup_finRange g).product (List.nodup_finRange g)))
  intro j j' b hb hb'
  split_ifs at hb hb' <;> simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at hb hb'
  rw [← hb] at hb'
  exact (congrArg Subtype.val hb').symm

theorem mem_copyList {g : ℕ} (j : CopyIdx g) : j ∈ copyList g := by
  rcases j with ⟨⟨a, c, d⟩, h⟩
  rw [copyList, List.mem_filterMap]
  refine ⟨(a, c, d), ?_, ?_⟩
  · simp [allTriples, List.mem_finRange]
  · rw [dif_pos h]

/-! ### The label system of §5 -/

namespace Crossing

variable {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
  (X : Crossing G β m) (r : Fin n)

/-- **Definition 5.1** as a `LabelSystem`: items are the crossing edges `k` (on the chord
`a_k < b_k`), labels are `Label`, copy bit `(a,c,d)` is held by `a`, computed by `c`, and must be
`P_{cd}(ℓ)`; the node table is `T_a(ℓ, y) = σ_a(ℓ) · χ_a(ℓ, y^{(a)}) · I_a(ℓ)`. -/
def hcSystem : LabelSystem g (Fin m) (CopyIdx g) Label where
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
  dflt := Label.N
  par j ℓ := zToBool (X.chords.P (labelPar ℓ) j.1.2.1 j.1.2.2)
  T a ℓ y := X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a (copyVec a y) * X.I r ℓ a
  par_local j ℓ ℓ' h := by
    rw [X.P_congr (c := j.1.2.1) (ℓ' := ℓ') (fun k hk => h k (X.mem_delta.1 hk))]
  T_local a ℓ ℓ' y y' hℓ hy := by
    have hd : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k := fun k hk => hℓ k (X.mem_delta.1 hk)
    have hc : ∀ p ∈ Chords.Q a, copyVec a y p = copyVec a y' p := by
      intro p hp
      simp only [Chords.Q, mem_filter, mem_univ, true_and] at hp
      simp only [copyVec, dif_pos hp]
      rw [hy _ rfl]
    rw [X.sigma_congr hd, X.chi_congr hd hc, X.I_congr r hd]

/-- The copy bits held by `a` are exactly the triples `(a, c, d)` with `(c, d) ∈ Q_a`. -/
theorem held_iff_mem_Q (a : Fin g) (p : Fin g × Fin g) :
    p ∈ Chords.Q a ↔ ∃ j : CopyIdx g, (X.hcSystem r).holder j = a ∧ (j.1.2.1, j.1.2.2) = p := by
  simp only [Chords.Q, mem_filter, mem_univ, true_and]
  constructor
  · intro h; exact ⟨⟨(a, p.1, p.2), h⟩, rfl, rfl⟩
  · rintro ⟨⟨⟨a', c, d⟩, h⟩, ha, rfl⟩
    exact (show a' = a from ha) ▸ h

@[simp] theorem hcSystem_T (a : Fin g) (ℓ : Fin m → Label) (y : CopyIdx g → Bool) :
    (X.hcSystem r).T a ℓ y =
      X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a (copyVec a y) * X.I r ℓ a := rfl

/-- The node table fed the correct copy bits is `σ_a χ_a(P) I_a`. -/
theorem hcSystem_T_par (a : Fin g) (ℓ : Fin m → Label) :
    (X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ) =
      X.chords.sigma (labelPar ℓ) a *
        X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) * X.I r ℓ a := by
  rw [hcSystem_T]
  congr 2
  refine X.chi_congr (fun _ _ => rfl) fun p hp => ?_
  simp only [Chords.Q, mem_filter, mem_univ, true_and] at hp
  simp only [copyVec, dif_pos hp]
  exact boolToZ_zToBool _

variable {w : ℕ} (C : LabelCode Label w)

/-- **Theorem 5.3.** The value of the network is `n · #HC(G)`. -/
theorem hcNet_value : ((X.hcSystem r).net C).value = n * (Hamiltonian.hamCycles G).card := by
  rw [LabelSystem.value_net, ← blob_factorisation X r]
  exact sum_congr rfl fun ℓ _ => prod_congr rfl fun a _ => X.hcSystem_T_par r a ℓ

/-! ### Proposition 5.4: the parameters -/

/-- `|T_a(ℓ, y)| ≤ 2^{3|E_int(a)| + |δ(a)|}` (`|σ_a χ_a| = 1`, `|I_a| ≤ 6^{|E_int(a)|} 2^{|δ(a)|}`). -/
theorem abs_hcT_le (a : Fin g) (ℓ : Fin m → Label) (y : CopyIdx g → Bool) :
    |(X.hcSystem r).T a ℓ y| ≤ 2 ^ (3 * (Eint G β a).card + (X.chords.delta a).card) := by
  rw [hcSystem_T, abs_mul, abs_mul]
  have hs : ∀ x : ZMod 2, |sgn x| = 1 := fun x => by
    rcases sgn_eq_one_or_neg_one x with h | h <;> simp [h]
  rw [Chords.sigma, Chords.chi, hs, hs, one_mul, one_mul, pow_add, pow_mul]
  refine (X.abs_I_le r ℓ a).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- **The bound `B = 2μ_a + 1`**: `|T_a(ℓ, y)| < 2^{2μ_a + 1}`. -/
theorem abs_hcT_lt (a : Fin g) (ℓ : Fin m → Label) (y : CopyIdx g → Bool) :
    |(X.hcSystem r).T a ℓ y| < 2 ^ (2 * mu G β a + 1) := by
  refine (X.abs_hcT_le r a ℓ y).trans_lt (pow_lt_pow_right₀ (by norm_num) ?_)
  have := X.two_Eint_add_delta_le a
  omega

/-- The items incident to `a` in the label system are the crossing edges `δ(a)`. -/
theorem hcSystem_card_inc (a : Fin g) :
    #(univ.filter ((X.hcSystem r).Inc a)) = (X.chords.delta a).card := rfl

/-- The copy bits touching `a` (held by `a`, or computed at `a`) number at most `g²`. -/
theorem hcSystem_card_touch_le (a : Fin g) :
    #(univ.filter ((X.hcSystem r).Touch a)) ≤ g ^ 2 := by
  have h := card_le_card_of_injOn
    (fun j : CopyIdx g => if j.1.1 = a then (j.1.2.1, j.1.2.2) else (j.1.1, j.1.2.2))
    (s := univ.filter ((X.hcSystem r).Touch a)) (t := (univ : Finset (Fin g × Fin g)))
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

/-- The shared bits at `a`: `Σ_{b ≠ a} c_{a,b} = w·|δ(a)| + #(copy bits touching a)`. -/
theorem hcNet_sum_c (a : Fin g) :
    ∑ b ∈ univ.erase a, ((X.hcSystem r).net C).c a b =
      (X.chords.delta a).card * w + #(univ.filter ((X.hcSystem r).Touch a)) := by
  rw [LabelSystem.sum_c_eq, hcSystem_card_inc]

theorem hcNet_sum_c_le (a : Fin g) :
    ∑ b ∈ univ.erase a, ((X.hcSystem r).net C).c a b ≤ w * mu G β a + g ^ 2 := by
  rw [hcNet_sum_c]
  have := X.card_delta_le_mu a
  have := X.hcSystem_card_touch_le r a
  nlinarith

/-- **Proposition 5.4 (Definition 2)**, general form. -/
theorem hcNet_is' {P B : ℕ} (hP1 : 1 ≤ P) (hB1 : 1 ≤ B)
    (hP : ∀ a, (X.chords.delta a).card * w + #(univ.filter ((X.hcSystem r).Touch a)) ≤ P)
    (hB : ∀ a, 3 * (Eint G β a).card + (X.chords.delta a).card < B) :
    ((X.hcSystem r).net C).Is P B :=
  (X.hcSystem r).net_is C hP1 hB1 hP fun a ℓ y => (X.abs_hcT_le r a ℓ y).trans_lt (pow_lt_pow_right₀ (by norm_num) (hB a))

/-- **Proposition 5.4 (Definition 2)** with `P = w·μ + g² + 1` and `B = 2μ + 1`, for any
`μ ≥ max_a μ_a`. -/
theorem hcNet_is (μ : ℕ) (hμ : ∀ a, mu G β a ≤ μ) :
    ((X.hcSystem r).net C).Is (w * μ + g ^ 2 + 1) (2 * μ + 1) :=
  (X.hcSystem r).net_is' C (by omega) (by omega)
    (fun a => (X.hcNet_sum_c_le r C a).trans (by
      have := Nat.mul_le_mul_left w (hμ a); omega))
    fun a ℓ y => (X.abs_hcT_lt r a ℓ y).trans_le (pow_le_pow_right₀ (by norm_num) (by
      have := hμ a; omega))

/-- **Proposition 5.4** for the 3-bit code: `Is (3μ + g² + 1) (2μ + 1)`. -/
theorem hcNet_is_labelCode (μ : ℕ) (hμ : ∀ a, mu G β a ≤ μ) :
    ((X.hcSystem r).net labelCode).Is (3 * μ + g ^ 2 + 1) (2 * μ + 1) :=
  X.hcNet_is r labelCode μ hμ

/-- **Theorem 5.3** for the 3-bit code. -/
theorem hcNet_value_labelCode :
    ((X.hcSystem r).net labelCode).value = n * (Hamiltonian.hamCycles G).card :=
  X.hcNet_value r labelCode

/-- The total `U = 2(w·m + #copy bits)`. -/
theorem hcNet_U : ((X.hcSystem r).net C).U = 2 * (m * w + Fintype.card (CopyIdx g)) := by
  rw [LabelSystem.U_eq, Fintype.card_fin]

theorem card_copyIdx_le (g : ℕ) : Fintype.card (CopyIdx g) ≤ g ^ 3 := by
  refine (Fintype.card_subtype_le _).trans ?_
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact le_of_eq (by ring)

theorem hcNet_U_le : ((X.hcSystem r).net C).U ≤ 2 * (m * w + g ^ 3) := by
  rw [hcNet_U]; have := card_copyIdx_le g; omega

end Crossing

end

end EthFollowup.ExactHC
