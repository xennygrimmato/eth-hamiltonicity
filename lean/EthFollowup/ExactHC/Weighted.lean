/-
# The weighted (TSP) version of the exact-#HC identity and of its blob factorisation

Write-up: `research/exact-extensions.md` (row 2 of the results table, TSP via Kronecker
substitution). Edge weights are `w : Sym2 (Fin n) → ℕ`, `w(X) = Σ_{e∈X} w e` (`Hamiltonian.wt`),
and the generating variable `z` is either an element of an arbitrary commutative semiring (part 1)
or an integer (parts 2–3: the Grassmann algebra of `Grassmann.lean` is over `ℤ`, and the algorithm
only needs the Kronecker substitution `z = 2^b`).

## Results
1. `Hamiltonian.n_mul_sum_hamCycles_pow_eq` (**weighted identity**, any commutative semiring `R`,
   `z : R`): `n · Σ_{H ∈ HC(G)} z^{w(H)} = Σ_{X 2-factor} z^{w(X)} · τ(X)`.
2. `fermionSumW G r z w = Σ_{X 2-factor} z^{w(X)} [Ω_V] Π_{e∈X}(1 + q_e)` and
   `fermionSumW_eq : fermionSumW G r z w = n · Σ_H z^{w(H)}` (weighted Corollary 3.4).
3. Weighted blob tables `Crossing.Iw r z w ℓ a = z^{w_ℓ(a)} · Σ_{x ⊆ E_int(a)} [deg = 2] z^{w(x)}
   [ω_a](F_a(x) Γ_a(ℓ))`, where `w_ℓ(a)` (`Crossing.wtL`) is the weight of the crossing edges with
   *low end* in `a` and label `≠ N` (so every selected edge is weighted exactly once).
   * `Crossing.sum_eps_prod_Iw : Σ_ℓ ε(ℓ) Π_a I^w_a(ℓ) = fermionSumW G r z w`,
   * `Crossing.sum_sigma_chi_Iw : Σ_ℓ Π_a σ_a χ_a(P) I^w_a = fermionSumW G r z w`,
   * `blob_factorisation_w : Σ_ℓ Π_a σ_a χ_a(P) I^w_a = n · Σ_H z^{w(H)}` (weighted Theorem 4.6),
   * locality `Crossing.Iw_congr`, the specialisation `Crossing.Iw_one : I^w(z = 1) = I`, and the
     size bounds `Crossing.wtL_le`, `Hamiltonian.wt_le_of_subset` used by the network layer.
-/
import EthFollowup.ExactHC.Main

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup

open Finset

/-! ### Edge weights and the weighted identity -/

namespace Hamiltonian

variable {n : ℕ}

/-- `w(X) = Σ_{e ∈ X} w e`. -/
def wt (w : Sym2 (Fin n) → ℕ) (X : Finset (Sym2 (Fin n))) : ℕ := ∑ e ∈ X, w e

theorem wt_le_card_mul {w : Sym2 (Fin n) → ℕ} {W : ℕ} (hw : ∀ e, w e ≤ W)
    (X : Finset (Sym2 (Fin n))) : wt w X ≤ X.card * W := by
  unfold wt
  have := sum_le_card_nsmul X w W fun e _ => hw e
  simpa using this

theorem wt_le_of_subset {w : Sym2 (Fin n) → ℕ} {W : ℕ} (hw : ∀ e, w e ≤ W)
    {x X : Finset (Sym2 (Fin n))} (hx : x ⊆ X) : wt w x ≤ X.card * W :=
  (wt_le_card_mul hw x).trans (Nat.mul_le_mul_right W (card_le_card hx))

/-- **The weighted identity**, over any commutative semiring `R` with `z : R`:
`n · Σ_{H ∈ HC(G)} z^{w(H)} = Σ_{X 2-factor of G} z^{w(X)} · τ(X)`. With `R = Polynomial ℤ`,
`z = X` this is the generating polynomial of the tours by weight; with `R = ℤ`, `z = 2^b` it is its
Kronecker substitution. -/
theorem n_mul_sum_hamCycles_pow_eq {R : Type*} [CommSemiring R] (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℕ) (z : R) :
    (n : R) * ∑ H ∈ hamCycles G, z ^ wt w H =
      ∑ X ∈ twoFactors G, z ^ wt w X * ((spanningTrees X).card : R) := by
  rw [hamCycles, sum_filter, mul_sum]
  refine sum_congr rfl fun X hX => ?_
  rw [card_spanningTrees_of_mem_twoFactors G hX]
  split_ifs
  · ring
  · simp

/-! #### Tours by weight, and the Kronecker decoding -/

/-- `c_k = #{H ∈ HC(G) : w(H) = k}`, the number of tours of weight `k`. -/
def tourCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℕ) (k : ℕ) :
    ℕ :=
  ((hamCycles G).filter fun H => wt w H = k).card

theorem tourCount_le_card (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℕ)
    (k : ℕ) : tourCount G w k ≤ (hamCycles G).card :=
  card_filter_le _ _

theorem card_hamCycles_le_two_pow (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (hamCycles G).card ≤ 2 ^ G.edgeFinset.card := by
  have h : hamCycles G ⊆ G.edgeFinset.powerset := fun H hH =>
    mem_powerset.2 (mem_powerset.1 (mem_filter.1 (mem_filter.1 hH).1).1)
  exact (card_le_card h).trans (le_of_eq (card_powerset _))

/-- A Hamiltonian cycle has `n` edges, so its weight is at most `n·W`. -/
theorem wt_le_of_mem_hamCycles (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {w : Sym2 (Fin n) → ℕ} {W : ℕ} (hw : ∀ e, w e ≤ W) {H : Finset (Sym2 (Fin n))}
    (hH : H ∈ hamCycles G) : wt w H ≤ n * W := by
  have hX : H ∈ twoFactors G := (mem_filter.1 hH).1
  have hc := card_eq_of_twoRegular (mem_filter.1 hX).2 (loopFree_of_mem_twoFactors G hX)
  have := wt_le_card_mul hw H
  rwa [hc] at this

/-- The generating sum of the tours by weight: `Σ_H z^{w(H)} = Σ_{k ≤ K} c_k z^k` for any
`K ≥ max_H w(H)`. -/
theorem sum_pow_wt_eq_sum_tourCount {R : Type*} [Semiring R] (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℕ) (z : R) {K : ℕ}
    (hK : ∀ H ∈ hamCycles G, wt w H ≤ K) :
    ∑ H ∈ hamCycles G, z ^ wt w H = ∑ k ∈ range (K + 1), (tourCount G w k : R) * z ^ k := by
  rw [← sum_fiberwise_of_maps_to (s := hamCycles G) (t := range (K + 1)) (g := wt w)
    (fun H hH => mem_range.2 (Nat.lt_succ_of_le (hK H hH)))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl (fun H hH => by rw [(mem_filter.1 hH).2]), sum_const, nsmul_eq_mul]
  rfl

/-- Reading the base-`B` digits of `Σ_{k<K} d_k B^k` when every `d_k < B`. -/
theorem digits_sum_range {B : ℕ} (hB : 0 < B) :
    ∀ (K : ℕ) (d : ℕ → ℕ), (∀ k, d k < B) → ∀ j : ℕ,
      (∑ k ∈ range K, d k * B ^ k) / B ^ j % B = if j < K then d j else 0
  | 0, d, _, j => by simp
  | K + 1, d, hd, j => by
    have hsplit : ∑ k ∈ range (K + 1), d k * B ^ k =
        d 0 + B * ∑ k ∈ range K, d (k + 1) * B ^ k := by
      rw [sum_range_succ', pow_zero, mul_one, mul_sum, add_comm]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [pow_succ]; ring
    rw [hsplit]
    cases j with
    | zero =>
      simp only [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0),
        Nat.zero_lt_succ, if_true]
    | succ j =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hd 0), zero_add, digits_sum_range hB K (fun k => d (k + 1))
          (fun k => hd (k + 1)) j]
      simp only [Nat.succ_lt_succ_iff]

/-- **Kronecker decoding of the weighted count.** Let `N = n · Σ_H 2^{b·w(H)}` (the value of the
weighted network at `z = 2^b`). If `n·c_k < 2^b` for every `k` and every tour has weight `≤ K`,
then the base-`2^b` digits of `N` are the `n·c_k`: `N / 2^{bj} mod 2^b = n · c_j` for `j ≤ K`. In
particular the minimum tour weight is the position of the lowest non-zero digit and the number of
optimal tours is that digit divided by `n`. -/
theorem kronecker_decode (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℕ)
    (b : ℕ) (hb : ∀ k, n * tourCount G w k < 2 ^ b) {K : ℕ}
    (hK : ∀ H ∈ hamCycles G, wt w H ≤ K) {j : ℕ} (hj : j ≤ K) :
    (n * ∑ H ∈ hamCycles G, 2 ^ (b * wt w H)) / 2 ^ (b * j) % 2 ^ b = n * tourCount G w j := by
  have h := digits_sum_range (B := 2 ^ b) (by positivity) (K + 1) (fun k => n * tourCount G w k)
    hb j
  rw [if_pos (Nat.lt_succ_of_le hj)] at h
  rw [← h, pow_mul]
  congr 2
  simp only [pow_mul]
  rw [sum_pow_wt_eq_sum_tourCount G w (2 ^ b) hK, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.cast_id, mul_assoc]

/-- A sufficient precision for the decoding: `b` bits with `n · 2^{|E|} < 2^b`. -/
theorem n_mul_tourCount_lt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℕ)
    {b : ℕ} (hb : n * 2 ^ G.edgeFinset.card < 2 ^ b) (k : ℕ) : n * tourCount G w k < 2 ^ b :=
  lt_of_le_of_lt (Nat.mul_le_mul_left n ((tourCount_le_card G w k).trans
    (card_hamCycles_le_two_pow G))) hb

end Hamiltonian

namespace ExactHC

open Grass Hamiltonian

noncomputable section

variable {n : ℕ}

/-- The weighted fermion sum `Σ_{X 2-factor} z^{w(X)} [Ω_V] Π_{e∈X}(1 + q_e)`. -/
def fermionSumW (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n) (z : ℤ)
    (w : Sym2 (Fin n) → ℕ) : ℤ :=
  ∑ X ∈ twoFactors G, z ^ wt w X * topV r (edgeProd r X)

/-- **Weighted Corollary 3.4**: `fermionSumW G r z w = n · Σ_{H ∈ HC(G)} z^{w(H)}`. -/
theorem fermionSumW_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n) (z : ℤ)
    (w : Sym2 (Fin n) → ℕ) :
    fermionSumW G r z w = n * ∑ H ∈ hamCycles G, z ^ wt w H := by
  rw [n_mul_sum_hamCycles_pow_eq G w z, fermionSumW]
  refine sum_congr rfl fun X hX => ?_
  rw [topV_edgeProd r X (loopFree_of_mem_twoFactors G hX)]

/-- At `z = 1` the weighted fermion sum is the unweighted one. -/
theorem fermionSumW_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n)
    (w : Sym2 (Fin n) → ℕ) : fermionSumW G r 1 w = fermionSum G r := by
  simp [fermionSumW, fermionSum]

/-! ### Weighted blob tables -/

namespace Crossing

variable {g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
  (X : Crossing G β m) (r : Fin n) (z : ℤ) (w : Sym2 (Fin n) → ℕ)

/-- `w_ℓ(a)`: the weight of the crossing edges `e_k` with low end in `V_a` and `ℓ_k ≠ N`. Each
selected crossing edge is weighted at its low end only. -/
def wtL (ℓ : Fin m → Label) (a : Fin g) : ℕ :=
  ∑ k ∈ (X.chords.delta a).filter (fun k => β (X.s k) = a ∧ ℓ k ≠ Label.N), w (X.edge k)

/-- The weight `Σ_{k ∈ T} w(e_k)` of a set of crossing edges. -/
def wtT (T : Finset (Fin m)) : ℕ := ∑ k ∈ T, w (X.edge k)

/-- **The weighted blob sum**
`I^w_a(ℓ) = z^{w_ℓ(a)} · Σ_{x ⊆ E_int(a)} Π_{v∈V_a}[deg_x(v) + deg_ℓ(v) = 2] · z^{w(x)} · [ω_a](F_a(x) Γ_a(ℓ))`. -/
def Iw (ℓ : Fin m → Label) (a : Fin g) : ℤ :=
  z ^ X.wtL w ℓ a * ∑ x ∈ (Eint G β a).powerset, X.degInd ℓ a x * z ^ wt w x *
    topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)

/-- At `z = 1`, `I^w_a = I_a`. -/
theorem Iw_one (ℓ : Fin m → Label) (a : Fin g) : X.Iw r 1 w ℓ a = X.I r ℓ a := by
  simp [Iw, I]

/-! #### Locality -/

theorem wtL_congr {ℓ ℓ' : Fin m → Label} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.wtL w ℓ a = X.wtL w ℓ' a := by
  unfold wtL
  congr 1
  refine filter_congr fun k hk => ?_
  rw [h k hk]

/-- `I^w_a(ℓ)` depends only on `ℓ|δ(a)`. -/
theorem Iw_congr {ℓ ℓ' : Fin m → Label} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.Iw r z w ℓ a = X.Iw r z w ℓ' a := by
  unfold Iw degInd
  simp only [X.wtL_congr w h, X.degL_congr h, X.Gam_congr r h]

/-! #### Size -/

theorem wtL_le {W : ℕ} (hw : ∀ e, w e ≤ W) (ℓ : Fin m → Label) (a : Fin g) :
    X.wtL w ℓ a ≤ (X.chords.delta a).card * W := by
  unfold wtL
  have h1 := sum_le_card_nsmul ((X.chords.delta a).filter
    (fun k => β (X.s k) = a ∧ ℓ k ≠ Label.N)) (fun k => w (X.edge k)) W fun k _ => hw _
  rw [smul_eq_mul] at h1
  exact h1.trans (Nat.mul_le_mul_right W (card_filter_le _ _))

/-! ### Weighted Theorem 4.6 -/

section Factorisation

/-- The core of steps 1–4 of Theorem 4.6, for a fixed choice `xs` of internal edges:
`ε(ℓ) Π_a [ω_a](F_a(x_a) Γ_a(ℓ)) = [Ω_V](Π_a F_a(x_a) · Π_k α_{ℓ_k} β_{ℓ_k})`. -/
theorem eps_mul_prod_topCoeff (ℓ : Fin m → Label) (xs : Fin g → Finset (Sym2 (Fin n)))
    (hxs : ∀ a, xs a ⊆ Eint G β a) :
    X.eps ℓ * ∏ a, topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a))
        (edgeProd r (xs a) * X.Gam r ℓ a) =
      topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
        (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod) := by
  rw [← topV_prod_blocks r β _ (fun a => X.suppIn_blobTerm r ℓ (hxs a)),
    prod_ofFn_mul_of_even _ _ (fun a => isHomog_edgeProd r (xs a)), X.sign_rule r ℓ,
    mul_smul_comm]
  unfold topV
  rw [topCoeff_zsmul]

/-- Steps 1–4, weighted: expand `Π_a I^w_a`. -/
theorem eps_mul_prod_Iw (ℓ : Fin m → Label) :
    X.eps ℓ * ∏ a, X.Iw r z w ℓ a =
      ∑ xs ∈ Fintype.piFinset (fun a => (Eint G β a).powerset),
        z ^ (∑ a, wt w (xs a)) * ((∏ a, X.degInd ℓ a (xs a)) * z ^ (∑ a, X.wtL w ℓ a) *
          topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
            (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod)) := by
  unfold Iw
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_univ_sum]
  simp only [mul_sum]
  refine sum_congr rfl fun xs hxs => ?_
  rw [Fintype.mem_piFinset] at hxs
  have hsub : ∀ a, xs a ⊆ Eint G β a := fun a => mem_powerset.1 (hxs a)
  rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum,
    ← X.eps_mul_prod_topCoeff r ℓ xs hsub]
  ring

/-- `Σ_a w_ℓ(a) = Σ_{k : ℓ_k ≠ N} w(e_k)`: every selected crossing edge is weighted once, at its
low end. -/
theorem sum_wtL (ℓ : Fin m → Label) : ∑ a, X.wtL w ℓ a = X.wtT w (supp ℓ) := by
  unfold wtL wtT
  rw [← sum_fiberwise (supp ℓ) (fun k => β (X.s k))]
  refine sum_congr rfl fun a _ => ?_
  congr 1
  ext k
  simp only [mem_filter, X.mem_delta, supp, mem_univ, true_and]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨Or.inl h1, h1, h2⟩

/-- Steps 5–6, weighted, for a fixed choice `xs` of internal edges. -/
theorem sum_labels_fixed_w (xs : Fin g → Finset (Sym2 (Fin n))) :
    ∑ ℓ : Fin m → Label, (∏ a, X.degInd ℓ a (xs a)) * z ^ (∑ a, X.wtL w ℓ a) *
        topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
          (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod) =
      ∑ T : Finset (Fin m), X.indT xs T * z ^ X.wtT w T *
        topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
          ((∏ k ∈ T, oneQ r (X.edge k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n)))) := by
  rw [← sum_fiberwise univ supp]
  refine sum_congr rfl fun T _ => ?_
  rw [← X.sum_fiber_pieces r T, mul_sum, topV, topCoeff_sum, mul_sum]
  refine sum_congr rfl fun ℓ hℓ => ?_
  have hT := (mem_filter.1 hℓ).2
  have h := X.prod_degInd ℓ xs
  rw [hT] at h
  rw [h, X.sum_wtL w ℓ, hT]
  rfl

/-- The weight of `x_int ∪ {e_k : k ∈ T}`. -/
theorem wt_unionEdges {xs : Fin g → Finset (Sym2 (Fin n))} (hxs : ∀ a, xs a ⊆ Eint G β a)
    (T : Finset (Fin m)) :
    wt w (X.unionEdges xs T) = (∑ a, wt w (xs a)) + X.wtT w T := by
  have hdisj : Disjoint (univ.biUnion xs) (T.image X.edge) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨a, -, hea⟩ := mem_biUnion.1 he
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.edge_not_mem_Eint k a (hxs a hea)
  have hpd : ((univ : Finset (Fin g)) : Set (Fin g)).PairwiseDisjoint xs :=
    fun a _ b _ hab => (Eint_disjoint hab).mono (hxs a) (hxs b)
  unfold wt wtT unionEdges
  rw [sum_union hdisj, sum_biUnion hpd, sum_image (fun k _ l _ h => X.edge_injective h)]

/-- Step 7 for an arbitrary function `F` of the edge set: regrouping by
`x = x_int ∪ 1_T` gives the sum over 2-factors. -/
theorem sum_internal_crossing_gen (F : Finset (Sym2 (Fin n)) → ℤ) :
    ∑ xs ∈ Fintype.piFinset (fun a => (Eint G β a).powerset), ∑ T : Finset (Fin m),
        X.indT xs T * F (X.unionEdges xs T) =
      ∑ Y ∈ twoFactors G, F Y := by
  classical
  unfold Hamiltonian.twoFactors
  rw [sum_filter, ← sum_product']
  refine sum_nbij' (fun p => X.unionEdges p.1 p.2)
    (fun Y => (fun a => Y.filter (· ∈ Eint G β a), univ.filter fun k => X.edge k ∈ Y))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Eint G β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    rw [mem_powerset]
    intro e he
    rcases X.mem_unionEdges.1 he with ⟨a, ha⟩ | ⟨k, -, rfl⟩
    · exact Eint_subset a (hxs a ha)
    · exact X.edge_mem_edgeFinset k
  · intro Y _
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨fun a => mem_powerset.2 fun e he => (mem_filter.1 he).2, mem_univ _⟩
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Eint G β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    refine Prod.ext (funext fun a => ?_) ?_
    · ext e
      simp only [mem_filter, X.mem_unionEdges]
      constructor
      · rintro ⟨⟨b, hb⟩ | ⟨k, -, rfl⟩, he⟩
        · by_cases hab : a = b
          · exact hab ▸ hb
          · exact absurd he (disjoint_left.1 (Eint_disjoint (Ne.symm hab)) (hxs b hb))
        · exact absurd he (X.edge_not_mem_Eint k a)
      · intro he
        exact ⟨Or.inl ⟨a, he⟩, hxs a he⟩
    · ext k
      simp only [mem_filter, mem_univ, true_and, X.mem_unionEdges]
      constructor
      · rintro (⟨b, hb⟩ | ⟨l, hl, hlk⟩)
        · exact absurd (hxs b hb) (X.edge_not_mem_Eint k b)
        · exact X.edge_injective hlk ▸ hl
      · intro hk
        exact Or.inr ⟨k, hk, rfl⟩
  · intro Y hY
    have hY' : Y ⊆ G.edgeFinset := mem_powerset.1 hY
    ext e
    simp only [X.mem_unionEdges, mem_filter, mem_univ, true_and]
    constructor
    · rintro (⟨a, he, -⟩ | ⟨k, hk, rfl⟩)
      · exact he
      · exact hk
    · intro he
      rcases X.edge_cases (hY' he) with ⟨a, ha⟩ | ⟨k, rfl⟩
      · exact Or.inl ⟨a, he, ha⟩
      · exact Or.inr ⟨k, he, rfl⟩
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Eint G β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    simp only
    rw [indT, prod_boole]
    by_cases h : ∀ a, ∀ v ∈ blob β a, deg (xs a) v + X.degT T a v = 2
    · rw [if_pos (fun a _ => h a), if_pos ((X.twoRegular_unionEdges_iff hxs T).2 h), one_mul]
    · rw [if_neg (fun h' => h fun a => h' a (mem_univ a)),
        if_neg (fun h' => h ((X.twoRegular_unionEdges_iff hxs T).1 h')), zero_mul]

/-- **Weighted Theorem 4.6, first equality**:
`Σ_{ℓ ∈ L^m} ε(ℓ) Π_a I^w_a(ℓ) = Σ_{X 2-factor} z^{w(X)} [Ω_V] Π_{e∈X}(1+q_e)`. -/
theorem sum_eps_prod_Iw :
    ∑ ℓ : Fin m → Label, X.eps ℓ * ∏ a, X.Iw r z w ℓ a = fermionSumW G r z w := by
  simp only [X.eps_mul_prod_Iw r z w]
  rw [sum_comm]
  unfold fermionSumW
  rw [← X.sum_internal_crossing_gen (fun Y => z ^ wt w Y * topV r (edgeProd r Y))]
  refine sum_congr rfl fun xs hxs => ?_
  rw [Fintype.mem_piFinset] at hxs
  have hsub : ∀ a, xs a ⊆ Eint G β a := fun a => mem_powerset.1 (hxs a)
  rw [← mul_sum, X.sum_labels_fixed_w r z w xs, mul_sum]
  refine sum_congr rfl fun T _ => ?_
  rw [X.wt_unionEdges w hsub T, X.edgeProd_unionEdges r hsub T, pow_add]
  ring

/-- **Weighted Theorem 4.6, second equality**: with `π_k = π(ℓ_k)` and correct parity copies,
`Σ_ℓ Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I^w_a(ℓ) = fermionSumW G r z w`. -/
theorem sum_sigma_chi_Iw :
    ∑ ℓ : Fin m → Label, ∏ a, X.chords.sigma (labelPar ℓ) a *
        X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) * X.Iw r z w ℓ a =
      fermionSumW G r z w := by
  rw [← X.sum_eps_prod_Iw r z w]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [prod_mul_distrib, eps,
    X.chords.eps_eq_prod_sigma_chi (labelPar ℓ) (fun _ p => X.chords.P (labelPar ℓ) p.1 p.2)
      (fun _ _ _ => rfl)]

end Factorisation

end Crossing

/-! ### The weighted blob factorisation, assembled -/

variable {g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}

/-- **Weighted blob factorisation** (TSP via Kronecker substitution): for every graph `G` on
`Fin n`, root `r`, partition `β`, crossing order `X`, integer `z` and weights `w`,
`Σ_{ℓ ∈ L^m} Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I^w_a(ℓ) = n · Σ_{H ∈ HC(G)} z^{w(H)}`. -/
theorem blob_factorisation_w (X : Crossing G β m) (r : Fin n) (z : ℤ) (w : Sym2 (Fin n) → ℕ) :
    ∑ ℓ : Fin m → Label, ∏ a, X.chords.sigma (labelPar ℓ) a *
        X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) * X.Iw r z w ℓ a =
      n * ∑ H ∈ hamCycles G, z ^ wt w H := by
  rw [X.sum_sigma_chi_Iw r z w, fermionSumW_eq]

/-- The same, with the global sign `ε(ℓ)`. -/
theorem blob_factorisation_w_eps (X : Crossing G β m) (r : Fin n) (z : ℤ)
    (w : Sym2 (Fin n) → ℕ) :
    ∑ ℓ : Fin m → Label, X.eps ℓ * ∏ a, X.Iw r z w ℓ a = n * ∑ H ∈ hamCycles G, z ^ wt w H := by
  rw [X.sum_eps_prod_Iw r z w, fermionSumW_eq]

/-- A crossing order always exists, so the weighted factorisation always applies. -/
theorem exists_blob_factorisation_w (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (β : Fin n → Fin g) (r : Fin n) (z : ℤ) (w : Sym2 (Fin n) → ℕ) :
    ∃ (m : ℕ) (X : Crossing G β m),
      ∑ ℓ : Fin m → Label, ∏ a, X.chords.sigma (labelPar ℓ) a *
          X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) *
          X.Iw r z w ℓ a =
        n * ∑ H ∈ hamCycles G, z ^ wt w H :=
  ⟨_, Crossing.canonical G β, blob_factorisation_w _ r z w⟩

end

end ExactHC

end EthFollowup
