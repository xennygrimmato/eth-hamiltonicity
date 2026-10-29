/-
# ATSP: the directed tour polynomial, its Kronecker decoding, and the assembled math layer

`research/tsp-theorem.md` §3 (Theorem TSP-2). For a digraph `A : Finset (Fin n × Fin n)` and arc
weights `w`, the directed tour polynomial is `T⃗_A(z) = Σ_{H ∈ DHC(A)} z^{w(H)}`. This file collects
what the network layer needs about it:

* `dtourCount A w k = #{H ∈ DHC(A) : w(H) = k}`;
* `card_dirHamCycles_le_two_pow`: `#DHC(A) ≤ 2^{|A|}` (so `b = |A| + 1` bits suffice, §3.2);
* `card_of_mem_cycleCovers`, `arcWt_le_of_mem_dirHamCycles`: a tour has `n` arcs, so
  `w(H) ≤ n·W`;
* `sum_pow_arcWt_eq_sum_dtourCount`: `T⃗_A(z) = Σ_{k ≤ K} c_k z^k`;
* `dkronecker_decode`: the base-`2^b` digits of `T⃗_A(2^b)` are the `c_k` (no division by `n`);
* `atsp_blob_factorisation`: the directed blob factorisation at `z = 2^b`, together with the
  decoding of its value — the complete mathematical content of the ATSP algorithm
  (Theorem 1.4 + Lemma 3.3 + Lemma 3.4 + the digit extraction of §2.4).
-/
import EthFollowup.ExactHC.DirectedBlobs
import EthFollowup.ExactHC.Weighted

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

variable {n : ℕ}

/-! ### Tours by weight -/

/-- `c_k = #{H ∈ DHC(A) : w(H) = k}`, the number of directed tours of weight `k`. -/
def dtourCount (A : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℕ) (k : ℕ) : ℕ :=
  ((DirectedHamiltonian.dirHamCycles A).filter fun H => arcWt w H = k).card

theorem dtourCount_le_card (A : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℕ) (k : ℕ) :
    dtourCount A w k ≤ (DirectedHamiltonian.dirHamCycles A).card :=
  card_filter_le _ _

theorem card_dirHamCycles_le_two_pow (A : Finset (Fin n × Fin n)) :
    (DirectedHamiltonian.dirHamCycles A).card ≤ 2 ^ A.card := by
  have h : DirectedHamiltonian.dirHamCycles A ⊆ A.powerset := fun H hH =>
    (mem_filter.1 (mem_filter.1 hH).1).1
  exact (card_le_card h).trans (le_of_eq (card_powerset _))

/-- A cycle cover has exactly `n` arcs. -/
theorem card_of_cycleCover {X : Finset (Fin n × Fin n)} (hX : DirectedHamiltonian.CycleCover X) :
    X.card = n := by
  rw [← sum_card_outArcs, sum_congr rfl fun v _ => cc_out_card hX v, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

theorem arcWt_le_card_mul {w : Fin n × Fin n → ℕ} {W : ℕ} (hw : ∀ e, w e ≤ W)
    (X : Finset (Fin n × Fin n)) : arcWt w X ≤ X.card * W := by
  unfold arcWt
  have := sum_le_card_nsmul X w W fun e _ => hw e
  simpa using this

/-- A directed tour has `n` arcs, so its weight is at most `n·W`. -/
theorem arcWt_le_of_mem_dirHamCycles (A : Finset (Fin n × Fin n)) {w : Fin n × Fin n → ℕ}
    {W : ℕ} (hw : ∀ e, w e ≤ W) {H : Finset (Fin n × Fin n)}
    (hH : H ∈ DirectedHamiltonian.dirHamCycles A) : arcWt w H ≤ n * W := by
  have hc := card_of_cycleCover (mem_filter.1 (mem_filter.1 hH).1).2
  have := arcWt_le_card_mul hw H
  rwa [hc] at this

/-- `T⃗_A(z) = Σ_{k ≤ K} c_k z^k` for any `K ≥ max_H w(H)`. -/
theorem sum_pow_arcWt_eq_sum_dtourCount {R : Type*} [Semiring R] (A : Finset (Fin n × Fin n))
    (w : Fin n × Fin n → ℕ) (z : R) {K : ℕ}
    (hK : ∀ H ∈ DirectedHamiltonian.dirHamCycles A, arcWt w H ≤ K) :
    ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H =
      ∑ k ∈ range (K + 1), (dtourCount A w k : R) * z ^ k := by
  rw [← sum_fiberwise_of_maps_to (s := DirectedHamiltonian.dirHamCycles A) (t := range (K + 1))
    (g := arcWt w) (fun H hH => mem_range.2 (Nat.lt_succ_of_le (hK H hH)))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl (fun H hH => by rw [(mem_filter.1 hH).2]), sum_const, nsmul_eq_mul]
  rfl

/-- **Kronecker decoding of the directed tour polynomial.** If `c_k < 2^b` for every `k` and every
directed tour has weight `≤ K`, then the base-`2^b` digits of `T⃗_A(2^b) = Σ_H 2^{b·w(H)}` are the
`c_k`: `T⃗_A(2^b) / 2^{bj} mod 2^b = c_j` for `j ≤ K`. -/
theorem dkronecker_decode (A : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℕ) (b : ℕ)
    (hb : ∀ k, dtourCount A w k < 2 ^ b) {K : ℕ}
    (hK : ∀ H ∈ DirectedHamiltonian.dirHamCycles A, arcWt w H ≤ K) {j : ℕ} (hj : j ≤ K) :
    (∑ H ∈ DirectedHamiltonian.dirHamCycles A, 2 ^ (b * arcWt w H)) / 2 ^ (b * j) % 2 ^ b =
      dtourCount A w j := by
  have h := Hamiltonian.digits_sum_range (B := 2 ^ b) (by positivity) (K + 1)
    (fun k => dtourCount A w k) hb j
  rw [if_pos (Nat.lt_succ_of_le hj)] at h
  rw [← h, pow_mul]
  congr 2
  simp only [pow_mul]
  rw [sum_pow_arcWt_eq_sum_dtourCount A w (2 ^ b) hK]
  rfl

/-- A sufficient precision for the decoding: `2^{|A|} < 2^b`, e.g. `b = |A| + 1`. -/
theorem dtourCount_lt (A : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℕ) {b : ℕ}
    (hb : 2 ^ A.card < 2 ^ b) (k : ℕ) : dtourCount A w k < 2 ^ b :=
  lt_of_le_of_lt ((dtourCount_le_card A w k).trans (card_dirHamCycles_le_two_pow A)) hb

/-! ### The assembled math layer for ATSP -/

/-- **ATSP, mathematical layer.** For a digraph `A` on `Fin n`, arc weights `w ≤ W`, any root `r`,
partition `β`, crossing order `X` and precision `b` with `2^{|A|} < 2^b`, the labelled blob sum at
`z = 2^b`,

  `Z := Σ_{ℓ ∈ L_d^m} Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I^w_a(ℓ)`,

is the integer `T⃗_A(2^b) = Σ_{H ∈ DHC(A)} 2^{b·w(H)}`, and its base-`2^b` digits are the numbers
of directed tours of each weight: for every `j ≤ n·W`, `Z / 2^{bj} mod 2^b = c_j`. -/
theorem atsp_blob_factorisation {g m : ℕ} {A : Finset (Fin n × Fin n)} {β : Fin n → Fin g}
    (X : DCrossing A β m) (r : Fin n) (w : Fin n × Fin n → ℕ) {W : ℕ} (hw : ∀ e, w e ≤ W)
    {b : ℕ} (hb : 2 ^ A.card < 2 ^ b) :
    (∑ ℓ : Fin m → DLabel, ∏ a, X.chords.sigma (dlabelPar ℓ) a *
        X.chords.chi (dlabelPar ℓ) a (fun p => X.chords.P (dlabelPar ℓ) p.1 p.2) *
        X.Iw r (2 ^ b) w ℓ a) =
      ((∑ H ∈ DirectedHamiltonian.dirHamCycles A, 2 ^ (b * arcWt w H) : ℕ) : ℤ) ∧
    ∀ j ≤ n * W,
      (∑ H ∈ DirectedHamiltonian.dirHamCycles A, 2 ^ (b * arcWt w H)) / 2 ^ (b * j) % 2 ^ b =
        dtourCount A w j := by
  refine ⟨?_, fun j hj => dkronecker_decode A w b (dtourCount_lt A w hb)
    (fun H hH => arcWt_le_of_mem_dirHamCycles A hw hH) hj⟩
  rw [dblob_factorisation_w]
  push_cast
  refine sum_congr rfl fun H _ => ?_
  rw [pow_mul]

end EthFollowup.ExactHC
