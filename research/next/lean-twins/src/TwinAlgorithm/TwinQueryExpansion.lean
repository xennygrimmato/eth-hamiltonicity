import TwinAlgorithm.TwinFormula
import PrimeAlgorithm.IntegerCountQueryFinal
import EthFollowup.Primes.TwinKernelCount

/-! # The twin numerator as a weighted sum of doubled-descriptor counts

`gaussian (twinNumerator b D N)` is a polynomial-size sum, over pairs of Ni's
query indices, of an external Gaussian-integer coefficient times the exact count
of the doubled (eight-kernel) descriptor `TwinKernel.twinValue`. -/

set_option maxHeartbeats 2000000
noncomputable section
namespace TwinAlgorithm.TwinQueryExpansion
open Finset PrimeAlgorithm PrimeAlgorithm.CertifiedCauchy PrimeAlgorithm.CertifiedNumerator
  PrimeAlgorithm.CertifiedPrimeSum PrimeAlgorithm.IntegerPrimeSum PrimeAlgorithm.DoubleRamanujan
  PrimeAlgorithm.IntegerKernelExpansion PrimeAlgorithm.CountQueryExpansion
  PrimeAlgorithm.CountWitnessReindex TwinAlgorithm.TwinFormula
  EthFollowup.Primes.CountKernel EthFollowup.Primes.TwinKernel

/-! ## The four-kernel expansion at a single witness -/

/-- The value of one copy's kernel product at one witness. -/
def pointNumerator (b N jM jN : ℕ) (D : PrimeData) (v : Base) : GaussianInt :=
  ∏ k : Fin 4, gaussian (numerator (coefficientBits b) (reciprocalBits b) (nodeCount b)
    (slotData D jM jN k) (kernelNumer v k) (kernelDenom (binParameters N jM jN) v k))

/-- The query-indexed count contribution of one witness. -/
def pointCount (b N jM jN : ℕ) (D : PrimeData) (indices : NodeChoices b) (σ : Fin 4 → Bool)
    (v : Base) : ℕ :=
  if (fun k => horizontalBranch b N jM jN D k (indices k) v) = σ then
    ∏ k, quotient b N jM jN D k (indices k) v else 0

theorem count_singleton {W : Type*} [DecidableEq W] (v : W) (q : Fin 4 → W → ℕ)
    (neg : W → Fin 4 → Bool) (σ : Fin 4 → Bool) :
    KernelSumExpansion.count {v} (fun _ => 1) q neg σ = if neg v = σ then ∏ i, q i v else 0 := by
  unfold KernelSumExpansion.count
  rw [filter_singleton]
  split_ifs <;> simp

theorem point_expansion {b : ℕ} {D : PrimeData} (hD : Certified b D) (N jM jN : ℕ) (v : Base) :
    pointNumerator b N jM jN D v =
      ∑ indices : NodeChoices b, ∑ σ : Fin 4 → Bool,
        queryCoefficient b jM jN D indices σ * (pointCount b N jM jN D indices σ v : GaussianInt) := by
  classical
  have hu (j : ℕ) (hj : j < nodeCount b) : 0 ≤ (D.pole j).1 :=
    (CertifiedCoordinateBounds.pole_real_positive hD.phase (mem_range.mpr hj)).le
  unfold pointNumerator
  have hex (k : Fin 4) := numerator_expansion (coefficientBits b) (reciprocalBits b) (nodeCount b)
    (slotData D jM jN k) (kernelNumer v k) (kernelDenom (binParameters N jM jN) v k)
    (by simpa only [slotData_pole] using hu)
  simp_rw [hex]
  simp only [slotData_pole]
  change (∏ k : Fin 4, ∑ a : NodeChoice b, coefficient b jM jN D k a
      (horizontalBranch b N jM jN D k a v) * (quotient b N jM jN D k a v : GaussianInt)) = _
  have hexp := KernelSumExpansion.four_partitioned_expansion
    ({v} : Finset Base) (fun _ => 1)
    (fun k a => coefficient b jM jN D k a)
    (fun k a v => quotient b N jM jN D k a v)
    (fun k a v => horizontalBranch b N jM jN D k a v)
  simp only [Nat.cast_one, one_mul, sum_singleton] at hexp
  rw [hexp]
  apply sum_congr rfl
  intro indices _
  apply sum_congr rfl
  intro σ _
  rw [count_singleton]
  rfl

/-! ## Witnesses with a fixed value of `n` -/

theorem fibre_sum {M n : ℕ} (hn : n ∈ Icc 2 M) (F : Base → GaussianInt) :
    (∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors.filter (fun d => 2 ≤ n/d),
      ∑ y ∈ unitsBelow d, F ![n,d,n/d,x,y]) =
      ∑ v ∈ baseWitnesses M, if v 0 = n then F v else 0 := by
  rw [← original_sum M (fun v => if v 0 = n then F v else 0)]
  symm
  rw [sum_eq_single n]
  · apply sum_congr rfl; intro x _
    apply sum_congr rfl; intro d _
    apply sum_congr rfl; intro y _
    exact if_pos rfl
  · intro m _ hmn
    apply sum_eq_zero; intro x _
    apply sum_eq_zero; intro d _
    apply sum_eq_zero; intro y _
    exact if_neg hmn
  · intro h
    exact absurd hn h

def baseNumerator (b : ℕ) (D : PrimeData) (v : Base) : GaussianInt :=
  gaussian (productNumerator b D (v 0) (v 1) (v 3) (v 4))

theorem indicatorNumerator_fibre {b M n : ℕ} (D : PrimeData) (hn : n ∈ Icc 2 M) :
    gaussian (indicatorNumerator b D n) =
      -∑ v ∈ baseWitnesses M, if v 0 = n then baseNumerator b D v else 0 := by
  rw [indicatorNumerator, gaussian_neg, gaussian_sum]
  congr 1
  rw [← fibre_sum hn (baseNumerator b D)]
  apply sum_congr rfl
  intro x _
  rw [gaussian_sum]
  symm
  rw [← sum_filter_add_sum_filter_not (n.divisors) (fun d => 2 ≤ n/d)]
  have hzero : ∑ d ∈ n.divisors.filter (fun d => ¬ 2 ≤ n/d),
      gaussian (∑ y ∈ unitsBelow d, productNumerator b D n d x y) = 0 := by
    apply sum_eq_zero
    intro d hd
    have hsmall : n/d < 2 := by have := (mem_filter.mp hd).2; omega
    simp [IntegerCountQueryFinal.productNumerator_zero hsmall]
  rw [hzero, add_zero]
  apply sum_congr rfl
  intro d _
  rw [gaussian_sum]
  apply sum_congr rfl
  intro y _
  simp [baseNumerator]

theorem mem_baseWitnesses_range {M : ℕ} {v : Base} (hv : v ∈ baseWitnesses M) :
    v 0 ∈ Icc 2 M := by
  obtain ⟨h1, h2, _⟩ := mem_baseWitnesses.mp hv
  exact mem_Icc.mpr ⟨h1, h2⟩

theorem sum_ite_link {N : ℕ} {x : GaussianInt} {v₂ : Base} (m : ℕ) (hm : m ∈ Icc 2 N) :
    (∑ n ∈ Icc 2 N, if m = n ∧ v₂ 0 = n + 2 then x else 0) =
      if v₂ 0 = m + 2 then x else 0 := by
  rw [sum_eq_single m]
  · simp
  · intro n _ hnm
    simp [Ne.symm hnm]
  · intro h; exact absurd hm h

/-- The twin numerator as a sum over linked pairs of base witnesses. -/
theorem twinNumerator_pairs (b : ℕ) (D : PrimeData) (N : ℕ) :
    gaussian (twinNumerator b D N) =
      ∑ v₁ ∈ baseWitnesses N, ∑ v₂ ∈ (baseWitnesses (N+2)).filter (fun v₂ => v₂ 0 = v₁ 0 + 2),
        baseNumerator b D v₁ * baseNumerator b D v₂ := by
  classical
  rw [twinNumerator, gaussian_sum]
  have h1 : ∀ n ∈ Icc 2 N, gaussian (multiply (indicatorNumerator b D n)
      (indicatorNumerator b D (n+2))) =
      ∑ v₁ ∈ baseWitnesses N, ∑ v₂ ∈ baseWitnesses (N+2),
        if v₁ 0 = n ∧ v₂ 0 = n + 2 then baseNumerator b D v₁ * baseNumerator b D v₂ else 0 := by
    intro n hn
    have hn2 : n + 2 ∈ Icc 2 (N+2) := by
      obtain ⟨a, c⟩ := mem_Icc.mp hn; exact mem_Icc.mpr ⟨by omega, by omega⟩
    rw [gaussian_multiply, indicatorNumerator_fibre (b := b) D hn,
      indicatorNumerator_fibre (b := b) D hn2, neg_mul_neg, sum_mul_sum]
    apply sum_congr rfl
    intro v₁ _
    apply sum_congr rfl
    intro v₂ _
    by_cases ha : v₁ 0 = n <;> by_cases hc : v₂ 0 = n + 2 <;> simp [ha, hc]
  rw [sum_congr rfl h1, sum_comm]
  apply sum_congr rfl
  intro v₁ hv₁
  rw [sum_comm, sum_filter]
  apply sum_congr rfl
  intro v₂ _
  rw [sum_ite_link (v₁ 0) (mem_baseWitnesses_range hv₁)]

/-! ## One pair of bins -/

theorem sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (w : Finset δ) (f : α → β → γ → δ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ w, f a b c d) =
      ∑ c ∈ u, ∑ d ∈ w, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc _ = ∑ a ∈ s, ∑ c ∈ u, ∑ d ∈ w, ∑ b ∈ t, f a b c d :=
        sum_congr rfl fun a _ => sum_comm.trans (sum_congr rfl fun c _ => sum_comm)
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ w, ∑ b ∈ t, f a b c d := sum_comm
    _ = _ := sum_congr rfl fun c _ => sum_comm

abbrev Choice (b : ℕ) := NodeChoices b × (Fin 4 → Bool)

theorem filter_eq_bases {b N jM jN : ℕ} {D : PrimeData} (hD : Certified b D)
    (indices : NodeChoices b) (σ : Fin 4 → Bool) (unitD : Bool) :
    (binWitnesses N jM jN unitD).filter
      (fun v => (fun k => horizontalBranch b N jM jN D k (indices k) v) = σ) =
      bases (parameters b N jM jN D indices) (queryBranch unitD indices σ) := by
  ext v
  rw [mem_filter, mem_bases, core_iff hD]

theorem quotient_eq_kernel {b N jM jN : ℕ} {D : PrimeData} (hD : Certified b D)
    {indices : NodeChoices b} {σ : Fin 4 → Bool} {unitD : Bool} {v : Base}
    (hv : v ∈ bases (parameters b N jM jN D indices) (queryBranch unitD indices σ)) :
    ∏ k, quotient b N jM jN D k (indices k) v =
      ∏ k, kernelQuotient (parameters b N jM jN D indices) (queryBranch unitD indices σ) v k := by
  have hsg := ((core_iff hD indices σ unitD v).mp (mem_bases.mp hv)).2
  apply prod_congr rfl
  intro k _
  simp only [quotient, componentQuotient, kernelQuotient, kernelDenom, parameters, queryBranch,
    binParameters, ← congrFun hsg k, horizontalBranch]

theorem pair_count {b N jM₁ jN₁ jM₂ jN₂ : ℕ} {D : PrimeData} (hD : Certified b D)
    (u₁ u₂ : Bool) (p₁ p₂ : Choice b) :
    (∑ v₁ ∈ binWitnesses N jM₁ jN₁ u₁, ∑ v₂ ∈ binWitnesses (N+2) jM₂ jN₂ u₂,
      if v₂ 0 = v₁ 0 + 2 then pointCount b N jM₁ jN₁ D p₁.1 p₁.2 v₁ *
        pointCount b (N+2) jM₂ jN₂ D p₂.1 p₂.2 v₂ else 0) =
      twinValue (parameters b N jM₁ jN₁ D p₁.1) (queryBranch u₁ p₁.1 p₁.2)
        (parameters b (N+2) jM₂ jN₂ D p₂.1) (queryBranch u₂ p₂.1 p₂.2) := by
  classical
  unfold twinValue
  rw [← filter_eq_bases hD p₁.1 p₁.2 u₁, ← filter_eq_bases hD p₂.1 p₂.2 u₂, sum_filter]
  apply sum_congr rfl
  intro v₁ hv₁
  by_cases h₁ : (fun k => horizontalBranch b N jM₁ jN₁ D k (p₁.1 k) v₁) = p₁.2
  · rw [if_pos h₁, sum_filter]
    have hb₁ : v₁ ∈ bases (parameters b N jM₁ jN₁ D p₁.1) (queryBranch u₁ p₁.1 p₁.2) := by
      rw [← filter_eq_bases hD]; exact mem_filter.mpr ⟨hv₁, h₁⟩
    apply sum_congr rfl
    intro v₂ hv₂
    by_cases h₂ : (fun k => horizontalBranch b (N+2) jM₂ jN₂ D k (p₂.1 k) v₂) = p₂.2
    · have hb₂ : v₂ ∈ bases (parameters b (N+2) jM₂ jN₂ D p₂.1) (queryBranch u₂ p₂.1 p₂.2) := by
        rw [← filter_eq_bases hD]; exact mem_filter.mpr ⟨hv₂, h₂⟩
      simp only [pointCount, if_pos h₁, if_pos h₂, quotient_eq_kernel hD hb₁,
        quotient_eq_kernel hD hb₂]
    · simp only [pointCount, if_neg h₂, mul_zero, ite_self]
  · rw [if_neg h₁]
    apply sum_eq_zero
    intro v₂ _
    simp only [pointCount, if_neg h₁, zero_mul, ite_self]

/-- The contribution of one pair of bins, expanded over the eight node choices and signs. -/
theorem pair_bin {b N jM₁ jN₁ jM₂ jN₂ : ℕ} {D : PrimeData} (hD : Certified b D)
    (u₁ u₂ : Bool) :
    (∑ v₁ ∈ binWitnesses N jM₁ jN₁ u₁, ∑ v₂ ∈ binWitnesses (N+2) jM₂ jN₂ u₂,
      if v₂ 0 = v₁ 0 + 2 then baseNumerator b D v₁ * baseNumerator b D v₂ else 0) =
      ∑ p₁ : Choice b, ∑ p₂ : Choice b,
        queryCoefficient b jM₁ jN₁ D p₁.1 p₁.2 * queryCoefficient b jM₂ jN₂ D p₂.1 p₂.2 *
          (twinValue (parameters b N jM₁ jN₁ D p₁.1) (queryBranch u₁ p₁.1 p₁.2)
            (parameters b (N+2) jM₂ jN₂ D p₂.1) (queryBranch u₂ p₂.1 p₂.2) : GaussianInt) := by
  classical
  have hpt : ∀ M jM jN u, ∀ v ∈ binWitnesses M jM jN u, baseNumerator b D v =
      ∑ p : Choice b, queryCoefficient b jM jN D p.1 p.2 *
        (pointCount b M jM jN D p.1 p.2 v : GaussianInt) := by
    intro M jM jN u v hv
    rw [baseNumerator, ← bin_term_eq_actual hv]
    rw [show (∏ k : Fin 4, gaussian (numerator (coefficientBits b) (reciprocalBits b) (nodeCount b)
      (slotData D jM jN k) (kernelNumer v k) (kernelDenom (binParameters M jM jN) v k))) =
      pointNumerator b M jM jN D v from rfl, point_expansion hD, Fintype.sum_prod_type]
  have hstep : (∑ v₁ ∈ binWitnesses N jM₁ jN₁ u₁, ∑ v₂ ∈ binWitnesses (N+2) jM₂ jN₂ u₂,
      if v₂ 0 = v₁ 0 + 2 then baseNumerator b D v₁ * baseNumerator b D v₂ else 0) =
      ∑ v₁ ∈ binWitnesses N jM₁ jN₁ u₁, ∑ v₂ ∈ binWitnesses (N+2) jM₂ jN₂ u₂,
        ∑ p₁ : Choice b, ∑ p₂ : Choice b,
          queryCoefficient b jM₁ jN₁ D p₁.1 p₁.2 * queryCoefficient b jM₂ jN₂ D p₂.1 p₂.2 *
            ((if v₂ 0 = v₁ 0 + 2 then pointCount b N jM₁ jN₁ D p₁.1 p₁.2 v₁ *
              pointCount b (N+2) jM₂ jN₂ D p₂.1 p₂.2 v₂ else 0 : ℕ) : GaussianInt) := by
    apply sum_congr rfl
    intro v₁ hv₁
    apply sum_congr rfl
    intro v₂ hv₂
    rw [hpt N jM₁ jN₁ u₁ v₁ hv₁, hpt (N+2) jM₂ jN₂ u₂ v₂ hv₂, sum_mul_sum]
    split_ifs with h
    · apply sum_congr rfl; intro p₁ _
      apply sum_congr rfl; intro p₂ _
      push_cast; ring
    · simp
  rw [hstep, sum_comm4]
  apply sum_congr rfl
  intro p₁ _
  apply sum_congr rfl
  intro p₂ _
  rw [← pair_count hD u₁ u₂ p₁ p₂]
  simp only [Nat.cast_sum, mul_sum]

end TwinAlgorithm.TwinQueryExpansion
