import TwinAlgorithm.TwinQueryExpansion

/-! The complete twin numerator equals a polynomial-size weighted sum of exact
doubled-descriptor counts, indexed by pairs of Ni's prime-counting query indices. -/

set_option maxHeartbeats 2000000
noncomputable section
namespace TwinAlgorithm.TwinQueryFinal
open Finset PrimeAlgorithm PrimeAlgorithm.CertifiedCauchy PrimeAlgorithm.CertifiedPrimeSum
  PrimeAlgorithm.IntegerKernelExpansion PrimeAlgorithm.CountQueryExpansion
  PrimeAlgorithm.CountWitnessReindex PrimeAlgorithm.IntegerCountQueryFinal
  TwinAlgorithm.TwinFormula TwinAlgorithm.TwinQueryExpansion
  EthFollowup.Primes.CountKernel EthFollowup.Primes.TwinKernel

abbrev TwinIndex (b : ℕ) := QueryIndex b × QueryIndex b

def twinCoefficient (b : ℕ) (D : PrimeData) (q : TwinIndex b) : GaussianInt :=
  coefficient b D q.1 * coefficient b D q.2

def twinQueryCount (b N : ℕ) (D : PrimeData) (q : TwinIndex b) : ℕ :=
  twinValue (queryParameters b N D q.1) (branch b q.1)
    (queryParameters b (N+2) D q.2) (branch b q.2)

def twinQueryNumerator (b N : ℕ) (D : PrimeData) : GaussianInt :=
  ∑ q : TwinIndex b, twinCoefficient b D q * (twinQueryCount b N D q : GaussianInt)

abbrev Bin (b : ℕ) := Fin (b+1) × Fin (b+1) × Bool

theorem bins_sum {α : Type*} [AddCommMonoid α] {M b : ℕ} (hM : M ≤ 2^b) (F : Base → α) :
    (∑ v ∈ baseWitnesses M, F v) = ∑ a : Bin b, ∑ v ∈ binWitnesses M a.1 a.2.1 a.2.2, F v := by
  rw [sum_bins hM]
  simp only [Fintype.sum_prod_type]
  simp only [← Fin.sum_univ_eq_sum_range]

theorem sum_four {B C M : Type*} [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : (B × B) × (C × C) → M) :
    ∑ x, f x = ∑ a₁, ∑ a₂, ∑ p₁, ∑ p₂, f ((a₁, a₂), (p₁, p₂)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply sum_congr rfl; intro a₁ _
  apply sum_congr rfl; intro a₂ _
  rw [Fintype.sum_prod_type]

def indexEquiv (b : ℕ) : (Bin b × Bin b) × (Choice b × Choice b) ≃ TwinIndex b where
  toFun x := ((x.1.1.1, x.1.1.2.1, x.1.1.2.2, x.2.1.1, x.2.1.2),
    (x.1.2.1, x.1.2.2.1, x.1.2.2.2, x.2.2.1, x.2.2.2))
  invFun q := (((q.1.1, q.1.2.1, q.1.2.2.1), (q.2.1, q.2.2.1, q.2.2.2.1)),
    ((q.1.2.2.2.1, q.1.2.2.2.2), (q.2.2.2.2.1, q.2.2.2.2.2)))
  left_inv := by rintro ⟨⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩, ⟨⟨g, h⟩, ⟨i, j⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c, d, e⟩, ⟨f, g, h, i, j⟩⟩; rfl

/-- The actual integer numerator of the analytic twin formula is a polynomial-size
weighted sum of the concrete doubled-descriptor counts. -/
theorem twinNumerator_eq_queries {N b : ℕ} {D : PrimeData}
    (hN : N + 2 ≤ 2^b) (hD : Certified b D) :
    gaussian (twinNumerator b D N) = twinQueryNumerator b N D := by
  classical
  have hN1 : N ≤ 2^b := le_trans (by omega) hN
  rw [twinNumerator_pairs]
  have hinner : ∀ v₁ : Base, (∑ v₂ ∈ (baseWitnesses (N+2)).filter (fun v₂ => v₂ 0 = v₁ 0 + 2),
      baseNumerator b D v₁ * baseNumerator b D v₂) =
      ∑ a₂ : Bin b, ∑ v₂ ∈ binWitnesses (N+2) a₂.1 a₂.2.1 a₂.2.2,
        if v₂ 0 = v₁ 0 + 2 then baseNumerator b D v₁ * baseNumerator b D v₂ else 0 := by
    intro v₁
    rw [sum_filter, bins_sum hN]
  rw [sum_congr rfl (fun v₁ _ => hinner v₁), bins_sum hN1]
  have hswap : ∀ a₁ : Bin b, (∑ v₁ ∈ binWitnesses N a₁.1 a₁.2.1 a₁.2.2, ∑ a₂ : Bin b,
      ∑ v₂ ∈ binWitnesses (N+2) a₂.1 a₂.2.1 a₂.2.2,
        if v₂ 0 = v₁ 0 + 2 then baseNumerator b D v₁ * baseNumerator b D v₂ else 0) =
      ∑ a₂ : Bin b, ∑ p₁ : Choice b, ∑ p₂ : Choice b,
        queryCoefficient b a₁.1 a₁.2.1 D p₁.1 p₁.2 * queryCoefficient b a₂.1 a₂.2.1 D p₂.1 p₂.2 *
          (twinValue (parameters b N a₁.1 a₁.2.1 D p₁.1) (queryBranch a₁.2.2 p₁.1 p₁.2)
            (parameters b (N+2) a₂.1 a₂.2.1 D p₂.1) (queryBranch a₂.2.2 p₂.1 p₂.2) :
              GaussianInt) := by
    intro a₁
    rw [sum_comm]
    apply sum_congr rfl
    intro a₂ _
    exact pair_bin hD a₁.2.2 a₂.2.2
  rw [sum_congr rfl (fun a₁ _ => hswap a₁)]
  unfold twinQueryNumerator
  rw [← Fintype.sum_equiv (indexEquiv b) _ _ (fun _ => rfl), sum_four]
  apply sum_congr rfl; intro a₁ _
  apply sum_congr rfl; intro a₂ _
  apply sum_congr rfl; intro p₁ _
  apply sum_congr rfl; intro p₂ _
  have hc : twinCoefficient b D (indexEquiv b ((a₁, a₂), (p₁, p₂))) =
      queryCoefficient b a₁.1 a₁.2.1 D p₁.1 p₁.2 * queryCoefficient b a₂.1 a₂.2.1 D p₂.1 p₂.2 :=
    neg_mul_neg _ _
  have hq : twinQueryCount b N D (indexEquiv b ((a₁, a₂), (p₁, p₂))) =
      twinValue (parameters b N a₁.1 a₁.2.1 D p₁.1) (queryBranch a₁.2.2 p₁.1 p₁.2)
        (parameters b (N+2) a₂.1 a₂.2.1 D p₂.1) (queryBranch a₂.2.2 p₂.1 p₂.2) := rfl
  rw [hc, hq]

theorem twinResult_queries {N b : ℕ} {D : PrimeData} (hN : N + 2 ≤ 2^b) (hb : 1 ≤ b)
    (hD : Certified b D) :
    twinResult b (twinQueryNumerator b N D).re = (twinCount N : ℤ) := by
  rw [← twinNumerator_eq_queries hN hD]
  exact twinResult_eq hN hb hD

end TwinAlgorithm.TwinQueryFinal
