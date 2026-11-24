import TwinAlgorithm.TwinQueryFinal
import PrimeAlgorithm.CountQueryEnumeration
import EthFollowup.Primes.TwinKernelQuery

/-! Explicit enumeration of all twin queries (pairs of Ni's raw query indices),
with their exact integer weights, computed in polynomial time, and one counted
network package that answers each of them exactly. -/

set_option maxHeartbeats 3000000
noncomputable section
namespace TwinAlgorithm.TwinEnumeration
open Groundwork Finset PrimeAlgorithm PrimeAlgorithm.CertifiedCauchy PrimeAlgorithm.CertifiedPrimeSum
  PrimeAlgorithm.CertifiedNumerator PrimeAlgorithm.IntegerKernelExpansion
  PrimeAlgorithm.CountQueryExpansion PrimeAlgorithm.CertifiedGenerator
  PrimeAlgorithm.IntegerCountQueryFinal PrimeAlgorithm.CountQueryEnumeration
  TwinAlgorithm.TwinQueryFinal EthFollowup.Primes.CountKernel EthFollowup.Primes.TwinKernel

/-! ## A larger fixed linear padding (factor 4096) -/

def pad2 (w : List Bool) : List Bool := EthFollowup.Primes.LinearPadding.repeated 12 w

theorem pad2_polyT : PolyT pad2 := EthFollowup.Primes.LinearPadding.repeated_polyT 12

theorem pad2_value (w : List Bool) : Groundwork.ofWord (pad2 w) = Groundwork.ofWord w :=
  EthFollowup.Primes.LinearPadding.repeated_value 12 w

theorem pad2_length (w : List Bool) : (pad2 w).length + 1 = 4096 * (w.length + 1) := by
  simpa [pad2] using EthFollowup.Primes.LinearPadding.repeated_length 12 w

theorem pad2_length_bounds (w : List Bool) :
    w.length ≤ (pad2 w).length ∧ (pad2 w).length + 2 ≤ 4097 * (w.length + 2) := by
  have := pad2_length w
  omega

theorem box_width_fits2 {w : List Bool} {b : ℕ} (hb : b ≤ w.length + 1) :
    5 * CertifiedCoordinateBounds.inputBits b + 2 ≤ (pad2 w).length := by
  have := pad2_length w
  unfold CertifiedCoordinateBounds.inputBits
  omega

theorem query_width_fits2 {w : List Bool} {b : ℕ} (hb : b ≤ w.length + 1) :
    48 * CertifiedCoordinateBounds.inputBits b ≤ (pad2 w).length := by
  have := pad2_length w
  unfold CertifiedCoordinateBounds.inputBits
  omega

theorem twin_query_fits {w : List Bool} {b : ℕ} (hb : b ≤ w.length + 1)
    (xs : List ℕ) (hlen : xs.length = 48)
    (hx : ∀ x ∈ xs, x < 2 ^ CertifiedCoordinateBounds.inputBits b) :
    (EthFollowup.ModP.encodeList xs).length ≤ (pad2 w).length := by
  rw [EthFollowup.ModP.length_encodeList, hlen]
  apply le_trans (Nat.mul_le_mul_left 48 ?_) (query_width_fits2 hb)
  apply EthFollowup.ModP.blockLen_le
  intro x hx'
  rw [← EthFollowup.ModP.bits_eq_encodeNat]
  exact EthFollowup.ModP.bits_length_le (hx x hx')

/-! ## Weights and query words -/

/-- Ni's four-factor coefficient chain (without the overall sign). -/
def chain (b : ℕ) (q : RawIndex) : GaussianIntPair :=
  multiply (multiply (multiply (coefficientPair b q 0) (coefficientPair b q 1))
    (coefficientPair b q 2)) (coefficientPair b q 3)

theorem gaussian_chain (b : ℕ) (q : QueryIndex b) :
    gaussian (chain b (encodeIndex q)) =
      queryCoefficient b q.1 q.2.1 (generate b) q.2.2.2.1 q.2.2.2.2 := by
  simp only [chain, gaussian_multiply, coefficientPair_encodeIndex, queryCoefficient,
    Fin.prod_univ_four]

def twinWeight (b : ℕ) (r : RawIndex × RawIndex) : ℤ := (multiply (chain b r.1) (chain b r.2)).1

def twinWordQuery (b N : ℕ) (r : RawIndex × RawIndex) : List Bool :=
  twinQuery (rawParameters b N r.1) (rawBranch r.1) (rawParameters b (N+2) r.2) (rawBranch r.2)

def twinEnumerate (b : ℕ) : List (RawIndex × RawIndex) := (enumerate b).product (enumerate b)

def items (b N : ℕ) : List (List Bool × ℤ) :=
  (twinEnumerate b).map fun r => (twinWordQuery b N r, twinWeight b r)

theorem twinWeight_encode (b : ℕ) (q : TwinIndex b) :
    twinWeight b (encodeIndex q.1, encodeIndex q.2) = (twinCoefficient b (generate b) q).re := by
  have h : gaussian (multiply (chain b (encodeIndex q.1)) (chain b (encodeIndex q.2))) =
      twinCoefficient b (generate b) q := by
    rw [gaussian_multiply, gaussian_chain, gaussian_chain, twinCoefficient,
      IntegerCountQueryFinal.coefficient, IntegerCountQueryFinal.coefficient, neg_mul_neg]
  rw [← h]
  rfl

theorem twinWordQuery_encode (b N : ℕ) (q : TwinIndex b) :
    twinWordQuery b N (encodeIndex q.1, encodeIndex q.2) =
      twinQuery (queryParameters b N (generate b) q.1) (branch b q.1)
        (queryParameters b (N+2) (generate b) q.2) (branch b q.2) := by
  simp only [twinWordQuery, rawParameters_encodeIndex, rawBranch_encodeIndex]

theorem sum_product_map {α β M : Type*} [AddCommMonoid M] (l₁ : List α) (l₂ : List β)
    (f : α × β → M) :
    ((l₁.product l₂).map f).sum = (l₁.map fun a => (l₂.map fun c => f (a, c)).sum).sum := by
  induction l₁ with
  | nil => simp [List.product]
  | cons a l ih =>
    simp only [List.product, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_map, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    rfl

theorem sum_twinEnumerate {M : Type} [AddCommMonoid M] (b : ℕ) (f : RawIndex × RawIndex → M) :
    ((twinEnumerate b).map f).sum = ∑ q : TwinIndex b, f (encodeIndex q.1, encodeIndex q.2) := by
  rw [twinEnumerate, sum_product_map]
  simp_rw [sum_enumerate]
  rw [Fintype.sum_prod_type (f := fun q : TwinIndex b => f (encodeIndex q.1, encodeIndex q.2))]

private def realPart : GaussianInt →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_items_count (b N : ℕ) (C : List Bool → ℕ)
    (hC : ∀ q : TwinIndex b,
      C (twinQuery (queryParameters b N (generate b) q.1) (branch b q.1)
        (queryParameters b (N+2) (generate b) q.2) (branch b q.2)) =
        twinQueryCount b N (generate b) q) :
    ((items b N).map (fun item => item.2 * (C item.1 : ℤ))).sum =
      (twinQueryNumerator b N (generate b)).re := by
  unfold items
  rw [List.map_map, sum_twinEnumerate]
  simp only [Function.comp_apply, twinWordQuery_encode, twinWeight_encode]
  change _ = realPart (∑ q : TwinIndex b,
    twinCoefficient b (generate b) q * (twinQueryCount b N (generate b) q : GaussianInt))
  rw [map_sum]
  apply sum_congr rfl
  intro q _
  rw [hC q]
  change _ = (twinCoefficient b (generate b) q * (twinQueryCount b N (generate b) q : GaussianInt)).re
  simp [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]

/-! ## Polynomial time -/

section ProgramPoly
variable {α : Type} [Enc α]

theorem chain_polyT {b : α → ℕ} {q : α → RawIndex} (hb : Unary b) (hq : PolyT q) :
    PolyT fun x => chain (b x) (q x) :=
  multiply_polyT (multiply_polyT (multiply_polyT (coefficientPair_polyT hb hq 0)
    (coefficientPair_polyT hb hq 1)) (coefficientPair_polyT hb hq 2)) (coefficientPair_polyT hb hq 3)

theorem twinWeight_polyT {b : α → ℕ} {r : α → RawIndex × RawIndex} (hb : Unary b)
    (hr : PolyT r) : PolyT fun x => twinWeight (b x) (r x) :=
  PolyT.fst (multiply_polyT (chain_polyT hb (PolyT.fst hr)) (chain_polyT hb (PolyT.snd hr)))

theorem twinWordQuery_polyT {b N : α → ℕ} {r : α → RawIndex × RawIndex}
    (hb : Unary b) (hr : PolyT r) : PolyT fun x => twinWordQuery (b x) (N x) (r x) := by
  have hq₁ : PolyT fun x => (r x).1 := PolyT.fst hr
  have hq₂ : PolyT fun x => (r x).2 := PolyT.snd hr
  have hn₁ (k : Fin 4) : PolyT fun x => quadGet (r x).1.2.2.1 k :=
    quadGet_polyT (PolyT.fst (PolyT.snd (PolyT.snd hq₁))) k
  have hs₁ (k : Fin 4) : PolyT fun x => quadGet (r x).1.2.2.2 k :=
    quadGet_polyT (PolyT.snd (PolyT.snd (PolyT.snd hq₁))) k
  have hp₁ (k : Fin 4) := pole_polyT hb (PolyT.fst (hn₁ k))
  have hn₂ (k : Fin 4) : PolyT fun x => quadGet (r x).2.2.2.1 k :=
    quadGet_polyT (PolyT.fst (PolyT.snd (PolyT.snd hq₂))) k
  have hs₂ (k : Fin 4) : PolyT fun x => quadGet (r x).2.2.2.2 k :=
    quadGet_polyT (PolyT.snd (PolyT.snd (PolyT.snd hq₂))) k
  have hp₂ (k : Fin 4) := pole_polyT hb (PolyT.fst (hn₂ k))
  apply twinQuery_polyT
  · exact PolyT.two_pow (min_unary (PolyT.fst (PolyT.fst hq₁)) hb)
  · exact PolyT.two_pow (min_unary (PolyT.snd (PolyT.fst hq₁)) hb)
  · exact PolyT.two_pow (CountQueryPoly.reciprocalBits_unary hb)
  · intro k; exact PolyT.toNat (PolyT.fst (hp₁ k))
  · intro k; exact PolyT.natAbs (PolyT.snd (hp₁ k))
  · intro k; exact PolyT.two_pow (coefficientBits_unary hb)
  · exact PolyT.fst (PolyT.snd hq₁)
  · exact hs₁
  · intro k; exact PolyT.snd (hn₁ k)
  · exact PolyT.two_pow (min_unary (PolyT.fst (PolyT.fst hq₂)) hb)
  · exact PolyT.two_pow (min_unary (PolyT.snd (PolyT.fst hq₂)) hb)
  · exact PolyT.two_pow (CountQueryPoly.reciprocalBits_unary hb)
  · intro k; exact PolyT.toNat (PolyT.fst (hp₂ k))
  · intro k; exact PolyT.natAbs (PolyT.snd (hp₂ k))
  · intro k; exact PolyT.two_pow (coefficientBits_unary hb)
  · exact PolyT.fst (PolyT.snd hq₂)
  · exact hs₂
  · intro k; exact PolyT.snd (hn₂ k)

theorem items_polyT {b N : α → ℕ} (hb : Unary b) (hN : PolyT N) :
    PolyT fun x => items (b x) (N x) := by
  have hf : PolyT fun x : α × (RawIndex × RawIndex) => x.1 := PolyT.fst PolyT.id'
  have hq : PolyT fun x : α × (RawIndex × RawIndex) => x.2 := PolyT.snd PolyT.id'
  exact PolyT.map (f := fun x r => (twinWordQuery (b x) (N x) r, twinWeight (b x) r))
    (PolyT.prodMk (twinWordQuery_polyT (hb.comp hf) hq) (twinWeight_polyT (hb.comp hf) hq))
    (product_polyT (enumerate_polyT hb) (enumerate_polyT hb))
end ProgramPoly

/-! ## Every emitted twin query is answered exactly by one package -/

theorem mem_items (b N : ℕ) (item : List Bool × ℤ) :
    item ∈ items b N → ∃ q : TwinIndex b,
      item = (twinQuery (queryParameters b N (generate b) q.1) (branch b q.1)
        (queryParameters b (N+2) (generate b) q.2) (branch b q.2),
        (twinCoefficient b (generate b) q).re) := by
  intro h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  obtain ⟨hr₁, hr₂⟩ := List.mem_product.mp hr
  have hv₁ := (mem_enumerate b r.1).mp hr₁
  have hv₂ := (mem_enumerate b r.2).mp hr₂
  refine ⟨(decodeIndex r.1 hv₁, decodeIndex r.2 hv₂), ?_⟩
  have he : (encodeIndex (decodeIndex r.1 hv₁), encodeIndex (decodeIndex r.2 hv₂)) = r := by
    rw [encode_decode, encode_decode]
  rw [← twinWordQuery_encode, ← twinWeight_encode]
  simp only
  rw [he]

theorem twin_items_package_exists :
    ∃ pk : EthFollowup.ModP.CntPackage (2^22*268),
      (∀ w, pk.R w = w.length) ∧ (∀ w, pk.Ok w) ∧
      ∀ (b N : ℕ) (w : List Bool), Certified b (generate b) → N + 2 ≤ 2^b →
        Groundwork.ofWord w = N → b ≤ w.length + 1 →
        (∀ item ∈ items b N, item.1.length ≤ pk.R (pad2 w)) ∧
        ((items b N).map (fun item => item.2 * (pk.Q (pad2 w) item.1 : ℤ))).sum =
          (twinQueryNumerator b N (generate b)).re := by
  obtain ⟨pk, hR, hOk, hQ⟩ := twin_package_exact_exists
  refine ⟨pk, hR, hOk, ?_⟩
  intro b N w hD hN hw hb
  have hN1 : N ≤ 2^b := le_trans (by omega) hN
  have hq (q : TwinIndex b) :
      (twinQuery (queryParameters b N (generate b) q.1) (branch b q.1)
        (queryParameters b (N+2) (generate b) q.2) (branch b q.2)).length ≤ pk.R (pad2 w) ∧
      pk.Q (pad2 w) (twinQuery (queryParameters b N (generate b) q.1) (branch b q.1)
        (queryParameters b (N+2) (generate b) q.2) (branch b q.2)) =
        twinQueryCount b N (generate b) q := by
    have hM₁ : (q.1.1 : ℕ) ≤ b := by omega
    have hN₁ : (q.1.2.1 : ℕ) ≤ b := by omega
    have hM₂ : (q.2.1 : ℕ) ≤ b := by omega
    have hN₂ : (q.2.2.1 : ℕ) ≤ b := by omega
    constructor
    · rw [hR]
      apply twin_query_fits hb _ (twinQueryData_length _ _ _ _)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact CountQueryBounds.actual_queryData_lt hD hM₁ hN₁ q.1.2.2.2.1 q.1.2.2.2.2
          q.1.2.2.1 x h
      · exact CountQueryBounds.actual_queryData_lt hD hM₂ hN₂ q.2.2.2.2.1 q.2.2.2.2.2
          q.2.2.2.1 x h
    · apply hQ
      · rw [pad2_value, hw]; rfl
      · rfl
      · exact CountQueryBounds.parameters_bitBounds hD hN1 hM₁ hN₁ q.1.2.2.2.1
      · exact CountQueryBounds.parameters_bitBounds hD hN hM₂ hN₂ q.2.2.2.2.1
      · exact box_width_fits2 hb
  constructor
  · intro item hi
    obtain ⟨q, rfl⟩ := mem_items b N item hi
    exact (hq q).1
  · exact sum_items_count b N (pk.Q (pad2 w)) (fun q => (hq q).2)

end TwinAlgorithm.TwinEnumeration
