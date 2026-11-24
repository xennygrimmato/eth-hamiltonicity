/- The exact count of the doubled descriptor: a fibre product of two copies of
Ni's four-kernel count over the shared value `n` (with `n₂ = n + 2`). -/
import EthFollowup.Primes.TwinKernelDesc
import EthFollowup.Primes.CountKernelPadding

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section
namespace EthFollowup.Primes.TwinKernel
open Finset EthFollowup.ModP EthFollowup.Factoring EthFollowup.ExactHC
open EthFollowup.Primes.CountKernel

/-- The value of the doubled count: pairs of base witnesses whose `n`-values differ by two,
each weighted by the product of its four kernel quotients. -/
def twinValue (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch) : ℕ :=
  ∑ v₁ ∈ bases P₁ br₁, ∑ v₂ ∈ bases P₂ br₂,
    if v₂ 0 = v₁ 0 + 2 then (∏ k, kernelQuotient P₁ br₁ v₁ k) * ∏ k, kernelQuotient P₂ br₂ v₂ k
    else 0

/-- Ni's witness bijection, weighted by any function of the shared variable `x₀ = n`. -/
theorem solutions_sum {P : Parameters} {br : Branch} {b l : ℕ} (bx : ℕ)
    (hf : Fits P b l)
    (hbox : ∀ v, Core P br v → ∀ w, WeightBounds P br v w → ∀ i, canonical P br v w i < bx)
    (g : ℕ → ℕ) :
    ∑ x ∈ solutions P br b l bx, g (x 0) = ∑ v ∈ bases P br, g (v 0) * ∏ k, kernelQuotient P br v k := by
  classical
  have h1 : ∑ x ∈ solutions P br b l bx, g (x 0) = ∑ z ∈ indices P br, g (z.1 0) := by
    apply Finset.sum_nbij (fun x : Fin 72 → ℕ => (⟨baseOf x, weightsOf x⟩ : Σ _ : Base, Weights))
    · intro x hx
      have hr := ((mem_solutions hf x).1 hx).2
      exact mem_indices.mpr ⟨relations_core hr, relations_weights hr⟩
    · intro x hx y hy he
      have hxr := ((mem_solutions hf x).1 hx).2
      have hyr := ((mem_solutions hf y).1 hy).2
      have hb := congrArg (fun z : Σ _ : Base, Weights => z.1) he
      have hw := congrArg (fun z : Σ _ : Base, Weights => z.2) he
      change baseOf x = baseOf y at hb
      change weightsOf x = weightsOf y at hw
      rw [assignment_eq_canonical hxr, assignment_eq_canonical hyr, hb, hw]
    · rintro ⟨v, w⟩ hz
      obtain ⟨hc, hw⟩ := mem_indices.mp hz
      refine ⟨canonical P br v w, ?_, ?_⟩
      · exact (mem_solutions hf _).2 ⟨hbox v hc w hw, canonical_relations hc hw⟩
      · simp
    · intro x _
      rfl
  rw [h1, indices, sum_sigma]
  apply sum_congr rfl
  intro v _
  dsimp only
  rw [sum_const, card_weightSet, smul_eq_mul, mul_comm]

def twinSolutions (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (b l box : ℕ) : Finset (Fin 144 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 144 => range box).filter
    fun x => (twinDescriptor P₁ br₁ P₂ br₂ b l).D.Sat b (extV 144 x)

def first (x : Fin 144 → ℕ) : Fin 72 → ℕ := fun j => x (Fin.castAdd 72 j)
def second (x : Fin 144 → ℕ) : Fin 72 → ℕ := fun j => x (Fin.natAdd 72 j)

theorem extV_second (x : Fin 144 → ℕ) :
    (fun i => extV 144 x (i + 72)) = extV 72 (second x) := by
  funext i
  unfold extV second
  by_cases hi : i < 72
  · rw [dif_pos (by omega), dif_pos hi]
    congr 1
    apply Fin.ext
    simp only [Fin.natAdd_mk]
    omega
  · rw [dif_neg (by omega), dif_neg hi]

theorem extV_first (x : Fin 144 → ℕ) : ∀ i < 72, extV 144 x i = extV 72 (first x) i := by
  intro i hi
  unfold extV first
  rw [dif_pos (by omega), dif_pos hi]
  rfl

theorem mem_twinSolutions {P₁ P₂ : Parameters} {br₁ br₂ : Branch} {b l box : ℕ}
    (hf₁ : Fits P₁ b l) (hf₂ : Fits P₂ b l) (hb : 1 ≤ b) (hl : 1 ≤ l) (x : Fin 144 → ℕ) :
    x ∈ twinSolutions P₁ br₁ P₂ br₂ b l box ↔
      first x ∈ solutions P₁ br₁ b l box ∧ second x ∈ solutions P₂ br₂ b l box ∧
        second x 0 = first x 0 + 2 := by
  rw [twinSolutions, mem_filter, Fintype.mem_piFinset, twin_sat hf₁ hf₂, mem_solutions hf₁,
    mem_solutions hf₂, extV_second, relations_congr hf₁ hb hl (extV_first x)]
  have h72 : extV 144 x 72 = second x 0 := by
    simp only [extV, second]
    rw [dif_pos (by norm_num)]
    rfl
  have h0 : extV 144 x 0 = first x 0 := by
    simp only [extV, first]
    rw [dif_pos (by norm_num)]
    rfl
  rw [h72, h0]
  simp only [mem_range]
  constructor
  · rintro ⟨hx, h1, h2, h3⟩
    exact ⟨⟨fun j => hx _, h1⟩, ⟨fun j => hx _, h2⟩, h3⟩
  · rintro ⟨⟨hx1, h1⟩, ⟨hx2, h2⟩, h3⟩
    refine ⟨fun i => ?_, h1, h2, h3⟩
    refine Fin.addCases (m := 72) (n := 72) (motive := fun i => x i < box)
      (fun j => ?_) (fun j => ?_) i
    · exact hx1 j
    · exact hx2 j

theorem twinSolutions_card {P₁ P₂ : Parameters} {br₁ br₂ : Branch} {b l box : ℕ}
    (hf₁ : Fits P₁ b l) (hf₂ : Fits P₂ b l) (hb : 1 ≤ b) (hl : 1 ≤ l) :
    (twinSolutions P₁ br₁ P₂ br₂ b l box).card =
      ∑ x₁ ∈ solutions P₁ br₁ b l box, ∑ x₂ ∈ solutions P₂ br₂ b l box,
        if x₂ 0 = x₁ 0 + 2 then 1 else 0 := by
  classical
  have hc : (twinSolutions P₁ br₁ P₂ br₂ b l box).card =
      ((solutions P₁ br₁ b l box ×ˢ solutions P₂ br₂ b l box).filter
        fun p => p.2 0 = p.1 0 + 2).card := by
    apply card_nbij' (fun x => (first x, second x)) (fun p => Fin.append p.1 p.2)
    · intro x hx
      have h := (mem_twinSolutions hf₁ hf₂ hb hl x).1 hx
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product]
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    · rintro ⟨x₁, x₂⟩ hp
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at hp
      apply (mem_twinSolutions hf₁ hf₂ hb hl _).2
      have e1 : first (Fin.append x₁ x₂) = x₁ := by funext j; exact Fin.append_left x₁ x₂ j
      have e2 : second (Fin.append x₁ x₂) = x₂ := by funext j; exact Fin.append_right x₁ x₂ j
      rw [e1, e2]
      exact ⟨hp.1.1, hp.1.2, hp.2⟩
    · intro x _
      exact Fin.append_castAdd_natAdd
    · rintro ⟨x₁, x₂⟩ _
      have e1 : first (Fin.append x₁ x₂) = x₁ := by funext j; exact Fin.append_left x₁ x₂ j
      have e2 : second (Fin.append x₁ x₂) = x₂ := by funext j; exact Fin.append_right x₁ x₂ j
      simp only [e1, e2]
  rw [hc, card_filter, sum_product]

/-- The doubled descriptor counts the fibre product exactly. -/
theorem twin_descriptor_count {P₁ P₂ : Parameters} {br₁ br₂ : Branch} {b l : ℕ} (bx : ℕ → ℕ)
    (hf₁ : Fits P₁ b l) (hf₂ : Fits P₂ b l) (hb : 1 ≤ b) (hl : 1 ≤ l)
    (hbox₁ : ∀ v, Core P₁ br₁ v → ∀ w, WeightBounds P₁ br₁ v w →
      ∀ i, canonical P₁ br₁ v w i < bx 0)
    (hbox₂ : ∀ v, Core P₂ br₂ v → ∀ w, WeightBounds P₂ br₂ v w →
      ∀ i, canonical P₂ br₂ v w i < bx 0) :
    (twinDescriptor P₁ br₁ P₂ br₂ b l).countB b bx = twinValue P₁ br₁ P₂ br₂ := by
  classical
  change (twinSolutions P₁ br₁ P₂ br₂ b l (bx 0)).card = _
  rw [twinSolutions_card hf₁ hf₂ hb hl]
  have hin : ∀ x₁ : Fin 72 → ℕ, (∑ x₂ ∈ solutions P₂ br₂ b l (bx 0),
      if x₂ 0 = x₁ 0 + 2 then 1 else 0) =
      ∑ v₂ ∈ bases P₂ br₂, (if v₂ 0 = x₁ 0 + 2 then 1 else 0) *
        ∏ k, kernelQuotient P₂ br₂ v₂ k := fun x₁ =>
    solutions_sum (bx 0) hf₂ hbox₂ (fun m => if m = x₁ 0 + 2 then 1 else 0)
  simp_rw [hin]
  rw [solutions_sum (bx 0) hf₁ hbox₁ (fun m => ∑ v₂ ∈ bases P₂ br₂,
    (if v₂ 0 = m + 2 then 1 else 0) * ∏ k, kernelQuotient P₂ br₂ v₂ k)]
  unfold twinValue
  apply sum_congr rfl
  intro v₁ _
  rw [sum_mul]
  apply sum_congr rfl
  intro v₂ _
  split_ifs <;> ring

/-- The concrete doubled network at any sufficient input size. -/
theorem twin_count_at {P₁ P₂ : Parameters} {br₁ br₂ : Branch} {B n : ℕ}
    (hb₁ : BitBounds P₁ B) (hb₂ : BitBounds P₂ B) (hn : 5*B+2 ≤ n) :
    (twinActual P₁ br₁ P₂ br₂ n).count n = twinValue P₁ br₁ P₂ br₂ :=
  twin_descriptor_count (lbox n) (bitBounds_fits_at hb₁ hn) (bitBounds_fits_at hb₂ hn)
    (one_le_b n) (kl_pos n 0)
    (fun _ hc _ hw => canonical_lbox_bound_at hb₁ hn hc hw)
    (fun _ hc _ hw => canonical_lbox_bound_at hb₂ hn hc hw)

/-- Exact value, linear communication and the counted-network shape of the doubled network. -/
theorem twinNetwork_spec_at {P₁ P₂ : Parameters} {br₁ br₂ : Branch} {B n g : ℕ}
    (hb₁ : BitBounds P₁ B) (hb₂ : BitBounds P₂ B) (hn : 5*B+2 ≤ n) (hg : 2 ≤ g) :
    let net := (arithSys n (twinActual P₁ br₁ P₂ br₂ n) g hg).net (aLabCode n)
    net.value = ((twinValue P₁ br₁ P₂ br₂ : ℕ) : ℤ) ∧ net.U ≤ 2^19*268*(n+2) := by
  refine ⟨?_, twinNetwork_communication P₁ br₁ P₂ br₂ hg⟩
  rw [arithNet_value hg (twinActual_WF P₁ br₁ P₂ br₂ n)]
  congr 1
  exact twin_count_at hb₁ hb₂ hn

end EthFollowup.Primes.TwinKernel
