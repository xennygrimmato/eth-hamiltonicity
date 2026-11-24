import TwinAlgorithm.TwinEnumeration
import PrimeAlgorithm.PrimeMachineInput
import PrimeAlgorithm.CountQueryFinish
import EthFollowup.ModP.BatchCollect

/-! The twin-prime counting machine: Ni's batch-query machine
(`NatBatchQuery.machine_TM_linear_input`) run on the doubled-descriptor package,
with the twin query list and a final integer division by `2 · commonScale^8`. -/

set_option maxHeartbeats 1000000
noncomputable section
namespace TwinAlgorithm.TwinMachine
open Groundwork EthFollowup.ModP EthFollowup.Primes PrimeAlgorithm PrimeAlgorithm.PrimeMachineInput
  PrimeAlgorithm.CertifiedGenerator PrimeAlgorithm.CertifiedCauchy TwinAlgorithm.TwinFormula
  TwinAlgorithm.TwinQueryFinal TwinAlgorithm.TwinEnumeration
open PrimeAlgorithm.IntegerPrimeSum (commonScale)

abbrev Item := List Bool × ℤ

def rawItems (w : List Bool) : List Item := TwinEnumeration.items (precision w) (ofWord w)

def items (w : List Bool) : List Item := (rawItems w).filter fun q => decide (q.1.length ≤ w.length)

def finish (p : List Bool × List ℕ) : List Bool :=
  Nat.bits (twinResult (precision p.1) (CountQueryFinish.dot (items p.1) p.2)).toNat

def spec : NatBatchQuerySpec := BatchCollect.spec items finish

section Poly
variable {α : Type} [Enc α]

theorem twinResult_polyT {b : α → ℕ} {z : α → ℤ} (hb : Unary b) (hz : PolyT z) :
    PolyT (fun x => twinResult (b x) (z x)) := by
  have hs := CountQueryFinish.commonScale_polyT hb
  have hp : PolyT (fun x => (commonScale (b x) : ℤ) ^ 8) :=
    ClauseBound.ParityChecks.CertLib.powZ_polyT (PolyT.natCast hs) (Unary.const 8)
  have hn : PolyT (fun x => 2 * z x + (commonScale (b x) : ℤ) ^ 8) :=
    PolyT.addZ (PolyT.mulZ (PolyT.const 2) hz) hp
  have hd : PolyT (fun x => 2 * commonScale (b x) ^ 8) :=
    PolyT.mul (PolyT.const 2) (PolyT.pow_unary hs (Unary.const 8))
  exact (ClauseBound.ParityChecks.CertLib.divZ_polyT hn hd).congr (fun x => by
    simp only [twinResult, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow])
end Poly

theorem rawItems_polyT : PolyT rawItems :=
  TwinEnumeration.items_polyT precision_unary (by fun_prop)

theorem items_polyT : PolyT items := by
  apply PolyT.filter (f := fun (w : List Bool) (q : Item) => decide (q.1.length ≤ w.length))
  · fun_prop
  · exact rawItems_polyT

theorem finish_polyT : PolyT finish := by
  have hB : Unary (fun p : List Bool × List ℕ => precision p.1) :=
    precision_unary.comp PolyT.id'.fst
  have hI : PolyT (fun p : List Bool × List ℕ => items p.1) := items_polyT.comp PolyT.id'.fst
  have hD := CountQueryFinish.dot_polyT hI (PolyT.id'.snd : PolyT (fun p : List Bool × List ℕ => p.2))
  exact PolyT.bits (PolyT.toNat (twinResult_polyT hB hD))

theorem precision_pad2 (w : List Bool) : precision (pad2 w) = precision w := by
  simp only [precision, pad2_value]

@[simp] theorem rawItems_pad (w : List Bool) : rawItems (pad2 w) = rawItems w := by
  simp only [rawItems, precision_pad2, pad2_value]

theorem items_pad (w : List Bool)
    (hl : ∀ q ∈ rawItems w, q.1.length ≤ (pad2 w).length) :
    items (pad2 w) = rawItems w := by
  unfold items
  rw [rawItems_pad]
  apply List.filter_eq_self.mpr
  intro q hq
  exact decide_eq_true (hl q hq)

theorem valid {c₀ : ℕ} (pk : CntPackage c₀)
    (hR : ∀ w, pk.R w = w.length) (hOk : ∀ w, pk.Ok w)
    (w : List Bool) (i : ℕ) (hi : i < (items w).length) :
    pk.Ok w ∧ (((items w).getD i ([], 0)).1).length ≤ pk.R w := by
  refine ⟨hOk w, ?_⟩
  rw [hR, List.getD_eq_getElem (items w) ([], 0) hi]
  have hm : (items w)[i] ∈ items w := List.getElem_mem hi
  have hh := (List.mem_filter.mp hm).2
  exact of_decide_eq_true hh

theorem bounds {c₀ : ℕ} (pk : CntPackage c₀)
    (hR : ∀ w, pk.R w = w.length) (hOk : ∀ w, pk.Ok w) :
    ∃ a, NatBatchQuery.Bounds pk spec a :=
  BatchCollect.bounds pk items_polyT finish_polyT (valid pk hR hOk)

/-- `N + 2 ≤ 2^b` for Ni's precision `b = bitlength(N) + 1`. -/
theorem value_add_two_bound (w : List Bool) : ofWord w + 2 ≤ 2 ^ precision w := by
  have h : ofWord w < 2 ^ (Nat.bits (ofWord w)).length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self (ofWord w)
  have h1 : 1 ≤ 2 ^ (Nat.bits (ofWord w)).length := Nat.one_le_two_pow
  unfold precision
  rw [pow_succ]
  omega

theorem one_le_precision (w : List Bool) : 1 ≤ precision w := by
  unfold precision; omega

theorem answer_pad {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool)
    (hlen : ∀ q ∈ rawItems w, q.1.length ≤ (pad2 w).length)
    (hsum : ((rawItems w).map fun q => q.2 * (pk.Q (pad2 w) q.1 : ℤ)).sum =
      (twinQueryNumerator (precision w) (ofWord w) (generate (precision w))).re) :
    NatBatchQuery.answer pk spec (pad2 w) = Nat.bits (twinCount (ofWord w)) := by
  rw [show spec = BatchCollect.spec items finish from rfl, BatchCollect.answer_eq]
  rw [finish]
  dsimp only
  rw [CountQueryFinish.dot_map_count, items_pad w hlen, precision_pad2, hsum,
    twinResult_queries (value_add_two_bound w) (one_le_precision w) (generate_certified _),
    Int.toNat_natCast]

theorem TM_of_package {c₀ : ℕ} (pk : CntPackage c₀)
    (hR : ∀ w, pk.R w = w.length) (hOk : ∀ w, pk.Ok w)
    (hlen : ∀ w q, q ∈ rawItems w → q.1.length ≤ (pad2 w).length)
    (hsum : ∀ w, ((rawItems w).map fun q => q.2 * (pk.Q (pad2 w) q.1 : ℤ)).sum =
      (twinQueryNumerator (precision w) (ofWord w) (generate (precision w))).re) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ w : List Bool, GraphProblems.Outputs M w (Nat.bits (twinCount (ofWord w)))
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨a, hb⟩ := bounds pk hR hOk
  have hf : PolyT spec.finish := by
    dsimp only [spec, BatchCollect.spec]
    exact finish_polyT
  obtain ⟨M, C, hfinite, hrun⟩ := NatBatchQuery.machine_TM_linear_input pk spec
    (BatchCollect.rounds_polyT (finish := finish) items_polyT)
    (BatchCollect.initial_polyT (items := items) (finish := finish))
    (BatchCollect.query_polyT (finish := finish) items_polyT)
    (BatchCollect.update_polyT (items := items) (finish := finish)) hf hb
    pad2 pad2_polyT (L := 4097)
    (fun w => (pad2_length_bounds w).1)
    (fun w => (pad2_length_bounds w).2)
  refine ⟨M, C, hfinite, fun w => ?_⟩
  have h := hrun w
  rw [answer_pad pk w (hlen w) (hsum w)] at h
  exact h

/-- One finite-alphabet Turing machine computes the exact twin-prime count for every
binary input, within the stated running time. -/
theorem twinCount_TM :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ w : List Bool, GraphProblems.Outputs M w (Nat.bits (twinCount (ofWord w)))
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨pk, hR, hOk, hsem⟩ := twin_items_package_exists
  have h (w : List Bool) := hsem (precision w) (ofWord w) w (generate_certified _)
    (value_add_two_bound w) rfl (precision_le w)
  apply TM_of_package pk hR hOk
  · intro w q hq
    have h1 := (h w).1 q hq
    rwa [hR] at h1
  · intro w
    exact (h w).2

/-- Natural-number form, with the actual binary length of `N`. -/
theorem twinCount_TM_all_inputs :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, GraphProblems.Outputs M (Nat.bits N) (Nat.bits (twinCount N))
        ⌊(C:ℝ)*2^((C:ℝ)*(Nat.bits N).length/
          Real.sqrt (Real.logb 2 ((Nat.bits N).length+2)))⌋₊ := by
  obtain ⟨M, C, hfinite, hrun⟩ := twinCount_TM
  refine ⟨M, C, hfinite, fun N => ?_⟩
  have h := hrun (Nat.bits N)
  have hv : ofWord (Nat.bits N) = N := by rw [bits_eq_encodeNat, gofWord_encodeNat]
  rwa [hv] at h

end TwinAlgorithm.TwinMachine
