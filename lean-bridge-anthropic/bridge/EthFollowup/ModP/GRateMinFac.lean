/-
# The sanity check of `GRate`: `Nat.minFac` as a counted prefix search (module B4, part 3)

`scratchpad/plans/modp-plan.md` §5. `CntPackage.ofMul` (the multiplication-network package as a
counted-network package) with `minFacSpec` (the search of `Factoring/Rate.lean`: `FR.smallF`,
`FR.stepF`, `FR.outF`) gives `Nat.minFac` through `GR.searchM_TM`:

* `minFacSpec`, `minFacSpec_seq` (the rounds are `FR.csq`), `minFacSpec_answer`;
* `minFac_TM_rate_viaGR`: the statement of `Factoring.minFac_TM_rate`, re-derived through `GRate`.

Standard axioms only.
-/
import EthFollowup.ModP.GRate
import EthFollowup.Factoring.MulPackage

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork EthFollowup.Factoring

/-- `Nat.minFac` as a counted prefix search: `N < 2` directly, else the binary search of `Rate.lean`. -/
def minFacSpec : SearchSpec where
  pre w := decide (Groundwork.ofWord w < 2)
  small := FR.smallF
  step := FR.stepF
  fin := FR.outF

theorem minFacSpec_seq {c₀ : ℕ} (pk : MulPackage c₀) (w : List Bool) (y : ℕ) :
    GR.seq (CntPackage.ofMul pk) minFacSpec w y = FR.csq w y := by
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [GR.seq_succ, ih]
    exact (FR.stepF_eq w y (FR.csq w y)).trans (Search.searchWith_succ _ _).symm

theorem minFacSpec_answer {c₀ : ℕ} (pk : MulPackage c₀) (w : List Bool) :
    GR.answer (CntPackage.ofMul pk) minFacSpec w = Nat.bits (Nat.minFac (Groundwork.ofWord w)) := by
  unfold GR.answer
  by_cases h : Groundwork.ofWord w < 2
  · have hp : minFacSpec.pre w = true := by simp only [minFacSpec, decide_eq_true_eq]; exact h
    rw [if_pos hp]; exact FR.smallF_eq h
  · have hp : minFacSpec.pre w = false := by simp only [minFacSpec, decide_eq_false_iff_not]; exact h
    rw [if_neg (by simp [hp])]
    show FR.outF (w, GR.seq (CntPackage.ofMul pk) minFacSpec w w.length) = _
    rw [minFacSpec_seq]; unfold FR.outF; rw [FR.ofWord_reverse, FR.csq_minFac (by omega)]

/-- **`Factoring.minFac_TM_rate`, re-derived through the generic search** `GR.searchM_TM`. -/
theorem minFac_TM_rate_viaGR :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, GraphProblems.Outputs M (Computability.encodeNat N) (Computability.encodeNat (Nat.minFac N))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat N).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat N).length + 2)))⌋₊ := by
  obtain ⟨c₀, ⟨pk⟩⟩ := mulPackage_nonempty
  have hlen : ∀ q, (minFacSpec.step q).length = q.1.2.2.length + 1 := by
    intro q; show (FR.stepF q).length = _; unfold FR.stepF; split_ifs <;> simp
  have hfinlen : ∀ w π, π.length ≤ w.length → (minFacSpec.fin (w, π)).length ≤ 1 * (w.length + 2) := by
    intro w π hπ
    show (Nat.bits (Groundwork.ofWord π.reverse)).length ≤ _
    rw [Nat.size_eq_bits_len]
    have := Nat.size_le.2 (Groundwork.ofWord_lt π.reverse)
    rw [List.length_reverse] at this
    omega
  have hsmlen : ∀ w, (minFacSpec.small w).length ≤ 1 * (w.length + 2) := by
    intro w; show (FR.smallF w).length ≤ _; unfold FR.smallF; split_ifs <;> simp
  have hOk : ∀ w, minFacSpec.pre w = false → (CntPackage.ofMul pk).Ok w := by
    intro w h
    show 1 ≤ Groundwork.ofWord w
    simp only [minFacSpec, decide_eq_false_iff_not, not_lt] at h
    omega
  obtain ⟨M, C, hfin, h⟩ := GR.searchM_TM (CntPackage.ofMul pk) minFacSpec FR.small_polyT FR.smallF_polyT
    FR.stepF_polyT FR.outF_polyT hlen hfinlen hsmlen hOk
  refine ⟨M, C, hfin, fun N => ?_⟩
  have := h (Computability.encodeNat N)
  rwa [minFacSpec_answer, FR.ofWord_encodeNat, ← FR.encodeNat_eq_bits] at this

end EthFollowup.ModP
