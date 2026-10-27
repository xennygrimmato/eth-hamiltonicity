/-
Bridge version of `EthFollowup.Comparator`. Instead of copying the comparator's definitions, it
imports openai/math's own development and states `ExactCountAndSatStatement` with the same body
as the comparator challenge `lean/ComparatorChallenges/SubexponentialSAT.lean`, now over the
upstream definitions. `exactCountAndSat_holds` discharges it with the upstream theorem.
-/
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation

/-- The comparator statement `exact_count_and_sat`, as a proposition (upstream definitions). -/
def ExactCountAndSatStatement (k : ℕ) (_hk : 2 ≤ k) : Prop :=
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape answerTape : Fin machine.tapeCount)
      (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF F)) final ∧
          final.config.tapes countTape =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes answerTape =
            Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
          final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
          BinaryArithmetic.toNat (countWord (SAT.count F)) = SAT.count F ∧
          (countWord (SAT.count F)).length ≤ n + 1 ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF F)) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e

/-- The upstream Lean theorem proves the statement. -/
theorem exactCountAndSat_holds (k : ℕ) (hk : 2 ≤ k) : ExactCountAndSatStatement k hk :=
  exact_count_and_sat k hk

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
