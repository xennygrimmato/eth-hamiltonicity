/-
Verbatim copy of the definitions and the statement of
`lean/ComparatorChallenges/SubexponentialSAT.lean` from openai/math at commit
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (Apache-2.0, Copyright OpenAI).

The only change: the final `theorem exact_count_and_sat ... := by sorry` is turned into a
`def ExactCountAndSatStatement (k : ℕ) (hk : 2 ≤ k) : Prop` with the identical body, so that
downstream files can take the upstream theorem as an explicit hypothesis instead of an axiom.
The upstream proof is `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` in
`lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean`.
-/
import Mathlib

namespace OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

def bitVal (b : Bool) : ℕ := if b then 1 else 0

def toNat : List Bool → ℕ
  | [] => 0
  | b :: bs => bitVal b + 2 * toNat bs

end OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms.SubexponentialSAT.SAT

universe u

abbrev Assignment (V : Type u) := V → Bool

structure Literal (V : Type u) where
  «variable» : V
  positive : Bool
  deriving DecidableEq

abbrev Clause (V : Type u) := Finset (Literal V)
abbrev CNF (V : Type u) := Finset (Clause V)

variable {V : Type u} [DecidableEq V]

def Literal.eval (a : Assignment V) (l : Literal V) : Bool :=
  a l.variable == l.positive

def Clause.eval (a : Assignment V) (C : Clause V) : Bool :=
  decide (∃ l ∈ C, l.eval a = true)

def CNF.eval (a : Assignment V) (F : CNF V) : Bool :=
  decide (∀ C ∈ F, C.eval a = true)

def WidthAtMost (k : ℕ) (F : CNF V) : Prop := ∀ C ∈ F, C.card ≤ k

section Finite

variable [Fintype V]

def satisfyingAssignments (F : CNF V) : Finset (Assignment V) :=
  Finset.univ.filter fun a => F.eval a = true

def count (F : CNF V) : ℕ := (satisfyingAssignments F).card

end Finite

end OAI.Algorithms.SubexponentialSAT.SAT

namespace OAI.Algorithms.SubexponentialSAT.Encoding

def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

def frame (bits : List Bool) : List Bool :=
  bits.foldr (fun b rest => true :: b :: rest) [false]

def encodeList {α : Type*} (enc : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: as => true :: (frame (enc a) ++ encodeList enc as)

def literalCode {n : ℕ} (l : SAT.Literal (Fin n)) : ℕ :=
  2 * l.variable.val + if l.positive then 1 else 0

def clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) : List ℕ :=
  (C.image literalCode).sort (· ≤ ·)

def cnfNumbers {n : ℕ} (F : SAT.CNF (Fin n)) : List (List ℕ) :=
  (F.image clauseNumbers).sort (· ≤ ·)

def encodeCNFBody {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeList (encodeList encodeNat) (cnfNumbers F)

def encodeCNF {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeNat n ++ encodeCNFBody F

def formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) : ℕ := (encodeCNF F).length

end OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms.SubexponentialSAT.Computation

universe u

inductive Trace {α : Type u} (step : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace step 0 a a
  | cons {n : ℕ} {a b c : α} :
      step a = some b → Trace step n b c → Trace step (n + 1) a c

structure PrimitiveMachine where
  tapeCount : ℕ
  stateCount : ℕ
  inputTape : Fin tapeCount
  start : Fin stateCount
  scan : Fin stateCount → Fin tapeCount
  transition : Fin stateCount → Option Bool →
    Bool ⊕ (Fin stateCount × Turing.TM0.Stmt (Option Bool))

namespace PrimitiveMachine

structure Cfg (machine : PrimitiveMachine) where
  state : Bool ⊕ Fin machine.stateCount
  tapes : Fin machine.tapeCount → Turing.Tape (Option Bool)

def step (machine : PrimitiveMachine) (c : machine.Cfg) : Option machine.Cfg :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    let tapeIndex := machine.scan q
    match machine.transition q (c.tapes tapeIndex).head with
    | .inl answer => some ⟨.inl answer, c.tapes⟩
    | .inr (q', action) =>
      let nextTape :=
        match action with
        | .move direction => (c.tapes tapeIndex).move direction
        | .write symbol => (c.tapes tapeIndex).write symbol
      some ⟨.inr q', Function.update c.tapes tapeIndex nextTape⟩

def init (machine : PrimitiveMachine) (input : List Bool) : machine.Cfg :=
  ⟨.inr machine.start, fun k =>
    if k = machine.inputTape then Turing.Tape.mk₁ (input.map some)
    else Turing.Tape.mk₁ []⟩

end PrimitiveMachine

end OAI.Algorithms.SubexponentialSAT.Computation

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement

noncomputable def runtimeScale (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
    Real.sqrt (Real.log ((n : ℝ) + 16))

noncomputable def runtimeBound (constant exponentConstant : ℝ)
    (degree inputBits numVars : ℕ) : ℝ :=
  constant * ((inputBits : ℝ) + 1) ^ degree *
    (2 : ℝ) ^ (exponentConstant * runtimeScale numVars)

end OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation

def countWord (a : ℕ) : List Bool := if a = 0 then [false] else a.bits

structure LocatedCfg (machine : PrimitiveMachine) where
  config : machine.Cfg
  position : Fin machine.tapeCount → ℤ
  lower : Fin machine.tapeCount → ℤ
  upper : Fin machine.tapeCount → ℤ

def locatedInit (machine : PrimitiveMachine) (input : List Bool) : LocatedCfg machine where
  config := machine.init input
  position _ := 0
  lower _ := 0
  upper i := if i = machine.inputTape then Int.ofNat (input.length - 1) else 0

def headDisplacement : Turing.TM0.Stmt (Option Bool) → ℤ
  | .move .left => -1
  | .move .right => 1
  | .write _ => 0

def LocatedCfg.monitor {machine : PrimitiveMachine} (c : LocatedCfg machine)
    (config : machine.Cfg) : LocatedCfg machine :=
  Sum.elim
    (fun _ => { c with config })
    (fun q =>
      Sum.elim
        (fun _ => { c with config })
        (fun targetAction =>
          let action := targetAction.2
          let i := machine.scan q
          let position := c.position i + headDisplacement action
          { config
            position := Function.update c.position i position
            lower := Function.update c.lower i (min (c.lower i) position)
            upper := Function.update c.upper i (max (c.upper i) position) })
        (machine.transition q (c.config.tapes (machine.scan q)).head))
    c.config.state

def locatedStep (machine : PrimitiveMachine) (c : LocatedCfg machine) :
    Option (LocatedCfg machine) :=
  (machine.step c.config).map c.monitor

def visitedSpace {machine : PrimitiveMachine} (c : LocatedCfg machine) : ℕ :=
  ∑ i, (c.upper i - c.lower i + 1).toNat

/-- The comparator statement `exact_count_and_sat` of openai/math, as a proposition.
Body identical to the upstream theorem statement. -/
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
