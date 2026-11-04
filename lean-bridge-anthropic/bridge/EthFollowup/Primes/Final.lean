/-
# Primes: the parity of π on any interval in `2^{O(n/√log n)}`

`scratchpad/plans/primes-plan.md`. For each problem: ONE Mathlib `TM2ComputableAux` machine with
finite alphabets and ONE constant `C`, halting within `⌊C · 2^{C n/√(log₂(n+2))}⌋` steps (`n` the
input length) with the answer:

* **`piParity_TM_rate`**: `π(x) mod 2` on `encodeNat x`;
* **`piIntervalParity_TM_rate`**: `#{p prime : A ≤ p ≤ B} mod 2` on `encodePair A B`.

Proof: the leveled counting network (`ArithL*`) of the description `primeDesc` (`PrimeDesc.lean`),
whose count is `Σ_{m ∈ [A,B]} τ^<(m)·C_L(m) ≡ #primes in [A, B] (mod 2)` (`ChainParity.primeParity`;
`π(x) = #primes in [1, x]`, `primeCounting_eq_card`), with one query (`SpecPrime.specPi`) through
`GR.queryM_TM` (`PrimePkgs.lean`).

Standard axioms only.
-/
import EthFollowup.Primes.PrimePkgs

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open EthFollowup.ModP

/-- **π(x) mod 2 in `2^{O(n/√log n)}`.** On `encodeNat x` the machine outputs
`encodeNat (π(x) mod 2)`. -/
theorem piParity_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (Nat.primeCounting x % 2))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ :=
  piParity_TM_of

/-- **The parity of the number of primes in any interval `[A, B]` in `2^{O(n/√log n)}`**, on
`encodePair A B`. -/
theorem piIntervalParity_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ A B : ℕ, GraphProblems.Outputs M (encodePair A B)
        (Computability.encodeNat (((Finset.Icc A B).filter Nat.Prime).card % 2))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodePair A B).length /
          Real.sqrt (Real.logb 2 ((encodePair A B).length + 2)))⌋₊ :=
  piIntervalParity_TM_of

end EthFollowup.Primes
