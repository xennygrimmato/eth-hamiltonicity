# Exact twin-prime counting in time 2^{O(b/√log b)} (Lean 4, machine-checked)

**Headline theorem** (`src/TwinIndependent/Solution.lean`):

```lean
theorem TwinIndependent.twinPrimeCounting_time : TwinIndependent.ExactTwinPrimeCounting
```

The statement is in `src/TwinIndependent/MainResults.lean`, which imports Mathlib only:

```lean
def twinPrimeCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (p + 2)).card

def ExactTwinPrimeCounting : Prop :=
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ N : ℕ, Outputs M (Nat.bits N) (Nat.bits (twinPrimeCount N)) (timeBound C N)
```

`timeBound C N = ⌊C · 2^(C·b/√log₂(b+2))⌋₊` with `b = (Nat.bits N).length`. `Outputs` is
Mathlib's `TM2OutputsInTime`. Both are copied verbatim from J. Ni's
`PrimeIndependent.MainResults` (release v0.1-verified), so the machine model and the bound
have the same shape as his `primeCounting_time`. The convention is `p ≤ N`, and the partner
`p + 2` may be larger than `N`.

```
'TwinIndependent.twinPrimeCounting_time' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorry` and no `axiom` anywhere in `src/`. Nothing remains to prove, so this
package has no `Remaining.lean`.

## What was added to Ni's development (1,931 lines; none of Ni's files were changed)

| file | content |
| --- | --- |
| `EthFollowup/Primes/TwinKernelDesc.lean` | The doubled descriptor. It holds Ni's four-kernel `CountKernel.descriptor` on variables 0..71 and a shifted copy on 72..143, plus the link equation `x₇₂ = x₀ + 2`, giving 144 variables and 67 equations (268 slots). Also proved here: the satisfaction lemma `twin_sat`, well-formedness, `Spread 268`, and the communication bound `U ≤ 2^19·268·(n+2)` from `arithSys_U_le`. |
| `EthFollowup/Primes/TwinKernelCount.lean` | A fibre-product count bijection over the shared `n`: `twin_descriptor_count` / `twin_count_at`. The count equals `twinValue = Σ_{v₁,v₂ linked} ∏q(v₁)·∏q(v₂)`. Also the bit bounds and `twinNetwork_spec_at` (value plus U bound). |
| `EthFollowup/Primes/TwinKernelQuery.lean` | The 48-entry query encoding, a polynomial-time reader, the `ArithLSpec` (cS = 268), and `twin_package_exact_exists`: one `CntPackage (2^22·268)` answers every twin query exactly. |
| `TwinAlgorithm/TwinFormula.lean` | The identity π₂(N) = Σ_{2≤n≤N} 1_P(n)·1_P(n+2), with Ni's per-`n` phase expansion. The error bound uses Ni's own certified table: `N·3(N+2)²(12+10b)2^{-6b-6} < 1/2`. Integer reconstruction: `twinResult_eq`, with denominator `commonScale^8`. |
| `TwinAlgorithm/TwinQueryExpansion.lean`, `TwinQueryFinal.lean` | The twin numerator is a sum, over pairs of Ni's query indices, of a Gaussian coefficient times `twinValue` (`twinNumerator_eq_queries`). |
| `TwinAlgorithm/TwinEnumeration.lean` | The explicit polynomial-time list of `(query, weight)` items, and padding by a factor of 4096. |
| `TwinAlgorithm/TwinMachine.lean` | `NatBatchQuery.machine_TM_linear_input` applied with `L = 4097`. This gives `twinCount_TM_all_inputs`. |

The error budget is bounded per `n` (|P̃(n) − P(n)| ≤ n²·ε), not per pair of tuples. Ni's
precision `b = bitlength(N)+1` and his table therefore already work for every `N`, and the
larger `D = 5β′+…` from the notebook is not needed. There are (b+1)⁴·4·(2M)⁸·2⁸ queries, which
is polynomial in b.

## Build

The build reuses the prebuilt Mathlib@0df444a and upstream oleans in `/home/user/anth-build/.lake`
(lean4 v4.33.1) and only reads them.

1. Run `./setup.sh /path/to/prime-algorithm`. This copies Ni's unmodified `formal/bridge`,
   `formal/unified` and `formal/independent` sources into `ni/`. It also symlinks the upstream
   `EthFollowup` oleans into `build/`, because Lean resolves a package root from a single
   search-path entry.
2. Run `python3 build.py TwinIndependent.Solution PrimeIndependent.Solution`. From a warm cache
   this took about 1 minute for the twin files and about 15 minutes for Ni's files, most of it
   cold disk reads.
3. Run `LEAN_PATH=$(cat scripts/leanpath) lean scripts/PrintAxioms.lean`.

As a sanity check, `scripts/Sanity.lean` evaluates `twinPrimeCount` at 5, 100 and 1000 and gets
2, 8 and 35.
