/-
# The final statements: Rudich–Rousseau's `Factoring` statement file, and its proof (module F6b)

`scratchpad/plans/factoring-plan.md`, row F6b and "Final statements".

## Part 1: Rudich–Rousseau's statement definitions, verbatim

Source: GitHub repository `IsaacRudich/SubexponentialDeterministicFactoring`, file `Challenge.lean`,
commit `5f5ff8f3823fa8fef8ee02a6f29049db3c76a0ce` (the commit registered as Palomar entry
PALOMAR-2026-10-28-000015-v1, archived as `PalomarArchive/IsaacRudich--SubexponentialDeterministicFactoring--6c87e6c7dafc`,
tag `palomar/PALOMAR-2026-10-28-000015-v1/5f5ff8f3…`), sha256 of the file
`c3adce9c7a04732442b615e69b3d33960ebc61dcacc5d281797c303d266ae12b`.
Authors: Isaac Rudich, Louis-Martin Rousseau. Licence: Apache-2.0.
Copied with the following MINIMAL SYNTACTIC adaptations (meaning unchanged):
* their file is a Lean `module` (Lean v4.35.0) with `public import …` and `@[expose] public section`; this
  file is an ordinary (non-module) file because it imports non-module bridge files, so the header is
  `import …` and the `@[expose] public section` line is dropped (in a non-module file everything is public
  and every definition body is visible, which is what `@[expose] public` asks for);
* their `namespace Factoring` is wrapped in `namespace RR`, so their names are `RR.Factoring.factor`, … ;
* their `theorem subexponentialRate …` (whose proof in `Challenge.lean` is a placeholder) is NOT copied as
  a declaration: its statement is copied verbatim in the comment below and proved as `RR.Factoring.subexponentialRate_of_pkg`
  (from the multiplication package hypothesis; see Part 2).
Their imports are `Mathlib.Computability.TuringMachine.Computable`, `Mathlib.Data.Nat.Prime.Defs`,
`Mathlib.Data.Nat.Log`; all three exist under these names in the Mathlib of this workspace (0df444a), where
`Turing.TM2ComputableInTime` already takes encodings as functions `α → List αΓ` (as in their Mathlib 56a0058).

## Part 2: proofs (`namespace EthFollowup.Factoring`)

* `minFac_TM_rate_of_pkg` (= F5a's `minFac_TM_of_pkg`): one `TM2ComputableAux` machine, finite alphabets,
  `Outputs M (encodeNat N) (encodeNat (minFac N)) ⌊C·2^{C n/√log₂(n+2)}⌋₊`;
* the adaptor `toFactoringMachine` / `factorsWithin_of_outputs` (GraphProblems.Outputs → RR's
  `FactoringMachine` / `FactorsWithin`) and its converse `outputs_of_factoringMachine`;
* `sqrtLogLog_of_pkg : RR.Factoring.SqrtLogLogConjecture` (constant 2C:
  `Nat.sqrt (Nat.log 2 n) + 1 ≤ 2√log₂(n+2)` and the floor of `2Cn/(s+1)` costs a factor 2);
* `subexponentialRate_of_pkg`: RR's headline statement `subexponentialRate`.
All take `hpkg : ∃ c₀, Nonempty (MulPackage c₀)` (F4's export, not yet available).

Standard axioms only.
-/
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Log
import EthFollowup.Factoring.Rate

set_option linter.unusedSectionVars false

namespace RR

/- ======================= BEGIN verbatim copy (Challenge.lean @ 5f5ff8f) ======================= -/

namespace Factoring

open Turing Computability

/-! ### The problem -/

/-- Factoring: the smallest prime factor of `N` (Mathlib's `Nat.minFac`; it is `1` for `N = 1`).
Applied repeatedly, it gives the whole factorization. -/
def factor : ℕ → ℕ := Nat.minFac

/-! ### Machines and time -/

/-- A Mathlib machine that computes `factor`, with numbers written in binary on input and output,
together with its running time as a function of the input length. -/
abbrev FactoringMachine := TM2ComputableInTime encodeNat encodeNat factor

/-- Every stack alphabet of the machine is finite, as for a textbook machine. -/
def FactoringMachine.FiniteAlphabets (M : FactoringMachine) : Prop :=
  ∀ k, Finite (M.tm.Γ k)

/-- Machine `M` factors every `N` within `T n` steps, where `n` is the number of bits of `N`. -/
def FactorsWithin (M : FactoringMachine) (T : ℕ → ℕ) : Prop :=
  M.FiniteAlphabets ∧ ∀ n, M.time n ≤ T n

/-- Some machine factors every `N` within `T n` steps. -/
def FactoringInTime (T : ℕ → ℕ) : Prop :=
  ∃ M : FactoringMachine, FactorsWithin M T

/-! ### The result -/

/- (their declaration, statement verbatim; proved below as `subexponentialRate_of_pkg`)
/-- **The result.** One machine factors in time `N ^ o(1)`: for every `k`, the same machine
factors within `C · 2 ^ (n / k)` steps, about `N ^ (1/k)`. -/
theorem subexponentialRate :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ,
      FactorsWithin M (fun n => C * 2 ^ (n / k)) := by
  <placeholder proof in Challenge.lean; omitted here>
-/

/-! ### The conjecture -/

/-- **The conjecture (not proved).** A faster rate, conjectured by the AI when asked to
conjecture: one machine factors in time `exp(O(log N / √(log log N)))`.  In the bit length `n`
(`n ≈ log₂ N`, so `log log N ≈ log n`) this is `2 ^ O(n / √(log n))`, written here as
`C · 2 ^ (C · n / (⌊√⌊log₂ n⌋⌋ + 1))`: the `C` in the exponent is the constant of the `O(·)`, the
`C` in front covers small inputs, and the `+ 1` only avoids dividing by zero when `n ≤ 3`.
Stated as a proposition, not as a theorem: nothing here claims it is true. -/
def SqrtLogLogConjecture : Prop :=
  ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (C * n / (Nat.sqrt (Nat.log 2 n) + 1)))

end Factoring

/- ======================== END verbatim copy ======================== -/

end RR

namespace EthFollowup.Factoring

open Computability

/-! ## (a) Our form of the rate -/

/-- The time bound of `minFac_TM_of_pkg`, as a function of the input length `n`. -/
noncomputable def rateT (C : ℕ) (n : ℕ) : ℕ :=
  ⌊(C : ℝ) * 2 ^ ((C : ℝ) * n / Real.sqrt (Real.logb 2 (n + 2)))⌋₊

theorem minFac_TM_rate_of_pkg (hpkg : ∃ c₀ : ℕ, Nonempty (MulPackage c₀)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, GraphProblems.Outputs M (Computability.encodeNat N) (Computability.encodeNat (Nat.minFac N))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat N).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat N).length + 2)))⌋₊ :=
  minFac_TM_of_pkg hpkg

/-! ## (b) Adaptor: `GraphProblems.Outputs` ↔ RR's `FactoringMachine` -/

/-- A `TM2ComputableAux` machine that outputs `encodeNat (minFac N)` on `encodeNat N` within
`T (encodeNat N).length` steps, as one of RR's `FactoringMachine`s with time function `T`. -/
noncomputable def toFactoringMachine (M : Turing.TM2ComputableAux Bool Bool) (T : ℕ → ℕ)
    (h : ∀ N : ℕ, GraphProblems.Outputs M (encodeNat N) (encodeNat (Nat.minFac N)) (T (encodeNat N).length)) :
    RR.Factoring.FactoringMachine where
  toTM2ComputableAux := M
  time := T
  outputsFun N := Classical.choice (h N)

@[simp] theorem toFactoringMachine_time (M : Turing.TM2ComputableAux Bool Bool) (T : ℕ → ℕ) (h) :
    (toFactoringMachine M T h).time = T := rfl

@[simp] theorem toFactoringMachine_aux (M : Turing.TM2ComputableAux Bool Bool) (T : ℕ → ℕ) (h) :
    (toFactoringMachine M T h).toTM2ComputableAux = M := rfl

/-- Converse direction: every `FactoringMachine` gives `Outputs` within its time function. -/
theorem outputs_of_factoringMachine (M : RR.Factoring.FactoringMachine) (N : ℕ) :
    GraphProblems.Outputs M.toTM2ComputableAux (encodeNat N) (encodeNat (Nat.minFac N))
      (M.time (encodeNat N).length) :=
  ⟨M.outputsFun N⟩

/-- The adaptor at the level of `FactorsWithin`: finite alphabets and `T ≤ T'` pointwise. -/
theorem factorsWithin_of_outputs (M : Turing.TM2ComputableAux Bool Bool) (T T' : ℕ → ℕ)
    (hfin : ∀ i, Finite (M.tm.Γ i))
    (h : ∀ N : ℕ, GraphProblems.Outputs M (encodeNat N) (encodeNat (Nat.minFac N)) (T (encodeNat N).length))
    (hT : ∀ n, T n ≤ T' n) :
    RR.Factoring.FactorsWithin (toFactoringMachine M T h) T' :=
  ⟨hfin, hT⟩

/-- The machine of (a) as one of RR's `FactoringMachine`s, with time function `rateT C`. -/
theorem exists_factoringMachine_rate (hpkg : ∃ c₀ : ℕ, Nonempty (MulPackage c₀)) :
    ∃ (M : RR.Factoring.FactoringMachine) (C : ℕ), RR.Factoring.FactorsWithin M (rateT C) := by
  obtain ⟨M, C, hfin, h⟩ := minFac_TM_rate_of_pkg hpkg
  exact ⟨toFactoringMachine M (rateT C) h, C, factorsWithin_of_outputs M _ _ hfin h fun _ => le_rfl⟩

/-! ## Real-analysis inequalities -/

/-- `⌊C·2^x⌋₊ ≤ C·2^{D+1}·2^q` when `x ≤ q + 1 + D`. -/
theorem floor_rpow_le (C q D : ℕ) (x : ℝ) (hx : x ≤ (q : ℝ) + 1 + D) :
    ⌊(C : ℝ) * 2 ^ x⌋₊ ≤ C * 2 ^ (D + 1) * 2 ^ q := by
  apply Nat.floor_le_of_le
  have h1 : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ ((q + (D + 1) : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
  rw [Real.rpow_natCast] at h1
  have h2 : (C : ℝ) * 2 ^ x ≤ C * 2 ^ (q + (D + 1)) :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  calc (C : ℝ) * 2 ^ x ≤ C * 2 ^ (q + (D + 1)) := h2
    _ = ((C * 2 ^ (D + 1) * 2 ^ q : ℕ) : ℝ) := by push_cast; ring

/-- `a / b < ⌊a / b⌋ + 1` for natural division. -/
theorem div_lt_natDiv_add_one (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hb']
  have : (a : ℝ) < ((a / b * b + b : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this; linarith

theorem one_le_logb_add_two (n : ℕ) : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num

theorem one_le_sqrt_logb (n : ℕ) : (1 : ℝ) ≤ Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) := by
  rw [Real.le_sqrt (by norm_num) (by linarith [one_le_logb_add_two n])]
  simpa using one_le_logb_add_two n

/-- `Nat.sqrt (Nat.log 2 n) + 1 ≤ 2·√log₂(n+2)`. -/
theorem natSqrt_log_add_one_le (n : ℕ) :
    ((Nat.sqrt (Nat.log 2 n) + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) := by
  have h1 : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
    have := Real.natLog_le_logb (n + 2) 2
    have hm : Nat.log 2 n ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
    push_cast at this
    exact le_trans (by exact_mod_cast hm) this
  have h2 : ((Nat.sqrt (Nat.log 2 n) : ℕ) : ℝ) ≤ Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) :=
    le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt h1)
  have h3 := one_le_sqrt_logb n
  push_cast
  linarith

/-- The exponent for `SqrtLogLogConjecture`: `C n/√log₂(n+2) ≤ ⌊2Cn/(s+1)⌋ + 1`, `s = ⌊√⌊log₂ n⌋⌋`. -/
theorem exp_le_sqrtLogLog (C n : ℕ) :
    (C : ℝ) * n / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) ≤
      (((2 * C * n) / (Nat.sqrt (Nat.log 2 n) + 1) : ℕ) : ℝ) + 1 + (0 : ℕ) := by
  set s := Nat.sqrt (Nat.log 2 n)
  set r := Real.sqrt (Real.logb 2 ((n : ℝ) + 2))
  have hr : 0 < r := lt_of_lt_of_le one_pos (one_le_sqrt_logb n)
  have hs : ((s + 1 : ℕ) : ℝ) ≤ 2 * r := natSqrt_log_add_one_le n
  have hs0 : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
  have h1 : (C : ℝ) * n / r ≤ ((2 * C * n : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hr hs0]
    push_cast at hs ⊢
    have : (0 : ℝ) ≤ (C : ℝ) * n := by positivity
    nlinarith
  have h2 := div_lt_natDiv_add_one (2 * C * n) (s + 1) (Nat.succ_pos _)
  push_cast at h1 h2 ⊢
  linarith

/-- The exponent for `subexponentialRate`: `C n/√log₂(n+2) ≤ ⌊n/k⌋ + 1 + C·2^{C²k²}`. -/
theorem exp_le_subexp (C k n : ℕ) (hk : 1 ≤ k) :
    (C : ℝ) * n / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) ≤
      ((n / k : ℕ) : ℝ) + 1 + ((C * 2 ^ (C ^ 2 * k ^ 2) : ℕ) : ℝ) := by
  set r := Real.sqrt (Real.logb 2 ((n : ℝ) + 2))
  have hr1 : 1 ≤ r := one_le_sqrt_logb n
  have hr : 0 < r := lt_of_lt_of_le one_pos hr1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hq := div_lt_natDiv_add_one n k hk
  have hCn : (0 : ℝ) ≤ (C : ℝ) * n := by positivity
  have hD : (0 : ℝ) ≤ ((C * 2 ^ (C ^ 2 * k ^ 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hbig : 2 ^ (C ^ 2 * k ^ 2) ≤ n + 2
  · -- `√log₂(n+2) ≥ C k`, so the exponent is at most `n / k`
    have hL : ((C ^ 2 * k ^ 2 : ℕ) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
      exact_mod_cast hbig
    have hCk : (C : ℝ) * k ≤ r := by
      rw [Real.le_sqrt (by positivity) (by linarith [one_le_logb_add_two n])]
      push_cast at hL; nlinarith
    have h1 : (C : ℝ) * n / r ≤ (n : ℝ) / k := by
      rw [div_le_div_iff₀ hr hk0]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith
    linarith
  · -- small `n`: the exponent is at most `C n ≤ C 2^{C²k²}`
    replace hbig := Nat.lt_of_not_le hbig
    have h1 : (C : ℝ) * n / r ≤ C * n := div_le_self hCn hr1
    have h2 : (C : ℝ) * n ≤ ((C * 2 ^ (C ^ 2 * k ^ 2) : ℕ) : ℝ) := by
      have : n ≤ 2 ^ (C ^ 2 * k ^ 2) := by omega
      have : C * n ≤ C * 2 ^ (C ^ 2 * k ^ 2) := Nat.mul_le_mul_left _ this
      exact_mod_cast this
    have : (0 : ℝ) ≤ ((n / k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

theorem rateT_le_sqrtLogLog (C n : ℕ) :
    rateT C n ≤ 2 * C * 2 ^ (2 * C * n / (Nat.sqrt (Nat.log 2 n) + 1)) := by
  have := floor_rpow_le C _ 0 _ (exp_le_sqrtLogLog C n)
  simp only [zero_add, pow_one] at this
  unfold rateT
  calc _ ≤ C * 2 * 2 ^ (2 * C * n / (Nat.sqrt (Nat.log 2 n) + 1)) := this
    _ = _ := by ring

theorem rateT_le_subexp (C k n : ℕ) (hk : 1 ≤ k) :
    rateT C n ≤ C * 2 ^ (C * 2 ^ (C ^ 2 * k ^ 2) + 1) * 2 ^ (n / k) :=
  floor_rpow_le C _ _ _ (exp_le_subexp C k n hk)

/-! ## (c) The conjecture, and (d) the headline result -/

theorem sqrtLogLog_of_pkg (hpkg : ∃ c₀ : ℕ, Nonempty (MulPackage c₀)) :
    RR.Factoring.SqrtLogLogConjecture := by
  obtain ⟨M, C, hfin, h⟩ := minFac_TM_rate_of_pkg hpkg
  exact ⟨2 * C, toFactoringMachine M (rateT C) h,
    factorsWithin_of_outputs M _ _ hfin h fun n => rateT_le_sqrtLogLog C n⟩

theorem subexponentialRate_of_pkg (hpkg : ∃ c₀ : ℕ, Nonempty (MulPackage c₀)) :
    ∃ M : RR.Factoring.FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ,
      RR.Factoring.FactorsWithin M (fun n => C * 2 ^ (n / k)) := by
  obtain ⟨M, C, hfin, h⟩ := minFac_TM_rate_of_pkg hpkg
  exact ⟨toFactoringMachine M (rateT C) h, fun k hk => ⟨C * 2 ^ (C * 2 ^ (C ^ 2 * k ^ 2) + 1),
    factorsWithin_of_outputs M _ _ hfin h fun n => rateT_le_subexp C k n hk⟩⟩

end EthFollowup.Factoring
