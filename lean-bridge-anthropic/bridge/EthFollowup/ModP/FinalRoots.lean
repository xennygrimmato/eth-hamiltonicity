/-
# Deterministic root finding modulo any `m` for fixed degree (roots-plan.md §2, H7)

For each fixed degree `d ≥ 1`: ONE Mathlib `TM2ComputableAux` machine with finite alphabets and ONE
constant `C` such that on the input `encodeList (m :: a)` (the modulus `m` and the coefficients
`a = [a_0, …, a_d]` of `f = Σ a_i x^i`, in equal-length little-endian blocks) it halts within
`⌊C · 2^{C |w| / √(log₂(|w|+2))}⌋` steps (`|w|` the input length) with

* **`polyRoot_TM_rate`**: the least root `minRootP m a` of `f` modulo `m` in `[0, m)` (`m` if there is none);
* **`nextRoot_TM_rate`**: on `encodeList (m :: lo :: a)`, the least root `≥ lo` (`nextRootP m a lo`);
* **`rootCount_TM_rate`**: the number of roots `#(rootSetP m a)` in `[0, m)`;
* `polyRoot_TM_total`: the least-root machine halts within the same bound on EVERY input word.

When all coefficients are `< m`, `|w| = (d+2)·|encodeNat m|` (`EncodeList.blockLen_cons_of_le`), so the
bound is `m^{o(1)}` for fixed `d`; `C` depends on `d` and is not tracked.

Baselines (deterministic, unconditional): Berlekamp, Math. Comp. 24 (1970) 713–735 (reduction of
factoring over F_q to root finding over F_p); Shoup, Inform. Process. Lett. 33 (1990) 261–267
(time n^{2+o(1)} p^{1/2}); Bourgain–Konyagin–Shparlinski, Math. Comp. 84 (2015), arXiv 1308.4803
(n p^{1/2+o(1)}; one root in (n + p^{1/2}) p^{o(1)}). Under GRH, Rónyai, J. Algorithms 9 (1988)
391–400 is polynomial time for fixed degree. The root count is classically deterministic polynomial
time (`deg gcd(f, x^p − x)`); it is included as a by-product, not as an improvement.

Standard axioms only.
-/
import EthFollowup.ModP.HornerPkg
import EthFollowup.ModP.Final

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring

/-- **Least root, with totality**: the least-root machine of degree `d` outputs `minRootP m a` on
`encodeList (m :: a)` and halts within the bound on every word. -/
theorem polyRoot_TM_total (d : ℕ) (hd : 1 ≤ d) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ (m : ℕ) (a : List ℕ), a.length = d + 1 →
        GraphProblems.Outputs M (encodeList (m :: a)) (Computability.encodeNat (minRootP m a))
          ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodeList (m :: a)).length /
            Real.sqrt (Real.logb 2 ((encodeList (m :: a)).length + 2)))⌋₊) ∧
      ∀ w : List Bool, ∃ y, GraphProblems.Outputs M w y
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ :=
  polyRoot_TM_of d hd tabAF_polyT (arithRoot d hd).prep_polyT

/-- **The least root modulo any `m` of a polynomial of degree `≤ d`** (`m` if there is none), in
`2^{O_d(n/√log n)}`. -/
theorem polyRoot_TM_rate (d : ℕ) (hd : 1 ≤ d) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (m : ℕ) (a : List ℕ), a.length = d + 1 →
        GraphProblems.Outputs M (encodeList (m :: a)) (Computability.encodeNat (minRootP m a))
          ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodeList (m :: a)).length /
            Real.sqrt (Real.logb 2 ((encodeList (m :: a)).length + 2)))⌋₊ := by
  obtain ⟨M, C, hfin, h, -⟩ := polyRoot_TM_total d hd
  exact ⟨M, C, hfin, h⟩

/-- **The least root `≥ lo` modulo any `m`** (`m` if there is none), on `encodeList (m :: lo :: a)`. -/
theorem nextRoot_TM_rate (d : ℕ) (hd : 1 ≤ d) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (m lo : ℕ) (a : List ℕ), a.length = d + 1 →
        GraphProblems.Outputs M (encodeList (m :: lo :: a)) (Computability.encodeNat (nextRootP m a lo))
          ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodeList (m :: lo :: a)).length /
            Real.sqrt (Real.logb 2 ((encodeList (m :: lo :: a)).length + 2)))⌋₊ := by
  obtain ⟨M, C, hfin, h, -⟩ := nextRoot_TM_of d hd tabAF_polyT (arithNext d hd).prep_polyT
  exact ⟨M, C, hfin, h⟩

/-- **The number of roots in `[0, m)`** of a polynomial of degree `≤ d` modulo `m`. -/
theorem rootCount_TM_rate (d : ℕ) (hd : 1 ≤ d) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (m : ℕ) (a : List ℕ), a.length = d + 1 →
        GraphProblems.Outputs M (encodeList (m :: a)) (Computability.encodeNat (rootSetP m a).card)
          ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodeList (m :: a)).length /
            Real.sqrt (Real.logb 2 ((encodeList (m :: a)).length + 2)))⌋₊ := by
  obtain ⟨M, C, hfin, h, -⟩ := rootCount_TM_of d hd tabAF_polyT (arithCnt d hd).prep_polyT
  exact ⟨M, C, hfin, h⟩

end EthFollowup.ModP
