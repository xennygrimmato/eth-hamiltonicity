/-
# The prime-parity packages (Executor P, step P2)

`scratchpad/plans/primes-plan.md`. Two leveled description readers (`ArithLSpec`) built from
`primeDesc` (`PrimeDesc.lean`, PolyT pieces in `PrimePoly.lean`), with `n = nf w = |w|`,
`L = primeL n = (Nat.bits n).length`, `b = b n`, `l0 = ℓ n`, one query (`R = 0`):
* `arithPi`: the interval `[1, ofWord w]` (`π(x)` on `encodeNat x`);
* `arithPiInt`: the interval `[rdM w, rdA w]` (on `encodePair A B`).
Spread `8`, `nL ≤ L + 1 ≤ ν n + 3`, well-formedness by `primeDescL_WF` (`kl n 0 = ℓ n`).
With `specPi` (`SpecPrime.lean`) and `GR.queryM_TM`: **`piParity_TM_of`**, **`piIntervalParity_TM_of`**.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLPackage
import EthFollowup.Primes.SpecPrime
import EthFollowup.Primes.PrimePoly
import EthFollowup.ModP.ArithPkgs

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring
  EthFollowup.ModP

/-! ## Common facts -/

theorem kl_zero (n : ℕ) : kl n 0 = ℓ n := by
  unfold kl kl1 sh ℓ ℓ1; rw [ℓ2_eq_ℓ1]; unfold ℓ1; simp

theorem primeDesc_WF (n A B : ℕ) : (primeDesc (b n) (ℓ n) n A B).WF n :=
  primeDescL_WF (kl n) (Factoring.one_le_b n) (kl_zero n) fun k => kl_pos n k

theorem primeDesc_nL (n A B : ℕ) : (primeDesc (b n) (ℓ n) n A B).nL ≤ ν n + 3 := by
  have h1 := nL_le (b := b n) (l0 := ℓ n) (L := primeL n) (A := A) (B := B)
  have h2 := primeL_le n
  unfold primeDesc; unfold ν; omega

theorem lt_bl {n B : ℕ} (h : B < 2 ^ n) : B < 2 ^ (b n * ℓ n) :=
  h.trans_le (Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact le_nB n))

theorem one_lt_bl (n : ℕ) : 1 < 2 ^ (b n * ℓ n) :=
  Nat.one_lt_two_pow (by have := lt_nB n; unfold nB at this; rw [mul_comm]; omega)

/-- **The count mod 2** of `primeDesc` at size `n`, for an interval `[A, B]` with `A ≤ 2^n`, `B < 2^n`. -/
theorem primeDesc_count_parity {n A B : ℕ} (hA : A ≤ 2 ^ n) (hB : B < 2 ^ n) :
    (primeDesc (b n) (ℓ n) n A B).count n % 2 = ((Icc A B).filter Nat.Prime).card % 2 := by
  refine primeDesc_count_mod_two (lbox n) ?_ (lt_bl hB) hB fun k y hy => lbox_spec n k hy
  have h1 : 2 ^ n < 2 ^ (b n * ℓ n) :=
    Nat.pow_lt_pow_right (by norm_num) (by have := lt_nB n; unfold nB at this; rw [mul_comm]; exact this)
  exact max_lt (lt_of_le_of_lt hA h1) (lt_of_le_of_lt Nat.one_le_two_pow h1)

theorem primeDesc_polyT {A B : List Bool × List Bool → ℕ} (hA : PolyT A) (hB : PolyT B) :
    PolyT fun y : List Bool × List Bool => primeDesc (b y.1.length) (ℓ y.1.length) y.1.length (A y) (B y) := by
  have hb := b_unary len_fst_unary
  have hl := ℓ_unary len_fst_unary
  have hL : Unary fun y : List Bool × List Bool => primeL y.1.length := primeL_unary len_fst_unary.poly
  exact (LDesc.mk_polyT (primeDescL_D_polyT hb hl hL hA hB) (primeDescL_lev_polyT hL)
    (primeDescL_levC_polyT hL)).congr fun _ => rfl

/-! ## π(x) mod 2 -/

/-- **π(x) mod 2**: the interval `[1, ofWord w]`, `n = |w|`. -/
def arithPi : ArithLSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R _ := 0
  R_le _ := Nat.zero_le _
  R_poly := PolyT.const 0
  desc y := primeDesc (b y.1.length) (ℓ y.1.length) y.1.length 1 (Groundwork.ofWord y.1)
  desc_poly := primeDesc_polyT (PolyT.const 1) gofWord_fst_polyT
  cS := 8
  one_le_cS := by norm_num
  spread _ := primeDescL_spread
  lev_le y := primeDesc_nL _ _ _
  wf w _ _ := primeDesc_WF _ _ _

theorem arithPi_parity (w : List Bool) :
    (arithPi.desc (w, [])).count (arithPi.nf w) % 2 =
      ((Icc 1 (Groundwork.ofWord w)).filter Nat.Prime).card % 2 :=
  primeDesc_count_parity Nat.one_le_two_pow (Groundwork.ofWord_lt w)

/-- **π(x) mod 2 in `2^{O(n/√log n)}`**, from the package of `arithPi` and the one-query
specification `specPi`. -/
theorem piParity_TM_of :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : ℕ, GraphProblems.Outputs M (Computability.encodeNat x)
        (Computability.encodeNat (Nat.primeCounting x % 2))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat x).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat x).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithPi.pkg_exists
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk specPi specPi_pre_polyT specPi_small_polyT specPi_q1_polyT
    specPi_q2_polyT specPi_fin_polyT (fun w => specPi_length pk w) (fun w _ => hOk w)
    (fun w _ => Nat.zero_le _) (fun w _ => Nat.zero_le _)
  refine ⟨M, C, hfin, fun x => ?_⟩
  have e : GR.answerQ pk specPi (Computability.encodeNat x) = Computability.encodeNat (Nat.primeCounting x % 2) := by
    refine specPi_answer_eq pk _ ?_
    rw [hQ, arithPi_parity, gofWord_encodeNat, primeCounting_eq_card]
  have := h (Computability.encodeNat x)
  rwa [e] at this

/-! ## The parity of the number of primes in `[A, B]` -/

/-- **π([A, B]) mod 2**: the interval `[rdM w, rdA w]`, `n = |w|`. -/
def arithPiInt : ArithLSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R _ := 0
  R_le _ := Nat.zero_le _
  R_poly := PolyT.const 0
  desc y := primeDesc (b y.1.length) (ℓ y.1.length) y.1.length (rdM y.1) (rdA y.1)
  desc_poly := primeDesc_polyT (rdM_polyT.comp (PolyT.fst PolyT.id')) (rdA_polyT.comp (PolyT.fst PolyT.id'))
  cS := 8
  one_le_cS := by norm_num
  spread _ := primeDescL_spread
  lev_le y := primeDesc_nL _ _ _
  wf w _ _ := primeDesc_WF _ _ _

theorem arithPiInt_parity (w : List Bool) :
    (arithPiInt.desc (w, [])).count (arithPiInt.nf w) % 2 =
      ((Icc (rdM w) (rdA w)).filter Nat.Prime).card % 2 := by
  refine primeDesc_count_parity ((rdM_lt w).le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)))
    ((rdA_lt w).trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)))

/-- **The parity of the number of primes in `[A, B]` in `2^{O(n/√log n)}`** (on `encodePair A B`). -/
theorem piIntervalParity_TM_of :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ A B : ℕ, GraphProblems.Outputs M (encodePair A B)
        (Computability.encodeNat (((Finset.Icc A B).filter Nat.Prime).card % 2))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (encodePair A B).length /
          Real.sqrt (Real.logb 2 ((encodePair A B).length + 2)))⌋₊ := by
  obtain ⟨pk, hQ, hR, hOk, -⟩ := arithPiInt.pkg_exists
  obtain ⟨M, C, hfin, h⟩ := GR.queryM_TM pk specPi specPi_pre_polyT specPi_small_polyT specPi_q1_polyT
    specPi_q2_polyT specPi_fin_polyT (fun w => specPi_length pk w) (fun w _ => hOk w)
    (fun w _ => Nat.zero_le _) (fun w _ => Nat.zero_le _)
  refine ⟨M, C, hfin, fun A B => ?_⟩
  have e : GR.answerQ pk specPi (encodePair A B) =
      Computability.encodeNat (((Finset.Icc A B).filter Nat.Prime).card % 2) := by
    refine specPi_answer_eq pk _ ?_
    rw [hQ, arithPiInt_parity, rdM_encodePair, rdA_encodePair]
  have := h (encodePair A B)
  rwa [e] at this

end EthFollowup.Primes
