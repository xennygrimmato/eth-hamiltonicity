/-
# ArithL, module 5: a counted-network package from a leveled description reader

Template: `ModP/ArithPackage.lean`. An `ArithLSpec` is a polynomial-time reader
`desc : (input word, query word) ↦ LDesc` with a network size `nf w ≤ |w|` (unary), rounds
`R w ≤ |w|`, a spread constant `cS ≥ 1` with `(desc y).Spread cS`, the level bound
`(desc y).nL ≤ ν (nf y.1) + 3`, and well-formedness at `nf w` for every query word of length `≤ R w`.
**`ArithLSpec.pkg_exists`** gives a `CntPackage (2^22·cS)` whose count is
`Q w π = LDesc.count (nf w) (desc (w, π))`, with `R = A.R` and `Ok = True`. The polynomial-time
table and reader are discharged here (`ArithLPoly`).

* `countL_le`: the count is at most `2^{b·Σ_v ℓ_{lv v}} ≤ 2^{2^13 cS (n+2)}` (geometric sum over the
  levels, `b ≤ Wa`); `countL_lt`;
* `ArithLSpec`, `prep`, `prep_unary`, `nV_unary`, `nL_unary`, `PL_unary`, **`prep_polyT`**, `net`;
* **`ArithLSpec.pkg_exists`**.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLPoly
import EthFollowup.Primes.ArithLNetCount
import EthFollowup.ModP.ArithPackage

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring
  EthFollowup.ModP

instance : SzLen LDesc := ⟨fun d => (SzLen.le d.toT : _)⟩

/-! ## The bound on the count -/

theorem b_le_Wa (n : ℕ) : b n ≤ Wa n := by
  have h1 := ℓ_mul_pow_le n
  have h2 : 2 ^ (2 * b n) ≤ 2 ^ J n :=
    le_trans (Nat.le_mul_of_pos_left _ (ℓ_pos n)) h1
  have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  unfold Wa; omega

theorem countB_le_prod (b : ℕ) (bx : ℕ → ℕ) (L : LDesc) :
    L.countB b bx ≤ ∏ v ∈ range L.D.nV, bx (L.lv v) := by
  unfold LDesc.countB
  refine (card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset]
  simp only [card_range]
  exact (Fin.prod_univ_eq_prod_range (fun v => bx (L.lv v)) L.D.nV).le

/-- **The count is at most `2^{2^13 c (n+2)}`** under `Spread c` and the level bound. -/
theorem countL_le {n c : ℕ} {L : LDesc} (hs : L.Spread c) (hc : 1 ≤ c) (hK : L.nL ≤ ν n + 3) :
    L.count n ≤ 2 ^ (2 ^ 13 * c * (n + 2)) := by
  have h1 : L.count n ≤ 2 ^ (b n * SV L (kl n)) := by
    refine (countB_le_prod (b n) (lbox n) L).trans (le_of_eq ?_)
    unfold SV lbox
    rw [Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
  have h2 : SV L (kl n) ≤ c * (4 * ℓ n + L.nL) :=
    (SV_le hs hc (kl_antitone n)).trans (Nat.mul_le_mul_left _ (sum_kl_le n _))
  have h3 : b n * ℓ n ≤ 257 * (n + 2) := by
    have := nB_le' n; unfold nB at this; rw [mul_comm]; exact this
  have h4 : b n * L.nL ≤ 2 ^ 12 * (n + 2) := by
    have := (ν_Wa_le n).1
    calc b n * L.nL ≤ Wa n * (ν n + 3) := Nat.mul_le_mul (b_le_Wa n) hK
      _ = (ν n + 3) * Wa n := mul_comm _ _
      _ ≤ 2 ^ 12 * (n + 2) := this
  have h5 : b n * SV L (kl n) ≤ 2 ^ 13 * c * (n + 2) := by
    calc b n * SV L (kl n) ≤ b n * (c * (4 * ℓ n + L.nL)) := Nat.mul_le_mul_left _ h2
      _ = c * (4 * (b n * ℓ n) + b n * L.nL) := by ring
      _ ≤ c * (4 * (257 * (n + 2)) + 2 ^ 12 * (n + 2)) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 ^ 13 * c * (n + 2) := by nlinarith
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) h5)

theorem countL_lt {n m c : ℕ} {L : LDesc} (hn : n ≤ m) (hs : L.Spread c) (hc : 1 ≤ c) (hK : L.nL ≤ ν n + 3) :
    L.count n < 2 ^ ((2 ^ 13 * c + 1) * (m + 2)) := by
  refine (countL_le hs hc hK).trans_lt (Nat.pow_lt_pow_right (by norm_num) ?_)
  have : 2 ^ 13 * c * (n + 2) ≤ 2 ^ 13 * c * (m + 2) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-! ## The specification of a package -/

/-- **A leveled description reader**: the network size `nf w` (unary), the rounds `R w`, the leveled
description `desc (w, π)` (polynomial time) with a spread constant, a level bound and
well-formedness. -/
structure ArithLSpec where
  nf : List Bool → ℕ
  nf_le : ∀ w, nf w ≤ w.length
  nf_unary : Unary nf
  R : List Bool → ℕ
  R_le : ∀ w, R w ≤ w.length
  R_poly : PolyT R
  desc : List Bool × List Bool → LDesc
  desc_poly : PolyT desc
  cS : ℕ
  one_le_cS : 1 ≤ cS
  spread : ∀ y, (desc y).Spread cS
  lev_le : ∀ y, (desc y).nL ≤ ν (nf y.1) + 3
  wf : ∀ w π, π.length ≤ R w → (desc (w, π)).WF (nf w)

namespace ArithLSpec

variable (A : ArithLSpec)

/-- **The reader of the package**: `(g in unary, (w, π)) ↦` the context of the leveled network of
`desc (w, π)` at size `nf w`, with `g` nodes and `P = PL`. -/
def prep (y : List Unit × (List Bool × List Bool)) : EthFollowup.Primes.ACtx :=
  EthFollowup.Primes.aCtxOf (A.nf y.2.1) (A.desc y.2) y.1.length (PL (A.nf y.2.1) A.cS y.1.length)

theorem prep_unary (g : ℕ) (w π : List Bool) :
    A.prep (Printed.unary g, (w, π)) =
      EthFollowup.Primes.aCtxOf (A.nf w) (A.desc (w, π)) g (PL (A.nf w) A.cS g) := by
  simp only [prep, Printed.unary, List.length_replicate]

theorem desc_poly' : PolyT fun y : List Unit × (List Bool × List Bool) => A.desc y.2 :=
  A.desc_poly.comp (PolyT.snd PolyT.id')

theorem nf_unary' : Unary fun y : List Unit × (List Bool × List Bool) => A.nf y.2.1 :=
  A.nf_unary.comp (PolyT.fst (PolyT.snd PolyT.id'))

theorem nL_unary : Unary fun y : List Unit × (List Bool × List Bool) => (A.desc y.2).nL :=
  Unary.of_le (A.nf_unary'.add (Unary.const 5)) (LDesc.nL_polyT A.desc_poly') fun y => by
    have h1 := A.lev_le y.2
    have h2 := ν_le (A.nf y.2.1)
    omega

theorem nV_unary : Unary fun y : List Unit × (List Bool × List Bool) => (A.desc y.2).D.nV :=
  Unary.of_le (Unary.mul (Unary.const A.cS) (A.nf_unary'.add (Unary.const 5)))
    (Desc.nV_polyT (LDesc.D_polyT A.desc_poly')) fun y => by
      have h1 := nV_le (A.spread y.2) A.one_le_cS
      have h2 := A.lev_le y.2
      have h3 := ν_le (A.nf y.2.1)
      exact h1.trans (Nat.mul_le_mul_left _ (by omega))

/-- The parameter `P = PL` of the reader, in unary. -/
theorem PL_unary : Unary fun y : List Unit × (List Bool × List Bool) => PL (A.nf y.2.1) A.cS y.1.length := by
  have hn := A.nf_unary'
  have hg := g_unary'
  unfold PL
  refine Unary.mul (Unary.const _) (Unary.add ?_ (dg_unary hn))
  exact Unary.of_le (hn.add (Unary.const 2)) (PolyT.div (hn.add (Unary.const 2)).poly hg.poly)
    fun x => Nat.div_le_self _ _

/-- **The reader is polynomial-time.** -/
theorem prep_polyT : PolyT A.prep :=
  aCtxOfL_polyT A.nf_unary' A.desc_poly' A.nV_unary A.nL_unary g_unary' A.PL_unary

/-- The network of `(g, w, π)` (an empty network for `g < 2`, never used). -/
def net (g : ℕ) (w π : List Bool) : Net g :=
  if h : 2 ≤ g then (EthFollowup.Primes.arithSys (A.nf w) (A.desc (w, π)) g h).net (aLabCode (A.nf w))
  else emptyNet g

/-- **The counted-network package of a leveled description reader**: `Q w π = LDesc.count (nf w)
(desc (w, π))`, `R = A.R`, `Ok = True`, `c₀ = 2^22·cS`, `qb = 2^13 cS + 1`. -/
theorem pkg_exists :
    ∃ pk : CntPackage (2 ^ 22 * A.cS), (∀ w π, pk.Q w π = (A.desc (w, π)).count (A.nf w)) ∧
      (∀ w, pk.R w = A.R w) ∧ (∀ w, pk.Ok w) ∧ pk.qb = 2 ^ 13 * A.cS + 1 := by
  have hp := A.prep_polyT
  obtain ⟨-, c', -, hc⟩ := id hp
  have hX : ∀ (g : ℕ) (w : List Bool) (q : ℕ), 1 ≤ q → 1 ≤ q * (w.length + g + 2) ^ q := fun g w q hq =>
    Nat.mul_le_mul hq (Nat.one_le_pow _ _ (by omega))
  obtain ⟨K, hK⟩ : ∃ K, K = 2 ^ 22 * 2049 * A.cS := ⟨_, rfl⟩
  refine ⟨{
    Ctx := EthFollowup.Primes.ACtx
    Np := EthFollowup.Primes.arithNp
    keeps := arithLNp_keeps
    P_unary := labelProcsW_P layALF_polyT
    B_unary := labelProcsW_B layALF_polyT
    prep := A.prep
    prep_poly := hp
    q := 3 * (c' * 6 ^ c') + 6 * K + 17 + c' + 1
    Q := fun w π => (A.desc (w, π)).count (A.nf w)
    R := A.R
    R_le := A.R_le
    R_poly := A.R_poly
    qb := 2 ^ 13 * A.cS + 1
    Ok := fun _ => True
    Q_lt := fun w π _ _ => countL_lt (A.nf_le w) (A.spread _) A.one_le_cS (A.lev_le _)
    net := A.net
    P := fun g w _ => PL (A.nf w) A.cS g
    B := fun _ _ _ => 1
    τ := fun _ _ _ => 1
    S := fun g w π => EthFollowup.Primes.SAN (A.nf w) (A.desc (w, π)) g (PL (A.nf w) A.cS g)
    isNet := fun g w π hg _ hπ => by
      rw [A.prep_unary, net, dif_pos hg]
      exact EthFollowup.Primes.arithNet_isNet hg
        (EthFollowup.Primes.arithSys_is hg (A.wf w π hπ) (A.spread _) A.one_le_cS (A.lev_le _))
    value := fun g w π hg _ hπ => by
      rw [net, dif_pos hg]
      exact EthFollowup.Primes.arithNet_value hg (A.wf w π hπ)
    U_le := fun g w π hg _ hπ => by
      rw [net, dif_pos hg]
      refine (EthFollowup.Primes.arithSys_U_le hg (A.wf w π hπ) (A.spread _) A.one_le_cS (A.lev_le _)).trans ?_
      have := A.nf_le w
      have h1 : 2 ^ 19 * A.cS ≤ 2 ^ 22 * A.cS := Nat.mul_le_mul_right _ (by norm_num)
      exact Nat.mul_le_mul h1 (by omega)
    P_le := fun g w π _ _ _ => by
      unfold PL
      exact Nat.mul_le_mul_left _
        (Nat.add_le_add (Nat.div_le_div_right (by have := A.nf_le w; omega)) (dg_mono (A.nf_le w)))
    B_le := fun g w π _ _ _ => hX g w _ (by omega)
    τ_le := fun g w π _ _ _ => hX g w _ (by omega)
    S_le := fun g w π _ _ hπ => by
      have hπw : π.length ≤ w.length := hπ.trans (A.R_le w)
      set y := (Printed.unary g, (w, π)) with hy
      set c := A.prep y
      have h1 : size c ≤ len c := SzLen.le c
      have h2 : len c ≤ c' * (len y + 1) ^ c' := hc y
      have hly : len y ≤ 4 * g + 6 * w.length + 10 := by
        rw [hy, len_pair, len_pair, len_units, len_bools, len_bools]
        simp only [Printed.unary, List.length_replicate]
        omega
      set X := w.length + g + 2 with hXd
      have hX1 : 1 ≤ X := by omega
      have h3 : len y + 1 ≤ 6 * X := by omega
      have h4 : c' * (len y + 1) ^ c' ≤ c' * 6 ^ c' * X ^ c' := by
        calc c' * (len y + 1) ^ c' ≤ c' * (6 * X) ^ c' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
          _ = c' * 6 ^ c' * X ^ c' := by rw [mul_pow]; ring
      set q := 3 * (c' * 6 ^ c') + 6 * K + 17 + c' + 1 with hq
      have h5 : X ^ c' ≤ X ^ q := Nat.pow_le_pow_right hX1 (by omega)
      have h6 : X ≤ X ^ q := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ q := Nat.pow_le_pow_right hX1 (by omega)
      have h7 : c' * 6 ^ c' * X ^ c' ≤ c' * 6 ^ c' * X ^ q := Nat.mul_le_mul_left _ h5
      have hP : PL (A.nf w) A.cS g ≤ K * X := by
        have hd := dg_le (A.nf w)
        have hdiv : (A.nf w + 2) / g ≤ A.nf w + 2 := Nat.div_le_self _ _
        have hn := A.nf_le w
        unfold PL
        calc 2 ^ 22 * A.cS * ((A.nf w + 2) / g + dg (A.nf w))
            ≤ 2 ^ 22 * A.cS * (2049 * X) := Nat.mul_le_mul_left _ (by omega)
          _ = K * X := by rw [hK]; ring
      have hKX : K * X ≤ K * X ^ q := Nat.mul_le_mul_left _ h6
      have e' : ∀ Y : ℕ, q * Y = 3 * (c' * 6 ^ c' * Y) + 6 * (K * Y) + 17 * Y + (c' + 1) * Y := fun Y => by
        rw [hq]; ring
      have e := e' (X ^ q)
      have hc0 : c = EthFollowup.Primes.aCtxOf (A.nf w) (A.desc (w, π)) g (PL (A.nf w) A.cS g) := A.prep_unary g w π
      show EthFollowup.Primes.SAN (A.nf w) (A.desc (w, π)) g (PL (A.nf w) A.cS g) + size c ≤ q * X ^ q
      unfold EthFollowup.Primes.SAN EthFollowup.Primes.SA
      rw [← hc0, e]
      generalize PL (A.nf w) A.cS g = P at *
      generalize c' * 6 ^ c' * X ^ q = Z at *
      generalize K * X ^ q = KY at *
      generalize K * X = KX at *
      generalize X ^ q = Y at *
      generalize c' * 6 ^ c' * X ^ c' = Z' at *
      generalize (c' + 1) * Y = Y' at *
      generalize c' * (len y + 1) ^ c' = T at *
      omega }, fun _ _ => rfl, fun _ => rfl, fun _ => trivial, rfl⟩

end ArithLSpec

end EthFollowup.Primes
