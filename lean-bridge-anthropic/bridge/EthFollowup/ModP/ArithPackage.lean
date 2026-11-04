/-
# ArithNet, module L4: a counted-network package from a description reader

`scratchpad/plans/modp-plan.md`, ADDENDUM §B (row L4). An `ArithSpec` is a polynomial-time reader
`desc : (input word, query word) ↦ Desc` with a network size `nf w ≤ |w|` (in unary), a number of
rounds `R w ≤ |w|`, a bound `cA (desc y) ≤ cD` on the shape constant and well-formedness at `nf w`
for every query word of length `≤ R w`. From it (and the polynomial-time table and reader of
ArithPoly, as hypotheses), `ArithSpec.pkg_exists` gives a `CntPackage (2^12·cD)` whose count is
`Q w π = Desc.count (nf w) (desc (w, π))`, with `R = A.R` and `Ok = True`.

* `SzLen` for sums and descriptions (sizes are at most word lengths);
* `nB_le'`, `dg_mono`, `nV_le_cA`, `countB_le_pow`, `count_lt` (the bound `Q < 2^{qb(|w|+2)}`);
* `ArithSpec`, `ArithSpec.prep` (the reader of the package), `ArithSpec.prep_unary`,
  `ArithSpec.cA_unary`, `ArithSpec.PA_unary`, `ArithSpec.net`;
* **`ArithSpec.pkg_exists`**.

Standard axioms only.
-/
import EthFollowup.ModP.ArithProcs
import EthFollowup.ModP.ArithNet
import EthFollowup.ModP.CntPackage
import EthFollowup.Factoring.MulPackage

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset EthFollowup.Factoring

/-! ## Sizes are at most word lengths -/

instance {α β : Type} [Enc α] [Enc β] [HasSize α] [HasSize β] [SzLen α] [SzLen β] : SzLen (α ⊕ β) :=
  ⟨fun s => by
    rcases s with a | b
    · have := SzLen.le a; rw [len_inl, size_inl]; omega
    · have := SzLen.le b; rw [len_inr, size_inr]; omega⟩

instance : SzLen Desc := ⟨fun d => (SzLen.le d.toE : _)⟩

/-! ## Arithmetic of the bounds -/

theorem nB_le' (n : ℕ) : nB n ≤ 257 * (n + 2) := by
  have e1 : nB n ≤ n + ℓ n := by
    unfold nB b; rw [mul_add, mul_one]; have := Nat.mul_div_le n (ℓ n); omega
  have e2 : ℓ n ≤ 2 ^ 8 * (n + 2) :=
    le_trans (Nat.le_mul_of_pos_right _ (by unfold W; omega)) (ℓ_mul_W_le n)
  omega

theorem dg_mono {n n' : ℕ} (h : n ≤ n') : dg n ≤ dg n' := by
  unfold dg
  apply Nat.pow_le_pow_right (by norm_num)
  have : ν n ≤ ν n' := Nat.log_mono_right (by omega)
  omega

theorem nV_le_cA (D : Desc) : D.nV ≤ cA D := by
  unfold cA
  have h1 : D.nV + D.nP + D.nQ + 1 ≤ (D.nV + D.nP + D.nQ + 1) * (D.nC + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem countB_le_pow (b B : ℕ) (D : Desc) : D.countB b B ≤ B ^ D.nV := by
  unfold Desc.countB
  refine (card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset]; simp

/-- The count at size `n ≤ m` is below `2^{(257 cD + 1)(m + 2)}`. -/
theorem count_lt {n m cD : ℕ} {D : Desc} (hn : n ≤ m) (hc : cA D ≤ cD) :
    D.count n < 2 ^ ((257 * cD + 1) * (m + 2)) := by
  have h1 : D.count n ≤ 2 ^ (nB n * D.nV) := by
    rw [pow_mul]; exact countB_le_pow _ _ _
  have hnB : nB n ≤ 257 * (m + 2) := (nB_le' n).trans (by omega)
  have hV : D.nV ≤ cD := (nV_le_cA D).trans hc
  have h2 : nB n * D.nV ≤ 257 * (m + 2) * cD := Nat.mul_le_mul hnB hV
  have e : (257 * cD + 1) * (m + 2) = 257 * (m + 2) * cD + (m + 2) := by ring
  refine h1.trans_lt (Nat.pow_lt_pow_right (by norm_num) ?_)
  rw [e]; omega

/-! ## The specification of a package -/

/-- **A description reader**: the network size `nf w` (unary), the rounds `R w`, the description
`desc (w, π)` of the query `π` on the input word `w` (polynomial time), with a shape bound and
well-formedness. -/
structure ArithSpec where
  nf : List Bool → ℕ
  nf_le : ∀ w, nf w ≤ w.length
  nf_unary : Unary nf
  R : List Bool → ℕ
  R_le : ∀ w, R w ≤ w.length
  R_poly : PolyT R
  desc : List Bool × List Bool → Desc
  desc_poly : PolyT desc
  cD : ℕ
  cA_le : ∀ y, cA (desc y) ≤ cD
  wf : ∀ w π, π.length ≤ R w → (desc (w, π)).WF (nf w)

theorem g_unary' : Unary fun y : List Unit × (List Bool × List Bool) => y.1.length :=
  Unary.of_length (PolyT.fst PolyT.id')

namespace ArithSpec

variable (A : ArithSpec)

/-- **The reader of the package**: `(g in unary, (w, π)) ↦` the context of the network of
`desc (w, π)` at size `nf w`, with `g` nodes and `P = PA`. -/
def prep (y : List Unit × (List Bool × List Bool)) : ACtx :=
  aCtxOf (A.nf y.2.1) (A.desc y.2) y.1.length (PA (A.nf y.2.1) (A.desc y.2) y.1.length)

theorem prep_unary (g : ℕ) (w π : List Bool) :
    A.prep (Printed.unary g, (w, π)) =
      aCtxOf (A.nf w) (A.desc (w, π)) g (PA (A.nf w) (A.desc (w, π)) g) := by
  simp only [prep, Printed.unary, List.length_replicate]

theorem desc_poly' : PolyT fun y : List Unit × (List Bool × List Bool) => A.desc y.2 :=
  A.desc_poly.comp (PolyT.snd PolyT.id')

theorem nf_unary' : Unary fun y : List Unit × (List Bool × List Bool) => A.nf y.2.1 :=
  A.nf_unary.comp (PolyT.fst (PolyT.snd PolyT.id'))


theorem cA_unary : Unary fun y : List Unit × (List Bool × List Bool) => cA (A.desc y.2) := by
  have hp : PolyT fun y : List Unit × (List Bool × List Bool) => cA (A.desc y.2) := by
    have h := A.desc_poly'
    unfold cA Desc.nP Desc.nQ Desc.nC
    fun_prop
  exact Unary.of_le (Unary.const A.cD) hp fun y => A.cA_le _

/-- The parameter `P = PA` of the reader, in unary. -/
theorem PA_unary : Unary fun y : List Unit × (List Bool × List Bool) =>
    PA (A.nf y.2.1) (A.desc y.2) y.1.length := by
  have hn := A.nf_unary'
  have hg := g_unary'
  unfold PA
  refine Unary.mul (Unary.mul (Unary.const _) A.cA_unary) (Unary.add ?_ (dg_unary hn))
  exact Unary.of_le (hn.add (Unary.const 2)) (PolyT.div (hn.add (Unary.const 2)).poly hg.poly)
    fun x => Nat.div_le_self _ _

/-- The network of `(g, w, π)` (an empty network for `g < 2`, never used). -/
def net (g : ℕ) (w π : List Bool) : Net g :=
  if h : 2 ≤ g then (arithSys (A.nf w) (A.desc (w, π)) g h).net (aLabCode (A.nf w)) else emptyNet g

/-- **The counted-network package of a description reader**, given the polynomial-time table
`tabAF` and reader `A.prep` (module ArithPoly): `Q w π = Desc.count (nf w) (desc (w, π))`,
`R = A.R`, `Ok = True`, `c₀ = 2^12·cD`, `qb = 257 cD + 1`. -/
theorem pkg_exists (hT : PolyT tabAF) (hp : PolyT A.prep) :
    ∃ pk : CntPackage (2 ^ 12 * A.cD), (∀ w π, pk.Q w π = (A.desc (w, π)).count (A.nf w)) ∧
      (∀ w, pk.R w = A.R w) ∧ (∀ w, pk.Ok w) ∧ pk.qb = 257 * A.cD + 1 := by
  obtain ⟨-, c', -, hc⟩ := id hp
  have hX : ∀ (g : ℕ) (w : List Bool) (q : ℕ), 1 ≤ q → 1 ≤ q * (w.length + g + 2) ^ q := fun g w q hq =>
    Nat.mul_le_mul hq (Nat.one_le_pow _ _ (by omega))
  have hlay : PolyT layAF := PolyT.fst PolyT.id'
  obtain ⟨K, hK⟩ : ∃ K, K = 2 ^ 12 * 2049 * A.cD := ⟨_, rfl⟩
  refine ⟨{
    Ctx := ACtx
    Np := arithNp
    keeps := labelProcsW_keeps hlay (PolyT.const false) ⟨IsPolyT.ofFun hT⟩
    P_unary := labelProcsW_P hlay
    B_unary := labelProcsW_B hlay
    prep := A.prep
    prep_poly := hp
    q := 3 * (c' * 6 ^ c') + 6 * K + 17 + c' + 1
    Q := fun w π => (A.desc (w, π)).count (A.nf w)
    R := A.R
    R_le := A.R_le
    R_poly := A.R_poly
    qb := 257 * A.cD + 1
    Ok := fun _ => True
    Q_lt := fun w π _ _ => count_lt (A.nf_le w) (A.cA_le _)
    net := A.net
    P := fun g w π => PA (A.nf w) (A.desc (w, π)) g
    B := fun _ _ _ => 1
    τ := fun _ _ _ => 1
    S := fun g w π => SAN (A.nf w) (A.desc (w, π)) g (PA (A.nf w) (A.desc (w, π)) g)
    isNet := fun g w π hg _ _ => by
      rw [A.prep_unary, net, dif_pos hg]
      exact arithNet_isNet hg (arithSys_is hg)
    value := fun g w π hg _ hπ => by
      rw [net, dif_pos hg]
      exact arithNet_value hg (A.wf w π hπ)
    U_le := fun g w π hg _ _ => by
      rw [net, dif_pos hg]
      refine (arithSys_U_le hg).trans (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) (A.cA_le _)) ?_)
      have := A.nf_le w; omega
    P_le := fun g w π _ _ _ => by
      unfold PA
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (A.cA_le _))
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
      have hP : PA (A.nf w) (A.desc (w, π)) g ≤ K * X := by
        have hd := dg_le (A.nf w)
        have hdiv : (A.nf w + 2) / g ≤ A.nf w + 2 := Nat.div_le_self _ _
        have hn := A.nf_le w
        unfold PA
        calc 2 ^ 12 * cA (A.desc (w, π)) * ((A.nf w + 2) / g + dg (A.nf w))
            ≤ 2 ^ 12 * A.cD * (2049 * X) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (A.cA_le _)) (by omega)
          _ = K * X := by rw [hK]; ring
      have hKX : K * X ≤ K * X ^ q := Nat.mul_le_mul_left _ h6
      have e' : ∀ Y : ℕ, q * Y = 3 * (c' * 6 ^ c' * Y) + 6 * (K * Y) + 17 * Y + (c' + 1) * Y := fun Y => by
        rw [hq]; ring
      have e := e' (X ^ q)
      have hc0 : c = aCtxOf (A.nf w) (A.desc (w, π)) g (PA (A.nf w) (A.desc (w, π)) g) := A.prep_unary g w π
      show SAN (A.nf w) (A.desc (w, π)) g (PA (A.nf w) (A.desc (w, π)) g) + size c ≤ q * X ^ q
      unfold SAN SA
      rw [← hc0, e]
      generalize PA (A.nf w) (A.desc (w, π)) g = P at *
      generalize c' * 6 ^ c' * X ^ q = Z at *
      generalize K * X ^ q = KY at *
      generalize K * X = KX at *
      generalize X ^ q = Y at *
      generalize c' * 6 ^ c' * X ^ c' = Z' at *
      generalize (c' + 1) * Y = Y' at *
      generalize c' * (len y + 1) ^ c' = T at *
      omega }, fun _ _ => rfl, fun _ => rfl, fun _ => trivial, rfl⟩

end ArithSpec

end EthFollowup.ModP
