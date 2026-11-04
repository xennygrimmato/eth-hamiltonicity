/-
# Counted-network packages (module B4, part 1)

`scratchpad/plans/modp-plan.md` §5. A `CntPackage c₀` is `Factoring.MulPackage c₀` with the counted
quantity abstracted: ONE context type, ONE set of procedures, ONE polynomial-time reader
`prep : (g in unary, (w, π)) ↦ context`, ONE constant `q`; a counted quantity `Q w π < 2^{qb(|w|+2)}`,
a number of rounds `R w ≤ |w|` (polynomial time) and a predicate `Ok` on input words. For every
`g ≥ 2`, every input word `w` with `Ok w` and every query word `π` with `|π| ≤ R w`: the network
`net g w π` is a network with parameters `P, B, τ, S` given by `Np`, its value is `Q w π`,
`U ≤ c₀(n+2)`, `P ≤ c₀((n+2)/g + dg n)`, `B, τ, S + size(prep …) ≤ q(n+g+2)^q` (`n = |w|`).

* `CntPackage`;
* `CntPackage.ofMul : MulPackage c₀ → CntPackage c₀` (`Q = D`, `R = length`, `Ok w ↔ 1 ≤ ofWord w`),
  the sanity check of the abstraction.

Standard axioms only.
-/
import EthFollowup.Factoring.Params

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset Groundwork EthFollowup.Factoring

open Eight.SecNetworks in
/-- **A uniform counted-network package** with the absolute constant `c₀` (`MulPackage` with the
counted quantity `Q`, the rounds `R` and the side condition `Ok` abstracted). -/
structure CntPackage (c₀ : ℕ) : Type 1 where
  Ctx : Type
  [encCtx : Enc Ctx]
  [sizeCtx : HasSize Ctx]
  [carriedCtx : Carried Ctx]
  Np : Procs Ctx
  keeps : Np.Keeps
  P_unary : Unary Np.P
  B_unary : Unary Np.B
  /-- The reader: `(g in unary, (input word, query word)) ↦ context`. -/
  prep : List Unit × (List Bool × List Bool) → Ctx
  prep_poly : PolyT prep
  q : ℕ
  /-- The counted quantity of the query word `π` on the input word `w`. -/
  Q : List Bool → List Bool → ℕ
  /-- The number of rounds (query words have length at most `R w`). -/
  R : List Bool → ℕ
  R_le : ∀ w, R w ≤ w.length
  R_poly : PolyT R
  qb : ℕ
  /-- The input words on which the networks are promised. -/
  Ok : List Bool → Prop
  Q_lt : ∀ (w π : List Bool), Ok w → π.length ≤ R w → Q w π < 2 ^ (qb * (w.length + 2))
  net : ∀ g : ℕ, List Bool → List Bool → Net g
  P : ℕ → List Bool → List Bool → ℕ
  B : ℕ → List Bool → List Bool → ℕ
  τ : ℕ → List Bool → List Bool → ℕ
  S : ℕ → List Bool → List Bool → ℕ
  isNet : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → Ok w → π.length ≤ R w →
    IsNetwork Np (prep (Printed.unary g, (w, π))) (net g w π) (P g w π) (B g w π) (τ g w π) (S g w π)
  value : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → Ok w → π.length ≤ R w →
    (net g w π).value = (Q w π : ℤ)
  U_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → Ok w → π.length ≤ R w →
    (net g w π).U ≤ c₀ * (w.length + 2)
  P_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → Ok w → π.length ≤ R w →
    P g w π ≤ c₀ * ((w.length + 2) / g + dg w.length)
  B_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → Ok w → π.length ≤ R w →
    B g w π ≤ q * (w.length + g + 2) ^ q
  τ_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → Ok w → π.length ≤ R w →
    τ g w π ≤ q * (w.length + g + 2) ^ q
  S_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → Ok w → π.length ≤ R w →
    S g w π + size (prep (Printed.unary g, (w, π))) ≤ q * (w.length + g + 2) ^ q

attribute [instance] CntPackage.encCtx CntPackage.sizeCtx CntPackage.carriedCtx

namespace CntPackage

/-- The multiplication count is below `2^{2^{10}(n+2)}`. -/
theorem D_lt (N n : ℕ) (π : List Bool) : D N n π < 2 ^ (2 ^ 10 * (n + 2)) := by
  have h1 : D N n π ≤ 2 ^ nB n * 2 ^ nB n := by
    unfold D Dw; refine (card_filter_le _ _).trans ?_; rw [card_product, card_range]
  have h2 : D N n π < 2 ^ (2 * nB n + 1) := by
    rw [pow_succ, two_mul, pow_add]
    have : 0 < 2 ^ nB n * 2 ^ nB n := by positivity
    omega
  have hnB : nB n ≤ n + 2 ^ 8 * (n + 2) := by
    have e1 : nB n ≤ n + ℓ n := by
      unfold nB b; rw [mul_add, mul_one]; have := Nat.mul_div_le n (ℓ n); omega
    have e2 : ℓ n ≤ 2 ^ 8 * (n + 2) :=
      le_trans (Nat.le_mul_of_pos_right _ (by unfold W; omega)) (ℓ_mul_W_le n)
    omega
  exact h2.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The sanity check**: a multiplication-network package is a counted-network package with
`Q w π = D(ofWord w, |w|, π)`, `R w = |w|` and `Ok w ↔ 1 ≤ ofWord w`. -/
def ofMul {c₀ : ℕ} (pk : MulPackage c₀) : CntPackage c₀ where
  Ctx := pk.Ctx
  Np := pk.Np
  keeps := pk.keeps
  P_unary := pk.P_unary
  B_unary := pk.B_unary
  prep := pk.prep
  prep_poly := pk.prep_poly
  q := pk.q
  Q w π := D (ofWord w) w.length π
  R w := w.length
  R_le _ := le_rfl
  R_poly := by fun_prop
  qb := 2 ^ 10
  Ok w := 1 ≤ ofWord w
  Q_lt w π _ _ := D_lt _ _ _
  net := pk.net
  P := pk.P
  B := pk.B
  τ := pk.τ
  S := pk.S
  isNet := pk.isNet
  value := pk.value
  U_le := pk.U_le
  P_le := pk.P_le
  B_le := pk.B_le
  τ_le := pk.τ_le
  S_le := pk.S_le

end CntPackage

end EthFollowup.ModP
