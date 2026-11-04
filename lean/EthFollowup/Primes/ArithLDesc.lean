/-
# Leveled arithmetic-constraint descriptions (ArithL library, module 1)

`scratchpad/plans/primes-plan.md` (Executor L); interface `primes-interface.md` (ArithLDesc).

A leveled description `L : LDesc` is an ArithNet description `L.D : Desc` (`ModP.ArithDesc`) together
with a **level** for every variable (`lev`) and every chain (`levC`). Variables of level `k` live in a
box `[0, bx k)` (the network takes `bx k = 2^{b·ℓ_k}` with geometrically shrinking `ℓ_k`), and the
semantics is otherwise that of `Desc.Sat`:

* `LDesc.countB b bx L = #{x ∈ ∏_v [0, bx (lv v)) : L.D.Sat b x}`;
* `LDesc.WFB b lk L`: well-formedness with `lk k` limbs (of `b` bits) at level `k`: ArithNet's
  conditions, plus: every product sits in a chain and has that chain's level (`lp`); product operands
  and comparison operands are variables of level `≥` (comparisons: `=`) the level of their product
  (comparison), constants have `≤ lk k` limbs; patterns have `≤ b·lk (lv v)` positions;
  **no `.lin` terms in chains** (write `x_v` as the product `x_v · 1`, `⟨v, .const [1]⟩`);
* `LDesc.Spread c L`: object `i` of each kind has level `≥ i / c` (gives the geometric cost sums).

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import EthFollowup.ModP.ArithDesc

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.ModP

/-- **A leveled description**: an ArithNet description with levels for variables and chains. -/
structure LDesc where
  D : Desc
  lev : List ℕ
  levC : List ℕ
  deriving DecidableEq, Inhabited, Repr

namespace LDesc

variable (L : LDesc)

/-- The level of variable `v`. -/
def lv (v : ℕ) : ℕ := L.lev.getD v 0
/-- The level of chain `c`. -/
def lc (c : ℕ) : ℕ := L.levC.getD c 0
/-- The level of product `p`: the level of its chain. -/
def lp (p : ℕ) : ℕ := L.lc (L.D.chainOf p)
/-- The level of comparison `q`: the level of its variable. -/
def lq (q : ℕ) : ℕ := L.lv (L.D.cmps.getD q default).v

/-- **The count**: `#{x ∈ ∏_{v < nV} [0, bx (lv v)) : x satisfies L.D}`. -/
def countB (b : ℕ) (bx : ℕ → ℕ) : ℕ :=
  ((Fintype.piFinset fun v : Fin L.D.nV => range (bx (L.lv v))).filter fun x =>
    L.D.Sat b (extV L.D.nV x)).card

/-- An operand at level `k` (`lk k` limbs of `b` bits): a variable of level `≥ k`, or a constant. -/
def OpOK (b : ℕ) (lk : ℕ → ℕ) (k : ℕ) : Operand → Prop
  | .var w => w < L.D.nV ∧ k ≤ L.lv w
  | .const l => l.length ≤ lk k ∧ ∀ y ∈ l, y < 2 ^ b

/-- A chain term source at level `k`: a product, or a constant (no `.lin` terms). -/
def SrcOK (b : ℕ) (lk : ℕ → ℕ) (k : ℕ) : Src → Prop
  | .prod p => p < L.D.prods.length
  | .lin _ => False
  | .const l => l.length ≤ lk k ∧ ∀ y ∈ l, y < 2 ^ b

/-- A comparison right-hand side at level `k`: a variable of level exactly `k`, or a constant. -/
def CmpOK (b : ℕ) (lk : ℕ → ℕ) (k : ℕ) : Operand → Prop
  | .var w => w < L.D.nV ∧ L.lv w = k
  | .const l => l.length ≤ lk k ∧ ∀ y ∈ l, y < 2 ^ b

/-- **Well-formedness** (limb width `b`, `lk k` limbs at level `k`). -/
structure WFB (b : ℕ) (lk : ℕ → ℕ) : Prop where
  pat_len : ∀ v < L.D.nV, (L.D.pat.getD v []).length ≤ b * lk (L.lv v)
  prod_ok : ∀ p < L.D.prods.length, (L.D.prods.getD p default).u < L.D.nV ∧
    L.lp p ≤ L.lv (L.D.prods.getD p default).u ∧ L.OpOK b lk (L.lp p) (L.D.prods.getD p default).w ∧
    L.D.chainOf p < L.D.chains.length
  term_ok : ∀ c < L.D.chains.length, ∀ t ∈ (L.D.chains.getD c default).lhs ++ (L.D.chains.getD c default).rhs,
    L.SrcOK b lk (L.lc c) t.src
  coeff_le : ∀ ch ∈ L.D.chains, (ch.lhs.map Term.coeff).sum ≤ 32 ∧ (ch.rhs.map Term.coeff).sum ≤ 32
  prod_once : ∀ c < L.D.chains.length, ∀ c' < L.D.chains.length, ∀ p : ℕ,
    (L.D.chains.getD c default).HasProd p → (L.D.chains.getD c' default).HasProd p → c = c'
  cmp_ok : ∀ q < L.D.cmps.length, (L.D.cmps.getD q default).v < L.D.nV ∧
    L.CmpOK b lk (L.lq q) (L.D.cmps.getD q default).rhs

/-- **Spread**: the `i`-th variable, product, chain and comparison has level `≥ i / c`. -/
structure Spread (c : ℕ) : Prop where
  var : ∀ v < L.D.nV, v / c ≤ L.lv v
  prod : ∀ p < L.D.prods.length, p / c ≤ L.lp p
  chain : ∀ j < L.D.chains.length, j / c ≤ L.lc j
  cmp : ∀ q < L.D.cmps.length, q / c ≤ L.lq q

/-- Number of levels: one more than the largest entry of `lev` and `levC`. -/
def nL : ℕ := (L.lev.foldr max 0 ⊔ L.levC.foldr max 0) + 1

theorem le_foldr_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | a :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max h).trans (le_max_right _ _)

theorem getD_le_foldr (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.foldr max 0 := by
  by_cases hl : i < l.length
  · rw [List.getD_eq_getElem _ _ hl]; exact le_foldr_max (List.getElem_mem hl)
  · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _

theorem lv_lt_nL (v : ℕ) : L.lv v < L.nL := by
  have := getD_le_foldr L.lev v
  unfold nL lv; omega

theorem lc_lt_nL (c : ℕ) : L.lc c < L.nL := by
  have := getD_le_foldr L.levC c
  unfold nL lc; omega

theorem lp_lt_nL (p : ℕ) : L.lp p < L.nL := L.lc_lt_nL _

theorem lq_lt_nL (q : ℕ) : L.lq q < L.nL := L.lv_lt_nL _

theorem chainOf_eq {b : ℕ} {lk : ℕ → ℕ} (hL : L.WFB b lk) {p c : ℕ} (hc : c < L.D.chains.length)
    (h : (L.D.chains.getD c default).HasProd p) : L.D.chainOf p = c := by
  obtain ⟨h1, h2⟩ := L.D.chainOf_spec hc h
  exact hL.prod_once _ (lt_of_le_of_lt h1 hc) _ hc p h2 h

end LDesc

end EthFollowup.Primes
