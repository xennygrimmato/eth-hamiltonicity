/-
# Arithmetic-constraint descriptions: syntax and semantics (ArithNet library, part of L1)

`scratchpad/plans/modp-plan.md`, ADDENDUM §B; interface `modp-interface.md` (L1/ArithDesc).

A description `D : Desc` has `nV` variables `x_0, …, x_{nV-1}` (natural numbers in a box
`[0, B)`), bit patterns on the variables, products `x_u · w` (`w` a variable or a constant),
linear chains `Σ_lhs coeff·value = Σ_rhs coeff·value` over products, variables and constants, and
comparisons `x_v ⋈ w` (`⋈ ∈ {<, ≤, =, ≥, >}`, Compare's `CmpRel`, meaning `CmpRel.Holds`). Constants are given by their `b`-bit limbs
(little-endian), their value is `limbsVal b l`.

* `Desc.Sat b D x`: `x : ℕ → ℕ` satisfies all patterns, comparisons and chains;
* `Desc.countB b B D`: the number of `x ∈ [0, B)^{nV}` satisfying `D` (the network counts this with
  `b = Params.b n`, `B = 2^{Params.nB n}`; the bridge abbreviation is `Desc.count n D`);
* `Desc.WFB b ℓ nB D`: well-formedness (indices in range, constants of `≤ ℓ` limbs `< 2^b`, patterns
  of length `≤ nB`, coefficient sums `≤ 32` per side, each product in at most one chain);
* `Desc.chainOf D p`: the chain that contains product `p` (`chainOf_eq`).

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Bitwise
import EthFollowup.ModP.Compare

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-! ## Syntax -/

/-- An operand: a variable or a constant (its `b`-bit limbs, little-endian). -/
inductive Operand where
  | var (v : ℕ)
  | const (limbs : List ℕ)
  deriving DecidableEq, Inhabited, Repr

/-- A product `x_u · w` (`w = x_u` allowed). -/
structure ProdD where
  u : ℕ
  w : Operand
  deriving DecidableEq, Inhabited, Repr

/-- The source of a chain term: product `p`, variable `v`, or a constant. -/
inductive Src where
  | prod (p : ℕ)
  | lin (v : ℕ)
  | const (limbs : List ℕ)
  deriving DecidableEq, Inhabited, Repr

/-- A chain term `coeff · value(src)`. -/
structure Term where
  coeff : ℕ
  src : Src
  deriving DecidableEq, Inhabited, Repr

/-- A linear chain `Σ_lhs coeff·value = Σ_rhs coeff·value`. -/
structure ChainD where
  lhs : List Term
  rhs : List Term
  deriving DecidableEq, Inhabited, Repr

instance : Inhabited CmpRel := ⟨.eq⟩

/-- A comparison `x_v ⋈ rhs`. -/
structure CmpD where
  v : ℕ
  rhs : Operand
  rel : CmpRel
  deriving DecidableEq, Inhabited, Repr

/-- **A description**: `nV` variables, a bit pattern per variable (`pat[v]`, missing = none),
products, chains and comparisons. -/
structure Desc where
  nV : ℕ
  pat : List (List (Option Bool))
  prods : List ProdD
  chains : List ChainD
  cmps : List CmpD
  deriving DecidableEq, Inhabited, Repr

/-! ## Semantics -/

/-- The value of the limbs `l` (`b`-bit, little-endian). -/
def limbsVal (b : ℕ) (l : List ℕ) : ℕ := ∑ i ∈ range l.length, l.getD i 0 * 2 ^ (b * i)

/-- The value of an operand. -/
def Operand.eval (b : ℕ) (x : ℕ → ℕ) : Operand → ℕ
  | .var v => x v
  | .const l => limbsVal b l

/-- The value of a product. -/
def ProdD.eval (b : ℕ) (x : ℕ → ℕ) (pd : ProdD) : ℕ := x pd.u * pd.w.eval b x

/-- The value of a term source (products looked up in `prods`). -/
def Src.eval (b : ℕ) (prods : List ProdD) (x : ℕ → ℕ) : Src → ℕ
  | .prod p => (prods.getD p default).eval b x
  | .lin v => x v
  | .const l => limbsVal b l

/-- The value `Σ coeff · value` of one side of a chain. -/
def sideVal (b : ℕ) (prods : List ProdD) (x : ℕ → ℕ) (ts : List Term) : ℕ :=
  (ts.map fun t => t.coeff * t.src.eval b prods x).sum

/-- One pattern position: `none` = free, `some v` = the bit is `v`. -/
def optBit : Option Bool → Bool → Bool
  | none, _ => true
  | some v, x => x == v

/-- `y` matches the bit pattern `pt` (position `j` = bit `j`, little-endian). -/
def patMatch (pt : List (Option Bool)) (y : ℕ) : Prop :=
  ∀ j < pt.length, optBit (pt.getD j none) (y.testBit j) = true

instance instDecPatMatch (pt : List (Option Bool)) (y : ℕ) : Decidable (patMatch pt y) := by
  unfold patMatch; infer_instance

/-- **`x` satisfies the description**: patterns, comparisons, chains. -/
def Desc.Sat (b : ℕ) (D : Desc) (x : ℕ → ℕ) : Prop :=
  (∀ v < D.nV, patMatch (D.pat.getD v []) (x v)) ∧
  (∀ q ∈ D.cmps, q.rel.Holds (x q.v) (q.rhs.eval b x)) ∧
  (∀ ch ∈ D.chains, sideVal b D.prods x ch.lhs = sideVal b D.prods x ch.rhs)

instance instDecDescSat (b : ℕ) (D : Desc) (x : ℕ → ℕ) : Decidable (D.Sat b x) := by
  unfold Desc.Sat; infer_instance

/-- A tuple `Fin nV → ℕ` as a function `ℕ → ℕ` (`0` beyond `nV`). -/
def extV (nV : ℕ) (x : Fin nV → ℕ) : ℕ → ℕ := fun v => if h : v < nV then x ⟨v, h⟩ else 0

/-- **The count of a description**: `#{x ∈ [0, B)^{nV} : x satisfies D}`. -/
def Desc.countB (b B : ℕ) (D : Desc) : ℕ :=
  ((Fintype.piFinset fun _ : Fin D.nV => range B).filter fun x => D.Sat b (extV D.nV x)).card

/-! ## Well-formedness -/

/-- An operand is in range: variable `< nV`, constant of `≤ ℓ` limbs `< 2^b`. -/
def Operand.OK (b ℓ nV : ℕ) : Operand → Prop
  | .var v => v < nV
  | .const l => l.length ≤ ℓ ∧ ∀ y ∈ l, y < 2 ^ b

/-- A term source is in range. -/
def Src.OK (b ℓ nV nP : ℕ) : Src → Prop
  | .prod p => p < nP
  | .lin v => v < nV
  | .const l => l.length ≤ ℓ ∧ ∀ y ∈ l, y < 2 ^ b

/-- Chain `ch` uses product `p`. -/
def ChainD.HasProd (ch : ChainD) (p : ℕ) : Prop := ∃ t ∈ ch.lhs ++ ch.rhs, t.src = .prod p

instance instDecHasProd (ch : ChainD) (p : ℕ) : Decidable (ch.HasProd p) := by unfold ChainD.HasProd; infer_instance

/-- **Well-formedness** (limb width `b`, `ℓ` limbs, box `2^{nB}`). -/
structure Desc.WFB (b ℓ nB : ℕ) (D : Desc) : Prop where
  pat_len : ∀ pt ∈ D.pat, pt.length ≤ nB
  prod_ok : ∀ pd ∈ D.prods, pd.u < D.nV ∧ pd.w.OK b ℓ D.nV
  term_ok : ∀ ch ∈ D.chains, ∀ t ∈ ch.lhs ++ ch.rhs, t.src.OK b ℓ D.nV D.prods.length
  coeff_le : ∀ ch ∈ D.chains, (ch.lhs.map Term.coeff).sum ≤ 32 ∧ (ch.rhs.map Term.coeff).sum ≤ 32
  prod_once : ∀ c < D.chains.length, ∀ c' < D.chains.length, ∀ p : ℕ,
    (D.chains.getD c default).HasProd p → (D.chains.getD c' default).HasProd p → c = c'
  cmp_ok : ∀ q ∈ D.cmps, q.v < D.nV ∧ q.rhs.OK b ℓ D.nV

/-- The chain containing product `p` (`D.chains.length` if none). -/
def Desc.chainOf (D : Desc) (p : ℕ) : ℕ := D.chains.findIdx fun ch => decide (ch.HasProd p)

theorem Desc.chainOf_le (D : Desc) (p : ℕ) : D.chainOf p ≤ D.chains.length :=
  List.findIdx_le_length

/-- If chain `c` uses `p`, then `chainOf p ≤ c` and chain `chainOf p` uses `p`. -/
theorem Desc.chainOf_spec {D : Desc} {p c : ℕ} (hc : c < D.chains.length)
    (h : (D.chains.getD c default).HasProd p) :
    D.chainOf p ≤ c ∧ (D.chains.getD (D.chainOf p) default).HasProd p := by
  have hc' : (D.chains[c]'hc).HasProd p := by
    rwa [List.getD_eq_getElem _ _ hc] at h
  have hlt : D.chainOf p < D.chains.length :=
    List.findIdx_lt_length_of_exists ⟨_, List.getElem_mem hc, by simpa using hc'⟩
  refine ⟨?_, ?_⟩
  · by_contra hn
    have := List.not_of_lt_findIdx (p := fun ch => decide (ch.HasProd p)) (xs := D.chains)
      (i := c) (by unfold Desc.chainOf at hn; omega)
    simp [hc'] at this
  · have := List.findIdx_getElem (w := hlt)
    rw [List.getD_eq_getElem _ _ hlt]
    exact of_decide_eq_true this

/-- Under well-formedness, the chain using `p` is `chainOf p`. -/
theorem Desc.chainOf_eq {b ℓ nB : ℕ} {D : Desc} (hD : D.WFB b ℓ nB) {p c : ℕ}
    (hc : c < D.chains.length) (h : (D.chains.getD c default).HasProd p) : D.chainOf p = c := by
  obtain ⟨h1, h2⟩ := D.chainOf_spec hc h
  exact hD.prod_once _ (lt_of_le_of_lt h1 hc) _ hc p h2 h

end EthFollowup.ModP
