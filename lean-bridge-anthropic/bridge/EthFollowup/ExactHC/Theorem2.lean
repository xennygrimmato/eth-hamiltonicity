/-
# Theorem 2 (sharp rate) at Turing-machine level, from a uniform HC network package

`research/lean-blueprint.md`, module C2 (Theorem 2); §6.4 of `research/exact-hc-theorem.md`;
route of `research/anthropic-api.md` §4.3.

**The hypothesis: uniformity in `g`.** Assembly.lean (Theorem 1) takes one `HCPackage g c₀` per
number `g` of nodes; there `g` is a constant (it depends on δ, D only), so a context type,
procedures and a polynomial `q` that depend on `g` are harmless. For Theorem 2, `g = 3K⁸` grows with
`n`, and ONE machine must serve all `n`; a family of per-`g` packages (with a different context
type, different procedures and a `q` depending on `g`) cannot be assembled into one machine. The
hypothesis here is therefore `T2.UPackage c₀`: ONE context type, ONE set of procedures `Np`
(`Procs.Keeps`, P and B unary), ONE polynomial-time reader `prep : (g in unary, code G) ↦ context`,
ONE absolute constant `q`, and for every `g ≥ 1` and every graph with `n ≥ 3`, minimum degree `≥ 2`:
`IsNetwork Np (prep (unary g, code G)) (net g G) P B τ S` of value `n·#HC(G)` with
`gμ ≤ 2m + gΔ`, `U ≤ c₀(m+n) + q g³`, `P ≤ c₀μ + q g²`, `B ≤ q(n+g+2)^q`,
`τ ≤ 2^{c₀μ}·q(n+g+2)^q`, `S + size(prep …) ≤ q(n+g+2)^q`.
`ULabelPackage c₀` is the same in label-sharing form (the hypotheses of `labelProcs_given` and
`net_is`, uniform in `g`); `ULabelPackage.toUPackage` converts. The HC network of M7 meets these
shapes (`P = 3μ + g² + 1`, `B = 2μ + 1`, `U ≤ 2(3m + g³)`), provided the C3 reader takes `g` as
input.

**The machine** (`T2.hcM2`, one `Stepped (List Bool) (List Bool)` with `IsPolyT`): read `code G`;
`K := K_ℓ` for the largest level with `K_ℓ ≤ max(⌊n^{1/30}⌋, K₀)` (`pickOf` on `levelsUnder x₀`),
`g := 3K⁸`; for every branch `y` of Lemma 6.1 with `Θ = n/g + 2` (Assembly's `brGraph`): `0` if the
branch graph is bad, else Lemma 8 case (i) (`ExplicitCost.groupingData`, `ζ = 1/(2K)`) with the
clique machine `E = cliqueMachine (c+2) x₀ Alg` of `CountedRoute.onTheCountedRecursion` (Theorem A(b)
on the pieces of Theorem B) and the network queries answered by `Np` (`QueryMachine.plug`,
`stPlug`); add up, divide by `n`, write `Nat.bits`.

**Main results.**
* `T2.net_runs`: one network, Lemma 8 + Theorem A(b) + procedures, in counted steps;
* `T2.branch_bound`: one branch costs `≤ 2^{A(m+n+2)/√log₂(n+2)}` steps and state size (the analysis
  of (6.2): the leading term `e_ℓ U` with `e_ℓ√log₂(n+2) ≤ (3x₀+6)(30C₀+1)`; all other terms
  `K^j` (`j ≤ 29`), `(m+n)/K`, `K²log n`, `log n` are `O((m+n)/√log n)` since
  `K³⁰ ≤ K₀³⁰(n+2)` and `n + 2 ≤ K^{30C₀+1}`);
* `T2.hcM2_runs`: the whole machine, `≤ 2^{A(m+n+2)/√log₂(n+2)}` steps and state size;
* `theorem2_TM`: from `∃ c₀, Nonempty (UPackage c₀)`, ONE Mathlib `TM2ComputableAux` machine with
  finite alphabets and ONE `C` with `Outputs M (code G) (Nat.bits #HC(G))
  ⌊C·2^{C(m+n)/√(log₂(n+2))}⌋` for EVERY graph `G`; `theorem2_TM_max`: the same with `max(m,n)`;
  `theorem2_TM_of_label`: from `ULabelPackage`.

Standard axioms only.
-/
import EthFollowup.ExactHC.Assembly
import ExplicitCost.GroupingLemma
import ExplicitCost.GroupingPoly
import CountedRoute.Main
import CountedToPadded.Pick
import CountedRecursion.PolyQueries
import CountKSat.Host

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace T2

open Groundwork Groundwork.Prog GraphProblems Asm

/-! ## Polynomial-time steps with a number of nodes that depends on the input -/

section PolyG

variable {α : Type} [Enc α]

@[fun_prop] theorem thetaW_polyT' {g : α → ℕ} {a : α → GIn} (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => thetaW (g x) (a x) := by
  unfold thetaW; fun_prop

@[fun_prop] theorem highW_polyT' {g : α → ℕ} {a : α → GIn} {v : α → ℕ} (hg : PolyT g) (ha : PolyT a)
    (hv : PolyT v) : PolyT fun x => highW (g x) (a x) (v x) := by
  have := thetaW_polyT' hg ha
  unfold highW; fun_prop

@[fun_prop] theorem hlist_polyT' {g : α → ℕ} {a : α → GIn} (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => hlist (g x) (a x) := by
  have := range_polyT ha; unfold hlist; fun_prop

theorem digitW_polyT' {g : α → ℕ} {a : α → GIn} {y v : α → ℕ} (hg : PolyT g) (ha : PolyT a)
    (hy : PolyT y) (hv : PolyT v) : PolyT fun x => digitW (g x) (a x) (y x) (v x) := by
  have := hlist_polyT' hg ha
  unfold digitW; fun_prop

@[fun_prop] theorem pickW_polyT' {g : α → ℕ} {a : α → GIn} {y v w : α → ℕ} (hg : PolyT g)
    (ha : PolyT a) (hy : PolyT y) (hv : PolyT v) (hw : PolyT w) :
    PolyT fun x => pickW (g x) (a x) (y x) (v x) (w x) :=
  pickD_polyT ha hv (digitW_polyT' hg ha hy hv) hw

@[fun_prop] theorem entryW_polyT' {g : α → ℕ} {a : α → GIn} {y u w : α → ℕ} (hg : PolyT g)
    (ha : PolyT a) (hy : PolyT y) (hu : PolyT u) (hw : PolyT w) :
    PolyT fun x => entryW (g x) (a x) (y x) (u x) (w x) := by
  unfold entryW keepW
  exact PolyT.and' (adjW_polyT ha hu hw) (PolyT.and'
    (PolyT.or' (PolyT.not' (highW_polyT' hg ha hu)) (pickW_polyT' hg ha hy hu hw))
    (PolyT.or' (PolyT.not' (highW_polyT' hg ha hw)) (pickW_polyT' hg ha hy hw hu)))

theorem brWord_polyT' {g : GIn × ℕ → ℕ} (hg : PolyT g) : PolyT fun p => brWord (g p) p := by
  have h1 := range_polyT (α := GIn × ℕ) (a := fun p => p.1) (by fun_prop)
  have h2 := range_polyT (α := (GIn × ℕ) × ℕ) (a := fun p => p.1.1) (by fun_prop)
  have h3 : PolyT fun p : GIn × ℕ => GraphProblems.unary p.1.1.length := by
    have : PolyT fun p : GIn × ℕ => p.1.1.map (fun _ => true) ++ [false] := by fun_prop
    refine this.congr fun p => ?_
    simp [GraphProblems.unary, List.map_const']
  unfold brWord brMatrix; fun_prop

theorem badW_polyT' {g : GIn × ℕ → ℕ} (hg : PolyT g) : PolyT fun p => badW (g p) p := by
  have h1 := range_polyT (α := GIn × ℕ) (a := fun p => p.1) (by fun_prop)
  have h2 := range_polyT (α := (GIn × ℕ) × ℕ) (a := fun p => p.1.1) (by fun_prop)
  unfold badW; fun_prop

theorem nBr_polyT' {g : GIn → ℕ} (hg : PolyT g) : PolyT fun a => nBr (g a) a := by
  unfold nBr
  exact PolyT.pow_unary (by fun_prop) (Unary.of_length (hlist_polyT' hg PolyT.id'))

end PolyG

/-! ## The level: `K = K_ℓ` for the largest `ℓ` with `K_ℓ ≤ max(⌊n^{1/30}⌋, K₀)` -/

section Level

open QueryMachines.Bridge CliqueLevels

/-- `⌊n^{1/30}⌋`. -/
def rootN (n : ℕ) : ℕ := ((List.range n).filter fun r => decide ((r + 1) ^ 30 ≤ n)).length

theorem length_filter_range_lt (p : ℕ → Bool) (t : ℕ) (hp : ∀ r, p r = true ↔ r < t) :
    ∀ k, ((List.range k).filter p).length = min k t
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range_lt p t hp k]
    by_cases h : k < t
    · have : p k = true := (hp k).2 h
      simp [List.filter_cons, this]; omega
    · have : p k = false := by
        cases hk : p k
        · rfl
        · exact absurd ((hp k).1 hk) h
      simp [List.filter_cons, this]; omega

theorem rootN_spec (n : ℕ) : rootN n ^ 30 ≤ n ∧ n < (rootN n + 1) ^ 30 := by
  have hn1 : n < (n + 1) ^ 30 :=
    calc n < n + 1 := Nat.lt_succ_self n
      _ = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ 30 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hex : ∃ r, n < (r + 1) ^ 30 := ⟨n, hn1⟩
  classical
  set t := Nat.find hex with ht
  have hiff : ∀ r, (r + 1) ^ 30 ≤ n ↔ r < t := fun r => by
    rw [ht, Nat.lt_find_iff]
    constructor
    · intro h m hm
      have : (m + 1) ^ 30 ≤ (r + 1) ^ 30 := Nat.pow_le_pow_left (by omega) _
      omega
    · intro h; have := h r le_rfl; omega
  have htn : t ≤ n := Nat.find_min' hex hn1
  have hr : rootN n = t := by
    unfold rootN
    rw [length_filter_range_lt _ t (fun r => by rw [decide_eq_true_iff]; exact hiff r) n]
    omega
  rw [hr]
  refine ⟨?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]; simp
  · have := (hiff (t - 1)).2 (by omega)
    rwa [Nat.sub_add_cancel hpos] at this

/-- The bound handed to the program that picks the level: `max(⌊n^{1/30}⌋, K₀)` in unary. -/
def bndL (K₀ : ℕ) (a : GIn) : List Unit := List.replicate (max (rootN a.1.length) K₀) ()

theorem rootL_polyT : PolyT fun a : GIn => (List.range a.1.length).filter fun r => decide ((r + 1) ^ 30 ≤ a.1.length) := by
  have hr : PolyT fun a : GIn => List.range a.1.length := range_polyT (α := GIn) (a := fun a => a) PolyT.id'
  have h1 : PolyT fun p : GIn × ℕ => p.2 + 1 := PolyT.add PolyT.id'.snd (PolyT.const 1)
  have h2 : PolyT fun p : GIn × ℕ => (p.2 + 1) ^ 30 := PolyT.pow_const h1 30
  have h3 : PolyT fun p : GIn × ℕ => p.1.1.length := PolyT.length PolyT.id'.fst.fst
  have hf : PolyT fun p : GIn × ℕ => decide ((p.2 + 1) ^ 30 ≤ p.1.1.length) := PolyT.decide_le h2 h3
  have := PolyT.filter (f := fun (a : GIn) (r : ℕ) => decide ((r + 1) ^ 30 ≤ a.1.length)) hf hr
  exact this

theorem rootN_unary : Unary fun a : GIn => rootN a.1.length := Unary.of_length rootL_polyT

theorem rootN_polyT : PolyT fun a : GIn => rootN a.1.length := PolyT.length rootL_polyT

theorem bndL_polyT (K₀ : ℕ) : PolyT (bndL K₀) := by
  have h2 : Unary fun a : GIn => max (rootN a.1.length) K₀ :=
    Unary.of_le (rootN_unary.add (Unary.const K₀)) (PolyT.max' rootN_polyT (PolyT.const K₀))
      fun a => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  unfold bndL
  exact h2

variable (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- `(ℓ, (ℓ, K_ℓ))` in unary for the largest level `ℓ` with `K_ℓ ≤ max(⌊n^{1/30}⌋, K₀)`. -/
def pickL (a : GIn) : List Unit × (List Unit × List Unit) := pickOf kf K₀ (bndL K₀ a)
/-- The number `K` of groups. -/
def kN (a : GIn) : ℕ := (pickL kf K₀ a).2.2.length
/-- The number `g = 3K⁸` of nodes. -/
def gN (a : GIn) : ℕ := 3 * kN kf K₀ a ^ 8

/-- What the clique machine is handed: `(ℓ, λ, B)` for `(K_ℓ, λ, B)`. -/
def argF (x : ExplicitCost.CliqueInput) : ExplicitCost.Head := ((pickOf kf K₀ x.1).1, x.2.1, x.2.2)

section Facts

variable {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : Levels Kf e C₀) (hk : ComputesLevels Kf kf)
include hL hk

theorem pickOf_polyT : PolyT (pickOf kf (Kf 0)) := (pickOfFacts Kf e C₀ kf hL hk).1

theorem kN_polyT : PolyT (kN kf (Kf 0)) := by
  have := pickOf_polyT kf hL hk
  have := bndL_polyT (Kf 0)
  unfold kN pickL; fun_prop

theorem kN_unary : Unary (kN kf (Kf 0)) := by
  have := pickOf_polyT kf hL hk
  have := bndL_polyT (Kf 0)
  unfold kN pickL; exact Unary.of_length (by fun_prop)

theorem gN_unary : Unary (gN kf (Kf 0)) := by
  have h := kN_unary kf hL hk
  have h2 := h.mul h
  have h4 := h2.mul h2
  have h8 := h4.mul h4
  have e : gN kf (Kf 0) = fun a => 3 * (kN kf (Kf 0) a * kN kf (Kf 0) a * (kN kf (Kf 0) a * kN kf (Kf 0) a) *
      (kN kf (Kf 0) a * kN kf (Kf 0) a * (kN kf (Kf 0) a * kN kf (Kf 0) a))) := by
    funext a; simp only [gN]; ring
  rw [e]
  exact (Unary.const 3).mul h8

theorem gN_polyT : PolyT (gN kf (Kf 0)) := (gN_unary kf hL hk).poly

theorem argF_polyT : PolyT (argF kf (Kf 0)) := by
  have := pickOf_polyT kf hL hk
  unfold argF; fun_prop

/-- The level picked: `K = K_ℓ ≤ max(⌊n^{1/30}⌋, K₀)` and `⌊n^{1/30}⌋ < K_{ℓ+1}`. -/
theorem kN_spec (a : GIn) : ∃ l, kN kf (Kf 0) a = Kf l ∧ Kf l ≤ max (rootN a.1.length) (Kf 0) ∧
    rootN a.1.length < Kf (l + 1) := by
  obtain ⟨h1, h2, h3⟩ := (pickOfFacts Kf e C₀ kf hL hk).2 (bndL (Kf 0) a)
  have hb : (bndL (Kf 0) a).length = max (rootN a.1.length) (Kf 0) := List.length_replicate
  refine ⟨(pickOf kf (Kf 0) (bndL (Kf 0) a)).1.length, ?_, ?_, ?_⟩
  · unfold kN pickL; rw [h1]; exact List.length_replicate
  · rw [← hb]; exact h2 (by rw [hb]; exact le_max_right _ _)
  · rw [hb] at h3; exact lt_of_le_of_lt (le_max_left _ _) h3

theorem argF_eq (l lam B : ℕ) :
    argF kf (Kf 0) (Printed.unary (Kf l), Printed.unary lam, Printed.unary B) =
      (Printed.unary l, Printed.unary lam, Printed.unary B) := by
  have hmono : StrictMono Kf := strictMono_nat_of_lt_succ hL.K_lt
  obtain ⟨h1, h2, h3⟩ := (pickOfFacts Kf e C₀ kf hL hk).2 (Printed.unary (Kf l))
  set l' := (pickOf kf (Kf 0) (Printed.unary (Kf l))).1.length with hl'
  have hlen : (Printed.unary (Kf l)).length = Kf l := List.length_replicate
  rw [hlen] at h2 h3
  have e1 : l' ≤ l := hmono.le_iff_le.1 (h2 (hmono.monotone (Nat.zero_le l)))
  have e2 : l < l' + 1 := hmono.lt_iff_lt.1 h3
  have e3 : l' = l := by omega
  simp only [argF]
  congr 1
  rw [Proof.eq_unary (pickOf kf (Kf 0) (Printed.unary (Kf l))).1, ← hl', e3]

end Facts

end Level

/-! ## The package, uniform in the number of nodes -/

open Eight.SecNetworks Printed Finset EthFollowup.Hamiltonian QueryMachines

/-- **An HC network package that is uniform in the number `g` of nodes**, with the absolute
constant `c₀`. Compared with `HCPackage g c₀` (one package per `g`), here ONE context type, ONE set
of procedures `Np` and ONE polynomial-time reader `prep` serve every `g`; the reader is handed `g`
in unary besides the graph code, and the constant `q` is absolute (the bounds are polynomial in
`n + g`, and the `g`-dependent terms of `U` and `P` are `q g³` and `q g²`).

This is what Theorem 2 needs: there `g = 3K⁸` grows with `n`, and the machine must be one machine
for all `n`, so neither the procedures nor the polynomial `q` may depend on `g`. -/
structure UPackage (c₀ : ℕ) : Type 1 where
  Ctx : Type
  [encCtx : Enc Ctx]
  [sizeCtx : HasSize Ctx]
  [carriedCtx : Carried Ctx]
  Np : Procs Ctx
  keeps : Np.Keeps
  P_unary : Unary Np.P
  B_unary : Unary Np.B
  /-- The reader: `(g in unary, code G) ↦ context`. -/
  prep : List Unit × List Bool → Ctx
  prep_poly : PolyT prep
  q : ℕ
  net : ∀ (g : ℕ) {n : ℕ}, SimpleGraph (Fin n) → Net g
  P : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  B : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  τ : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  S : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  mu : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  isNet : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) →
    IsNetwork Np (prep (Printed.unary g, code G)) (net g G) (P g G) (B g G) (τ g G) (S g G)
  value : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (net g G).value = (n : ℤ) * ((hamCycles G).card : ℤ)
  mu_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) → g * mu g G ≤ 2 * G.edgeFinset.card + g * Δ
  U_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (net g G).U ≤ c₀ * (G.edgeFinset.card + n) + q * g ^ 3
  P_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → P g G ≤ c₀ * mu g G + q * g ^ 2
  B_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → B g G ≤ q * (n + g + 2) ^ q
  τ_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → τ g G ≤ 2 ^ (c₀ * mu g G) * (q * (n + g + 2) ^ q)
  S_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → S g G + size (prep (Printed.unary g, code G)) ≤ q * (n + g + 2) ^ q

attribute [instance] UPackage.encCtx UPackage.sizeCtx UPackage.carriedCtx

/-! ## One network: Lemma 8 (case (i)) with the clique machine, the queries answered by the
procedures -/

/-- Queries of Definition 2(iii), priced `τ`, answered by procedures that take `≤ τ` steps: three
times the cost (`stPlug`, as in `Printed.stOnProcedures`). -/
theorem plug_within {X C : Type} [HasSize C] (M : QueryMachine NetQuery ℤ X ℤ) {Np : Procs C} {c : C}
    {g : ℕ} {N : Net g} {P B τ S : ℕ} (hN : IsNetwork Np c N P B τ S) {x : X} {T S₀ : ℕ} {v : ℤ}
    (h : M.Within (netOracle N) (fun _ => τ) x T S₀ v) :
    (M.plug (answerOf Np)).Runs (c, x) (3 * T) (size c + S₀ + (S + 3) + 1) v := by
  obtain ⟨own, L, hrun, hle⟩ := h
  have hp := stPlug _ _ _ _ _ M (answerOf Np) (netOracle N) c x own S₀ (S + 3) L v (fun _ => τ) hrun
    fun y _ w hw => answerOf_runs hN.given hw
  rw [QueryMachine.sum_map_const] at hle hp
  refine hp.mono ?_ le_rfl
  have := hN.τ_pos
  nlinarith

/-- The body of Lemma 8 (`ExplicitCost.GroupingExplicit`) for the constant `C₁`. -/
def GEBody (C₁ : ℕ) : Prop := ∀ (α : Type) (E : QueryMachine TableQuery ℤ α ℤ) (arg : ExplicitCost.CliqueInput → α) (a b K g : ℕ) (N : Net g) (P B τ 𝒯 SE : ℕ),
  2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → 1 ≤ τ → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  ExplicitCost.SolvesCliques E (arg (unary K, unary (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U), unary (AppRunningTime.B'of K g P B))) K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (AppRunningTime.B'of K g P B) 𝒯 SE →
    ∃ T : ℕ, (ExplicitCost.groupingData E arg).Within (netOracle N) (fun _ => τ) (ExplicitCost.groupingInput a b K N P B) T (SE + (g * (P + B) + size (a, b)) ^ C₁) N.value ∧
      (T : ℝ) ≤ ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (2 * (g : ℝ) * P / K) * τ) * ((g : ℝ) * (P + B)) ^ C₁

theorem geBody : ∃ C₁, GEBody C₁ := ExplicitCost.groupingExplicit

variable {c₀ : ℕ} (pk : UPackage c₀)

/-- The input of Lemma 8 (ζ = 1/(2K), K, g = 3K⁸, Definition 2(iii)) written from the context. -/
def ginF (c : pk.Ctx) (k : ℕ) : ExplicitCost.GroupingInput :=
  ((1, 2 * k), ((unary k, unary (3 * k ^ 8)),
    inputOf (3 * k ^ 8) (pk.Np.P c) (pk.Np.B c) (pk.Np.len c) (pk.Np.cap c)))

/-- Lemma 8's procedure with the clique machine `E`, its queries answered by the procedures. -/
def GM {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : ExplicitCost.CliqueInput → α) :
    Stepped (pk.Ctx × ExplicitCost.GroupingInput) ℤ :=
  (ExplicitCost.groupingData E arg).plug (answerOf pk.Np)

/-- `L` and `B'` of Lemma 8, case (i). -/
noncomputable def Lc (K g P U : ℕ) : ℕ := AppRunningTime.Lof K g ((1 : ℕ) / ((2 * K : ℕ) : ℝ)) P U
def Bc (K g P B : ℕ) : ℕ := AppRunningTime.B'of K g P B
/-- The clique bound of Theorem A(b), cut to a natural number. -/
noncomputable def Tc (e : ℝ) (K C₀ L B' : ℕ) : ℕ := ⌊CliqueLevels.bound e K C₀ L B'⌋₊

/-- **One network.** -/
theorem net_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {kf : List Unit × List Unit → Option (List Unit)}
    {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀) (l : ℕ) {N : Net (3 * Kf l ^ 8)} {c : pk.Ctx}
    {P B τ S : ℕ} (hN : IsNetwork pk.Np c N P B τ S) :
    ∃ T : ℕ, (GM pk E (argF kf (Kf 0))).Runs (c, ginF pk c (Kf l)) (3 * T)
        (size c + (Tc (e l) (Kf l) C₀ (Lc (Kf l) (3 * Kf l ^ 8) P N.U) (Bc (Kf l) (3 * Kf l ^ 8) P B) +
          (3 * Kf l ^ 8 * (P + B) + size (1, 2 * Kf l)) ^ C₁) + (S + 3) + 1) N.value ∧
      (T : ℝ) ≤ ((Kf l : ℝ) ^ (3 * Kf l ^ 8) + Tc (e l) (Kf l) C₀ (Lc (Kf l) (3 * Kf l ^ 8) P N.U)
          (Bc (Kf l) (3 * Kf l ^ 8) P B) * (2 : ℝ) ^ (2 * ((3 * Kf l ^ 8 : ℕ) : ℝ) * P / Kf l) * τ) *
        (((3 * Kf l ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁ := by
  have hK2 : 2 ≤ Kf l := hL.K_two l
  have hg2 : 2 ≤ 3 * Kf l ^ 8 := by
    have : 1 ≤ Kf l ^ 8 := Nat.one_le_pow _ _ (by omega)
    omega
  have hP1 := hN.is.P_pos
  have hB1 := hN.is.B_pos
  have hζ : ((1 : ℕ) : ℝ) / ((2 * Kf l : ℕ) : ℝ) = 1 / (2 * Kf l) := by push_cast; ring
  have hcases : AppRunningTime.Cases (Kf l) (3 * Kf l ^ 8) (((1 : ℕ) : ℝ) / ((2 * Kf l : ℕ) : ℝ)) P N.c :=
    Or.inl ⟨rfl, hζ⟩
  have hL1 : 1 ≤ Lc (Kf l) (3 * Kf l ^ 8) P N.U := by
    rw [Lc, AppRunningTime.Lof, Nat.one_le_ceil_iff]
    have hK0 : (0 : ℝ) < Kf l := by exact_mod_cast (by omega : 0 < Kf l)
    have : (0 : ℝ) < (2 : ℝ) * (((1 : ℕ) : ℝ) / ((2 * Kf l : ℕ) : ℝ)) * ((3 * Kf l ^ 8 : ℕ) : ℝ) * P := by
      have : (0 : ℝ) < ((3 * Kf l ^ 8 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 3 * Kf l ^ 8)
      have : (0 : ℝ) < P := by exact_mod_cast hP1
      rw [hζ]; positivity
    have : (0 : ℝ) ≤ N.U := by positivity
    positivity
  have hB'1 : 1 ≤ Bc (Kf l) (3 * Kf l ^ 8) P B := by
    rw [Bc, AppRunningTime.B'of]
    have : 1 ≤ (3 * Kf l ^ 8) ^ 2 * B := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact this.trans (Nat.le_add_left _ _)
  have hsc : ExplicitCost.SolvesCliques E (argF kf (Kf 0) (unary (Kf l),
      unary (Lc (Kf l) (3 * Kf l ^ 8) P N.U), unary (Bc (Kf l) (3 * Kf l ^ 8) P B))) (Kf l)
      (Lc (Kf l) (3 * Kf l ^ 8) P N.U) (Bc (Kf l) (3 * Kf l ^ 8) P B)
      (Tc (e l) (Kf l) C₀ (Lc (Kf l) (3 * Kf l ^ 8) P N.U) (Bc (Kf l) (3 * Kf l ^ 8) P B))
      (Tc (e l) (Kf l) C₀ (Lc (Kf l) (3 * Kf l ^ 8) P N.U) (Bc (Kf l) (3 * Kf l ^ 8) P B)) := by
    intro W hW
    obtain ⟨T, S', hw, hT, hS⟩ := hsol l _ _ W hL1 hB'1 hW
    rw [argF_eq kf hL hk]
    exact hw.mono (Nat.le_floor hT) (Nat.le_floor hS)
  obtain ⟨T, hw, hT⟩ := hC₁ _ E (argF kf (Kf 0)) 1 (2 * Kf l) (Kf l) (3 * Kf l ^ 8) N P B τ _ _
    hK2 hg2 one_pos (by omega) hN.is hN.τ_pos hcases hsc
  have hin : ginF pk c (Kf l) = ExplicitCost.groupingInput 1 (2 * Kf l) (Kf l) N P B := by
    unfold ginF ExplicitCost.groupingInput ExplicitCost.dataInput
    rw [← hN.given.P_eq, ← hN.given.B_eq,
      inputOf_eq N (pk.Np.P c) (pk.Np.B c) _ _ hN.given.len_eq hN.given.cap_eq]
  refine ⟨T, ?_, hT⟩
  rw [hin]
  exact plug_within _ hN hw

theorem net_runs' {C₁ : ℕ} (hC₁ : GEBody C₁) {kf : List Unit × List Unit → Option (List Unit)}
    {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀) (l : ℕ) {K : ℕ} (hKl : K = Kf l) {N : Net (3 * K ^ 8)}
    {c : pk.Ctx} {P B τ S : ℕ} (hN : IsNetwork pk.Np c N P B τ S) {v : ℤ} (hv : N.value = v) :
    ∃ T : ℕ, (GM pk E (argF kf (Kf 0))).Runs (c, ginF pk c K) (3 * T)
        (size c + (Tc (e l) K C₀ (Lc K (3 * K ^ 8) P N.U) (Bc K (3 * K ^ 8) P B) +
          (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1) v ∧
      (T : ℝ) ≤ ((K : ℝ) ^ (3 * K ^ 8) + Tc (e l) K C₀ (Lc K (3 * K ^ 8) P N.U)
          (Bc K (3 * K ^ 8) P B) * (2 : ℝ) ^ (2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K) * τ) *
        (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁ := by
  subst hKl
  obtain ⟨T, h1, h2⟩ := net_runs pk hC₁ hL hk E hsol l hN
  exact ⟨T, hv ▸ h1, h2⟩

/-! ## The machine of Theorem 2 -/

section Machine

variable (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
  (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- The context of the branch `y`: the reader on `g` and the code of the branch graph. -/
def ctxF (p : GIn × ℕ) : pk.Ctx := pk.prep (unary (gN kf K₀ p.1), brWord (gN kf K₀ p.1) p)

/-- One branch: `0` if the branch graph has `n ≤ 2` or a vertex of degree `< 2`; otherwise Lemma 8
on its network, with the clique machine `E` and `K` groups. -/
def bodyM2 : Stepped (GIn × ℕ) ℤ :=
  Stepped.ite (fun p => badW (gN kf K₀ p.1) p) (Stepped.const 0)
    (Stepped.mapIn (fun p => (ctxF pk kf K₀ p, ginF pk (ctxF pk kf K₀ p) (kN kf K₀ p.1)))
      (GM pk E (argF kf K₀)))

/-- The sum over the branches of Lemma 6.1 (`Θ = n/g + 2`): `n · #HC(G)`. -/
def mainM2 : Stepped (List Bool) ℤ :=
  Stepped.mapIn read1 (Stepped.sumRange (fun a => nBr (gN kf K₀ a) a) (bodyM2 pk E kf K₀))

/-- **The machine of Theorem 2.** -/
def hcM2 : Stepped (List Bool) (List Bool) := Stepped.bind (mainM2 pk E kf K₀) (Stepped.ofFun finW)

variable {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem ctxF_polyT (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    PolyT (ctxF pk kf (Kf 0)) := by
  have hg : PolyT fun p : GIn × ℕ => gN kf (Kf 0) p.1 := (gN_polyT kf hL hk).comp PolyT.id'.fst
  have hu : PolyT fun p : GIn × ℕ => Printed.unary (gN kf (Kf 0) p.1) := (gN_unary kf hL hk).comp PolyT.id'.fst
  have hb := brWord_polyT' hg
  exact pk.prep_poly.comp (PolyT.prodMk hu hb)

theorem hcM2_poly (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf)
    (hE : E.PolyTimeSteps) : Nonempty (IsPolyT (hcM2 pk E kf (Kf 0))) := by
  have hc := ctxF_polyT pk kf hL hk
  have hgm : Nonempty (IsPolyT (GM pk E (argF kf (Kf 0)))) :=
    stPolyPlug _ _ _ _ _ _ _ (ExplicitCost.groupingPoly.2 _ E _ hE (argF_polyT kf hL hk))
      (answerOf_poly pk.Np pk.keeps.mem pk.keeps.W pk.keeps.Ψ pk.keeps.f)
  obtain ⟨i1⟩ := hgm
  have hkU : Unary fun p : GIn × ℕ => kN kf (Kf 0) p.1 := (kN_unary kf hL hk).comp PolyT.id'.fst
  have hgU : Unary fun p : GIn × ℕ => 3 * kN kf (Kf 0) p.1 ^ 8 := (gN_unary kf hL hk).comp PolyT.id'.fst
  have hin : PolyT fun p : GIn × ℕ => inputOf (3 * kN kf (Kf 0) p.1 ^ 8) (pk.Np.P (ctxF pk kf (Kf 0) p))
      (pk.Np.B (ctxF pk kf (Kf 0) p)) (pk.Np.len (ctxF pk kf (Kf 0) p)) (pk.Np.cap (ctxF pk kf (Kf 0) p)) :=
    ExplicitCost.inputOf_polyT_data hgU (pk.P_unary.comp hc) (pk.B_unary.comp hc)
      (pk.keeps.len.comp (h := fun q : (GIn × ℕ) × ℕ => (ctxF pk kf (Kf 0) q.1, q.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) PolyT.id'.snd))
      (pk.keeps.cap.comp (h := fun q : (GIn × ℕ) × ℕ × ℕ => (ctxF pk kf (Kf 0) q.1, q.2.1, q.2.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) (PolyT.prodMk PolyT.id'.snd.fst PolyT.id'.snd.snd)))
  have hg1 : PolyT fun p : GIn × ℕ => (ctxF pk kf (Kf 0) p, ginF pk (ctxF pk kf (Kf 0) p) (kN kf (Kf 0) p.1)) := by
    unfold ginF
    have h2k : PolyT fun p : GIn × ℕ => 2 * kN kf (Kf 0) p.1 := PolyT.mul (PolyT.const 2) hkU.poly
    exact PolyT.prodMk hc (PolyT.prodMk (PolyT.prodMk (PolyT.const 1) h2k)
      (PolyT.prodMk (PolyT.prodMk hkU hgU) hin))
  have : IsPolyT (Stepped.mapIn (fun p : GIn × ℕ => (ctxF pk kf (Kf 0) p,
      ginF pk (ctxF pk kf (Kf 0) p) (kN kf (Kf 0) p.1))) (GM pk E (argF kf (Kf 0)))) := IsPolyT.mapIn hg1
  have : IsPolyT (Stepped.const (0 : ℤ) : Stepped (GIn × ℕ) ℤ) := IsPolyT.const 0
  have hbad : PolyT fun p : GIn × ℕ => badW (gN kf (Kf 0) p.1) p :=
    badW_polyT' ((gN_polyT kf hL hk).comp PolyT.id'.fst)
  have : IsPolyT (bodyM2 pk E kf (Kf 0)) := IsPolyT.ite hbad
  have : IsPolyT (Stepped.sumRange (fun a => nBr (gN kf (Kf 0) a) a) (bodyM2 pk E kf (Kf 0))) :=
    IsPolyT.sumRange (nBr_polyT' (gN_polyT kf hL hk))
  have : IsPolyT (mainM2 pk E kf (Kf 0)) := IsPolyT.mapIn stCertRead.1
  have : IsPolyT (Stepped.ofFun finW) := IsPolyT.ofFun finW_polyT
  exact ⟨IsPolyT.bind⟩

end Machine

/-! ## The exponent: real-number facts -/

section Real

/-- `log₂ (n+2)`. -/
noncomputable def Lam (n : ℕ) : ℝ := Real.logb 2 ((n : ℝ) + 2)
/-- `√(log₂ (n+2))`. -/
noncomputable def sq (n : ℕ) : ℝ := Real.sqrt (Lam n)
/-- The exponent of Theorem 2: `A (m + n + 2) / √(log₂ (n+2))`. -/
noncomputable def Xp (A n m : ℕ) : ℝ := A * ((m : ℝ) + n + 2) / sq n

theorem one_le_Lam (n : ℕ) : 1 ≤ Lam n := by
  unfold Lam
  rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_one]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem one_le_sq (n : ℕ) : 1 ≤ sq n := by
  unfold sq
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (one_le_Lam n)

theorem sq_pos (n : ℕ) : 0 < sq n := lt_of_lt_of_le one_pos (one_le_sq n)

theorem sq_le_Lam (n : ℕ) : sq n ≤ Lam n := by
  have h := one_le_Lam n
  unfold sq
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

theorem sq_sq (n : ℕ) : sq n * sq n = Lam n := by
  unfold sq; exact Real.mul_self_sqrt (by linarith [one_le_Lam n])

theorem logb_nat_le (K : ℕ) (hK : 1 ≤ K) : Real.logb 2 K ≤ K := by
  have h : (K : ℝ) < 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have := Real.logb_lt_logb one_lt_two hK0 h
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
  exact this.le

/-- `log₂ (n+2) ≤ c₁ log₂ K` when `n + 2 ≤ K^{c₁}`. -/
theorem Lam_le_logb {n K c₁ : ℕ} (hK : 1 ≤ K) (h : n + 2 ≤ K ^ c₁) : Lam n ≤ c₁ * Real.logb 2 K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have h' : (n : ℝ) + 2 ≤ (K : ℝ) ^ c₁ := by exact_mod_cast h
  unfold Lam
  rw [← Real.logb_pow]
  exact Real.logb_le_logb_of_le one_lt_two (by positivity) h'

theorem Lam_le_K {n K c₁ : ℕ} (hK : 1 ≤ K) (h : n + 2 ≤ K ^ c₁) : Lam n ≤ c₁ * K := by
  have := Lam_le_logb hK h
  have := logb_nat_le K hK
  have : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg c₁
  nlinarith

theorem one_le_c₁ {n K c₁ : ℕ} (h : n + 2 ≤ K ^ c₁) : 1 ≤ c₁ := by
  rcases Nat.eq_zero_or_pos c₁ with h0 | h0
  · rw [h0, pow_zero] at h; omega
  · exact h0

theorem sq_le_K {n K c₁ : ℕ} (hK : 1 ≤ K) (h : n + 2 ≤ K ^ c₁) : sq n ≤ c₁ * K := by
  have h1 := Lam_le_K hK h
  have h2 := sq_sq n
  have h3 := one_le_sq n
  have hc : (1 : ℝ) ≤ c₁ := by exact_mod_cast one_le_c₁ h
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith

/-- `e · √(log₂ (n+2)) ≤ (3x₀+6) c₁` when `e ≤ (3x₀+6)/√(log₂ K)`. -/
theorem e_sq_le {n K c₁ : ℕ} {e a : ℝ} (hK : 2 ≤ K) (h : n + 2 ≤ K ^ c₁) (he0 : 0 ≤ e)
    (ha : 0 ≤ a) (he : e ≤ a / Real.sqrt (Real.logb 2 K)) : e * sq n ≤ a * c₁ := by
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  have hlg : 0 < Real.logb 2 K := Real.logb_pos one_lt_two hK1
  have hsl : 0 < Real.sqrt (Real.logb 2 K) := Real.sqrt_pos.2 hlg
  have hc : (1 : ℝ) ≤ c₁ := by exact_mod_cast one_le_c₁ h
  -- sq n ≤ c₁ √(log₂ K)
  have h1 : sq n ≤ c₁ * Real.sqrt (Real.logb 2 K) := by
    have e1 : sq n ≤ Real.sqrt (c₁ * Real.logb 2 K) := Real.sqrt_le_sqrt (Lam_le_logb (by omega) h)
    have e2 : Real.sqrt ((c₁ : ℝ) * Real.logb 2 K) = Real.sqrt c₁ * Real.sqrt (Real.logb 2 K) :=
      Real.sqrt_mul (by positivity) _
    have e3 : Real.sqrt (c₁ : ℝ) ≤ c₁ := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    calc sq n ≤ Real.sqrt c₁ * Real.sqrt (Real.logb 2 K) := e2 ▸ e1
      _ ≤ c₁ * Real.sqrt (Real.logb 2 K) := by gcongr
  have h2 : e * Real.sqrt (Real.logb 2 K) ≤ a := by rwa [le_div_iff₀ hsl] at he
  calc e * sq n ≤ e * (c₁ * Real.sqrt (Real.logb 2 K)) := by gcongr
    _ = c₁ * (e * Real.sqrt (Real.logb 2 K)) := by ring
    _ ≤ c₁ * a := by gcongr
    _ = a * c₁ := by ring

/-- `(n+2)^A = 2^{A log₂(n+2)}`. -/
theorem pow_eq_two_rpow (n A : ℕ) : ((n : ℝ) + 2) ^ A = (2 : ℝ) ^ (A * Lam n) := by
  rw [mul_comm, Real.rpow_mul (by norm_num), Lam, Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
    Real.rpow_natCast]

/-- A polynomial bound `x ≤ A (n+2)^A` gives `x ≤ 2^{2A log₂(n+2)}`. -/
theorem pol_le_two_rpow {A n x : ℕ} (h : Pol A n x) : (x : ℝ) ≤ (2 : ℝ) ^ (2 * A * Lam n) := by
  have h1 : (x : ℝ) ≤ A * ((n : ℝ) + 2) ^ A := by exact_mod_cast h
  have h2 : (A : ℝ) ≤ (2 : ℝ) ^ (A * Lam n) := by
    have e1 : (A : ℝ) ≤ (2 : ℝ) ^ (A : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast Nat.lt_two_pow_self.le
    have e2 : (A : ℝ) ≤ A * Lam n := le_mul_of_one_le_right (Nat.cast_nonneg A) (one_le_Lam n)
    exact e1.trans (Real.rpow_le_rpow_of_exponent_le one_le_two e2)
  rw [pow_eq_two_rpow] at h1
  calc (x : ℝ) ≤ (2 : ℝ) ^ (A * Lam n) * (2 : ℝ) ^ (A * Lam n) := h1.trans (by gcongr)
    _ = (2 : ℝ) ^ (2 * A * Lam n) := by rw [← Real.rpow_add two_pos]; ring_nf

end Real

/-! ## One branch: the bounds -/

section Branch

/-- `L ≤ U + gP + 1`. -/
theorem Lc_le (K g P U : ℕ) (hK : 1 ≤ K) : Lc K g P U ≤ U + g * P + 1 := by
  unfold Lc AppRunningTime.Lof
  apply Nat.ceil_le.2
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hζ : 2 * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) ≤ 1 := by
    push_cast
    rw [show (2 : ℝ) * (1 / (2 * K)) = 1 / K by field_simp]
    rw [div_le_one (by linarith)]; exact hK1
  have h1 : (U : ℝ) + 2 * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) * g * P ≤ U + g * P := by
    have : (0 : ℝ) ≤ (g : ℝ) * P := by positivity
    nlinarith
  have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ hK1
  have h0 : (0 : ℝ) ≤ (U : ℝ) + 2 * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) * g * P := by positivity
  calc ((U : ℝ) + 2 * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) * g * P) / (K : ℝ) ^ 2
      ≤ (U : ℝ) + 2 * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) * g * P := div_le_self h0 hK2
    _ ≤ U + g * P := h1
    _ ≤ ((U + g * P + 1 : ℕ) : ℝ) := by push_cast; linarith

/-- `K² L ≤ U + gP/K + K²`. -/
theorem K2L_le (K g P U : ℕ) (hK : 1 ≤ K) :
    (K : ℝ) ^ 2 * Lc K g P U ≤ U + g * P / K + (K : ℝ) ^ 2 := by
  unfold Lc AppRunningTime.Lof
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hc := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ((U : ℝ) + 2 * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) * g * P) /
    (K : ℝ) ^ 2 by positivity)).le
  have e1 : (2 : ℝ) * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) * g * P = g * P / K := by
    push_cast; field_simp
  rw [e1] at hc
  have hK2 : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
  calc (K : ℝ) ^ 2 * (⌈((U : ℝ) + 2 * (((1 : ℕ) : ℝ) / ((2 * K : ℕ) : ℝ)) * g * P) / (K : ℝ) ^ 2⌉₊ : ℕ)
      = (K : ℝ) ^ 2 * (⌈((U : ℝ) + g * P / K) / (K : ℝ) ^ 2⌉₊ : ℕ) := by rw [e1]
    _ ≤ (K : ℝ) ^ 2 * (((U : ℝ) + g * P / K) / (K : ℝ) ^ 2 + 1) := by gcongr
    _ = U + g * P / K + (K : ℝ) ^ 2 := by field_simp

theorem Bc_le (K g P B : ℕ) : Bc K g P B ≤ 2 * g * P + K + g ^ 2 * B := by
  unfold Bc AppRunningTime.B'of
  have := Nat.div_le_self (2 * g * P + K - 1) K
  omega

theorem size_pair_le (K : ℕ) : size (1, 2 * K) ≤ 2 * K + 3 := by
  have h1 := size_nat_le' 1
  have h2 := size_nat_le' (2 * K)
  change size 1 + size (2 * K) ≤ _
  omega

/-- Polynomial bounds of the numbers of one branch. -/
theorem branch_pol (c₀ q k₀ : ℕ) : ∃ A₀ : ℕ, ∀ (n m K mu P B U : ℕ), 1 ≤ K → K ^ 30 ≤ k₀ * (n + 2) →
    m ≤ n * n → 3 * K ^ 8 * mu ≤ 2 * m + 3 * K ^ 8 * (n / (3 * K ^ 8) + 2) →
    U ≤ c₀ * (m + n) + q * (3 * K ^ 8) ^ 3 → P ≤ c₀ * mu + q * (3 * K ^ 8) ^ 2 →
    B ≤ q * (n + 3 * K ^ 8 + 2) ^ q →
    Pol A₀ n (K * (Lc K (3 * K ^ 8) P U + Bc K (3 * K ^ 8) P B)) ∧
    Pol A₀ n (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ∧ Pol A₀ n (q * (n + 3 * K ^ 8 + 2) ^ q) := by
  -- the bounding polynomials
  let Gb : ℕ → ℕ := fun n => 3 * k₀ * (n + 2)
  let Kb : ℕ → ℕ := fun n => k₀ * (n + 2)
  let μb : ℕ → ℕ := fun n => 2 * (n * n) + n + 2 * Gb n
  let Ub : ℕ → ℕ := fun n => c₀ * (n * n + n) + q * Gb n ^ 3
  let Pb : ℕ → ℕ := fun n => c₀ * μb n + q * Gb n ^ 2
  let Bb : ℕ → ℕ := fun n => q * (n + Gb n + 2) ^ q
  have pG : ∃ A, ∀ n, Pol A n (Gb n) :=
    ⟨_, fun n => Pol.mul (Pol.const (3 * k₀)) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨aG, hG⟩ := pG
  have pK : ∃ A, ∀ n, Pol A n (Kb n) :=
    ⟨_, fun n => Pol.mul (Pol.const k₀) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨aK, hK⟩ := pK
  have pμ : ∃ A, ∀ n, Pol A n (μb n) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.mul (Pol.const 2) (Pol.mul Pol.id Pol.id)) Pol.id)
      (Pol.mul (Pol.const 2) (hG n))⟩
  obtain ⟨aμ, hμ⟩ := pμ
  have pU : ∃ A, ∀ n, Pol A n (Ub n) :=
    ⟨_, fun n => Pol.add (Pol.mul (Pol.const c₀) (Pol.add (Pol.mul Pol.id Pol.id) Pol.id))
      (Pol.mul (Pol.const q) (Pol.pow (hG n) 3))⟩
  obtain ⟨aU, hU⟩ := pU
  have pP : ∃ A, ∀ n, Pol A n (Pb n) :=
    ⟨_, fun n => Pol.add (Pol.mul (Pol.const c₀) (hμ n)) (Pol.mul (Pol.const q) (Pol.pow (hG n) 2))⟩
  obtain ⟨aP, hP⟩ := pP
  have pB : ∃ A, ∀ n, Pol A n (Bb n) :=
    ⟨_, fun n => Pol.mul (Pol.const q) (Pol.pow (Pol.add (Pol.add Pol.id (hG n)) (Pol.const 2)) q)⟩
  obtain ⟨aB, hB⟩ := pB
  have p1 : ∃ A, ∀ n, Pol A n (Kb n * ((Ub n + Gb n * Pb n + 1) + (2 * Gb n * Pb n + Kb n + Gb n ^ 2 * Bb n))) :=
    ⟨_, fun n => Pol.mul (hK n) (Pol.add (Pol.add (Pol.add (hU n) (Pol.mul (hG n) (hP n))) (Pol.const 1))
      (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.const 2) (hG n)) (hP n)) (hK n))
        (Pol.mul (Pol.pow (hG n) 2) (hB n))))⟩
  obtain ⟨a1, h1⟩ := p1
  have p2 : ∃ A, ∀ n, Pol A n (Gb n * (Pb n + Bb n) + (2 * Kb n + 3)) :=
    ⟨_, fun n => Pol.add (Pol.mul (hG n) (Pol.add (hP n) (hB n)))
      (Pol.add (Pol.mul (Pol.const 2) (hK n)) (Pol.const 3))⟩
  obtain ⟨a2, h2⟩ := p2
  refine ⟨a1 + a2 + aB, fun n m K mu P B U hK1 hup hm hmu hUle hPle hBle => ?_⟩
  -- the numbers against the polynomials
  have hKK : K ≤ Kb n := by
    have : K ≤ K ^ 30 := Nat.le_self_pow (by norm_num) K
    exact this.trans hup
  have hgK : 3 * K ^ 8 ≤ Gb n := by
    have : K ^ 8 ≤ K ^ 30 := Nat.pow_le_pow_right hK1 (by norm_num)
    show 3 * K ^ 8 ≤ 3 * k₀ * (n + 2)
    rw [mul_assoc]; exact Nat.mul_le_mul_left 3 (this.trans hup)
  have hg1 : 1 ≤ 3 * K ^ 8 := by have := Nat.one_le_pow 8 K hK1; omega
  have hmu' : mu ≤ μb n := by
    have h1 : 3 * K ^ 8 * (n / (3 * K ^ 8)) ≤ n := Nat.mul_div_le n _
    have h2 : 3 * K ^ 8 * mu ≤ 2 * m + n + 2 * (3 * K ^ 8) := by nlinarith
    have h3 : mu ≤ 3 * K ^ 8 * mu := Nat.le_mul_of_pos_left mu (by omega)
    show mu ≤ 2 * (n * n) + n + 2 * Gb n
    omega
  have hU' : U ≤ Ub n := by
    refine hUle.trans (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) ?_)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgK 3)
  have hP' : P ≤ Pb n := hPle.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hmu')
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgK 2)))
  have hq' : q * (n + 3 * K ^ 8 + 2) ^ q ≤ Bb n :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hB' : B ≤ Bb n := hBle.trans hq'
  have hL' : Lc K (3 * K ^ 8) P U ≤ Ub n + Gb n * Pb n + 1 :=
    (Lc_le K _ P U hK1).trans (by have := Nat.mul_le_mul hgK hP'; omega)
  have hBc' : Bc K (3 * K ^ 8) P B ≤ 2 * Gb n * Pb n + Kb n + Gb n ^ 2 * Bb n :=
    (Bc_le K _ P B).trans (by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hgK) hP'
      have := Nat.mul_le_mul (Nat.pow_le_pow_left hgK 2) hB'
      omega)
  refine ⟨((h1 n).mono (by omega)).le (Nat.mul_le_mul hKK (Nat.add_le_add hL' hBc')),
    ((h2 n).mono (by omega)).le ?_, ((hB n).mono (by omega)).le hq'⟩
  have := size_pair_le K
  have := Nat.mul_le_mul hgK (Nat.add_le_add hP' hB')
  omega

end Branch

section Branch2

/-- The products with `√(log₂(n+2))` of the lower-order terms are `O(m + n + 2)`. -/
theorem prod_facts {n m K c₁ k₀ : ℕ} (hK : 2 ≤ K) (hup : K ^ 30 ≤ k₀ * (n + 2)) (hlo : n + 2 ≤ K ^ c₁) :
    (∀ j ≤ 29, (K : ℝ) ^ j * sq n ≤ c₁ * k₀ * ((m : ℝ) + n + 2)) ∧
    ((m : ℝ) + n + 2) / K * sq n ≤ c₁ * ((m : ℝ) + n + 2) ∧
    Lam n * sq n ≤ (c₁ : ℝ) ^ 2 * k₀ * ((m : ℝ) + n + 2) ∧
    (K : ℝ) ^ 2 * Lam n * sq n ≤ (c₁ : ℝ) ^ 2 * k₀ * ((m : ℝ) + n + 2) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hK0 : (0 : ℝ) < K := by linarith
  have hs := sq_le_K (by omega) hlo
  have hs0 := sq_pos n
  have hΛ := Lam_le_K (by omega) hlo
  have hc : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg _
  have h30 : (K : ℝ) ^ 30 ≤ k₀ * ((m : ℝ) + n + 2) := by
    have : ((K ^ 30 : ℕ) : ℝ) ≤ ((k₀ * (n + 2) : ℕ) : ℝ) := by exact_mod_cast hup
    push_cast at this
    have : (0 : ℝ) ≤ k₀ * (m : ℝ) := by positivity
    nlinarith
  have hpow : ∀ j ≤ 30, (K : ℝ) ^ j ≤ (K : ℝ) ^ 30 := fun j hj => pow_le_pow_right₀ hK1 hj
  refine ⟨fun j hj => ?_, ?_, ?_, ?_⟩
  · calc (K : ℝ) ^ j * sq n ≤ (K : ℝ) ^ j * (c₁ * K) := by gcongr
      _ = c₁ * (K : ℝ) ^ (j + 1) := by ring
      _ ≤ c₁ * (K : ℝ) ^ 30 := mul_le_mul_of_nonneg_left (hpow _ (by omega)) hc
      _ ≤ c₁ * (k₀ * ((m : ℝ) + n + 2)) := by gcongr
      _ = _ := by ring
  · have hM : (0 : ℝ) ≤ (m : ℝ) + n + 2 := by positivity
    calc ((m : ℝ) + n + 2) / K * sq n ≤ ((m : ℝ) + n + 2) / K * (c₁ * K) := by gcongr
      _ = c₁ * ((m : ℝ) + n + 2) := by field_simp
  · have hΛ0 : 0 ≤ Lam n := by linarith [one_le_Lam n]
    calc Lam n * sq n ≤ (c₁ * K) * (c₁ * K) := by gcongr
      _ = (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 2 := by ring
      _ ≤ (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 30 := mul_le_mul_of_nonneg_left (hpow 2 (by norm_num)) (by positivity)
      _ ≤ (c₁ : ℝ) ^ 2 * (k₀ * ((m : ℝ) + n + 2)) := by gcongr
      _ = _ := by ring
  · have hΛ0 : 0 ≤ Lam n := by linarith [one_le_Lam n]
    calc (K : ℝ) ^ 2 * Lam n * sq n ≤ (K : ℝ) ^ 2 * (c₁ * K) * (c₁ * K) := by gcongr
      _ = (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 4 := by ring
      _ ≤ (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 30 := mul_le_mul_of_nonneg_left (hpow 4 (by norm_num)) (by positivity)
      _ ≤ (c₁ : ℝ) ^ 2 * (k₀ * ((m : ℝ) + n + 2)) := by gcongr
      _ = _ := by ring

/-- `x ≤ A (m+n+2)/s` from `x s ≤ A (m+n+2)`. -/
theorem le_Xp {x : ℝ} {A n m : ℕ} (h : x * sq n ≤ A * ((m : ℝ) + n + 2)) : x ≤ Xp A n m := by
  unfold Xp; rw [le_div_iff₀ (sq_pos n)]; exact h

theorem Xp_mono {A A' n m : ℕ} (h : A ≤ A') : Xp A n m ≤ Xp A' n m := by
  unfold Xp
  have : (0 : ℝ) ≤ (m : ℝ) + n + 2 := by positivity
  have : (A : ℝ) ≤ A' := by exact_mod_cast h
  have := sq_pos n
  gcongr

theorem two_rpow_natCast_mul (x : ℝ) (k : ℕ) : ((2 : ℝ) ^ x) ^ k = (2 : ℝ) ^ (x * k) :=
  (Real.rpow_mul_natCast (by norm_num) x k).symm

theorem two_pow_nat (k : ℕ) : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast 2 k).symm

end Branch2

section Branch3

/-- The exponent of one branch against `A (m+n+2)/√(log₂(n+2))`, multiplied out. -/
theorem core_exp {n m K mu P U A₀ c₀ q C₀ C₁ x₀ k₀ c₁ : ℕ} {e L : ℝ} (hK2 : 2 ≤ K)
    (hup : K ^ 30 ≤ k₀ * (n + 2)) (hlo : n + 2 ≤ K ^ c₁) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (heK : e ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 K))
    (hmu : 3 * K ^ 8 * mu ≤ 2 * m + 3 * K ^ 8 * (n / (3 * K ^ 8) + 2))
    (hU : U ≤ c₀ * (m + n) + q * (3 * K ^ 8) ^ 3) (hP : P ≤ c₀ * mu + q * (3 * K ^ 8) ^ 2)
    (hKL : (K : ℝ) ^ 2 * L ≤ U + 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) :
    (3 + ((K * (3 * K ^ 8) : ℕ) : ℝ) + (e * (K : ℝ) ^ 2 * L + 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) +
      2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K + ((c₀ * mu : ℕ) : ℝ) + 2 * A₀ * Lam n) + 2 * A₀ * Lam n * C₁) * sq n ≤
      (((3 + 2 * c₀ + 1 + 18 * c₀ + 3 + 108 * q) * (c₁ * k₀) + c₀ * ((3 * x₀ + 6) * c₁) + 8 * c₀ * c₁ +
        (2 * A₀ * C₀ + (2 * A₀ + 2 * A₀ * C₁)) * (c₁ ^ 2 * k₀) : ℕ) : ℝ) * ((m : ℝ) + n + 2) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hK0 : (0 : ℝ) < K := by linarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hM0 : (0 : ℝ) ≤ (m : ℝ) + n + 2 := by positivity
  have hs0 := sq_pos n
  have hgμ : 3 * (K : ℝ) ^ 8 * mu ≤ 2 * m + n + 6 * (K : ℝ) ^ 8 := by
    have h1 : 3 * K ^ 8 * (n / (3 * K ^ 8)) ≤ n := Nat.mul_div_le n _
    have h2 : 3 * K ^ 8 * mu ≤ 2 * m + n + 6 * K ^ 8 := by nlinarith
    exact_mod_cast h2
  have hUr : (U : ℝ) ≤ c₀ * ((m : ℝ) + n) + 27 * q * (K : ℝ) ^ 24 := by
    have : (U : ℝ) ≤ ((c₀ * (m + n) + q * (3 * K ^ 8) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hU
    push_cast at this; nlinarith
  have hPr : (P : ℝ) ≤ c₀ * mu + 9 * q * (K : ℝ) ^ 16 := by
    have : (P : ℝ) ≤ ((c₀ * mu + q * (3 * K ^ 8) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hP
    push_cast at this; nlinarith
  have hK8 : (0 : ℝ) ≤ 3 * (K : ℝ) ^ 8 := by positivity
  have hgP : 3 * (K : ℝ) ^ 8 * P ≤ c₀ * (2 * m + n + 6 * (K : ℝ) ^ 8) + 27 * q * (K : ℝ) ^ 24 := by
    have hc : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
    calc 3 * (K : ℝ) ^ 8 * P ≤ 3 * (K : ℝ) ^ 8 * (c₀ * mu + 9 * q * (K : ℝ) ^ 16) := by gcongr
      _ = c₀ * (3 * (K : ℝ) ^ 8 * mu) + 27 * q * (K : ℝ) ^ 24 := by ring
      _ ≤ c₀ * (2 * m + n + 6 * (K : ℝ) ^ 8) + 27 * q * (K : ℝ) ^ 24 := by gcongr
  have hgPK : 3 * (K : ℝ) ^ 8 * P / K ≤
      2 * c₀ * ((m : ℝ) + n + 2) / K + 6 * c₀ * (K : ℝ) ^ 8 + 27 * q * (K : ℝ) ^ 24 := by
    have hc : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have e1 : (6 * c₀ * (K : ℝ) ^ 8 + 27 * q * (K : ℝ) ^ 24) / K ≤ 6 * c₀ * (K : ℝ) ^ 8 + 27 * q * (K : ℝ) ^ 24 :=
      div_le_self (by positivity) hK1
    have e2 : c₀ * (2 * (m : ℝ) + n) / K ≤ 2 * c₀ * ((m : ℝ) + n + 2) / K := by
      apply div_le_div_of_nonneg_right _ hK0.le
      have : (2 * (m : ℝ) + n) ≤ 2 * ((m : ℝ) + n + 2) := by linarith
      calc c₀ * (2 * (m : ℝ) + n) ≤ c₀ * (2 * ((m : ℝ) + n + 2)) := mul_le_mul_of_nonneg_left this hc
        _ = _ := by ring
    calc 3 * (K : ℝ) ^ 8 * P / K ≤ (c₀ * (2 * m + n + 6 * (K : ℝ) ^ 8) + 27 * q * (K : ℝ) ^ 24) / K := by
          gcongr
      _ = c₀ * (2 * (m : ℝ) + n) / K + (6 * c₀ * (K : ℝ) ^ 8 + 27 * q * (K : ℝ) ^ 24) / K := by ring
      _ ≤ _ := by linarith
  have hμK : (mu : ℝ) ≤ 2 * ((m : ℝ) + n + 2) / K + 2 := by
    have hg0 : (0 : ℝ) < 3 * (K : ℝ) ^ 8 := by positivity
    have hKg : (K : ℝ) ≤ 3 * (K : ℝ) ^ 8 := by
      have : (K : ℝ) ≤ (K : ℝ) ^ 8 := le_self_pow₀ hK1 (by norm_num)
      linarith
    have e1 : (mu : ℝ) ≤ (2 * ((m : ℝ) + n + 2)) / (3 * (K : ℝ) ^ 8) + 2 := by
      have e0 : (mu : ℝ) ≤ (2 * ((m : ℝ) + n + 2) + 2 * (3 * (K : ℝ) ^ 8)) / (3 * (K : ℝ) ^ 8) := by
        rw [le_div_iff₀ hg0]; linarith
      have e3 : (2 * ((m : ℝ) + n + 2) + 2 * (3 * (K : ℝ) ^ 8)) / (3 * (K : ℝ) ^ 8) =
          (2 * ((m : ℝ) + n + 2)) / (3 * (K : ℝ) ^ 8) + 2 := by field_simp
      linarith
    have e2 : (2 * ((m : ℝ) + n + 2)) / (3 * (K : ℝ) ^ 8) ≤ 2 * ((m : ℝ) + n + 2) / K :=
      div_le_div_of_nonneg_left (by positivity) hK0 hKg
    linarith
  have heKL : e * (K : ℝ) ^ 2 * L ≤ e * U + 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2 := by positivity
    calc e * (K : ℝ) ^ 2 * L = e * ((K : ℝ) ^ 2 * L) := by ring
      _ ≤ e * (U + 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) := by gcongr
      _ = e * U + e * (3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) := by ring
      _ ≤ e * U + 1 * (3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have heU : e * U ≤ c₀ * (e * ((m : ℝ) + n + 2)) + 27 * q * (K : ℝ) ^ 24 := by
    have hc : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
    have h0 : (0 : ℝ) ≤ 27 * q * (K : ℝ) ^ 24 := by positivity
    calc e * U ≤ e * (c₀ * ((m : ℝ) + n) + 27 * q * (K : ℝ) ^ 24) := by gcongr
      _ = c₀ * (e * ((m : ℝ) + n)) + e * (27 * q * (K : ℝ) ^ 24) := by ring
      _ ≤ c₀ * (e * ((m : ℝ) + n + 2)) + 1 * (27 * q * (K : ℝ) ^ 24) := by
          have t1 : e * ((m : ℝ) + n) ≤ e * ((m : ℝ) + n + 2) := mul_le_mul_of_nonneg_left (by linarith) he0
          have t2 : e * (27 * q * (K : ℝ) ^ 24) ≤ 1 * (27 * q * (K : ℝ) ^ 24) := mul_le_mul_of_nonneg_right he1 h0
          have t3 := mul_le_mul_of_nonneg_left t1 hc
          linarith
      _ = _ := by ring
  have hcμ : (c₀ : ℝ) * mu ≤ c₀ * (2 * ((m : ℝ) + n + 2) / K + 2) :=
    mul_le_mul_of_nonneg_left hμK (Nat.cast_nonneg _)
  have hY : 3 + ((K * (3 * K ^ 8) : ℕ) : ℝ) + (e * (K : ℝ) ^ 2 * L + 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) + 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K + ((c₀ * mu : ℕ) : ℝ) + 2 * A₀ * Lam n) + 2 * A₀ * Lam n * C₁ ≤ (3 + 2 * c₀) + (K : ℝ) ^ 2 + 18 * c₀ * (K : ℝ) ^ 8 + 3 * (K : ℝ) ^ 9 +
      108 * q * (K : ℝ) ^ 24 + c₀ * (e * ((m : ℝ) + n + 2)) + 8 * c₀ * (((m : ℝ) + n + 2) / K) +
      2 * A₀ * C₀ * ((K : ℝ) ^ 2 * Lam n) + (2 * A₀ + 2 * A₀ * C₁) * Lam n := by
    have ex1 : ((K * (3 * K ^ 8) : ℕ) : ℝ) = 3 * (K : ℝ) ^ 9 := by push_cast; ring
    have ex4 : 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K = 2 * (3 * (K : ℝ) ^ 8 * P / K) := by push_cast; ring
    have exT : 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) = 2 * A₀ * C₀ * ((K : ℝ) ^ 2 * Lam n) := by
      push_cast; ring
    have ex2 : ((c₀ * mu : ℕ) : ℝ) = c₀ * mu := by push_cast; ring
    have ex3 : 2 * A₀ * Lam n * C₁ = 2 * A₀ * C₁ * Lam n := by ring
    have eMK : 2 * c₀ * ((m : ℝ) + n + 2) / K = 2 * c₀ * (((m : ℝ) + n + 2) / K) := by ring
    have eMK' : c₀ * (2 * ((m : ℝ) + n + 2) / K + 2) = 2 * c₀ * (((m : ℝ) + n + 2) / K) + 2 * c₀ := by ring
    rw [eMK] at hgPK
    rw [eMK'] at hcμ
    rw [ex1, ex2, ex3, exT, ex4]
    linarith
  obtain ⟨pj, pM, pΛ, pK2Λ⟩ := prod_facts (m := m) hK2 hup hlo
  have he := e_sq_le hK2 hlo he0 (Nat.cast_nonneg _) heK
  have hc₀ : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have f0 : (3 + 2 * (c₀ : ℝ)) * sq n ≤ (3 + 2 * (c₀ : ℝ)) * (c₁ * k₀ * ((m : ℝ) + n + 2)) := by
    have := pj 0 (by norm_num); rw [pow_zero, one_mul] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have f2 := pj 2 (by norm_num)
  have f8 := mul_le_mul_of_nonneg_left (pj 8 (by norm_num)) (by positivity : (0 : ℝ) ≤ 18 * c₀)
  have f9 := mul_le_mul_of_nonneg_left (pj 9 (by norm_num)) (by positivity : (0 : ℝ) ≤ 3)
  have f24 := mul_le_mul_of_nonneg_left (pj 24 (by norm_num)) (by positivity : (0 : ℝ) ≤ 108 * q)
  have fe : c₀ * (e * ((m : ℝ) + n + 2)) * sq n ≤ c₀ * (((3 * x₀ + 6 : ℕ) : ℝ) * c₁) * ((m : ℝ) + n + 2) := by
    have : e * ((m : ℝ) + n + 2) * sq n ≤ ((3 * x₀ + 6 : ℕ) : ℝ) * c₁ * ((m : ℝ) + n + 2) := by
      calc e * ((m : ℝ) + n + 2) * sq n = (e * sq n) * ((m : ℝ) + n + 2) := by ring
        _ ≤ _ := by gcongr
    calc c₀ * (e * ((m : ℝ) + n + 2)) * sq n = c₀ * (e * ((m : ℝ) + n + 2) * sq n) := by ring
      _ ≤ c₀ * (((3 * x₀ + 6 : ℕ) : ℝ) * c₁ * ((m : ℝ) + n + 2)) := by gcongr
      _ = _ := by ring
  have fM := mul_le_mul_of_nonneg_left pM (by positivity : (0 : ℝ) ≤ 8 * c₀)
  have fK := mul_le_mul_of_nonneg_left pK2Λ (by positivity : (0 : ℝ) ≤ 2 * A₀ * C₀)
  have fΛ := mul_le_mul_of_nonneg_left pΛ (by positivity : (0 : ℝ) ≤ 2 * A₀ + 2 * A₀ * C₁)
  calc (3 + ((K * (3 * K ^ 8) : ℕ) : ℝ) + (e * (K : ℝ) ^ 2 * L + 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) + 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K + ((c₀ * mu : ℕ) : ℝ) + 2 * A₀ * Lam n) + 2 * A₀ * Lam n * C₁) * sq n ≤ ((3 + 2 * c₀) + (K : ℝ) ^ 2 + 18 * c₀ * (K : ℝ) ^ 8 + 3 * (K : ℝ) ^ 9 +
      108 * q * (K : ℝ) ^ 24 + c₀ * (e * ((m : ℝ) + n + 2)) + 8 * c₀ * (((m : ℝ) + n + 2) / K) +
      2 * A₀ * C₀ * ((K : ℝ) ^ 2 * Lam n) + (2 * A₀ + 2 * A₀ * C₁) * Lam n) * sq n := by gcongr
    _ ≤ _ := by
      push_cast at fe ⊢
      linarith [f0, f2, f8, f9, f24, fe, fM, fK, fΛ]


/-- **One branch, in `2^{O((m+n)/√log n)}`.** The steps (three times the bound of Lemma 8) and the
state bound of one branch are at most `2^{A (m+n+2)/√(log₂(n+2))}`, for one constant `A` that
depends only on the constants of the package, of Lemma 8, of Theorem A(b) and of the level choice. -/
theorem branch_bound (c₀ q C₁ C₀ x₀ k₀ c₁ : ℕ) : ∃ A : ℕ, ∀ (n m K mu P B τ S U sc : ℕ) (e : ℝ),
    2 ≤ K → K ^ 30 ≤ k₀ * (n + 2) → n + 2 ≤ K ^ c₁ → 0 ≤ e → e ≤ 1 →
    e ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 K) → m ≤ n * n →
    3 * K ^ 8 * mu ≤ 2 * m + 3 * K ^ 8 * (n / (3 * K ^ 8) + 2) →
    U ≤ c₀ * (m + n) + q * (3 * K ^ 8) ^ 3 → P ≤ c₀ * mu + q * (3 * K ^ 8) ^ 2 →
    B ≤ q * (n + 3 * K ^ 8 + 2) ^ q → τ ≤ 2 ^ (c₀ * mu) * (q * (n + 3 * K ^ 8 + 2) ^ q) →
    S + sc ≤ q * (n + 3 * K ^ 8 + 2) ^ q →
    3 * (((K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) *
        (2 : ℝ) ^ (2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K) * τ) * (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁)
      ≤ (2 : ℝ) ^ Xp A n m ∧
    ((sc + (Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) +
      (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Xp A n m := by
  obtain ⟨A₀, hA₀⟩ := branch_pol c₀ q k₀
  refine ⟨(3 + 2 * c₀ + 1 + 18 * c₀ + 3 + 108 * q) * (c₁ * k₀) + c₀ * ((3 * x₀ + 6) * c₁) + 8 * c₀ * c₁ +
    (2 * A₀ * C₀ + (2 * A₀ + 2 * A₀ * C₁)) * (c₁ ^ 2 * k₀), ?_⟩
  intro n m K mu P B τ S U sc e hK2 hup hlo he0 he1 heK hm hmu hU hP hB hτ hS
  obtain ⟨h1, h2, h3⟩ := hA₀ n m K mu P B U (by omega) hup hm hmu hU hP hB
  have hΛ1 : 1 ≤ Lam n := one_le_Lam n
  have hPw1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * A₀ * Lam n) := Real.one_le_rpow one_le_two (by positivity)
  have hx1 := pol_le_two_rpow h1
  have hx2 := pol_le_two_rpow h2
  have hx3 := pol_le_two_rpow h3
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hK0 : (0 : ℝ) < K := by linarith
  -- the exponents
  set Pw : ℝ := (2 : ℝ) ^ (2 * A₀ * Lam n) with hPwd
  set L := Lc K (3 * K ^ 8) P U with hLd
  set B' := Bc K (3 * K ^ 8) P B with hB'd
  set XT : ℝ := e * (K : ℝ) ^ 2 * L + 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) with hXT
  set x4 : ℝ := 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K with hx4
  set X1 : ℝ := ((K * (3 * K ^ 8) : ℕ) : ℝ) with hX1
  set X2 : ℝ := XT + x4 + ((c₀ * mu : ℕ) : ℝ) + 2 * A₀ * Lam n with hX2
  set X3 : ℝ := 2 * A₀ * Lam n * C₁ with hX3
  have hXT0 : 0 ≤ XT := by positivity
  have hx40 : 0 ≤ x4 := by positivity
  have hX10 : 0 ≤ X1 := by positivity
  have hX20 : 0 ≤ X2 := by positivity
  have hX30 : 0 ≤ X3 := by positivity
  have hcm0 : (0 : ℝ) ≤ ((c₀ * mu : ℕ) : ℝ) := Nat.cast_nonneg _
  have hAΛ0 : (0 : ℝ) ≤ 2 * A₀ * Lam n := by positivity
  -- the factors
  have hT : (Tc e K C₀ L B' : ℝ) ≤ (2 : ℝ) ^ XT := by
    have hb : CliqueLevels.bound e K C₀ L B' ≤ (2 : ℝ) ^ XT := by
      unfold CliqueLevels.bound
      have hx1' : (K : ℝ) * ((L : ℝ) + B') ≤ Pw := by push_cast at hx1; exact hx1
      calc (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * ((K : ℝ) * ((L : ℝ) + B')) ^ (C₀ * K ^ 2)
          ≤ (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * Pw ^ (C₀ * K ^ 2) := by gcongr
        _ = (2 : ℝ) ^ XT := by
          rw [hXT, Real.rpow_add two_pos, hPwd, two_rpow_natCast_mul]
    exact (Nat.floor_le (by unfold CliqueLevels.bound; positivity)).trans hb
  have hτr : (τ : ℝ) ≤ (2 : ℝ) ^ ((c₀ * mu : ℕ) : ℝ) * Pw := by
    have : (τ : ℝ) ≤ ((2 ^ (c₀ * mu) * (q * (n + 3 * K ^ 8 + 2) ^ q) : ℕ) : ℝ) := by exact_mod_cast hτ
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, two_pow_nat] at this
    exact this.trans (by gcongr)
  have hKg : (K : ℝ) ^ (3 * K ^ 8) ≤ (2 : ℝ) ^ X1 := by
    have e1 : (K : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast Nat.lt_two_pow_self.le
    calc (K : ℝ) ^ (3 * K ^ 8) ≤ ((2 : ℝ) ^ K) ^ (3 * K ^ 8) := by gcongr
      _ = (2 : ℝ) ^ (K * (3 * K ^ 8)) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ X1 := two_pow_nat _
  have hgPB : (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁ ≤ (2 : ℝ) ^ X3 := by
    have : ((3 * K ^ 8 : ℕ) : ℝ) * (P + B) ≤ Pw := by
      have e1 : ((3 * K ^ 8 * (P + B) : ℕ) : ℝ) ≤ ((3 * K ^ 8 * (P + B) + size (1, 2 * K) : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right _ _
      push_cast at e1 ⊢; push_cast at hx2; linarith
    calc (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁ ≤ Pw ^ C₁ := by gcongr
      _ = (2 : ℝ) ^ X3 := two_rpow_natCast_mul _ _
  have e2 : (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * ((2 : ℝ) ^ ((c₀ * mu : ℕ) : ℝ) * Pw) = (2 : ℝ) ^ X2 := by
    rw [hX2, hPwd, Real.rpow_add two_pos (XT + x4 + _), Real.rpow_add two_pos (XT + x4),
      Real.rpow_add two_pos XT]
    ring
  have hY1 : (2 : ℝ) ^ X1 ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hY2 : (2 : ℝ) ^ X2 ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hY3 : (2 : ℝ) ^ X3 ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hYT : (2 : ℝ) ^ XT ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hYPw : Pw ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hY0 : (1 : ℝ) ≤ (2 : ℝ) ^ (X1 + X2 + X3) := Real.one_le_rpow one_le_two (by linarith)
  have h8 : (2 : ℝ) ^ (3 + X1 + X2 + X3) = 8 * (2 : ℝ) ^ (X1 + X2 + X3) := by
    rw [add_assoc, add_assoc, Real.rpow_add two_pos]; norm_num; ring_nf
  -- the exponent against `A (m+n+2)/s`
  have hfin : 3 + X1 + X2 + X3 ≤ Xp ((3 + 2 * c₀ + 1 + 18 * c₀ + 3 + 108 * q) * (c₁ * k₀) +
      c₀ * ((3 * x₀ + 6) * c₁) + 8 * c₀ * c₁ + (2 * A₀ * C₀ + (2 * A₀ + 2 * A₀ * C₁)) * (c₁ ^ 2 * k₀)) n m := by
    apply le_Xp
    have hKL := K2L_le K (3 * K ^ 8) P U (by omega)
    rw [← hLd] at hKL
    push_cast at hKL
    rw [hX1, hX2, hXT, hx4, hX3]
    exact core_exp hK2 hup hlo he0 he1 heK hmu hU hP hKL
  constructor
  · calc 3 * (((K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ L B' * (2 : ℝ) ^ x4 * τ) *
          (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁)
        ≤ 3 * (((2 : ℝ) ^ X1 + (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * ((2 : ℝ) ^ ((c₀ * mu : ℕ) : ℝ) * Pw)) *
          (2 : ℝ) ^ X3) := by
          have hA : (K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ L B' * (2 : ℝ) ^ x4 * τ ≤
              (2 : ℝ) ^ X1 + (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * ((2 : ℝ) ^ ((c₀ * mu : ℕ) : ℝ) * Pw) :=
            add_le_add hKg (mul_le_mul (mul_le_mul_of_nonneg_right hT (by positivity)) hτr
              (by positivity) (by positivity))
          exact mul_le_mul_of_nonneg_left (mul_le_mul hA hgPB (by positivity) (by positivity))
            (by norm_num)
      _ = 3 * (((2 : ℝ) ^ X1 + (2 : ℝ) ^ X2) * (2 : ℝ) ^ X3) := by rw [e2]
      _ ≤ 3 * (((2 : ℝ) ^ (X1 + X2 + X3) + (2 : ℝ) ^ (X1 + X2 + X3))) := by
          have : (2 : ℝ) ^ X1 * (2 : ℝ) ^ X3 ≤ (2 : ℝ) ^ (X1 + X2 + X3) := by
            rw [← Real.rpow_add two_pos]; exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
          have : (2 : ℝ) ^ X2 * (2 : ℝ) ^ X3 ≤ (2 : ℝ) ^ (X1 + X2 + X3) := by
            rw [← Real.rpow_add two_pos]; exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
          rw [add_mul]; linarith
      _ ≤ (2 : ℝ) ^ (3 + X1 + X2 + X3) := by rw [h8]; linarith
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hfin
  · have hx3' : ((S + sc : ℕ) : ℝ) ≤ Pw := le_trans (by exact_mod_cast hS) hx3
    have hgx : (((3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁ : ℕ) : ℝ) ≤ (2 : ℝ) ^ X3 := by
      push_cast; push_cast at hx2
      calc ((3 : ℝ) * (K : ℝ) ^ 8 * (P + B) + (size (1, 2 * K) : ℝ)) ^ C₁ ≤ Pw ^ C₁ := by gcongr
        _ = (2 : ℝ) ^ X3 := two_rpow_natCast_mul _ _
    calc ((sc + (Tc e K C₀ L B' + (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1 : ℕ) : ℝ)
        = ((S + sc : ℕ) : ℝ) + (Tc e K C₀ L B' : ℝ) +
          (((3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁ : ℕ) : ℝ) + 4 := by push_cast; ring
      _ ≤ (2 : ℝ) ^ (X1 + X2 + X3) + (2 : ℝ) ^ (X1 + X2 + X3) + (2 : ℝ) ^ (X1 + X2 + X3) +
          4 * (2 : ℝ) ^ (X1 + X2 + X3) := by linarith
      _ ≤ (2 : ℝ) ^ (3 + X1 + X2 + X3) := by rw [h8]; linarith
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hfin

end Branch3

/-! ## The branches of one graph -/

section Graph

theorem Xp_add (A B n m : ℕ) : Xp A n m + Xp B n m = Xp (A + B) n m := by
  unfold Xp; push_cast; ring

theorem Xp_nonneg (A n m : ℕ) : 0 ≤ Xp A n m := by
  unfold Xp; have := sq_pos n; positivity

/-- A polynomial bound gives a bound `2^{A' (m+n+2)/√log₂(n+2)}`. -/
theorem pol_le_Xp {n m K c₁ k₀ A x : ℕ} (hK : 2 ≤ K) (hup : K ^ 30 ≤ k₀ * (n + 2))
    (hlo : n + 2 ≤ K ^ c₁) (h : Pol A n x) : (x : ℝ) ≤ (2 : ℝ) ^ Xp (2 * A * (c₁ ^ 2 * k₀)) n m := by
  refine (pol_le_two_rpow h).trans (Real.rpow_le_rpow_of_exponent_le one_le_two (le_Xp ?_))
  obtain ⟨-, -, pΛ, -⟩ := prod_facts (m := m) hK hup hlo
  have : (0 : ℝ) ≤ 2 * A := by positivity
  calc 2 * (A : ℝ) * Lam n * sq n = 2 * A * (Lam n * sq n) := by ring
    _ ≤ 2 * A * ((c₁ : ℝ) ^ 2 * k₀ * ((m : ℝ) + n + 2)) := by gcongr
    _ = _ := by push_cast; ring

theorem card_edge_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : G.edgeFinset.card ≤ n * n :=
  calc G.edgeFinset.card ≤ (Fintype.card (Fin n)).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ n * n := by rw [Fintype.card_fin]; exact (Nat.choose_le_pow n 2).trans (by rw [pow_two])

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

/-- The level of a graph on `n` vertices: `K = K_ℓ ≥ 2`, `K^30 ≤ K₀^30 (n+2)` and
`n + 2 ≤ K^{30C₀+1}`. -/
theorem kfacts (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) {n : ℕ}
    (a : GIn) (ha : a.1.length = n) :
    ∃ l, kN kf (Kf 0) a = Kf l ∧ 2 ≤ Kf l ∧ Kf l ^ 30 ≤ Kf 0 ^ 30 * (n + 2) ∧
      n + 2 ≤ Kf l ^ (30 * C₀ + 1) := by
  obtain ⟨l, h1, h2, h3⟩ := kN_spec kf hL hk a
  rw [ha] at h2 h3
  obtain ⟨r1, r2⟩ := rootN_spec n
  have hK2 := hL.K_two l
  have h01 : 1 ≤ Kf 0 ^ 30 := Nat.one_le_pow _ _ (by have := hL.K_two 0; omega)
  refine ⟨l, h1, hK2, ?_, ?_⟩
  · have e1 : Kf l ^ 30 ≤ (max (rootN n) (Kf 0)) ^ 30 := Nat.pow_le_pow_left h2 30
    have e2 : (max (rootN n) (Kf 0)) ^ 30 ≤ rootN n ^ 30 + Kf 0 ^ 30 := by
      rcases le_total (rootN n) (Kf 0) with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    have e3 : n + Kf 0 ^ 30 ≤ Kf 0 ^ 30 * (n + 2) := by nlinarith
    omega
  · have e1 : rootN n + 1 ≤ Kf l ^ C₀ := (Nat.succ_le_of_lt h3).trans (hL.K_le l)
    have e2 : n + 1 ≤ Kf l ^ (30 * C₀) := by
      have := Nat.pow_le_pow_left e1 30
      rw [← pow_mul, mul_comm C₀ 30] at this
      omega
    rw [pow_succ]
    nlinarith

end Graph

section Body

theorem logb_le_self (n : ℕ) : Lam n ≤ (n : ℝ) + 2 := by
  unfold Lam
  have h : ((n : ℝ) + 2) < 2 ^ ((n : ℝ) + 2) := by
    have : ((n + 2 : ℕ) : ℝ) < (2 : ℝ) ^ (n + 2) := by exact_mod_cast Nat.lt_two_pow_self
    rw [two_pow_nat] at this; push_cast at this; exact this
  have := Real.logb_lt_logb one_lt_two (by positivity) h
  rw [Real.logb_rpow two_pos (by norm_num)] at this
  exact this.le

theorem one_le_Xp_one (n m : ℕ) : 1 ≤ Xp 1 n m := by
  apply le_Xp
  have := sq_le_Lam n
  have := logb_le_self n
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast; linarith

theorem add_one_le_Xp {x : ℝ} {A n m : ℕ} (h : x ≤ (2 : ℝ) ^ Xp A n m) :
    x + 1 ≤ (2 : ℝ) ^ Xp (A + 1) n m := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ Xp A n m := Real.one_le_rpow one_le_two (Xp_nonneg A n m)
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ Xp 1 n m := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (one_le_Xp_one n m)
  rw [← Xp_add, Real.rpow_add two_pos]
  nlinarith

theorem size_y_le {n : ℕ} (G : SimpleGraph (Fin n)) (g : ℕ) {y : ℕ} (hy : y < nBr g (aOf G)) :
    size y ≤ n * n * n + 1 := by
  apply size_nat_of_lt
  have hl : (hlist g (aOf G)).length ≤ n := by
    unfold hlist; rw [aOf_len]
    exact (List.length_filter_le _ _).trans (by rw [List.length_range])
  calc y < nBr g (aOf G) := hy
    _ = (n * n) ^ (hlist g (aOf G)).length := by unfold nBr radix; rw [aOf_len]
    _ ≤ (2 ^ (n * n)) ^ (hlist g (aOf G)).length := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ ≤ (2 ^ (n * n)) ^ n := Nat.pow_le_pow_right (Nat.one_le_two_pow) hl
    _ = 2 ^ (n * n * n) := by rw [← pow_mul]

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

/-- **One branch, with one bound for all graphs.** -/
theorem body2_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {y : ℕ},
      y < nBr (gN kf (Kf 0) (aOf G)) (aOf G) →
      ∃ t : ℕ, (bodyM2 pk E kf (Kf 0)).Runs (aOf G, y) t ⌊(2 : ℝ) ^ Xp A n G.edgeFinset.card⌋₊
          ((n : ℤ) * ((hamCycles (brGraph G (gN kf (Kf 0) (aOf G)) y)).card : ℤ)) ∧
        t ≤ ⌊(2 : ℝ) ^ Xp A n G.edgeFinset.card⌋₊ := by
  obtain ⟨A₁, hA₁⟩ := branch_bound c₀ pk.q C₁ C₀ x₀ (Kf 0 ^ 30) (30 * C₀ + 1)
  have hP2 : ∃ A, ∀ n, Pol A n ((2 * n + 1) + (2 * (n * n) + 1) + (n * n * n + 1) + 3) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.mul Pol.id Pol.id)) (Pol.const 1)))
      (Pol.add (Pol.mul (Pol.mul Pol.id Pol.id) Pol.id) (Pol.const 1))) (Pol.const 3)⟩
  obtain ⟨A₂, hA₂⟩ := hP2
  refine ⟨A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30), fun {n} G _ {y} hy => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aOf G) (aOf_len G)
  rw [← hKl] at hK2 hup hlo
  have hg1 : 1 ≤ gN kf (Kf 0) (aOf G) := by
    have : 1 ≤ kN kf (Kf 0) (aOf G) ^ 8 := Nat.one_le_pow _ _ (by omega)
    simp only [gN]; omega
  have hA1 : A₁ ≤ A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30) := by omega
  by_cases hb : badW (gN kf (Kf 0) (aOf G)) (aOf G, y) = true
  · -- the branch has no Hamiltonian cycle
    have h0 := hamCycles_eq_empty ((badW_iff G _ y).1 hb)
    have hr : (bodyM2 pk E kf (Kf 0)).Runs (aOf G, y) 1 (max (size (aOf G, y)) (size (0 : ℤ)) + 1 + 1) 0 := by
      unfold bodyM2
      exact Stepped.ite_runs_true hb (Stepped.const_runs _ _)
    refine ⟨1, ?_, ?_⟩
    · rw [h0, card_empty, Nat.cast_zero, mul_zero]
      refine hr.mono le_rfl ?_
      apply Nat.le_floor
      have hs : max (size (aOf G, y)) (size (0 : ℤ)) + 1 + 1 ≤
          (2 * n + 1) + (2 * (n * n) + 1) + (n * n * n + 1) + 3 := by
        have h1 := size_aOf G
        have h2 := size_y_le G _ hy
        have h3 : size (0 : ℤ) = 1 := rfl
        have h4 : size (aOf G, y) = size (aOf G) + size y := rfl
        rw [h3, h4]; omega
      have := pol_le_Xp (m := G.edgeFinset.card) hK2 hup hlo ((hA₂ n).le hs)
      exact this.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono (by omega)))
    · apply Nat.le_floor
      have : (1 : ℝ) ≤ (2 : ℝ) ^ Xp (A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30)) n G.edgeFinset.card :=
        Real.one_le_rpow one_le_two (Xp_nonneg _ _ _)
      exact_mod_cast this
  · have hb' : badW (gN kf (Kf 0) (aOf G)) (aOf G, y) = false := by simpa using hb
    have hgood : ¬ (n ≤ 2 ∨ ∃ v, (brGraph G (gN kf (Kf 0) (aOf G)) y).degree v < 2) :=
      fun h => hb ((badW_iff G _ y).2 h)
    have h3 : 3 ≤ n := by omega
    have hdeg : ∀ v, 2 ≤ (brGraph G (gN kf (Kf 0) (aOf G)) y).degree v := fun v => by
      by_contra h; exact hgood (Or.inr ⟨v, by omega⟩)
    have hcode : brWord (gN kf (Kf 0) (aOf G)) (aOf G, y) = code (brGraph G (gN kf (Kf 0) (aOf G)) y) := by
      rw [← read1_code]; exact brWord_code G _ y
    have hctx : ctxF pk kf (Kf 0) (aOf G, y) =
        pk.prep (Printed.unary (gN kf (Kf 0) (aOf G)), code (brGraph G (gN kf (Kf 0) (aOf G)) y)) := by
      unfold ctxF; rw [hcode]
    have hN := pk.isNet _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg
    have hval := pk.value _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg
    have hS := pk.S_le _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg
    rw [← hctx] at hN hS
    obtain ⟨T, hrun, hT⟩ := net_runs' pk hC₁ hL hk E hsol l hKl hN hval
    have hmH := card_edge_brGraph_le G (gN kf (Kf 0) (aOf G)) y
    have hmu := pk.mu_le _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg _
      (degree_brGraph_le G (gN kf (Kf 0) (aOf G)) y)
    have hU := pk.U_le _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg
    have hP := pk.P_le _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg
    have hB := pk.B_le _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg
    have hτ := pk.τ_le _ (brGraph G (gN kf (Kf 0) (aOf G)) y) hg1 h3 hdeg
    have he0 : 0 ≤ e l := by
      have h1 := hL.e_ge l
      have hK1 : (1 : ℝ) < Kf l := by exact_mod_cast (by have := hL.K_two l; omega : 1 < Kf l)
      have : 0 < Real.logb 2 (Kf l) := Real.logb_pos one_lt_two hK1
      exact le_trans (by positivity) h1
    have heK := he l
    rw [← hKl] at heK
    obtain ⟨hb1, hb2⟩ := hA₁ n G.edgeFinset.card (kN kf (Kf 0) (aOf G))
      (pk.mu (gN kf (Kf 0) (aOf G)) (brGraph G (gN kf (Kf 0) (aOf G)) y))
      (pk.P (gN kf (Kf 0) (aOf G)) (brGraph G (gN kf (Kf 0) (aOf G)) y))
      (pk.B (gN kf (Kf 0) (aOf G)) (brGraph G (gN kf (Kf 0) (aOf G)) y))
      (pk.τ (gN kf (Kf 0) (aOf G)) (brGraph G (gN kf (Kf 0) (aOf G)) y))
      (pk.S (gN kf (Kf 0) (aOf G)) (brGraph G (gN kf (Kf 0) (aOf G)) y))
      ((pk.net (gN kf (Kf 0) (aOf G)) (brGraph G (gN kf (Kf 0) (aOf G)) y) :
        Net (3 * kN kf (Kf 0) (aOf G) ^ 8)).U)
      (size (ctxF pk kf (Kf 0) (aOf G, y))) (e l) hK2 hup hlo
      he0 (hL.e_le l) heK (card_edge_le G) (hmu.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmH) _))
      (hU.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hmH n)) _)) hP hB hτ hS
    have hAm := Real.rpow_le_rpow_of_exponent_le one_le_two
      (Xp_mono (n := n) (m := G.edgeFinset.card) (by omega : A₁ + 1 ≤ A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30)))
    have hAm' := Real.rpow_le_rpow_of_exponent_le one_le_two
      (Xp_mono (n := n) (m := G.edgeFinset.card) hA1)
    have hr := Stepped.ite_runs_false (p := fun p : GIn × ℕ => badW (gN kf (Kf 0) p.1) p)
      (M := Stepped.const (0 : ℤ)) (a := (aOf G, y)) hb'
      (Stepped.mapIn_runs (f := fun p : GIn × ℕ => (ctxF pk kf (Kf 0) p,
        ginF pk (ctxF pk kf (Kf 0) p) (kN kf (Kf 0) p.1))) (M := GM pk E (argF kf (Kf 0)))
        (a := (aOf G, y)) hrun)
    unfold bodyM2
    refine ⟨3 * T, hr.mono le_rfl (Nat.le_floor ?_), Nat.le_floor ?_⟩
    · have := (add_one_le_Xp hb2).trans hAm
      exact_mod_cast this
    · have := (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 3)).trans (hb1.trans hAm')
      exact_mod_cast this

end Body

/-! ## The whole machine on one graph -/

section Whole

theorem div_mul_le_three (m n : ℕ) : m / n * (n + 2) ≤ 3 * m := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have h1 : m / n * n ≤ m := Nat.div_mul_le_self m n
    have h2 : m / n * 2 ≤ 2 * m := by
      have : m / n ≤ m := Nat.div_le_self m n
      omega
    nlinarith

theorem edge_le_D {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ (G.edgeFinset.card / n + 1) * n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; have := card_edge_le G; simp at this ⊢; omega
  · have := Nat.lt_div_mul_add (a := G.edgeFinset.card) hpos
    rw [add_mul, one_mul]; omega

/-- The number of branches: `2^{O((m+n)/√log n)}`. -/
theorem nBr_le_Xp {n K c₁ k₀ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hK : 2 ≤ K)
    (hup : K ^ 30 ≤ k₀ * (n + 2)) (hlo : n + 2 ≤ K ^ c₁) :
    (nBr (3 * K ^ 8) (aOf G) : ℝ) ≤ (2 : ℝ) ^ Xp (36 * (c₁ ^ 2 * k₀)) n G.edgeFinset.card := by
  set m := G.edgeFinset.card with hmd
  set D := m / n + 1 with hD
  have hg1 : 1 ≤ 3 * K ^ 8 := by have := Nat.one_le_pow 8 K (by omega); omega
  have h1 := nBr_le G hg1 (edge_le_D G)
  rw [← hmd, ← hD] at h1
  have h2 : (nBr (3 * K ^ 8) (aOf G) : ℝ) ≤ ((n : ℝ) + 2) ^ (4 * D * (3 * K ^ 8)) := by exact_mod_cast h1
  rw [pow_eq_two_rpow] at h2
  refine h2.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (le_Xp ?_))
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hs := sq_le_K (by omega) hlo
  have hΛ := Lam_le_K (by omega) hlo
  have hs0 := sq_pos n
  have hΛ0 : 0 ≤ Lam n := by linarith [one_le_Lam n]
  have hc : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg _
  have hΛs : Lam n * sq n ≤ (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
    calc Lam n * sq n ≤ (c₁ * K) * (c₁ * K) := by gcongr
      _ = _ := by ring
  have h30 : (K : ℝ) ^ 30 ≤ k₀ * ((n : ℝ) + 2) := by exact_mod_cast hup
  have h10 : (K : ℝ) ^ 10 ≤ (K : ℝ) ^ 30 := pow_le_pow_right₀ hKr (by norm_num)
  have hDn : (D : ℝ) * ((n : ℝ) + 2) ≤ 3 * ((m : ℝ) + n + 2) := by
    have := div_mul_le_three m n
    have h : ((m / n * (n + 2) : ℕ) : ℝ) ≤ ((3 * m : ℕ) : ℝ) := by exact_mod_cast this
    rw [hD]; push_cast at h ⊢; nlinarith
  have hk0 : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  calc ((4 * D * (3 * K ^ 8) : ℕ) : ℝ) * Lam n * sq n
      = 12 * D * ((K : ℝ) ^ 8 * (Lam n * sq n)) := by push_cast; ring
    _ ≤ 12 * D * ((K : ℝ) ^ 8 * ((c₁ : ℝ) ^ 2 * (K : ℝ) ^ 2)) := by gcongr
    _ = 12 * (c₁ : ℝ) ^ 2 * D * (K : ℝ) ^ 10 := by ring
    _ ≤ 12 * (c₁ : ℝ) ^ 2 * D * (k₀ * ((n : ℝ) + 2)) := by gcongr; linarith
    _ = 12 * (c₁ : ℝ) ^ 2 * k₀ * (D * ((n : ℝ) + 2)) := by ring
    _ ≤ 12 * (c₁ : ℝ) ^ 2 * k₀ * (3 * ((m : ℝ) + n + 2)) := by gcongr
    _ = _ := by push_cast; ring

/-- `x ≤ 2^{X_A}`, `y ≤ 2^{X_B}` give `x + y ≤ 2^{X_{A+B+1}}`. -/
theorem add_le_Xp {x y : ℝ} {A B n m : ℕ} (hx : x ≤ (2 : ℝ) ^ Xp A n m) (hy : y ≤ (2 : ℝ) ^ Xp B n m) :
    x + y ≤ (2 : ℝ) ^ Xp (A + B + 1) n m := by
  have h1 : (2 : ℝ) ^ Xp A n m ≤ (2 : ℝ) ^ Xp (A + B) n m :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono (by omega))
  have h2 : (2 : ℝ) ^ Xp B n m ≤ (2 : ℝ) ^ Xp (A + B) n m :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono (by omega))
  have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ Xp 1 n m := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (one_le_Xp_one n m)
  rw [← Xp_add, Real.rpow_add two_pos]
  have : (0 : ℝ) ≤ (2 : ℝ) ^ Xp (A + B) n m := by positivity
  nlinarith

theorem mul_le_Xp {x y : ℝ} {A B n m : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ (2 : ℝ) ^ Xp A n m)
    (hy : y ≤ (2 : ℝ) ^ Xp B n m) : x * y ≤ (2 : ℝ) ^ Xp (A + B) n m := by
  rw [← Xp_add, Real.rpow_add two_pos]
  have : (0 : ℝ) ≤ (2 : ℝ) ^ Xp A n m := by positivity
  rcases le_total 0 y with hy0 | hy0
  · exact mul_le_mul hx hy hy0 this
  · have : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 hy0
    have : (0 : ℝ) ≤ (2 : ℝ) ^ Xp A n m * (2 : ℝ) ^ Xp B n m := by positivity
    linarith

theorem pow_le_Xp {x : ℝ} {A n m : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ (2 : ℝ) ^ Xp A n m) (k : ℕ) :
    x ^ k ≤ (2 : ℝ) ^ Xp (k * A) n m := by
  have : Xp (k * A) n m = k * Xp A n m := by unfold Xp; push_cast; ring
  rw [this, mul_comm, Real.rpow_mul_natCast (by norm_num)]
  exact pow_le_pow_left₀ hx0 hx k

theorem const_le_Xp (k n m : ℕ) : (k : ℝ) ≤ (2 : ℝ) ^ Xp k n m := by
  have h1 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast Nat.lt_two_pow_self.le
  refine h1.trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have := one_le_Xp_one n m
  have e : Xp k n m = k * Xp 1 n m := by unfold Xp; push_cast; ring
  rw [e]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

end Whole

section Machine2

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

/-- **The machine of Theorem 2 on every graph**: `#HC(G)` in binary, within `2^{A(m+n+2)/√log₂(n+2)}`
steps, on states of at most that size. -/
theorem hcM2_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ T S : ℕ,
      (hcM2 pk E kf (Kf 0)).Runs (code G) T S (Nat.bits (hamCycles G).card) ∧
        (T : ℝ) ≤ (2 : ℝ) ^ Xp A n G.edgeFinset.card ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A n G.edgeFinset.card := by
  obtain ⟨Ab, hAb⟩ := body2_runs pk hC₁ hL hk E hsol he
  have hQ : ∃ A, ∀ n, Pol A n ((2 * (n + 1 + n * n) + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) +
      ((n + 2) * (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2))) + n + n * n + 1) +
      (2 * (n + 1 + n * n) + 1 + (n + n * n + 1)) + (2 * (n * n + 1) + 1) + 4) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.add
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)))
        (Pol.const 1))
      (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
        (Pol.add (Pol.mul (Pol.const 2) (Pol.mul Pol.id Pol.id)) (Pol.const 1))))
      (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 2))
        (Pol.mul (Pol.mul (Pol.const 4) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1)))
          (Pol.mul (Pol.const (3 * (Kf 0 ^ 30))) (Pol.add Pol.id (Pol.const 2))))) Pol.id) (Pol.mul Pol.id Pol.id))
        (Pol.const 1)))
      (Pol.add (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)))
        (Pol.const 1)) (Pol.add (Pol.add Pol.id (Pol.mul Pol.id Pol.id)) (Pol.const 1))))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1))) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨AQ, hAQ⟩ := hQ
  obtain ⟨AN, hAN⟩ : ∃ x, x = 36 * ((30 * C₀ + 1) ^ 2 * (Kf 0 ^ 30)) := ⟨_, rfl⟩
  obtain ⟨AP, hAP⟩ : ∃ x, x = 2 * AQ * ((30 * C₀ + 1) ^ 2 * (Kf 0 ^ 30)) := ⟨_, rfl⟩
  refine ⟨(AN + (Ab + 1) + 2 + 1) + ((AP + (AN + 1 + 1) + 1) + Ab + 1), fun {n} G _ => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aOf G) (aOf_len G)
  rw [← hKl] at hK2 hup hlo
  have hg1 : 1 ≤ gN kf (Kf 0) (aOf G) := by
    have : 1 ≤ kN kf (Kf 0) (aOf G) ^ 8 := Nat.one_le_pow _ _ (by omega)
    simp only [gN]; omega
  -- the branches
  choose! t ht using fun y (hy : y < nBr (gN kf (Kf 0) (aOf G)) (aOf G)) => hAb G hy
  set m := G.edgeFinset.card with hmd
  set Sm := ⌊(2 : ℝ) ^ Xp Ab n m⌋₊ with hSm
  set N := nBr (gN kf (Kf 0) (aOf G)) (aOf G) with hN
  have hNR : (N : ℝ) ≤ (2 : ℝ) ^ Xp AN n m := hAN ▸ nBr_le_Xp G hK2 hup hlo
  have hNle : N ≤ (n + 2) ^ (4 * (m / n + 1) * gN kf (Kf 0) (aOf G)) := nBr_le G hg1 (edge_le_D G)
  set v : ℕ → ℤ := fun y => (n : ℤ) * ((hamCycles (brGraph G (gN kf (Kf 0) (aOf G)) y)).card : ℤ) with hv
  have hV : ∀ y < N, (v y).natAbs ≤ n * 2 ^ (n * n) := fun y _ => by
    simp only [hv, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (card_hamCycles_le _)
  have hsum := Stepped.sumRange_runs (M := bodyM2 pk E kf (Kf 0)) (N := fun a => nBr (gN kf (Kf 0) a) a)
    (a := aOf G) t v (n * 2 ^ (n * n)) Sm (fun y hy => (ht y hy).1) hV
  have hval : ∑ y ∈ range N, v y = (n : ℤ) * ((hamCycles G).card : ℤ) := by
    simp only [hv, ← Finset.mul_sum]
    rw [← Nat.cast_sum, sum_branches G _]
  rw [hval] at hsum
  have hmain : (mainM2 pk E kf (Kf 0)).Runs (code G) _ _ ((n : ℤ) * ((hamCycles G).card : ℤ)) :=
    Stepped.mapIn_runs (f := read1) (by rw [read1_code]; exact hsum)
  have hfin := Stepped.ofFun_runs finW (code G, (n : ℤ) * ((hamCycles G).card : ℤ))
  have hout : finW (code G, (n : ℤ) * ((hamCycles G).card : ℤ)) = Nat.bits (hamCycles G).card := by
    unfold finW
    congr 1
    simp only [code, GraphProblems.Read.ones_unary_append]
    rw [show ((n : ℤ) * ((hamCycles G).card : ℤ)).toNat = n * (hamCycles G).card by
      rw [← Nat.cast_mul, Int.toNat_natCast]]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [hamCycles_eq_empty (Or.inl (by norm_num))]
      simp
    · exact Nat.mul_div_cancel_left _ h0
  rw [hout] at hfin
  have hrun := Stepped.bind_runs hmain hfin
  refine ⟨_, _, hrun, ?_, ?_⟩
  · -- the steps
    have ht1 : ∀ y ∈ range N, t y + 1 ≤ Sm + 1 := fun y hy => by
      have := (ht y (mem_range.1 hy)).2; omega
    have hsumT : ∑ y ∈ range N, (t y + 1) ≤ N * (Sm + 1) := by
      have := Finset.sum_le_sum ht1
      simpa [sum_const, card_range, smul_eq_mul] using this
    have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n m := Nat.floor_le (by positivity)
    have h1 : (Sm : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (Ab + 1) n m := add_one_le_Xp hSmR
    have h2 : (N : ℝ) * ((Sm : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (AN + (Ab + 1)) n m :=
      mul_le_Xp (Nat.cast_nonneg _) hNR h1
    have h3 : (N : ℝ) * ((Sm : ℝ) + 1) + 2 ≤ (2 : ℝ) ^ Xp (AN + (Ab + 1) + 2 + 1) n m :=
      add_le_Xp h2 (by exact_mod_cast const_le_Xp 2 n m)
    have h4 : (((∑ y ∈ range N, (t y + 1)) + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) * ((Sm : ℝ) + 1) + 2 := by
      have : (((∑ y ∈ range N, (t y + 1)) : ℕ) : ℝ) ≤ ((N * (Sm + 1) : ℕ) : ℝ) := by exact_mod_cast hsumT
      push_cast at this ⊢; linarith
    refine h4.trans (h3.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono ?_)))
    omega
  · -- the states
    have hD : m / n + 1 ≤ n * n + 1 := by
      have := Nat.div_le_self m n
      have := card_edge_le G
      omega
    have hgK : gN kf (Kf 0) (aOf G) ≤ 3 * (Kf 0 ^ 30) * (n + 2) := by
      have : kN kf (Kf 0) (aOf G) ^ 8 ≤ kN kf (Kf 0) (aOf G) ^ 30 := Nat.pow_le_pow_right (by omega) (by norm_num)
      simp only [gN]; nlinarith
    have h1 : size (code G) = 2 * (n + 1 + n * n) + 1 := by
      rw [LabelSystem.size_word, length_code stMatrixLength]
    have h2 := size_aOf G
    have h3 : size N ≤ N + 1 := size_nat_le' _
    have h4 : size (N * (n * 2 ^ (n * n))) ≤ (n + 2) * (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2))) + n + n * n + 1 := by
      apply size_nat_of_lt
      have hE : 4 * (m / n + 1) * gN kf (Kf 0) (aOf G) ≤ 4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 hD) hgK
      have e1 : (n + 2) ^ (4 * (m / n + 1) * gN kf (Kf 0) (aOf G)) ≤
          2 ^ ((n + 2) * (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2)))) :=
        calc (n + 2) ^ (4 * (m / n + 1) * gN kf (Kf 0) (aOf G))
            ≤ (n + 2) ^ (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2))) := Nat.pow_le_pow_right (by omega) hE
          _ ≤ (2 ^ (n + 2)) ^ (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2))) :=
              Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = _ := (pow_mul _ _ _).symm
      have e2 : n < 2 ^ n := Nat.lt_two_pow_self
      calc N * (n * 2 ^ (n * n)) ≤ 2 ^ ((n + 2) * (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2)))) * (n * 2 ^ (n * n)) :=
            Nat.mul_le_mul_right _ (hNle.trans e1)
        _ < 2 ^ ((n + 2) * (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2)))) * (2 ^ n * 2 ^ (n * n)) := by
            apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
            exact Nat.mul_lt_mul_of_pos_right e2 (by positivity)
        _ = _ := by rw [← pow_add, ← pow_add]; ring_nf
    have h5 : size ((n : ℤ) * ((hamCycles G).card : ℤ)) ≤ n + n * n + 1 := by
      apply size_int_of_lt
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast, pow_add]
      calc n * (hamCycles G).card ≤ n * 2 ^ (n * n) := Nat.mul_le_mul_left _ (card_hamCycles_le G)
        _ < 2 ^ n * 2 ^ (n * n) := Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by positivity)
    have h6 : size (Nat.bits (hamCycles G).card) ≤ 2 * (n * n + 1) + 1 := by
      rw [LabelSystem.size_word, Nat.size_eq_bits_len]
      have : (hamCycles G).card < 2 ^ (n * n + 1) := by
        rw [pow_succ]
        have := card_hamCycles_le G
        have : 0 < 2 ^ (n * n) := by positivity
        omega
      have := Nat.size_le.2 this
      omega
    have hpair : size (code G, (n : ℤ) * ((hamCycles G).card : ℤ)) =
        size (code G) + size ((n : ℤ) * ((hamCycles G).card : ℤ)) := rfl
    have hSnat : max (size (code G) + (size (aOf G) + size N + (size (N * (n * 2 ^ (n * n))) + Sm) + 1))
        (max (size (code G, (n : ℤ) * ((hamCycles G).card : ℤ))) (size (Nat.bits (hamCycles G).card)) + 1) + 1 ≤
        ((2 * (n + 1 + n * n) + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) +
          ((n + 2) * (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2))) + n + n * n + 1) +
          (2 * (n + 1 + n * n) + 1 + (n + n * n + 1)) + (2 * (n * n + 1) + 1) + 4) + (N + 1) + Sm := by
      rw [hpair]
      simp only [max_def]
      split_ifs <;> omega
    have hP := pol_le_Xp (m := m) hK2 hup hlo (hAQ n)
    rw [← hAP] at hP
    have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n m := Nat.floor_le (by positivity)
    have hN1 : (N : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (AN + 1 + 1) n m :=
      (add_le_Xp hNR (by exact_mod_cast const_le_Xp 1 n m))
    have hall := add_le_Xp (add_le_Xp hP hN1) hSmR
    have hcast : ((max (size (code G) + (size (aOf G) + size N + (size (N * (n * 2 ^ (n * n))) + Sm) + 1))
        (max (size (code G, (n : ℤ) * ((hamCycles G).card : ℤ))) (size (Nat.bits (hamCycles G).card)) + 1) + 1 : ℕ) : ℝ) ≤
        (((2 * (n + 1 + n * n) + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) +
          ((n + 2) * (4 * (n * n + 1) * (3 * (Kf 0 ^ 30) * (n + 2))) + n + n * n + 1) +
          (2 * (n + 1 + n * n) + 1 + (n + n * n + 1)) + (2 * (n * n + 1) + 1) + 4 : ℕ) : ℝ) + ((N : ℝ) + 1) + Sm := by
      have := (Nat.cast_le (α := ℝ)).2 hSnat
      push_cast at this ⊢; linarith
    refine hcast.trans (hall.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono ?_)))
    omega

end Machine2

/-- `2^{A(m+n+2)/s} ≤ 2^{2A} · 2^{A(m+n)/s}`. -/
theorem Xp_split (A n m : ℕ) :
    (2 : ℝ) ^ Xp A n m ≤ (2 : ℝ) ^ (2 * (A : ℝ)) * (2 : ℝ) ^ ((A : ℝ) * ((m : ℝ) + n) / sq n) := by
  rw [← Real.rpow_add two_pos]
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  unfold Xp
  have hs := one_le_sq n
  have hs0 := sq_pos n
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  rw [show (A : ℝ) * ((m : ℝ) + n + 2) / sq n = (A : ℝ) * ((m : ℝ) + n) / sq n + 2 * A / sq n by ring]
  have : 2 * (A : ℝ) / sq n ≤ 2 * A := div_le_self (by positivity) hs
  linarith

end T2

open T2 Asm EthFollowup.Hamiltonian in
/-- **Theorem 2, Turing-machine level, from a uniform HC network package.** Suppose that for some
absolute constant `c₀` there is ONE HC network package serving every number `g` of nodes
(`T2.UPackage c₀`: one context type, one set of procedures, one reader that is handed `g` in unary,
one absolute constant `q`). Then there are ONE Turing machine of Mathlib with finite alphabets and
ONE constant `C` such that, on the code of ANY graph `G` with `n` vertices and `m` edges
(`GraphProblems.code G`: `n` in unary, then the adjacency matrix), the machine halts within
`⌊C · 2^{C (m+n)/√(log₂(n+2))}⌋` steps with `#HC(G)` in binary (`Nat.bits`).

The route is that of §6.4 of `research/exact-hc-theorem.md`: the clique machine of Theorem A(b) on
the pieces of Theorem B (`CountedRoute.onTheCountedRecursion`, `e_ℓ ≤ (3x₀+6)/√log K_ℓ`), Lemma 8
case (i) (`ExplicitCost.groupingExplicit`, `ζ = 1/(2K)`, `g = 3K⁸`) with the network queries answered
by the package's procedures (`stPlug`), `K = K_ℓ` for the largest level with
`K_ℓ ≤ max(⌊n^{1/30}⌋, K₀)`, the branching of Lemma 6.1 with `Θ = n/g + 2` and the sum over the
branches, all in one `Stepped` machine (`T2.hcM2`), and `CountKSat.exists_tmW`. -/
theorem theorem2_TM (hpkg : ∃ c₀ : ℕ, Nonempty (UPackage c₀)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨c₀, ⟨pk⟩⟩ := hpkg
  obtain ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := geBody
  have hL := hyp.levels
  have hk := hyp.computesK
  obtain ⟨A, hA⟩ := hcM2_runs pk hC₁ hL hk _ hyp.solves (x₀ := x₀) fun l => he l
  obtain ⟨inst⟩ := hcM2_poly pk _ _ hL hk hyp.steps
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.exists_tmW (hcM2 pk (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)
    (CliqueLevels.levelsUnder x₀) (Levels.Gen.K x₀ 0))
  have hQ : ∃ A, ∀ n, Pol A n (n + 1 + n * n) :=
    ⟨_, fun n => Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)⟩
  obtain ⟨AL, hAL⟩ := hQ
  set c₁ := 30 * C₀ + 1
  set k₀ := Levels.Gen.K x₀ 0 ^ 30
  set Af := q + (A + 1) + q * (2 * AL * (c₁ ^ 2 * k₀) + A + 1 + 1) with hAf
  refine ⟨M, 2 ^ (2 * Af), hfin, fun n G _ => ?_⟩
  obtain ⟨T, S, hrun, hT, hS⟩ := hA G
  obtain ⟨ev⟩ := hM (GraphProblems.code G) T S _ hrun
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aOf G) (aOf_len G)
  rw [← hKl] at hK2 hup hlo
  set m := G.edgeFinset.card
  have hlen : (GraphProblems.code G).length = n + 1 + n * n := GraphProblems.length_code GraphProblems.stMatrixLength G
  have hLx : ((GraphProblems.code G).length : ℝ) ≤ (2 : ℝ) ^ Xp (2 * AL * (c₁ ^ 2 * k₀)) n m := by
    rw [hlen]; exact pol_le_Xp hK2 hup hlo (hAL n)
  have h1 : (T : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (A + 1) n m := add_one_le_Xp hT
  have h2 : ((GraphProblems.code G).length : ℝ) + S + 1 ≤
      (2 : ℝ) ^ Xp (2 * AL * (c₁ ^ 2 * k₀) + A + 1 + 1) n m :=
    add_one_le_Xp (add_le_Xp hLx hS)
  have h3 := pow_le_Xp (by positivity) h2 q
  have h4 : (q : ℝ) * ((T : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (q + (A + 1)) n m :=
    mul_le_Xp (Nat.cast_nonneg _) (const_le_Xp q n m) h1
  have h5 := mul_le_Xp (by positivity) h4 h3
  rw [← hAf] at h5
  have hle : q * (T + 1) * ((GraphProblems.code G).length + S + 1) ^ q ≤
      ⌊((2 ^ (2 * Af) : ℕ) : ℝ) * (2 : ℝ) ^ (((2 ^ (2 * Af) : ℕ) : ℝ) * ((m : ℝ) + n) /
        Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
    apply Nat.le_floor
    have e1 : ((q * (T + 1) * ((GraphProblems.code G).length + S + 1) ^ q : ℕ) : ℝ) =
        (q : ℝ) * ((T : ℝ) + 1) * (((GraphProblems.code G).length : ℝ) + S + 1) ^ q := by push_cast; ring
    rw [e1]
    refine h5.trans ((Xp_split Af n m).trans ?_)
    have hC : (Af : ℝ) ≤ ((2 ^ (2 * Af) : ℕ) : ℝ) := by
      have : Af ≤ 2 ^ (2 * Af) := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have e2 : (2 : ℝ) ^ (2 * (Af : ℝ)) = ((2 ^ (2 * Af) : ℕ) : ℝ) := by
      rw [show (2 : ℝ) * (Af : ℝ) = ((2 * Af : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]; push_cast; ring
    rw [e2, show Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) = T2.sq n from rfl]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : (0 : ℝ) ≤ (m : ℝ) + n := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC this) (T2.sq_pos n).le
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

open EthFollowup.Hamiltonian in
/-- **Theorem 2 in the form `2^{C·max(m,n)/√log n}`.** -/
theorem theorem2_TM_max (hpkg : ∃ c₀ : ℕ, Nonempty (T2.UPackage c₀)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * (max G.edgeFinset.card n : ℕ) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨M, C, hfin, hM⟩ := theorem2_TM hpkg
  refine ⟨M, 2 * C, hfin, fun n G _ => ?_⟩
  obtain ⟨ev⟩ := hM n G
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.floor_le_floor ?_)⟩⟩
  have hs : 0 < Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) := T2.sq_pos n
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hC2 : (C : ℝ) ≤ ((2 * C : ℕ) : ℝ) := by push_cast; linarith
  have hmax : ((G.edgeFinset.card : ℝ) + n) ≤ 2 * ((max G.edgeFinset.card n : ℕ) : ℝ) := by
    have : G.edgeFinset.card + n ≤ 2 * max G.edgeFinset.card n := by omega
    have h : ((G.edgeFinset.card + n : ℕ) : ℝ) ≤ ((2 * max G.edgeFinset.card n : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
    exact h
  have key : (C : ℝ) * ((G.edgeFinset.card : ℝ) + n) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) ≤
      ((2 * C : ℕ) : ℝ) * ((max G.edgeFinset.card n : ℕ) : ℝ) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) := by
    apply div_le_div_of_nonneg_right _ hs.le
    calc (C : ℝ) * ((G.edgeFinset.card : ℝ) + n) ≤ C * (2 * ((max G.edgeFinset.card n : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hmax hC
      _ = ((2 * C : ℕ) : ℝ) * ((max G.edgeFinset.card n : ℕ) : ℝ) := by push_cast; ring
  exact mul_le_mul hC2 (Real.rpow_le_rpow_of_exponent_le one_le_two key) (by positivity) (by positivity)

/-! ## The uniform package in the form of the label-sharing network (C1a, C1b) -/

open Groundwork Groundwork.Prog GraphProblems Eight.SecNetworks Printed Finset EthFollowup.Hamiltonian

/-- **A uniform HC network package in label-sharing form**: `LabelPackage` with ONE context type,
ONE reader `lay`, ONE parity procedure `par`, ONE table procedure `Tp` and ONE reader `prep`
(handed `g` in unary besides the graph code) for every number `g` of nodes, and ONE absolute
constant `q`; the bounds are polynomial in `n + g`, with `q g³` in `U` and `q g²` in `P`.
`toUPackage` turns it into a `T2.UPackage`. -/
structure ULabelPackage (c₀ : ℕ) : Type 1 where
  Ctx : Type
  [encCtx : Enc Ctx]
  [sizeCtx : HasSize Ctx]
  [carriedCtx : Carried Ctx]
  lay : Ctx → Lay
  lay_poly : PolyT lay
  par : Ctx × (ℕ × List Bool) → Bool
  par_poly : PolyT par
  Tp : Stepped (Ctx × WQ) ℤ
  Tp_poly : Nonempty (IsPolyT Tp)
  prep : List Unit × List Bool → Ctx
  prep_poly : PolyT prep
  q : ℕ
  K : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → Type
  R : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → Type
  L : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → Type
  fintypeK : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), Fintype (K g G)
  decEqK : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), DecidableEq (K g G)
  fintypeR : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), Fintype (R g G)
  decEqR : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), DecidableEq (R g G)
  fintypeL : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), Fintype (L g G)
  decEqL : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), DecidableEq (L g G)
  w : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  X : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), LabelSystem g (K g G) (R g G) (L g G)
  C : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), LabelCode (L g G) (w g G)
  P : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  B : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  τ : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  S : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  mu : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  P_pos : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → 1 ≤ P g G
  B_pos : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → 1 ≤ B g G
  τ_pos : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → 1 ≤ τ g G
  hP : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) →
    ∀ a, #(univ.filter ((X g G).Inc a)) * w g G + #(univ.filter ((X g G).Touch a)) ≤ P g G
  hT : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → ∀ a ℓ y, |(X g G).T a ℓ y| < 2 ^ B g G
  describes : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (X g G).Describes (C g G) (P g G) (B g G) (lay (prep (Printed.unary g, code G)))
  parSpec : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (X g G).ParSpec (C g G) par (prep (Printed.unary g, code G))
  tSpec : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (X g G).TSpec (C g G) Tp (prep (Printed.unary g, code G)) (τ g G) (S g G)
  value : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) →
    ∑ ℓ : K g G → L g G, ∏ a, (X g G).T a ℓ (fun j => (X g G).par j ℓ) = (n : ℤ) * ((hamCycles G).card : ℤ)
  mu_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) → g * mu g G ≤ 2 * G.edgeFinset.card + g * Δ
  U_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) →
    2 * (Fintype.card (K g G) * w g G + Fintype.card (R g G)) ≤ c₀ * (G.edgeFinset.card + n) + q * g ^ 3
  P_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → P g G ≤ c₀ * mu g G + q * g ^ 2
  B_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → B g G ≤ q * (n + g + 2) ^ q
  τ_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → τ g G ≤ 2 ^ (c₀ * mu g G) * (q * (n + g + 2) ^ q)
  S_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) →
    S g G + 2 * size (prep (Printed.unary g, code G)) + 2 * g + 4 * P g G + 8 ≤ q * (n + g + 2) ^ q

attribute [instance] ULabelPackage.encCtx ULabelPackage.sizeCtx ULabelPackage.carriedCtx
  ULabelPackage.fintypeK ULabelPackage.decEqK ULabelPackage.fintypeR ULabelPackage.decEqR
  ULabelPackage.fintypeL ULabelPackage.decEqL

namespace ULabelPackage

variable {c₀ : ℕ} (lp : ULabelPackage c₀)

/-- **From the label-sharing form to a uniform package**, by `labelProcs_given` (C1b), `net_is`,
`value_net` and `U_eq` (C1a), as `LabelPackage.toHCPackage`. -/
noncomputable def toUPackage : T2.UPackage c₀ where
  Ctx := lp.Ctx
  Np := labelProcs lp.lay lp.par lp.Tp
  keeps := labelProcs_keeps lp.lay_poly lp.par_poly lp.Tp_poly
  P_unary := Lay.P_unary lp.lay_poly
  B_unary := Lay.B_unary lp.lay_poly
  prep := lp.prep
  prep_poly := lp.prep_poly
  q := lp.q
  net g _ G := (lp.X g G).net (lp.C g G)
  P g _ G := lp.P g G
  B g _ G := lp.B g G
  τ g _ G := lp.τ g G
  S g _ G := lp.S g G + size (lp.prep (Printed.unary g, code G)) + 2 * g + 4 * lp.P g G + 8
  mu g _ G := lp.mu g G
  isNet g _ G _ hg h3 hd :=
    (labelProcs_given (lp.X g G) (lp.C g G) lp.lay_poly lp.par_poly lp.Tp_poly
      ((lp.X g G).net_is (lp.C g G) (lp.P_pos g G hg h3 hd) (lp.B_pos g G hg h3 hd) (lp.hP g G hg h3 hd)
        (lp.hT g G hg h3 hd))
      (lp.describes g G hg h3 hd) (lp.parSpec g G hg h3 hd) (lp.tSpec g G hg h3 hd) (lp.τ_pos g G hg h3 hd)).1
  value g _ G _ hg h3 hd := by rw [LabelSystem.value_net]; exact lp.value g G hg h3 hd
  mu_le g _ G _ hg h3 hd := lp.mu_le g G hg h3 hd
  U_le g _ G _ hg h3 hd := by rw [LabelSystem.U_eq]; exact lp.U_le g G hg h3 hd
  P_le g _ G _ hg h3 hd := lp.P_le g G hg h3 hd
  B_le g _ G _ hg h3 hd := lp.B_le g G hg h3 hd
  τ_le g _ G _ hg h3 hd := lp.τ_le g G hg h3 hd
  S_le g _ G _ hg h3 hd := by have := lp.S_le g G hg h3 hd; omega

end ULabelPackage

/-- **Theorem 2 (TM level) from a uniform label-sharing package.** -/
theorem theorem2_TM_of_label (hpkg : ∃ c₀ : ℕ, Nonempty (ULabelPackage c₀)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨c₀, h⟩ := hpkg
  exact theorem2_TM ⟨c₀, h.map ULabelPackage.toUPackage⟩

end EthFollowup.ExactHC
