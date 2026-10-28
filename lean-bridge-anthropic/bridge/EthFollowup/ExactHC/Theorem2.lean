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
    {c : pk.Ctx} {P B τ S : ℕ} (hN : IsNetwork pk.Np c N P B τ S) :
    ∃ T : ℕ, (GM pk E (argF kf (Kf 0))).Runs (c, ginF pk c K) (3 * T)
        (size c + (Tc (e l) K C₀ (Lc K (3 * K ^ 8) P N.U) (Bc K (3 * K ^ 8) P B) +
          (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1) N.value ∧
      (T : ℝ) ≤ ((K : ℝ) ^ (3 * K ^ 8) + Tc (e l) K C₀ (Lc K (3 * K ^ 8) P N.U)
          (Bc K (3 * K ^ 8) P B) * (2 : ℝ) ^ (2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K) * τ) *
        (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁ := by
  subst hKl
  exact net_runs pk hC₁ hL hk E hsol l hN

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

end T2

end EthFollowup.ExactHC
