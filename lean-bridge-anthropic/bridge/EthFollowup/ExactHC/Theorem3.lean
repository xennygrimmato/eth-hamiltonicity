/-
# Theorem 3 (thm:main-degree) at Turing-machine level, from a uniform degree package

`research/hc-degree-theorem.md` §4 (Algorithm A, §4.1–4.2); `paper/main.tex` §8 (`sec:degree`).
This file mirrors `Theorem2.lean` and reuses its level choice (`T2.kN`, `T2.gN`, `T2.kfacts`), its
Lemma 8 interface (`T2.GEBody`, `T2.plug_within`) and its exponent calculus (`T2.Xp`, `T2.Lam`,
`T2.sq`, …), with the *pseudo edge count* `Md n m = n·⌊log₂(m/n + 2)⌋` in the role of `m`.

**The hypothesis** `T3.DPackage c₀`: ONE context type, ONE set of procedures, ONE reader
`prep : (g in unary, (y, graph)) ↦ context`, ONE absolute constant `q`, a number `nPr g G` of
profile indices with a polynomial-time test `good g G y`, and for every `g ≥ 1`, every graph with
`n ≥ 3` and minimum degree `≥ 2` and every good index `y`: `IsNetwork Np (prep …) (net g G y) P B τ S`
with `g·ν ≤ n + g`, `U ≤ c₀(n·lgd + n) + q g³`, `P ≤ c₀·ν·lgN n + q g²`, `τ ≤ 2^{c₀ ν lgN n}·poly`,
`B, S, |value| ≤ poly`, `nPr ≤ (n+2)^{q g²}`, and `∑_{y good} value(net g G y) = n·#HC(G)`.
(`lgN n = ⌊log₂(n+2)⌋` is the per-vertex label budget `log Δ`, `lgd = ⌊log₂(m/n + 2)⌋` the
average-degree term; Proposition 3.2 of the note.)

**The machine** `T3.hcM3`: read `code G`; `K`, `g = 3K⁸` as in Theorem 2; for every profile index
`y < nPr`: `0` if `n ≤ 2`, a vertex has degree `< 2`, or `y` is not good; else Lemma 8 case (i)
with the clique machine on the network of `y`; add up, divide by `n`, write `Nat.bits`. No
branching (no Lemma 6.1).

**Main results.** `T3.branch_bound3` (one profile: `2^{A(Md+n+2)/√log₂(n+2)}`), `T3.hcM3_runs`,
`theorem3_TM_of_package`: ONE Turing machine and ONE `C` with
`Outputs M (code G) (Nat.bits #HC(G)) ⌊C·2^{C·n·log₂(2m/n + 2)/√(log₂(n+2))}⌋` for EVERY graph.
-/
import EthFollowup.ExactHC.Theorem2

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace T3

open Groundwork Groundwork.Prog GraphProblems Asm T2

/-! ## The package -/

open Eight.SecNetworks Printed Finset EthFollowup.Hamiltonian QueryMachines

/-- The per-vertex term `⌊log₂(n+2)⌋` (as `lgN` of `RankNetwork.lean`). -/
def lgN (n : ℕ) : ℕ := Nat.log 2 (n + 2)

/-- The average-degree term `⌊log₂(m/n + 2)⌋`. -/
def lgd (n m : ℕ) : ℕ := Nat.log 2 (m / n + 2)

/-- The pseudo edge count `n·⌊log₂(m/n + 2)⌋` that replaces `m` in the exponent of Theorem 2. -/
def Md (n m : ℕ) : ℕ := n * lgd n m

/-- **A uniform degree package** (the hypothesis of Theorem 3), with the absolute constant `c₀`. -/
structure DPackage (c₀ : ℕ) : Type 1 where
  Ctx : Type
  [encCtx : Enc Ctx]
  [sizeCtx : HasSize Ctx]
  [carriedCtx : Carried Ctx]
  Np : Procs Ctx
  keeps : Np.Keeps
  P_unary : Unary Np.P
  B_unary : Unary Np.B
  /-- The reader: `(g in unary, (profile index, graph)) ↦ context`. -/
  prep : List Unit × (ℕ × GIn) → Ctx
  prep_poly : PolyT prep
  /-- The number of profile indices. -/
  nPr : ℕ → GIn → ℕ
  nPr_poly : PolyT fun p : List Unit × GIn => nPr p.1.length p.2
  /-- The test of a profile index (admissible profile). -/
  good : ℕ → GIn → ℕ → Bool
  good_poly : PolyT fun p : (List Unit × GIn) × ℕ => good p.1.1.length p.1.2 p.2
  q : ℕ
  net : ∀ (g : ℕ) {n : ℕ}, SimpleGraph (Fin n) → ℕ → Net g
  P : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  B : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  τ : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  S : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  nu : ℕ → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  isNet : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → ∀ y, y < nPr g (aOf G) → good g (aOf G) y = true →
    IsNetwork Np (prep (Printed.unary g, (y, aOf G))) (net g G y) (P g G) (B g G) (τ g G) (S g G)
  value : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) →
    ∑ y ∈ range (nPr g (aOf G)), (if good g (aOf G) y = true then (net g G y).value else 0) =
      (n : ℤ) * ((hamCycles G).card : ℤ)
  value_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → ∀ y, y < nPr g (aOf G) → good g (aOf G) y = true →
    (net g G y).value.natAbs < 2 ^ (q * (n + g + 2) ^ q)
  nPr_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)), 1 ≤ g → nPr g (aOf G) ≤ (n + 2) ^ (q * g ^ 2)
  nu_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → g * nu g G ≤ n + g
  U_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → ∀ y, y < nPr g (aOf G) → good g (aOf G) y = true →
    (net g G y).U ≤ c₀ * (Md n G.edgeFinset.card + n) + q * g ^ 3
  P_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → P g G ≤ c₀ * (nu g G * lgN n) + q * g ^ 2
  B_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → B g G ≤ q * (n + g + 2) ^ q
  τ_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → τ g G ≤ 2 ^ (c₀ * (nu g G * lgN n)) * (q * (n + g + 2) ^ q)
  S_le : ∀ (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ g → 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → ∀ y, y < nPr g (aOf G) → good g (aOf G) y = true →
    S g G + size (prep (Printed.unary g, (y, aOf G))) ≤ q * (n + g + 2) ^ q

attribute [instance] DPackage.encCtx DPackage.sizeCtx DPackage.carriedCtx

variable {c₀ : ℕ} (pk : DPackage c₀)

/-! ## One network -/

/-- The input of Lemma 8 written from the context. -/
def ginF (c : pk.Ctx) (k : ℕ) : ExplicitCost.GroupingInput :=
  ((1, 2 * k), ((unary k, unary (3 * k ^ 8)),
    inputOf (3 * k ^ 8) (pk.Np.P c) (pk.Np.B c) (pk.Np.len c) (pk.Np.cap c)))

/-- Lemma 8's procedure with the clique machine `E`, its queries answered by the procedures. -/
def GM {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : ExplicitCost.CliqueInput → α) :
    Stepped (pk.Ctx × ExplicitCost.GroupingInput) ℤ :=
  (ExplicitCost.groupingData E arg).plug (answerOf pk.Np)

/-- **One network** (as `T2.net_runs`). -/
theorem net_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {kf : List Unit × List Unit → Option (List Unit)}
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
  have hK2 : 2 ≤ Kf l := hL.K_two l
  have hg2 : 2 ≤ 3 * Kf l ^ 8 := by
    have : 1 ≤ Kf l ^ 8 := Nat.one_le_pow _ _ (by omega)
    omega
  have hP1 := hN.is.P_pos
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
    have : 1 ≤ (3 * Kf l ^ 8) ^ 2 * B := Nat.one_le_iff_ne_zero.2 (by have := hN.is.B_pos; positivity)
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

/-! ## The machine of Theorem 3 -/

section Machine

variable (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
  (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- The context of the profile index `y` of the graph `a`. -/
def ctxF (p : GIn × ℕ) : pk.Ctx := pk.prep (unary (gN kf K₀ p.1), (p.2, p.1))

/-- The graph is bad (`n ≤ 2` or a vertex of degree `< 2`), or the index is not good. -/
def bad3 (p : GIn × ℕ) : Bool :=
  decide (p.1.1.length ≤ 2) || (List.range p.1.1.length).any (fun v => decide (degW p.1 v < 2)) ||
    !pk.good (gN kf K₀ p.1) p.1 p.2

/-- One profile index: `0` if bad, else Lemma 8 on its network. -/
def bodyM3 : Stepped (GIn × ℕ) ℤ :=
  Stepped.ite (bad3 pk kf K₀) (Stepped.const 0)
    (Stepped.mapIn (fun p => (ctxF pk kf K₀ p, ginF pk (ctxF pk kf K₀ p) (kN kf K₀ p.1)))
      (GM pk E (argF kf K₀)))

/-- The sum over the profile indices: `n · #HC(G)`. -/
def mainM3 : Stepped (List Bool) ℤ :=
  Stepped.mapIn read1 (Stepped.sumRange (fun a => pk.nPr (gN kf K₀ a) a) (bodyM3 pk E kf K₀))

/-- **The machine of Theorem 3.** -/
def hcM3 : Stepped (List Bool) (List Bool) := Stepped.bind (mainM3 pk E kf K₀) (Stepped.ofFun finW)

variable {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem ctxF_polyT (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    PolyT (ctxF pk kf (Kf 0)) := by
  have hu : PolyT fun p : GIn × ℕ => Printed.unary (gN kf (Kf 0) p.1) :=
    (gN_unary kf hL hk).comp PolyT.id'.fst
  exact pk.prep_poly.comp (PolyT.prodMk hu (PolyT.prodMk PolyT.id'.snd PolyT.id'.fst))

theorem bad3_polyT (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    PolyT (bad3 pk kf (Kf 0)) := by
  have hu : PolyT fun p : GIn × ℕ => Printed.unary (gN kf (Kf 0) p.1) :=
    (gN_unary kf hL hk).comp PolyT.id'.fst
  have hg : PolyT fun p : GIn × ℕ => pk.good (gN kf (Kf 0) p.1) p.1 p.2 := by
    have := pk.good_poly.comp (PolyT.prodMk (PolyT.prodMk hu PolyT.id'.fst) PolyT.id'.snd)
    refine this.congr fun p => ?_
    simp [Printed.unary]
  have hr := range_polyT (α := GIn × ℕ) (a := fun p => p.1) (by fun_prop)
  have hd : PolyT fun q : (GIn × ℕ) × ℕ => decide (degW q.1.1 q.2 < 2) := by fun_prop
  unfold bad3; fun_prop

theorem nPrF_polyT (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    PolyT fun a : GIn => pk.nPr (gN kf (Kf 0) a) a := by
  have hu : PolyT fun a : GIn => Printed.unary (gN kf (Kf 0) a) := gN_unary kf hL hk
  have := pk.nPr_poly.comp (PolyT.prodMk hu PolyT.id')
  refine this.congr fun a => ?_
  simp [Printed.unary]

theorem hcM3_poly (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf)
    (hE : E.PolyTimeSteps) : Nonempty (IsPolyT (hcM3 pk E kf (Kf 0))) := by
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
  have : IsPolyT (bodyM3 pk E kf (Kf 0)) := IsPolyT.ite (bad3_polyT pk kf hL hk)
  have : IsPolyT (Stepped.sumRange (fun a => pk.nPr (gN kf (Kf 0) a) a) (bodyM3 pk E kf (Kf 0))) :=
    IsPolyT.sumRange (nPrF_polyT pk kf hL hk)
  have : IsPolyT (mainM3 pk E kf (Kf 0)) := IsPolyT.mapIn stCertRead.1
  have : IsPolyT (Stepped.ofFun finW) := IsPolyT.ofFun finW_polyT
  exact ⟨IsPolyT.bind⟩

end Machine


/-! ## The exponent: the per-vertex term -/

section Real3

theorem lgN_le_Lam (n : ℕ) : (lgN n : ℝ) ≤ Lam n := by
  unfold lgN Lam
  have h : 2 ^ Nat.log 2 (n + 2) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have h' : (2 : ℝ) ^ (Nat.log 2 (n + 2) : ℝ) ≤ (n : ℝ) + 2 := by
    rw [Real.rpow_natCast]; exact_mod_cast h
  rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity)]
  exact h'

theorem lgN_nonneg (n : ℕ) : (0 : ℝ) ≤ lgN n := Nat.cast_nonneg _

/-- `(log₂ K)² ≤ 9K`. -/
theorem logb_sq_le (K : ℕ) (hK : 1 ≤ K) : Real.logb 2 K ^ 2 ≤ 9 * K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK0
  have h1 : Real.log (Real.sqrt K) ≤ Real.sqrt K := by
    have := Real.log_le_sub_one_of_pos hs; linarith
  have h2 : Real.log K = 2 * Real.log (Real.sqrt K) := by
    rw [Real.log_sqrt hK0.le]; ring
  have hl2 := Real.log_two_gt_d9
  have hl0 : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have h3 : Real.logb 2 K ≤ 3 * Real.sqrt K := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h4 : 0 ≤ Real.logb 2 K := div_nonneg hl0 (by linarith)
  calc Real.logb 2 K ^ 2 ≤ (3 * Real.sqrt K) ^ 2 := pow_le_pow_left₀ h4 h3 2
    _ = 9 * K := by rw [mul_pow, Real.sq_sqrt hK0.le]; ring

/-- `lgN n · √(log₂(n+2)) ≤ 9c₁²K` when `n + 2 ≤ K^{c₁}`. -/
theorem lgN_sq_le {n K c₁ : ℕ} (hK : 1 ≤ K) (h : n + 2 ≤ K ^ c₁) :
    (lgN n : ℝ) * T2.sq n ≤ 9 * (c₁ : ℝ) ^ 2 * K := by
  have h1 := lgN_le_Lam n
  have h2 := sq_le_Lam n
  have h3 := Lam_le_logb hK h
  have h0 := lgN_nonneg n
  have hs0 := (sq_pos n).le
  have hl : 0 ≤ Real.logb 2 K := Real.logb_nonneg one_lt_two (by exact_mod_cast hK)
  have hΛ0 : 0 ≤ Lam n := by linarith [one_le_Lam n]
  have h4 := logb_sq_le K hK
  have hc : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg _
  calc (lgN n : ℝ) * T2.sq n ≤ Lam n * Lam n := mul_le_mul h1 h2 hs0 hΛ0
    _ ≤ (c₁ * Real.logb 2 K) * (c₁ * Real.logb 2 K) := mul_le_mul h3 h3 hΛ0 (by positivity)
    _ = (c₁ : ℝ) ^ 2 * Real.logb 2 K ^ 2 := by ring
    _ ≤ (c₁ : ℝ) ^ 2 * (9 * K) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

theorem lgN_le (n : ℕ) : lgN n ≤ n + 2 := (Nat.log_lt_self 2 (by omega)).le

end Real3

/-! ## One profile index: the bounds -/

section Branch

/-- Polynomial bounds of the numbers of one network. -/
theorem branch_pol3 (c₀ q k₀ : ℕ) : ∃ A₀ : ℕ, ∀ (n M K nu P B U : ℕ), 1 ≤ K → K ^ 30 ≤ k₀ * (n + 2) →
    M ≤ (n + 2) * (n + 2) → 3 * K ^ 8 * nu ≤ n + 3 * K ^ 8 →
    U ≤ c₀ * (M + n) + q * (3 * K ^ 8) ^ 3 → P ≤ c₀ * (nu * lgN n) + q * (3 * K ^ 8) ^ 2 →
    B ≤ q * (n + 3 * K ^ 8 + 2) ^ q →
    Pol A₀ n (K * (Lc K (3 * K ^ 8) P U + Bc K (3 * K ^ 8) P B)) ∧
    Pol A₀ n (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ∧ Pol A₀ n (q * (n + 3 * K ^ 8 + 2) ^ q) := by
  let Gb : ℕ → ℕ := fun n => 3 * k₀ * (n + 2)
  let Kb : ℕ → ℕ := fun n => k₀ * (n + 2)
  let μb : ℕ → ℕ := fun n => (n + Gb n) * (n + 2)
  let Ub : ℕ → ℕ := fun n => c₀ * ((n + 2) * (n + 2) + n) + q * Gb n ^ 3
  let Pb : ℕ → ℕ := fun n => c₀ * μb n + q * Gb n ^ 2
  let Bb : ℕ → ℕ := fun n => q * (n + Gb n + 2) ^ q
  have pG : ∃ A, ∀ n, Pol A n (Gb n) :=
    ⟨_, fun n => Pol.mul (Pol.const (3 * k₀)) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨aG, hG⟩ := pG
  have pK : ∃ A, ∀ n, Pol A n (Kb n) :=
    ⟨_, fun n => Pol.mul (Pol.const k₀) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨aK, hK⟩ := pK
  have pμ : ∃ A, ∀ n, Pol A n (μb n) :=
    ⟨_, fun n => Pol.mul (Pol.add Pol.id (hG n)) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨aμ, hμ⟩ := pμ
  have pU : ∃ A, ∀ n, Pol A n (Ub n) :=
    ⟨_, fun n => Pol.add (Pol.mul (Pol.const c₀) (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 2))
      (Pol.add Pol.id (Pol.const 2))) Pol.id)) (Pol.mul (Pol.const q) (Pol.pow (hG n) 3))⟩
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
  refine ⟨a1 + a2 + aB, fun n M K nu P B U hK1 hup hM hnu hUle hPle hBle => ?_⟩
  have hKK : K ≤ Kb n := by
    have : K ≤ K ^ 30 := Nat.le_self_pow (by norm_num) K
    exact this.trans hup
  have hgK : 3 * K ^ 8 ≤ Gb n := by
    have : K ^ 8 ≤ K ^ 30 := Nat.pow_le_pow_right hK1 (by norm_num)
    show 3 * K ^ 8 ≤ 3 * k₀ * (n + 2)
    rw [mul_assoc]; exact Nat.mul_le_mul_left 3 (this.trans hup)
  have hg1 : 1 ≤ 3 * K ^ 8 := by have := Nat.one_le_pow 8 K hK1; omega
  have hmu' : nu * lgN n ≤ μb n := by
    have h3 : nu ≤ 3 * K ^ 8 * nu := Nat.le_mul_of_pos_left nu (by omega)
    exact Nat.mul_le_mul (by omega) (lgN_le n)
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

set_option maxHeartbeats 1600000 in
/-- The exponent of one profile index against `A (M+n+2)/√(log₂(n+2))`, multiplied out. -/
theorem core_exp3 {n M K nu P U A₀ c₀ q C₀ C₁ x₀ k₀ c₁ : ℕ} {e L : ℝ} (hK2 : 2 ≤ K)
    (hup : K ^ 30 ≤ k₀ * (n + 2)) (hlo : n + 2 ≤ K ^ c₁) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (heK : e ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 K))
    (hnu : 3 * K ^ 8 * nu ≤ n + 3 * K ^ 8)
    (hU : U ≤ c₀ * (M + n) + q * (3 * K ^ 8) ^ 3) (hP : P ≤ c₀ * (nu * lgN n) + q * (3 * K ^ 8) ^ 2)
    (hKL : (K : ℝ) ^ 2 * L ≤ U + 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) :
    (3 + ((K * (3 * K ^ 8) : ℕ) : ℝ) + (e * (K : ℝ) ^ 2 * L + 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) +
      2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K + ((c₀ * (nu * lgN n) : ℕ) : ℝ) + 2 * A₀ * Lam n) +
        2 * A₀ * Lam n * C₁) * T2.sq n ≤
      (((3 + 3 + 27 * q + 81 * q + 1) * (c₁ * k₀) + c₀ * ((3 * x₀ + 6) * c₁) + 36 * c₀ * c₁ ^ 2 +
        81 * c₀ * c₁ ^ 2 * k₀ + 9 * c₀ * c₁ ^ 2 * k₀ +
        (2 * A₀ * C₀ + 2 * A₀ + 2 * A₀ * C₁) * (c₁ ^ 2 * k₀) : ℕ) : ℝ) * ((M : ℝ) + n + 2) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hK0 : (0 : ℝ) < K := by linarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (M : ℝ) + n + 2 := ⟨_, rfl⟩
  rw [← hY]
  have hY0 : (0 : ℝ) ≤ Y := by rw [hY]; positivity
  have hs0 := sq_pos n
  have hc₀ : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hk₀ : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
  have hc₁ : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg _
  set lg : ℝ := (lgN n : ℝ) with hlg
  have hlg0 : 0 ≤ lg := lgN_nonneg n
  have hLs : lg * T2.sq n ≤ 9 * (c₁ : ℝ) ^ 2 * K := lgN_sq_le (by omega) hlo
  obtain ⟨pj, -, pΛ, pK2Λ⟩ := prod_facts (m := M) hK2 hup hlo
  simp only [← hY] at pj pΛ pK2Λ
  have he := e_sq_le hK2 hlo he0 (Nat.cast_nonneg _) heK
  have h30 : (K : ℝ) ^ 30 ≤ k₀ * Y := by
    have : ((K ^ 30 : ℕ) : ℝ) ≤ ((k₀ * (n + 2) : ℕ) : ℝ) := by exact_mod_cast hup
    push_cast at this
    have : (0 : ℝ) ≤ k₀ * (M : ℝ) := by positivity
    rw [hY]; nlinarith
  have hK8Y : (K : ℝ) ^ 8 ≤ k₀ * Y := (pow_le_pow_right₀ hK1 (by norm_num)).trans h30
  have hKY : (K : ℝ) ≤ k₀ * Y := by
    have := pow_le_pow_right₀ hK1 (show 1 ≤ 30 by norm_num); rw [pow_one] at this; linarith
  have hnY : (n : ℝ) ≤ Y := by rw [hY]; have : (0 : ℝ) ≤ M := Nat.cast_nonneg _; linarith
  -- the real forms of the hypotheses
  have hnur : 3 * (K : ℝ) ^ 8 * nu ≤ n + 3 * (K : ℝ) ^ 8 := by exact_mod_cast hnu
  have hUr : (U : ℝ) ≤ c₀ * ((M : ℝ) + n) + 27 * q * (K : ℝ) ^ 24 := by
    have : (U : ℝ) ≤ ((c₀ * (M + n) + q * (3 * K ^ 8) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hU
    push_cast at this; nlinarith
  have hPr : (P : ℝ) ≤ c₀ * (nu * lg) + 9 * q * (K : ℝ) ^ 16 := by
    have : (P : ℝ) ≤ ((c₀ * (nu * lgN n) + q * (3 * K ^ 8) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hP
    push_cast at this; rw [hlg]; nlinarith
  -- `3K⁸P/K`
  have hgP : 3 * (K : ℝ) ^ 8 * P / K ≤ c₀ * ((n : ℝ) / K * lg) + 3 * c₀ * ((K : ℝ) ^ 7 * lg) +
      27 * q * (K : ℝ) ^ 23 := by
    have h1 : 3 * (K : ℝ) ^ 8 * P ≤ c₀ * ((n : ℝ) + 3 * (K : ℝ) ^ 8) * lg + 27 * q * (K : ℝ) ^ 24 := by
      calc 3 * (K : ℝ) ^ 8 * P ≤ 3 * (K : ℝ) ^ 8 * (c₀ * (nu * lg) + 9 * q * (K : ℝ) ^ 16) := by gcongr
        _ = c₀ * (3 * (K : ℝ) ^ 8 * nu) * lg + 27 * q * (K : ℝ) ^ 24 := by ring
        _ ≤ c₀ * ((n : ℝ) + 3 * (K : ℝ) ^ 8) * lg + 27 * q * (K : ℝ) ^ 24 := by gcongr
    rw [div_le_iff₀ hK0]
    have e1 : (c₀ * ((n : ℝ) / K * lg) + 3 * c₀ * ((K : ℝ) ^ 7 * lg) + 27 * q * (K : ℝ) ^ 23) * K =
        c₀ * ((n : ℝ) + 3 * (K : ℝ) ^ 8) * lg + 27 * q * (K : ℝ) ^ 24 := by field_simp
    rw [e1]; exact h1
  -- `ν ≤ n/K + 1`
  have hnuK : (nu : ℝ) ≤ (n : ℝ) / K + 1 := by
    have hg0 : (0 : ℝ) < 3 * (K : ℝ) ^ 8 := by positivity
    have hKg : (K : ℝ) ≤ 3 * (K : ℝ) ^ 8 := by
      have : (K : ℝ) ≤ (K : ℝ) ^ 8 := le_self_pow₀ hK1 (by norm_num)
      linarith
    have e0 : (nu : ℝ) ≤ (n : ℝ) / (3 * (K : ℝ) ^ 8) + 1 := by
      rw [div_add_one hg0.ne', le_div_iff₀ hg0]; linarith
    have e2 : (n : ℝ) / (3 * (K : ℝ) ^ 8) ≤ (n : ℝ) / K :=
      div_le_div_of_nonneg_left (by positivity) hK0 hKg
    linarith
  have hcmu : ((c₀ * (nu * lgN n) : ℕ) : ℝ) ≤ c₀ * ((n : ℝ) / K * lg) + c₀ * lg := by
    push_cast
    rw [← hlg]
    have : (nu : ℝ) * lg ≤ ((n : ℝ) / K + 1) * lg := mul_le_mul_of_nonneg_right hnuK hlg0
    calc (c₀ : ℝ) * ((nu : ℝ) * lg) ≤ c₀ * (((n : ℝ) / K + 1) * lg) := mul_le_mul_of_nonneg_left this hc₀
      _ = _ := by ring
  have heKL : e * (K : ℝ) ^ 2 * L ≤ e * U + 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2 := by positivity
    calc e * (K : ℝ) ^ 2 * L = e * ((K : ℝ) ^ 2 * L) := by ring
      _ ≤ e * (U + 3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) := by gcongr
      _ = e * U + e * (3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) := by ring
      _ ≤ e * U + 1 * (3 * (K : ℝ) ^ 8 * P / K + (K : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have heU : e * U ≤ c₀ * (e * Y) + 27 * q * (K : ℝ) ^ 24 := by
    have h0 : (0 : ℝ) ≤ 27 * q * (K : ℝ) ^ 24 := by positivity
    have t1 : e * ((M : ℝ) + n) ≤ e * Y := mul_le_mul_of_nonneg_left (by rw [hY]; linarith) he0
    calc e * U ≤ e * (c₀ * ((M : ℝ) + n) + 27 * q * (K : ℝ) ^ 24) := by gcongr
      _ = c₀ * (e * ((M : ℝ) + n)) + e * (27 * q * (K : ℝ) ^ 24) := by ring
      _ ≤ c₀ * (e * Y) + 1 * (27 * q * (K : ℝ) ^ 24) := by
          have t2 : e * (27 * q * (K : ℝ) ^ 24) ≤ 1 * (27 * q * (K : ℝ) ^ 24) :=
            mul_le_mul_of_nonneg_right he1 h0
          have t3 := mul_le_mul_of_nonneg_left t1 hc₀
          linarith
      _ = _ := by ring
  -- the sum of the terms
  have hS : 3 + ((K * (3 * K ^ 8) : ℕ) : ℝ) + (e * (K : ℝ) ^ 2 * L + 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) +
      2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K + ((c₀ * (nu * lgN n) : ℕ) : ℝ) + 2 * A₀ * Lam n) +
        2 * A₀ * Lam n * C₁ ≤
      3 + 3 * (K : ℝ) ^ 9 + c₀ * (e * Y) + 27 * q * (K : ℝ) ^ 24 + (K : ℝ) ^ 2 +
        4 * c₀ * ((n : ℝ) / K * lg) + 9 * c₀ * ((K : ℝ) ^ 7 * lg) + 81 * q * (K : ℝ) ^ 23 + c₀ * lg +
        2 * A₀ * C₀ * ((K : ℝ) ^ 2 * Lam n) + (2 * A₀ + 2 * A₀ * C₁) * Lam n := by
    have ex1 : ((K * (3 * K ^ 8) : ℕ) : ℝ) = 3 * (K : ℝ) ^ 9 := by push_cast; ring
    have ex4 : 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K = 2 * (3 * (K : ℝ) ^ 8 * P / K) := by push_cast; ring
    have exT : 2 * A₀ * Lam n * ((C₀ * K ^ 2 : ℕ) : ℝ) = 2 * A₀ * C₀ * ((K : ℝ) ^ 2 * Lam n) := by
      push_cast; ring
    rw [ex1, ex4, exT]
    linarith only [heKL, heU, hgP, hcmu]
  -- times `√(log₂(n+2))`
  have f0 := pj 0 (by norm_num); rw [pow_zero, one_mul] at f0
  have f2 := pj 2 (by norm_num)
  have f9 := pj 9 (by norm_num)
  have f23 := pj 23 (by norm_num)
  have f24 := pj 24 (by norm_num)
  have fe : (e * Y) * T2.sq n ≤ ((3 * x₀ + 6 : ℕ) : ℝ) * c₁ * Y := by
    calc (e * Y) * T2.sq n = (e * T2.sq n) * Y := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he hY0
  have fn : ((n : ℝ) / K * lg) * T2.sq n ≤ 9 * (c₁ : ℝ) ^ 2 * Y := by
    calc ((n : ℝ) / K * lg) * T2.sq n = (n : ℝ) / K * (lg * T2.sq n) := by ring
      _ ≤ (n : ℝ) / K * (9 * (c₁ : ℝ) ^ 2 * K) := mul_le_mul_of_nonneg_left hLs (by positivity)
      _ = 9 * (c₁ : ℝ) ^ 2 * n := by field_simp
      _ ≤ 9 * (c₁ : ℝ) ^ 2 * Y := mul_le_mul_of_nonneg_left hnY (by positivity)
  have f7 : ((K : ℝ) ^ 7 * lg) * T2.sq n ≤ 9 * (c₁ : ℝ) ^ 2 * k₀ * Y := by
    calc ((K : ℝ) ^ 7 * lg) * T2.sq n = (K : ℝ) ^ 7 * (lg * T2.sq n) := by ring
      _ ≤ (K : ℝ) ^ 7 * (9 * (c₁ : ℝ) ^ 2 * K) := mul_le_mul_of_nonneg_left hLs (by positivity)
      _ = 9 * (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 8 := by ring
      _ ≤ 9 * (c₁ : ℝ) ^ 2 * (k₀ * Y) := mul_le_mul_of_nonneg_left hK8Y (by positivity)
      _ = _ := by ring
  have fl : lg * T2.sq n ≤ 9 * (c₁ : ℝ) ^ 2 * k₀ * Y := by
    calc lg * T2.sq n ≤ 9 * (c₁ : ℝ) ^ 2 * K := hLs
      _ ≤ 9 * (c₁ : ℝ) ^ 2 * (k₀ * Y) := mul_le_mul_of_nonneg_left hKY (by positivity)
      _ = _ := by ring
  have hS' := mul_le_mul_of_nonneg_right hS hs0.le
  refine hS'.trans ?_
  have fe' := mul_le_mul_of_nonneg_left fe hc₀
  have fn' := mul_le_mul_of_nonneg_left fn (by positivity : (0 : ℝ) ≤ 4 * c₀)
  have f7' := mul_le_mul_of_nonneg_left f7 (by positivity : (0 : ℝ) ≤ 9 * c₀)
  have fl' := mul_le_mul_of_nonneg_left fl hc₀
  have fK := mul_le_mul_of_nonneg_left pK2Λ (by positivity : (0 : ℝ) ≤ 2 * A₀ * C₀)
  have fΛ := mul_le_mul_of_nonneg_left pΛ (by positivity : (0 : ℝ) ≤ 2 * A₀ + 2 * A₀ * C₁)
  have f9' := mul_le_mul_of_nonneg_left f9 (by positivity : (0 : ℝ) ≤ 3)
  have f23' := mul_le_mul_of_nonneg_left f23 (by positivity : (0 : ℝ) ≤ 81 * q)
  have f24' := mul_le_mul_of_nonneg_left f24 (by positivity : (0 : ℝ) ≤ 27 * q)
  have f0' := mul_le_mul_of_nonneg_left f0 (by positivity : (0 : ℝ) ≤ 3)
  push_cast at fe' ⊢
  linarith only [fe', fn', f7', fl', fK, fΛ, f9', f23', f24', f0', f2]

/-- **One profile index, in `2^{O((Md+n)/√log n)}`** (as `T2.branch_bound`). -/
theorem branch_bound3 (c₀ q C₁ C₀ x₀ k₀ c₁ : ℕ) : ∃ A : ℕ, ∀ (n m K nu P B τ S U sc : ℕ) (e : ℝ),
    2 ≤ K → K ^ 30 ≤ k₀ * (n + 2) → n + 2 ≤ K ^ c₁ → 0 ≤ e → e ≤ 1 →
    e ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 K) → m ≤ (n + 2) * (n + 2) →
    3 * K ^ 8 * nu ≤ n + 3 * K ^ 8 →
    U ≤ c₀ * (m + n) + q * (3 * K ^ 8) ^ 3 → P ≤ c₀ * (nu * lgN n) + q * (3 * K ^ 8) ^ 2 →
    B ≤ q * (n + 3 * K ^ 8 + 2) ^ q → τ ≤ 2 ^ (c₀ * (nu * lgN n)) * (q * (n + 3 * K ^ 8 + 2) ^ q) →
    S + sc ≤ q * (n + 3 * K ^ 8 + 2) ^ q →
    3 * (((K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) *
        (2 : ℝ) ^ (2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K) * τ) * (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁)
      ≤ (2 : ℝ) ^ Xp A n m ∧
    ((sc + (Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) +
      (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Xp A n m := by
  obtain ⟨A₀, hA₀⟩ := branch_pol3 c₀ q k₀
  refine ⟨(3 + 3 + 27 * q + 81 * q + 1) * (c₁ * k₀) + c₀ * ((3 * x₀ + 6) * c₁) + 36 * c₀ * c₁ ^ 2 +
    81 * c₀ * c₁ ^ 2 * k₀ + 9 * c₀ * c₁ ^ 2 * k₀ + (2 * A₀ * C₀ + 2 * A₀ + 2 * A₀ * C₁) * (c₁ ^ 2 * k₀), ?_⟩
  intro n m K nu P B τ S U sc e hK2 hup hlo he0 he1 heK hm hmu hU hP hB hτ hS
  obtain ⟨h1, h2, h3⟩ := hA₀ n m K nu P B U (by omega) hup hm hmu hU hP hB
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
  set X2 : ℝ := XT + x4 + ((c₀ * (nu * lgN n) : ℕ) : ℝ) + 2 * A₀ * Lam n with hX2
  set X3 : ℝ := 2 * A₀ * Lam n * C₁ with hX3
  have hXT0 : 0 ≤ XT := by positivity
  have hx40 : 0 ≤ x4 := by positivity
  have hX10 : 0 ≤ X1 := by positivity
  have hX20 : 0 ≤ X2 := by positivity
  have hX30 : 0 ≤ X3 := by positivity
  have hcm0 : (0 : ℝ) ≤ ((c₀ * (nu * lgN n) : ℕ) : ℝ) := Nat.cast_nonneg _
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
  have hτr : (τ : ℝ) ≤ (2 : ℝ) ^ ((c₀ * (nu * lgN n) : ℕ) : ℝ) * Pw := by
    have : (τ : ℝ) ≤ ((2 ^ (c₀ * (nu * lgN n)) * (q * (n + 3 * K ^ 8 + 2) ^ q) : ℕ) : ℝ) := by exact_mod_cast hτ
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
  have e2 : (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * ((2 : ℝ) ^ ((c₀ * (nu * lgN n) : ℕ) : ℝ) * Pw) = (2 : ℝ) ^ X2 := by
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
  have hfin : 3 + X1 + X2 + X3 ≤ Xp ((3 + 3 + 27 * q + 81 * q + 1) * (c₁ * k₀) + c₀ * ((3 * x₀ + 6) * c₁) + 36 * c₀ * c₁ ^ 2 +
    81 * c₀ * c₁ ^ 2 * k₀ + 9 * c₀ * c₁ ^ 2 * k₀ + (2 * A₀ * C₀ + 2 * A₀ + 2 * A₀ * C₁) * (c₁ ^ 2 * k₀)) n m := by
    apply le_Xp
    have hKL := K2L_le K (3 * K ^ 8) P U (by omega)
    rw [← hLd] at hKL
    push_cast at hKL
    rw [hX1, hX2, hXT, hx4, hX3]
    exact core_exp3 hK2 hup hlo he0 he1 heK hmu hU hP hKL
  constructor
  · calc 3 * (((K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ L B' * (2 : ℝ) ^ x4 * τ) *
          (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁)
        ≤ 3 * (((2 : ℝ) ^ X1 + (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * ((2 : ℝ) ^ ((c₀ * (nu * lgN n) : ℕ) : ℝ) * Pw)) *
          (2 : ℝ) ^ X3) := by
          have hA : (K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ L B' * (2 : ℝ) ^ x4 * τ ≤
              (2 : ℝ) ^ X1 + (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * ((2 : ℝ) ^ ((c₀ * (nu * lgN n) : ℕ) : ℝ) * Pw) :=
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

end Branch


/-! ## One profile index of one graph -/

section Body

variable (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
  {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

variable (kf) in
/-- What the body computes on the index `y`. -/
noncomputable def vOf (K₀ : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (y : ℕ) : ℤ :=
  if bad3 pk kf K₀ (aOf G, y) = true then 0 else (pk.net (gN kf K₀ (aOf G)) G y).value

theorem bad3_iff (K₀ : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y : ℕ) :
    bad3 pk kf K₀ (aOf G, y) = true ↔
      (n ≤ 2 ∨ ∃ v, G.degree v < 2) ∨ pk.good (gN kf K₀ (aOf G)) (aOf G) y = false := by
  simp only [bad3, aOf_len, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
    Bool.not_eq_true']
  refine or_congr (or_congr Iff.rfl ⟨fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, ?_⟩, fun ⟨v, h⟩ => ⟨v, v.2, ?_⟩⟩) Iff.rfl
  · have := degW_aOf G ⟨v, hv⟩; simp only at this; omega
  · have := degW_aOf G v; omega

theorem sum_vOf (K₀ : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : 1 ≤ gN kf K₀ (aOf G)) :
    ∑ y ∈ range (pk.nPr (gN kf K₀ (aOf G)) (aOf G)), vOf pk kf K₀ G y =
      (n : ℤ) * ((hamCycles G).card : ℤ) := by
  by_cases hb : n ≤ 2 ∨ ∃ v, G.degree v < 2
  · rw [hamCycles_eq_empty hb, card_empty, Nat.cast_zero, mul_zero]
    refine sum_eq_zero fun y _ => ?_
    rw [vOf, if_pos ((bad3_iff pk K₀ G y).2 (Or.inl hb))]
  · have h3 : 3 ≤ n := by omega
    have hdeg : ∀ v, 2 ≤ G.degree v := fun v => by
      by_contra h; exact hb (Or.inr ⟨v, by omega⟩)
    rw [← pk.value _ G hg h3 hdeg]
    refine sum_congr rfl fun y _ => ?_
    unfold vOf
    by_cases hgood : pk.good (gN kf K₀ (aOf G)) (aOf G) y = true
    · rw [if_neg (fun h => by
        rcases (bad3_iff pk K₀ G y).1 h with h | h
        · exact hb h
        · rw [h] at hgood; exact Bool.false_ne_true hgood), if_pos hgood]
    · rw [if_pos ((bad3_iff pk K₀ G y).2 (Or.inr (by simpa using hgood))), if_neg hgood]

theorem Md_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Md n G.edgeFinset.card ≤ (n + 2) * (n + 2) := by
  unfold Md lgd
  have h1 : Nat.log 2 (G.edgeFinset.card / n + 2) ≤ G.edgeFinset.card / n + 2 :=
    (Nat.log_lt_self 2 (Nat.succ_ne_zero _)).le
  have h2 : n * (G.edgeFinset.card / n) ≤ G.edgeFinset.card := Nat.mul_div_le _ _
  have h3 := card_edge_le G
  calc n * Nat.log 2 (G.edgeFinset.card / n + 2) ≤ n * (G.edgeFinset.card / n + 2) := Nat.mul_le_mul_left _ h1
    _ ≤ (n + 2) * (n + 2) := by nlinarith

theorem size_y_le3 {n : ℕ} (G : SimpleGraph (Fin n)) {g y : ℕ} (hg : 1 ≤ g)
    (hy : y < pk.nPr g (aOf G)) : size y ≤ (n + 2) * (pk.q * g ^ 2) + 1 := by
  apply size_nat_of_lt
  calc y < pk.nPr g (aOf G) := hy
    _ ≤ (n + 2) ^ (pk.q * g ^ 2) := pk.nPr_le g G hg
    _ ≤ (2 ^ (n + 2)) ^ (pk.q * g ^ 2) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ ((n + 2) * (pk.q * g ^ 2)) := by rw [← pow_mul]

/-- **One profile index, with one bound for all graphs.** -/
theorem body3_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {y : ℕ},
      y < pk.nPr (gN kf (Kf 0) (aOf G)) (aOf G) →
      ∃ t : ℕ, (bodyM3 pk E kf (Kf 0)).Runs (aOf G, y) t ⌊(2 : ℝ) ^ Xp A n (Md n G.edgeFinset.card)⌋₊
          (vOf pk kf (Kf 0) G y) ∧ t ≤ ⌊(2 : ℝ) ^ Xp A n (Md n G.edgeFinset.card)⌋₊ := by
  obtain ⟨A₁, hA₁⟩ := branch_bound3 c₀ pk.q C₁ C₀ x₀ (Kf 0 ^ 30) (30 * C₀ + 1)
  have hP2 : ∃ A, ∀ n, Pol A n ((2 * n + 1) + (2 * (n * n) + 1) +
      ((n + 2) * (pk.q * (3 * (Kf 0 ^ 30) * (n + 2)) ^ 2) + 1) + 3) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.mul Pol.id Pol.id)) (Pol.const 1)))
      (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 2)) (Pol.mul (Pol.const pk.q)
        (Pol.pow (Pol.mul (Pol.const (3 * (Kf 0 ^ 30))) (Pol.add Pol.id (Pol.const 2))) 2))) (Pol.const 1)))
      (Pol.const 3)⟩
  obtain ⟨A₂, hA₂⟩ := hP2
  refine ⟨A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30), fun {n} G _ {y} hy => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aOf G) (aOf_len G)
  rw [← hKl] at hK2 hup hlo
  have hg1 : 1 ≤ gN kf (Kf 0) (aOf G) := by
    have : 1 ≤ kN kf (Kf 0) (aOf G) ^ 8 := Nat.one_le_pow _ _ (by omega)
    simp only [gN]; omega
  have hgK : gN kf (Kf 0) (aOf G) ≤ 3 * (Kf 0 ^ 30) * (n + 2) := by
    have : kN kf (Kf 0) (aOf G) ^ 8 ≤ kN kf (Kf 0) (aOf G) ^ 30 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simp only [gN]; nlinarith
  set M := Md n G.edgeFinset.card with hMd
  have hA1 : A₁ ≤ A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30) := by omega
  by_cases hb : bad3 pk kf (Kf 0) (aOf G, y) = true
  · have hr : (bodyM3 pk E kf (Kf 0)).Runs (aOf G, y) 1 (max (size (aOf G, y)) (size (0 : ℤ)) + 1 + 1) 0 := by
      unfold bodyM3
      exact Stepped.ite_runs_true hb (Stepped.const_runs _ _)
    refine ⟨1, ?_, ?_⟩
    · rw [vOf, if_pos hb]
      refine hr.mono le_rfl ?_
      apply Nat.le_floor
      have hs : max (size (aOf G, y)) (size (0 : ℤ)) + 1 + 1 ≤
          (2 * n + 1) + (2 * (n * n) + 1) + ((n + 2) * (pk.q * (3 * (Kf 0 ^ 30) * (n + 2)) ^ 2) + 1) + 3 := by
        have h1 := size_aOf G
        have h2 := size_y_le3 pk G hg1 hy
        have h2' : (n + 2) * (pk.q * gN kf (Kf 0) (aOf G) ^ 2) ≤
            (n + 2) * (pk.q * (3 * (Kf 0 ^ 30) * (n + 2)) ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgK 2))
        have h3 : size (0 : ℤ) = 1 := rfl
        have h4 : size (aOf G, y) = size (aOf G) + size y := rfl
        rw [h3, h4]; omega
      have := pol_le_Xp (m := M) hK2 hup hlo ((hA₂ n).le hs)
      exact this.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono (by omega)))
    · apply Nat.le_floor
      have : (1 : ℝ) ≤ (2 : ℝ) ^ Xp (A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30)) n M :=
        Real.one_le_rpow one_le_two (Xp_nonneg _ _ _)
      exact_mod_cast this
  · have hb' : bad3 pk kf (Kf 0) (aOf G, y) = false := by simpa using hb
    have hgood' := fun h => hb ((bad3_iff pk (Kf 0) G y).2 h)
    have h3 : 3 ≤ n := by
      by_contra h; exact hgood' (Or.inl (Or.inl (by omega)))
    have hdeg : ∀ v, 2 ≤ G.degree v := fun v => by
      by_contra h; exact hgood' (Or.inl (Or.inr ⟨v, by omega⟩))
    have hgood : pk.good (gN kf (Kf 0) (aOf G)) (aOf G) y = true := by
      by_contra h; exact hgood' (Or.inr (by simpa using h))
    have hN := pk.isNet _ G hg1 h3 hdeg y hy hgood
    have hS := pk.S_le _ G hg1 h3 hdeg y hy hgood
    have hctx : ctxF pk kf (Kf 0) (aOf G, y) = pk.prep (Printed.unary (gN kf (Kf 0) (aOf G)), (y, aOf G)) := rfl
    rw [← hctx] at hN hS
    have hval : (pk.net (gN kf (Kf 0) (aOf G)) G y).value = vOf pk kf (Kf 0) G y := by
      rw [vOf, if_neg hb]
    obtain ⟨T, hrun, hT⟩ := net_runs pk hC₁ hL hk E hsol l hKl hN
    have hnu := pk.nu_le _ G hg1 h3 hdeg
    have hU := pk.U_le _ G hg1 h3 hdeg y hy hgood
    have hP := pk.P_le _ G hg1 h3 hdeg
    have hB := pk.B_le _ G hg1 h3 hdeg
    have hτ := pk.τ_le _ G hg1 h3 hdeg
    have he0 : 0 ≤ e l := by
      have h1 := hL.e_ge l
      have hK1 : (1 : ℝ) < Kf l := by exact_mod_cast (by have := hL.K_two l; omega : 1 < Kf l)
      have : 0 < Real.logb 2 (Kf l) := Real.logb_pos one_lt_two hK1
      exact le_trans (by positivity) h1
    have heK := he l
    rw [← hKl] at heK
    obtain ⟨hb1, hb2⟩ := hA₁ n M (kN kf (Kf 0) (aOf G))
      (pk.nu (gN kf (Kf 0) (aOf G)) G)
      (pk.P (gN kf (Kf 0) (aOf G)) G)
      (pk.B (gN kf (Kf 0) (aOf G)) G)
      (pk.τ (gN kf (Kf 0) (aOf G)) G)
      (pk.S (gN kf (Kf 0) (aOf G)) G)
      ((pk.net (gN kf (Kf 0) (aOf G)) G y : Net (3 * kN kf (Kf 0) (aOf G) ^ 8)).U)
      (size (ctxF pk kf (Kf 0) (aOf G, y))) (e l) hK2 hup hlo
      he0 (hL.e_le l) heK (Md_le G) hnu hU hP hB hτ hS
    have hAm := Real.rpow_le_rpow_of_exponent_le one_le_two
      (Xp_mono (n := n) (m := M) (by omega : A₁ + 1 ≤ A₁ + 1 + 2 * A₂ * ((30 * C₀ + 1) ^ 2 * Kf 0 ^ 30)))
    have hAm' := Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono (n := n) (m := M) hA1)
    have hr := Stepped.ite_runs_false (p := bad3 pk kf (Kf 0))
      (M := Stepped.const (0 : ℤ)) (a := (aOf G, y)) hb'
      (Stepped.mapIn_runs (f := fun p : GIn × ℕ => (ctxF pk kf (Kf 0) p,
        ginF pk (ctxF pk kf (Kf 0) p) (kN kf (Kf 0) p.1))) (M := GM pk E (argF kf (Kf 0)))
        (a := (aOf G, y)) hrun)
    rw [← hval]
    unfold bodyM3
    refine ⟨3 * T, hr.mono le_rfl (Nat.le_floor ?_), Nat.le_floor ?_⟩
    · have := (add_one_le_Xp hb2).trans hAm
      exact_mod_cast this
    · have := (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 3)).trans (hb1.trans hAm')
      exact_mod_cast this

/-- The number of profile indices: `2^{O((Md+n)/√log n)}`. -/
theorem nPr_le_Xp {n K c₁ k₀ : ℕ} (G : SimpleGraph (Fin n)) (hK : 2 ≤ K)
    (hup : K ^ 30 ≤ k₀ * (n + 2)) (hlo : n + 2 ≤ K ^ c₁) (M : ℕ) :
    (pk.nPr (3 * K ^ 8) (aOf G) : ℝ) ≤ (2 : ℝ) ^ Xp (9 * pk.q * (c₁ ^ 2 * k₀)) n M := by
  have hg1 : 1 ≤ 3 * K ^ 8 := by have := Nat.one_le_pow 8 K (by omega); omega
  have h1 := pk.nPr_le (3 * K ^ 8) G hg1
  have h2 : (pk.nPr (3 * K ^ 8) (aOf G) : ℝ) ≤ ((n : ℝ) + 2) ^ (pk.q * (3 * K ^ 8) ^ 2) := by exact_mod_cast h1
  rw [pow_eq_two_rpow] at h2
  refine h2.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (le_Xp ?_))
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hs := sq_le_K (by omega) hlo
  have hΛ := Lam_le_K (by omega) hlo
  have hs0 := sq_pos n
  have hΛ0 : 0 ≤ Lam n := by linarith [one_le_Lam n]
  have hc : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg _
  have hΛs : Lam n * T2.sq n ≤ (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
    calc Lam n * T2.sq n ≤ (c₁ * K) * (c₁ * K) := by gcongr
      _ = _ := by ring
  have h30 : (K : ℝ) ^ 30 ≤ k₀ * ((n : ℝ) + 2) := by exact_mod_cast hup
  have h18 : (K : ℝ) ^ 18 ≤ (K : ℝ) ^ 30 := pow_le_pow_right₀ hKr (by norm_num)
  have hk0 : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ pk.q := Nat.cast_nonneg _
  have hM : (n : ℝ) + 2 ≤ (M : ℝ) + n + 2 := by have : (0 : ℝ) ≤ M := Nat.cast_nonneg _; linarith
  calc ((pk.q * (3 * K ^ 8) ^ 2 : ℕ) : ℝ) * Lam n * T2.sq n
      = 9 * pk.q * ((K : ℝ) ^ 16 * (Lam n * T2.sq n)) := by push_cast; ring
    _ ≤ 9 * pk.q * ((K : ℝ) ^ 16 * ((c₁ : ℝ) ^ 2 * (K : ℝ) ^ 2)) := by gcongr
    _ = 9 * pk.q * (c₁ : ℝ) ^ 2 * (K : ℝ) ^ 18 := by ring
    _ ≤ 9 * pk.q * (c₁ : ℝ) ^ 2 * (k₀ * ((M : ℝ) + n + 2)) := by
        have : (k₀ : ℝ) * ((n : ℝ) + 2) ≤ k₀ * ((M : ℝ) + n + 2) := mul_le_mul_of_nonneg_left hM hk0
        gcongr; linarith
    _ = _ := by push_cast; ring

end Body

/-! ## The whole machine on one graph -/

section Machine3

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem vOf_natAbs_le (K₀ : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : 1 ≤ gN kf K₀ (aOf G)) {y : ℕ} (hy : y < pk.nPr (gN kf K₀ (aOf G)) (aOf G)) :
    (vOf pk kf K₀ G y).natAbs ≤ 2 ^ (pk.q * (n + gN kf K₀ (aOf G) + 2) ^ pk.q) := by
  unfold vOf
  split_ifs with hb
  · simp
  · have hgood' := fun h => hb ((bad3_iff pk K₀ G y).2 h)
    have h3 : 3 ≤ n := by
      by_contra h; exact hgood' (Or.inl (Or.inl (by omega)))
    have hdeg : ∀ v, 2 ≤ G.degree v := fun v => by
      by_contra h; exact hgood' (Or.inl (Or.inr ⟨v, by omega⟩))
    have hgood : pk.good (gN kf K₀ (aOf G)) (aOf G) y = true := by
      by_contra h; exact hgood' (Or.inr (by simpa using h))
    exact (pk.value_le _ G hg h3 hdeg y hy hgood).le

/-- **The machine of Theorem 3 on every graph**: `#HC(G)` in binary, within
`2^{A(Md+n+2)/√log₂(n+2)}` steps, on states of at most that size. -/
theorem hcM3_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ T S : ℕ,
      (hcM3 pk E kf (Kf 0)).Runs (code G) T S (Nat.bits (hamCycles G).card) ∧
        (T : ℝ) ≤ (2 : ℝ) ^ Xp A n (Md n G.edgeFinset.card) ∧
        (S : ℝ) ≤ (2 : ℝ) ^ Xp A n (Md n G.edgeFinset.card) := by
  obtain ⟨Ab, hAb⟩ := body3_runs pk E hC₁ hL hk hsol he
  set q := pk.q
  set k₀ := Kf 0 ^ 30 with hk0d
  have hQ : ∃ A, ∀ n, Pol A n ((2 * (n + 1 + n * n) + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) +
      ((n + 2) * (q * (3 * k₀ * (n + 2)) ^ 2) + q * (n + 3 * k₀ * (n + 2) + 2) ^ q + 2) +
      (2 * (n + 1 + n * n) + 1 + (n + n * n + 1)) + (2 * (n * n + 1) + 1) + 4) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.add
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)))
        (Pol.const 1))
      (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
        (Pol.add (Pol.mul (Pol.const 2) (Pol.mul Pol.id Pol.id)) (Pol.const 1))))
      (Pol.add (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 2)) (Pol.mul (Pol.const q)
          (Pol.pow (Pol.mul (Pol.const (3 * k₀)) (Pol.add Pol.id (Pol.const 2))) 2)))
        (Pol.mul (Pol.const q) (Pol.pow (Pol.add (Pol.add Pol.id
          (Pol.mul (Pol.const (3 * k₀)) (Pol.add Pol.id (Pol.const 2)))) (Pol.const 2)) q)))
        (Pol.const 2)))
      (Pol.add (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)))
        (Pol.const 1)) (Pol.add (Pol.add Pol.id (Pol.mul Pol.id Pol.id)) (Pol.const 1))))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1))) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨AQ, hAQ⟩ := hQ
  obtain ⟨AN, hAN⟩ : ∃ x, x = 9 * q * ((30 * C₀ + 1) ^ 2 * k₀) := ⟨_, rfl⟩
  obtain ⟨AP, hAP⟩ : ∃ x, x = 2 * AQ * ((30 * C₀ + 1) ^ 2 * k₀) := ⟨_, rfl⟩
  refine ⟨(AN + (Ab + 1) + 2 + 1) + ((AP + (AN + 1 + 1) + 1) + Ab + 1), fun {n} G _ => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aOf G) (aOf_len G)
  rw [← hKl] at hK2 hup hlo
  have hg1 : 1 ≤ gN kf (Kf 0) (aOf G) := by
    have : 1 ≤ kN kf (Kf 0) (aOf G) ^ 8 := Nat.one_le_pow _ _ (by omega)
    simp only [gN]; omega
  have hgK : gN kf (Kf 0) (aOf G) ≤ 3 * k₀ * (n + 2) := by
    have : kN kf (Kf 0) (aOf G) ^ 8 ≤ kN kf (Kf 0) (aOf G) ^ 30 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h := Nat.mul_le_mul_left 3 (this.trans hup)
    simp only [gN, hk0d]; rw [mul_assoc]; exact h
  choose! t ht using fun y (hy : y < pk.nPr (gN kf (Kf 0) (aOf G)) (aOf G)) => hAb G hy
  set m := G.edgeFinset.card with hmd
  set M := Md n m with hMd
  set Sm := ⌊(2 : ℝ) ^ Xp Ab n M⌋₊ with hSm
  set N := pk.nPr (gN kf (Kf 0) (aOf G)) (aOf G) with hN
  set V := 2 ^ (q * (n + gN kf (Kf 0) (aOf G) + 2) ^ q) with hVd
  have hNR : (N : ℝ) ≤ (2 : ℝ) ^ Xp AN n M := hAN ▸ nPr_le_Xp pk G hK2 hup hlo M
  have hNle : N ≤ (n + 2) ^ (q * gN kf (Kf 0) (aOf G) ^ 2) := pk.nPr_le _ G hg1
  have hV : ∀ y < N, (vOf pk kf (Kf 0) G y).natAbs ≤ V := fun y hy => vOf_natAbs_le pk (Kf 0) G hg1 hy
  have hsum := Stepped.sumRange_runs (M := bodyM3 pk E kf (Kf 0)) (N := fun a => pk.nPr (gN kf (Kf 0) a) a)
    (a := aOf G) t (vOf pk kf (Kf 0) G) V Sm (fun y hy => (ht y hy).1) hV
  rw [sum_vOf pk (Kf 0) G hg1] at hsum
  have hmain : (mainM3 pk E kf (Kf 0)).Runs (code G) _ _ ((n : ℤ) * ((hamCycles G).card : ℤ)) :=
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
  · have ht1 : ∀ y ∈ range N, t y + 1 ≤ Sm + 1 := fun y hy => by
      have := (ht y (mem_range.1 hy)).2; omega
    have hsumT : ∑ y ∈ range N, (t y + 1) ≤ N * (Sm + 1) := by
      have := Finset.sum_le_sum ht1
      simpa [sum_const, card_range, smul_eq_mul] using this
    have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n M := Nat.floor_le (by positivity)
    have h1 : (Sm : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (Ab + 1) n M := add_one_le_Xp hSmR
    have h2 : (N : ℝ) * ((Sm : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (AN + (Ab + 1)) n M :=
      mul_le_Xp (Nat.cast_nonneg _) hNR h1
    have h3 : (N : ℝ) * ((Sm : ℝ) + 1) + 2 ≤ (2 : ℝ) ^ Xp (AN + (Ab + 1) + 2 + 1) n M :=
      add_le_Xp h2 (by exact_mod_cast const_le_Xp 2 n M)
    have h4 : (((∑ y ∈ range N, (t y + 1)) + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) * ((Sm : ℝ) + 1) + 2 := by
      have : (((∑ y ∈ range N, (t y + 1)) : ℕ) : ℝ) ≤ ((N * (Sm + 1) : ℕ) : ℝ) := by exact_mod_cast hsumT
      push_cast at this ⊢; linarith
    refine h4.trans (h3.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono ?_)))
    omega
  · have h1 : size (code G) = 2 * (n + 1 + n * n) + 1 := by
      rw [LabelSystem.size_word, length_code stMatrixLength]
    have h2 := size_aOf G
    have h3 : size N ≤ N + 1 := size_nat_le' _
    have h4 : size (N * V) ≤ (n + 2) * (q * (3 * k₀ * (n + 2)) ^ 2) + q * (n + 3 * k₀ * (n + 2) + 2) ^ q + 2 := by
      apply size_nat_of_lt
      have e1 : N ≤ 2 ^ ((n + 2) * (q * (3 * k₀ * (n + 2)) ^ 2)) :=
        calc N ≤ (n + 2) ^ (q * gN kf (Kf 0) (aOf G) ^ 2) := hNle
          _ ≤ (n + 2) ^ (q * (3 * k₀ * (n + 2)) ^ 2) :=
              Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgK 2))
          _ ≤ (2 ^ (n + 2)) ^ (q * (3 * k₀ * (n + 2)) ^ 2) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
          _ = _ := (pow_mul _ _ _).symm
      have e2 : V ≤ 2 ^ (q * (n + 3 * k₀ * (n + 2) + 2) ^ q) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      calc N * V ≤ 2 ^ ((n + 2) * (q * (3 * k₀ * (n + 2)) ^ 2)) * 2 ^ (q * (n + 3 * k₀ * (n + 2) + 2) ^ q) :=
            Nat.mul_le_mul e1 e2
        _ < _ := by rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
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
    have hSnat : max (size (code G) + (size (aOf G) + size N + (size (N * V) + Sm) + 1))
        (max (size (code G, (n : ℤ) * ((hamCycles G).card : ℤ))) (size (Nat.bits (hamCycles G).card)) + 1) + 1 ≤
        ((2 * (n + 1 + n * n) + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) +
          ((n + 2) * (q * (3 * k₀ * (n + 2)) ^ 2) + q * (n + 3 * k₀ * (n + 2) + 2) ^ q + 2) +
          (2 * (n + 1 + n * n) + 1 + (n + n * n + 1)) + (2 * (n * n + 1) + 1) + 4) + (N + 1) + Sm := by
      rw [hpair]
      simp only [max_def]
      split_ifs <;> omega
    have hP := pol_le_Xp (m := M) hK2 hup hlo (hAQ n)
    rw [← hAP] at hP
    have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n M := Nat.floor_le (by positivity)
    have hN1 : (N : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (AN + 1 + 1) n M :=
      (add_le_Xp hNR (by exact_mod_cast const_le_Xp 1 n M))
    have hall := add_le_Xp (add_le_Xp hP hN1) hSmR
    have hcast : ((max (size (code G) + (size (aOf G) + size N + (size (N * V) + Sm) + 1))
        (max (size (code G, (n : ℤ) * ((hamCycles G).card : ℤ))) (size (Nat.bits (hamCycles G).card)) + 1) + 1 : ℕ) : ℝ) ≤
        (((2 * (n + 1 + n * n) + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) +
          ((n + 2) * (q * (3 * k₀ * (n + 2)) ^ 2) + q * (n + 3 * k₀ * (n + 2) + 2) ^ q + 2) +
          (2 * (n + 1 + n * n) + 1 + (n + n * n + 1)) + (2 * (n * n + 1) + 1) + 4 : ℕ) : ℝ) + ((N : ℝ) + 1) + Sm := by
      have := (Nat.cast_le (α := ℝ)).2 hSnat
      push_cast at this ⊢; linarith
    refine hcast.trans (hall.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono ?_)))
    omega

end Machine3

/-- `Md + n ≤ 2n·log₂(2m/n + 2)`. -/
theorem Md_add_le (n m : ℕ) :
    ((Md n m : ℕ) : ℝ) + n ≤ 2 * n * Real.logb 2 (2 * (m : ℝ) / n + 2) := by
  have hL1 : 1 ≤ Real.logb 2 (2 * (m : ℝ) / n + 2) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_one]
    have : (0 : ℝ) ≤ 2 * (m : ℝ) / n := by positivity
    linarith
  have hlgd : (lgd n m : ℝ) ≤ Real.logb 2 (2 * (m : ℝ) / n + 2) := by
    unfold lgd
    have h : 2 ^ Nat.log 2 (m / n + 2) ≤ m / n + 2 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
    have h' : (2 : ℝ) ^ (Nat.log 2 (m / n + 2) : ℝ) ≤ ((m / n : ℕ) : ℝ) + 2 := by
      rw [Real.rpow_natCast]; exact_mod_cast h
    have h2 : ((m / n : ℕ) : ℝ) ≤ 2 * (m : ℝ) / n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [h0]
      · have : ((m / n : ℕ) : ℝ) ≤ (m : ℝ) / n := Nat.cast_div_le
        have : (m : ℝ) / n ≤ 2 * (m : ℝ) / n := by
          apply div_le_div_of_nonneg_right _ (by positivity); have : (0 : ℝ) ≤ m := Nat.cast_nonneg _; linarith
        linarith
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity)]
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold Md; push_cast
  nlinarith

end T3

open T3 T2 Asm EthFollowup.Hamiltonian in
/-- **Theorem 3, Turing-machine level, from a uniform degree package.** If for some absolute
constant `c₀` there is ONE degree package (`T3.DPackage c₀`), then there are ONE Turing machine of
Mathlib with finite alphabets and ONE constant `C` such that on the code of ANY graph `G` with `n`
vertices and `m` edges the machine halts within `⌊C · 2^{C·n·log₂(2m/n + 2)/√(log₂(n+2))}⌋` steps
with `#HC(G)` in binary. (`2m/n` is the average degree `d̄`.) -/
theorem theorem3_TM_of_package (hpkg : ∃ c₀ : ℕ, Nonempty (DPackage c₀)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n * Real.logb 2 (2 * (G.edgeFinset.card : ℝ) / n + 2) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨c₀, ⟨pk⟩⟩ := hpkg
  obtain ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := T2.geBody
  have hL := hyp.levels
  have hk := hyp.computesK
  obtain ⟨A, hA⟩ := hcM3_runs pk hC₁ hL hk _ hyp.solves (x₀ := x₀) fun l => he l
  obtain ⟨inst⟩ := hcM3_poly pk _ _ hL hk hyp.steps
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.exists_tmW (hcM3 pk (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)
    (CliqueLevels.levelsUnder x₀) (Levels.Gen.K x₀ 0))
  have hQ : ∃ A, ∀ n, Pol A n (n + 1 + n * n) :=
    ⟨_, fun n => Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)⟩
  obtain ⟨AL, hAL⟩ := hQ
  set c₁ := 30 * C₀ + 1
  set k₀ := Levels.Gen.K x₀ 0 ^ 30
  set Af := q + (A + 1) + q * (2 * AL * (c₁ ^ 2 * k₀) + A + 1 + 1) with hAf
  refine ⟨M, 2 ^ (2 * Af + 1), hfin, fun n G _ => ?_⟩
  obtain ⟨T, S, hrun, hT, hS⟩ := hA G
  obtain ⟨ev⟩ := hM (GraphProblems.code G) T S _ hrun
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aOf G) (aOf_len G)
  rw [← hKl] at hK2 hup hlo
  set m := G.edgeFinset.card
  set Mm := Md n m
  have hlen : (GraphProblems.code G).length = n + 1 + n * n := GraphProblems.length_code GraphProblems.stMatrixLength G
  have hLx : ((GraphProblems.code G).length : ℝ) ≤ (2 : ℝ) ^ Xp (2 * AL * (c₁ ^ 2 * k₀)) n Mm := by
    rw [hlen]; exact pol_le_Xp hK2 hup hlo (hAL n)
  have h1 : (T : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (A + 1) n Mm := add_one_le_Xp hT
  have h2 : ((GraphProblems.code G).length : ℝ) + S + 1 ≤
      (2 : ℝ) ^ Xp (2 * AL * (c₁ ^ 2 * k₀) + A + 1 + 1) n Mm :=
    add_one_le_Xp (add_le_Xp hLx hS)
  have h3 := pow_le_Xp (by positivity) h2 q
  have h4 : (q : ℝ) * ((T : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (q + (A + 1)) n Mm :=
    mul_le_Xp (Nat.cast_nonneg _) (const_le_Xp q n Mm) h1
  have h5 := mul_le_Xp (by positivity) h4 h3
  rw [← hAf] at h5
  have hle : q * (T + 1) * ((GraphProblems.code G).length + S + 1) ^ q ≤
      ⌊((2 ^ (2 * Af + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (((2 ^ (2 * Af + 1) : ℕ) : ℝ) * n *
        Real.logb 2 (2 * (m : ℝ) / n + 2) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
    apply Nat.le_floor
    have e1 : ((q * (T + 1) * ((GraphProblems.code G).length + S + 1) ^ q : ℕ) : ℝ) =
        (q : ℝ) * ((T : ℝ) + 1) * (((GraphProblems.code G).length : ℝ) + S + 1) ^ q := by push_cast; ring
    rw [e1]
    refine h5.trans ((Xp_split Af n Mm).trans ?_)
    have hC : 2 * (Af : ℝ) ≤ ((2 ^ (2 * Af + 1) : ℕ) : ℝ) := by
      have : 2 * Af ≤ 2 ^ (2 * Af + 1) := by
        have := (Nat.lt_two_pow_self (n := Af)).le
        rw [pow_succ, pow_mul]
        have : 2 ^ Af ≤ (2 ^ 2) ^ Af := Nat.pow_le_pow_left (by norm_num) _
        omega
      exact_mod_cast this
    have e2 : (2 : ℝ) ^ (2 * (Af : ℝ)) ≤ ((2 ^ (2 * Af + 1) : ℕ) : ℝ) := by
      rw [show (2 : ℝ) * (Af : ℝ) = ((2 * Af : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [show Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) = T2.sq n from rfl]
    refine mul_le_mul e2 (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (by positivity) (by positivity)
    apply div_le_div_of_nonneg_right _ (T2.sq_pos n).le
    have hMd := Md_add_le n m
    have hA0 : (0 : ℝ) ≤ Af := Nat.cast_nonneg _
    have hL0 : 0 ≤ (n : ℝ) * Real.logb 2 (2 * (m : ℝ) / n + 2) := by
      have : 0 ≤ Real.logb 2 (2 * (m : ℝ) / n + 2) :=
        Real.logb_nonneg one_lt_two (by linarith [show (0 : ℝ) ≤ 2 * (m : ℝ) / n by positivity])
      positivity
    calc (Af : ℝ) * ((Mm : ℝ) + n) ≤ Af * (2 * n * Real.logb 2 (2 * (m : ℝ) / n + 2)) :=
          mul_le_mul_of_nonneg_left hMd hA0
      _ = (2 * (Af : ℝ)) * (n * Real.logb 2 (2 * (m : ℝ) / n + 2)) := by ring
      _ ≤ ((2 ^ (2 * Af + 1) : ℕ) : ℝ) * (n * Real.logb 2 (2 * (m : ℝ) / n + 2)) :=
          mul_le_mul_of_nonneg_right hC hL0
      _ = _ := by ring
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

theorem two_card_edge_le_maxDegree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≤ n * G.maxDegree := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  calc ∑ v, G.degree v ≤ ∑ _v : Fin n, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
    _ = n * G.maxDegree := by simp

theorem avg_le_maxDegree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    2 * (G.edgeFinset.card : ℝ) / n ≤ G.maxDegree := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  · have h : ((2 * G.edgeFinset.card : ℕ) : ℝ) ≤ ((n * G.maxDegree : ℕ) : ℝ) := by
      exact_mod_cast two_card_edge_le_maxDegree G
    push_cast at h
    rw [div_le_iff₀ (by exact_mod_cast h0)]
    linarith

open EthFollowup.Hamiltonian in
/-- **Theorem 3, maximum-degree form**: `⌊C · 2^{C·n·log₂(Δ + 2)/√(log₂(n+2))}⌋` steps, `Δ` the maximum
degree. -/
theorem theorem3_maxdeg_TM_of_package (hpkg : ∃ c₀ : ℕ, Nonempty (T3.DPackage c₀)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n * Real.logb 2 ((G.maxDegree : ℝ) + 2) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨M, C, hfin, hM⟩ := theorem3_TM_of_package hpkg
  refine ⟨M, C, hfin, fun n G _ => ?_⟩
  obtain ⟨ev⟩ := hM n G
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.floor_le_floor ?_)⟩⟩
  have hd : 2 * (G.edgeFinset.card : ℝ) / n + 2 ≤ (G.maxDegree : ℝ) + 2 := by
    linarith [avg_le_maxDegree G]
  have h0 : 0 < 2 * (G.edgeFinset.card : ℝ) / n + 2 := by positivity
  have hl := Real.logb_le_logb_of_le one_lt_two h0 hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left hl (by positivity)

end EthFollowup.ExactHC
