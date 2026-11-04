/-
# The generic counted prefix search in `2^{O(n/√log n)}` steps (module B4, part 2)

`scratchpad/plans/modp-plan.md` §5. `Factoring/Rate.lean` with the counted quantity and the search
abstracted: a `CntPackage` (`CntPackage.lean`) answers the queries `Q w (π ++ [0])` by Lemma 8
case (i) (`ExplicitCost.groupingExplicit`, `ζ = 1/(2K)`, `g = 3K⁸`, `K = K_ℓ` for the largest level
with `K_ℓ ≤ max(⌊n^{1/40}⌋, K₀)`, `Level40.lean`) with the clique machine of Theorem A(b) on the
pieces of Theorem B; a `SearchSpec` says what to do with the counts.

* `SearchSpec`: `pre` (answered directly by `small`), `step` (one round: from `(w, y, π)` and the
  count of `π ++ [0]` the next word, one bit longer), `fin` (the output from `(w, π)`);
* `GR.seq pk sp w y` (the word after `y` rounds), `GR.answer pk sp w`;
* `GR.cntM` (one query), `GR.bodyR`, `GR.loopR` (`R w` rounds, `Srch.iterRange`), `GR.searchM`
  (the machine); `GR.searchM_poly`;
* `GR.netR_runs`, `GR.body_runs`, `GR.searchM_runs` (as `FR.netR_runs`, `FR.body_runs`,
  `FR.facM_runs`; the exponent arithmetic `FR.round_bound` is reused unchanged);
* `GR.TM_of_runs`: a `Stepped` machine within `2^{A(n+2)/√log₂(n+2)}` is a Mathlib machine within
  `⌊C·2^{C n/√log₂(n+2)}⌋` (`CountKSat.exists_tmW`);
* **`GR.searchM_TM`**: ONE Mathlib `TM2ComputableAux` machine with finite alphabets and ONE `C`
  with `Outputs M w (answer pk sp w) ⌊C·2^{C|w|/√log₂(|w|+2)}⌋` for EVERY input word `w`;
* the one/two-query machine: `QuerySpec` (`pre`, `small`, query words `q1`, `q2`, `fin` of the two
  counts), `GR.answerQ`, `GR.cntQ` (one query read from any input), `GR.queryM`, `GR.cntQ_poly`,
  `GR.queryM_poly`, `GR.query_runs` (one query on any `(w, π)`), `GR.queryM_runs`, **`GR.queryM_TM`**.

Standard axioms only.
-/
import EthFollowup.ModP.CntPackage
import EthFollowup.Factoring.Rate

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

/-- **A counted prefix search.** On the input word `w`: if `pre w`, output `small w`; else `R w`
rounds from the empty word, round `y` turning the word `π` (with the count of `π ++ [0]`) into
`step ((w, y, π), count)`, and then the output `fin (w, π)`. -/
structure SearchSpec where
  pre : List Bool → Bool
  small : List Bool → List Bool
  step : (List Bool × ℕ × List Bool) × ℤ → List Bool
  fin : List Bool × List Bool → List Bool

namespace GR

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset Printed QueryMachines
  EthFollowup.Factoring

variable {c₀ : ℕ} (pk : CntPackage c₀) (sp : SearchSpec)

/-! ## The search -/

/-- The word after `y` rounds. -/
def seq (w : List Bool) : ℕ → List Bool
  | 0 => []
  | y + 1 => sp.step ((w, y, seq w y), ((pk.Q w (seq w y ++ [false]) : ℕ) : ℤ))

/-- **The answer** of the search on the input word `w`. -/
def answer (w : List Bool) : List Bool :=
  if sp.pre w then sp.small w else sp.fin (w, seq pk sp w (pk.R w))

theorem seq_zero (w : List Bool) : seq pk sp w 0 = [] := rfl

theorem seq_succ (w : List Bool) (y : ℕ) :
    seq pk sp w (y + 1) = sp.step ((w, y, seq pk sp w y), ((pk.Q w (seq pk sp w y ++ [false]) : ℕ) : ℤ)) :=
  rfl

theorem seq_length (hlen : ∀ q, (sp.step q).length = q.1.2.2.length + 1) (w : List Bool) (y : ℕ) :
    (seq pk sp w y).length = y := by
  induction y with
  | zero => rfl
  | succ y ih => rw [seq_succ, hlen, ih]

/-! ## The machine -/

/-- The input of Lemma 8 (ζ = 1/(2K), K, g = 3K⁸, Definition 2(iii)) written from the context. -/
def ginF (c : pk.Ctx) (k : ℕ) : ExplicitCost.GroupingInput :=
  ((1, 2 * k), ((unary k, unary (3 * k ^ 8)),
    inputOf (3 * k ^ 8) (pk.Np.P c) (pk.Np.B c) (pk.Np.len c) (pk.Np.cap c)))

/-- Lemma 8's procedure with the clique machine `E`, its queries answered by the procedures. -/
def GM {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : ExplicitCost.CliqueInput → α) :
    Stepped (pk.Ctx × ExplicitCost.GroupingInput) ℤ :=
  (ExplicitCost.groupingData E arg).plug (answerOf pk.Np)

section Mach

variable (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
  (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- The context of the query `π ++ [0]`, with `g = 3K⁸` nodes. -/
def ctxR (p : FR.RIn) : pk.Ctx := pk.prep (unary (3 * kN40 kf K₀ p.1 ^ 8), (p.1, p.2.2 ++ [false]))

/-- **One query**: the count `Q w (π ++ [0])` by Lemma 8 on the network. -/
def cntM : Stepped FR.RIn ℤ :=
  Stepped.mapIn (fun p => (ctxR pk kf K₀ p, ginF pk (ctxR pk kf K₀ p) (kN40 kf K₀ p.1)))
    (GM pk E (T2.argF kf K₀))

/-- **One round** of the search. -/
def bodyR : Stepped FR.RIn (List Bool) := Stepped.bind (cntM pk E kf K₀) (Stepped.ofFun sp.step)

/-- **The `R w` rounds** from the empty word. -/
def loopR : Stepped (List Bool) (List Bool) :=
  Srch.iterRange pk.R (bodyR pk sp E kf K₀) (fun _ => [])

/-- **The machine**: `pre w` directly, else the search and `fin`. -/
def searchM : Stepped (List Bool) (List Bool) :=
  Stepped.ite sp.pre (Stepped.ofFun sp.small)
    (Stepped.bind (loopR pk sp E kf K₀) (Stepped.ofFun sp.fin))

end Mach

/-! ### Polynomial time -/

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem ctxR_polyT (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    PolyT (ctxR pk kf (Kf 0)) := by
  have hg : Unary fun p : FR.RIn => 3 * kN40 kf (Kf 0) p.1 ^ 8 := (gN40_unary kf hL hk).comp PolyT.id'.fst
  have hq : PolyT fun p : FR.RIn => (p.1, p.2.2 ++ [false]) := by fun_prop
  exact pk.prep_poly.comp (PolyT.prodMk hg hq)

theorem searchM_poly (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ) (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf) (hE : E.PolyTimeSteps) (hpre : PolyT sp.pre)
    (hsmall : PolyT sp.small) (hstep : PolyT sp.step) (hfin : PolyT sp.fin) :
    Nonempty (IsPolyT (searchM pk sp E kf (Kf 0))) := by
  have hc := ctxR_polyT pk hL hk
  have hgm : Nonempty (IsPolyT (GM pk E (T2.argF kf (Kf 0)))) :=
    stPolyPlug _ _ _ _ _ _ _ (ExplicitCost.groupingPoly.2 _ E _ hE (T2.argF_polyT kf hL hk))
      (answerOf_poly pk.Np pk.keeps.mem pk.keeps.W pk.keeps.Ψ pk.keeps.f)
  obtain ⟨i1⟩ := hgm
  have hkU : Unary fun p : FR.RIn => kN40 kf (Kf 0) p.1 := (kN40_unary kf hL hk).comp PolyT.id'.fst
  have hgU : Unary fun p : FR.RIn => 3 * kN40 kf (Kf 0) p.1 ^ 8 := (gN40_unary kf hL hk).comp PolyT.id'.fst
  have hin : PolyT fun p : FR.RIn => inputOf (3 * kN40 kf (Kf 0) p.1 ^ 8) (pk.Np.P (ctxR pk kf (Kf 0) p))
      (pk.Np.B (ctxR pk kf (Kf 0) p)) (pk.Np.len (ctxR pk kf (Kf 0) p)) (pk.Np.cap (ctxR pk kf (Kf 0) p)) :=
    ExplicitCost.inputOf_polyT_data hgU (pk.P_unary.comp hc) (pk.B_unary.comp hc)
      (pk.keeps.len.comp (h := fun q : FR.RIn × ℕ => (ctxR pk kf (Kf 0) q.1, q.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) PolyT.id'.snd))
      (pk.keeps.cap.comp (h := fun q : FR.RIn × ℕ × ℕ => (ctxR pk kf (Kf 0) q.1, q.2.1, q.2.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) (PolyT.prodMk PolyT.id'.snd.fst PolyT.id'.snd.snd)))
  have hg1 : PolyT fun p : FR.RIn =>
      (ctxR pk kf (Kf 0) p, ginF pk (ctxR pk kf (Kf 0) p) (kN40 kf (Kf 0) p.1)) := by
    unfold ginF
    have h2k : PolyT fun p : FR.RIn => 2 * kN40 kf (Kf 0) p.1 := PolyT.mul (PolyT.const 2) hkU.poly
    exact PolyT.prodMk hc (PolyT.prodMk (PolyT.prodMk (PolyT.const 1) h2k)
      (PolyT.prodMk (PolyT.prodMk hkU hgU) hin))
  have : IsPolyT (cntM pk E kf (Kf 0)) := IsPolyT.mapIn hg1
  have : IsPolyT (Stepped.ofFun sp.step) := IsPolyT.ofFun hstep
  have : IsPolyT (bodyR pk sp E kf (Kf 0)) := IsPolyT.bind
  have : IsPolyT (loopR pk sp E kf (Kf 0)) := Srch.IsPolyT.iterRange pk.R_poly (by fun_prop)
  have : IsPolyT (Stepped.ofFun sp.fin) := IsPolyT.ofFun hfin
  have : IsPolyT (Stepped.bind (loopR pk sp E kf (Kf 0)) (Stepped.ofFun sp.fin)) := IsPolyT.bind
  have : IsPolyT (Stepped.ofFun sp.small) := IsPolyT.ofFun hsmall
  exact ⟨IsPolyT.ite hpre⟩

/-! ## One network: Lemma 8 (case (i)) with the clique machine -/

open T2 in
/-- **Lemma 8 + Theorem A(b) on a network given by the procedures of the package** (as
`FR.netR_runs`). -/
theorem netR_runs {C₁ : ℕ} (hC₁ : GEBody C₁) (hL : CliqueLevels.Levels Kf e C₀)
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

/-! ## One round -/

theorem size_Q_le {w π : List Bool} (hw : pk.Ok w) (hπ : π.length ≤ pk.R w) :
    size ((pk.Q w π : ℕ) : ℤ) ≤ pk.qb * (w.length + 2) + 1 :=
  Asm.size_int_of_lt (by rw [Int.natAbs_natCast]; exact pk.Q_lt w π hw hπ)

open T2 in
/-- **One round, with one bound for all input words** `w` with `Ok w`. -/
theorem body_runs (hlen : ∀ q, (sp.step q).length = q.1.2.2.length + 1)
    {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ w : List Bool, pk.Ok w → ∀ y < pk.R w, ∃ t : ℕ,
      (bodyR pk sp E kf (Kf 0)).Runs (w, y, seq pk sp w y) t ⌊(2 : ℝ) ^ Xp A w.length 0⌋₊
          (seq pk sp w (y + 1)) ∧
        t ≤ ⌊(2 : ℝ) ^ Xp A w.length 0⌋₊ := by
  obtain ⟨A₁, hA₁⟩ := FR.round_bound c₀ pk.q C₁ C₀ x₀ (Kf 0 ^ 40) (40 * C₀ + 1)
  obtain ⟨AQ, hAQ⟩ : ∃ A, ∀ n, Asm.Pol A n (1000 * (n + 2) + pk.qb * (n + 2)) :=
    ⟨_, fun n => Asm.Pol.add (Asm.Pol.mul (Asm.Pol.const 1000) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2)))
      (Asm.Pol.mul (Asm.Pol.const pk.qb) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2)))⟩
  obtain ⟨AP, hAP⟩ : ∃ x, x = 2 * AQ * ((40 * C₀ + 1) ^ 2 * Kf 0 ^ 40) := ⟨_, rfl⟩
  refine ⟨(A₁ + AP + 1) + (A₁ + 2 + 1), fun w hOk y hy => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts40 kf hL hk w
  rw [← hKl] at hK2 hup hlo
  have hR := pk.R_le w
  set n := w.length with hn
  set K := kN40 kf (Kf 0) w with hKd
  have hK1 : 1 ≤ K := by omega
  have hup30 : K ^ 30 ≤ Kf 0 ^ 40 * (n + 2) := (Nat.pow_le_pow_right hK1 (by norm_num)).trans hup
  set g := 3 * K ^ 8 with hg
  have hg2 : 2 ≤ g := by have : 1 ≤ K ^ 8 := Nat.one_le_pow _ _ (by omega); omega
  set π := seq pk sp w y with hπd
  have hπl : π.length = y := seq_length pk sp hlen w y
  have hπ' : (π ++ [false]).length ≤ pk.R w := by
    rw [List.length_append, hπl, List.length_singleton]; omega
  have hNet := pk.isNet g w (π ++ [false]) hg2 hOk hπ'
  have hval := pk.value g w (π ++ [false]) hg2 hOk hπ'
  have hU := pk.U_le g w (π ++ [false]) hg2 hOk hπ'
  have hP := pk.P_le g w (π ++ [false]) hg2 hOk hπ'
  have hB := pk.B_le g w (π ++ [false]) hg2 hOk hπ'
  have hτ := pk.τ_le g w (π ++ [false]) hg2 hOk hπ'
  have hS := pk.S_le g w (π ++ [false]) hg2 hOk hπ'
  obtain ⟨T, hrun, hT⟩ := netR_runs pk hC₁ hL hk E hsol l hKl hNet
  rw [hval] at hrun
  have hcnt : (cntM pk E kf (Kf 0)).Runs (w, y, π) (3 * T) _ ((pk.Q w (π ++ [false]) : ℕ) : ℤ) :=
    Stepped.mapIn_runs hrun
  have hstep := Stepped.ofFun_runs sp.step ((w, y, π), ((pk.Q w (π ++ [false]) : ℕ) : ℤ))
  rw [← seq_succ] at hstep
  have hbody := Stepped.bind_runs hcnt hstep
  have he0 : 0 ≤ e l := by
    have h1 := hL.e_ge l
    have hK1' : (1 : ℝ) < Kf l := by exact_mod_cast (by have := hL.K_two l; omega : 1 < Kf l)
    have : 0 < Real.logb 2 (Kf l) := Real.logb_pos one_lt_two hK1'
    exact le_trans (by positivity) h1
  have heK := he l
  rw [← hKl] at heK
  obtain ⟨hb1, hb2⟩ := hA₁ n K (pk.P g w (π ++ [false])) (pk.B g w (π ++ [false])) (pk.τ g w (π ++ [false]))
    (pk.S g w (π ++ [false])) (pk.net g w (π ++ [false])).U (size (pk.prep (unary g, (w, π ++ [false]))))
    (e l) hK2 hup hlo he0 (hL.e_le l) heK hU hP hB hτ hS
  have hPQ := pol_le_Xp (m := 0) hK2 hup30 hlo (hAQ n)
  rw [← hAP] at hPQ
  have hAm := Real.rpow_le_rpow_of_exponent_le one_le_two
    (Xp_mono (n := n) (m := 0) (by omega : A₁ + AP + 1 ≤ (A₁ + AP + 1) + (A₁ + 2 + 1)))
  have hAm' := Real.rpow_le_rpow_of_exponent_le one_le_two
    (Xp_mono (n := n) (m := 0) (by omega : A₁ + 2 + 1 ≤ (A₁ + AP + 1) + (A₁ + 2 + 1)))
  refine ⟨3 * T + 1 + 1, hbody.mono le_rfl (Nat.le_floor ?_), Nat.le_floor ?_⟩
  · -- the states
    have hsy : size y ≤ n + 1 := (Asm.size_nat_le' y).trans (by omega)
    have hD := size_Q_le pk hOk hπ'
    have hs1 : size (w, y, π) = (2 * n + 1) + (size y + (2 * y + 1)) := by
      change size w + (size y + size π) = _
      rw [FR.size_bools, FR.size_bools, hπl]
    have hs2 : size (seq pk sp w (y + 1)) = 2 * (y + 1) + 1 := by
      rw [FR.size_bools, seq_length pk sp hlen]
    have hs3 : size ((w, y, π), ((pk.Q w (π ++ [false]) : ℕ) : ℤ)) =
        size (w, y, π) + size ((pk.Q w (π ++ [false]) : ℕ) : ℤ) := rfl
    set X := size (pk.prep (unary g, (w, π ++ [false]))) + (Tc (e l) K C₀ (Lc K g (pk.P g w (π ++ [false]))
      (pk.net g w (π ++ [false])).U) (Bc K g (pk.P g w (π ++ [false])) (pk.B g w (π ++ [false]))) +
      (g * (pk.P g w (π ++ [false]) + pk.B g w (π ++ [false])) + size (1, 2 * K)) ^ C₁) +
      (pk.S g w (π ++ [false]) + 3) + 1 with hX
    have hle : max (size (w, y, π) + X) (max (size ((w, y, π), ((pk.Q w (π ++ [false]) : ℕ) : ℤ)))
        (size (seq pk sp w (y + 1))) + 1) + 1 ≤ X + (1000 * (n + 2) + pk.qb * (n + 2)) := by
      rw [hs3, hs2, hs1]
      generalize pk.qb * (n + 2) = Z at hD ⊢
      simp only [max_def]; split_ifs <;> omega
    have hX' : (X : ℝ) ≤ (2 : ℝ) ^ Xp A₁ n 0 := by
      have : X = size (pk.prep (unary g, (w, π ++ [false]))) + (Tc (e l) K C₀ (Lc K g (pk.P g w (π ++ [false]))
        (pk.net g w (π ++ [false])).U) (Bc K g (pk.P g w (π ++ [false])) (pk.B g w (π ++ [false]))) +
        (g * (pk.P g w (π ++ [false]) + pk.B g w (π ++ [false])) + size (1, 2 * K)) ^ C₁) +
        (pk.S g w (π ++ [false]) + 3) + 1 := hX
      rw [this]; exact hb2
    have hsum := add_le_Xp hX' hPQ
    refine le_trans ?_ (hsum.trans hAm)
    have := (Nat.cast_le (α := ℝ)).2 hle
    push_cast at this ⊢; linarith
  · -- the steps
    have h3T : ((3 * T : ℕ) : ℝ) ≤ (2 : ℝ) ^ Xp A₁ n 0 := by
      push_cast
      exact (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 3)).trans hb1
    have := add_le_Xp h3T (const_le_Xp 2 n 0)
    refine le_trans ?_ (this.trans hAm')
    push_cast; linarith

/-! ## The whole machine -/

open T2 in
/-- **The machine on every input word** `w` (`n = |w|`): the output `answer pk sp w` within
`2^{A(n+2)/√log₂(n+2)}` steps, on states of at most that size (and `n` is below that bound). -/
theorem searchM_runs (hlen : ∀ q, (sp.step q).length = q.1.2.2.length + 1) {ob : ℕ}
    (hfinlen : ∀ w π, π.length ≤ w.length → (sp.fin (w, π)).length ≤ ob * (w.length + 2))
    (hsmlen : ∀ w, (sp.small w).length ≤ ob * (w.length + 2))
    (hOk : ∀ w, sp.pre w = false → pk.Ok w)
    {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ w : List Bool, ∃ T S : ℕ,
      (searchM pk sp E kf (Kf 0)).Runs w T S (answer pk sp w) ∧
      (T : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧
      (w.length : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 := by
  obtain ⟨Ab, hAb⟩ := body_runs pk sp hlen hC₁ hL hk E hsol he
  obtain ⟨AQ, hAQ⟩ : ∃ A, ∀ n, Asm.Pol A n (1000 * (n + 2) + 2 * (ob * (n + 2))) :=
    ⟨_, fun n => Asm.Pol.add (Asm.Pol.mul (Asm.Pol.const 1000) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2)))
      (Asm.Pol.mul (Asm.Pol.const 2)
        (Asm.Pol.mul (Asm.Pol.const ob) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2))))⟩
  obtain ⟨AP, hAP⟩ : ∃ x, x = 2 * AQ * ((40 * C₀ + 1) ^ 2 * Kf 0 ^ 40) := ⟨_, rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ x, x = AP + (Ab + 1) + 2 + 1 := ⟨_, rfl⟩
  refine ⟨Af, fun w => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts40 kf hL hk w
  rw [← hKl] at hK2 hup hlo
  have hR := pk.R_le w
  set n := w.length with hn
  have hup30 : kN40 kf (Kf 0) w ^ 30 ≤ Kf 0 ^ 40 * (n + 2) :=
    (Nat.pow_le_pow_right (by omega) (by norm_num)).trans hup
  have hPQ := pol_le_Xp (m := 0) hK2 hup30 hlo (hAQ n)
  rw [← hAP] at hPQ
  have hmono : ∀ {A : ℕ}, A ≤ Af → (2 : ℝ) ^ Xp A n 0 ≤ (2 : ℝ) ^ Xp Af n 0 := fun h =>
    Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono h)
  have hPAf := hPQ.trans (hmono (by omega))
  have hnl : (n : ℝ) ≤ (2 : ℝ) ^ Xp Af n 0 := by
    have : (0 : ℝ) ≤ (ob : ℝ) * ((n : ℝ) + 2) := by positivity
    refine le_trans ?_ hPAf; push_cast; linarith
  have hsw : size w = 2 * n + 1 := FR.size_bools w
  by_cases hs : sp.pre w = true
  · -- answered directly
    have hr := Stepped.ite_runs_true (p := sp.pre)
      (N := Stepped.bind (loopR pk sp E kf (Kf 0)) (Stepped.ofFun sp.fin)) hs (Stepped.ofFun_runs sp.small w)
    have hans : sp.small w = answer pk sp w := by simp [answer, hs]
    rw [hans] at hr
    refine ⟨1, _, hr, ?_, ?_, hnl⟩
    · have : (1 : ℝ) ≤ (2 : ℝ) ^ Xp Af n 0 := Real.one_le_rpow one_le_two (Xp_nonneg _ _ _)
      exact_mod_cast this
    · have h5 : size (answer pk sp w) ≤ 2 * (ob * (n + 2)) + 1 := by
        rw [← hans, FR.size_bools]; have := hsmlen w; rw [← hn] at this
        generalize ob * (n + 2) = Z at this ⊢; omega
      have hle : max (size w) (size (answer pk sp w)) + 1 + 1 ≤ 1000 * (n + 2) + 2 * (ob * (n + 2)) := by
        generalize ob * (n + 2) = Z at h5 ⊢
        simp only [max_def]; split_ifs <;> omega
      refine le_trans ?_ hPAf
      exact_mod_cast hle
  · -- the search
    have hp : sp.pre w = false := by simpa using hs
    have hOkw := hOk w hp
    choose! t ht using fun y (hy : y < pk.R w) => hAb w hOkw y hy
    set Sm := ⌊(2 : ℝ) ^ Xp Ab n 0⌋₊ with hSm
    have hloop := Srch.iterRange_runs (N := pk.R) (M := bodyR pk sp E kf (Kf 0))
      (c₀ := fun _ => []) w (seq pk sp w) rfl t (2 * n + 1) Sm (fun y hy => (ht y hy).1)
      (fun y hy => by rw [FR.size_bools, seq_length pk sp hlen]; omega)
    have hfin := Stepped.ofFun_runs sp.fin (w, seq pk sp w (pk.R w))
    have hans : sp.fin (w, seq pk sp w (pk.R w)) = answer pk sp w := by simp [answer, hp]
    rw [hans] at hfin
    have hb := Stepped.bind_runs hloop hfin
    have hr := Stepped.ite_runs_false (p := sp.pre) (M := Stepped.ofFun sp.small) hp hb
    refine ⟨_, _, hr, ?_, ?_, hnl⟩
    · -- the steps
      have ht1 : ∀ y ∈ range (pk.R w), t y + 1 ≤ Sm + 1 := fun y hy => by
        have := (ht y (mem_range.1 hy)).2; omega
      have hsumT : ∑ y ∈ range (pk.R w), (t y + 1) ≤ n * (Sm + 1) := by
        have := Finset.sum_le_sum ht1
        simp only [sum_const, card_range, smul_eq_mul] at this
        exact this.trans (Nat.mul_le_mul_right _ hR)
      have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n 0 := Nat.floor_le (by positivity)
      have h1 : (Sm : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (Ab + 1) n 0 := add_one_le_Xp hSmR
      have hnP : (n : ℝ) ≤ (2 : ℝ) ^ Xp AP n 0 := by
        have : (0 : ℝ) ≤ (ob : ℝ) * ((n : ℝ) + 2) := by positivity
        refine le_trans ?_ hPQ; push_cast; linarith
      have h2 : (n : ℝ) * ((Sm : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (AP + (Ab + 1)) n 0 :=
        mul_le_Xp (Nat.cast_nonneg _) hnP h1
      have h3 : (n : ℝ) * ((Sm : ℝ) + 1) + 2 ≤ (2 : ℝ) ^ Xp (AP + (Ab + 1) + 2 + 1) n 0 :=
        add_le_Xp h2 (by exact_mod_cast const_le_Xp 2 n 0)
      have h4 : (((∑ y ∈ range (pk.R w), (t y + 1)) + 1 + 1 : ℕ) : ℝ) ≤ (n : ℝ) * ((Sm : ℝ) + 1) + 2 := by
        have : (((∑ y ∈ range (pk.R w), (t y + 1)) : ℕ) : ℝ) ≤ ((n * (Sm + 1) : ℕ) : ℝ) := by
          exact_mod_cast hsumT
        push_cast at this ⊢; linarith
      exact h4.trans (h3.trans (hmono (by omega)))
    · -- the states
      have hseql : (seq pk sp w (pk.R w)).length = pk.R w := seq_length pk sp hlen w _
      have hout : size (answer pk sp w) ≤ 2 * (ob * (n + 2)) + 1 := by
        rw [← hans, FR.size_bools]; have := hfinlen w _ (hseql.trans_le hR); rw [← hn] at this
        generalize ob * (n + 2) = Z at this ⊢; omega
      have hsn : size (pk.R w) ≤ n + 1 := (Asm.size_nat_le' _).trans (by omega)
      have hpair : size (w, seq pk sp w (pk.R w)) = size w + size (seq pk sp w (pk.R w)) := rfl
      have hcs : size (seq pk sp w (pk.R w)) = 2 * pk.R w + 1 := by rw [FR.size_bools, hseql]
      have hle : max (size w + (size w + size (pk.R w) + (2 * n + 1 + Sm) + 1))
          (max (size (w, seq pk sp w (pk.R w))) (size (answer pk sp w)) + 1) + 1 + 1 ≤
            1000 * (n + 2) + 2 * (ob * (n + 2)) + Sm := by
        rw [hpair, hcs, hsw]
        generalize ob * (n + 2) = Z at hout ⊢
        simp only [max_def]; split_ifs <;> omega
      have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n 0 := Nat.floor_le (by positivity)
      have hall := add_le_Xp hPQ hSmR
      refine le_trans ?_ (hall.trans (hmono (by omega)))
      have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this ⊢; linarith

/-! ## From a machine with the bound to a Mathlib Turing machine -/

open EthFollowup.ExactHC.T2 in
/-- **A `Stepped` machine within `2^{A(n+2)/√log₂(n+2)}` steps and states is a Mathlib
`TM2ComputableAux` machine** with finite alphabets within `⌊C·2^{C n/√log₂(n+2)}⌋` steps
(`CountKSat.exists_tmW`). -/
theorem TM_of_runs (Mc : Stepped (List Bool) (List Bool)) (hp : Nonempty (IsPolyT Mc))
    (ans : List Bool → List Bool)
    (h : ∃ A : ℕ, ∀ w : List Bool, ∃ T S : ℕ, Mc.Runs w T S (ans w) ∧
      (T : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧
      (w.length : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ w : List Bool, GraphProblems.Outputs M w (ans w)
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨inst⟩ := hp
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.exists_tmW Mc
  obtain ⟨Af, hAf⟩ : ∃ x, x = q + (A + 1) + q * (A + A + 1 + 1) := ⟨_, rfl⟩
  refine ⟨M, 2 ^ (2 * Af), hfin, fun w => ?_⟩
  obtain ⟨T, S, hrun, hT, hS, hLx⟩ := hA w
  obtain ⟨ev⟩ := hM w T S _ hrun
  set n := w.length with hn
  have h1 : (T : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (A + 1) n 0 := add_one_le_Xp hT
  have h2 : (n : ℝ) + S + 1 ≤ (2 : ℝ) ^ Xp (A + A + 1 + 1) n 0 := add_one_le_Xp (add_le_Xp hLx hS)
  have h3 := pow_le_Xp (by positivity) h2 q
  have h4 : (q : ℝ) * ((T : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (q + (A + 1)) n 0 :=
    mul_le_Xp (Nat.cast_nonneg _) (const_le_Xp q n 0) h1
  have h5 := mul_le_Xp (by positivity) h4 h3
  rw [← hAf] at h5
  have hsplit := Xp_split Af n 0
  simp only [Nat.cast_zero, zero_add] at hsplit
  have hle : q * (T + 1) * (n + S + 1) ^ q ≤
      ⌊((2 ^ (2 * Af) : ℕ) : ℝ) * 2 ^ (((2 ^ (2 * Af) : ℕ) : ℝ) * (n : ℝ) /
        Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
    apply Nat.le_floor
    have e1 : ((q * (T + 1) * (n + S + 1) ^ q : ℕ) : ℝ) =
        (q : ℝ) * ((T : ℝ) + 1) * ((n : ℝ) + S + 1) ^ q := by push_cast; ring
    rw [e1]
    refine h5.trans (hsplit.trans ?_)
    have hC : (Af : ℝ) ≤ ((2 ^ (2 * Af) : ℕ) : ℝ) := by
      have : Af ≤ 2 ^ (2 * Af) := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have e2 : (2 : ℝ) ^ (2 * (Af : ℝ)) = ((2 ^ (2 * Af) : ℕ) : ℝ) := by
      rw [show (2 : ℝ) * (Af : ℝ) = ((2 * Af : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]; push_cast; ring
    rw [e2, show Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) = T2.sq n from rfl]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC this) (T2.sq_pos n).le
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

/-- **The generic counted prefix search in `2^{O(n/√log n)}` steps.** For a counted-network
package `pk` and a search specification `sp` whose four functions are polynomial time, whose round
adds one bit, whose outputs have length `O(|w| + 2)` and whose direct case `pre` covers every input
word outside `pk.Ok`: ONE Turing machine of Mathlib with finite alphabets and ONE constant `C` such
that, for EVERY input word `w`, the machine started on `w` halts within
`⌊C · 2^{C |w|/√(log₂(|w|+2))}⌋` steps with `answer pk sp w`. -/
theorem searchM_TM (hpre : PolyT sp.pre) (hsmall : PolyT sp.small) (hstep : PolyT sp.step)
    (hfin : PolyT sp.fin) (hlen : ∀ q, (sp.step q).length = q.1.2.2.length + 1) {ob : ℕ}
    (hfinlen : ∀ w π, π.length ≤ w.length → (sp.fin (w, π)).length ≤ ob * (w.length + 2))
    (hsmlen : ∀ w, (sp.small w).length ≤ ob * (w.length + 2))
    (hOk : ∀ w, sp.pre w = false → pk.Ok w) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ w : List Bool, GraphProblems.Outputs M w (answer pk sp w)
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ := by
  obtain ⟨c, x₀, C₀, D', Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := T2.geBody
  exact TM_of_runs _ (searchM_poly pk sp _ hyp.levels hyp.computesK hyp.steps hpre hsmall hstep hfin) _
    (searchM_runs pk sp hlen hfinlen hsmlen hOk hC₁ hyp.levels hyp.computesK _ hyp.solves (x₀ := x₀)
      fun l => he l)

/-! ## A fixed number of queries: the one/two-query machine -/

/-- **A two-query specification** (one query: take `q2 = q1`). On the input word `w`: if `pre w`,
output `small w`; else the counts `Q w (q1 w)`, `Q w (q2 w)` and the output `fin (w, count₁, count₂)`. -/
structure QuerySpec where
  pre : List Bool → Bool
  small : List Bool → List Bool
  q1 : List Bool → List Bool
  q2 : List Bool → List Bool
  fin : List Bool × ℕ × ℕ → List Bool

variable (qs : QuerySpec)

/-- **The answer** of the two-query machine on the input word `w`. -/
def answerQ (w : List Bool) : List Bool :=
  if qs.pre w then qs.small w else qs.fin (w, pk.Q w (qs.q1 w), pk.Q w (qs.q2 w))

/-- The output from the input word and the two counts (as integers). -/
def finQ (p : (List Bool × ℤ) × ℤ) : List Bool := qs.fin (p.1.1, p.1.2.toNat, p.2.toNat)

section QMach

variable (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
  (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- The context of the query `(w, π)`, with `g = 3K⁸` nodes. -/
def ctxQ (p : List Bool × List Bool) : pk.Ctx := pk.prep (unary (3 * kN40 kf K₀ p.1 ^ 8), p)

/-- **One query** `(w, π) = f a` read from the input `a`: the count `Q w π` by Lemma 8. -/
def cntQ {α : Type} (f : α → List Bool × List Bool) : Stepped α ℤ :=
  Stepped.mapIn (fun a => (ctxQ pk kf K₀ (f a), ginF pk (ctxQ pk kf K₀ (f a)) (kN40 kf K₀ (f a).1)))
    (GM pk E (T2.argF kf K₀))

/-- **The two-query machine**: `pre w` directly, else the two counts and `fin`. -/
def queryM : Stepped (List Bool) (List Bool) :=
  Stepped.ite qs.pre (Stepped.ofFun qs.small)
    (Stepped.bind (cntQ pk E kf K₀ fun w => (w, qs.q1 w))
      (Stepped.bind (cntQ pk E kf K₀ fun p : List Bool × ℤ => (p.1, qs.q2 p.1)) (Stepped.ofFun (finQ qs))))

end QMach

theorem cntQ_poly (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ) (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf) (hE : E.PolyTimeSteps) {α : Type} [Enc α] [HasSize α]
    [Carried α] {f : α → List Bool × List Bool} (hf : PolyT f) :
    Nonempty (IsPolyT (cntQ pk E kf (Kf 0) f)) := by
  have hgm : Nonempty (IsPolyT (GM pk E (T2.argF kf (Kf 0)))) :=
    stPolyPlug _ _ _ _ _ _ _ (ExplicitCost.groupingPoly.2 _ E _ hE (T2.argF_polyT kf hL hk))
      (answerOf_poly pk.Np pk.keeps.mem pk.keeps.W pk.keeps.Ψ pk.keeps.f)
  obtain ⟨i1⟩ := hgm
  have hkU : Unary fun a : α => kN40 kf (Kf 0) (f a).1 := (kN40_unary kf hL hk).comp hf.fst
  have hgU : Unary fun a : α => 3 * kN40 kf (Kf 0) (f a).1 ^ 8 := (gN40_unary kf hL hk).comp hf.fst
  have hc : PolyT fun a : α => ctxQ pk kf (Kf 0) (f a) := pk.prep_poly.comp (PolyT.prodMk hgU hf)
  have hin : PolyT fun a : α => inputOf (3 * kN40 kf (Kf 0) (f a).1 ^ 8) (pk.Np.P (ctxQ pk kf (Kf 0) (f a)))
      (pk.Np.B (ctxQ pk kf (Kf 0) (f a))) (pk.Np.len (ctxQ pk kf (Kf 0) (f a)))
      (pk.Np.cap (ctxQ pk kf (Kf 0) (f a))) :=
    ExplicitCost.inputOf_polyT_data hgU (pk.P_unary.comp hc) (pk.B_unary.comp hc)
      (pk.keeps.len.comp (h := fun q : α × ℕ => (ctxQ pk kf (Kf 0) (f q.1), q.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) PolyT.id'.snd))
      (pk.keeps.cap.comp (h := fun q : α × ℕ × ℕ => (ctxQ pk kf (Kf 0) (f q.1), q.2.1, q.2.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) (PolyT.prodMk PolyT.id'.snd.fst PolyT.id'.snd.snd)))
  have hg1 : PolyT fun a : α =>
      (ctxQ pk kf (Kf 0) (f a), ginF pk (ctxQ pk kf (Kf 0) (f a)) (kN40 kf (Kf 0) (f a).1)) := by
    unfold ginF
    have h2k : PolyT fun a : α => 2 * kN40 kf (Kf 0) (f a).1 := PolyT.mul (PolyT.const 2) hkU.poly
    exact PolyT.prodMk hc (PolyT.prodMk (PolyT.prodMk (PolyT.const 1) h2k)
      (PolyT.prodMk (PolyT.prodMk hkU hgU) hin))
  exact ⟨IsPolyT.mapIn hg1⟩

theorem queryM_poly (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ) (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf) (hE : E.PolyTimeSteps) (hpre : PolyT qs.pre)
    (hsmall : PolyT qs.small) (hq1 : PolyT qs.q1) (hq2 : PolyT qs.q2) (hfin : PolyT qs.fin) :
    Nonempty (IsPolyT (queryM pk qs E kf (Kf 0))) := by
  obtain ⟨i1⟩ := cntQ_poly pk E hL hk hE (f := fun w : List Bool => (w, qs.q1 w)) (by fun_prop)
  obtain ⟨i2⟩ := cntQ_poly pk E hL hk hE (f := fun p : List Bool × ℤ => (p.1, qs.q2 p.1)) (by fun_prop)
  have : IsPolyT (Stepped.ofFun (finQ qs)) := IsPolyT.ofFun (by unfold finQ; fun_prop)
  have : IsPolyT (Stepped.bind (cntQ pk E kf (Kf 0) fun p : List Bool × ℤ => (p.1, qs.q2 p.1))
      (Stepped.ofFun (finQ qs))) := IsPolyT.bind
  have : IsPolyT (Stepped.bind (cntQ pk E kf (Kf 0) fun w => (w, qs.q1 w))
      (Stepped.bind (cntQ pk E kf (Kf 0) fun p : List Bool × ℤ => (p.1, qs.q2 p.1))
        (Stepped.ofFun (finQ qs)))) := IsPolyT.bind
  have : IsPolyT (Stepped.ofFun qs.small) := IsPolyT.ofFun hsmall
  exact ⟨IsPolyT.ite hpre⟩

open T2 in
/-- **One query, with one bound for all input words** `w` with `Ok w` and all query words `π`
with `|π| ≤ R w`: Lemma 8 on the network `net g w π` (`g = 3K⁸`) within
`2^{A(n+2)/√log₂(n+2)}` steps and states. -/
theorem query_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ w π : List Bool, pk.Ok w → π.length ≤ pk.R w → ∃ t S : ℕ,
      (GM pk E (argF kf (Kf 0))).Runs (ctxQ pk kf (Kf 0) (w, π),
          ginF pk (ctxQ pk kf (Kf 0) (w, π)) (kN40 kf (Kf 0) w)) t S ((pk.Q w π : ℕ) : ℤ) ∧
        (t : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 := by
  obtain ⟨A₁, hA₁⟩ := FR.round_bound c₀ pk.q C₁ C₀ x₀ (Kf 0 ^ 40) (40 * C₀ + 1)
  refine ⟨A₁, fun w π hOk hπ => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts40 kf hL hk w
  rw [← hKl] at hK2 hup hlo
  set n := w.length with hn
  set K := kN40 kf (Kf 0) w with hKd
  set g := 3 * K ^ 8 with hg
  have hg2 : 2 ≤ g := by have : 1 ≤ K ^ 8 := Nat.one_le_pow _ _ (by omega); omega
  have hNet := pk.isNet g w π hg2 hOk hπ
  have hval := pk.value g w π hg2 hOk hπ
  obtain ⟨T, hrun, hT⟩ := netR_runs pk hC₁ hL hk E hsol l hKl hNet
  rw [hval] at hrun
  have he0 : 0 ≤ e l := by
    have h1 := hL.e_ge l
    have hK1' : (1 : ℝ) < Kf l := by exact_mod_cast (by have := hL.K_two l; omega : 1 < Kf l)
    have : 0 < Real.logb 2 (Kf l) := Real.logb_pos one_lt_two hK1'
    exact le_trans (by positivity) h1
  have heK := he l
  rw [← hKl] at heK
  obtain ⟨hb1, hb2⟩ := hA₁ n K (pk.P g w π) (pk.B g w π) (pk.τ g w π) (pk.S g w π) (pk.net g w π).U
    (size (pk.prep (unary g, (w, π)))) (e l) hK2 hup hlo he0 (hL.e_le l) heK
    (pk.U_le g w π hg2 hOk hπ) (pk.P_le g w π hg2 hOk hπ) (pk.B_le g w π hg2 hOk hπ)
    (pk.τ_le g w π hg2 hOk hπ) (pk.S_le g w π hg2 hOk hπ)
  refine ⟨3 * T, _, hrun, ?_, hb2⟩
  push_cast
  exact (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 3)).trans hb1

open T2 in
/-- **The two-query machine on every input word** `w` (`n = |w|`): the output `answerQ pk qs w`
within `2^{A(n+2)/√log₂(n+2)}` steps, on states of at most that size. -/
theorem queryM_runs {ob : ℕ} (hlen : ∀ w, (answerQ pk qs w).length ≤ ob * (w.length + 2))
    (hOk : ∀ w, qs.pre w = false → pk.Ok w)
    (hq1 : ∀ w, qs.pre w = false → (qs.q1 w).length ≤ pk.R w)
    (hq2 : ∀ w, qs.pre w = false → (qs.q2 w).length ≤ pk.R w)
    {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ w : List Bool, ∃ T S : ℕ,
      (queryM pk qs E kf (Kf 0)).Runs w T S (answerQ pk qs w) ∧
      (T : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧
      (w.length : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 := by
  obtain ⟨Aq, hAq⟩ := query_runs pk hC₁ hL hk E hsol he
  obtain ⟨AQ, hAQ⟩ : ∃ A, ∀ n, Asm.Pol A n (1000 * (n + 2) + 2 * (pk.qb * (n + 2)) + 2 * (ob * (n + 2))) :=
    ⟨_, fun n => Asm.Pol.add (Asm.Pol.add
      (Asm.Pol.mul (Asm.Pol.const 1000) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2)))
      (Asm.Pol.mul (Asm.Pol.const 2)
        (Asm.Pol.mul (Asm.Pol.const pk.qb) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2)))))
      (Asm.Pol.mul (Asm.Pol.const 2)
        (Asm.Pol.mul (Asm.Pol.const ob) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2))))⟩
  obtain ⟨AP, hAP⟩ : ∃ x, x = 2 * AQ * ((40 * C₀ + 1) ^ 2 * Kf 0 ^ 40) := ⟨_, rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ x, x = (Aq + Aq + 1) + 2 + 1 + AP + 1 := ⟨_, rfl⟩
  refine ⟨Af, fun w => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts40 kf hL hk w
  rw [← hKl] at hK2 hup hlo
  set n := w.length with hn
  have hup30 : kN40 kf (Kf 0) w ^ 30 ≤ Kf 0 ^ 40 * (n + 2) :=
    (Nat.pow_le_pow_right (by omega) (by norm_num)).trans hup
  have hPQ := pol_le_Xp (m := 0) hK2 hup30 hlo (hAQ n)
  rw [← hAP] at hPQ
  have hmono : ∀ {A : ℕ}, A ≤ Af → (2 : ℝ) ^ Xp A n 0 ≤ (2 : ℝ) ^ Xp Af n 0 := fun h =>
    Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono h)
  have hPAf := hPQ.trans (hmono (by omega))
  have hZ1 : (0 : ℝ) ≤ (pk.qb : ℝ) * ((n : ℝ) + 2) := by positivity
  have hZ2 : (0 : ℝ) ≤ (ob : ℝ) * ((n : ℝ) + 2) := by positivity
  have hnl : (n : ℝ) ≤ (2 : ℝ) ^ Xp Af n 0 := by
    refine le_trans ?_ hPAf; push_cast; linarith
  have hsw : size w = 2 * n + 1 := FR.size_bools w
  have hout : size (answerQ pk qs w) ≤ 2 * (ob * (n + 2)) + 1 := by
    rw [FR.size_bools]; have := hlen w; rw [← hn] at this
    generalize ob * (n + 2) = Z at this ⊢; omega
  by_cases hs : qs.pre w = true
  · -- answered directly
    have hr := Stepped.ite_runs_true (p := qs.pre)
      (N := Stepped.bind (cntQ pk E kf (Kf 0) fun w => (w, qs.q1 w))
        (Stepped.bind (cntQ pk E kf (Kf 0) fun p : List Bool × ℤ => (p.1, qs.q2 p.1))
          (Stepped.ofFun (finQ qs)))) hs (Stepped.ofFun_runs qs.small w)
    have hans : qs.small w = answerQ pk qs w := by simp [answerQ, hs]
    rw [hans] at hr
    refine ⟨1, _, hr, ?_, ?_, hnl⟩
    · have : (1 : ℝ) ≤ (2 : ℝ) ^ Xp Af n 0 := Real.one_le_rpow one_le_two (Xp_nonneg _ _ _)
      exact_mod_cast this
    · have hle : max (size w) (size (answerQ pk qs w)) + 1 + 1 ≤
          1000 * (n + 2) + 2 * (pk.qb * (n + 2)) + 2 * (ob * (n + 2)) := by
        generalize ob * (n + 2) = Z at hout ⊢
        generalize pk.qb * (n + 2) = Z' at ⊢
        simp only [max_def]; split_ifs <;> omega
      refine le_trans ?_ hPAf
      exact_mod_cast hle
  · -- the two queries
    have hp : qs.pre w = false := by simpa using hs
    have hOkw := hOk w hp
    obtain ⟨t1, S1, hr1, ht1, hS1⟩ := hAq w (qs.q1 w) hOkw (hq1 w hp)
    obtain ⟨t2, S2, hr2, ht2, hS2⟩ := hAq w (qs.q2 w) hOkw (hq2 w hp)
    set c1 : ℤ := ((pk.Q w (qs.q1 w) : ℕ) : ℤ) with hc1
    set c2 : ℤ := ((pk.Q w (qs.q2 w) : ℕ) : ℤ) with hc2
    have hm1 : (cntQ pk E kf (Kf 0) fun w => (w, qs.q1 w)).Runs w t1 S1 c1 := Stepped.mapIn_runs hr1
    have hm2 : (cntQ pk E kf (Kf 0) fun p : List Bool × ℤ => (p.1, qs.q2 p.1)).Runs (w, c1) t2 S2 c2 :=
      Stepped.mapIn_runs hr2
    have hf := Stepped.ofFun_runs (finQ qs) ((w, c1), c2)
    have hans : finQ qs ((w, c1), c2) = answerQ pk qs w := by
      simp only [finQ, hc1, hc2, Int.toNat_natCast, answerQ, hp]; rfl
    rw [hans] at hf
    have hb2 := Stepped.bind_runs hm2 hf
    have hb1 := Stepped.bind_runs hm1 hb2
    have hr := Stepped.ite_runs_false (p := qs.pre) (M := Stepped.ofFun qs.small) hp hb1
    refine ⟨_, _, hr, ?_, ?_, hnl⟩
    · -- the steps
      have h12 : (t1 : ℝ) + t2 ≤ (2 : ℝ) ^ Xp (Aq + Aq + 1) n 0 := add_le_Xp ht1 ht2
      have h3 := add_le_Xp h12 (by exact_mod_cast const_le_Xp 3 n 0 : (3 : ℝ) ≤ (2 : ℝ) ^ Xp 3 n 0)
      refine le_trans ?_ (h3.trans (hmono (by omega)))
      push_cast; linarith
    · -- the states
      have hs1 : size c1 ≤ pk.qb * (n + 2) + 1 := size_Q_le pk hOkw (hq1 w hp)
      have hs2 : size c2 ≤ pk.qb * (n + 2) + 1 := size_Q_le pk hOkw (hq2 w hp)
      have hpair : size (w, c1) = size w + size c1 := rfl
      have hpair2 : size ((w, c1), c2) = size w + size c1 + size c2 := rfl
      have hle : max (size w + S1) (max (size (w, c1) + S2)
          (max (size ((w, c1), c2)) (size (answerQ pk qs w)) + 1) + 1) + 1 + 1 ≤
            (1000 * (n + 2) + 2 * (pk.qb * (n + 2)) + 2 * (ob * (n + 2))) + (S1 + S2) := by
        rw [hpair2, hpair, hsw]
        generalize ob * (n + 2) = Z at hout ⊢
        generalize pk.qb * (n + 2) = Z' at hs1 hs2 ⊢
        simp only [max_def]; split_ifs <;> omega
      have hS12 : (S1 : ℝ) + S2 ≤ (2 : ℝ) ^ Xp (Aq + Aq + 1) n 0 := add_le_Xp hS1 hS2
      have hall := add_le_Xp hPQ hS12
      refine le_trans ?_ (hall.trans (hmono (by omega)))
      have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this ⊢; linarith

/-- **The one/two-query machine in `2^{O(n/√log n)}` steps.** For a counted-network package `pk`
and a two-query specification `qs` whose five functions are polynomial time, whose answers have
length `O(|w| + 2)`, whose queries are words of length at most `R w` and whose direct case `pre`
covers every input word outside `pk.Ok`: ONE Turing machine of Mathlib with finite alphabets and
ONE constant `C` such that, for EVERY input word `w`, the machine started on `w` halts within
`⌊C · 2^{C |w|/√(log₂(|w|+2))}⌋` steps with `answerQ pk qs w`
(`= qs.fin (w, Q w (q1 w), Q w (q2 w))` off `pre`). -/
theorem queryM_TM (hpre : PolyT qs.pre) (hsmall : PolyT qs.small) (hq1p : PolyT qs.q1)
    (hq2p : PolyT qs.q2) (hfin : PolyT qs.fin) {ob : ℕ}
    (hlen : ∀ w, (answerQ pk qs w).length ≤ ob * (w.length + 2))
    (hOk : ∀ w, qs.pre w = false → pk.Ok w)
    (hq1 : ∀ w, qs.pre w = false → (qs.q1 w).length ≤ pk.R w)
    (hq2 : ∀ w, qs.pre w = false → (qs.q2 w).length ≤ pk.R w) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ w : List Bool, GraphProblems.Outputs M w (answerQ pk qs w)
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ := by
  obtain ⟨c, x₀, C₀, D', Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := T2.geBody
  exact TM_of_runs _ (queryM_poly pk qs _ hyp.levels hyp.computesK hyp.steps hpre hsmall hq1p hq2p hfin) _
    (queryM_runs pk qs hlen hOk hq1 hq2 hC₁ hyp.levels hyp.computesK _ hyp.solves (x₀ := x₀)
      fun l => he l)

end GR

end EthFollowup.ModP
