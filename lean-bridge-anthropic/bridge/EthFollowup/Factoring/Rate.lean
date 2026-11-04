/-
# `Nat.minFac` in `2^{O(n/√log n)}` steps from a multiplication-network package (module F5a)

`scratchpad/plans/factoring-plan.md` §1, §3. The route of `theorem2_TM`
(`EthFollowup/ExactHC/Theorem2.lean`) and `amplitude_TM_rate` (`Quantum/QRate.lean`): the clique
machine of Theorem A(b) on the pieces of Theorem B (`CountedRoute.onTheCountedRecursion`),
Lemma 8 case (i) (`ExplicitCost.groupingExplicit`, `ζ = 1/(2K)`, `g = 3K⁸`) with the network queries
answered by the procedures of a `MulPackage` (`stPlug`), `K = K_ℓ` for the largest level with
`K_ℓ ≤ max(⌊n^{1/40}⌋, K₀)` (`Level40.lean`).

* `FR.cntM`: one query: the network count `D(N, n, π ++ [0])` for the input word `w` (`N = ofWord w`,
  `n = |w|`) and the current prefix `π`;
* `FR.bodyR`: one round of the binary search (`Search.searchStep` with the oracle
  `D - [π ++ [0] ⊑ word n 1]`), `FR.loopR`: `n` rounds (`Srch.iterRange`);
* `FR.facM`: the machine (`N < 2` answered directly; else the loop and `Nat.bits`); `FR.facM_poly`;
* `FR.netR_runs`: Lemma 8 + Theorem A(b) on one network; `FR.round_bound`: the exponent arithmetic
  of plan §3 (by `T2.branch_bound` at `n + n₀`, `m = C(n+2)`);
* `FR.facM_runs`: on every word `w`, the output `Nat.bits (minFac (ofWord w))` within
  `2^{A(n+2)/√log₂(n+2)}` steps and state size;
* `minFac_TM_of_pkg`: from `∃ c₀, Nonempty (MulPackage c₀)`, ONE Mathlib `TM2ComputableAux` machine
  with finite alphabets and ONE `C` with `Outputs M (encodeNat N) (encodeNat (minFac N))
  ⌊C·2^{C n/√log₂(n+2)}⌋` (`n = |encodeNat N|`) for every `N`.

Standard axioms only.
-/
import EthFollowup.Factoring.Params
import EthFollowup.Factoring.Search
import EthFollowup.Factoring.Level40
import EthFollowup.ExactHC.SearchMachine

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

namespace FR

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset Printed QueryMachines

/-! ## Words -/

theorem gofWord_append_singleton (l : List Bool) (x : Bool) :
    Groundwork.ofWord (l ++ [x]) = Groundwork.ofWord l + 2 ^ l.length * x.toNat := by
  induction l with
  | nil => simp [Groundwork.ofWord]
  | cons a l ih =>
    simp only [List.cons_append, Groundwork.ofWord, ih, List.length_cons, pow_succ]; ring

/-- The little-endian value of the reversed word is the big-endian value. -/
theorem ofWord_reverse (π : List Bool) : Groundwork.ofWord π.reverse = Search.ofWord π := by
  induction π with
  | nil => rfl
  | cons x l ih =>
    rw [List.reverse_cons, gofWord_append_singleton, ih, Search.ofWord_cons, List.length_reverse]; ring

theorem ofWord_bits (k : ℕ) : Groundwork.ofWord (Nat.bits k) = k := by
  induction k using Nat.binaryRec' with
  | zero => simp [Groundwork.ofWord]
  | bit x k h ih => rw [Nat.bits_append_bit _ _ h, Groundwork.ofWord, ih, Nat.bit_val]; ring

theorem encodePosNum_eq_bits (p : PosNum) : Computability.encodePosNum p = Nat.bits (p : ℕ) := by
  induction p with
  | one => rfl
  | bit1 p ih => rw [Computability.encodePosNum, ih, PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
  | bit0 p ih =>
    rw [Computability.encodePosNum, ih, PosNum.cast_bit0, ← two_mul, Nat.bit0_bits]
    exact (PosNum.cast_pos p).ne'

/-- Mathlib's `encodeNat` is `Nat.bits`. -/
theorem encodeNat_eq_bits (N : ℕ) : Computability.encodeNat N = Nat.bits N := by
  have hN := Num.to_of_nat N
  unfold Computability.encodeNat
  cases h : (N : Num) with
  | zero => rw [h] at hN; simp [Computability.encodeNum, ← hN]
  | pos p => rw [h] at hN; simp only [Computability.encodeNum]; rw [encodePosNum_eq_bits, ← hN]; rfl

theorem ofWord_encodeNat (N : ℕ) : Groundwork.ofWord (Computability.encodeNat N) = N := by
  rw [encodeNat_eq_bits, ofWord_bits]

/-- Params' count is F6a's count with `n' = nB n`. -/
theorem D_eq_search (N n : ℕ) (π : List Bool) : D N n π = Search.D N (nB n) n π := rfl

/-! ## The machine -/

variable {c₀ : ℕ} (pk : MulPackage c₀)

/-- The input of Lemma 8 (ζ = 1/(2K), K, g = 3K⁸, Definition 2(iii)) written from the context. -/
def ginF (c : pk.Ctx) (k : ℕ) : ExplicitCost.GroupingInput :=
  ((1, 2 * k), ((unary k, unary (3 * k ^ 8)),
    inputOf (3 * k ^ 8) (pk.Np.P c) (pk.Np.B c) (pk.Np.len c) (pk.Np.cap c)))

/-- Lemma 8's procedure with the clique machine `E`, its queries answered by the procedures. -/
def GM {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : ExplicitCost.CliqueInput → α) :
    Stepped (pk.Ctx × ExplicitCost.GroupingInput) ℤ :=
  (ExplicitCost.groupingData E arg).plug (answerOf pk.Np)

/-- The input of one round: the input word `w`, the round `y`, the current prefix `π`. -/
abbrev RIn : Type := List Bool × ℕ × List Bool

/-- The correction `[π ++ [0] ⊑ word n 1]`: `π` is all zeros and `|π| + 1 < n`. -/
def corrB (n : ℕ) (π : List Bool) : Bool :=
  decide (π.length + 1 < n) && decide (Groundwork.ofWord π.reverse = 0)

/-- One round after the query: keep `0` iff the corrected count is positive. -/
def stepF (q : RIn × ℤ) : List Bool :=
  if (corrB q.1.1.length q.1.2.2).toNat < q.2.toNat then q.1.2.2 ++ [false] else q.1.2.2 ++ [true]

/-- The output: the big-endian word found, as `Nat.bits` of its value. -/
def outF (q : List Bool × List Bool) : List Bool := Nat.bits (Groundwork.ofWord q.2.reverse)

/-- `N < 2`: `minFac 0 = 2`, `minFac 1 = 1`. -/
def smallF (w : List Bool) : List Bool := if Groundwork.ofWord w = 0 then [false, true] else [true]

section Mach

variable (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
  (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- The context of the query `π ++ [0]`, with `g = 3K⁸` nodes. -/
def ctxR (p : RIn) : pk.Ctx := pk.prep (unary (3 * kN40 kf K₀ p.1 ^ 8), (p.1, p.2.2 ++ [false]))

/-- **One query**: the count `D(N, n, π ++ [0])` by Lemma 8 on the network. -/
def cntM : Stepped RIn ℤ :=
  Stepped.mapIn (fun p => (ctxR pk kf K₀ p, ginF pk (ctxR pk kf K₀ p) (kN40 kf K₀ p.1)))
    (GM pk E (T2.argF kf K₀))

/-- **One round** of the binary search. -/
def bodyR : Stepped RIn (List Bool) := Stepped.bind (cntM pk E kf K₀) (Stepped.ofFun stepF)

/-- **The `n` rounds** from the empty prefix. -/
def loopR : Stepped (List Bool) (List Bool) :=
  Srch.iterRange (fun w => w.length) (bodyR pk E kf K₀) (fun _ => [])

/-- **The machine**: `N < 2` directly, else the search and `Nat.bits`. -/
def facM : Stepped (List Bool) (List Bool) :=
  Stepped.ite (fun w => decide (Groundwork.ofWord w < 2)) (Stepped.ofFun smallF)
    (Stepped.bind (loopR pk E kf K₀) (Stepped.ofFun outF))

end Mach

/-! ### Polynomial time -/

theorem stepF_polyT : PolyT stepF := by unfold stepF corrB; fun_prop

theorem outF_polyT : PolyT outF := by unfold outF; fun_prop

theorem smallF_polyT : PolyT smallF := by unfold smallF; fun_prop

theorem small_polyT : PolyT fun w : List Bool => decide (Groundwork.ofWord w < 2) := by fun_prop

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem ctxR_polyT (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    PolyT (ctxR pk kf (Kf 0)) := by
  have hg : Unary fun p : RIn => 3 * kN40 kf (Kf 0) p.1 ^ 8 := (gN40_unary kf hL hk).comp PolyT.id'.fst
  have hq : PolyT fun p : RIn => (p.1, p.2.2 ++ [false]) := by fun_prop
  exact pk.prep_poly.comp (PolyT.prodMk hg hq)

theorem facM_poly (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ) (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf) (hE : E.PolyTimeSteps) :
    Nonempty (IsPolyT (facM pk E kf (Kf 0))) := by
  have hc := ctxR_polyT pk hL hk
  have hgm : Nonempty (IsPolyT (GM pk E (T2.argF kf (Kf 0)))) :=
    stPolyPlug _ _ _ _ _ _ _ (ExplicitCost.groupingPoly.2 _ E _ hE (T2.argF_polyT kf hL hk))
      (answerOf_poly pk.Np pk.keeps.mem pk.keeps.W pk.keeps.Ψ pk.keeps.f)
  obtain ⟨i1⟩ := hgm
  have hkU : Unary fun p : RIn => kN40 kf (Kf 0) p.1 := (kN40_unary kf hL hk).comp PolyT.id'.fst
  have hgU : Unary fun p : RIn => 3 * kN40 kf (Kf 0) p.1 ^ 8 := (gN40_unary kf hL hk).comp PolyT.id'.fst
  have hin : PolyT fun p : RIn => inputOf (3 * kN40 kf (Kf 0) p.1 ^ 8) (pk.Np.P (ctxR pk kf (Kf 0) p))
      (pk.Np.B (ctxR pk kf (Kf 0) p)) (pk.Np.len (ctxR pk kf (Kf 0) p)) (pk.Np.cap (ctxR pk kf (Kf 0) p)) :=
    ExplicitCost.inputOf_polyT_data hgU (pk.P_unary.comp hc) (pk.B_unary.comp hc)
      (pk.keeps.len.comp (h := fun q : RIn × ℕ => (ctxR pk kf (Kf 0) q.1, q.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) PolyT.id'.snd))
      (pk.keeps.cap.comp (h := fun q : RIn × ℕ × ℕ => (ctxR pk kf (Kf 0) q.1, q.2.1, q.2.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) (PolyT.prodMk PolyT.id'.snd.fst PolyT.id'.snd.snd)))
  have hg1 : PolyT fun p : RIn => (ctxR pk kf (Kf 0) p, ginF pk (ctxR pk kf (Kf 0) p) (kN40 kf (Kf 0) p.1)) := by
    unfold ginF
    have h2k : PolyT fun p : RIn => 2 * kN40 kf (Kf 0) p.1 := PolyT.mul (PolyT.const 2) hkU.poly
    exact PolyT.prodMk hc (PolyT.prodMk (PolyT.prodMk (PolyT.const 1) h2k)
      (PolyT.prodMk (PolyT.prodMk hkU hgU) hin))
  have : IsPolyT (cntM pk E kf (Kf 0)) := IsPolyT.mapIn hg1
  have : IsPolyT (Stepped.ofFun stepF) := IsPolyT.ofFun stepF_polyT
  have : IsPolyT (bodyR pk E kf (Kf 0)) := IsPolyT.bind
  have : IsPolyT (loopR pk E kf (Kf 0)) := Srch.IsPolyT.iterRange (by fun_prop) (by fun_prop)
  have : IsPolyT (Stepped.ofFun outF) := IsPolyT.ofFun outF_polyT
  have : IsPolyT (Stepped.bind (loopR pk E kf (Kf 0)) (Stepped.ofFun outF)) := IsPolyT.bind
  have : IsPolyT (Stepped.ofFun smallF) := IsPolyT.ofFun smallF_polyT
  exact ⟨IsPolyT.ite small_polyT⟩

/-! ## One network: Lemma 8 (case (i)) with the clique machine -/

open T2 in
/-- **Lemma 8 + Theorem A(b) on a network given by the procedures of the package** (as
`T2.net_runs`). -/
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

/-! ## The exponent (plan §3) -/

section Expo

open T2

theorem Kdg_le' {n K k₀ a : ℕ} (hup : K ^ 40 ≤ k₀ * (n + 2)) (hd : dg n ^ 4 ≤ a * (n + 2) ^ 3) :
    K ^ 8 * dg n ≤ (k₀ ^ 4 * a ^ 5 + 1) * (n + 2) := by
  generalize hx : K ^ 8 * dg n = x
  generalize hC : k₀ ^ 4 * a ^ 5 = C
  generalize hy : n + 2 = y at hup hd
  have hy1 : 1 ≤ y := by omega
  have h20 : x ^ 20 ≤ C * y ^ 19 := by
    have e : x ^ 20 = (K ^ 40) ^ 4 * (dg n ^ 4) ^ 5 := by rw [← hx]; ring
    rw [e, ← hC]
    calc (K ^ 40) ^ 4 * (dg n ^ 4) ^ 5 ≤ (k₀ * y) ^ 4 * (a * y ^ 3) ^ 5 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hup 4) (Nat.pow_le_pow_left hd 5)
      _ = _ := by ring
  by_contra hlt
  have hlt' := not_le.1 hlt
  have h1 : ((C + 1) * y) ^ 20 < x ^ 20 := Nat.pow_lt_pow_left hlt' (by norm_num)
  have h2 : C * y ^ 19 ≤ ((C + 1) * y) ^ 20 := by
    calc C * y ^ 19 ≤ (C + 1) * y ^ 19 := Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ ≤ (C + 1) ^ 20 * y ^ 20 :=
          Nat.mul_le_mul (Nat.le_self_pow (by norm_num) _) (Nat.pow_le_pow_right hy1 (by norm_num))
      _ = _ := by ring
  exact absurd (lt_of_le_of_lt (h20.trans h2) h1) (lt_irrefl _)

/-- `K⁸ · dg n ≤ C (n+2)` when `K⁴⁰ ≤ k₀ (n+2)`: `(K⁸ dg)²⁰ ≤ k₀⁴ 2²²⁰ (n+2)¹⁹`. -/
theorem Kdg_le {n K k₀ : ℕ} (hup : K ^ 40 ≤ k₀ * (n + 2)) :
    K ^ 8 * dg n ≤ (k₀ ^ 4 * (2 ^ 44) ^ 5 + 1) * (n + 2) :=
  Kdg_le' hup (dg_pow_le n)

theorem sq_mono {n n' : ℕ} (h : n ≤ n') : T2.sq n ≤ T2.sq n' := by
  unfold T2.sq T2.Lam
  apply Real.sqrt_le_sqrt
  apply Real.logb_le_logb_of_le one_lt_two (by positivity)
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  linarith

/-- The exponent at `n + n₀` with `m = C_m (n+2)` against the exponent at `n` with `m = 0`. -/
theorem Xp_shift (A n n₀ Cm : ℕ) : Xp A (n + n₀) (Cm * (n + 2)) ≤ Xp (A * (Cm + 1 + n₀)) n 0 := by
  unfold Xp
  rw [div_le_div_iff₀ (T2.sq_pos _) (T2.sq_pos _)]
  refine mul_le_mul ?_ (sq_mono (Nat.le_add_right n n₀)) (T2.sq_pos _).le (by positivity)
  push_cast
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  nlinarith [mul_nonneg hA (mul_nonneg hn0 hn), mul_nonneg hA hn0]

/-- **One round, in `2^{O(n/√log n)}`** (plan §3): the steps (three times the bound of Lemma 8) and
the state bound of one query are at most `2^{A (n+2)/√(log₂(n+2))}`. By `T2.branch_bound` at
`n + n₀` with `m = C_m (n+2)` and `μ = (n+2)/g + dg n`; the hypothesis `K⁴⁰ ≤ k₀(n+2)` gives
`g · dg n = O(n+2)` (`Kdg_le`). -/
theorem round_bound (c₀ q C₁ C₀ x₀ k₀ c₁ : ℕ) : ∃ A : ℕ, ∀ (n K P B τ S U sc : ℕ) (e : ℝ),
    2 ≤ K → K ^ 40 ≤ k₀ * (n + 2) → n + 2 ≤ K ^ c₁ → 0 ≤ e → e ≤ 1 →
    e ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 K) →
    U ≤ c₀ * (n + 2) → P ≤ c₀ * ((n + 2) / (3 * K ^ 8) + dg n) →
    B ≤ q * (n + 3 * K ^ 8 + 2) ^ q → τ ≤ q * (n + 3 * K ^ 8 + 2) ^ q →
    S + sc ≤ q * (n + 3 * K ^ 8 + 2) ^ q →
    3 * (((K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) *
        (2 : ℝ) ^ (2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K) * τ) * (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁)
      ≤ (2 : ℝ) ^ Xp A n 0 ∧
    ((sc + (Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) +
      (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Xp A n 0 := by
  obtain ⟨Cd, hCd⟩ : ∃ x, x = k₀ ^ 4 * (2 ^ 44) ^ 5 + 1 := ⟨_, rfl⟩
  obtain ⟨Cm, hCm⟩ : ∃ x, x = 1 + 3 * Cd := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ : ∃ x, x = Cm + 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ := branch_bound c₀ q C₁ C₀ x₀ k₀ (c₁ + n₀)
  refine ⟨A * (Cm + 1 + n₀), fun n K P B τ S U sc e hK2 hup hlo he0 he1 heK hU hP hB hτ hS => ?_⟩
  have hK1 : 1 ≤ K := by omega
  have hdg : K ^ 8 * dg n ≤ Cd * (n + 2) := hCd ▸ Kdg_le hup
  have hup' : K ^ 30 ≤ k₀ * (n + n₀ + 2) :=
    (Nat.pow_le_pow_right hK1 (by norm_num : 30 ≤ 40)).trans (hup.trans (Nat.mul_le_mul_left _ (by omega)))
  have hlo' : n + n₀ + 2 ≤ K ^ (c₁ + n₀) := by
    rw [pow_add]
    have h1 : n₀ + 1 ≤ K ^ n₀ := (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hK2 n₀)
    have h2 := Nat.mul_le_mul hlo h1
    nlinarith
  have hm : Cm * (n + 2) ≤ (n + n₀) * (n + n₀) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmu : 3 * K ^ 8 * ((n + 2) / (3 * K ^ 8) + dg n) ≤
      2 * (Cm * (n + 2)) + 3 * K ^ 8 * ((n + n₀) / (3 * K ^ 8) + 2) := by
    have h1 : 3 * K ^ 8 * ((n + 2) / (3 * K ^ 8)) ≤ n + 2 := Nat.mul_div_le _ _
    have h2 : 3 * K ^ 8 * dg n ≤ 3 * (Cd * (n + 2)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left 3 hdg
    have e1 : 3 * K ^ 8 * ((n + 2) / (3 * K ^ 8) + dg n) =
        3 * K ^ 8 * ((n + 2) / (3 * K ^ 8)) + 3 * K ^ 8 * dg n := by rw [mul_add]
    have e2 : Cm * (n + 2) = (n + 2) + 3 * (Cd * (n + 2)) := by rw [hCm]; ring
    rw [e1, e2]; omega
  have hU' : U ≤ c₀ * (Cm * (n + 2) + (n + n₀)) + q * (3 * K ^ 8) ^ 3 := by
    have : n + 2 ≤ Cm * (n + 2) + (n + n₀) := by omega
    exact hU.trans ((Nat.mul_le_mul_left c₀ this).trans (Nat.le_add_right _ _))
  have hP' : P ≤ c₀ * ((n + 2) / (3 * K ^ 8) + dg n) + q * (3 * K ^ 8) ^ 2 := hP.trans (Nat.le_add_right _ _)
  have hmono : q * (n + 3 * K ^ 8 + 2) ^ q ≤ q * (n + n₀ + 3 * K ^ 8 + 2) ^ q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hτ' : τ ≤ 2 ^ (c₀ * ((n + 2) / (3 * K ^ 8) + dg n)) * (q * (n + n₀ + 3 * K ^ 8 + 2) ^ q) :=
    (hτ.trans hmono).trans (Nat.le_mul_of_pos_left _ (by positivity))
  obtain ⟨h1, h2⟩ := hA (n + n₀) (Cm * (n + 2)) K ((n + 2) / (3 * K ^ 8) + dg n) P B τ S U sc e hK2 hup' hlo'
    he0 he1 heK hm hmu hU' hP' (hB.trans hmono) hτ' (hS.trans hmono)
  have hX := Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_shift A n n₀ Cm)
  exact ⟨h1.trans hX, h2.trans hX⟩

end Expo

/-! ## The search with the network counts -/

/-- The oracle the machine realises: the count minus the correction (read from the query without
its last bit). -/
def cntO (w π' : List Bool) : ℕ :=
  D (Groundwork.ofWord w) w.length π' - (corrB w.length π'.dropLast).toNat

/-- The prefix after `y` rounds. -/
def csq (w : List Bool) (y : ℕ) : List Bool := Search.searchWith (cntO w) y

theorem stepF_eq (w : List Bool) (y : ℕ) (π : List Bool) :
    stepF ((w, y, π), ((D (Groundwork.ofWord w) w.length (π ++ [false]) : ℕ) : ℤ)) =
      Search.searchStep (cntO w) π := by
  simp only [stepF, Search.searchStep, cntO, List.dropLast_concat, Int.toNat_natCast, Nat.sub_pos_iff_lt]

/-- The correction is `[π ++ [0] ⊑ word n 1]` in F6a's numeric form. -/
theorem corrB_toNat {n : ℕ} {π : List Bool} (h : π.length < n) :
    (corrB n π).toNat =
      if 1 / 2 ^ (n - (π ++ [false]).length) = Search.ofWord (π ++ [false]) then 1 else 0 := by
  rw [Search.ofWord_append_singleton, List.length_append, List.length_singleton]
  unfold corrB
  rw [ofWord_reverse]
  simp only [Bool.toNat_false, Nat.add_zero]
  by_cases h1 : π.length + 1 < n
  · have hp : 2 ≤ 2 ^ (n - (π.length + 1)) :=
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : 1 / 2 ^ (n - (π.length + 1)) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0]
    by_cases hx : Search.ofWord π = 0
    · simp [h1, hx]
    · have : (0 = 2 * Search.ofWord π) ↔ False := ⟨fun h => hx (by omega), False.elim⟩
      simp [h1, hx, this]
  · have he : n - (π.length + 1) = 0 := by omega
    rw [he]
    simp [h1]; omega

theorem cntO_agree {w : List Bool} (π : List Bool) (h : π.length < w.length) :
    0 < cntO w (π ++ [false]) ↔
      0 < Search.cnt' (Groundwork.ofWord w) (nB w.length) w.length (π ++ [false]) := by
  unfold cntO Search.cnt'
  rw [List.dropLast_concat, corrB_toNat h, D_eq_search]

/-- The search finds `minFac`. -/
theorem csq_minFac {w : List Bool} (hN : 2 ≤ Groundwork.ofWord w) :
    Search.ofWord (csq w w.length) = Nat.minFac (Groundwork.ofWord w) :=
  Search.searchWith_eq_minFac hN (Groundwork.ofWord_lt w) (lt_nB w.length).le fun π h => cntO_agree π h

theorem size_D_le (N n : ℕ) (π : List Bool) :
    size ((D N n π : ℕ) : ℤ) ≤ 2 * (n + 2 ^ 8 * (n + 2)) + 2 := by
  have h1 : D N n π ≤ 2 ^ nB n * 2 ^ nB n := by
    unfold D Dw; refine (card_filter_le _ _).trans ?_; rw [card_product, card_range]
  have h2 : D N n π < 2 ^ (2 * nB n + 1) := by
    rw [pow_succ, two_mul, pow_add]
    have : 0 < 2 ^ nB n * 2 ^ nB n := by positivity
    omega
  have h3 := Nat.size_le.2 h2
  have hnB : nB n ≤ n + 2 ^ 8 * (n + 2) := by
    have e1 : nB n ≤ n + ℓ n := by
      unfold nB b; rw [mul_add, mul_one]; have := Nat.mul_div_le n (ℓ n); omega
    have e2 : ℓ n ≤ 2 ^ 8 * (n + 2) :=
      le_trans (Nat.le_mul_of_pos_right _ (by unfold W; omega)) (ℓ_mul_W_le n)
    omega
  simp only [size_int, Int.natAbs_natCast]; omega

theorem size_bools (l : List Bool) : size l = 2 * l.length + 1 := LabelSystem.size_word l

open T2 in
/-- **One round, with one bound for all input words** `w` with `ofWord w ≥ 2`. -/
theorem body_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ w : List Bool, 2 ≤ Groundwork.ofWord w → ∀ y < w.length, ∃ t : ℕ,
      (bodyR pk E kf (Kf 0)).Runs (w, y, csq w y) t ⌊(2 : ℝ) ^ Xp A w.length 0⌋₊ (csq w (y + 1)) ∧
        t ≤ ⌊(2 : ℝ) ^ Xp A w.length 0⌋₊ := by
  obtain ⟨A₁, hA₁⟩ := round_bound c₀ pk.q C₁ C₀ x₀ (Kf 0 ^ 40) (40 * C₀ + 1)
  obtain ⟨AQ, hAQ⟩ : ∃ A, ∀ n, Asm.Pol A n (1000 * (n + 2)) :=
    ⟨_, fun n => Asm.Pol.mul (Asm.Pol.const 1000) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2))⟩
  obtain ⟨AP, hAP⟩ : ∃ x, x = 2 * AQ * ((40 * C₀ + 1) ^ 2 * Kf 0 ^ 40) := ⟨_, rfl⟩
  refine ⟨(A₁ + AP + 1) + (A₁ + 2 + 1), fun w hN y hy => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts40 kf hL hk w
  rw [← hKl] at hK2 hup hlo
  set n := w.length with hn
  set N := Groundwork.ofWord w with hNd
  set K := kN40 kf (Kf 0) w with hKd
  have hK1 : 1 ≤ K := by omega
  have hup30 : K ^ 30 ≤ Kf 0 ^ 40 * (n + 2) := (Nat.pow_le_pow_right hK1 (by norm_num)).trans hup
  set g := 3 * K ^ 8 with hg
  have hg2 : 2 ≤ g := by have : 1 ≤ K ^ 8 := Nat.one_le_pow _ _ (by omega); omega
  set π := csq w y with hπd
  have hπl : π.length = y := Search.length_searchWith _ _
  have hπ' : (π ++ [false]).length ≤ n := by
    rw [List.length_append, hπl, List.length_singleton]; omega
  have hN1 : 1 ≤ N := by omega
  have hNet := pk.isNet g w (π ++ [false]) hg2 hN1 hπ'
  have hval := pk.value g w (π ++ [false]) hg2 hN1 hπ'
  have hU := pk.U_le g w (π ++ [false]) hg2 hN1 hπ'
  have hP := pk.P_le g w (π ++ [false]) hg2 hN1 hπ'
  have hB := pk.B_le g w (π ++ [false]) hg2 hN1 hπ'
  have hτ := pk.τ_le g w (π ++ [false]) hg2 hN1 hπ'
  have hS := pk.S_le g w (π ++ [false]) hg2 hN1 hπ'
  obtain ⟨T, hrun, hT⟩ := netR_runs pk hC₁ hL hk E hsol l hKl hNet
  rw [hval] at hrun
  have hcnt : (cntM pk E kf (Kf 0)).Runs (w, y, π) (3 * T) _ ((D N n (π ++ [false]) : ℕ) : ℤ) :=
    Stepped.mapIn_runs hrun
  have hstep := Stepped.ofFun_runs stepF ((w, y, π), ((D N n (π ++ [false]) : ℕ) : ℤ))
  rw [stepF_eq] at hstep
  have hbody := Stepped.bind_runs hcnt hstep
  have hnext : csq w (y + 1) = Search.searchStep (cntO w) π := Search.searchWith_succ _ _
  rw [hnext]
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
    have hD := size_D_le N n (π ++ [false])
    have hs1 : size (w, y, π) = (2 * n + 1) + (size y + (2 * y + 1)) := by
      change size w + (size y + size π) = _
      rw [size_bools, size_bools, hπl]
    have hs2 : size (Search.searchStep (cntO w) π) = 2 * (y + 1) + 1 := by
      rw [size_bools]; unfold Search.searchStep; split_ifs <;> simp [hπl]
    have hs3 : size ((w, y, π), ((D N n (π ++ [false]) : ℕ) : ℤ)) =
        size (w, y, π) + size ((D N n (π ++ [false]) : ℕ) : ℤ) := rfl
    set X := size (pk.prep (unary g, (w, π ++ [false]))) + (Tc (e l) K C₀ (Lc K g (pk.P g w (π ++ [false]))
      (pk.net g w (π ++ [false])).U) (Bc K g (pk.P g w (π ++ [false])) (pk.B g w (π ++ [false]))) +
      (g * (pk.P g w (π ++ [false]) + pk.B g w (π ++ [false])) + size (1, 2 * K)) ^ C₁) +
      (pk.S g w (π ++ [false]) + 3) + 1 with hX
    have hle : max (size (w, y, π) + X) (max (size ((w, y, π), ((D N n (π ++ [false]) : ℕ) : ℤ)))
        (size (Search.searchStep (cntO w) π)) + 1) + 1 ≤ X + 1000 * (n + 2) := by
      rw [hs3, hs2, hs1]
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

theorem smallF_eq {w : List Bool} (h : Groundwork.ofWord w < 2) :
    smallF w = Nat.bits (Nat.minFac (Groundwork.ofWord w)) := by
  unfold smallF
  rcases (by omega : Groundwork.ofWord w = 0 ∨ Groundwork.ofWord w = 1) with h0 | h1
  · rw [h0, Nat.minFac_zero]; rfl
  · rw [h1, Nat.minFac_one]; rfl

open T2 in
/-- **The machine on every input word** `w` (`n = |w|`): the output `Nat.bits (minFac (ofWord w))`
within `2^{A(n+2)/√log₂(n+2)}` steps, on states of at most that size (and `n` is below that bound). -/
theorem facM_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ w : List Bool, ∃ T S : ℕ,
      (facM pk E kf (Kf 0)).Runs w T S (Nat.bits (Nat.minFac (Groundwork.ofWord w))) ∧
      (T : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 ∧
      (w.length : ℝ) ≤ (2 : ℝ) ^ Xp A w.length 0 := by
  obtain ⟨Ab, hAb⟩ := body_runs pk hC₁ hL hk E hsol he
  obtain ⟨AQ, hAQ⟩ : ∃ A, ∀ n, Asm.Pol A n (1000 * (n + 2)) :=
    ⟨_, fun n => Asm.Pol.mul (Asm.Pol.const 1000) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2))⟩
  obtain ⟨AP, hAP⟩ : ∃ x, x = 2 * AQ * ((40 * C₀ + 1) ^ 2 * Kf 0 ^ 40) := ⟨_, rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ x, x = AP + (Ab + 1) + 2 + 1 := ⟨_, rfl⟩
  refine ⟨Af, fun w => ?_⟩
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts40 kf hL hk w
  rw [← hKl] at hK2 hup hlo
  set n := w.length with hn
  set N := Groundwork.ofWord w with hNd
  have hup30 : kN40 kf (Kf 0) w ^ 30 ≤ Kf 0 ^ 40 * (n + 2) :=
    (Nat.pow_le_pow_right (by omega) (by norm_num)).trans hup
  have hPQ := pol_le_Xp (m := 0) hK2 hup30 hlo (hAQ n)
  rw [← hAP] at hPQ
  have hmono : ∀ {A : ℕ}, A ≤ Af → (2 : ℝ) ^ Xp A n 0 ≤ (2 : ℝ) ^ Xp Af n 0 := fun h =>
    Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono h)
  have hPAf := hPQ.trans (hmono (by omega))
  have hnl : (n : ℝ) ≤ (2 : ℝ) ^ Xp Af n 0 := by
    refine le_trans ?_ hPAf; push_cast; linarith
  have hsw : size w = 2 * n + 1 := size_bools w
  by_cases hs : N < 2
  · -- `N = 0, 1`
    have hp : decide (Groundwork.ofWord w < 2) = true := by simpa using hs
    have hr := Stepped.ite_runs_true (p := fun w => decide (Groundwork.ofWord w < 2))
      (N := Stepped.bind (loopR pk E kf (Kf 0)) (Stepped.ofFun outF)) hp (Stepped.ofFun_runs smallF w)
    rw [smallF_eq hs] at hr
    refine ⟨1, _, hr, ?_, ?_, hnl⟩
    · have : (1 : ℝ) ≤ (2 : ℝ) ^ Xp Af n 0 := Real.one_le_rpow one_le_two (Xp_nonneg _ _ _)
      exact_mod_cast this
    · have h5 : size (Nat.bits (Nat.minFac N)) ≤ 5 := by
        rw [← smallF_eq hs, size_bools]; unfold smallF; split_ifs <;> simp
      have hle : max (size w) (size (Nat.bits (Nat.minFac N))) + 1 + 1 ≤ 1000 * (n + 2) := by
        simp only [max_def]; split_ifs <;> omega
      refine le_trans ?_ hPAf
      exact_mod_cast hle
  · -- `N ≥ 2`: the search
    have hN : 2 ≤ N := by omega
    have hp : decide (Groundwork.ofWord w < 2) = false := by simpa using hs
    choose! t ht using fun y (hy : y < n) => hAb w hN y hy
    set Sm := ⌊(2 : ℝ) ^ Xp Ab n 0⌋₊ with hSm
    have hloop := Srch.iterRange_runs (N := fun w : List Bool => w.length) (M := bodyR pk E kf (Kf 0))
      (c₀ := fun _ => []) w (csq w) rfl t (2 * n + 1) Sm (fun y hy => (ht y hy).1)
      (fun y hy => by rw [csq, size_bools, Search.length_searchWith]; omega)
    have hout : outF (w, csq w n) = Nat.bits (Nat.minFac N) := by
      unfold outF; rw [ofWord_reverse, csq_minFac hN]
    have hfin := Stepped.ofFun_runs outF (w, csq w n)
    rw [hout] at hfin
    have hb := Stepped.bind_runs hloop hfin
    have hr := Stepped.ite_runs_false (p := fun w => decide (Groundwork.ofWord w < 2))
      (M := Stepped.ofFun smallF) hp hb
    refine ⟨_, _, hr, ?_, ?_, hnl⟩
    · -- the steps
      have ht1 : ∀ y ∈ range n, t y + 1 ≤ Sm + 1 := fun y hy => by
        have := (ht y (mem_range.1 hy)).2; omega
      have hsumT : ∑ y ∈ range n, (t y + 1) ≤ n * (Sm + 1) := by
        have := Finset.sum_le_sum ht1
        simpa [sum_const, card_range, smul_eq_mul] using this
      have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n 0 := Nat.floor_le (by positivity)
      have h1 : (Sm : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (Ab + 1) n 0 := add_one_le_Xp hSmR
      have hnP : (n : ℝ) ≤ (2 : ℝ) ^ Xp AP n 0 := by refine le_trans ?_ hPQ; push_cast; linarith
      have h2 : (n : ℝ) * ((Sm : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (AP + (Ab + 1)) n 0 :=
        mul_le_Xp (Nat.cast_nonneg _) hnP h1
      have h3 : (n : ℝ) * ((Sm : ℝ) + 1) + 2 ≤ (2 : ℝ) ^ Xp (AP + (Ab + 1) + 2 + 1) n 0 :=
        add_le_Xp h2 (by exact_mod_cast const_le_Xp 2 n 0)
      have h4 : (((∑ y ∈ range n, (t y + 1)) + 1 + 1 : ℕ) : ℝ) ≤ (n : ℝ) * ((Sm : ℝ) + 1) + 2 := by
        have : (((∑ y ∈ range n, (t y + 1)) : ℕ) : ℝ) ≤ ((n * (Sm + 1) : ℕ) : ℝ) := by exact_mod_cast hsumT
        push_cast at this ⊢; linarith
      exact h4.trans (h3.trans (hmono (by omega)))
    · -- the states
      have hmf : Nat.minFac N ≤ N := Nat.minFac_le (by omega)
      have hNlt : N < 2 ^ n := Groundwork.ofWord_lt w
      have hbits : size (Nat.bits (Nat.minFac N)) ≤ 2 * n + 1 := by
        rw [size_bools, Nat.size_eq_bits_len]
        have := Nat.size_le.2 (lt_of_le_of_lt hmf hNlt)
        omega
      have hsn : size n ≤ n + 1 := Asm.size_nat_le' n
      have hpair : size (w, csq w n) = size w + size (csq w n) := rfl
      have hcs : size (csq w n) = 2 * n + 1 := by rw [csq, size_bools, Search.length_searchWith]
      have hle : max (size w + (size w + size n + (2 * n + 1 + Sm) + 1))
          (max (size (w, csq w n)) (size (Nat.bits (Nat.minFac N))) + 1) + 1 + 1 ≤ 1000 * (n + 2) + Sm := by
        rw [hpair, hcs, hsw]
        simp only [max_def]; split_ifs <;> omega
      have hSmR : (Sm : ℝ) ≤ (2 : ℝ) ^ Xp Ab n 0 := Nat.floor_le (by positivity)
      have hall := add_le_Xp hPQ hSmR
      refine le_trans ?_ (hall.trans (hmono (by omega)))
      have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this ⊢; linarith

end FR

open FR EthFollowup.ExactHC EthFollowup.ExactHC.T2 in
/-- **`Nat.minFac` in `2^{O(n/√log n)}` steps, from a multiplication-network package.** Suppose that
for some absolute constant `c₀` there is ONE multiplication-network package (`MulPackage c₀`: one
context type, one set of procedures, one reader handed `g` in unary, one constant `q`). Then there
are ONE Turing machine of Mathlib with finite alphabets and ONE constant `C` such that, for EVERY
natural number `N`, started on `encodeNat N` (length `n`), the machine halts within
`⌊C · 2^{C n/√(log₂(n+2))}⌋` steps with `encodeNat (Nat.minFac N)`.

The route: `n` rounds of binary search for `minFac N` (`Search.searchWith_eq_minFac`), each round one
divisor count `D(N, n, π ++ [0])` by Lemma 8 case (i) on the network of the package with
`g = 3K⁸` nodes, `K = K_ℓ` for the largest level with `K_ℓ ≤ max(⌊n^{1/40}⌋, K₀)`, the clique
machine of Theorem A(b) on the pieces of Theorem B; all in one `Stepped` machine (`FR.facM`), and
`CountKSat.exists_tmW`. -/
theorem minFac_TM_of_pkg (hpkg : ∃ c₀ : ℕ, Nonempty (MulPackage c₀)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, GraphProblems.Outputs M (Computability.encodeNat N) (Computability.encodeNat (Nat.minFac N))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat N).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat N).length + 2)))⌋₊ := by
  obtain ⟨c₀, ⟨pk⟩⟩ := hpkg
  obtain ⟨c, x₀, C₀, D', Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := geBody
  have hL := hyp.levels
  have hk := hyp.computesK
  obtain ⟨A, hA⟩ := facM_runs pk hC₁ hL hk _ hyp.solves (x₀ := x₀) fun l => he l
  obtain ⟨inst⟩ := facM_poly pk _ hL hk hyp.steps
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.exists_tmW (facM pk (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)
    (CliqueLevels.levelsUnder x₀) (Levels.Gen.K x₀ 0))
  obtain ⟨Af, hAf⟩ : ∃ x, x = q + (A + 1) + q * (A + A + 1 + 1) := ⟨_, rfl⟩
  refine ⟨M, 2 ^ (2 * Af), hfin, fun N => ?_⟩
  obtain ⟨T, S, hrun, hT, hS, hLx⟩ := hA (Computability.encodeNat N)
  rw [ofWord_encodeNat, ← encodeNat_eq_bits] at hrun
  obtain ⟨ev⟩ := hM (Computability.encodeNat N) T S _ hrun
  set n := (Computability.encodeNat N).length with hn
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

end EthFollowup.Factoring
