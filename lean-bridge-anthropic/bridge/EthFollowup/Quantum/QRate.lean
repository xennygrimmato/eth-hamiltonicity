/-
# Theorem Q1 at Turing-machine level, rate form: `amplitude_TM_rate`

`research/quantum-circuits.md`, Theorem Q1 and §3.4, with the route of `theorem2_TM`
(`EthFollowup/ExactHC/Theorem2.lean`): the clique machine of Theorem A(b) on the pieces of Theorem B
(`CountedRoute.onTheCountedRecursion`), Lemma 8 case (i) (`ExplicitCost.groupingExplicit`,
`ζ = 1/(2K)`, `g = 3K⁸`) with the network queries answered by the procedures `qNp` of the circuit
network (`stPlug`), and `K = K_ℓ` for the largest level with `K_ℓ ≤ max(⌊(G)^{1/30}⌋, K₀)`, read from
the number `G` of two-qubit gates (`T2.kN` on `G` in unary).

* `qR`: the machine (read the word, pick `K`, build the context of the circuit network with
  `g = 3K⁸` nodes, run Lemma 8, decode); `qR_poly`;
* `netQ_runs`: Lemma 8 + Theorem A(b) on the circuit network, in counted steps;
* `rate_bound`: the cost of one circuit is `≤ 2^{A((G+2)/√log₂(G+2) + (K²+1) log₂(L+2))}`
  (`L` the length of the word); the factor `(K²+1) log₂(L+2)` comes from the polynomial factor
  `(K(L'+B'))^{C₀K²}` of Theorem A(b), since the precision `B` of the stream values grows with the
  number of gates (`ℓ¹` bound of the Kronecker substitution);
* `amplitude_TM_rate`: ONE Turing machine and ONE constant `C` with
  `⌊C · 2^{C·G/√log₂(G+2)} · (L+2)^{C·(G+2)^{1/15}}⌋` steps for EVERY circuit;
* `amplitude_TM_rate'`: when `log₂(L+2) ≤ (G+2)^{9/10}` (Q1's condition `log(G₁+2) ≤ G^{0.9}`, here
  on the whole word), `⌊C · 2^{C·(G+2)/√log₂(G+2)}⌋` steps.
-/
import EthFollowup.Quantum.QTheorem
import EthFollowup.ExactHC.Theorem2

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset Printed QueryMachines

/-! ## The machine -/

/-- The number of two-qubit gates, read from the word. -/
def gW (w : List Bool) : ℕ := (scanA (readQ w).1.length (readQ w).2.2.2).1.length

/-- `G` in unary, as the first component of a graph input (for `T2.kN`, which reads only it). -/
def aQ (w : List Bool) : Asm.GIn := (List.replicate (gW w) (), ([] : List Bool))

section Mach

variable (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
  (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

/-- The number `K` of groups. -/
def kQ (w : List Bool) : ℕ := T2.kN kf K₀ (aQ w)

/-- The context of the circuit network with `g = 3K⁸` nodes. -/
def cQ (w : List Bool) : QCtx := prepQ (3 * kQ kf K₀ w ^ 8) w

/-- The input of Lemma 8 (ζ = 1/(2K), K, g = 3K⁸, Definition 2(iii)) written from the context. -/
def ginQ (c : QCtx) (k : ℕ) : ExplicitCost.GroupingInput :=
  ((1, 2 * k), ((unary k, unary (3 * k ^ 8)),
    inputOf (3 * k ^ 8) (qNp.P c) (qNp.B c) (qNp.len c) (qNp.cap c)))

/-- Lemma 8's procedure with the clique machine `E`, its queries answered by the procedures `qNp`. -/
def GMQ {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : ExplicitCost.CliqueInput → α) :
    Stepped (QCtx × ExplicitCost.GroupingInput) ℤ :=
  (ExplicitCost.groupingData E arg).plug (answerOf qNp)

/-- Lemma 8 on the circuit network of the word. -/
def mainR : Stepped (List Bool) ℤ :=
  Stepped.mapIn (fun w => (cQ kf K₀ w, ginQ (cQ kf K₀ w) (kQ kf K₀ w))) (GMQ E (T2.argF kf K₀))

/-- **The machine of Theorem Q1, rate form.** -/
def qR : Stepped (List Bool) (List Bool) := Stepped.bind (mainR E kf K₀) (Stepped.ofFun finQ)

end Mach

/-! ### Polynomial time -/

namespace QP

theorem gW_unary : Unary gW := by
  have hn : Unary fun w => (readQ w).1.length := Unary.of_length readQ_1
  have h222 := readQ_222
  have hst : PolyT fun w => scanA (readQ w).1.length (readQ w).2.2.2 := scanA_polyT hn h222
  exact Unary.of_length (PolyT.fst hst)

theorem aQ_polyT : PolyT aQ := PolyT.prodMk gW_unary (PolyT.const ([] : List Bool))

/-- The reader with the number of nodes in unary. -/
theorem prepQ_polyG : PolyT fun p : List Unit × List Bool => prepQ p.1.length p.2 := by
  have hR1 : PolyT fun p : List Unit × List Bool => (readQ p.2).1 := PolyT.comp (f := fun w : List Bool => (readQ w).1) (g := fun p : List Unit × List Bool => p.2) readQ_1 PolyT.id'.snd
  have hR21 : PolyT fun p : List Unit × List Bool => (readQ p.2).2.1 := PolyT.comp (f := fun w : List Bool => (readQ w).2.1) (g := fun p : List Unit × List Bool => p.2) readQ_21 PolyT.id'.snd
  have hR221 : PolyT fun p : List Unit × List Bool => (readQ p.2).2.2.1 :=
    PolyT.comp (f := fun w : List Bool => (readQ w).2.2.1) (g := fun p : List Unit × List Bool => p.2) readQ_221 PolyT.id'.snd
  have hR222 : PolyT fun p : List Unit × List Bool => (readQ p.2).2.2.2 :=
    PolyT.comp (f := fun w : List Bool => (readQ w).2.2.2) (g := fun p : List Unit × List Bool => p.2) readQ_222 PolyT.id'.snd
  have hn : Unary fun p : List Unit × List Bool => (readQ p.2).1.length := Unary.of_length hR1
  have hb : Unary fun p : List Unit × List Bool => bK (readQ p.2).1.length (readQ p.2).2.2.2.length :=
    bK_unary.comp PolyT.id'.snd
  have hg : Unary fun p : List Unit × List Bool => p.1.length := Unary.of_length PolyT.id'.fst
  have hst : PolyT fun p : List Unit × List Bool => scanA (readQ p.2).1.length (readQ p.2).2.2.2 :=
    scanA_polyT hn hR222
  have hM : PolyT fun p : List Unit × List Bool => Mb (bK (readQ p.2).1.length (readQ p.2).2.2.2.length) := by
    unfold Mb; exact PolyT.add (PolyT.two_pow ((Unary.const 4).mul hb)) (PolyT.const 1)
  have h1 : PolyT fun p : List Unit × List Bool => 2 ^ bK (readQ p.2).1.length (readQ p.2).2.2.2.length :=
    PolyT.two_pow hb
  have h2 : PolyT fun p : List Unit × List Bool => 2 ^ (2 * bK (readQ p.2).1.length (readQ p.2).2.2.2.length) :=
    PolyT.two_pow ((Unary.const 2).mul hb)
  have h3 : PolyT fun p : List Unit × List Bool => 2 ^ (3 * bK (readQ p.2).1.length (readQ p.2).2.2.2.length) :=
    PolyT.two_pow ((Unary.const 3).mul hb)
  have hG : Unary fun p : List Unit × List Bool => (scanA (readQ p.2).1.length (readQ p.2).2.2.2).1.length :=
    Unary.of_length (PolyT.fst hst)
  have hP : Unary fun p : List Unit × List Bool => PQ (scanA (readQ p.2).1.length (readQ p.2).2.2.2) p.1.length := by
    unfold PQ
    exact (Unary.const 4).mul ((Unary.of_le hG (PolyT.div hG.poly hg.poly) fun w => Nat.div_le_self _ _).add
      (Unary.const 1))
  have hB : Unary fun p : List Unit × List Bool =>
      BQ (scanA (readQ p.2).1.length (readQ p.2).2.2.2) (bK (readQ p.2).1.length (readQ p.2).2.2.2.length) := by
    unfold BQ
    exact (((Unary.const 2).mul hG).add ((Unary.const 4).mul hb)).add (Unary.const 2)
  unfold prepQ
  exact qCtx_polyT hst hg hn hM (PolyT.mod h1 hM) (PolyT.mod h2 hM) (PolyT.mod h3 hM) hR21 hR221 hP hB
    fun w => by unfold Mb; positivity

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem kQ_unary (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    Unary (kQ kf (Kf 0)) := (T2.kN_unary kf hL hk).comp aQ_polyT

theorem gQ_unary (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    Unary fun w => 3 * kQ kf (Kf 0) w ^ 8 := (T2.gN_unary kf hL hk).comp aQ_polyT

theorem cQ_polyT (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf) :
    PolyT (cQ kf (Kf 0)) := by
  have hg := gQ_unary hL hk
  refine (PolyT.comp prepQ_polyG (PolyT.prodMk hg PolyT.id')).congr fun w => ?_
  simp only [cQ, List.length_replicate]

theorem qR_poly (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ) (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf) (hE : E.PolyTimeSteps) : Nonempty (IsPolyT (qR E kf (Kf 0))) := by
  have hc := cQ_polyT hL hk
  have hgm : Nonempty (IsPolyT (GMQ E (T2.argF kf (Kf 0)))) :=
    stPolyPlug _ _ _ _ _ _ _ (ExplicitCost.groupingPoly.2 _ E _ hE (T2.argF_polyT kf hL hk))
      (answerOf_poly qNp qNp_keeps.mem qNp_keeps.W qNp_keeps.Ψ qNp_keeps.f)
  obtain ⟨i1⟩ := hgm
  have hkU := kQ_unary hL hk
  have hgU := gQ_unary hL hk
  have hin : PolyT fun w : List Bool => inputOf (3 * kQ kf (Kf 0) w ^ 8) (qNp.P (cQ kf (Kf 0) w))
      (qNp.B (cQ kf (Kf 0) w)) (qNp.len (cQ kf (Kf 0) w)) (qNp.cap (cQ kf (Kf 0) w)) :=
    ExplicitCost.inputOf_polyT_data hgU (qNp_P.comp hc) (qNp_B.comp hc)
      (qNp_keeps.len.comp (h := fun q : List Bool × ℕ => (cQ kf (Kf 0) q.1, q.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) PolyT.id'.snd))
      (qNp_keeps.cap.comp (h := fun q : List Bool × ℕ × ℕ => (cQ kf (Kf 0) q.1, q.2.1, q.2.2))
        (PolyT.prodMk (hc.comp PolyT.id'.fst) (PolyT.prodMk PolyT.id'.snd.fst PolyT.id'.snd.snd)))
  have hg1 : PolyT fun w : List Bool => (cQ kf (Kf 0) w, ginQ (cQ kf (Kf 0) w) (kQ kf (Kf 0) w)) := by
    unfold ginQ
    have h2k : PolyT fun w : List Bool => 2 * kQ kf (Kf 0) w := PolyT.mul (PolyT.const 2) hkU.poly
    exact PolyT.prodMk hc (PolyT.prodMk (PolyT.prodMk (PolyT.const 1) h2k)
      (PolyT.prodMk (PolyT.prodMk hkU hgU) hin))
  have : IsPolyT (mainR E kf (Kf 0)) := IsPolyT.mapIn hg1
  have : IsPolyT (Stepped.ofFun finQ) := IsPolyT.ofFun finQ_polyT
  exact ⟨IsPolyT.bind⟩

end QP

/-! ## One circuit network: Lemma 8 (case (i)) with the clique machine -/

open T2 in
/-- **Lemma 8 + Theorem A(b) on a network given by the procedures `qNp`** (as `T2.net_runs`). -/
theorem netQ_runs {C₁ : ℕ} (hC₁ : GEBody C₁) {kf : List Unit × List Unit → Option (List Unit)}
    {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀) (l : ℕ) {K : ℕ} (hKl : K = Kf l) {N : Net (3 * K ^ 8)}
    {c : QCtx} {P B τ S : ℕ} (hN : IsNetwork qNp c N P B τ S) :
    ∃ T : ℕ, (GMQ E (argF kf (Kf 0))).Runs (c, ginQ c K) (3 * T)
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
  have hin : ginQ c (Kf l) = ExplicitCost.groupingInput 1 (2 * Kf l) (Kf l) N P B := by
    unfold ginQ ExplicitCost.groupingInput ExplicitCost.dataInput
    rw [← hN.given.P_eq, ← hN.given.B_eq,
      inputOf_eq N (qNp.P c) (qNp.B c) _ _ hN.given.len_eq hN.given.cap_eq]
  refine ⟨T, ?_, hT⟩
  rw [hin]
  exact plug_within _ hN hw

/-! ## The exponent -/

open T2 in
/-- The exponent of the rate form: `A ((G+2)/√log₂(G+2) + (K²+1) log₂(L+2))`. -/
noncomputable def Zq (A K G L : ℕ) : ℝ := A * (((G : ℝ) + 2) / T2.sq G + ((K : ℝ) ^ 2 + 1) * Lam L)

section Expo

open T2 Asm

theorem Zq_inner_nonneg (K G L : ℕ) : 0 ≤ ((G : ℝ) + 2) / T2.sq G + ((K : ℝ) ^ 2 + 1) * Lam L := by
  have := T2.sq_pos G; have := one_le_Lam L; positivity

theorem Zq_nonneg (A K G L : ℕ) : 0 ≤ Zq A K G L := by
  unfold Zq; have := Zq_inner_nonneg K G L; positivity

theorem Zq_add (A B K G L : ℕ) : Zq A K G L + Zq B K G L = Zq (A + B) K G L := by
  unfold Zq; push_cast; ring

theorem Zq_mono {A A' : ℕ} (K G L : ℕ) (h : A ≤ A') : Zq A K G L ≤ Zq A' K G L := by
  unfold Zq
  have hA : (A : ℝ) ≤ A' := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_right hA (Zq_inner_nonneg K G L)

theorem two_Zq_mono {A A' : ℕ} (K G L : ℕ) (h : A ≤ A') : (2 : ℝ) ^ Zq A K G L ≤ (2 : ℝ) ^ Zq A' K G L :=
  Real.rpow_le_rpow_of_exponent_le one_le_two (Zq_mono K G L h)

theorem Lam_le_Zq (A K G L : ℕ) : (A : ℝ) * Lam L ≤ Zq A K G L := by
  unfold Zq
  have h1 := T2.sq_pos G
  have h2 := one_le_Lam L
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have : Lam L ≤ ((G : ℝ) + 2) / T2.sq G + ((K : ℝ) ^ 2 + 1) * Lam L := by
    have : 0 ≤ ((G : ℝ) + 2) / T2.sq G := by positivity
    have : 0 ≤ (K : ℝ) ^ 2 * Lam L := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_left this hA

theorem one_le_Zq_one (K G L : ℕ) : 1 ≤ Zq 1 K G L := by
  have h1 := Lam_le_Zq 1 K G L
  have h2 := one_le_Lam L
  push_cast at h1; linarith

theorem const_le_Zq (k K G L : ℕ) : (k : ℝ) ≤ (2 : ℝ) ^ Zq k K G L := by
  have h1 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast Nat.lt_two_pow_self.le
  refine h1.trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have h2 := Lam_le_Zq k K G L
  have h3 := one_le_Lam L
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem add_le_Zq {x y : ℝ} {A B K G L : ℕ} (hx : x ≤ (2 : ℝ) ^ Zq A K G L) (hy : y ≤ (2 : ℝ) ^ Zq B K G L) :
    x + y ≤ (2 : ℝ) ^ Zq (A + B + 1) K G L := by
  have h1 := two_Zq_mono K G L (by omega : A ≤ A + B)
  have h2 := two_Zq_mono K G L (by omega : B ≤ A + B)
  have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ Zq 1 K G L := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (one_le_Zq_one K G L)
  rw [← Zq_add, Real.rpow_add two_pos]
  have h0 : 0 ≤ (2 : ℝ) ^ Zq (A + B) K G L := by positivity
  nlinarith

theorem add_one_le_Zq {x : ℝ} {A K G L : ℕ} (h : x ≤ (2 : ℝ) ^ Zq A K G L) :
    x + 1 ≤ (2 : ℝ) ^ Zq (A + 1) K G L := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ Zq 0 K G L := by unfold Zq; simp
  have := add_le_Zq h h1
  exact this.trans (two_Zq_mono K G L (by omega))

theorem mul_le_Zq {x y : ℝ} {A B K G L : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ (2 : ℝ) ^ Zq A K G L)
    (hy : y ≤ (2 : ℝ) ^ Zq B K G L) : x * y ≤ (2 : ℝ) ^ Zq (A + B) K G L := by
  rw [← Zq_add, Real.rpow_add two_pos]
  calc x * y ≤ x * (2 : ℝ) ^ Zq B K G L := mul_le_mul_of_nonneg_left hy hx0
    _ ≤ _ := mul_le_mul_of_nonneg_right hx (by positivity)

theorem pow_le_Zq {x : ℝ} {A K G L : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ (2 : ℝ) ^ Zq A K G L) (k : ℕ) :
    x ^ k ≤ (2 : ℝ) ^ Zq (k * A) K G L := by
  have e : Zq (k * A) K G L = Zq A K G L * k := by unfold Zq; push_cast; ring
  rw [e, ← two_rpow_natCast_mul]
  exact pow_le_pow_left₀ hx0 hx k

theorem pol_le_Zq {A L x : ℕ} (K G : ℕ) (h : Pol A L x) : (x : ℝ) ≤ (2 : ℝ) ^ Zq (2 * A) K G L := by
  refine (pol_le_two_rpow h).trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have := Lam_le_Zq (2 * A) K G L
  push_cast at this; linarith

/-- Polynomial bounds, in the length `L` of the word, of the numbers of the circuit network. -/
theorem rate_pol (k₀ qB : ℕ) : ∃ A₀ : ℕ, ∀ (L G K P B U : ℕ), 1 ≤ K → K ^ 30 ≤ k₀ * (G + 2) → G ≤ L →
    U ≤ 4 * G → P = 4 * (G / (3 * K ^ 8) + 1) → B ≤ qB * (L + 2) ^ qB →
    Pol A₀ L (K * (Lc K (3 * K ^ 8) P U + Bc K (3 * K ^ 8) P B)) ∧
    Pol A₀ L (3 * K ^ 8 * (P + B) + size (1, 2 * K)) := by
  let Gb : ℕ → ℕ := fun n => 3 * k₀ * (n + 2)
  let Kb : ℕ → ℕ := fun n => k₀ * (n + 2)
  let Ub : ℕ → ℕ := fun n => 4 * n
  let Pb : ℕ → ℕ := fun n => 4 * n + 4
  let Bb : ℕ → ℕ := fun n => qB * (n + 2) ^ qB
  obtain ⟨aG, hG⟩ : ∃ A, ∀ n, Pol A n (Gb n) :=
    ⟨_, fun n => Pol.mul (Pol.const (3 * k₀)) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨aK, hK⟩ : ∃ A, ∀ n, Pol A n (Kb n) :=
    ⟨_, fun n => Pol.mul (Pol.const k₀) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨aU, hU⟩ : ∃ A, ∀ n, Pol A n (Ub n) := ⟨_, fun n => Pol.mul (Pol.const 4) Pol.id⟩
  obtain ⟨aP, hP⟩ : ∃ A, ∀ n, Pol A n (Pb n) :=
    ⟨_, fun n => Pol.add (Pol.mul (Pol.const 4) Pol.id) (Pol.const 4)⟩
  obtain ⟨aB, hB⟩ : ∃ A, ∀ n, Pol A n (Bb n) :=
    ⟨_, fun n => Pol.mul (Pol.const qB) (Pol.pow (Pol.add Pol.id (Pol.const 2)) qB)⟩
  obtain ⟨a1, h1⟩ : ∃ A, ∀ n, Pol A n (Kb n * ((Ub n + Gb n * Pb n + 1) + (2 * Gb n * Pb n + Kb n + Gb n ^ 2 * Bb n))) :=
    ⟨_, fun n => Pol.mul (hK n) (Pol.add (Pol.add (Pol.add (hU n) (Pol.mul (hG n) (hP n))) (Pol.const 1))
      (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.const 2) (hG n)) (hP n)) (hK n))
        (Pol.mul (Pol.pow (hG n) 2) (hB n))))⟩
  obtain ⟨a2, h2⟩ : ∃ A, ∀ n, Pol A n (Gb n * (Pb n + Bb n) + (2 * Kb n + 3)) :=
    ⟨_, fun n => Pol.add (Pol.mul (hG n) (Pol.add (hP n) (hB n)))
      (Pol.add (Pol.mul (Pol.const 2) (hK n)) (Pol.const 3))⟩
  refine ⟨a1 + a2, fun L G K P B U hK1 hup hGL hUle hPe hBle => ?_⟩
  have hK30 : k₀ * (G + 2) ≤ k₀ * (L + 2) := Nat.mul_le_mul_left _ (by omega)
  have hKK : K ≤ Kb L := by
    have : K ≤ K ^ 30 := Nat.le_self_pow (by norm_num) K
    show K ≤ k₀ * (L + 2); omega
  have hgK : 3 * K ^ 8 ≤ Gb L := by
    have : K ^ 8 ≤ K ^ 30 := Nat.pow_le_pow_right hK1 (by norm_num)
    show 3 * K ^ 8 ≤ 3 * k₀ * (L + 2)
    rw [mul_assoc]; exact Nat.mul_le_mul_left 3 (by omega)
  have hP' : P ≤ Pb L := by
    have : G / (3 * K ^ 8) ≤ G := Nat.div_le_self _ _
    show P ≤ 4 * L + 4; omega
  have hU' : U ≤ Ub L := by show U ≤ 4 * L; omega
  have hB' : B ≤ Bb L := hBle
  have hL' : Lc K (3 * K ^ 8) P U ≤ Ub L + Gb L * Pb L + 1 :=
    (Lc_le K _ P U hK1).trans (by have := Nat.mul_le_mul hgK hP'; omega)
  have hBc' : Bc K (3 * K ^ 8) P B ≤ 2 * Gb L * Pb L + Kb L + Gb L ^ 2 * Bb L :=
    (Bc_le K _ P B).trans (by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hgK) hP'
      have := Nat.mul_le_mul (Nat.pow_le_pow_left hgK 2) hB'
      omega)
  refine ⟨((h1 L).mono (by omega)).le (Nat.mul_le_mul hKK (Nat.add_le_add hL' hBc')),
    ((h2 L).mono (by omega)).le ?_⟩
  have := size_pair_le K
  have := Nat.mul_le_mul hgK (Nat.add_le_add hP' hB')
  omega

end Expo

/-! ## The cost of one circuit -/

section Cost

open T2 Asm

/-- The lower-order terms (`T2.prod_facts` with `m = 0`, `n = G`). -/
theorem prodG {G K c₁ k₀ : ℕ} (hK : 2 ≤ K) (hup : K ^ 30 ≤ k₀ * (G + 2)) (hlo : G + 2 ≤ K ^ c₁) :
    (∀ j ≤ 29, (K : ℝ) ^ j * T2.sq G ≤ c₁ * k₀ * ((G : ℝ) + 2)) ∧
    ((G : ℝ) + 2) / K * T2.sq G ≤ c₁ * ((G : ℝ) + 2) := by
  obtain ⟨pj, pM, -, -⟩ := prod_facts (m := 0) hK hup hlo
  simp only [Nat.cast_zero, zero_add] at pj pM
  exact ⟨pj, pM⟩

/-- The exponent of the network part of the cost, against `A (G+2)/√log₂(G+2)`. -/
theorem gpart_le {G K P U c₁ k₀ x₀ : ℕ} {e L' : ℝ} (hK2 : 2 ≤ K) (hup : K ^ 30 ≤ k₀ * (G + 2))
    (hlo : G + 2 ≤ K ^ c₁) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (heK : e ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 K))
    (hU : U ≤ 4 * G) (hP : P = 4 * (G / (3 * K ^ 8) + 1))
    (hKL : (K : ℝ) ^ 2 * L' ≤ U + ((3 * K ^ 8 : ℕ) : ℝ) * P / K + (K : ℝ) ^ 2) :
    (3 + ((K * (3 * K ^ 8) : ℕ) : ℝ) + e * (K : ℝ) ^ 2 * L' + 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K +
      ((2 * (G / (3 * K ^ 8) + 1) + 1 : ℕ) : ℝ)) * T2.sq G ≤
      (((50 * k₀ + 20 + 4 * (3 * x₀ + 6)) * c₁ : ℕ) : ℝ) * ((G : ℝ) + 2) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hK0 : (0 : ℝ) < K := by linarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hs0 := T2.sq_pos G
  have hG0 : (0 : ℝ) ≤ (G : ℝ) + 2 := by positivity
  obtain ⟨pj, pM⟩ := prodG (c₁ := c₁) hK2 hup hlo
  have he := e_sq_le hK2 hlo he0 (Nat.cast_nonneg _) heK
  obtain ⟨q, hq⟩ : ∃ q, q = G / (3 * K ^ 8) := ⟨_, rfl⟩
  rw [← hq] at hP ⊢
  have hgq : 3 * K ^ 8 * q ≤ G := hq ▸ Nat.mul_div_le G _
  have hgqr : 3 * (K : ℝ) ^ 8 * q ≤ G := by exact_mod_cast hgq
  have hgP : ((3 * K ^ 8 : ℕ) : ℝ) * P ≤ 4 * G + 12 * (K : ℝ) ^ 8 := by
    rw [hP]; push_cast; nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((3 * K ^ 8 : ℕ) : ℝ) * P / K := ⟨_, rfl⟩
  have e4 : 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K = 2 * y := by rw [hy]; ring
  rw [← hy] at hKL
  rw [e4]
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyb : y ≤ 4 * (((G : ℝ) + 2) / K) + 12 * (K : ℝ) ^ 7 := by
    rw [hy, div_le_iff₀ hK0]
    have : 4 * (((G : ℝ) + 2) / K) * K = 4 * ((G : ℝ) + 2) := by field_simp
    have : (4 * (((G : ℝ) + 2) / K) + 12 * (K : ℝ) ^ 7) * K = 4 * ((G : ℝ) + 2) + 12 * (K : ℝ) ^ 8 := by
      field_simp
    nlinarith
  have hqK : (q : ℝ) ≤ ((G : ℝ) + 2) / K := by
    rw [le_div_iff₀ hK0]
    have : (K : ℝ) ≤ 3 * (K : ℝ) ^ 8 := by
      have : (K : ℝ) ≤ (K : ℝ) ^ 8 := le_self_pow₀ hK1 (by norm_num)
      linarith
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  have hUr : (U : ℝ) ≤ 4 * ((G : ℝ) + 2) := by
    have : (U : ℝ) ≤ 4 * G := by exact_mod_cast hU
    linarith
  have f0 := pj 0 (by norm_num)
  rw [pow_zero, one_mul] at f0
  have f2 := pj 2 (by norm_num)
  have f7 := pj 7 (by norm_num)
  have f9 := pj 9 (by norm_num)
  have fy : y * T2.sq G ≤ 4 * (c₁ * ((G : ℝ) + 2)) + 12 * (c₁ * k₀ * ((G : ℝ) + 2)) := by
    calc y * T2.sq G ≤ (4 * (((G : ℝ) + 2) / K) + 12 * (K : ℝ) ^ 7) * T2.sq G :=
          mul_le_mul_of_nonneg_right hyb hs0.le
      _ = 4 * (((G : ℝ) + 2) / K * T2.sq G) + 12 * ((K : ℝ) ^ 7 * T2.sq G) := by ring
      _ ≤ _ := by linarith
  have ha0 : (0 : ℝ) ≤ ((3 * x₀ + 6 : ℕ) : ℝ) * c₁ := by positivity
  have feU : e * U * T2.sq G ≤ ((3 * x₀ + 6 : ℕ) : ℝ) * c₁ * (4 * ((G : ℝ) + 2)) := by
    calc e * U * T2.sq G = (e * T2.sq G) * U := by ring
      _ ≤ (((3 * x₀ + 6 : ℕ) : ℝ) * c₁) * U := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hUr ha0
  have hT : e * (K : ℝ) ^ 2 * L' ≤ e * U + y + (K : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ y + (K : ℝ) ^ 2 := by positivity
    calc e * (K : ℝ) ^ 2 * L' = e * ((K : ℝ) ^ 2 * L') := by ring
      _ ≤ e * (U + y + (K : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hKL he0
      _ = e * U + e * (y + (K : ℝ) ^ 2) := by ring
      _ ≤ e * U + 1 * (y + (K : ℝ) ^ 2) := by
          have := mul_le_mul_of_nonneg_right he1 h0; linarith
      _ = _ := by ring
  have fT := mul_le_mul_of_nonneg_right hT hs0.le
  have fq : (q : ℝ) * T2.sq G ≤ c₁ * ((G : ℝ) + 2) := (mul_le_mul_of_nonneg_right hqK hs0.le).trans pM
  have e1 : ((K * (3 * K ^ 8) : ℕ) : ℝ) = 3 * (K : ℝ) ^ 9 := by push_cast; ring
  have e3 : ((2 * (q + 1) + 1 : ℕ) : ℝ) = 2 * q + 3 := by push_cast; ring
  rw [e1, e3]
  push_cast at feU ⊢
  have t1 : 0 ≤ (c₁ : ℝ) * k₀ * ((G : ℝ) + 2) := by positivity
  have t2 : 0 ≤ (c₁ : ℝ) * ((G : ℝ) + 2) := by positivity
  linarith [f0, f2, f9, fy, feU, fT, fq]

/-- **The cost of one circuit**: the steps (three times the bound of Lemma 8) and the state bound
are at most `2^{A((G+2)/√log₂(G+2) + (K²+1) log₂(L+2))}`, for one constant `A` that depends only
on the constants of Lemma 8, of Theorem A(b), of the level choice and of the polynomial bounds. -/
theorem rate_bound (C₁ C₀ x₀ k₀ c₁ qB qS : ℕ) : ∃ A : ℕ, ∀ (L G K P B τ S U sc : ℕ) (e : ℝ),
    2 ≤ K → K ^ 30 ≤ k₀ * (G + 2) → G + 2 ≤ K ^ c₁ → 0 ≤ e → e ≤ 1 →
    e ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 K) → G ≤ L → U ≤ 4 * G →
    P = 4 * (G / (3 * K ^ 8) + 1) → B ≤ qB * (L + 2) ^ qB → τ = 2 * 2 ^ (2 * (G / (3 * K ^ 8) + 1)) →
    S + sc ≤ qS * (L + 2) ^ qS →
    3 * (((K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) *
        (2 : ℝ) ^ (2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K) * τ) * (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁)
      ≤ (2 : ℝ) ^ Zq A K G L ∧
    ((sc + (Tc e K C₀ (Lc K (3 * K ^ 8) P U) (Bc K (3 * K ^ 8) P B) +
      (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Zq A K G L := by
  obtain ⟨A₀, hA₀⟩ := rate_pol k₀ qB
  obtain ⟨A₁, hA₁⟩ : ∃ x, x = A₀ + qS := ⟨_, rfl⟩
  obtain ⟨AG, hAG⟩ : ∃ x, x = (50 * k₀ + 20 + 4 * (3 * x₀ + 6)) * c₁ := ⟨_, rfl⟩
  obtain ⟨AL, hAL⟩ : ∃ x, x = 2 * A₁ * C₀ + 2 * A₁ * C₁ + 2 * A₁ := ⟨_, rfl⟩
  refine ⟨AG + AL, ?_⟩
  intro L G K P B τ S U sc e hK2 hup hlo he0 he1 heK hGL hU hP hB hτ hS
  obtain ⟨h1, h2⟩ := hA₀ L G K P B U (by omega) hup hGL hU hP hB
  have h1' := h1.mono (show A₀ ≤ A₁ by omega)
  have h2' := h2.mono (show A₀ ≤ A₁ by omega)
  have h3' : Pol A₁ L (S + sc) := (show Pol qS L (S + sc) from hS).mono (by omega)
  have hΛ1 : 1 ≤ Lam L := one_le_Lam L
  have hx1 := pol_le_two_rpow h1'
  have hx2 := pol_le_two_rpow h2'
  have hx3 := pol_le_two_rpow h3'
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hK0 : (0 : ℝ) < K := by linarith
  have hs0 := T2.sq_pos G
  set Pw : ℝ := (2 : ℝ) ^ (2 * A₁ * Lam L) with hPwd
  set L' := Lc K (3 * K ^ 8) P U with hLd
  set B' := Bc K (3 * K ^ 8) P B with hB'd
  set XT : ℝ := e * (K : ℝ) ^ 2 * L' + 2 * A₁ * Lam L * ((C₀ * K ^ 2 : ℕ) : ℝ) with hXT
  set x4 : ℝ := 2 * ((3 * K ^ 8 : ℕ) : ℝ) * P / K with hx4
  set xτ : ℝ := ((2 * (G / (3 * K ^ 8) + 1) + 1 : ℕ) : ℝ) with hxτ
  set X1 : ℝ := ((K * (3 * K ^ 8) : ℕ) : ℝ) with hX1
  set X2 : ℝ := XT + x4 + xτ + 2 * A₁ * Lam L with hX2
  set X3 : ℝ := 2 * A₁ * Lam L * C₁ with hX3
  have hXT0 : 0 ≤ XT := by positivity
  have hx40 : 0 ≤ x4 := by positivity
  have hxτ0 : 0 ≤ xτ := by positivity
  have hX10 : 0 ≤ X1 := by positivity
  have hX30 : 0 ≤ X3 := by positivity
  have hAΛ0 : (0 : ℝ) ≤ 2 * A₁ * Lam L := by positivity
  have hX20 : 0 ≤ X2 := by positivity
  -- the factors
  have hT : (Tc e K C₀ L' B' : ℝ) ≤ (2 : ℝ) ^ XT := by
    have hb : CliqueLevels.bound e K C₀ L' B' ≤ (2 : ℝ) ^ XT := by
      unfold CliqueLevels.bound
      have hx1' : (K : ℝ) * ((L' : ℝ) + B') ≤ Pw := by push_cast at hx1; exact hx1
      calc (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L') * ((K : ℝ) * ((L' : ℝ) + B')) ^ (C₀ * K ^ 2)
          ≤ (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L') * Pw ^ (C₀ * K ^ 2) := by gcongr
        _ = (2 : ℝ) ^ XT := by
          rw [hXT, Real.rpow_add two_pos, hPwd, two_rpow_natCast_mul]
    exact (Nat.floor_le (by unfold CliqueLevels.bound; positivity)).trans hb
  have hτr : (τ : ℝ) = (2 : ℝ) ^ xτ := by
    rw [hxτ, Real.rpow_natCast, hτ]; push_cast; ring
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
  have e2 : (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * (2 : ℝ) ^ xτ ≤ (2 : ℝ) ^ X2 := by
    rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hY1 : (2 : ℝ) ^ X1 * (2 : ℝ) ^ X3 ≤ (2 : ℝ) ^ (X1 + X2 + X3) := by
    rw [← Real.rpow_add two_pos]; exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hY2 : (2 : ℝ) ^ X2 * (2 : ℝ) ^ X3 ≤ (2 : ℝ) ^ (X1 + X2 + X3) := by
    rw [← Real.rpow_add two_pos]; exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hY3 : (2 : ℝ) ^ X3 ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hYT : (2 : ℝ) ^ XT ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hYPw : Pw ≤ (2 : ℝ) ^ (X1 + X2 + X3) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hY0 : (1 : ℝ) ≤ (2 : ℝ) ^ (X1 + X2 + X3) := Real.one_le_rpow one_le_two (by linarith)
  have h8 : (2 : ℝ) ^ (3 + X1 + X2 + X3) = 8 * (2 : ℝ) ^ (X1 + X2 + X3) := by
    rw [add_assoc, add_assoc, Real.rpow_add two_pos]; norm_num; ring_nf
  -- the exponent
  have hfin : 3 + X1 + X2 + X3 ≤ Zq (AG + AL) K G L := by
    have hKL := K2L_le K (3 * K ^ 8) P U (by omega)
    rw [← hLd] at hKL
    have hg := gpart_le hK2 hup hlo he0 he1 heK hU hP hKL
    rw [← hAG] at hg
    have hgd : 3 + X1 + e * (K : ℝ) ^ 2 * L' + x4 + xτ ≤ (AG : ℝ) * (((G : ℝ) + 2) / T2.sq G) := by
      rw [mul_div_assoc', le_div_iff₀ hs0]; exact hg
    have hLp : 2 * A₁ * Lam L * ((C₀ * K ^ 2 : ℕ) : ℝ) + 2 * A₁ * Lam L + X3 ≤
        (AL : ℝ) * (((K : ℝ) ^ 2 + 1) * Lam L) := by
      rw [hAL, hX3]; push_cast
      have t1 : 0 ≤ (A₁ : ℝ) * C₀ * Lam L := by positivity
      have t2 : 0 ≤ (A₁ : ℝ) * C₁ * Lam L * (K : ℝ) ^ 2 := by positivity
      have t3 : 0 ≤ (A₁ : ℝ) * Lam L * (K : ℝ) ^ 2 := by positivity
      linarith
    have hZ : (AG : ℝ) * (((G : ℝ) + 2) / T2.sq G) + (AL : ℝ) * (((K : ℝ) ^ 2 + 1) * Lam L) ≤
        Zq (AG + AL) K G L := by
      unfold Zq; push_cast
      have t1 : 0 ≤ (AG : ℝ) * (((K : ℝ) ^ 2 + 1) * Lam L) := by positivity
      have t2 : 0 ≤ (AL : ℝ) * (((G : ℝ) + 2) / T2.sq G) := by positivity
      linarith
    have hsplit : 3 + X1 + X2 + X3 = (3 + X1 + e * (K : ℝ) ^ 2 * L' + x4 + xτ) +
        (2 * A₁ * Lam L * ((C₀ * K ^ 2 : ℕ) : ℝ) + 2 * A₁ * Lam L + X3) := by
      rw [hX2, hXT]; ring
    rw [hsplit]; linarith
  constructor
  · calc 3 * (((K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ L' B' * (2 : ℝ) ^ x4 * τ) *
          (((3 * K ^ 8 : ℕ) : ℝ) * (P + B)) ^ C₁)
        ≤ 3 * (((2 : ℝ) ^ X1 + (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * (2 : ℝ) ^ xτ) * (2 : ℝ) ^ X3) := by
          have hA : (K : ℝ) ^ (3 * K ^ 8) + Tc e K C₀ L' B' * (2 : ℝ) ^ x4 * τ ≤
              (2 : ℝ) ^ X1 + (2 : ℝ) ^ XT * (2 : ℝ) ^ x4 * (2 : ℝ) ^ xτ := by
            rw [hτr]
            exact add_le_add hKg (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT (by positivity))
              (by positivity))
          exact mul_le_mul_of_nonneg_left (mul_le_mul hA hgPB (by positivity) (by positivity))
            (by norm_num)
      _ ≤ 3 * (((2 : ℝ) ^ X1 + (2 : ℝ) ^ X2) * (2 : ℝ) ^ X3) := by gcongr
      _ ≤ 3 * (((2 : ℝ) ^ (X1 + X2 + X3) + (2 : ℝ) ^ (X1 + X2 + X3))) := by
          rw [add_mul]; linarith
      _ ≤ (2 : ℝ) ^ (3 + X1 + X2 + X3) := by rw [h8]; linarith
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hfin
  · have hx3' : ((S + sc : ℕ) : ℝ) ≤ Pw := hx3
    have hgx : (((3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁ : ℕ) : ℝ) ≤ (2 : ℝ) ^ X3 := by
      push_cast; push_cast at hx2
      calc ((3 : ℝ) * (K : ℝ) ^ 8 * (P + B) + (size (1, 2 * K) : ℝ)) ^ C₁ ≤ Pw ^ C₁ := by gcongr
        _ = (2 : ℝ) ^ X3 := two_rpow_natCast_mul _ _
    calc ((sc + (Tc e K C₀ L' B' + (3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁) + (S + 3) + 1 : ℕ) : ℝ)
        = ((S + sc : ℕ) : ℝ) + (Tc e K C₀ L' B' : ℝ) +
          (((3 * K ^ 8 * (P + B) + size (1, 2 * K)) ^ C₁ : ℕ) : ℝ) + 4 := by push_cast; ring
      _ ≤ (2 : ℝ) ^ (X1 + X2 + X3) + (2 : ℝ) ^ (X1 + X2 + X3) + (2 : ℝ) ^ (X1 + X2 + X3) +
          4 * (2 : ℝ) ^ (X1 + X2 + X3) := by linarith
      _ ≤ (2 : ℝ) ^ (3 + X1 + X2 + X3) := by rw [h8]; linarith
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hfin

end Cost

/-! ## The machine on every circuit -/

theorem gW_code {n : ℕ} (C : List (Gate n)) (x y : Basis n) : gW (circCode C x y) = (stC C).1.length := by
  unfold gW
  rw [readQ_code]
  simp only [List.length_replicate]
  rw [scanA_eq _ (validC_codes C)]

open T2 Asm in
/-- **The rate machine on every circuit**: with `K` the level picked for `G` two-qubit gates, the
machine outputs the decoded residue of a nonnegative integer `Z ≡ P(2^b) (mod M_b)` within
`2^{Zq A K G L}` steps on states of size `≤ 2^{Zq A K G L}`. -/
theorem qR_bound {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ} {kf : List Unit × List Unit → Option (List Unit)}
    {Kf : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : CliqueLevels.Levels Kf e C₀)
    (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀ l, e l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (Real.logb 2 (Kf l))) :
    ∃ A : ℕ, ∀ {n : ℕ} (C : List (Gate n)) (x y : Basis n), ∃ (Z : ℤ) (K T S : ℕ),
      0 ≤ Z ∧ (Z : ZMod (MC C)) = evR ((2 : ZMod (MC C)) ^ bC C) (ampPoly C x y) ∧
      2 ≤ K ∧ K ^ 30 ≤ Kf 0 ^ 30 * (twoCount C + 2) ∧
      (qR E kf (Kf 0)).Runs (circCode C x y) T S
        (outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C)) ∧
      (T : ℝ) ≤ (2 : ℝ) ^ Zq A K (twoCount C) (circCode C x y).length ∧
      (S : ℝ) ≤ (2 : ℝ) ^ Zq A K (twoCount C) (circCode C x y).length := by
  obtain ⟨-, cP, -, hlenP⟩ := QP.prepQ_polyG
  obtain ⟨-, cF, -, hlenF⟩ := QP.finQ_polyT
  obtain ⟨k₀, hk₀⟩ : ∃ x, x = Kf 0 ^ 30 := ⟨_, rfl⟩
  -- the polynomials in the length `L` of the word
  obtain ⟨fg, hfg⟩ : ∃ f : ℕ → ℕ, f = fun L => 3 * k₀ * (L + 2) := ⟨_, rfl⟩
  obtain ⟨fB, hfB⟩ : ∃ f : ℕ → ℕ, f = fun L => 2 * L + 4 * ((L + 1) * L + 2) + 2 := ⟨_, rfl⟩
  obtain ⟨fc, hfc⟩ : ∃ f : ℕ → ℕ, f = fun L => cP * ((4 * fg L + 2) + (3 * L + 2) + 2 + 1) ^ cP := ⟨_, rfl⟩
  obtain ⟨fS, hfS⟩ : ∃ f : ℕ → ℕ, f = fun L => 7 * fc L + 8 * (4 * L + 4) + 6 * (L + 1) + 2 * fg L + 28 :=
    ⟨_, rfl⟩
  obtain ⟨fZ, hfZ⟩ : ∃ f : ℕ → ℕ, f = fun L => 2 * L + fg L * fB L + 2 := ⟨_, rfl⟩
  obtain ⟨fO, hfO⟩ : ∃ f : ℕ → ℕ, f = fun L => cF * ((3 * L + 2) + (3 * fZ L + 5) + 2 + 1) ^ cF := ⟨_, rfl⟩
  obtain ⟨fW, hfW⟩ : ∃ f : ℕ → ℕ, f = fun L => (2 * L + 1) + (2 * L + 1 + fZ L) + fO L + 4 := ⟨_, rfl⟩
  have pg : ∃ A, ∀ L, Pol A L (fg L) := ⟨_, fun L => by
    rw [hfg]; exact Pol.mul (Pol.const (3 * k₀)) (Pol.add Pol.id (Pol.const 2))⟩
  obtain ⟨ag, hg⟩ := pg
  have pB : ∃ A, ∀ L, Pol A L (fB L) := ⟨_, fun L => by
    rw [hfB]; exact Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id)
      (Pol.mul (Pol.const 4) (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 1)) Pol.id) (Pol.const 2)))) (Pol.const 2)⟩
  obtain ⟨qB, hqB⟩ := pB
  have pc : ∃ A, ∀ L, Pol A L (fc L) := ⟨_, fun L => by
    rw [hfc]; exact Pol.mul (Pol.const cP) (Pol.pow (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 4) (hg L))
      (Pol.const 2)) (Pol.add (Pol.mul (Pol.const 3) Pol.id) (Pol.const 2))) (Pol.const 2)) (Pol.const 1)) cP)⟩
  obtain ⟨ac, hc⟩ := pc
  have pS : ∃ A, ∀ L, Pol A L (fS L) := ⟨_, fun L => by
    rw [hfS]; exact Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 7) (hc L))
      (Pol.mul (Pol.const 8) (Pol.add (Pol.mul (Pol.const 4) Pol.id) (Pol.const 4))))
      (Pol.mul (Pol.const 6) (Pol.add Pol.id (Pol.const 1)))) (Pol.mul (Pol.const 2) (hg L))) (Pol.const 28)⟩
  obtain ⟨qS, hqS⟩ := pS
  have pZ : ∃ A, ∀ L, Pol A L (fZ L) := ⟨_, fun L => by
    rw [hfZ]; exact Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.mul (hg L) (hqB L))) (Pol.const 2)⟩
  obtain ⟨aZ, hZ⟩ := pZ
  have pO : ∃ A, ∀ L, Pol A L (fO L) := ⟨_, fun L => by
    rw [hfO]; exact Pol.mul (Pol.const cF) (Pol.pow (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 3) Pol.id)
      (Pol.const 2)) (Pol.add (Pol.mul (Pol.const 3) (hZ L)) (Pol.const 5))) (Pol.const 2)) (Pol.const 1)) cF)⟩
  obtain ⟨aO, hO⟩ := pO
  have pW : ∃ A, ∀ L, Pol A L (fW L) := ⟨_, fun L => by
    rw [hfW]; exact Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
      (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1)) (hZ L))) (hO L)) (Pol.const 4)⟩
  obtain ⟨AW, hAW⟩ := pW
  obtain ⟨A₁, hA₁⟩ := rate_bound C₁ C₀ x₀ k₀ (30 * C₀ + 1) qB qS
  refine ⟨A₁ + 2 * AW + 3, fun {n} C x y => ?_⟩
  rw [← twoCount_eq C]
  -- the word and the level
  set w := circCode C x y with hw
  set L := w.length with hLdef
  set G := (stC C).1.length with hGdef
  have hlen : L = n + 1 + n + n + C.length * (4 + 2 * n) := length_circCode C x y
  have hn : n ≤ L := by omega
  have hm : C.length ≤ L := by nlinarith
  have hGL : G ≤ L := by rw [hGdef, twoCount_eq]; exact (twoCount_le C).trans hm
  have haQ : (aQ w).1.length = G := by
    show (List.replicate (gW w) ()).length = G
    rw [List.length_replicate, hw, gW_code]
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aQ w) haQ
  rw [← hk₀] at hup
  set K := kQ kf (Kf 0) w with hKdef
  have hKl' : K = Kf l := hKl
  rw [← hKl'] at hK2 hup hlo
  set g := 3 * K ^ 8 with hgdef
  have hg1 : 1 ≤ g := by have : 1 ≤ K ^ 8 := Nat.one_le_pow _ _ (by omega); omega
  haveI : NeZero g := ⟨by omega⟩
  have hgL : g ≤ fg L := by
    have : K ^ 8 ≤ K ^ 30 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : k₀ * (G + 2) ≤ k₀ * (L + 2) := Nat.mul_le_mul_left _ (by omega)
    rw [hfg]; show 3 * K ^ 8 ≤ 3 * k₀ * (L + 2); rw [mul_assoc]; omega
  -- the network and Lemma 8
  set N := (XC g C x y).net boolCode with hNdef
  set Z := N.value with hZdef
  set P := PQ (stC C) g with hPdef
  set B := BQ (stC C) (bC C) with hBdef
  set τ := τQ (stC C) g with hτdef
  set S' := SQ (stC C) g (cC g C x y) P + size (cC g C x y) + 2 * g + 4 * P + 8 with hS'def
  have hcQ : cQ kf (Kf 0) w = cC g C x y := prep_cC g C x y
  have hN : IsNetwork qNp (cC g C x y) N P B τ S' := (qGiven g C x y).1
  obtain ⟨T, hrun, hT⟩ := netQ_runs hC₁ hL hk E hsol l hKl' hN
  have hmain : (mainR E kf (Kf 0)).Runs w (3 * T) (size (cC g C x y) +
      (Tc (e l) K C₀ (Lc K g P N.U) (Bc K g P B) + (g * (P + B) + size (1, 2 * K)) ^ C₁) + (S' + 3) + 1) Z := by
    apply Stepped.mapIn_runs
    show (GMQ E (argF kf (Kf 0))).Runs (cQ kf (Kf 0) w, ginQ (cQ kf (Kf 0) w) K) _ _ _
    rw [hcQ]; exact hrun
  have hout : finQ (w, Z) = outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C) := by
    unfold finQ bW
    simp only [w, readQ_code, List.length_replicate, length_codes, hcount_eq]
  have hfin := Stepped.ofFun_runs finQ (w, Z)
  rw [hout] at hfin
  have hrun2 := Stepped.bind_runs hmain hfin
  -- the numbers
  have hbb : bC C ≤ (L + 1) * L + 2 := by
    show (n + 1) * C.length + 2 ≤ _; have := Nat.mul_le_mul (Nat.add_le_add_right hn 1) hm; omega
  have hBB : B ≤ fB L := by
    show 2 * G + 4 * bC C + 2 ≤ _; rw [hfB]; beta_reduce; omega
  have hgG : G / g ≤ L := (Nat.div_le_self _ _).trans hGL
  have hPP : P ≤ 4 * L + 4 := by show 4 * (G / g + 1) ≤ _; omega
  have hlw : len w = 3 * L + 2 := len_bools w
  have hcc : size (cC g C x y) ≤ fc L := by
    have h1 : size (cC g C x y) ≤ len (cC g C x y) := SizeLe.le _
    have h2 := hlenP (List.replicate g (), w)
    dsimp only at h2
    rw [List.length_replicate, prep_cC, len_pair (List.replicate g ()) w, len_units, List.length_replicate, hlw] at h2
    refine h1.trans (h2.trans ?_)
    rw [hfc]; beta_reduce
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hsw : size w = 2 * L + 1 := LabelSystem.size_word w
  have hK := length_cl_le (stC C) g
  have hU : N.U ≤ 4 * G := by
    have := LabelSystem.U_eq (XC g C x y) boolCode
    simp only [Fintype.card_fin, Fintype.card_eq_zero, add_zero, mul_one] at this
    show N.U ≤ _; rw [this]; omega
  have hZnat : Z.natAbs.size ≤ 2 * L + fg L * fB L + 1 := by
    have h1 := value_le g C x y
    have h2 : Z.natAbs < 2 ^ ((cpart (stC C) g).cl.length + g * B + 1) :=
      lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
    have h3 := Nat.size_le.2 h2
    have h4 : g * B ≤ fg L * fB L := Nat.mul_le_mul hgL hBB
    omega
  have hZs : size Z ≤ fZ L := by show Z.natAbs.size + 1 ≤ _; rw [hfZ]; beta_reduce; omega
  have hOs : size (outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C)) ≤ fO L := by
    have h1 := SizeLe.le (outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C))
    have h2 := hlenF (w, Z)
    rw [hout, len_pair, hlw, len_int] at h2
    refine h1.trans (h2.trans ?_)
    rw [hfO]; beta_reduce
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have : Z.natAbs.size + 1 ≤ fZ L := hZs
    omega
  have hSS : S' + size (cC g C x y) ≤ qS * (L + 2) ^ qS := by
    have e1 : SQ (stC C) g (cC g C x y) P = 5 * size (cC g C x y) + 4 * P + 6 * (G / g + 1) + 20 := rfl
    have h1 : S' + size (cC g C x y) ≤ fS L := by
      rw [hS'def, e1, hfS]; simp only; omega
    exact h1.trans (hqS L)
  have he0 : 0 ≤ e l := by
    have h1 := hL.e_ge l
    have hK1 : (1 : ℝ) < Kf l := by exact_mod_cast (by have := hL.K_two l; omega : 1 < Kf l)
    have : 0 < Real.logb 2 (Kf l) := Real.logb_pos one_lt_two hK1
    exact le_trans (by positivity) h1
  have heK := he l
  rw [← hKl'] at heK
  obtain ⟨hb1, hb2⟩ := hA₁ L G K P B τ S' N.U (size (cC g C x y)) (e l) hK2 hup hlo he0 (hL.e_le l) heK
    hGL hU rfl ((hBB.trans (hqB L))) rfl hSS
  refine ⟨Z, K, 3 * T + 1 + 1, _, value_nonneg g C x y, ?_, hK2, ?_, hrun2, ?_, ?_⟩
  · exact qValue g C x y
  · rw [hk₀] at hup; exact hup
  · -- the steps
    have h3T : ((3 * T : ℕ) : ℝ) ≤ (2 : ℝ) ^ Zq A₁ K G L := by
      push_cast
      have : (0 : ℝ) ≤ 3 := by norm_num
      exact (mul_le_mul_of_nonneg_left hT this).trans hb1
    have h2 := const_le_Zq 2 K G L
    have := add_le_Zq h3T h2
    refine le_trans ?_ (this.trans (two_Zq_mono K G L (by omega)))
    push_cast; linarith
  · -- the states
    have hW := pol_le_Zq K G (hAW L)
    have hsum := add_le_Zq hb2 hW
    refine le_trans ?_ (hsum.trans (two_Zq_mono K G L (by omega)))
    clear_value Z w
    have hpair : size (w, Z) = size w + size Z := Groundwork.size_prod (w, Z)
    have hle : max (size w + (size (cC g C x y) + (Tc (e l) K C₀ (Lc K g P N.U) (Bc K g P B) +
        (g * (P + B) + size (1, 2 * K)) ^ C₁) + (S' + 3) + 1))
        (max (size (w, Z)) (size (outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C))) + 1) + 1 ≤
        (size (cC g C x y) + (Tc (e l) K C₀ (Lc K g P N.U) (Bc K g P B) +
          (g * (P + B) + size (1, 2 * K)) ^ C₁) + (S' + 3) + 1) + fW L := by
      rw [hpair, hfW]; simp only
      have := hsw; have := hZs; have := hOs
      simp only [max_def]; split_ifs <;> omega
    exact_mod_cast hle

/-! ## Theorem Q1, rate form -/

/-- `K² + 1 ≤ (k₀ + 1)(G+2)^{1/15}` when `K³⁰ ≤ k₀ (G+2)`. -/
theorem K2_le_root {K k₀ G : ℕ} (hk₀ : 1 ≤ k₀) (hup : K ^ 30 ≤ k₀ * (G + 2)) :
    (K : ℝ) ^ 2 + 1 ≤ ((k₀ : ℝ) + 1) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) := by
  have hG1 : (1 : ℝ) ≤ (G : ℝ) + 2 := by have : (0 : ℝ) ≤ G := Nat.cast_nonneg G; linarith
  have hk1 : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
  have e15 : ((1 : ℝ) / 15) = ((15 : ℕ) : ℝ)⁻¹ := by norm_num
  have h1 : (K : ℝ) ^ 2 = (((K : ℝ) ^ 2) ^ 15) ^ ((1 : ℝ) / 15) := by
    rw [e15, Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have h2 : ((K : ℝ) ^ 2) ^ 15 ≤ (k₀ : ℝ) * ((G : ℝ) + 2) := by
    rw [← pow_mul]; exact_mod_cast hup
  have h3 : (K : ℝ) ^ 2 ≤ ((k₀ : ℝ) * ((G : ℝ) + 2)) ^ ((1 : ℝ) / 15) := by
    rw [h1]; exact Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  rw [Real.mul_rpow (by positivity) (by positivity)] at h3
  have h4 : (k₀ : ℝ) ^ ((1 : ℝ) / 15) ≤ k₀ := by
    calc (k₀ : ℝ) ^ ((1 : ℝ) / 15) ≤ (k₀ : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
      _ = k₀ := Real.rpow_one _
  have h5 : (1 : ℝ) ≤ ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) := Real.one_le_rpow hG1 (by norm_num)
  have h6 : (k₀ : ℝ) ^ ((1 : ℝ) / 15) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) ≤
      (k₀ : ℝ) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  nlinarith

/-- `2^{Zq A K G L} ≤ 2^{2A} · 2^{A G/√log₂(G+2)} · (L+2)^{A(K²+1)}`. -/
theorem Zq_split (A K G L : ℕ) :
    (2 : ℝ) ^ Zq A K G L ≤ (2 : ℝ) ^ (2 * (A : ℝ)) * (2 : ℝ) ^ ((A : ℝ) * G / T2.sq G) *
      ((L : ℝ) + 2) ^ ((A : ℝ) * ((K : ℝ) ^ 2 + 1)) := by
  have hs := T2.one_le_sq G
  have hs0 := T2.sq_pos G
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have e1 : Zq A K G L = (A : ℝ) * G / T2.sq G + 2 * A / T2.sq G + (A : ℝ) * ((K : ℝ) ^ 2 + 1) * T2.Lam L := by
    unfold Zq; ring
  have e2 : (2 : ℝ) ^ ((A : ℝ) * ((K : ℝ) ^ 2 + 1) * T2.Lam L) = ((L : ℝ) + 2) ^ ((A : ℝ) * ((K : ℝ) ^ 2 + 1)) := by
    rw [mul_comm _ (T2.Lam L), Real.rpow_mul (by norm_num), T2.Lam,
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  have h3 : (2 : ℝ) ^ (2 * (A : ℝ) / T2.sq G) ≤ (2 : ℝ) ^ (2 * (A : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (div_le_self (by positivity) hs)
  rw [e1, Real.rpow_add two_pos, Real.rpow_add two_pos, e2]
  have : (0 : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * G / T2.sq G) := by positivity
  have : (0 : ℝ) ≤ ((L : ℝ) + 2) ^ ((A : ℝ) * ((K : ℝ) ^ 2 + 1)) := by positivity
  calc (2 : ℝ) ^ ((A : ℝ) * G / T2.sq G) * (2 : ℝ) ^ (2 * (A : ℝ) / T2.sq G) *
        ((L : ℝ) + 2) ^ ((A : ℝ) * ((K : ℝ) ^ 2 + 1))
      ≤ (2 : ℝ) ^ ((A : ℝ) * G / T2.sq G) * (2 : ℝ) ^ (2 * (A : ℝ)) *
        ((L : ℝ) + 2) ^ ((A : ℝ) * ((K : ℝ) ^ 2 + 1)) := by gcongr
    _ = _ := by ring

open T2 Asm in
/-- **Theorem Q1 (exact amplitudes, rate form), Turing-machine level.** There are ONE Turing
machine of Mathlib with finite alphabets and ONE constant `C` such that, for EVERY Clifford+T
circuit `Cir` (gates `H, T, T†, S, S†, X, Z, CNOT, CZ, CS, SWAP, CH`, arbitrary connectivity) on `n`
qubits and all basis states `x, y`, the machine, started on the word `circCode Cir x y` (length
`L`), halts within `⌊C · 2^{C·G/√log₂(G+2)} · (L+2)^{C·(G+2)^{1/15}}⌋` steps (`G = twoCount Cir`) with
the word `outWord a k` of integers `a₀, …, a₃` and `k = hcount Cir` such that
`⟨y|Cir|x⟩ = (a₀ + a₁ω + a₂ω² + a₃ω³)/√2^k`.

The route: the clique machine of Theorem A(b) on the pieces of Theorem B
(`CountedRoute.onTheCountedRecursion`), Lemma 8 case (i) (`ExplicitCost.groupingExplicit`) on the
circuit network with `g = 3K⁸` nodes, `K = K_ℓ` for the largest level with
`K_ℓ ≤ max(⌊G^{1/30}⌋, K₀)`. The factor `(L+2)^{C(G+2)^{1/15}}` is `(K(L'+B'))^{C₀K²}` of Theorem A(b)
with `K² = O(G^{1/15})`: the precision of the stream values grows with the number of gates. -/
theorem amplitude_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (Cir : List (Gate n)) (x y : Basis n), ∃ a : Fin 4 → ℤ,
        amplitude Cir x y = (∑ j : Fin 4, (a j : ℂ) * ω ^ (j : ℕ)) / ((Real.sqrt 2 : ℝ) : ℂ) ^ hcount Cir ∧
        GraphProblems.Outputs M (circCode Cir x y) (outWord a (hcount Cir))
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * (twoCount Cir : ℝ) /
              Real.sqrt (Real.logb 2 ((twoCount Cir : ℝ) + 2))) *
            (((circCode Cir x y).length : ℝ) + 2) ^ ((C : ℝ) * ((twoCount Cir : ℝ) + 2) ^ ((1 : ℝ) / 15))⌋₊ := by
  obtain ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := geBody
  have hL := hyp.levels
  have hk := hyp.computesK
  obtain ⟨A, hA⟩ := qR_bound hC₁ hL hk _ hyp.solves (x₀ := x₀) fun l => he l
  obtain ⟨inst⟩ := QP.qR_poly _ hL hk hyp.steps
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.exists_tmW (qR (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)
    (CliqueLevels.levelsUnder x₀) (Levels.Gen.K x₀ 0))
  obtain ⟨k₀, hk₀⟩ : ∃ x, x = Levels.Gen.K x₀ 0 ^ 30 := ⟨_, rfl⟩
  have hk₀1 : 1 ≤ k₀ := by rw [hk₀]; exact Nat.one_le_pow _ _ (by have := hL.K_two 0; omega)
  obtain ⟨Af, hAf⟩ : ∃ x, x = q + (A + 1) + q * (2 + A + 1 + 1) := ⟨_, rfl⟩
  refine ⟨M, 2 ^ (2 * Af) + Af * (k₀ + 1), hfin, fun n Cir x y => ?_⟩
  obtain ⟨Z, K, T, S, hZ0, hZv, hK2, hup, hrun, hT, hS⟩ := hA Cir x y
  rw [← hk₀] at hup
  refine ⟨fun j => decodeK (bC Cir) (Z.toNat % MC Cir) j.val, ?_, ?_⟩
  · -- the amplitude
    have h := amplitude_of_residue Cir x y Z hZv
    have e : (Z % (Mb (bK n Cir.length) : ℤ)).toNat = Z.toNat % MC Cir := by
      obtain ⟨z, hz⟩ := Int.eq_ofNat_of_zero_le hZ0
      rw [hz, ← Int.natCast_mod, Int.toNat_natCast, Int.toNat_natCast]
    rw [h, e]
  · -- the time
    obtain ⟨ev⟩ := hM (circCode Cir x y) T S _ hrun
    refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.le_floor ?_)⟩⟩
    set L := (circCode Cir x y).length
    set G := twoCount Cir
    have hLx : (L : ℝ) ≤ (2 : ℝ) ^ Zq (2 * 1) K G L := pol_le_Zq K G (Pol.id : Pol 1 L L)
    have h1 : (T : ℝ) + 1 ≤ (2 : ℝ) ^ Zq (A + 1) K G L := add_one_le_Zq hT
    have h2 : (L : ℝ) + S + 1 ≤ (2 : ℝ) ^ Zq (2 * 1 + A + 1 + 1) K G L := add_one_le_Zq (add_le_Zq hLx hS)
    have h3 := pow_le_Zq (by positivity) h2 q
    have h4 : (q : ℝ) * ((T : ℝ) + 1) ≤ (2 : ℝ) ^ Zq (q + (A + 1)) K G L :=
      mul_le_Zq (Nat.cast_nonneg _) (const_le_Zq q K G L) h1
    have h5 := mul_le_Zq (by positivity) h4 h3
    have hAf' : q + (A + 1) + q * (2 * 1 + A + 1 + 1) = Af := by rw [hAf]
    rw [hAf'] at h5
    have e1 : ((q * (T + 1) * (L + S + 1) ^ q : ℕ) : ℝ) =
        (q : ℝ) * ((T : ℝ) + 1) * ((L : ℝ) + S + 1) ^ q := by push_cast; ring
    rw [e1]
    refine h5.trans ((Zq_split Af K G L).trans ?_)
    -- the constants
    set Cf : ℕ := 2 ^ (2 * Af) + Af * (k₀ + 1)
    have hC1 : (2 : ℝ) ^ (2 * (Af : ℝ)) ≤ Cf := by
      have : (2 : ℝ) ^ (2 * (Af : ℝ)) = ((2 ^ (2 * Af) : ℕ) : ℝ) := by
        rw [show (2 : ℝ) * (Af : ℝ) = ((2 * Af : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]; push_cast; ring
      rw [this]; exact_mod_cast Nat.le_add_right _ _
    have hC2 : (Af : ℝ) ≤ Cf := by
      have : Af ≤ Cf := le_trans (Nat.le_mul_of_pos_right _ (by omega)) (Nat.le_add_left _ _)
      exact_mod_cast this
    have hC3 : (Af : ℝ) * ((K : ℝ) ^ 2 + 1) ≤ (Cf : ℝ) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) := by
      have hK := K2_le_root hk₀1 hup
      have e3 : (Cf : ℝ) = 2 ^ (2 * Af) + Af * ((k₀ : ℝ) + 1) := by simp only [Cf]; push_cast; ring
      have h0 : (0 : ℝ) ≤ ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) := by positivity
      have hA0 : (0 : ℝ) ≤ Af := Nat.cast_nonneg _
      calc (Af : ℝ) * ((K : ℝ) ^ 2 + 1) ≤ Af * (((k₀ : ℝ) + 1) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15)) :=
            mul_le_mul_of_nonneg_left hK hA0
        _ ≤ (2 ^ (2 * Af) + Af * ((k₀ : ℝ) + 1)) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) := by
            have : (0 : ℝ) ≤ 2 ^ (2 * Af) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15) := by positivity
            nlinarith
        _ = _ := by rw [e3]
    have hL1 : (1 : ℝ) ≤ (L : ℝ) + 2 := by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith
    have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
    have hs0 := T2.sq_pos G
    have hexpG : (2 : ℝ) ^ ((Af : ℝ) * G / T2.sq G) ≤ (2 : ℝ) ^ ((Cf : ℝ) * G / Real.sqrt (Real.logb 2 ((G : ℝ) + 2))) := by
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [show Real.sqrt (Real.logb 2 ((G : ℝ) + 2)) = T2.sq G from rfl]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hG0) hs0.le
    have hexpL : ((L : ℝ) + 2) ^ ((Af : ℝ) * ((K : ℝ) ^ 2 + 1)) ≤
        ((L : ℝ) + 2) ^ ((Cf : ℝ) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 hC3
    calc (2 : ℝ) ^ (2 * (Af : ℝ)) * (2 : ℝ) ^ ((Af : ℝ) * G / T2.sq G) * ((L : ℝ) + 2) ^ ((Af : ℝ) * ((K : ℝ) ^ 2 + 1))
        ≤ (Cf : ℝ) * (2 : ℝ) ^ ((Cf : ℝ) * G / Real.sqrt (Real.logb 2 ((G : ℝ) + 2))) *
            ((L : ℝ) + 2) ^ ((Cf : ℝ) * ((G : ℝ) + 2) ^ ((1 : ℝ) / 15)) := by gcongr
      _ = _ := by push_cast; ring

/-! ## The rate form under Q1's condition on the input length -/

/-- `√(log₂(G+2)) ≤ 6 (G+2)^{1/30}`. -/
theorem sq_le_root (G : ℕ) : T2.sq G ≤ 6 * ((G : ℝ) + 2) ^ ((1 : ℝ) / 30) := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (G : ℝ) + 2 := ⟨_, rfl⟩
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; have : (0 : ℝ) ≤ G := Nat.cast_nonneg G; linarith
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [one_div, Real.log_inv] at h
    linarith
  have hlog : Real.log x ≤ x ^ ((1 : ℝ) / 15) / (1 / 15) := Real.log_le_rpow_div (by linarith) (by norm_num)
  have hy0 : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 15) := by positivity
  have hlb : Real.logb 2 x ≤ 36 * x ^ ((1 : ℝ) / 15) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have e : x ^ ((1 : ℝ) / 15) / (1 / 15) = 15 * x ^ ((1 : ℝ) / 15) := by ring
    rw [e] at hlog
    nlinarith
  have hsq : (6 * x ^ ((1 : ℝ) / 30)) ^ 2 = 36 * x ^ ((1 : ℝ) / 15) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 30)), ← Real.rpow_mul (by linarith)]
    norm_num
  unfold T2.sq T2.Lam
  rw [← hx]
  calc Real.sqrt (Real.logb 2 x) ≤ Real.sqrt ((6 * x ^ ((1 : ℝ) / 30)) ^ 2) := by
        apply Real.sqrt_le_sqrt; rw [hsq]; exact hlb
    _ = 6 * x ^ ((1 : ℝ) / 30) := Real.sqrt_sq (by positivity)

/-- **Theorem Q1 (rate form) under Q1's condition on the input length.** The machine and constant
of `amplitude_TM_rate`, with `7C`: when `log₂(L+2) ≤ (G+2)^{9/10}` (`L` the length of the word; Q1
assumes `log(G₁+2) ≤ G^{0.9}`), the machine halts within `⌊C · 2^{C·(G+2)/√log₂(G+2)}⌋` steps. -/
theorem amplitude_TM_rate' :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (Cir : List (Gate n)) (x y : Basis n), ∃ a : Fin 4 → ℤ,
        amplitude Cir x y = (∑ j : Fin 4, (a j : ℂ) * ω ^ (j : ℕ)) / ((Real.sqrt 2 : ℝ) : ℂ) ^ hcount Cir ∧
        (Real.logb 2 (((circCode Cir x y).length : ℝ) + 2) ≤ ((twoCount Cir : ℝ) + 2) ^ ((9 : ℝ) / 10) →
          GraphProblems.Outputs M (circCode Cir x y) (outWord a (hcount Cir))
            ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((twoCount Cir : ℝ) + 2) /
              Real.sqrt (Real.logb 2 ((twoCount Cir : ℝ) + 2)))⌋₊) := by
  obtain ⟨M, C, hfin, hM⟩ := amplitude_TM_rate
  refine ⟨M, 7 * C, hfin, fun n Cir x y => ?_⟩
  obtain ⟨a, ha, hout⟩ := hM n Cir x y
  refine ⟨a, ha, fun hcond => ?_⟩
  obtain ⟨ev⟩ := hout
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.floor_mono ?_)⟩⟩
  set L := (circCode Cir x y).length
  set G := twoCount Cir
  rw [show Real.sqrt (Real.logb 2 ((G : ℝ) + 2)) = T2.sq G from rfl]
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (G : ℝ) + 2 := ⟨_, rfl⟩
  rw [← hX] at hcond ⊢
  have hX1 : (1 : ℝ) ≤ X := by rw [hX]; have : (0 : ℝ) ≤ G := Nat.cast_nonneg G; linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hs0 := T2.sq_pos G
  have hs := sq_le_root G
  rw [← hX] at hs
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  -- `(L+2)^{C X^{1/15}} = 2^{C X^{1/15} log₂(L+2)}`
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = Real.logb 2 ((L : ℝ) + 2) := ⟨_, rfl⟩
  rw [← hlam] at hcond
  have hL2 : ((L : ℝ) + 2) = (2 : ℝ) ^ lam := by
    rw [hlam, Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  rw [hL2, ← Real.rpow_mul (by norm_num)]
  -- `X^{1/15} log₂(L+2) ≤ X^{29/30} ≤ 6X/s`
  have h1 : X ^ ((1 : ℝ) / 15) * lam ≤ X ^ ((29 : ℝ) / 30) := by
    calc X ^ ((1 : ℝ) / 15) * lam ≤ X ^ ((1 : ℝ) / 15) * X ^ ((9 : ℝ) / 10) :=
          mul_le_mul_of_nonneg_left hcond (by positivity)
      _ = X ^ ((29 : ℝ) / 30) := by rw [← Real.rpow_add hX0]; norm_num
  have h2 : X ^ ((29 : ℝ) / 30) * T2.sq G ≤ 6 * X := by
    calc X ^ ((29 : ℝ) / 30) * T2.sq G ≤ X ^ ((29 : ℝ) / 30) * (6 * X ^ ((1 : ℝ) / 30)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 6 * (X ^ ((29 : ℝ) / 30) * X ^ ((1 : ℝ) / 30)) := by ring
      _ = 6 * X := by rw [← Real.rpow_add hX0]; norm_num
  have h3 : X ^ ((29 : ℝ) / 30) ≤ 6 * X / T2.sq G := by rw [le_div_iff₀ hs0]; exact h2
  have hGX : (G : ℝ) ≤ X := by rw [hX]; linarith
  have hexp : (C : ℝ) * G / T2.sq G + lam * ((C : ℝ) * X ^ ((1 : ℝ) / 15)) ≤ ((7 * C : ℕ) : ℝ) * X / T2.sq G := by
    have e1 : lam * ((C : ℝ) * X ^ ((1 : ℝ) / 15)) = (C : ℝ) * (X ^ ((1 : ℝ) / 15) * lam) := by ring
    have e2 : ((7 * C : ℕ) : ℝ) * X / T2.sq G = (C : ℝ) * X / T2.sq G + (C : ℝ) * (6 * X / T2.sq G) := by
      push_cast; ring
    have e3 : (C : ℝ) * G / T2.sq G ≤ (C : ℝ) * X / T2.sq G :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGX hC0) hs0.le
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left (h1.trans h3) hC0
    linarith
  have hC7 : (C : ℝ) ≤ ((7 * C : ℕ) : ℝ) := by exact_mod_cast (by omega : C ≤ 7 * C)
  calc (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * G / T2.sq G) * (2 : ℝ) ^ (lam * ((C : ℝ) * X ^ ((1 : ℝ) / 15)))
      = (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * G / T2.sq G + lam * ((C : ℝ) * X ^ ((1 : ℝ) / 15))) := by
        rw [Real.rpow_add two_pos]; ring
    _ ≤ ((7 * C : ℕ) : ℝ) * (2 : ℝ) ^ (((7 * C : ℕ) : ℝ) * X / T2.sq G) := by
        gcongr
        · exact one_le_two

end EthFollowup.Quantum
