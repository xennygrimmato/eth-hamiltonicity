/-
# Parity of Hamiltonian cycles for every graph (unbounded degree)

`HamiltonianParity.lean` encodes "exactly two incident edges are selected" at a vertex `v` as a
single constraint of width `deg v`. Here it is replaced by a sequential counter. With the
incident edges of `v` listed as `e₀, …, e_{d−1}`, two state bits per prefix record the number of
selected edges among `e₀, …, e_{i−1}` (0, 1 or 2). Each counter step is a constraint on five
variables. The state bits are determined by the edge bits, so the model count is unchanged
(`count_bigCNF`).

Result: one machine (the comparator at width 5) computes, for **every** graph `G`, a number
congruent mod 2 to the number of Hamiltonian cycles, in time `C (L+1)^d 2^{A ρ(5|E| + 3n)}` and
polynomial space (`hamParity_allGraphs`).
-/
import EthFollowup.HamiltonianParity

namespace EthFollowup.Hamiltonian

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open EthFollowup

theorem countP_toList {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Bool) :
    s.toList.countP p = (s.filter (fun x => p x = true)).card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((Finset.nodup_toList s).filter _)]
  congr 1
  ext x
  simp

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

noncomputable section

/-! ### Incident edge lists -/

/-- The incident edges of `v`, in some fixed order. -/
noncomputable def incList (v : Fin n) : List (EdgeVar G) :=
  (Finset.univ.filter fun e : EdgeVar G => v ∈ (e : Sym2 (Fin n))).toList

theorem incident_card (v : Fin n) :
    (Finset.univ.filter fun e : EdgeVar G => v ∈ (e : Sym2 (Fin n))).card = G.degree v := by
  have := incidentScope_card G v
  rwa [incidentScope, Finset.card_map] at this

theorem incList_length (v : Fin n) : (incList G v).length = G.degree v := by
  rw [incList, Finset.length_toList, incident_card]

/-- The `i`-th incident edge of `v`. -/
noncomputable def incAt (v : Fin n) (i : Fin (G.degree v)) : EdgeVar G :=
  (incList G v)[i.val]'(by rw [incList_length]; exact i.2)

/-! ### Variables -/

/-- Counter bits: vertex, prefix length `0..deg v`, and which of the two bits. -/
abbrev Aux := (v : Fin n) × Fin (G.degree v + 1) × Bool

/-- All variables of the unbounded-degree encoding. -/
abbrev BVar := Var G ⊕ Aux G

/-- Instance search on the dependent `Σ`-type exceeds the default size limit without this. -/
instance : DecidableEq (SAT.Literal (BVar G)) := inferInstance

theorem card_bvar : Fintype.card (BVar G) = 5 * G.edgeFinset.card + 3 * n := by
  rw [Fintype.card_sum, card_var, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  have hsum : ∑ v : Fin n, (G.degree v + 1) * 2 = 2 * (∑ v, G.degree v) + 2 * n := by
    rw [Finset.sum_congr rfl fun v _ => show (G.degree v + 1) * 2 = 2 * G.degree v + 2 by ring,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_comm]
  rw [hsum, SimpleGraph.sum_degrees_eq_twice_card_edges]
  ring

def bit (v : Fin n) (i : Fin (G.degree v + 1)) (b : Bool) : BVar G := Sum.inr ⟨v, (i, b)⟩

def xVar (e : EdgeVar G) : BVar G := Sum.inl (Sum.inl e)

/-- Value of the two counter bits at prefix `i`, read from a set `T` of true variables. -/
def valT (T : Finset (BVar G)) (v : Fin n) (i : Fin (G.degree v + 1)) : ℕ :=
  (decide (bit G v i false ∈ T)).toNat + 2 * (decide (bit G v i true ∈ T)).toNat

/-! ### Constraints -/

def startCNF (v : Fin n) : SAT.CNF (BVar G) :=
  constraintCNF {bit G v 0 false, bit G v 0 true} fun T => valT G T v 0 = 0

def endCNF (v : Fin n) : SAT.CNF (BVar G) :=
  constraintCNF {bit G v (Fin.last _) false, bit G v (Fin.last _) true} fun T =>
    valT G T v (Fin.last _) = 2

def stepScope (v : Fin n) (i : Fin (G.degree v)) : Finset (BVar G) :=
  {bit G v i.castSucc false, bit G v i.castSucc true, xVar G (incAt G v i),
    bit G v i.succ false, bit G v i.succ true}

def stepCNF (v : Fin n) (i : Fin (G.degree v)) : SAT.CNF (BVar G) :=
  constraintCNF (stepScope G v i) fun T =>
    valT G T v i.succ = valT G T v i.castSucc + (decide (xVar G (incAt G v i) ∈ T)).toNat ∧
      valT G T v i.succ ≤ 2

def chainCNF (v : Fin n) : SAT.CNF (BVar G) :=
  startCNF G v ∪ endCNF G v ∪ Finset.univ.biUnion (stepCNF G v)

/-- Root and edge constraints of `cutCNF`, without the vertex constraints. -/
def restCNF (r : Fin n) : SAT.CNF (Var G) :=
  rootCNF G r ∪ (adjPairs G).attach.biUnion (edgeCNF G)

/-- The unbounded-degree Cut&Count formula. -/
def bigCNF (r : Fin n) : SAT.CNF (BVar G) :=
  CNF.map Sum.inl (restCNF G r) ∪ Finset.univ.biUnion (chainCNF G)

/-! ### Semantics of the counter -/

/-- Prefix counts of selected incident edges. -/
noncomputable def pc (x : SAT.Assignment (Var G)) (v : Fin n) (i : ℕ) : ℕ :=
  ((incList G v).take i).countP fun e => x (Sum.inl e)

/-- Value of the counter bits of an assignment. -/
def val (a : SAT.Assignment (BVar G)) (v : Fin n) (i : Fin (G.degree v + 1)) : ℕ :=
  (a (bit G v i false)).toNat + 2 * (a (bit G v i true)).toNat

theorem decide_mem_filter {α : Type*} [DecidableEq α] {S : Finset α} {x : α} (hx : x ∈ S)
    (a : α → Bool) : decide (x ∈ S.filter fun y => a y = true) = a x := by
  by_cases h : a x = true <;> simp [Finset.mem_filter, hx, h]

theorem pc_zero (x : SAT.Assignment (Var G)) (v : Fin n) : pc G x v 0 = 0 := by
  simp [pc]

theorem pc_succ (x : SAT.Assignment (Var G)) (v : Fin n) (i : Fin (G.degree v)) :
    pc G x v (i.val + 1) = pc G x v i.val + (x (Sum.inl (incAt G v i))).toNat := by
  have hi : i.val < (incList G v).length := by rw [incList_length]; exact i.2
  rw [pc, pc, List.take_add_one, List.getElem?_eq_getElem hi, List.countP_append]
  simp [incAt, List.countP_cons, Bool.toNat]

theorem pc_mono (x : SAT.Assignment (Var G)) (v : Fin n) {i j : ℕ} (hij : i ≤ j) :
    pc G x v i ≤ pc G x v j := by
  unfold pc
  apply List.Sublist.countP_le
  exact (List.take_sublist_take_left hij)

theorem pc_last (x : SAT.Assignment (Var G)) (v : Fin n) :
    pc G x v (G.degree v) = ((edgesOf G x).filter fun e => v ∈ e).card := by
  rw [pc, ← incList_length, List.take_length, incList, countP_toList]
  refine Finset.card_bij' (fun e _ => (e : Sym2 (Fin n)))
    (fun e he => ⟨e, edgesOf_subset G x (Finset.mem_filter.1 he).1⟩) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [Finset.mem_filter, mem_edgesOf]
    exact ⟨⟨e.2, he.2⟩, he.1⟩
  · intro e he
    simp only [Finset.mem_filter, mem_edgesOf] at he
    obtain ⟨⟨h, ha⟩, hv⟩ := he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv, ha⟩
  · intro e _; rfl
  · intro e _; rfl

theorem stepCNF_eval (a : SAT.Assignment (BVar G)) (v : Fin n) (i : Fin (G.degree v)) :
    SAT.CNF.eval a (stepCNF G v i) = true ↔
      val G a v i.succ = val G a v i.castSucc + (a (xVar G (incAt G v i))).toNat ∧
        val G a v i.succ ≤ 2 := by
  rw [stepCNF, constraintCNF_eval]
  simp only [valT, val]
  rw [decide_mem_filter (by simp [stepScope]), decide_mem_filter (by simp [stepScope]),
    decide_mem_filter (by simp [stepScope]), decide_mem_filter (by simp [stepScope]),
    decide_mem_filter (by simp [stepScope])]

theorem startCNF_eval (a : SAT.Assignment (BVar G)) (v : Fin n) :
    SAT.CNF.eval a (startCNF G v) = true ↔ val G a v 0 = 0 := by
  rw [startCNF, constraintCNF_eval]
  simp only [valT, val]
  rw [decide_mem_filter (by simp), decide_mem_filter (by simp)]

theorem endCNF_eval (a : SAT.Assignment (BVar G)) (v : Fin n) :
    SAT.CNF.eval a (endCNF G v) = true ↔ val G a v (Fin.last _) = 2 := by
  rw [endCNF, constraintCNF_eval]
  simp only [valT, val]
  rw [decide_mem_filter (by simp), decide_mem_filter (by simp)]

/-- The chain constraints hold iff the counter bits hold the prefix counts and the final count
is two. -/
theorem chain_iff (a : SAT.Assignment (BVar G)) (v : Fin n) :
    SAT.CNF.eval a (chainCNF G v) = true ↔
      (∀ i : Fin (G.degree v + 1), val G a v i = pc G (a ∘ Sum.inl) v i) ∧
        pc G (a ∘ Sum.inl) v (G.degree v) = 2 := by
  rw [chainCNF, CNF.eval_union, CNF.eval_union, CNF.eval_biUnion, startCNF_eval, endCNF_eval]
  simp only [Finset.mem_univ, true_implies, stepCNF_eval]
  have hx : ∀ i : Fin (G.degree v),
      (a (xVar G (incAt G v i))).toNat = ((a ∘ Sum.inl) (Sum.inl (incAt G v i))).toNat := by
    intro i; rfl
  constructor
  · rintro ⟨⟨h0, hlast⟩, hstep⟩
    have hall : ∀ k (hk : k < G.degree v + 1), val G a v ⟨k, hk⟩ = pc G (a ∘ Sum.inl) v k := by
      intro k
      induction k with
      | zero => intro _; rw [pc_zero]; exact h0
      | succ k ih =>
        intro hk
        have hk' : k < G.degree v := by omega
        have := (hstep ⟨k, hk'⟩).1
        simp only [Fin.succ_mk, Fin.castSucc_mk] at this
        rw [this, ih (by omega), pc_succ G _ v ⟨k, hk'⟩, hx]
    refine ⟨fun i => hall i.val i.2, ?_⟩
    have := hall (G.degree v) (by omega)
    rw [← this]
    exact hlast
  · rintro ⟨hall, hlast⟩
    refine ⟨⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
    · rw [hall 0]; exact pc_zero G _ v
    · rw [hall (Fin.last _)]; exact hlast
    · rw [hall, hall]
      simp only [Fin.val_succ, Fin.val_castSucc]
      rw [pc_succ, hx]
    · rw [hall]
      simp only [Fin.val_succ]
      rw [← hlast]
      exact pc_mono G _ v (by omega)

/-- The canonical counter bits for an edge/cut assignment. -/
noncomputable def ext (x : SAT.Assignment (Var G)) : Aux G → Bool
  | ⟨v, (i, b)⟩ => if b then decide (pc G x v i = 2) else decide (pc G x v i = 1)

theorem chain_iff_ext (a : SAT.Assignment (BVar G)) (v : Fin n) :
    SAT.CNF.eval a (chainCNF G v) = true ↔
      (∀ i : Fin (G.degree v + 1), ∀ b : Bool,
        a (Sum.inr ⟨v, (i, b)⟩) = ext G (a ∘ Sum.inl) ⟨v, (i, b)⟩) ∧
        pc G (a ∘ Sum.inl) v (G.degree v) = 2 := by
  rw [chain_iff]
  constructor
  · rintro ⟨hall, hlast⟩
    refine ⟨fun i b => ?_, hlast⟩
    have hle : pc G (a ∘ Sum.inl) v i ≤ 2 := hlast ▸ pc_mono G _ v (by omega)
    have h := hall i
    simp only [val, bit] at h
    cases hb0 : a (Sum.inr ⟨v, (i, false)⟩) <;> cases hb1 : a (Sum.inr ⟨v, (i, true)⟩) <;>
      cases b <;> simp_all [ext] <;> omega
  · rintro ⟨hall, hlast⟩
    refine ⟨fun i => ?_, hlast⟩
    have hle : pc G (a ∘ Sum.inl) v i ≤ 2 := hlast ▸ pc_mono G _ v (by omega)
    simp only [val, bit, hall i false, hall i true, ext]
    rcases (by omega : pc G (a ∘ Sum.inl) v i = 0 ∨ pc G (a ∘ Sum.inl) v i = 1 ∨
      pc G (a ∘ Sum.inl) v i = 2) with h | h | h <;> simp [h]

theorem restCNF_eval (r : Fin n) (x : SAT.Assignment (Var G)) :
    SAT.CNF.eval x (restCNF G r) = true ↔
      Consistent (edgesOf G x) (cutOf G x) ∧ cutOf G x r = false := by
  rw [restCNF, CNF.eval_union, CNF.eval_biUnion, edges_consistent_iff, rootCNF_eval]
  tauto

theorem bigCNF_eval (r : Fin n) (a : SAT.Assignment (BVar G)) :
    SAT.CNF.eval a (bigCNF G r) = true ↔
      SAT.CNF.eval (a ∘ Sum.inl) (cutCNF G r) = true ∧
        (a ∘ Sum.inr) = ext G (a ∘ Sum.inl) := by
  rw [bigCNF, CNF.eval_union, CNF.map_eval, CNF.eval_biUnion, restCNF_eval, cutCNF_eval]
  simp only [Finset.mem_univ, true_implies, chain_iff_ext, TwoRegular]
  constructor
  · rintro ⟨⟨hc, hr⟩, hch⟩
    refine ⟨⟨fun v => ?_, hc, hr⟩, ?_⟩
    · rw [← pc_last]; exact (hch v).2
    · funext ⟨v, (i, b)⟩
      exact (hch v).1 i b
  · rintro ⟨⟨hreg, hc, hr⟩, hext⟩
    refine ⟨⟨hc, hr⟩, fun v => ⟨fun i b => ?_, ?_⟩⟩
    · exact congrFun hext ⟨v, (i, b)⟩
    · rw [pc_last]; exact hreg v

/-- The counter encoding has the same number of models as `cutCNF`. -/
theorem count_bigCNF (r : Fin n) : SAT.count (bigCNF G r) = SAT.count (cutCNF G r) := by
  unfold SAT.count SAT.satisfyingAssignments
  refine Finset.card_bij' (fun a _ => a ∘ Sum.inl) (fun x _ => Sum.elim x (ext G x)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ((bigCNF_eval G r a).1 ha).1
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [bigCNF_eval]
    exact ⟨by simpa using hx, by funext y; simp⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have h := ((bigCNF_eval G r a).1 ha).2
    funext y
    rcases y with y | y
    · rfl
    · simp only [Sum.elim_inr]
      exact (congrFun h y).symm
  · intro x _
    funext y
    rfl

theorem count_bigCNF_mod_two (r : Fin n) :
    (SAT.count (bigCNF G r) : ZMod 2) = ((hamCycles G).card : ZMod 2) := by
  rw [count_bigCNF, count_cutCNF_mod_two]

theorem card_le_five {α : Type*} [DecidableEq α] (a b c d e : α) :
    ({a, b, c, d, e} : Finset α).card ≤ 5 := by
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  simp

theorem bigCNF_width (r : Fin n) : SAT.WidthAtMost 5 (bigCNF G r) := by
  refine width_union (CNF.map_width _ (width_union ?_ ?_)) ?_
  · exact constraintCNF_width _ _ (by simp)
  · refine width_biUnion fun p _ => constraintCNF_width _ _ ?_
    exact Finset.card_le_three.trans (by norm_num)
  · refine width_biUnion fun v _ => width_union (width_union ?_ ?_) ?_
    · exact constraintCNF_width _ _ (Finset.card_le_two.trans (by norm_num))
    · exact constraintCNF_width _ _ (Finset.card_le_two.trans (by norm_num))
    · exact width_biUnion fun i _ => constraintCNF_width _ _ (by
        unfold stepScope; exact card_le_five _ _ _ _ _)

/-- The unbounded-degree encoding on `Fin (5|E| + 3n)`. -/
noncomputable def bigCNFFin (r : Fin n) : SAT.CNF (Fin (Fintype.card (BVar G))) :=
  CNF.relabel (Fintype.equivFin (BVar G)) (bigCNF G r)

/-- **Parity of Hamiltonian cycles for every graph.** Conditional on the comparator statement at
width 5, one machine computes, for every graph `G` on `n` vertices, a number congruent mod 2 to
the number of Hamiltonian cycles of `G`, in time `C (L+1)^d 2^{A ρ(5|E| + 3n)}` and polynomial
visited space. -/
theorem hamParity_allGraphs (h : ExactCountAndSatStatement 5 (by norm_num)) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n),
        ∃ (N time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (bigCNFFin G r))) final ∧
          final.config.tapes countTape = Turing.Tape.mk₁ ((countWord N).map some) ∧
          BinaryArithmetic.toNat (countWord N) = N ∧
          (N : ZMod 2) = ((hamCycles G).card : ZMod 2) ∧
          Fintype.card (BVar G) = 5 * G.edgeFinset.card + 3 * n ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength (bigCNFFin G r)) (Fintype.card (BVar G)) ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF (bigCNFFin G r))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (bigCNFFin G r) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, _answerTape, C, A, S, d, e, hC, hA, hS, hd, he, hrun⟩ := h
  refine ⟨machine, countTape, C, A, S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n G _ r
  have hw : SAT.WidthAtMost 5 (bigCNFFin G r) := CNF.relabel_width _ (bigCNF_width G r)
  obtain ⟨time, final, htrace, hcount, -, -, hdecode, -, htime, hspace⟩ :=
    hrun (Fintype.card (BVar G)) (bigCNFFin G r) hw
  refine ⟨SAT.count (bigCNFFin G r), time, final, htrace, hcount, hdecode, ?_,
    card_bvar G, htime, hspace⟩
  rw [bigCNFFin, CNF.relabel_count, count_bigCNF_mod_two]

end

end EthFollowup.Hamiltonian
