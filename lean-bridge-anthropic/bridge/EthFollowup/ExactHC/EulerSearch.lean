/-
# Deciding and finding Eulerian circuits at Turing-machine level

From the edge splitting of `EulerSplit.lean` and its preprocessing `Eul.eulW` (`EulerTheorems.lean`),
with the decision and search machines `Srch.decS`, `Srch.searchS` of `SearchMachine.lean` on top of
the stepped machine of Theorem 1 (`Dir.hc_stepped`).

## Main results
* `eulerDecision_TM`: for every `δ > 0` and `Δ`, one Turing machine of Mathlib writes the bit
  «`G` has an Eulerian circuit» (`(ESplit.eulerCircuitsAll G).Nonempty`) within
  `⌊C·(n+2)^C·2^{δm}⌋` steps on every graph of maximum degree `≤ Δ`;
* `eulerSearch_TM`: within the same bound, a word `w`: `w = []` if `G` has no Eulerian circuit, and
  otherwise `w` is the adjacency matrix of the transition graph `phiE G T` (a Hamiltonian cycle of
  the split graph `eulerSplitAll G`) of an Eulerian circuit `T ∈ eulerCircuitsAll G` (Kotzig's
  description: a transition system with connected transition graph).

The machine `Stepped.mapIn eulW (Srch.searchS Mh)` runs the search on the split graph: it makes
`(3m)² + 1` calls of the counting machine on subgraphs of `eulerSplitAll G`; the factor is absorbed
into `(n+2)^C`. As in `theoremEuler`, the factor `(n+2)^C` pays for reading the `n²`-bit input.

Standard axioms only.
-/
import EthFollowup.ExactHC.EulerTheorems
import EthFollowup.ExactHC.Corollaries

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian

namespace EulS

/-- **From runs of a stepped machine to a Turing machine of Mathlib**, with a bound of the form
`C·N^C·E` (`N ≥ 1` a polynomial parameter, `E ≥ 1` the exponential part), when the input length
and the state sizes are `≤ B·N^B` and the steps `≤ B·N^B·E`. The machine does not depend on `B`. -/
theorem out_of_runs (Q : Stepped (List Bool) (List Bool)) [IsPolyT Q] :
    ∃ (TM : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (TM.tm.Γ i)) ∧
      ∀ (B : ℕ) (x : List Bool) (T S : ℕ) (w : List Bool) (N : ℕ) (E : ℝ), 1 ≤ N → 1 ≤ E →
        Q.Runs x T S w → x.length + S + 1 ≤ B * N ^ B → (T : ℝ) ≤ B * (N : ℝ) ^ B * E →
        GraphProblems.Outputs TM x w
          ⌊((q * (B + 1) * B ^ q + B + B * q : ℕ) : ℝ) * (N : ℝ) ^ (q * (B + 1) * B ^ q + B + B * q) * E⌋₊ := by
  obtain ⟨TM, q, hfin, hM⟩ := CountKSat.exists_tmW Q
  refine ⟨TM, q, hfin, fun B x T S w N E hN' hE hr hL' hT => ?_⟩
  obtain ⟨ev⟩ := hM x T S w hr
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.le_floor ?_)⟩⟩
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN'
  have hL : ((x.length + S + 1 : ℕ) : ℝ) ≤ (B : ℝ) * (N : ℝ) ^ B := by exact_mod_cast hL'
  have hNB : (1 : ℝ) ≤ (N : ℝ) ^ B := one_le_pow₀ hN
  have hNE : (1 : ℝ) ≤ (N : ℝ) ^ B * E := one_le_mul_of_one_le_of_one_le hNB hE
  have hT1 : (T : ℝ) + 1 ≤ ((B : ℝ) + 1) * ((N : ℝ) ^ B * E) := by nlinarith
  have hc : ((q * (B + 1) * B ^ q : ℕ) : ℝ) ≤ ((q * (B + 1) * B ^ q + B + B * q : ℕ) : ℝ) := by
    exact_mod_cast (by omega : q * (B + 1) * B ^ q ≤ q * (B + 1) * B ^ q + B + B * q)
  have hp : (N : ℝ) ^ (B + B * q) ≤ (N : ℝ) ^ (q * (B + 1) * B ^ q + B + B * q) :=
    pow_le_pow_right₀ hN (by omega)
  have hE0 : (0 : ℝ) ≤ E := by linarith
  calc ((q * (T + 1) * (x.length + S + 1) ^ q : ℕ) : ℝ)
      = (q : ℝ) * ((T : ℝ) + 1) * ((x.length + S + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (((B : ℝ) + 1) * ((N : ℝ) ^ B * E)) * ((B : ℝ) * (N : ℝ) ^ B) ^ q := by
        gcongr
    _ = ((q * (B + 1) * B ^ q : ℕ) : ℝ) * (N : ℝ) ^ (B + B * q) * E := by
        rw [mul_pow, ← pow_mul, pow_add]; push_cast; ring
    _ ≤ ((q * (B + 1) * B ^ q + B + B * q : ℕ) : ℝ) * (N : ℝ) ^ (q * (B + 1) * B ^ q + B + B * q) * E := by
        gcongr

/-- The constant of the polynomial parts. -/
def bB (A : ℕ) : ℕ := A * 4 ^ A + (20 * A + 1000)

theorem le_bB (A : ℕ) : A + 3 ≤ bB A := by unfold bB; omega

/-- **The polynomial parts**: everything `≤ 1000·P^4 + 20·A·P^4 + A(3m+k)^A` is `≤ B·P^B`,
`B = bB A`, when `m ≤ P²` and `k ≤ P`. -/
theorem absorbP {P m k A X : ℕ} (hP : 1 ≤ P) (hm : m ≤ P ^ 2) (hk : k ≤ P)
    (hX : X ≤ 1000 * P ^ 4 + 20 * (A * P ^ 4) + A * (3 * m + k) ^ A) : X ≤ bB A * P ^ bB A := by
  have hPP : P ≤ P ^ 2 := by nlinarith
  have h1 : 3 * m + k ≤ 4 * P ^ 2 := by omega
  have h2 : (3 * m + k) ^ A ≤ 4 ^ A * P ^ (2 * A) := by
    calc (3 * m + k) ^ A ≤ (4 * P ^ 2) ^ A := Nat.pow_le_pow_left h1 _
      _ = 4 ^ A * P ^ (2 * A) := by rw [mul_pow, ← pow_mul]
  have h3 : P ^ (2 * A) ≤ P ^ bB A := Nat.pow_le_pow_right hP (by unfold bB; omega)
  have h4 : P ^ 4 ≤ P ^ bB A := Nat.pow_le_pow_right hP (by unfold bB; omega)
  have h5 : A * (3 * m + k) ^ A ≤ A * 4 ^ A * P ^ bB A := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h3))
  have h6 : bB A * P ^ bB A = A * 4 ^ A * P ^ bB A + 20 * (A * P ^ bB A) + 1000 * P ^ bB A := by
    unfold bB; ring
  have h7 : A * P ^ 4 ≤ A * P ^ bB A := Nat.mul_le_mul_left _ h4
  rw [h6]
  omega

/-- `absorbP` for `P = n + 2`, `k = 2`, `m ≤ n²`. -/
theorem absorb {n m A X : ℕ} (hm : m ≤ n * n)
    (hX : X ≤ 1000 * (n + 2) ^ 4 + 20 * (A * (n + 2) ^ 4) + A * (3 * m + 2) ^ A) :
    X ≤ bB A * (n + 2) ^ bB A :=
  absorbP (by omega) (by nlinarith) (by omega) hX

/-- The small polynomial facts used with `absorb`. -/
theorem small {n m : ℕ} (hm : m ≤ n * n) :
    n ≤ (n + 2) ^ 4 ∧ n * n ≤ (n + 2) ^ 4 ∧ m ≤ (n + 2) ^ 4 ∧ 3 * m * (3 * m) ≤ 9 * (n + 2) ^ 4 ∧
      1 ≤ (n + 2) ^ 4 := by
  have hP : n * n ≤ (n + 2) ^ 2 := by nlinarith
  have hP2 : (n + 2) ^ 2 ≤ (n + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : (n + 2) ^ 4 = (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  have hmm : m * m ≤ (n + 2) ^ 4 := by
    rw [h4]; exact Nat.mul_le_mul (hm.trans hP) (hm.trans hP)
  refine ⟨by nlinarith, hP.trans hP2, (hm.trans hP).trans hP2, by nlinarith, Nat.one_le_pow _ _ (by omega)⟩

theorem decide_eul {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    decide ((Nat.bits (ESplit.eulerCircuitsAll G).card).length ≠ 0) =
      decide (ESplit.eulerCircuitsAll G).Nonempty := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, Cor.bits_length_ne_zero_iff,
    ← Finset.card_pos]
  omega

theorem cast_n2 (n : ℕ) : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring

/-- The exponential part: `A·2^{(δ/2)m} ≤ (B·N^B)·2^{δm}` for `A ≤ B·N^B`. -/
theorem exp_part {δ : ℝ} (hδ : 0 < δ) {A B N m T : ℕ} (hAB : A ≤ B * N ^ B)
    (hT : (T : ℝ) ≤ A * (2 : ℝ) ^ (δ / 2 * (m : ℝ))) :
    (T : ℝ) ≤ B * (N : ℝ) ^ B * (2 : ℝ) ^ (δ * (m : ℝ)) := by
  have h4 : (2 : ℝ) ^ (δ / 2 * (m : ℝ)) ≤ (2 : ℝ) ^ (δ * (m : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hB : (A : ℝ) ≤ (B : ℝ) * (N : ℝ) ^ B := by exact_mod_cast hAB
  have hE0 : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * (m : ℝ)) := by positivity
  exact hT.trans (mul_le_mul hB h4 hE0 (by positivity))

end EulS

open Eul ESplit Dir EulS in
/-- **Deciding the existence of an Eulerian circuit in time `2^{δm}` on graphs of bounded degree,
Turing-machine level, unconditional.** For every `δ > 0` and `Δ` there are a Turing machine of
Mathlib with finite alphabets and a constant `C` such that on the code of any graph `G` with `n`
vertices, `m` edges and maximum degree `≤ Δ` it halts within `⌊C·(n+2)^C·2^{δm}⌋` steps with the one
bit «`G` has an Eulerian circuit» (`ESplit.eulerCircuitsAll`, Kotzig's description). -/
theorem eulerDecision_TM (δ : ℝ) (hδ : 0 < δ) (Δ : ℕ) :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        GraphProblems.Outputs Mc (GraphProblems.code G) [decide (eulerCircuitsAll G).Nonempty]
          ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ))⌋₊ := by
  obtain ⟨Mh, ⟨inst⟩, A₀, hA₀⟩ := hc_stepped (δ / 3) (by positivity) (Δ + 1)
  have i1 : IsPolyT (Stepped.mapIn eulW Mh) := IsPolyT.mapIn eulW_polyT
  obtain ⟨iD⟩ := Srch.decS_poly (Stepped.mapIn eulW Mh)
  obtain ⟨TM, q, hfin, hM⟩ := out_of_runs (Srch.decS (Stepped.mapIn eulW Mh))
  refine ⟨TM, q * (bB A₀ + 1) * bB A₀ ^ q + bB A₀ + bB A₀ * q, hfin, fun n G _ hΔ => ?_⟩
  obtain ⟨T, hr, hT⟩ := hA₀ (eulerSplitAll G) (by convert card_edge_eulerSplitAll_le G hΔ)
  have hsz := Cor.size_bits_hc (eulerSplitAll G)
  rw [← eulW_code, card_hamCycles_eulerSplitAll] at hr
  rw [card_hamCycles_eulerSplitAll] at hsz
  have hr' := Srch.decS_runs _ (Stepped.mapIn_runs hr)
  rw [decide_eul] at hr'
  rw [← length_edgeList G, ← cast_n2]
  have hm := M_le G
  obtain ⟨s1, s2, s3, s4, s5⟩ := small hm
  have hL : (GraphProblems.code G).length = n + 1 + n * n :=
    GraphProblems.length_code GraphProblems.stMatrixLength G
  have hS := Srch.size_code G
  rw [exp_three] at hT
  refine hM (bB A₀) _ _ _ _ (n + 2) ((2 : ℝ) ^ (δ * (M G : ℝ))) (by omega)
    (Real.one_le_rpow one_le_two (by positivity)) hr' ?_ ?_
  · apply absorb hm
    rw [hL, hS]
    omega
  · have hT2 : (T + 2 : ℕ) ≤ (A₀ + 2) * (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := by
      have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := Real.one_le_rpow one_le_two (by positivity)
      push_cast; linarith
    refine exp_part hδ (A := A₀ + 2) ?_ (by exact_mod_cast hT2)
    exact (by have := le_bB A₀; omega : A₀ + 2 ≤ bB A₀).trans
      (Nat.le_mul_of_pos_right _ (by positivity))

open Eul ESplit Dir EulS in
/-- **Finding an Eulerian circuit in time `2^{δm}` on graphs of bounded degree, Turing-machine
level, unconditional.** For every `δ > 0` and `Δ` there are a Turing machine of Mathlib with finite
alphabets and a constant `C` such that on the code of any graph `G` with `n` vertices, `m` edges and
maximum degree `≤ Δ` it halts within `⌊C·(n+2)^C·2^{δm}⌋` steps with a word `w`: `w = []` if `G` has
no Eulerian circuit, and otherwise `w` is the adjacency matrix (`GraphProblems.matrix`, row by row,
on the `3m` copies of the split graph) of the transition graph `phiE G T` of an Eulerian circuit
`T ∈ eulerCircuitsAll G` (Kotzig's description; `phiE G T` is a Hamiltonian cycle of
`eulerSplitAll G`, `ESplit.hamCycles_eulerSplit`). -/
theorem eulerSearch_TM (δ : ℝ) (hδ : 0 < δ) (Δ : ℕ) :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        ∃ w : List Bool, GraphProblems.Outputs Mc (GraphProblems.code G) w
            ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ))⌋₊ ∧
          (eulerCircuitsAll G = ∅ → w = []) ∧
          ((eulerCircuitsAll G).Nonempty →
            ∃ T ∈ eulerCircuitsAll G, w = GraphProblems.matrix (graphOf (phiE G T))) := by
  obtain ⟨Mh, ⟨inst⟩, A₀, hA₀⟩ := hc_stepped (δ / 3) (by positivity) (Δ + 1)
  obtain ⟨iS⟩ := Srch.searchS_poly Mh
  have i1 : IsPolyT (Stepped.mapIn eulW (Srch.searchS Mh)) := IsPolyT.mapIn eulW_polyT
  obtain ⟨TM, q, hfin, hM⟩ := out_of_runs (Stepped.mapIn eulW (Srch.searchS Mh))
  refine ⟨TM, q * (bB A₀ + 1) * bB A₀ ^ q + bB A₀ + bB A₀ * q, hfin, fun n G _ hΔ => ?_⟩
  obtain ⟨To, hTo⟩ : ∃ To, To = ⌊(A₀ : ℝ) * (2 : ℝ) ^ (δ / 3 / 2 * ((3 * M G : ℕ) : ℝ))⌋₊ := ⟨_, rfl⟩
  obtain ⟨So, hSo⟩ : ∃ So, So = A₀ * (3 * M G + 2) ^ A₀ + (2 * (3 * M G * (3 * M G) + 1) + 1) :=
    ⟨_, rfl⟩
  have hedge : (@SimpleGraph.edgeFinset _ (eulerSplitAll G) (eulerSplitAll G).fintypeEdgeSet).card ≤
      (Δ + 1) * (3 * M G) := by
    convert card_edge_eulerSplitAll_le G hΔ
  have hO : ∀ H : SimpleGraph (Fin (3 * M G)), H ≤ eulerSplitAll G → ∃ T w,
      Mh.Runs (GraphProblems.code H) T So w ∧ T ≤ To ∧ size w ≤ So ∧
        (w = [] ↔ ¬∃ X : Finset (Sym2 (Fin (3 * M G))),
          (X : Set (Sym2 (Fin (3 * M G)))) ⊆ H.edgeSet ∧ (TwoRegular X ∧ (graphOf X).Connected)) := by
    intro H hHG
    classical
    have hcard : H.edgeFinset.card ≤ (Δ + 1) * (3 * M G) := le_trans (Cor.card_edge_mono hHG) hedge
    obtain ⟨T, hR, hT⟩ := hA₀ H hcard
    refine ⟨T, _, hR.mono le_rfl (by omega), by rw [hTo]; exact Nat.le_floor hT, ?_,
      Cor.bits_hc_nil_iff H⟩
    have := Cor.size_bits_hc H
    omega
  obtain ⟨T, w, hR, hT, h1, h2⟩ := Srch.searchS_runs Mh (eulerSplitAll G) _ To So hO
  obtain ⟨o1, o2⟩ := Cor.search_out_hc (eulerSplitAll G) h1 h2
  rw [← eulW_code] at hR
  have hR' := Stepped.mapIn_runs hR
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [← length_edgeList G, ← cast_n2]
    have hm := M_le G
    obtain ⟨s1, s2, s3, s4, s5⟩ := small hm
    have hL : (GraphProblems.code G).length = n + 1 + n * n :=
      GraphProblems.length_code GraphProblems.stMatrixLength G
    have hToR : (To : ℝ) ≤ (A₀ : ℝ) * (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := by
      rw [← exp_three, hTo]; exact Nat.floor_le (by positivity)
    have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := Real.one_le_rpow one_le_two (by positivity)
    have hTR : (T : ℝ) ≤ ((3 * M G * (3 * M G) + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := by exact_mod_cast hT
    have h3 : (To : ℝ) + 3 ≤ ((A₀ : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := by nlinarith
    have hT3 : (T : ℝ) ≤ (((3 * M G * (3 * M G) + 1) * (A₀ + 3) : ℕ) : ℝ) *
        (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := by
      calc (T : ℝ) ≤ ((3 * M G * (3 * M G) + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := hTR
        _ ≤ ((3 * M G * (3 * M G) + 1 : ℕ) : ℝ) * (((A₀ : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 * (M G : ℝ))) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (((3 * M G * (3 * M G) + 1) * (A₀ + 3) : ℕ) : ℝ) * (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := by
            push_cast; ring
    refine hM (bB A₀) _ _ _ _ (n + 2) ((2 : ℝ) ^ (δ * (M G : ℝ))) (by omega)
      (Real.one_le_rpow one_le_two (by positivity)) hR' ?_ (exp_part hδ ?_ hT3)
    · apply absorb hm
      rw [hL, hSo]
      omega
    · apply absorb hm
      have hA : 3 * M G * (3 * M G) + 1 ≤ 10 * (n + 2) ^ 4 := by omega
      have hA1 : (3 * M G * (3 * M G) + 1) * (A₀ + 3) ≤ 10 * (n + 2) ^ 4 * (A₀ + 3) :=
        Nat.mul_le_mul_right _ hA
      have hA2 : 10 * (n + 2) ^ 4 * (A₀ + 3) = 10 * (A₀ * (n + 2) ^ 4) + 30 * (n + 2) ^ 4 := by ring
      omega
  · intro he
    refine o1 ?_
    rw [hamCycles_eulerSplit]
    show (eulerCircuitsAll G).image (phiE G) = ∅
    rw [he, image_empty]
  · intro hne
    obtain ⟨X, hX, hw⟩ := o2 (by rw [hamCycles_eulerSplit]; exact hne.image _)
    rw [hamCycles_eulerSplit, mem_image] at hX
    obtain ⟨T', hT', rfl⟩ := hX
    exact ⟨T', hT', hw⟩

end EthFollowup.ExactHC
