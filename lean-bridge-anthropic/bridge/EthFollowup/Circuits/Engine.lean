/-
# The rate engine inside the algorithm of Section 7: a padded function, not a stepped machine

Anthropic's `Eight.stAlg_of` runs a stepped #3-SAT engine (`Alg.EngineOK`: exact count over all N
variables, states of size c(N+2)^c, time c·2^{δN}). The rate engine `GeneralPieces.Tied.TopM`
(rates/GeneralPieces/Tied/Defs.lean) is instead a polynomial-time function `AM` of (input, pad) that
is correct once the pad has 2^{eM} units, with eM ≤ G·k·m/√log₂(m+2). We do not build a stepped
engine (referee issue 2): the whole algorithm is ONE polynomial-time function of (x, pad),

  aX(x, pad) = «the formula pre(x) is nonempty and AM(code of pre(x) renamed, pad) is 0»,

with the polynomial-time exponent eX(x) = eM(code of pre(x) renamed), and Anthropic's padding host
`PaddedDescent.exists_tm_padded` turns it into a Turing machine with time q·(|x| + 2^{eX x} + 1)^q.
The state-size question disappears: the host pays for the pad in the polynomial.

Referee issue 3 (count over occurring variables): the formula is renamed by Anthropic's
`VariableBound.Rename.renF`/`encN` (the variables that occur numbered 0, …), which gives AllOccur;
only «count = 0» is used, and `numSat_eq` (count = 2^{#free}·count over occurring) makes the
zero test exact (`aX_spec`). Issue 4: IsKCNF (≤ 3 literals, no repeated clause) is `Shaped3`, kept by
the renaming; m ≥ 1 because the empty formula is answered directly.
-/
import EthFollowup.Circuits.FormCount
import GeneralPieces.Main
import GeneralPieces.Num.Asymptotic
import VariableBound.Paper.Rename.Code
import VariableBound.Paper.Rename.Cert
import PaddedDescent.Pad

set_option linter.unusedSectionVars false

namespace EthFollowup.Circuits

open ENP Groundwork Turing CircuitLowerBound PaddedDescent PaddedDescent.F ClauseBound.Alg
open VariableBound.Rename MainTheoremForms
open Sat3 (CNF)

/-- The rate engine of Theorem A(c) (first sentence) for the named programs, at ρ = 1/√2, i.e.
r(m) = 1/√log₂(m+2): Anthropic's proof (`thmRunningTime_c_m_tied` on the pieces of Theorem B). -/
theorem exists_topM : ∃ (Idx : Type) (_ : Enc Idx) (S : Solver Idx) (pick : U → U × Idx),
    GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2)) := by
  obtain ⟨c, P₀, A', val, h⟩ := GeneralPieces.thmHalfPieces_iff.1 AppRunningTime.thmHalfPieces
  have hT := GeneralPieces.thmRunningTime_c_m_tied h.1
  unfold GeneralPieces.Tied.PartCm at hT
  have hα : AppRunningTime.alpha' (1 / Real.sqrt 2) = 1 / 2 := GeneralPieces.Asymptotic.alpha_half
  rw [hα] at hT
  exact ⟨_, _, _, _, hT⟩

/-! ### The formula as an input of the engine -/

/-- The code of (3, ψ with the occurring variables renamed). -/
def fmlCode (ψ : Cnf) : List Bool := encN (List.replicate 3 ()) (renF ψ)

theorem fmlCode_polyT {α : Type} [Enc α] {ψ : α → Cnf} (h : PolyT ψ) : PolyT fun x => fmlCode (ψ x) :=
  encN_polyT (PolyT.const _) (renF_polyT h)

/-- ψ as a formula on x₀ … x_N. -/
def liftF (N : ℕ) (ψ : Cnf) : CNF (N + 1) := ψ.map fun C => C.map fun l => (Fin.ofNat (N + 1) l.1, l.2)

theorem toN_liftF {N : ℕ} {ψ : Cnf} (h : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N) : Decode.toN (liftF N ψ) = ψ := by
  unfold Decode.toN liftF
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ψ]
  refine List.map_congr_left fun D hD => ?_
  simp only [Function.comp_apply, List.map_map, id]
  conv_rhs => rw [← List.map_id D]
  refine List.map_congr_left fun l hl => ?_
  simp only [Function.comp_apply, Fin.val_ofNat, id]
  rw [Nat.mod_eq_of_lt (by have := h D hD l hl; omega)]

theorem fmlCode_eq {N : ℕ} {ψ : Cnf} (h : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N) :
    fmlCode ψ = SatM.enc 3 (ren (liftF N ψ)) := by
  conv_lhs => rw [← toN_liftF h]
  unfold fmlCode
  rw [← encN_toN, toN_ren, renF, ← length_occL, List.map_const']

theorem isKCNF_liftF {N : ℕ} {ψ : Cnf} (h : Shaped3 N ψ) : SatK.IsKCNF 3 (liftF N ψ) := by
  refine ⟨fun C hC => ?_, ?_⟩
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
    rw [List.length_map]
    exact (h.1 D hD).1
  · have h2 : (Decode.toN (liftF N ψ)).Nodup := by rw [toN_liftF fun D hD => (h.1 D hD).2]; exact h.2
    exact List.Nodup.of_map _ h2

theorem satisfiable_liftF {N : ℕ} {ψ : Cnf} (h : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N) :
    Sat3.Satisfiable (liftF N ψ) ↔ Sat ψ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun v => if hv : v < N + 1 then a ⟨v, hv⟩ else false, fun D hD => ?_⟩
    obtain ⟨l, hl, hal⟩ := ha _ (List.mem_map.2 ⟨D, hD, rfl⟩)
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    have hv := h D hD l' hl'
    refine ⟨l', hl', ?_⟩
    have hfin : (⟨l'.1, by omega⟩ : Fin (N + 1)) = Fin.ofNat (N + 1) l'.1 :=
      Fin.ext (by simp [Nat.mod_eq_of_lt (show l'.1 < N + 1 by omega)])
    show (if hv : l'.1 < N + 1 then a ⟨l'.1, hv⟩ else false) = l'.2
    rw [dif_pos (by omega), hfin]
    exact hal
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.val, fun C hC => ?_⟩
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
    obtain ⟨l, hl, hal⟩ := ha D hD
    have hv := h D hD l hl
    refine ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show l.1 < N + 1 by omega)]
    exact hal

theorem numSat_eq_zero_iff {n : ℕ} (φ : CNF n) : SatK.numSat φ = 0 ↔ ¬Sat3.Satisfiable φ := by
  unfold SatK.numSat Sat3.Satisfiable
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro h ⟨a, ha⟩
    exact h (Finset.mem_univ a) ha
  · intro h a _ ha
    exact h ⟨a, ha⟩

theorem numSat_lt {n : ℕ} (φ : CNF n) : SatK.numSat φ < 2 ^ (n + 1) := by
  unfold SatK.numSat
  refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n)

variable {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx)

/-- The engine's answer «count = 0» is «ψ is unsatisfiable», for a nonempty formula of the shape. -/
theorem isZ_AM_iff (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2))) {N : ℕ} {ψ : Cnf} (hsh : Shaped3 N ψ)
    (hne : ψ ≠ []) (pad : U) (hp : 2 ^ eM S pick (fmlCode ψ) ≤ pad.length) :
    Alg.isZ (AM S pick (fmlCode ψ, pad)) = true ↔ ¬Sat ψ := by
  have hv : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N := fun D hD => (hsh.1 D hD).2
  rw [fmlCode_eq hv] at hp ⊢
  have hlen : 1 ≤ (ren (liftF N ψ)).length := by
    rw [length_ren, liftF, List.length_map]
    exact List.length_pos_iff.2 hne
  rw [hT.correct 3 _ _ (by norm_num) hlen (isKCNF_ren _ (isKCNF_liftF hsh)) (allOccur_ren _) pad hp,
    Alg.isZ_binary (numSat_lt _), numSat_ren, ← satisfiable_liftF hv, ← numSat_eq_zero_iff, numSat_eq]
  constructor
  · intro h; rw [h, Nat.mul_zero]
  · intro h
    rcases Nat.mul_eq_zero.1 h with h | h
    · exact absurd h (by positivity)
    · exact h

/-- The rate at the formula: eM ≤ G·3·m·r(m), m the number of clauses. -/
theorem eM_le {G : ℕ} (hG : ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      (eM S pick (SatM.enc k φ) : ℝ) ≤ G * ((k : ℝ) * φ.length * SatM.rPow (1 / 2) φ.length))
    {N : ℕ} {ψ : Cnf} (hsh : Shaped3 N ψ) (hne : ψ ≠ []) :
    (eM S pick (fmlCode ψ) : ℝ) ≤ G * (3 * ψ.length * SatM.rPow (1 / 2) ψ.length) := by
  have hv : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N := fun D hD => (hsh.1 D hD).2
  have hl : (ren (liftF N ψ)).length = ψ.length := by rw [length_ren, liftF, List.length_map]
  have hlen : 1 ≤ (ren (liftF N ψ)).length := by rw [hl]; exact List.length_pos_iff.2 hne
  have := hG 3 _ _ (by norm_num) hlen (isKCNF_ren _ (isKCNF_liftF hsh)) (allOccur_ren _)
  rw [hl, ← fmlCode_eq hv] at this
  exact_mod_cast this

/-! ### The algorithm as a padded function -/

variable (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool)

/-- The exponent of the pad. -/
def eX (x : List Bool) : ℕ := bif (Alg.pre F fb x).2.isEmpty then 0 else eM S pick (fmlCode (Alg.pre F fb x).2)

/-- The answer: true if and only if the formula of the algorithm is unsatisfiable (`aX_spec`). -/
def aX (p : List Bool × U) : Bool :=
  bif (Alg.pre F fb p.1).2.isEmpty then false else Alg.isZ (AM S pick (fmlCode (Alg.pre F fb p.1).2, p.2))

theorem eX_polyT (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2))) (hS : StCertSched) (hF : PolyT F) (hb : PolyT fb) :
    PolyT (eX S pick F fb) := by
  have h1 := Alg.pre_polyT hS hF hb
  have h2 : PolyT fun x => fmlCode (Alg.pre F fb x).2 := fmlCode_polyT (by fun_prop)
  have h3 : PolyT fun x => eM S pick (fmlCode (Alg.pre F fb x).2) := hT.poly_e.comp h2
  unfold eX
  fun_prop

theorem aX_polyT (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2))) (hS : StCertSched) (hF : PolyT F) (hb : PolyT fb) :
    PolyT (aX S pick F fb) := by
  have h1 := Alg.pre_polyT hS hF hb
  have h2 : PolyT fun p : List Bool × U => fmlCode (Alg.pre F fb p.1).2 := fmlCode_polyT (by fun_prop)
  have h3 : PolyT fun p : List Bool × U => AM S pick (fmlCode (Alg.pre F fb p.1).2, p.2) := hT.poly_A.comp (by fun_prop)
  have h4 : PolyT fun p : List Bool × U => Alg.isZ (AM S pick (fmlCode (Alg.pre F fb p.1).2, p.2)) := Alg.isZ_polyT.comp h3
  unfold aX
  fun_prop

/-- The answer of the algorithm with the pad of 2^{eX x} units is «the formula is unsatisfiable». -/
theorem aX_spec (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2))) {a₀ : ℕ} {g : MCode → ℕ} (hF : Alg.FormOK a₀ g F)
    (x : List Bool) : aX S pick F fb (x, pad (eX S pick F fb x)) = true ↔ ¬Sat (Alg.pre F fb x).2 := by
  have hsh := Alg.shaped_pre (fb := fb) hF x
  unfold aX eX
  cases h : (Alg.pre F fb x).2.isEmpty
  · have hne : (Alg.pre F fb x).2 ≠ [] := fun h' => by rw [h', List.isEmpty_nil] at h; exact Bool.noConfusion h
    simp only [cond_false]
    exact isZ_AM_iff S pick hT hsh hne _ (by simp [pad])
  · have he : (Alg.pre F fb x).2 = [] := List.isEmpty_iff.1 h
    simp only [cond_true, Bool.false_eq_true, false_iff, not_not, he]
    exact Alg.sat_nil

/-- The formula of the algorithm has at most 4·Nv + 1 clauses. -/
theorem pre_count (hc : ∀ q, (F q).2.length ≤ 4 * (F q).1.length + 1) (x : List Bool) :
    (Alg.pre F fb x).2.length ≤ 4 * (Alg.pre F fb x).1.length + 1 := by
  rcases Alg.pre_cases F fb x with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e]
  · exact hc _
  all_goals simp

end EthFollowup.Circuits
