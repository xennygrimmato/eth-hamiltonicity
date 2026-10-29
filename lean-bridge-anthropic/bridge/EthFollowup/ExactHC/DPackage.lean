/-
# The uniform degree package, and Theorem 3 (thm:main-degree) unconditionally (module A1, file 7)

`research/hc-degree-theorem.md` §2–4. We construct `T3.DPackage 10` from

* the rank-encoded network `N_s = (crossV g G).netS 0 s` of `RankNetwork.lean` for the vertex-balanced
  partition and the crossing order `RW.crossV` (`RankWordProcs.lean`), with the profile `s` of the index
  `y < (n²+1)^{g·g}` (`VB.prof`);
* the procedures `RW.rankProcs` (A2: layout, parity procedure, degree-pruned table procedure, all with
  `g` read from the context) and `RW.rank_given`, `RW.state_boundU`;
* the test `goodW` (lower digits zero, admissible, `s ≤ e`), the value `sum_netS` (Theorem 2.5) via
  `VB.sum_profiles`, the parameters `netS_is`, `U_netS_le` (Proposition 3.2).

Results: `DPkg.dPackage : Nonempty (T3.DPackage 10)`, **`theorem3`** (average degree) and
**`theorem3_maxdeg`** (maximum degree), unconditional at Turing-machine level.
-/
import EthFollowup.ExactHC.Theorem3
import EthFollowup.ExactHC.RankNetwork
import EthFollowup.ExactHC.RankWordProcs

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace DPkg

open Groundwork Groundwork.Prog GraphProblems Asm Finset Eight.SecNetworks

/-! ## The word-level data -/

/-- The radix of the profile digits: `n² + 1 > m`. -/
def RdN (n : ℕ) : ℕ := n * n + 1

/-- The number of profile indices `(n²+1)^{g·g}`. -/
def nPrW (g : ℕ) (a : GIn) : ℕ := VB.nPrN (RdN a.1.length) g

/-- The number of vertices of blob `b`. -/
def blobW (g : ℕ) (a : GIn) (b : ℕ) : ℕ := (RW.vaV g a b).length

/-- Admissibility of the profile `y`: `∑_{c ≠ b} s_bc ≤ 2|V_b|`. -/
def admW (g : ℕ) (a : GIn) (y : ℕ) : Bool :=
  (List.range g).all fun b =>
    decide (((RW.othV g b).map fun c => VB.profN (RdN a.1.length) g y b c).sum ≤ 2 * blobW g a b)

/-- `s_bc ≤ e_bc`. -/
def bndW (g : ℕ) (a : GIn) (y : ℕ) : Bool :=
  (List.range g).all fun b => (List.range g).all fun c =>
    decide (VB.profN (RdN a.1.length) g y b c ≤ RW.eV g a b c)

/-- **The test of a profile index.** -/
def goodW (g : ℕ) (a : GIn) (y : ℕ) : Bool :=
  VB.upperN (RdN a.1.length) g y && admW g a y && bndW g a y

/-- The context of `(g, y, graph)`. -/
def prepD (p : List Unit × (ℕ × GIn)) : RW.UR :=
  (p.1, (p.2.2, RW.profMatN p.1.length (RdN p.2.2.1.length) p.2.1))

/-! ## Polynomial time -/

section Poly

theorem RdN_polyT {α : Type} [Enc α] {a : α → GIn} (ha : PolyT a) : PolyT fun x => RdN (a x).1.length := by
  unfold RdN; fun_prop

theorem prepD_polyT : PolyT prepD := by
  have hu : PolyT fun p : List Unit × (ℕ × GIn) => p.1 := by fun_prop
  have hR := RdN_polyT (a := fun p : List Unit × (ℕ × GIn) => p.2.2) (by fun_prop)
  have h := RW.profMatN_polyU hu hR (y := fun p => p.2.1) (by fun_prop)
  unfold prepD; fun_prop

theorem nPrW_polyT : PolyT fun p : List Unit × GIn => nPrW p.1.length p.2 := by
  have hR := RdN_polyT (a := fun p : List Unit × GIn => p.2) (by fun_prop)
  have hg : Unary fun p : List Unit × GIn => p.1.length := Unary.of_length (by fun_prop)
  unfold nPrW VB.nPrN
  exact PolyT.pow_unary hR (hg.mul hg)

section Gen

variable {α : Type} [Enc α] {u : α → List Unit} (hu : PolyT u) {a : α → GIn} (ha : PolyT a)
include hu ha

theorem profSum_polyT {y b : α → ℕ} (hy : PolyT y) (hb : PolyT b) :
    PolyT fun x => ((RW.othV (u x).length (b x)).map fun c =>
      VB.profN (RdN (a x).1.length) (u x).length (y x) (b x) c).sum := by
  have ho := RW.othV_polyU hu hb
  have hpr : PolyT fun p : α × ℕ => VB.profN (RdN (a p.1).1.length) (u p.1).length (y p.1) (b p.1) p.2 :=
    VB.profN_polyT (RdN_polyT (ha.comp PolyT.id'.fst)) (PolyT.length (hu.comp PolyT.id'.fst))
      (hy.comp PolyT.id'.fst) (hb.comp PolyT.id'.fst) PolyT.id'.snd
  exact PolyT.sum (PolyT.map (f := fun x c => VB.profN (RdN (a x).1.length) (u x).length (y x) (b x) c) hpr ho)

theorem admW_polyT {y : α → ℕ} (hy : PolyT y) : PolyT fun x => admW (u x).length (a x) (y x) := by
  have hr := PolyT.range (Unary.of_length hu)
  have hu1 : PolyT fun p : α × ℕ => u p.1 := hu.comp PolyT.id'.fst
  have ha1 : PolyT fun p : α × ℕ => a p.1 := ha.comp PolyT.id'.fst
  have hs := profSum_polyT hu1 ha1 (y := fun p => y p.1) (b := fun p => p.2) (hy.comp PolyT.id'.fst)
    PolyT.id'.snd
  have hva := RW.vaV_polyU hu1 (a := fun p => a p.1) (b := fun p => p.2) ha1 PolyT.id'.snd
  have hin : PolyT fun p : α × ℕ => decide (((RW.othV (u p.1).length p.2).map fun c =>
      VB.profN (RdN (a p.1).1.length) (u p.1).length (y p.1) p.2 c).sum ≤
        2 * (RW.vaV (u p.1).length (a p.1) p.2).length) :=
    PolyT.decide_le hs (PolyT.mul (PolyT.const 2) (PolyT.length hva))
  unfold admW blobW
  exact PolyT.all (f := fun x b => decide (((RW.othV (u x).length b).map fun c =>
    VB.profN (RdN (a x).1.length) (u x).length (y x) b c).sum ≤ 2 * (RW.vaV (u x).length (a x) b).length)) hin hr

theorem bndW_polyT {y : α → ℕ} (hy : PolyT y) : PolyT fun x => bndW (u x).length (a x) (y x) := by
  have hr := PolyT.range (Unary.of_length hu)
  have hu1 : PolyT fun p : α × ℕ => u p.1 := hu.comp PolyT.id'.fst
  have hr1 : PolyT fun p : α × ℕ => List.range (u p.1).length := PolyT.range (Unary.of_length hu1)
  have hu2 : PolyT fun p : (α × ℕ) × ℕ => u p.1.1 := hu.comp PolyT.id'.fst.fst
  have ha2 : PolyT fun p : (α × ℕ) × ℕ => a p.1.1 := ha.comp PolyT.id'.fst.fst
  have hpr : PolyT fun p : (α × ℕ) × ℕ => VB.profN (RdN (a p.1.1).1.length) (u p.1.1).length (y p.1.1) p.1.2 p.2 :=
    VB.profN_polyT (RdN_polyT ha2) (PolyT.length hu2) (hy.comp PolyT.id'.fst.fst) PolyT.id'.fst.snd PolyT.id'.snd
  have he := (RW.eV_unaryU hu2 (a := fun p => a p.1.1) (b := fun p => p.1.2) (c := fun p => p.2)
    ha2 PolyT.id'.fst.snd PolyT.id'.snd).poly
  have hin : PolyT fun p : (α × ℕ) × ℕ => decide (VB.profN (RdN (a p.1.1).1.length) (u p.1.1).length (y p.1.1) p.1.2 p.2 ≤
      RW.eV (u p.1.1).length (a p.1.1) p.1.2 p.2) := PolyT.decide_le hpr he
  have hmid : PolyT fun p : α × ℕ => (List.range (u p.1).length).all fun c =>
      decide (VB.profN (RdN (a p.1).1.length) (u p.1).length (y p.1) p.2 c ≤ RW.eV (u p.1).length (a p.1) p.2 c) :=
    PolyT.all (f := fun p c => decide (VB.profN (RdN (a p.1).1.length) (u p.1).length (y p.1) p.2 c ≤
      RW.eV (u p.1).length (a p.1) p.2 c)) hin hr1
  unfold bndW
  exact PolyT.all (f := fun x b => (List.range (u x).length).all fun c =>
    decide (VB.profN (RdN (a x).1.length) (u x).length (y x) b c ≤ RW.eV (u x).length (a x) b c)) hmid hr

end Gen

theorem goodW_polyT : PolyT fun p : (List Unit × GIn) × ℕ => goodW p.1.1.length p.1.2 p.2 := by
  have hu : PolyT fun p : (List Unit × GIn) × ℕ => p.1.1 := PolyT.id'.fst.fst
  have ha : PolyT fun p : (List Unit × GIn) × ℕ => p.1.2 := PolyT.id'.fst.snd
  have hy : PolyT fun p : (List Unit × GIn) × ℕ => p.2 := PolyT.id'.snd
  have h1 := VB.upperN_polyT (RdN_polyT ha) (Unary.of_length hu) hy
  unfold goodW
  exact PolyT.and' (PolyT.and' h1 (admW_polyT hu ha hy)) (bndW_polyT hu ha hy)

end Poly

/-! ## The graph side -/

section Graph

/-- A network for the excluded cases `g = 0` or `n = 0` (never used). -/
def dummyNet (g : ℕ) : Net g := ⟨fun _ => 0, fun _ => ∅, fun _ _ => 0, fun _ _ _ _ => 0, fun _ _ => 0, fun _ _ _ _ => 0⟩

/-- **The network of the profile index `y`**: `N_s` for `s = VB.prof (n²+1) g y`. -/
noncomputable def netD : (g : ℕ) → ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → Net g
  | 0, _, _, _ => dummyNet 0
  | _ + 1, 0, _, _ => dummyNet _
  | g + 1, n + 1, G, y =>
    haveI := Classical.decRel G.Adj
    (RW.crossV (g + 1) G).netS 0 (VB.prof (RdN (n + 1)) (g + 1) y)

/-- The degree bound `max 2 Δ`. -/
noncomputable def DD {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  haveI := Classical.decRel G.Adj
  max 2 G.maxDegree

theorem netS_congr {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
    (X : Crossing G β m) (r : Fin n) {s s' : Fin g → Fin g → ℕ} (e : s' = s) (h1 : ∀ a b, s' a b = s' b a)
    (h2 : ∀ a b, s a b = s b a) :
    (X.hcSystem r).netP ((X.hcSystem r).rankPC s' h1 rfl) = (X.hcSystem r).netP ((X.hcSystem r).rankPC s h2 rfl) := by
  subst e; rfl

theorem netS_eq {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
    (X : Crossing G β m) (r : Fin n) {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a) :
    X.netS r s = (X.hcSystem r).netP ((X.hcSystem r).rankPC s hs rfl) :=
  netS_congr X r (symProf_eq hs) _ hs

variable {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]

theorem card_blob_eq (a : Fin g) :
    #(blob (VB.vertexBalanced (n + 1) g) a) = blobW g (aOf G) a.val := by
  unfold blobW RW.vaV
  rw [aOf_len, ← Pkg.map_val_filter_finRange (fun v : Fin (n + 1) => decide (VB.vertexBalanced (n + 1) g v = a))
    _ (fun v => by simp [Fin.ext_iff, RW.bV, aOf_len]; rfl), List.length_map,
    length_filter_of_complete _ (List.nodup_finRange _) List.mem_finRange]
  rfl

theorem sum_othV (a : Fin g) (h : ℕ → ℕ) :
    ((RW.othV g a.val).map h).sum = ∑ b ∈ univ.erase a, h b.val := by
  rw [RW.othV_eq, List.map_map, ← List.sum_toFinset _ (othersL_nodup a)]
  congr 1
  ext b; simp [mem_othersL]

theorem admW_iff (y : ℕ) :
    admW g (aOf G) y = true ↔ Crossing.Adm (VB.vertexBalanced (n + 1) g) (VB.prof (RdN (n + 1)) g y) := by
  simp only [admW, List.all_eq_true, List.mem_range, decide_eq_true_eq, aOf_len]
  constructor
  · intro h a
    have := h a.val a.2
    rw [sum_othV, ← card_blob_eq] at this
    exact this
  · intro h b hb
    have := h ⟨b, hb⟩
    have e := card_blob_eq G ⟨b, hb⟩
    simp only at e
    rw [sum_othV (a := ⟨b, hb⟩), ← e]
    exact this

theorem bndW_iff (y : ℕ) :
    bndW g (aOf G) y = true ↔ Crossing.Bnd (RW.crossV g G) 0 (VB.prof (RdN (n + 1)) g y) := by
  simp only [bndW, List.all_eq_true, List.mem_range, decide_eq_true_eq, aOf_len, Crossing.Bnd,
    Crossing.eP]
  constructor
  · intro h a b
    have := h a.val a.2 b.val b.2
    rwa [RW.eV_eq G 0 a b] at this
  · intro h b hb c hc
    have := h ⟨b, hb⟩ ⟨c, hc⟩
    rw [RW.eV_eq G 0 ⟨b, hb⟩ ⟨c, hc⟩]
    exact this

theorem goodW_iff (y : ℕ) :
    goodW g (aOf G) y = true ↔ VB.upperN (RdN (n + 1)) g y = true ∧
      (Crossing.Adm (VB.vertexBalanced (n + 1) g) (VB.prof (RdN (n + 1)) g y) ∧
        Crossing.Bnd (RW.crossV g G) 0 (VB.prof (RdN (n + 1)) g y)) := by
  rw [← admW_iff G y, ← bndW_iff G y]
  simp [goodW, aOf_len, Bool.and_assoc]

theorem mV_lt : RW.mV g G < RdN (n + 1) := by
  have h2 : (RW.cplV g (aOf G)).length ≤ (Pkg.pairsW (aOf G)).length := List.length_filter_le _ _
  have h3 : (Pkg.pairsW (aOf G)).length = (n + 1) * (n + 1) := by
    simp [Pkg.pairsW, aOf_len, List.length_product]
  show (RW.cplV g (aOf G)).length < _
  unfold RdN; omega

theorem card_mV_le : RW.mV g G ≤ G.edgeFinset.card := by
  have := Finset.card_le_card_of_injOn (RW.crossV g G).edge (s := (univ : Finset (Fin (RW.mV g G))))
    (t := G.edgeFinset) (by intro k _; exact (RW.crossV g G).edge_mem_edgeFinset k)
    (RW.crossV g G).edge_injective.injOn
  simpa using this

/-- **The value** (Theorem 2.5 with the enumeration of the profiles). -/
theorem value_D :
    ∑ y ∈ range (nPrW g (aOf G)), (if goodW g (aOf G) y = true then
      ((RW.crossV g G).netS 0 (VB.prof (RdN (n + 1)) g y)).value else 0) =
      ((n + 1 : ℕ) : ℤ) * ((Hamiltonian.hamCycles G).card : ℤ) := by
  have e : ∀ y, (if goodW g (aOf G) y = true then
      ((RW.crossV g G).netS 0 (VB.prof (RdN (n + 1)) g y)).value else 0) =
      if VB.upperN (RdN (n + 1)) g y = true then
        (fun s => if Crossing.Adm (VB.vertexBalanced (n + 1) g) s ∧ Crossing.Bnd (RW.crossV g G) 0 s then
          ((RW.crossV g G).netS 0 s).value else 0) (VB.prof (RdN (n + 1)) g y) else 0 := by
    intro y
    by_cases hu : VB.upperN (RdN (n + 1)) g y = true
    · by_cases hab : Crossing.Adm (VB.vertexBalanced (n + 1) g) (VB.prof (RdN (n + 1)) g y) ∧
          Crossing.Bnd (RW.crossV g G) 0 (VB.prof (RdN (n + 1)) g y)
      · rw [if_pos ((goodW_iff G y).2 ⟨hu, hab⟩), if_pos hu]; simp only [if_pos hab]
      · rw [if_neg (fun h => hab ((goodW_iff G y).1 h).2), if_pos hu]; simp only [if_neg hab]
    · rw [if_neg (fun h => hu ((goodW_iff G y).1 h).1), if_neg hu]
  rw [sum_congr rfl fun y _ => e y]
  unfold nPrW
  rw [aOf_len]
  refine (VB.sum_profiles (Rd := RdN (n + 1)) (by unfold RdN; omega) g (fun s =>
    if Crossing.Adm (VB.vertexBalanced (n + 1) g) s ∧ Crossing.Bnd (RW.crossV g G) 0 s then
      ((RW.crossV g G).netS 0 s).value else 0)).trans ?_
  exact (RW.crossV g G).sum_netS 0 (mV_lt G)

end Graph

/-! ## The bounds -/

section Bounds

theorem two_pow_ge (k : ℕ) : k < 2 ^ k := Nat.lt_two_pow_self

/-- `|value(N_s)| < 2^{3n² + 1 + g(2n²+1)}`. -/
theorem natAbs_value_lt {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
    (X : Crossing G β m) (r : Fin n) (s : Fin g → Fin g → ℕ) (hm : m ≤ n * n) :
    (X.netS r s).value.natAbs < 2 ^ (3 * (n * n) + 1 + g * (2 * (n * n) + 1)) := by
  have hT : ∀ ℓ : Fin m → Label, |(if (∀ a b, a ≠ b → X.profL r ℓ a b = symProf s a b) then
      ∏ a, (X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ) else 0)| ≤ 2 ^ (g * (2 * (n * n) + 1)) := by
    intro ℓ
    split_ifs
    · rw [Finset.abs_prod]
      calc ∏ a, |(X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ)| ≤ ∏ _a : Fin g, (2 : ℤ) ^ (2 * (n * n) + 1) :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun a _ => (Crossing.abs_T_lt (X := X) (r := r) a ℓ _).le
        _ = 2 ^ (g * (2 * (n * n) + 1)) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    · simp
  have h1 : |(X.netS r s).value| ≤ ((5 ^ m : ℕ) : ℤ) * 2 ^ (g * (2 * (n * n) + 1)) := by
    rw [Crossing.value_netS]
    refine (abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun ℓ _ => hT ℓ).trans ?_)
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    have hL : Fintype.card Label = 5 := rfl
    rw [hL]
  have h5 : 5 ^ m < 2 ^ (3 * (n * n) + 1) := by
    calc 5 ^ m ≤ 8 ^ m := Nat.pow_le_pow_left (by norm_num) m
      _ ≤ 8 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) hm
      _ = 2 ^ (3 * (n * n)) := by rw [pow_mul 2 3, show (2 : ℕ) ^ 3 = 8 by norm_num]
      _ < 2 ^ (3 * (n * n) + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h5' : ((5 ^ m : ℕ) : ℤ) < 2 ^ (3 * (n * n) + 1) := by exact_mod_cast h5
  have h2 : ((5 ^ m : ℕ) : ℤ) * 2 ^ (g * (2 * (n * n) + 1)) < 2 ^ (3 * (n * n) + 1 + g * (2 * (n * n) + 1)) := by
    rw [pow_add]; exact mul_lt_mul_of_pos_right h5' (by positivity)
  have h3 : ((X.netS r s).value.natAbs : ℤ) < 2 ^ (3 * (n * n) + 1 + g * (2 * (n * n) + 1)) := by
    rw [Int.natCast_natAbs]; exact h1.trans_lt h2
  exact_mod_cast h3

end Bounds

/-! ## The package -/

section Package

open Printed

theorem isNetwork_mono {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g}
    {P B τ S S' : ℕ} (h : IsNetwork Np c N P B τ S) (hS : S ≤ S') : IsNetwork Np c N P B τ S' :=
  ⟨h.is, h.τ_pos,
    { P_eq := h.given.P_eq
      B_eq := h.given.B_eq
      len_eq := h.given.len_eq
      cap_eq := h.given.cap_eq
      mem_runs := fun a z hz => (h.given.mem_runs a z hz).mono le_rfl hS
      W_runs := fun a z hz => (h.given.W_runs a z hz).mono le_rfl hS
      Ψ_runs := fun a b hab z hz z' hz' => (h.given.Ψ_runs a b hab z hz z' hz').mono le_rfl hS
      f_runs := fun a b hab z hz θ hθ => (h.given.f_runs a b hab z hz θ hθ).mono le_rfl hS }⟩

/-- The constant of `RW.state_boundU`. -/
noncomputable def AS : ℕ := RW.state_boundU.choose

theorem AS_spec : ∀ (g : ℕ) [NeZero g] (n : ℕ) (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
    (s : Fin g → Fin g → ℕ), (∀ a b, s a b ≤ (((RW.crossV g G).hcSystem 0).pairItems a b).length) →
    ∀ D : ℕ, D ≤ n + 2 →
      RW.SRU g G s D + size (RW.cRk g G s) + 2 * g + 4 * RW.PR g (aOf G) + 8 ≤ AS * (n + g + 2) ^ AS :=
  RW.state_boundU.choose_spec

/-- The state bound of the package. -/
noncomputable def SD (g : ℕ) {n : ℕ} (_G : SimpleGraph (Fin n)) : ℕ := AS * (n + g + 2) ^ AS

theorem lgN_eq (n : ℕ) : T3.lgN n = Nat.log2 (n + 2) := Nat.log2_eq_log_two.symm

theorem lgN_eq' (n : ℕ) : lgN n = Nat.log2 (n + 2) := Nat.log2_eq_log_two.symm

theorem PR_eq (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    RW.PR g (aOf G) = 10 * ((n / g + 1) * lgN n) + 2 * g ^ 2 + 1 := by
  simp [RW.PR, aOf_len, lgN_eq']

theorem BR_eq {n : ℕ} (G : SimpleGraph (Fin n)) : RW.BR (aOf G) = 2 * (n * n) + 1 := by
  simp [RW.BR, aOf_len]

theorem prepD_eq (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (y : ℕ) :
    prepD (Printed.unary g, (y, aOf G)) = RW.cRk g G (VB.prof (RdN n) g y) := by
  simp only [prepD, RW.cRk, aOf_len, Printed.unary, List.length_replicate, RW.profMatN_eq]

theorem netD_eq {g n : ℕ} (G : SimpleGraph (Fin (n + 1))) [inst : DecidableRel G.Adj] (y : ℕ) :
    netD (g + 1) G y = (RW.crossV (g + 1) G).netS 0 (VB.prof (RdN (n + 1)) (g + 1) y) := by
  obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
  rfl

theorem DD_eq {n : ℕ} (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj] : DD G = max 2 G.maxDegree := by
  obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
  rfl

theorem maxDegree_le {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] : G.maxDegree ≤ n := by
  have := G.maxDegree_lt_card_verts
  simp at this; omega

/-- **One network**, from `RW.rank_given` and `netS_is`. -/
theorem isNet_D {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] {y : ℕ}
    (hgood : goodW g (aOf G) y = true) :
    IsNetwork RW.rankProcs (prepD (Printed.unary g, (y, aOf G)))
      ((RW.crossV g G).netS 0 (VB.prof (RdN (n + 1)) g y)) (RW.PR g (aOf G)) (RW.BR (aOf G))
      (RW.τR g (n + 1) (max 2 G.maxDegree)) (SD g G) := by
  obtain ⟨-, hA, hB⟩ := (goodW_iff G y).1 hgood
  have hs := VB.prof_symm (RdN (n + 1)) g y
  have hN := Crossing.netS_is (X := RW.crossV g G) (r := 0) (VB.prof (RdN (n + 1)) g y) hs hA
    (ν := (n + 1) / g + 1) (fun a => VB.card_blob_vb_le (n + 1) g a)
  rw [netS_eq _ _ hs] at hN ⊢
  rw [show 10 * (((n + 1) / g + 1) * lgN (n + 1)) + 2 * g ^ 2 + 1 = RW.PR g (aOf G) from (PR_eq g G).symm,
    show 2 * ((n + 1) * (n + 1)) + 1 = RW.BR (aOf G) from (BR_eq G).symm] at hN
  have hD2 : 2 ≤ max 2 G.maxDegree := le_max_left _ _
  have hdeg : ∀ v, G.degree v ≤ max 2 G.maxDegree := fun v => (G.degree_le_maxDegree v).trans (le_max_right _ _)
  have h := (RW.rank_given G hs hB hD2 hdeg hN).1
  rw [prepD_eq]
  refine isNetwork_mono h ?_
  have hD : max 2 G.maxDegree ≤ n + 2 := max_le (by omega) ((maxDegree_le G).trans (by omega))
  have := AS_spec g n G _ hB _ hD
  have hmono : AS * (n + g + 2) ^ AS ≤ AS * (n + 1 + g + 2) ^ AS :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  unfold SD
  omega

theorem size_prepD_le {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] {y : ℕ}
    (hgood : goodW g (aOf G) y = true) :
    size (prepD (Printed.unary g, (y, aOf G))) ≤ AS * (n + 1 + g + 2) ^ AS := by
  obtain ⟨-, -, hB⟩ := (goodW_iff G y).1 hgood
  have hD : 2 ≤ n + 2 := by omega
  have := AS_spec g n G _ hB 2 hD
  have hmono : AS * (n + g + 2) ^ AS ≤ AS * (n + 1 + g + 2) ^ AS :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  rw [prepD_eq]
  omega

theorem pow_ge_cube {x q : ℕ} (hx : 1 ≤ x) (hq : 3 ≤ q) : x ^ 3 ≤ x ^ q := Nat.pow_le_pow_right hx hq

theorem expo_le {n g q : ℕ} (hq : 6 ≤ q) :
    3 * (n * n) + 1 + g * (2 * (n * n) + 1) ≤ q * (n + g + 2) ^ q := by
  set x := n + g + 2 with hx
  have hn : n ≤ x := by omega
  have hg : g ≤ x := by omega
  have h1 : 3 * (n * n) + 1 + g * (2 * (n * n) + 1) ≤ 6 * x ^ 3 := by
    have : n * n ≤ x * x := Nat.mul_le_mul hn hn
    have : g * (2 * (n * n) + 1) ≤ x * (2 * (x * x) + 1) := Nat.mul_le_mul hg (by omega)
    have : 1 ≤ x := by omega
    have : x * x ≤ x ^ 3 := by nlinarith
    have : x * (2 * (x * x) + 1) ≤ 3 * x ^ 3 := by nlinarith
    nlinarith
  have h2 := pow_ge_cube (show 1 ≤ x by omega) (show 3 ≤ q by omega)
  calc _ ≤ 6 * x ^ 3 := h1
    _ ≤ q * x ^ q := Nat.mul_le_mul hq h2

/-- The τ bound: `3·D^{2ν}·5^ν ≤ 2^{10·ν·lgN n} · 3`. -/
theorem τR_le {g n D : ℕ} (hD : D ≤ n) :
    RW.τR g n D ≤ 2 ^ (10 * ((n / g + 1) * T3.lgN n)) * 3 := by
  unfold RW.τR
  set ν := n / g + 1
  set L := T3.lgN n
  have hL : 1 ≤ L := Nat.log_pos (by norm_num) (by omega)
  have hDL : D < 2 ^ (L + 1) := lt_of_le_of_lt hD (by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2); unfold L T3.lgN; omega)
  have h1 : D ^ (2 * ν) ≤ 2 ^ ((L + 1) * (2 * ν)) :=
    (Nat.pow_le_pow_left hDL.le _).trans_eq (pow_mul _ _ _).symm
  have h2 : 5 ^ ν ≤ 2 ^ (3 * ν) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
  have h3 : (L + 1) * (2 * ν) + 3 * ν ≤ 10 * (ν * L) := by nlinarith
  calc 3 * D ^ (2 * ν) * 5 ^ ν ≤ 3 * 2 ^ ((L + 1) * (2 * ν)) * 2 ^ (3 * ν) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 3 h1) h2
    _ = 2 ^ ((L + 1) * (2 * ν) + 3 * ν) * 3 := by rw [pow_add]; ring
    _ ≤ 2 ^ (10 * (ν * L)) * 3 := Nat.mul_le_mul_right 3 (Nat.pow_le_pow_right (by norm_num) h3)

/-- **The uniform degree package with `c₀ = 10`.** -/
theorem dPackage : Nonempty (T3.DPackage 10) := by
  refine ⟨{
    Ctx := RW.UR
    Np := RW.rankProcs
    keeps := procsP_keeps RW.layU_polyT RW.parU_polyT (tableProcD_poly RW.rdU_polyT)
    P_unary := LayP.P_unary RW.layU_polyT
    B_unary := LayP.B_unary RW.layU_polyT
    prep := prepD
    prep_poly := prepD_polyT
    nPr := nPrW
    nPr_poly := nPrW_polyT
    good := goodW
    good_poly := goodW_polyT
    q := 2 * AS + 6
    net := netD
    P := fun g _ G => RW.PR g (aOf G)
    B := fun _ _ G => RW.BR (aOf G)
    τ := fun g n G => RW.τR g n (DD G)
    S := fun g _ G => SD g G
    nu := fun g n _ => n / g + 1
    isNet := fun g {n} G inst hg h3 _ y _ hgood => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show IsNetwork RW.rankProcs (prepD (Printed.unary (g + 1), (y, aOf G))) (netD (g + 1) G y)
        (RW.PR (g + 1) (aOf G)) (RW.BR (aOf G)) (RW.τR (g + 1) (n + 1) (DD G)) (SD (g + 1) G)
      rw [netD_eq, DD_eq]
      exact isNet_D G hgood
    value := fun g {n} G inst hg h3 _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [sum_congr rfl fun y _ => by rw [netD_eq]]
      exact value_D G
    value_le := fun g {n} G inst hg h3 _ y _ _ => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [netD_eq]
      have hm : RW.mV (g + 1) G ≤ (n + 1) * (n + 1) := by have := mV_lt (g := g + 1) G; unfold RdN at this; omega
      refine (natAbs_value_lt (RW.crossV (g + 1) G) 0 _ hm).trans_le (Nat.pow_le_pow_right (by norm_num) (expo_le (by omega)))
    nPr_le := fun g {n} G hg => by
      unfold nPrW VB.nPrN RdN
      rw [aOf_len]
      calc (n * n + 1) ^ (g * g) ≤ ((n + 2) ^ 2) ^ (g * g) := Nat.pow_le_pow_left (by nlinarith) _
        _ = (n + 2) ^ (2 * (g * g)) := by rw [← pow_mul]
        _ ≤ (n + 2) ^ ((2 * AS + 6) * g ^ 2) := Nat.pow_le_pow_right (by omega) (by rw [sq]; nlinarith)
    nu_le := fun g {n} G _ hg _ _ => by
      have := Nat.mul_div_le n g
      rw [Nat.mul_add, mul_one]; omega
    U_le := fun g {n} G inst hg h3 _ y _ hgood => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [netD_eq]
      obtain ⟨-, hA, -⟩ := (goodW_iff G y).1 hgood
      have h := Crossing.U_netS_le (X := RW.crossV (g + 1) G) (r := 0) _ (VB.prof_symm _ _ y) hA
        (card_mV_le G)
      refine h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
    P_le := fun g {n} G _ hg _ _ => by
      rw [PR_eq]
      have h1 : 1 ≤ g ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h2 : 3 * g ^ 2 ≤ (2 * AS + 6) * g ^ 2 := Nat.mul_le_mul_right _ (by omega)
      have e : lgN n = T3.lgN n := rfl
      rw [e]
      omega
    B_le := fun g {n} G _ _ _ _ => by
      rw [BR_eq]
      have := expo_le (n := n) (g := g) (q := 2 * AS + 6) (by omega)
      nlinarith
    τ_le := fun g {n} G inst hg h3 _ => by
      rw [DD_eq]
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hD : max 2 G.maxDegree ≤ n + 1 := max_le (by omega) ((maxDegree_le G).trans (by omega))
      refine (τR_le hD).trans (Nat.mul_le_mul_left _ ?_)
      have := expo_le (n := n + 1) (g := g) (q := 2 * AS + 6) (by omega)
      have : 1 ≤ (n + 1) * (n + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
    S_le := fun g {n} G inst hg h3 _ y _ hgood => by
      obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h1 := size_prepD_le G hgood
      have h2 : AS * (n + 1 + (g + 1) + 2) ^ AS ≤ AS * (n + 1 + (g + 1) + 2) ^ (2 * AS + 6) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      show AS * (n + 1 + (g + 1) + 2) ^ AS + _ ≤ _
      have h3 : (2 * AS + 6) * (n + 1 + (g + 1) + 2) ^ (2 * AS + 6) =
          AS * (n + 1 + (g + 1) + 2) ^ (2 * AS + 6) + AS * (n + 1 + (g + 1) + 2) ^ (2 * AS + 6) +
            6 * (n + 1 + (g + 1) + 2) ^ (2 * AS + 6) := by ring
      omega }⟩

end Package

end DPkg

/-- **The hypothesis of Theorem 3 holds**: a uniform degree package with `c₀ = 10`. -/
theorem exists_dPackage : ∃ c₀ : ℕ, Nonempty (T3.DPackage c₀) := ⟨10, DPkg.dPackage⟩

open EthFollowup.Hamiltonian in
/-- **Theorem 3 (thm:main-degree), Turing-machine level, unconditional.** ONE Turing machine of Mathlib
with finite alphabets and ONE constant `C` such that, on the code of every graph `G` with `n` vertices
and `m` edges, the machine halts within `⌊C · 2^{C·n·log₂(2m/n + 2)/√(log₂(n+2))}⌋` steps with
`#HC(G)` in binary. (`2m/n = d̄` is the average degree; for minimum degree `≥ 2`,
`log₂(d̄ + 2) ≤ log₂(2e·d̄)`, which is the bound `2^{O(n log(2e·d̄)/√log n)}` of the paper.) -/
theorem theorem3 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n * Real.logb 2 (2 * (G.edgeFinset.card : ℝ) / n + 2) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ :=
  theorem3_TM_of_package exists_dPackage

open EthFollowup.Hamiltonian in
/-- **Theorem 3, maximum-degree form, unconditional**: `⌊C · 2^{C·n·log₂(Δ + 2)/√(log₂(n+2))}⌋`. -/
theorem theorem3_maxdeg :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n * Real.logb 2 ((G.maxDegree : ℝ) + 2) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ :=
  theorem3_maxdeg_TM_of_package exists_dPackage

end EthFollowup.ExactHC
