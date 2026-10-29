/-
# The word-level procedures of the rank-encoded HC network (workstream A, file 4b)

The concrete procedures for the rank-encoded network `N_s` of `research/hc-degree-theorem.md`
(Definition 2.2) of a graph, computed from the graph code (`GIn`, as read by `read1`) and the
profile matrix: the analogue of `Package.lean`'s `layW`/`rdW`/`parW` for

* the **vertex-balanced partition** `VB.vertexBalanced` (Lemma 4.1; word level `bV a v = vbN n g v`),
* the crossing order `crossV g G` (crossing pairs `(u, v)`, `u ~ v`, `β u < β v`, lexicographic),
  root `0`, label system `X := (crossV g G).hcSystem 0`,
* the **rank code** `X.rankPC s hs rfl` for a symmetric profile `s` with `s a b ≤ e_ab`.

The word-level functions take `g` as their first argument; the procedures read it from the context
in unary (uniform in `g`, as `UPackage.lean`): context `UR = List Unit × RIn`, `RIn = GIn × List (List ℕ)`
(`g` unary, the graph, the profile matrix), `cRk g G s = (unary g, (aOf G, profMat g s))`;
`profMatN g Rd y` computes the matrix of the profile number `y` (`profMatN_eq`, `profMatN_polyU`).

* `layU c = layR c.1.length c.2` (the layout: `P = PR`, `B = BR`, per pair the offset `offV`, the
  width `capV = cw(e,s) + 2s`, the rank-field width `cw(e,s)` and `C(e,s)`), `layU_polyT`,
  `layR_describes`/`layU_describes`;
* `rdU` (the reader of the degree-pruned table procedure: the label codes are read from the rank
  blocks with `Rank.rawCodes`), `rdU_polyT`, `rdR_desc : TDesc …`;
* `parU` (the copy bits `P_{cd}` via `parBit`), `parU_polyT`, `parSpecU`;
* `tSpecU` : `tableProcD rdU` computes the node tables within `τR = 3·D^{2ν}·5^ν` steps
  (`ν = (n+1)/g + 1`, `D ≥ 2` a degree bound), states `≤ SRU`;
* **`rank_given`**: `Given.IsGivenNetwork (Given.ofProcs rankProcs) Given.noTable (cRk g G s)
  (X.netP (X.rankPC s hs rfl)) (PR g (aOf G)) (BR (aOf G)) (τR g (n+1) D) (SRU g G s D + size (cRk g G s) + 2g + 4·PR + 8)`;
* **`state_boundU`**: that state bound is `≤ A·(n+g+2)^A` for an absolute `A` (if `s ≤ e`, `D ≤ n+2`).
-/
import EthFollowup.ExactHC.Package
import EthFollowup.ExactHC.UPackage
import EthFollowup.ExactHC.RankProcs
import EthFollowup.ExactHC.DegTableProc
import EthFollowup.ExactHC.VertexBalanced

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace RW

open Groundwork Groundwork.Prog GraphProblems Asm Pkg Finset

/-- The input of the procedures: the graph and the profile matrix. -/
abbrev RIn : Type := GIn × List (List ℕ)

/-! ## The word-level layout and readers -/

section Word

variable (g : ℕ)

/-- The blob of the vertex `v` (vertex-balanced partition). -/
def bV (a : GIn) (v : ℕ) : ℕ := VB.vbN a.1.length g v
/-- The crossing pairs `(u, v)`, `u ~ v`, `β u < β v`, in lexicographic order. -/
def cplV (a : GIn) : List (ℕ × ℕ) :=
  (pairsW a).filter fun p => adjW a p.1 p.2 && decide (bV g a p.1 < bV g a p.2)
def ceV (a : GIn) (k : ℕ) : ℕ × ℕ := (cplV g a).getD k (0, 0)
/-- The crossing edges at the blob `b`. -/
def incV (a : GIn) (b : ℕ) : List ℕ :=
  (List.range (cplV g a).length).filter fun k =>
    decide (bV g a (ceV g a k).1 = b ∨ bV g a (ceV g a k).2 = b)
def onPV (a : GIn) (b c k : ℕ) : Bool :=
  decide ((bV g a (ceV g a k).1 = b ∧ bV g a (ceV g a k).2 = c) ∨
    (bV g a (ceV g a k).1 = c ∧ bV g a (ceV g a k).2 = b))
/-- The crossing edges between the blobs `b` and `c`, in crossing order. -/
def itV (a : GIn) (b c : ℕ) : List ℕ := (List.range (cplV g a).length).filter (onPV g a b c)
/-- `e_bc`. -/
def eV (a : GIn) (b c : ℕ) : ℕ := (itV g a b c).length

/-- The profile entry of the pair `{b, c}` in a profile matrix. -/
def sV (sm : List (List ℕ)) (b c : ℕ) : ℕ := (sm.getD (min b c) []).getD (max b c) 0
/-- The profile entry, capped by `e_bc`. -/
def sB (q : RIn) (b c : ℕ) : ℕ := min (sV q.2 b c) (eV g q.1 b c)
/-- The width `cw(e, s) + 2s` of the block of `{b, c}`. -/
def capV (q : RIn) (b c : ℕ) : ℕ := Rank.cw (eV g q.1 b c) (sB g q b c) + 2 * sB g q b c
/-- The nodes other than `b`. -/
def othV (b : ℕ) : List ℕ := (List.range g).filter fun c => decide (c ≠ b)
/-- The offset of block `c` in a setting of `b`. -/
def offV (q : RIn) (b c : ℕ) : ℕ := (((othV g b).filter fun d => decide (d < c)).map (capV g q b)).sum
/-- The total width of the blocks of `b`. -/
def scV (q : RIn) (b : ℕ) : ℕ := ((othV g b).map (capV g q b)).sum

/-- `P = 10·(n/g + 1)·log₂(n+2) + 2g² + 1` (`RankNetwork.netS_is` with `ν = n/g + 1`). -/
def PR (a : GIn) : ℕ := 10 * ((a.1.length / g + 1) * Nat.log2 (a.1.length + 2)) + 2 * g ^ 2 + 1
/-- `B = 2n² + 1`. -/
def BR (a : GIn) : ℕ := 2 * (a.1.length * a.1.length) + 1

/-- **The layout** of the rank-encoded network, read from the graph and the profile matrix. -/
def layR (q : RIn) : LayP :=
  (((List.replicate (PR g q.1) (), List.replicate (BR q.1) ()), List.replicate g ()),
    ((List.range g).map fun b => (List.replicate (scV g q b) (), (nhTab g).getD b []),
      (List.range g).map fun b => (List.range g).map fun c =>
        (((offV g q b c, List.replicate (capV g q b c) ()),
          (Rank.cw (eV g q.1 b c) (sB g q b c), Nat.choose (eV g q.1 b c) (sB g q b c))),
          ((cpTab g).getD b []).getD c [])))

/-- Block `c` of a setting `z` of `b`. -/
def blkV (q : RIn) (b c : ℕ) (z : List Bool) : List Bool := (z.drop (offV g q b c)).take (capV g q b c)
/-- The other blob of the crossing edge `k` at `b`. -/
def othB (a : GIn) (b k : ℕ) : ℕ :=
  if bV g a (ceV g a k).1 = b then bV g a (ceV g a k).2 else bV g a (ceV g a k).1
/-- The code of the label of the crossing edge `k`, read from the rank block of a setting `z` of `b`. -/
def codeV (q : RIn) (b k : ℕ) (z : List Bool) : ℕ :=
  (Rank.rawCodes (eV g q.1 b (othB g q.1 b k)) (sB g q b (othB g q.1 b k)) 2
    (blkV g q b (othB g q.1 b k) z)).getD ((itV g q.1 b (othB g q.1 b k)).idxOf k) 0
/-- The crossing edge number `i` at `b`. -/
def kI (a : GIn) (b i : ℕ) : ℕ := (incV g a b).getD i 0

def ceR (q : RIn) (b : ℕ) (z : List Bool) (i : ℕ) : CE :=
  ((kI g q.1 b i, decide (bV g q.1 (ceV g q.1 (kI g q.1 b i)).1 = b)),
    ceV g q.1 (kI g q.1 b i),
    (bV g q.1 (ceV g q.1 (kI g q.1 b i)).1, bV g q.1 (ceV g q.1 (kI g q.1 b i)).2),
    codeV g q b (kI g q.1 b i) z)

/-- The crossing data at the blob `b`, with the label codes read from the setting `z`. -/
def clR (q : RIn) (b : ℕ) (z : List Bool) : List CE :=
  (List.range (incV g q.1 b).length).map (ceR g q b z)
def vaV (a : GIn) (b : ℕ) : List ℕ := (List.range a.1.length).filter fun v => decide (bV g a v = b)
def vrV (a : GIn) (b : ℕ) : List ℕ :=
  (List.range a.1.length).filter fun v => decide (bV g a v = b) && decide (v ≠ 0)
def esV (a : GIn) (b : ℕ) : List (ℕ × ℕ) :=
  (pairsW a).filter fun p =>
    decide (p.1 < p.2) && adjW a p.1 p.2 && decide (bV g a p.1 = b) && decide (bV g a p.2 = b)
def ylR (q : RIn) (b : ℕ) (z : List Bool) : List ((ℕ × ℕ) × Bool) :=
  ((hpTab g).getD b []).zip (z.drop (scV g q b))

/-- **The reader of the degree-pruned table procedure.** -/
def rdR (p : RIn × WQ) : TD :=
  ((0, p.2.1), (vaV g p.1.1 p.2.1, vrV g p.1.1 p.2.1), (esV g p.1.1 p.2.1, clR g p.1 p.2.1 p.2.2),
    ylR g p.1 p.2.1 p.2.2)

/-- **The parity procedure**: copy bit number `j` is `P_{cd}` (`(a, c, d)` its triple). -/
def parR (p : RIn × (ℕ × List Bool)) : Bool :=
  parBit (trAt g p.2.1).2.1 (trAt g p.2.1).2.2 (clR g p.1 (trAt g p.2.1).2.1 p.2.2)

/-- The profile matrix of a profile. -/
def profMat (s : Fin g → Fin g → ℕ) : List (List ℕ) :=
  (List.range g).map fun a => (List.range g).map fun b => if h : a < g ∧ b < g then s ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- The profile matrix of the profile number `y` (`VB.prof`). -/
def profMatN (Rd y : ℕ) : List (List ℕ) :=
  (List.range g).map fun a => (List.range g).map fun b => VB.profN Rd g y a b

theorem profMatN_eq (Rd y : ℕ) : profMatN g Rd y = profMat g (VB.prof Rd g y) := by
  unfold profMatN profMat
  refine List.map_congr_left fun a ha => List.map_congr_left fun b hb => ?_
  rw [dif_pos ⟨List.mem_range.1 ha, List.mem_range.1 hb⟩]
  rfl

end Word

/-! ## Polynomial time -/

section Poly

variable (g : ℕ) {α : Type} [Enc α]

@[fun_prop] theorem bV_polyT {a : α → GIn} {v : α → ℕ} (ha : PolyT a) (hv : PolyT v) :
    PolyT fun x => bV g (a x) (v x) := by
  unfold bV VB.vbN
  exact PolyT.div (PolyT.mul hv (PolyT.const g)) (PolyT.length (PolyT.fst ha))

@[fun_prop] theorem cplV_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => cplV g (a x) := by
  unfold cplV; fun_prop

@[fun_prop] theorem ceV_polyT {a : α → GIn} {k : α → ℕ} (ha : PolyT a) (hk : PolyT k) :
    PolyT fun x => ceV g (a x) (k x) := by
  unfold ceV; fun_prop

theorem rangeV_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => List.range (cplV g (a x)).length :=
  PolyT.range (Unary.of_length (by fun_prop))

@[fun_prop] theorem incV_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => incV g (a x) (b x) := by
  have := rangeV_polyT g ha; unfold incV; fun_prop

@[fun_prop] theorem onPV_polyT {a : α → GIn} {b c k : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c)
    (hk : PolyT k) : PolyT fun x => onPV g (a x) (b x) (c x) (k x) := by
  unfold onPV; fun_prop

@[fun_prop] theorem itV_polyT {a : α → GIn} {b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => itV g (a x) (b x) (c x) := by
  have := rangeV_polyT g ha; unfold itV; fun_prop

theorem eV_unary {a : α → GIn} {b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    Unary fun x => eV g (a x) (b x) (c x) := by
  unfold eV; exact Unary.of_length (itV_polyT g ha hb hc)

@[fun_prop] theorem sV_polyT {sm : α → List (List ℕ)} {b c : α → ℕ} (hs : PolyT sm) (hb : PolyT b)
    (hc : PolyT c) : PolyT fun x => sV (sm x) (b x) (c x) := by
  unfold sV; fun_prop

theorem sB_unary {q : α → RIn} {b c : α → ℕ} (hq : PolyT q) (hb : PolyT b) (hc : PolyT c) :
    Unary fun x => sB g (q x) (b x) (c x) := by
  have he := eV_unary g (a := fun x => (q x).1) (by fun_prop) hb hc
  have h1 : PolyT fun x => sV (q x).2 (b x) (c x) := by fun_prop
  unfold sB
  exact Unary.of_le he (PolyT.min' h1 he.poly) fun x => min_le_right _ _

theorem capV_unary {q : α → RIn} {b c : α → ℕ} (hq : PolyT q) (hb : PolyT b) (hc : PolyT c) :
    Unary fun x => capV g (q x) (b x) (c x) := by
  have he := eV_unary g (a := fun x => (q x).1) (by fun_prop) hb hc
  have hs := sB_unary g hq hb hc
  unfold capV
  exact (Rank.cw_unary he hs.poly).add ((Unary.const 2).mul hs)

@[fun_prop] theorem capV_polyT {q : α → RIn} {b c : α → ℕ} (hq : PolyT q) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => capV g (q x) (b x) (c x) := (capV_unary g hq hb hc).poly

theorem othV_polyT {b : α → ℕ} (hb : PolyT b) : PolyT fun x => othV g (b x) := by
  have : PolyT fun _ : α => List.range g := PolyT.const _
  unfold othV; fun_prop

@[fun_prop] theorem offV_polyT {q : α → RIn} {b c : α → ℕ} (hq : PolyT q) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => offV g (q x) (b x) (c x) := by
  have := othV_polyT g hb
  have h : PolyT fun p : α × ℕ => capV g (q p.1) (b p.1) p.2 := capV_polyT g (by fun_prop) (by fun_prop) (by fun_prop)
  unfold offV; fun_prop

theorem length_itV_le (a : GIn) (b c : ℕ) : eV g a b c ≤ (cplV g a).length := by
  unfold eV itV
  exact (List.length_filter_le _ _).trans (by simp)

theorem capV_le (q : RIn) (b c : ℕ) : capV g q b c ≤ 3 * (cplV g q.1).length := by
  have h1 := Rank.cw_le (eV g q.1 b c) (sB g q b c)
  have h2 : sB g q b c ≤ eV g q.1 b c := min_le_right _ _
  have h3 := length_itV_le g q.1 b c
  unfold capV; omega

theorem scV_le (q : RIn) (b : ℕ) : scV g q b ≤ g * (3 * (cplV g q.1).length) := by
  unfold scV
  have h := List.sum_le_card_nsmul ((othV g b).map (capV g q b)) (3 * (cplV g q.1).length) (by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact capV_le g q b c)
  have hl : ((othV g b).map (capV g q b)).length ≤ g := by
    rw [List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
  simp only [smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right _ hl)

theorem scV_unary {q : α → RIn} {b : α → ℕ} (hq : PolyT q) (hb : PolyT b) :
    Unary fun x => scV g (q x) (b x) := by
  have := othV_polyT g hb
  have h : PolyT fun p : α × ℕ => capV g (q p.1) (b p.1) p.2 := capV_polyT g (by fun_prop) (by fun_prop) (by fun_prop)
  have hp : PolyT fun x => scV g (q x) (b x) := by unfold scV; fun_prop
  exact Unary.of_le ((Unary.const g).mul ((Unary.const 3).mul
    (Unary.of_length (cplV_polyT g (a := fun x => (q x).1) (by fun_prop))))) hp fun x => scV_le g (q x) (b x)

theorem PR_unary : Unary (PR g) := by
  have hn : Unary fun a : GIn => a.1.length := Unary.of_length (w := fun a : GIn => a.1) (by fun_prop)
  have hl : PolyT fun a : GIn => a.1.length := PolyT.length (PolyT.fst PolyT.id')
  have hp : PolyT (PR g) := by
    unfold PR
    exact PolyT.add (PolyT.add (PolyT.mul (PolyT.const 10) (PolyT.mul (PolyT.add (PolyT.div hl (PolyT.const g))
      (PolyT.const 1)) (PolyT.log2' (PolyT.add hl (PolyT.const 2))))) (PolyT.const _)) (PolyT.const 1)
  refine Unary.of_le (((Unary.const 10).mul ((hn.add (Unary.const 1)).mul (hn.add (Unary.const 2)))).add
    (Unary.const (2 * g ^ 2 + 1))) hp fun a => ?_
  unfold PR
  have h1 : a.1.length / g ≤ a.1.length := Nat.div_le_self _ _
  have h2 : Nat.log2 (a.1.length + 2) ≤ a.1.length + 2 := Nat.log2_le_self _
  have := Nat.mul_le_mul (Nat.add_le_add_right h1 1) h2
  omega

theorem BR_unary : Unary BR := by
  have hn : Unary fun a : GIn => a.1.length := Unary.of_length (w := fun a : GIn => a.1) (by fun_prop)
  unfold BR
  exact ((Unary.const 2).mul (hn.mul hn)).add (Unary.const 1)

theorem layR_polyT : PolyT (layR g) := by
  have hP : PolyT fun q : RIn => List.replicate (PR g q.1) () := (PR_unary g).comp (by fun_prop)
  have hB : PolyT fun q : RIn => List.replicate (BR q.1) () := BR_unary.comp (by fun_prop)
  have hr : PolyT fun _ : RIn => List.range g := PolyT.const _
  have hr2 : PolyT fun _ : RIn × ℕ => List.range g := PolyT.const _
  have hsc : PolyT fun p : RIn × ℕ => List.replicate (scV g p.1 p.2) () :=
    scV_unary g (q := fun p : RIn × ℕ => p.1) (by fun_prop) (by fun_prop)
  have hcap : PolyT fun p : (RIn × ℕ) × ℕ => List.replicate (capV g p.1.1 p.1.2 p.2) () :=
    capV_unary g (q := fun p : (RIn × ℕ) × ℕ => p.1.1) (by fun_prop) (by fun_prop) (by fun_prop)
  have hcw : PolyT fun p : (RIn × ℕ) × ℕ => Rank.cw (eV g p.1.1.1 p.1.2 p.2) (sB g p.1.1 p.1.2 p.2) :=
    Rank.cw_polyT (eV_unary g (a := fun p : (RIn × ℕ) × ℕ => p.1.1.1) (by fun_prop) (by fun_prop) (by fun_prop))
      (sB_unary g (q := fun p : (RIn × ℕ) × ℕ => p.1.1) (by fun_prop) (by fun_prop) (by fun_prop)).poly
  have hch : PolyT fun p : (RIn × ℕ) × ℕ => Nat.choose (eV g p.1.1.1 p.1.2 p.2) (sB g p.1.1 p.1.2 p.2) :=
    Rank.choose_polyT (eV_unary g (a := fun p : (RIn × ℕ) × ℕ => p.1.1.1) (by fun_prop) (by fun_prop) (by fun_prop))
      (sB_unary g (q := fun p : (RIn × ℕ) × ℕ => p.1.1) (by fun_prop) (by fun_prop) (by fun_prop)).poly
  have hoff : PolyT fun p : (RIn × ℕ) × ℕ => offV g p.1.1 p.1.2 p.2 := by fun_prop
  unfold layR; fun_prop

@[fun_prop] theorem blkV_polyT {q : α → RIn} {b c : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hc : PolyT c) (hz : PolyT z) : PolyT fun x => blkV g (q x) (b x) (c x) (z x) := by
  unfold blkV; fun_prop

@[fun_prop] theorem othB_polyT {a : α → GIn} {b k : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hk : PolyT k) :
    PolyT fun x => othB g (a x) (b x) (k x) := by
  unfold othB; fun_prop

@[fun_prop] theorem codeV_polyT {q : α → RIn} {b k : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hk : PolyT k) (hz : PolyT z) : PolyT fun x => codeV g (q x) (b x) (k x) (z x) := by
  have ho : PolyT fun x => othB g (q x).1 (b x) (k x) := by fun_prop
  have he := eV_unary g (a := fun x => (q x).1) (by fun_prop) hb ho
  have hs := (sB_unary g hq hb ho).poly
  have hr := Rank.rawCodes_polyT 2 he hs (blkV_polyT g hq hb ho hz)
  unfold codeV; fun_prop

@[fun_prop] theorem kI_polyT {a : α → GIn} {b i : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hi : PolyT i) :
    PolyT fun x => kI g (a x) (b x) (i x) := by
  unfold kI; fun_prop

@[fun_prop] theorem ceR_polyT {q : α → RIn} {b : α → ℕ} {z : α → List Bool} {i : α → ℕ} (hq : PolyT q)
    (hb : PolyT b) (hz : PolyT z) (hi : PolyT i) : PolyT fun x => ceR g (q x) (b x) (z x) (i x) := by
  unfold ceR; fun_prop

@[fun_prop] theorem clR_polyT {q : α → RIn} {b : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hz : PolyT z) : PolyT fun x => clR g (q x) (b x) (z x) := by
  have : PolyT fun x => List.range (incV g (q x).1 (b x)).length := PolyT.range (Unary.of_length (by fun_prop))
  unfold clR; fun_prop

@[fun_prop] theorem vaV_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vaV g (a x) (b x) := by
  have := range_polyT ha; unfold vaV; fun_prop

@[fun_prop] theorem vrV_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vrV g (a x) (b x) := by
  have := range_polyT ha; unfold vrV; fun_prop

@[fun_prop] theorem esV_polyT {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => esV g (a x) (b x) := by
  unfold esV; fun_prop

@[fun_prop] theorem ylR_polyT {q : α → RIn} {b : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hz : PolyT z) : PolyT fun x => ylR g (q x) (b x) (z x) := by
  have := (scV_unary g hq hb).poly
  unfold ylR
  exact PolyT.zip (PolyT.getD (PolyT.const _) hb (PolyT.const _)) (PolyT.drop this hz)

theorem rdR_polyT : PolyT (rdR g) := by
  unfold rdR; fun_prop

theorem parR_polyT : PolyT (parR g) := by
  have h : PolyT fun q : RIn × (ℕ × List Bool) =>
      (((trAt g q.2.1).2.1, (trAt g q.2.1).2.2), clR g q.1 (trAt g q.2.1).2.1 q.2.2) := by fun_prop
  exact (PolyT.comp parBit_polyT h).congr fun q => rfl

theorem profMatN_polyT {Rd y : α → ℕ} (hR : PolyT Rd) (hy : PolyT y) :
    PolyT fun x => profMatN g (Rd x) (y x) := by
  have : PolyT fun _ : α => List.range g := PolyT.const _
  have : PolyT fun _ : α × ℕ => List.range g := PolyT.const _
  unfold profMatN; fun_prop

end Poly

/-! ## The graph side: partition, crossing order, label system -/

noncomputable section Graph

variable {g : ℕ} [NeZero g]

theorem mem_cplV {a : GIn} {p : ℕ × ℕ} : p ∈ cplV g a ↔
    (p.1 < a.1.length ∧ p.2 < a.1.length) ∧ adjW a p.1 p.2 = true ∧ bV g a p.1 < bV g a p.2 := by
  simp [cplV, mem_pairsW]

theorem cplV_nodup (a : GIn) : (cplV g a).Nodup := (pairsW_nodup a).filter _

variable {n : ℕ} (G : SimpleGraph (Fin n))

theorem bV_aOf (v : ℕ) : bV g (aOf G) v = VB.vbN n g v := by simp [bV, aOf_len]

theorem vb_valN (v : Fin n) : (VB.vertexBalanced n g v).val = VB.vbN n g v.val := rfl

theorem vb_val (v : Fin n) : (VB.vertexBalanced n g v).val = bV g (aOf G) v.val := by
  rw [bV_aOf]; rfl

variable (g) in
abbrev mV : ℕ := (cplV g (aOf G)).length

variable (g) in
def sVt (k : Fin (mV g G)) : Fin n :=
  ⟨((cplV g (aOf G))[k.val]).1, by
    have := (mem_cplV.1 (List.getElem_mem k.isLt)).1.1; simpa using this⟩

variable (g) in
def tVt (k : Fin (mV g G)) : Fin n :=
  ⟨((cplV g (aOf G))[k.val]).2, by
    have := (mem_cplV.1 (List.getElem_mem k.isLt)).1.2; simpa using this⟩

theorem ceV_eq (k : Fin (mV g G)) : ceV g (aOf G) k.val = ((sVt g G k).val, (tVt g G k).val) := by
  simp [ceV, sVt, tVt, List.getD_eq_getElem?_getD, k.isLt]

variable (g) in
/-- **The crossing order** for the vertex-balanced partition: the crossing pairs in lexicographic
order. -/
def crossV : Crossing G (VB.vertexBalanced n g) (mV g G) where
  s := sVt g G
  t := tVt g G
  lt k := by
    have h := (mem_cplV.1 (List.getElem_mem k.isLt)).2.2
    rw [Fin.lt_def, vb_val, vb_val]; exact h
  adj k := by
    have h := (mem_cplV.1 (List.getElem_mem k.isLt)).2.1
    exact (adjW_aOf G _ _).1 h
  inj k l h1 h2 := by
    have e := (cplV_nodup (g := g) (aOf G)).getElem_inj_iff.1
      (Prod.ext (congrArg Fin.val h1) (congrArg Fin.val h2))
    exact Fin.ext e
  exhaust u v huv hlt := by
    have hm : (u.val, v.val) ∈ cplV g (aOf G) := by
      rw [Fin.lt_def, vb_val, vb_val] at hlt
      exact mem_cplV.2 ⟨by simp, (adjW_aOf G u.2 v.2).2 huv, hlt⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
    exact ⟨⟨i, hi⟩, Fin.ext (by simp [sVt, he]), Fin.ext (by simp [tVt, he])⟩

@[simp] theorem crossV_s (k : Fin (mV g G)) : (crossV g G).s k = sVt g G k := rfl
@[simp] theorem crossV_t (k : Fin (mV g G)) : (crossV g G).t k = tVt g G k := rfl

section Sys

variable [DecidableRel G.Adj] (r : Fin n)

@[simp] theorem hcV_lo (k : Fin (mV g G)) :
    ((crossV g G).hcSystem r).lo k = VB.vertexBalanced n g (sVt g G k) := rfl
@[simp] theorem hcV_hi (k : Fin (mV g G)) :
    ((crossV g G).hcSystem r).hi k = VB.vertexBalanced n g (tVt g G k) := rfl
@[simp] theorem hcV_holder (j : CopyIdx g) : ((crossV g G).hcSystem r).holder j = j.1.1 := rfl
@[simp] theorem hcV_source (j : CopyIdx g) : ((crossV g G).hcSystem r).source j = j.1.2.1 := rfl
@[simp] theorem hcV_kord : ((crossV g G).hcSystem r).kord = List.finRange (mV g G) := rfl
@[simp] theorem hcV_rord : ((crossV g G).hcSystem r).rord = copyList g := rfl
@[simp] theorem hcV_dflt : ((crossV g G).hcSystem r).dflt = Label.N := rfl

theorem incList_valV (a : Fin g) :
    (((crossV g G).hcSystem r).incList a).map Fin.val = incV g (aOf G) a.val := by
  unfold LabelSystem.incList incV
  rw [hcV_kord]
  refine map_val_filter_finRange _ _ fun k => ?_
  simp only [LabelSystem.Inc, hcV_lo, hcV_hi, ceV_eq, Fin.ext_iff, vb_valN, bV_aOf]

theorem length_incV (a : Fin g) :
    (incV g (aOf G) a.val).length = (((crossV g G).hcSystem r).incList a).length := by
  rw [← incList_valV G r a, List.length_map]

theorem pairItems_valV (a b : Fin g) :
    (((crossV g G).hcSystem r).pairItems a b).map Fin.val = itV g (aOf G) a.val b.val := by
  unfold LabelSystem.pairItems itV
  rw [hcV_kord]
  refine map_val_filter_finRange _ _ fun k => ?_
  simp only [onPV, LabelSystem.OnPair, hcV_lo, hcV_hi, ceV_eq, Fin.ext_iff, vb_valN, bV_aOf]

theorem eV_eq (a b : Fin g) : eV g (aOf G) a.val b.val = (((crossV g G).hcSystem r).pairItems a b).length := by
  rw [eV, ← pairItems_valV G r a b, List.length_map]

theorem heldList_eqV (a : Fin g) : ((crossV g G).hcSystem r).heldList a = heldF g a := rfl

theorem copyData_eqV (a b : Fin g) : LabelSystem.copyData ((crossV g G).hcSystem r) a b = copyPairF g a b := by
  unfold LabelSystem.copyData LabelSystem.pairCopies copyPairF
  simp only [hcV_rord, hcV_holder, hcV_source, LabelSystem.CopyOn, heldList_eqV]
  congr

theorem sort_deltaV (a : Fin g) :
    ((crossV g G).chords.delta a).sort (· ≤ ·) = ((crossV g G).hcSystem r).incList a := by
  rw [sort_eq_filter]
  unfold LabelSystem.incList
  refine List.filter_congr fun k _ => ?_
  simp only [Crossing.mem_delta, decide_eq_decide]
  rfl

end Sys

end Graph

/-! ## The layout described -/

noncomputable section Describe

variable {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n)

theorem othV_eq (a : Fin g) : othV g a.val = (othersL g a).map Fin.val := by
  unfold othV othersL
  refine (map_val_filter_finRange _ _ fun k => ?_).symm
  simp [Fin.ext_iff]

variable {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a)
include hs


theorem sV_profMat (a b : Fin g) : sV (profMat g s) a.val b.val = s a b := by
  have hmin : min a.val b.val < g := lt_of_le_of_lt (min_le_left _ _) a.2
  have hmax : max a.val b.val < g := max_lt a.2 b.2
  unfold sV profMat
  rw [getD_map_range _ hmin, getD_map_range _ hmax, dif_pos ⟨hmin, hmax⟩]
  rcases le_total a b with h | h
  · have h' : a.val ≤ b.val := h
    congr 1
    · exact Fin.ext (min_eq_left h')
    · exact Fin.ext (max_eq_right h')
  · have h' : b.val ≤ a.val := h
    rw [hs a b]
    congr 1
    · exact Fin.ext (min_eq_right h')
    · exact Fin.ext (max_eq_left h')

variable (hB : ∀ a b, s a b ≤ (((crossV g G).hcSystem r).pairItems a b).length)
include hB

theorem sB_eq (a b : Fin g) : sB g (aOf G, profMat g s) a.val b.val = s a b := by
  unfold sB
  rw [sV_profMat hs, eV_eq G r]
  exact min_eq_left (hB a b)

theorem capV_eq (a b : Fin g) :
    capV g (aOf G, profMat g s) a.val b.val = (((crossV g G).hcSystem r).rankPC s hs rfl).cap a b := by
  change _ = Rank.cw (((crossV g G).hcSystem r).pairItems a b).length (s a b) + 2 * s a b
  unfold capV
  rw [sB_eq G r hs hB, eV_eq G r]

theorem offV_eq (a b : Fin g) :
    offV g (aOf G, profMat g s) a.val b.val = (((crossV g G).hcSystem r).rankPC s hs rfl).offP a b := by
  unfold offV LabelSystem.PairCode.offP
  rw [othV_eq, List.filter_map, List.map_map]
  congr 1
  have e : ((othersL g a).filter ((fun d => decide (d < b.val)) ∘ Fin.val)) =
      (othersL g a).filter fun c => decide (c < b) := List.filter_congr fun c _ => by
    rw [Bool.eq_iff_iff]; simp only [Function.comp_apply, decide_eq_true_eq]; exact Iff.rfl
  rw [e]
  exact List.map_congr_left fun c _ => capV_eq G r hs hB a c

theorem scV_eq (a : Fin g) :
    scV g (aOf G, profMat g s) a.val = (((crossV g G).hcSystem r).rankPC s hs rfl).sumCap a := by
  unfold scV LabelSystem.PairCode.sumCap
  rw [othV_eq, List.map_map]
  congr 1
  exact List.map_congr_left fun c _ => capV_eq G r hs hB a c

/-- **The layout** describes the rank-encoded network. -/
theorem layR_describes :
    LabelSystem.DescribesP (((crossV g G).hcSystem r).rankPC s hs rfl) (PR g (aOf G)) (BR (aOf G))
      (layR g (aOf G, profMat g s)) where
  P_eq := by simp [LayP.P, layR]
  B_eq := by simp [LayP.B, layR]
  g_eq := by simp [LayP.g, layR]
  sc_eq a := by
    unfold LayP.sc LayP.node layR
    rw [getD_map_range _ a.2]
    simp [scV_eq G r hs hB a]
  nh_eq a := by
    unfold LayP.nh LayP.node layR nhTab
    rw [getD_map_range _ a.2, getD_map_range _ a.2]
    simp [nhN, a.2, heldList_eqV]
  off_eq a b _ := by
    unfold LayP.off LayP.pair layR
    rw [getD_map_range _ a.2, getD_map_range _ b.2]
    exact offV_eq G r hs hB a b
  wd_eq a b _ := by
    unfold LayP.wd LayP.pair layR
    rw [getD_map_range _ a.2, getD_map_range _ b.2]
    simp [capV_eq G r hs hB a b]
  cps_eq a b _ := by
    unfold LayP.cps LayP.pair layR cpTab
    rw [getD_map_range _ a.2, getD_map_range _ b.2, getD_map_range _ a.2, getD_map_range _ b.2]
    simp [cpN, a.2, b.2, copyData_eqV]
  valid a b _ w := by
    have hrw : LayP.rw (layR g (aOf G, profMat g s)) a.val b.val =
        LabelSystem.rankRw ((crossV g G).hcSystem r) s a b := by
      unfold LayP.rw LayP.pair layR
      rw [getD_map_range _ a.2, getD_map_range _ b.2]
      simp only [LabelSystem.rankRw, sB_eq G r hs hB, eV_eq G r]
    have hnr : LayP.nr (layR g (aOf G, profMat g s)) a.val b.val =
        LabelSystem.rankNr ((crossV g G).hcSystem r) s a b := by
      unfold LayP.nr LayP.pair layR
      rw [getD_map_range _ a.2, getD_map_range _ b.2]
      simp only [LabelSystem.rankNr, sB_eq G r hs hB, eV_eq G r]
    rw [hrw, hnr]
    exact LabelSystem.rank_valid a b w

end Describe

/-! ## The data of the table procedure and of the parity procedure -/

noncomputable section Read

variable {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]

/-- The internal edges of the blob `a`, as ordered pairs `u < v`. -/
def esFV (a : Fin g) : List (Fin (n + 1) × Fin (n + 1)) :=
  ((List.finRange (n + 1)) ×ˢ (List.finRange (n + 1))).filter fun p =>
    decide (p.1 < p.2) && decide (G.Adj p.1 p.2) && decide (VB.vertexBalanced (n + 1) g p.1 = a) &&
      decide (VB.vertexBalanced (n + 1) g p.2 = a)

theorem esFV_val (a : Fin g) : (esFV G a).map valP = esV g (aOf G) a.val := by
  unfold esFV esV pairsW
  rw [aOf_len, ← List.map_coe_finRange_eq_range, product_map, List.filter_map]
  have e : (Prod.map Fin.val Fin.val : Fin (n + 1) × Fin (n + 1) → ℕ × ℕ) = valP := by
    funext p; rfl
  rw [e]
  congr 1
  refine List.filter_congr fun p _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  simp only [valP, adjW_aOf G p.1.2 p.2.2, Fin.lt_def, Fin.ext_iff, vb_valN, bV_aOf]

theorem esFV_nodup (a : Fin g) : ((esFV G a).map symP).Nodup := by
  refine List.Nodup.map_on ?_ (((List.nodup_finRange _).product (List.nodup_finRange _)).filter _)
  intro p hp q hq h
  simp only [esFV, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  simp only [symP, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · have h3 : p.1 < p.2 := hp.2.1.1.1
    have h4 : q.1 < q.2 := hq.2.1.1.1
    rw [h1, h2] at h3
    exact absurd (h3.trans h4) (lt_irrefl _)

theorem mem_esFV (a : Fin g) (e : Sym2 (Fin (n + 1))) :
    e ∈ (esFV G a).map symP ↔ e ∈ Crossing.Eint G (VB.vertexBalanced (n + 1) g) a := by
  rw [Crossing.mem_Eint, List.mem_map]
  induction e using Sym2.ind with
  | _ u v =>
    constructor
    · rintro ⟨p, hp, he⟩
      simp only [esFV, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
      rw [← he]
      refine ⟨by simpa [symP] using hp.2.1.1.2, fun w hw => ?_⟩
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact hp.2.1.2
      · exact hp.2.2
    · rintro ⟨he, hb⟩
      have hadj : G.Adj u v := by simpa using he
      have hu := hb u (Sym2.mem_mk_left u v)
      have hv := hb v (Sym2.mem_mk_right u v)
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
      · exact ⟨(u, v), by simp [esFV, List.mem_finRange, h, hadj, hu, hv], rfl⟩
      · exact ⟨(v, u), by simp [esFV, List.mem_finRange, h, hadj.symm, hu, hv], Sym2.eq_swap⟩

theorem labNum_eq_code (l : Label) : Rank.labNum l = l.code := by cases l <;> rfl

theorem othB_eq (a : Fin g) (k : Fin (mV g G)) :
    othB g (aOf G) a.val k.val = (((crossV g G).hcSystem 0).other a k).val := by
  unfold othB LabelSystem.other
  simp only [ceV_eq, hcV_lo, hcV_hi, bV_aOf]
  split_ifs with h1 h2 h2 <;> simp_all [Fin.ext_iff, vb_valN]

variable {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a)
  (hB : ∀ a b, s a b ≤ (((crossV g G).hcSystem 0).pairItems a b).length)
include hs hB

/-- **The crossing data at `a`, read from a setting**, with the label codes decoded from the rank
blocks. -/
theorem clR_eq (a : Fin g) {x : (Fin (mV g G) → Label) × (CopyIdx g → Bool)}
    (hx : x ∈ (((crossV g G).hcSystem 0).rankPC s hs rfl).locSetP a) :
    clR g (aOf G, profMat g s) a.val ((((crossV g G).hcSystem 0).rankPC s hs rfl).encP a x) =
      (((crossV g G).chords.delta a).sort (· ≤ ·)).map (ceOf (crossV g G) x.1 a) := by
  set X := (crossV g G).hcSystem 0
  set C := X.rankPC s hs rfl
  set z := C.encP a x
  have hz : z ∈ (X.netP C).S a := C.mem_SP.2 ⟨x, hx, rfl⟩
  rw [sort_deltaV G 0]
  set L := X.incList a with hL
  unfold clR
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, length_incV G 0 a, hL]
    rfl
  intro i h1 h2
  have hi : i < L.length := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  have e1 : kI g (aOf G) a.val i = (L[i]).val := by
    unfold kI
    rw [← incList_valV G 0 a, ← hL]
    simp [List.getD_eq_getElem?_getD, hi]
  have hk : X.Inc a L[i] := X.mem_incList.1 (List.getElem_mem hi)
  set k := L[i]
  set c := X.other a k
  have hc := othB_eq G a k
  have hcode : codeV g (aOf G, profMat g s) a.val k.val z = (x.1 k).code := by
    unfold codeV
    rw [hc]
    have hblk : blkV g (aOf G, profMat g s) a.val c.val z = C.blockAt a c z := by
      unfold blkV LabelSystem.PairCode.blockAt
      rw [offV_eq G 0 hs hB, capV_eq G 0 hs hB]
    have hidx : (itV g (aOf G) a.val c.val).idxOf k.val = (X.pairItems a c).idxOf k := by
      rw [← pairItems_valV G 0 a c]
      exact idxOf_map_of_injective Fin.val_injective k _
    rw [hblk, hidx, eV_eq G 0, sB_eq G 0 hs hB, ← LabelSystem.labNum_decLab hz hk, C.decLab_encP hx,
      labNum_eq_code]
  unfold ceR ceOf
  rw [e1, ceV_eq, hcode]
  simp [Fin.ext_iff, vb_valN, bV_aOf]

/-- **The reader produces the data of the node table** (`TDesc`). -/
theorem rdR_desc (a : Fin g) {x : (Fin (mV g G) → Label) × (CopyIdx g → Bool)}
    (hx : x ∈ (((crossV g G).hcSystem 0).rankPC s hs rfl).locSetP a) :
    TDesc G (crossV g G) 0 a x.1 (copyVec a x.2)
      (rdR g ((aOf G, profMat g s), (a.val, (((crossV g G).hcSystem 0).rankPC s hs rfl).encP a x))) where
  r_eq := rfl
  a_eq := rfl
  va := by
    refine ⟨(List.finRange (n + 1)).filter fun v => decide (VB.vertexBalanced (n + 1) g v = a), fun v => by
      simp [List.mem_finRange], ?_⟩
    simp only [rdR, vaV, aOf_len]
    exact (map_val_filter_finRange _ _ fun v => by simp [Fin.ext_iff, vb_valN, bV_aOf]).symm
  vr_eq := by
    simp only [rdR, vrV, aOf_len]
    rw [sort_eq_filter]
    refine (map_val_filter_finRange _ _ fun v => ?_).symm
    simp only [Finset.mem_erase, mem_blob, Fin.ext_iff, vb_valN, bV_aOf, Fin.val_zero, ne_eq]
    by_cases h1 : VB.vbN (n + 1) g v.val = a.val <;> by_cases h2 : v.val = 0 <;> simp [h1, h2]
  es := ⟨esFV G a, esFV_nodup G a, mem_esFV G a, (esFV_val G a).symm⟩
  cl_eq := clR_eq G hs hB a hx
  yl := by
    refine ⟨(heldF g a).map fun j => (j.1.2.1, j.1.2.2), ?_, ?_, ?_⟩
    · refine List.Nodup.map_on ?_ (heldF_nodup a)
      intro j hj j' hj' h
      rw [mem_heldF] at hj hj'
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (hj.trans hj'.symm) (Prod.ext h.1 h.2))
    · intro p
      simp only [List.mem_map, mem_heldF, Chords.Q, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rw [← hj]; exact j.2
      · intro h
        exact ⟨⟨(a, p.1, p.2), h⟩, rfl, rfl⟩
    · simp only [rdR, ylR, hpTab]
      rw [getD_map_range _ a.2]
      simp only [hpN, dif_pos a.2]
      have hz : ((((crossV g G).hcSystem 0).rankPC s hs rfl).encP a x).drop
          (scV g (aOf G, profMat g s) a.val) = (heldF g a).map x.2 := by
        rw [scV_eq G 0 hs hB, LabelSystem.PairCode.drop_sumCap_encP _ hx, heldList_eqV]
      rw [hz, List.zip_map', List.map_map]
      refine List.map_congr_left fun j hj => ?_
      have hja : j.1.1 = a := mem_heldF.1 hj
      have h : a < j.1.2.1 ∧ j.1.2.1 < j.1.2.2 := by rw [← hja]; exact j.2
      have e : (⟨(a, j.1.2.1, j.1.2.2), h⟩ : CopyIdx g) = j := Subtype.ext (Prod.ext hja.symm rfl)
      simp only [Function.comp_apply, copyVec, dif_pos h, e, Prod.mk.injEq, true_and]
      cases x.2 j <;> rfl

/-- **The parity procedure computes the copy bits.** -/
theorem parSpecR : LabelSystem.ParSpecP (((crossV g G).hcSystem 0).rankPC s hs rfl) (parR g)
    (aOf G, profMat g s) := by
  intro j x hx
  have hj := mem_copyList j
  simp only [parR, hcV_rord, trAt, trTab]
  rw [getD_map_idxOf (inst := instBEqOfDecidableEq) (tv g) hj]
  simp only [tv, hcV_source]
  rw [clR_eq G hs hB j.1.2.1 hx]
  show _ = zToBool ((crossV g G).chords.P (labelPar x.1) j.1.2.1 j.1.2.2)
  rw [P_eq_parBit]
  cases parBit _ _ _ <;> rfl

end Read

/-! ## A polynomial bound on the state bound -/

section Bound

theorem size_list_le {α : Type} [HasSize α] (k : ℕ) :
    ∀ L : List α, (∀ x ∈ L, size x ≤ k) → size L ≤ L.length * (k + 1) + 1
  | [], _ => by show 0 + 1 ≤ _; simp
  | a :: l, h => by
    have e : size (a :: l) = size a + 1 + size l := by
      show ((a :: l).map fun x => size x + 1).sum + 1 = size a + 1 + ((l.map fun x => size x + 1).sum + 1)
      rw [List.map_cons, List.sum_cons]; omega
    have h1 := h a List.mem_cons_self
    have h2 := size_list_le k l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [e, List.length_cons]
    nlinarith

theorem size_profMat_le (g : ℕ) {s : Fin g → Fin g → ℕ} {E : ℕ} (hE : ∀ a b, s a b ≤ E) :
    size (profMat g s) ≤ (g + 1) * ((g + 1) * (E + 2)) + 1 := by
  have hin : ∀ x ∈ profMat g s, size x ≤ g * (E + 2) + 1 := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    refine (size_list_le (E + 1) _ fun y hy => ?_).trans (by simp)
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
    split_ifs with h
    · have := hE ⟨a, h.1⟩ ⟨b, h.2⟩
      have := Nat.size_le.2 (lt_of_le_of_lt this Nat.lt_two_pow_self)
      change Nat.size _ + 1 ≤ _
      have := Nat.size_le_size (hE ⟨a, h.1⟩ ⟨b, h.2⟩)
      have := Nat.size_le.2 (Nat.lt_two_pow_self (n := E))
      omega
    · change Nat.size 0 + 1 ≤ _; simp
  refine (size_list_le _ _ hin).trans ?_
  simp only [profMat, List.length_map, List.length_range]
  nlinarith

end Bound

/-! ## Polynomial time, with `g` read from the input (uniform in `g`) -/

section PolyU

variable {α : Type} [Enc α] {u : α → List Unit} (hu : PolyT u)
include hu

theorem bV_polyU {a : α → GIn} {v : α → ℕ} (ha : PolyT a) (hv : PolyT v) :
    PolyT fun x => bV (u x).length (a x) (v x) := by
  unfold bV VB.vbN
  exact PolyT.div (PolyT.mul hv (PolyT.length hu)) (PolyT.length (PolyT.fst ha))

theorem cplV_polyU {a : α → GIn} (ha : PolyT a) : PolyT fun x => cplV (u x).length (a x) := by
  have := pairsW_polyT ha
  have h := bV_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.1) (by fun_prop) (by fun_prop)
  have h' := bV_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.2) (by fun_prop) (by fun_prop)
  unfold cplV; fun_prop

theorem ceV_polyU {a : α → GIn} {k : α → ℕ} (ha : PolyT a) (hk : PolyT k) :
    PolyT fun x => ceV (u x).length (a x) (k x) := by
  have := cplV_polyU hu ha
  unfold ceV; fun_prop

theorem incV_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => incV (u x).length (a x) (b x) := by
  have h0 : PolyT fun x => List.range (cplV (u x).length (a x)).length :=
    PolyT.range (Unary.of_length (cplV_polyU hu ha))
  have hc := ceV_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (k := fun p => p.2) (by fun_prop) (by fun_prop)
  have h1 := bV_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => (ceV (u p.1).length (a p.1) p.2).1) (by fun_prop) (by fun_prop)
  have h2 := bV_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => (ceV (u p.1).length (a p.1) p.2).2) (by fun_prop) (by fun_prop)
  unfold incV; fun_prop

theorem onPV_polyU {a : α → GIn} {b c k : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c)
    (hk : PolyT k) : PolyT fun x => onPV (u x).length (a x) (b x) (c x) (k x) := by
  have hc' := ceV_polyU hu ha hk
  have h1 := bV_polyU hu ha (v := fun x => (ceV (u x).length (a x) (k x)).1) (by fun_prop)
  have h2 := bV_polyU hu ha (v := fun x => (ceV (u x).length (a x) (k x)).2) (by fun_prop)
  unfold onPV; fun_prop

theorem itV_polyU {a : α → GIn} {b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => itV (u x).length (a x) (b x) (c x) := by
  have h0 : PolyT fun x => List.range (cplV (u x).length (a x)).length :=
    PolyT.range (Unary.of_length (cplV_polyU hu ha))
  have h1 := onPV_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (b := fun p => b p.1) (c := fun p => c p.1) (k := fun p => p.2) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)
  unfold itV; fun_prop

theorem eV_unaryU {a : α → GIn} {b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    Unary fun x => eV (u x).length (a x) (b x) (c x) := by
  unfold eV; exact Unary.of_length (itV_polyU hu ha hb hc)

theorem sB_unaryU {q : α → RIn} {b c : α → ℕ} (hq : PolyT q) (hb : PolyT b) (hc : PolyT c) :
    Unary fun x => sB (u x).length (q x) (b x) (c x) := by
  have he := eV_unaryU hu (a := fun x => (q x).1) (by fun_prop) hb hc
  have h1 : PolyT fun x => sV (q x).2 (b x) (c x) := by fun_prop
  unfold sB
  exact Unary.of_le he (PolyT.min' h1 he.poly) fun x => min_le_right _ _

theorem capV_unaryU {q : α → RIn} {b c : α → ℕ} (hq : PolyT q) (hb : PolyT b) (hc : PolyT c) :
    Unary fun x => capV (u x).length (q x) (b x) (c x) := by
  have he := eV_unaryU hu (a := fun x => (q x).1) (by fun_prop) hb hc
  have hs := sB_unaryU hu hq hb hc
  unfold capV
  exact (Rank.cw_unary he hs.poly).add ((Unary.const 2).mul hs)

theorem othV_polyU {b : α → ℕ} (hb : PolyT b) : PolyT fun x => othV (u x).length (b x) := by
  have := UPkg.rangeU hu
  unfold othV; fun_prop

theorem offV_polyU {q : α → RIn} {b c : α → ℕ} (hq : PolyT q) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => offV (u x).length (q x) (b x) (c x) := by
  have := othV_polyU hu hb
  have h : PolyT fun p : α × ℕ => capV (u p.1).length (q p.1) (b p.1) p.2 :=
    (capV_unaryU (u := fun p : α × ℕ => u p.1) (by fun_prop) (q := fun p => q p.1) (by fun_prop)
      (by fun_prop) (by fun_prop)).poly
  unfold offV; fun_prop

theorem scV_unaryU {q : α → RIn} {b : α → ℕ} (hq : PolyT q) (hb : PolyT b) :
    Unary fun x => scV (u x).length (q x) (b x) := by
  have := othV_polyU hu hb
  have h : PolyT fun p : α × ℕ => capV (u p.1).length (q p.1) (b p.1) p.2 :=
    (capV_unaryU (u := fun p : α × ℕ => u p.1) (by fun_prop) (q := fun p => q p.1) (by fun_prop)
      (by fun_prop) (by fun_prop)).poly
  have hp : PolyT fun x => scV (u x).length (q x) (b x) := by unfold scV; fun_prop
  exact Unary.of_le ((Unary.of_length hu).mul ((Unary.const 3).mul
    (Unary.of_length (cplV_polyU hu (a := fun x => (q x).1) (by fun_prop))))) hp
    fun x => scV_le (u x).length (q x) (b x)

theorem PR_unaryU {a : α → GIn} (ha : PolyT a) : Unary fun x => PR (u x).length (a x) := by
  have hn : Unary fun x => (a x).1.length := Unary.of_length (w := fun x => (a x).1) (by fun_prop)
  have hg : Unary fun x => (u x).length := Unary.of_length hu
  have hl : PolyT fun x => (a x).1.length := hn.poly
  have hp : PolyT fun x => PR (u x).length (a x) := by
    unfold PR
    exact PolyT.add (PolyT.add (PolyT.mul (PolyT.const 10) (PolyT.mul (PolyT.add (PolyT.div hl
      (PolyT.length hu)) (PolyT.const 1)) (PolyT.log2' (PolyT.add hl (PolyT.const 2)))))
      (PolyT.mul (PolyT.const 2) (PolyT.pow_const (PolyT.length hu) 2))) (PolyT.const 1)
  refine Unary.of_le ((((Unary.const 10).mul ((hn.add (Unary.const 1)).mul (hn.add (Unary.const 2)))).add
    ((Unary.const 2).mul (hg.mul hg))).add (Unary.const 1)) hp fun x => ?_
  unfold PR
  have h1 : (a x).1.length / (u x).length ≤ (a x).1.length := Nat.div_le_self _ _
  have h2 : Nat.log2 ((a x).1.length + 2) ≤ (a x).1.length + 2 := Nat.log2_le_self _
  have := Nat.mul_le_mul (Nat.add_le_add_right h1 1) h2
  rw [sq]
  omega

theorem blkV_polyU {q : α → RIn} {b c : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hc : PolyT c) (hz : PolyT z) : PolyT fun x => blkV (u x).length (q x) (b x) (c x) (z x) := by
  have h1 := offV_polyU hu hq hb hc
  have h2 := (capV_unaryU hu hq hb hc).poly
  unfold blkV; fun_prop

theorem othB_polyU {a : α → GIn} {b k : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hk : PolyT k) :
    PolyT fun x => othB (u x).length (a x) (b x) (k x) := by
  have hc := ceV_polyU hu ha hk
  have h1 := bV_polyU hu ha (v := fun x => (ceV (u x).length (a x) (k x)).1) (by fun_prop)
  have h2 := bV_polyU hu ha (v := fun x => (ceV (u x).length (a x) (k x)).2) (by fun_prop)
  unfold othB; fun_prop

theorem codeV_polyU {q : α → RIn} {b k : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hk : PolyT k) (hz : PolyT z) : PolyT fun x => codeV (u x).length (q x) (b x) (k x) (z x) := by
  have ho := othB_polyU hu (a := fun x => (q x).1) (by fun_prop) hb hk
  have he := eV_unaryU hu (a := fun x => (q x).1) (by fun_prop) hb ho
  have hs := (sB_unaryU hu hq hb ho).poly
  have hr := Rank.rawCodes_polyT 2 he hs (blkV_polyU hu hq hb ho hz)
  have hi := itV_polyU hu (a := fun x => (q x).1) (by fun_prop) hb ho
  unfold codeV; fun_prop

theorem kI_polyU {a : α → GIn} {b i : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hi : PolyT i) :
    PolyT fun x => kI (u x).length (a x) (b x) (i x) := by
  have := incV_polyU hu ha hb
  unfold kI; fun_prop

theorem ceR_polyU {q : α → RIn} {b : α → ℕ} {z : α → List Bool} {i : α → ℕ} (hq : PolyT q)
    (hb : PolyT b) (hz : PolyT z) (hi : PolyT i) : PolyT fun x => ceR (u x).length (q x) (b x) (z x) (i x) := by
  have hk := kI_polyU hu (a := fun x => (q x).1) (by fun_prop) hb hi
  have hc := ceV_polyU hu (a := fun x => (q x).1) (by fun_prop) hk
  have h1 := bV_polyU hu (a := fun x => (q x).1) (by fun_prop)
    (v := fun x => (ceV (u x).length (q x).1 (kI (u x).length (q x).1 (b x) (i x))).1) (by fun_prop)
  have h2 := bV_polyU hu (a := fun x => (q x).1) (by fun_prop)
    (v := fun x => (ceV (u x).length (q x).1 (kI (u x).length (q x).1 (b x) (i x))).2) (by fun_prop)
  have h3 := codeV_polyU hu hq hb hk hz
  unfold ceR; fun_prop

theorem clR_polyU {q : α → RIn} {b : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hz : PolyT z) : PolyT fun x => clR (u x).length (q x) (b x) (z x) := by
  have h0 : PolyT fun x => List.range (incV (u x).length (q x).1 (b x)).length :=
    PolyT.range (Unary.of_length (incV_polyU hu (a := fun x => (q x).1) (by fun_prop) hb))
  have h1 := ceR_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (q := fun p => q p.1)
    (b := fun p => b p.1) (z := fun p => z p.1) (i := fun p => p.2) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)
  unfold clR; fun_prop

theorem vaV_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vaV (u x).length (a x) (b x) := by
  have := range_polyT ha
  have h1 := bV_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2) (by fun_prop) (by fun_prop)
  unfold vaV; fun_prop

theorem vrV_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => vrV (u x).length (a x) (b x) := by
  have := range_polyT ha
  have h1 := bV_polyU (u := fun p : α × ℕ => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2) (by fun_prop) (by fun_prop)
  unfold vrV; fun_prop

theorem esV_polyU {a : α → GIn} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => esV (u x).length (a x) (b x) := by
  have := pairsW_polyT ha
  have h1 := bV_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.1) (by fun_prop) (by fun_prop)
  have h2 := bV_polyU (u := fun p : α × (ℕ × ℕ) => u p.1) (by fun_prop) (a := fun p => a p.1)
    (v := fun p => p.2.2) (by fun_prop) (by fun_prop)
  unfold esV; fun_prop

theorem ylR_polyU {q : α → RIn} {b : α → ℕ} {z : α → List Bool} (hq : PolyT q) (hb : PolyT b)
    (hz : PolyT z) : PolyT fun x => ylR (u x).length (q x) (b x) (z x) := by
  have := (scV_unaryU hu hq hb).poly
  unfold ylR
  exact PolyT.zip (PolyT.getD (UPkg.hpTab_polyT hu) hb (PolyT.const _)) (PolyT.drop this hz)

theorem profMatN_polyU {Rd y : α → ℕ} (hR : PolyT Rd) (hy : PolyT y) :
    PolyT fun x => profMatN (u x).length (Rd x) (y x) := by
  have h0 := UPkg.rangeU hu
  have h1 := UPkg.rangeU (u := fun p : α × ℕ => u p.1) (by fun_prop)
  have h2 : PolyT fun p : (α × ℕ) × ℕ => VB.profN (Rd p.1.1) (u p.1.1).length (y p.1.1) p.1.2 p.2 :=
    VB.profN_polyT (by fun_prop) (PolyT.length (by fun_prop)) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold profMatN; fun_prop

end PolyU

/-! ## The uniform procedures -/

section Readers

/-- The context: `g` in unary, the graph, the profile matrix. -/
abbrev UR : Type := List Unit × RIn

/-- The layout, with `g` read from the context. -/
def layU (c : UR) : LayP := layR c.1.length c.2
/-- The reader of the table procedure, with `g` read from the context. -/
def rdU (q : UR × WQ) : TD := rdR q.1.1.length (q.1.2, q.2)
/-- The parity procedure, with `g` read from the context. -/
def parU (q : UR × (ℕ × List Bool)) : Bool := parR q.1.1.length (q.1.2, q.2)

/-- **The procedures of the rank-encoded HC network** (one `Procs` for all `g`). -/
def rankProcs : Eight.SecNetworks.Procs UR := procsP layU parU (tableProcD rdU)

theorem layU_polyT : PolyT layU := by
  have hu : PolyT fun c : UR => c.1 := by fun_prop
  have hq : PolyT fun c : UR => c.2 := by fun_prop
  have hP : PolyT fun c : UR => List.replicate (PR c.1.length c.2.1) () :=
    PR_unaryU hu (a := fun c => c.2.1) (by fun_prop)
  have hB : PolyT fun c : UR => List.replicate (BR c.2.1) () := BR_unary.comp (by fun_prop)
  have hg : PolyT fun c : UR => List.replicate c.1.length () := Unary.of_length hu
  have hr := UPkg.rangeU hu
  have hr2 := UPkg.rangeU (u := fun p : UR × ℕ => p.1.1) (by fun_prop)
  have hsc : PolyT fun p : UR × ℕ => List.replicate (scV p.1.1.length p.1.2 p.2) () :=
    scV_unaryU (u := fun p : UR × ℕ => p.1.1) (by fun_prop) (q := fun p => p.1.2) (by fun_prop) (by fun_prop)
  have hnh := UPkg.nhTab_polyT (u := fun p : UR × ℕ => p.1.1) (by fun_prop)
  have hcp := UPkg.cpTab_polyT (u := fun p : (UR × ℕ) × ℕ => p.1.1.1) (by fun_prop)
  have hcap : PolyT fun p : (UR × ℕ) × ℕ => List.replicate (capV p.1.1.1.length p.1.1.2 p.1.2 p.2) () :=
    capV_unaryU (u := fun p : (UR × ℕ) × ℕ => p.1.1.1) (by fun_prop) (q := fun p => p.1.1.2) (by fun_prop)
      (by fun_prop) (by fun_prop)
  have he := eV_unaryU (u := fun p : (UR × ℕ) × ℕ => p.1.1.1) (by fun_prop) (a := fun p => p.1.1.2.1)
    (b := fun p => p.1.2) (c := fun p => p.2) (by fun_prop) (by fun_prop) (by fun_prop)
  have hs := (sB_unaryU (u := fun p : (UR × ℕ) × ℕ => p.1.1.1) (by fun_prop) (q := fun p => p.1.1.2)
    (b := fun p => p.1.2) (c := fun p => p.2) (by fun_prop) (by fun_prop) (by fun_prop)).poly
  have hcw := Rank.cw_polyT he hs
  have hch := Rank.choose_polyT he hs
  have hoff := offV_polyU (u := fun p : (UR × ℕ) × ℕ => p.1.1.1) (by fun_prop) (q := fun p => p.1.1.2)
    (b := fun p => p.1.2) (c := fun p => p.2) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold layU layR; fun_prop

theorem rdU_polyT : PolyT rdU := by
  have hu : PolyT fun q : UR × WQ => q.1.1 := by fun_prop
  have hq : PolyT fun q : UR × WQ => q.1.2 := by fun_prop
  have ha : PolyT fun q : UR × WQ => q.1.2.1 := by fun_prop
  have hb : PolyT fun q : UR × WQ => q.2.1 := by fun_prop
  have hz : PolyT fun q : UR × WQ => q.2.2 := by fun_prop
  have h1 := vaV_polyU hu ha hb
  have h2 := vrV_polyU hu ha hb
  have h3 := esV_polyU hu ha hb
  have h4 := clR_polyU hu hq hb hz
  have h5 := ylR_polyU hu hq hb hz
  unfold rdU rdR; fun_prop

theorem parU_polyT : PolyT parU := by
  have hu : PolyT fun q : UR × (ℕ × List Bool) => q.1.1 := by fun_prop
  have hj := UPkg.trAt_polyU hu (j := fun q => q.2.1) (by fun_prop)
  have hc := clR_polyU hu (q := fun q => q.1.2) (b := fun q => (trAt q.1.1.length q.2.1).2.1)
    (z := fun q => q.2.2) (by fun_prop) (by fun_prop) (by fun_prop)
  have h : PolyT fun q : UR × (ℕ × List Bool) =>
      (((trAt q.1.1.length q.2.1).2.1, (trAt q.1.1.length q.2.1).2.2),
        clR q.1.1.length q.1.2 (trAt q.1.1.length q.2.1).2.1 q.2.2) := by fun_prop
  exact (PolyT.comp parBit_polyT h).congr fun q => rfl

end Readers

/-! ## The specifications in the uniform context -/

section USpec

/-- The polynomial bound on the word of the data read by `rdU`. -/
noncomputable def cRU : ℕ := rdU_polyT.choose_spec.choose

theorem size_rdU (q : UR × WQ) : size (rdU q) ≤ cRU * (7 * size q + 1) ^ cRU := by
  refine (size_le_len_TD _).trans ((rdU_polyT.choose_spec.choose_spec.2 q).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)))
  have := Carried.le q
  omega

/-- The context of the graph `G`, for `g` nodes and the profile `s`. -/
noncomputable def cRk (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin g → Fin g → ℕ) : UR :=
  (Printed.unary g, (aOf G, profMat g s))

@[simp] theorem cRk_len (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin g → Fin g → ℕ) :
    (cRk g G s).1.length = g := by
  simp [cRk, Printed.unary]

theorem size_cRk (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin g → Fin g → ℕ) :
    size (cRk g G s) = (2 * g + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) + size (profMat g s) := by
  show size (Printed.unary g) + (size (aOf G) + size (profMat g s)) = _
  rw [size_units, size_aOf]; simp [Printed.unary]; omega

/-- The time bound `3·D^{2ν}·5^ν`, `ν = N/g + 1` (`N` vertices, `D` a degree bound). -/
def τR (g N D : ℕ) : ℕ := 3 * D ^ (2 * (N / g + 1)) * 5 ^ (N / g + 1)

theorem one_le_τR (g N D : ℕ) (hD : 1 ≤ D) : 1 ≤ τR g N D := by
  unfold τR
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.pow_pos hD)) (Nat.pow_pos (by norm_num))

/-- The state bound of the table procedure, uniform in `g`. -/
noncomputable def SRU (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin g → Fin g → ℕ) (D : ℕ) : ℕ :=
  3 * (cRU * (7 * (size (cRk g G s) + (g + 1) + (2 * PR g (aOf G) + 1)) + 1) ^ cRU) +
    8 * (n / g + 1) * (Nat.size D + 2) + 20

theorem parU_cRk (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin g → Fin g → ℕ)
    (p : ℕ × List Bool) : parU (cRk g G s, p) = parR g ((aOf G, profMat g s), p) := by
  unfold parU; rw [cRk_len]; rfl

variable {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
  {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a)
  (hB : ∀ a b, s a b ≤ (((crossV g G).hcSystem 0).pairItems a b).length)
include hs hB

theorem layU_describes :
    LabelSystem.DescribesP (((crossV g G).hcSystem 0).rankPC s hs rfl) (PR g (aOf G)) (BR (aOf G))
      (layU (cRk g G s)) := by
  have e : layU (cRk g G s) = layR g (aOf G, profMat g s) := by
    simp only [layU, cRk_len]; rfl
  rw [e]
  exact layR_describes G 0 hs hB

theorem parSpecU : LabelSystem.ParSpecP (((crossV g G).hcSystem 0).rankPC s hs rfl) parU (cRk g G s) := by
  intro j x hx
  rw [parU_cRk]
  exact parSpecR G hs hB j x hx

/-- **The degree-pruned table procedure computes the node tables** of the rank-encoded network
within `τR = 3·D^{2ν}·5^ν` steps (`ν = (n+1)/g + 1`), uniformly in `g`. -/
theorem tSpecU {D : ℕ} (hD2 : 2 ≤ D) (hdeg : ∀ v, G.degree v ≤ D)
    (hN : (((crossV g G).hcSystem 0).netP (((crossV g G).hcSystem 0).rankPC s hs rfl)).Is
      (PR g (aOf G)) (BR (aOf G))) :
    LabelSystem.TSpecP (((crossV g G).hcSystem 0).rankPC s hs rfl) (tableProcD rdU)
      (cRk g G s) (τR g (n + 1) D) (SRU g G s D) := by
  intro a x hx
  rw [Crossing.hcSystem_T]
  set C := ((crossV g G).hcSystem 0).rankPC s hs rfl
  have e : rdU (cRk g G s, (a.val, C.encP a x)) = rdR g ((aOf G, profMat g s), (a.val, C.encP a x)) := by
    simp only [rdU, cRk_len]; rfl
  have hD := rdR_desc G hs hB a hx
  rw [← e] at hD
  have h := tableProcD_runs G (crossV g G) rdU (cRk g G s, (a.val, C.encP a x)) 0 a x.1
    (copyVec a x.2) hD hD2 (fun v _ => hdeg v)
  have hν : (blob (VB.vertexBalanced (n + 1) g) a).card ≤ (n + 1) / g + 1 := VB.card_blob_vb_le (n + 1) g a
  refine h.mono ?_ ?_
  · unfold τR
    have hD1 : 0 < D := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right hD1 (by omega)))
      (Nat.pow_le_pow_right (by norm_num) hν)
  · have hz : (C.encP a x).length ≤ PR g (aOf G) := by
      rw [C.length_encP hx]; exact hN.len_le a
    have hq := size_rdU (cRk g G s, (a.val, C.encP a x))
    have hs' : size (cRk g G s, (a.val, C.encP a x)) ≤ size (cRk g G s) + (g + 1) + (2 * PR g (aOf G) + 1) := by
      show size (cRk g G s) + (size a.val + size (C.encP a x)) ≤ _
      rw [LabelSystem.size_word]
      have := LabelSystem.size_fin' a
      omega
    have hq' : size (rdU (cRk g G s, (a.val, C.encP a x))) ≤
        cRU * (7 * (size (cRk g G s) + (g + 1) + (2 * PR g (aOf G) + 1)) + 1) ^ cRU :=
      hq.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have h8 : 8 * (blob (VB.vertexBalanced (n + 1) g) a).card * (Nat.size D + 2) ≤
        8 * ((n + 1) / g + 1) * (Nat.size D + 2) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hν)
    unfold SRU
    omega

/-- **The rank-encoded HC network of `G`, given by procedures**, uniformly in `g` (Definition 2(iii),
the form consumed by `Given.stOnGiven` / `Given.onSteps`): for the vertex-balanced partition, the
crossing order `crossV`, root `0`, a symmetric profile `s` with `s a b ≤ e_ab`, a degree bound
`D ≥ 2`, in the context `cRk g G s = (unary g, (aOf G, profMat g s))`. -/
theorem rank_given {D : ℕ} (hD2 : 2 ≤ D) (hdeg : ∀ v, G.degree v ≤ D)
    (hN : (((crossV g G).hcSystem 0).netP (((crossV g G).hcSystem 0).rankPC s hs rfl)).Is
      (PR g (aOf G)) (BR (aOf G))) :
    Given.IsGivenNetwork (Given.ofProcs rankProcs) Given.noTable (cRk g G s)
      (((crossV g G).hcSystem 0).netP (((crossV g G).hcSystem 0).rankPC s hs rfl))
      (PR g (aOf G)) (BR (aOf G)) (τR g (n + 1) D)
      (SRU g G s D + size (cRk g G s) + 2 * g + 4 * PR g (aOf G) + 8) :=
  procsP_given _ layU_polyT parU_polyT (tableProcD_poly rdU_polyT) hN
    (layU_describes G hs hB) (parSpecU G hs hB) (tSpecU G hs hB hD2 hdeg hN) (one_le_τR g _ _ (by omega))

end USpec

/-! ## An absolute polynomial bound on the state bound -/

section UBound

/-- **The state bound is polynomial in `n + g`**, uniformly in `g`: for a profile with
`s a b ≤ e_ab` and a degree bound `D ≤ n + 2`. -/
theorem state_boundU : ∃ A : ℕ, ∀ (g : ℕ) [NeZero g] (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] (s : Fin g → Fin g → ℕ),
    (∀ a b, s a b ≤ (((crossV g G).hcSystem 0).pairItems a b).length) → ∀ D : ℕ, D ≤ n + 2 →
      SRU g G s D + size (cRk g G s) + 2 * g + 4 * PR g (aOf G) + 8 ≤ A * (n + g + 2) ^ A := by
  refine ⟨_, fun g _ n G _ s hB D hD => le_trans ?_ (((Pol.const 3).mul ((Pol.const cRU).mul
    ((((Pol.const 7).mul ((Pol.const 80).mul (Pol.pow_n 4))).add (Pol.const 1)).pow cRU))).add
    ((Pol.const 200).mul (Pol.pow_n 4)) : Pol _ (n + g) _)⟩
  set M := n + g with hM
  set Y := (M + 2) ^ 4 with hY
  have hM2 : (M + 2) ^ 2 ≤ Y := by
    rw [hY]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY2 : (M + 2) ^ 2 = M * M + 4 * M + 4 := by ring
  have hY4 : (M + 2) ^ 4 = (M + 2) ^ 2 * (M + 2) ^ 2 := by ring
  -- the profile entries
  have hE : ∀ a b, s a b ≤ (n + 1) * (n + 1) := by
    intro a b
    refine (hB a b).trans ?_
    have h1 : (((crossV g G).hcSystem 0).pairItems a b).length ≤ mV g G := by
      unfold LabelSystem.pairItems
      exact (List.length_filter_le _ _).trans (by simp)
    have h2 : mV g G ≤ (pairsW (aOf G)).length := List.length_filter_le _ _
    have h3 : (pairsW (aOf G)).length = (n + 1) * (n + 1) := by
      simp [pairsW, aOf_len, List.length_product]
    omega
  have hpm := size_profMat_le g hE
  have hsz := size_cRk g G s
  have hn1 : n + 1 ≤ M + 2 := by omega
  have hg1 : g + 1 ≤ M + 2 := by omega
  have hnn : (n + 1) * (n + 1) ≤ (M + 2) ^ 2 := by rw [sq]; exact Nat.mul_le_mul hn1 hn1
  have hpm' : size (profMat g s) ≤ 4 * Y := by
    have h1 : (n + 1) * (n + 1) + 2 ≤ 2 * (M + 2) ^ 2 := by rw [hY2] at hnn ⊢; omega
    have h2 : (g + 1) * ((g + 1) * ((n + 1) * (n + 1) + 2)) ≤ (M + 2) * ((M + 2) * (2 * (M + 2) ^ 2)) :=
      Nat.mul_le_mul hg1 (Nat.mul_le_mul hg1 h1)
    have h3 : (M + 2) * ((M + 2) * (2 * (M + 2) ^ 2)) = 2 * Y := by rw [hY]; ring
    have : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
    omega
  have hPR : PR g (aOf G) ≤ 30 * Y := by
    unfold PR
    rw [aOf_len]
    have h1 : (n + 1) / g ≤ n + 1 := Nat.div_le_self _ _
    have h2 : Nat.log2 (n + 1 + 2) ≤ n + 3 := Nat.log2_le_self _
    have h3 := Nat.mul_le_mul (Nat.add_le_add_right h1 1) h2
    have h4 : (n + 1 + 1) * (n + 3) ≤ 2 * (M + 2) ^ 2 := by
      have := Nat.mul_le_mul (show n + 1 + 1 ≤ M + 2 by omega) (show n + 3 ≤ 2 * (M + 2) by omega)
      rw [sq]; nlinarith
    have h5 : g ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : 1 ≤ (M + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hcs : size (cRk g G s) ≤ 10 * Y := by
    have : n * n ≤ (M + 2) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    rw [hY2] at hM2 this
    omega
  have hX : size (cRk g G s) + (g + 1) + (2 * PR g (aOf G) + 1) ≤ 80 * Y := by
    rw [hY2] at hM2; omega
  have hp : (7 * (size (cRk g G s) + (g + 1) + (2 * PR g (aOf G) + 1)) + 1) ^ cRU ≤
      (7 * (80 * Y) + 1) ^ cRU := Nat.pow_le_pow_left (by omega) _
  have hp' := Nat.mul_le_mul_left cRU hp
  have hs8 : 8 * ((n + 1) / g + 1) * (Nat.size D + 2) ≤ 16 * Y := by
    have h1 : (n + 1) / g ≤ n + 1 := Nat.div_le_self _ _
    have h2 : Nat.size D ≤ D := Nat.size_le.2 Nat.lt_two_pow_self
    have := Nat.mul_le_mul (Nat.add_le_add_right h1 1) (Nat.add_le_add_right (h2.trans hD) 2)
    have h4 : (n + 1 + 1) * (n + 2 + 2) ≤ 2 * (M + 2) ^ 2 := by
      have := Nat.mul_le_mul (show n + 1 + 1 ≤ M + 2 by omega) (show n + 2 + 2 ≤ 2 * (M + 2) by omega)
      rw [sq]; nlinarith
    rw [hY2] at hM2 h4
    nlinarith
  have hrest : 8 * ((n + 1) / g + 1) * (Nat.size D + 2) + 20 + size (cRk g G s) + 2 * g +
      4 * PR g (aOf G) + 8 ≤ 200 * Y := by
    have : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
    rw [hY2] at hM2; omega
  unfold SRU
  omega

end UBound

end RW

end EthFollowup.ExactHC
