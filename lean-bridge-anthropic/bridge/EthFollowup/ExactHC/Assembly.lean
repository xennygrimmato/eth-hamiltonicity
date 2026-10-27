/-
# Theorem 1 at Turing-machine level, from an HC network package (module C2)

`research/lean-blueprint.md`, module C2; §6 of `research/exact-hc-theorem.md` (Lemma 6.1, Lemma 6.2,
proof of Theorem 1, "alternative route" of §6.3).

**The hypothesis.** `HCPackage g c₀` collects what the Hamiltonian-specific modules (M7: the
network of Definition 5.1; C1c: its table procedure) must supply for `g` nodes: one set of
procedures `Np` (polynomial-time steps, `Procs.Keeps`), a polynomial-time reader `prep` of
`GraphProblems.code G`, and for every graph with `n ≥ 3` and minimum degree `≥ 2` a network
`IsNetwork Np (prep (code G)) (net G) P B τ S` of value `n·#HC(G)`, with
`U ≤ c₀(m+n) + q`, `P ≤ c₀μ + q`, `B ≤ q(n+2)^q`, `τ ≤ 2^{c₀μ}·q(n+2)^q`,
`S + size(prep (code G)) ≤ q(n+2)^q` and `gμ ≤ 2m + gΔ` (Lemma 6.2), where `c₀` is absolute and `q`
may depend on `g`. `LabelPackage` is the same in the form of the label-sharing network of
`LabelNetwork.lean`/`LabelProcs.lean` (the hypotheses of `labelProcs_given` and `net_is`, the value
in the form of `value_net`); `LabelPackage.toHCPackage` converts.

**The machine** (`Asm.hcM`, a `Stepped (List Bool) (List Bool)` with `IsPolyT`): read `code G`;
for every branch `y < nBr = (n²)^{|H|}` (`H` = vertices of degree `> Θ = n/g + 2`; the digit of `y`
at `v ∈ H` names two neighbours of `v`) build the code of the branch graph `G_y` (Lemma 6.1:
`sum_branches : Σ_y #HC(G_y) = #HC(G)`, every `G_y` has maximum degree `≤ Θ` and at most `m`
edges, `nBr ≤ (n+2)^{4Dg}`); if `G_y` has `n ≤ 2` or a vertex of degree `< 2` count `0`, else run
`Printed.networkOnSteps g NM Np` on `prep (code G_y)` (Lemma 1 + `Given.onSteps`); add up, divide
by `n`, write `Nat.bits`.

**Main results.**
* `Asm.hcM_runs`: on every graph with `m ≤ Dn` the machine returns `#HC(G)` within `A·2^{(δ/2)n}`
  steps on states of size `≤ A(n+2)^A`, given Lemma 1 for `(K, e)` with `e·c₀(D+1) ≤ δ/8` and
  `4c₀(2D+1) ≤ (δ/8)K`, `g = 3K⁸`.
* `theorem1_TM`: from `∃ c₀, ∀ g ≥ 1, Nonempty (HCPackage g c₀)`, for every `δ > 0` and `D` a
  Mathlib `TM2ComputableAux` machine with finite alphabets and `C` such that every graph with at
  most `D·n` edges gives `GraphProblems.Outputs M (code G) (Nat.bits #HC(G)) ⌊C·2^{δn}⌋₊` (the
  form of Anthropic's Corollary 7, via `Given.stEveryEta`, `Printed.groupingLemma`,
  `Given.onSteps` and `GraphProblems.tm_of_stepped`).
* `theorem1_TM_of_label`: the same from label-sharing packages.

Standard axioms only.
-/
import EthFollowup.ExactHC.LabelProcs
import EthFollowup.ExactHC.Preprocess
import Given.Networks
import Given.End
import Printed.End
import GraphProblems.Host
import GraphProblems.Read
import GraphProblems.Cert
import GraphProblems.SetTM
import StepMachines.Prog.Range
import ToTuring.Poly.Range
import ToTuring.Poly.Comb
import ToTuring.Machine.EndTM

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog GraphProblems

namespace Asm

abbrev GIn : Type := List Unit × List Bool

def adjW (a : GIn) (u v : ℕ) : Bool := adjB a.1.length a.2 u v
def degW (a : GIn) (v : ℕ) : ℕ := ((List.range a.1.length).filter (adjW a v)).length
def thetaW (g : ℕ) (a : GIn) : ℕ := a.1.length / g + 2
def highW (g : ℕ) (a : GIn) (v : ℕ) : Bool := decide (thetaW g a < degW a v)
def hlist (g : ℕ) (a : GIn) : List ℕ := (List.range a.1.length).filter (highW g a)
def radix (a : GIn) : ℕ := a.1.length * a.1.length
def nBr (g : ℕ) (a : GIn) : ℕ := radix a ^ (hlist g a).length
def digitW (g : ℕ) (a : GIn) (y v : ℕ) : ℕ := y / radix a ^ ((hlist g a).idxOf v) % radix a
/-- The digit `d` read as the pair `(d / n, d % n)` of neighbours of `v`. -/
def pickD (a : GIn) (v d w : ℕ) : Bool :=
  decide (d / a.1.length < d % a.1.length) && adjW a v (d / a.1.length) && adjW a v (d % a.1.length) &&
    (decide (w = d / a.1.length) || decide (w = d % a.1.length))
def pickW (g : ℕ) (a : GIn) (y v w : ℕ) : Bool := pickD a v (digitW g a y v) w
def keepW (g : ℕ) (a : GIn) (y u w : ℕ) : Bool :=
  (!highW g a u || pickW g a y u w) && (!highW g a w || pickW g a y w u)
def entryW (g : ℕ) (a : GIn) (y u w : ℕ) : Bool := adjW a u w && keepW g a y u w
def brMatrix (g : ℕ) (p : GIn × ℕ) : List Bool :=
  (List.range p.1.1.length).flatMap fun u => (List.range p.1.1.length).map fun w => entryW g p.1 p.2 u w
def brWord (g : ℕ) (p : GIn × ℕ) : List Bool := GraphProblems.unary p.1.1.length ++ brMatrix g p
def badW (g : ℕ) (p : GIn × ℕ) : Bool :=
  decide (p.1.1.length ≤ 2) || (List.range p.1.1.length).any fun v =>
    decide (((List.range p.1.1.length).filter (entryW g p.1 p.2 v)).length < 2)

section Poly
variable {α : Type} [Enc α]

theorem range_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => List.range (a x).1.length :=
  PolyT.range (Unary.of_length (by fun_prop))

@[fun_prop] theorem adjW_polyT {a : α → GIn} {u v : α → ℕ} (ha : PolyT a) (hu : PolyT u) (hv : PolyT v) :
    PolyT fun x => adjW (a x) (u x) (v x) := by unfold adjW; fun_prop

@[fun_prop] theorem degW_polyT {a : α → GIn} {v : α → ℕ} (ha : PolyT a) (hv : PolyT v) :
    PolyT fun x => degW (a x) (v x) := by
  have := range_polyT ha; unfold degW; fun_prop

@[fun_prop] theorem highW_polyT (g : ℕ) {a : α → GIn} {v : α → ℕ} (ha : PolyT a) (hv : PolyT v) :
    PolyT fun x => highW g (a x) (v x) := by unfold highW thetaW; fun_prop

@[fun_prop] theorem hlist_polyT (g : ℕ) {a : α → GIn} (ha : PolyT a) : PolyT fun x => hlist g (a x) := by
  have := range_polyT ha; unfold hlist; fun_prop

@[fun_prop] theorem radix_polyT {a : α → GIn} (ha : PolyT a) : PolyT fun x => radix (a x) := by
  unfold radix; fun_prop

theorem nBr_polyT (g : ℕ) : PolyT (nBr g) := by
  unfold nBr
  exact PolyT.pow_unary (by fun_prop) (Unary.of_length (by fun_prop))

theorem digitW_polyT (g : ℕ) {a : α → GIn} {y v : α → ℕ} (ha : PolyT a) (hy : PolyT y) (hv : PolyT v) :
    PolyT fun x => digitW g (a x) (y x) (v x) := by unfold digitW; fun_prop

theorem pickD_polyT {a : α → GIn} {v d w : α → ℕ} (ha : PolyT a) (hv : PolyT v) (hd : PolyT d) (hw : PolyT w) :
    PolyT fun x => pickD (a x) (v x) (d x) (w x) := by
  have h0 : PolyT fun x => (a x).1.length := PolyT.length (PolyT.fst ha)
  have h1 : PolyT fun x => d x / (a x).1.length := PolyT.div hd h0
  have h2 : PolyT fun x => d x % (a x).1.length := PolyT.mod hd h0
  unfold pickD
  exact PolyT.and' (PolyT.and' (PolyT.and' (PolyT.decide_lt h1 h2) (adjW_polyT ha hv h1))
    (adjW_polyT ha hv h2)) (PolyT.or' (PolyT.decide_eq hw h1) (PolyT.decide_eq hw h2))

@[fun_prop] theorem pickW_polyT (g : ℕ) {a : α → GIn} {y v w : α → ℕ} (ha : PolyT a) (hy : PolyT y) (hv : PolyT v) (hw : PolyT w) :
    PolyT fun x => pickW g (a x) (y x) (v x) (w x) :=
  pickD_polyT ha hv (digitW_polyT g ha hy hv) hw

@[fun_prop] theorem entryW_polyT (g : ℕ) {a : α → GIn} {y u w : α → ℕ} (ha : PolyT a) (hy : PolyT y) (hu : PolyT u) (hw : PolyT w) :
    PolyT fun x => entryW g (a x) (y x) (u x) (w x) := by
  unfold entryW keepW
  exact PolyT.and' (adjW_polyT ha hu hw) (PolyT.and'
    (PolyT.or' (PolyT.not' (highW_polyT g ha hu)) (pickW_polyT g ha hy hu hw))
    (PolyT.or' (PolyT.not' (highW_polyT g ha hw)) (pickW_polyT g ha hy hw hu)))

theorem brWord_polyT (g : ℕ) : PolyT (brWord g) := by
  have h1 := range_polyT (α := GIn × ℕ) (a := fun p => p.1) (by fun_prop)
  have h2 := range_polyT (α := (GIn × ℕ) × ℕ) (a := fun p => p.1.1) (by fun_prop)
  have h3 : PolyT fun p : GIn × ℕ => GraphProblems.unary p.1.1.length := by
    have : PolyT fun p : GIn × ℕ => p.1.1.map (fun _ => true) ++ [false] := by fun_prop
    refine this.congr fun p => ?_
    simp [GraphProblems.unary, List.map_const']
  unfold brWord brMatrix; fun_prop

theorem badW_polyT (g : ℕ) : PolyT (badW g) := by
  have h1 := range_polyT (α := GIn × ℕ) (a := fun p => p.1) (by fun_prop)
  have h2 := range_polyT (α := (GIn × ℕ) × ℕ) (a := fun p => p.1.1) (by fun_prop)
  unfold badW; fun_prop


end Poly

/-! ### The branches, read back as graphs -/

open Finset EthFollowup.Hamiltonian

theorem len_filter_range (n : ℕ) (q : ℕ → Bool) :
    ((List.range n).filter q).length = (univ.filter fun v : Fin n => q v.val = true).card := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map, List.length_map]
  convert length_filter_of_complete (List.finRange n) (List.nodup_finRange n) (List.mem_finRange)
    (fun v : Fin n => q v.val = true) using 3
  funext x; simp

section Graph

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- The input `code G` as read by `read1`. -/
noncomputable def aOf : GIn := (List.replicate n (), GraphProblems.matrix G)

theorem read1_code : read1 (code G) = aOf G := stRead1 n G

@[simp] theorem aOf_len : (aOf G).1.length = n := by simp [aOf]

theorem adjW_aOf {u v : ℕ} (hu : u < n) (hv : v < n) :
    adjW (aOf G) u v = true ↔ G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  have := stAdj n G ⟨u, hu⟩ ⟨v, hv⟩
  simpa [adjW, aOf] using this

theorem degW_aOf [DecidableRel G.Adj] (v : Fin n) : degW (aOf G) v = G.degree v := by
  rw [degW, aOf_len, len_filter_range, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  congr 1; ext w; simp [adjW_aOf G v.2 w.2]

theorem highW_aOf [DecidableRel G.Adj] (g : ℕ) (v : Fin n) :
    highW g (aOf G) v = true ↔ thetaW g (aOf G) < G.degree v := by
  simp [highW, degW_aOf]

theorem hlist_length [DecidableRel G.Adj] (g : ℕ) :
    (hlist g (aOf G)).length = (high G (thetaW g (aOf G))).card := by
  rw [hlist, aOf_len, len_filter_range]
  congr 1; ext v; simp [high, highW_aOf]

theorem mem_hlist {g v : ℕ} : v ∈ hlist g (aOf G) ↔ ∃ _ : v < n, highW g (aOf G) v = true := by
  simp [hlist]

theorem hlist_nodup (g : ℕ) : (hlist g (aOf G)).Nodup := List.nodup_range.filter _

theorem entryW_comm (g y : ℕ) (u w : Fin n) :
    entryW g (aOf G) y u w = entryW g (aOf G) y w u := by
  have h : adjW (aOf G) u w = adjW (aOf G) w u := by
    rw [Bool.eq_iff_iff, adjW_aOf G u.2 w.2, adjW_aOf G w.2 u.2]; exact G.adj_comm _ _
  simp only [entryW, keepW, h]
  congr 1
  exact Bool.and_comm _ _

/-- The branch `y`: `G` minus every edge at a vertex `v` of degree `> Θ` that is not one of the two
edges `v — d/n`, `v — d%n` named by the digit `d` of `y` at `v`. -/
def brGraph (g y : ℕ) : SimpleGraph (Fin n) where
  Adj u w := entryW g (aOf G) y u w = true
  symm := ⟨fun u w h => by rwa [entryW_comm]⟩
  loopless := ⟨fun u h => by
    simp only [entryW, Bool.and_eq_true] at h
    exact G.loopless.irrefl u ((adjW_aOf G u.2 u.2).1 h.1)⟩

noncomputable instance (g y : ℕ) : DecidableRel (brGraph G g y).Adj := fun u w =>
  inferInstanceAs (Decidable (entryW g (aOf G) y u w = true))

theorem brGraph_adj {g y : ℕ} {u w : Fin n} :
    (brGraph G g y).Adj u w ↔ G.Adj u w ∧ keepW g (aOf G) y u w = true := by
  change entryW g (aOf G) y u w = true ↔ _
  simp only [entryW, Bool.and_eq_true, adjW_aOf G u.2 w.2]

theorem brGraph_le (g y : ℕ) : brGraph G g y ≤ G := fun _ _ h => ((brGraph_adj G).1 h).1

/-- The branch word is the code of the branch graph. -/
theorem brWord_code (g y : ℕ) : brWord g (read1 (code G), y) = code (brGraph G g y) := by
  rw [read1_code]
  simp only [brWord, code, aOf_len]
  congr 1
  unfold brMatrix GraphProblems.matrix
  simp only [aOf_len]
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun w _ => ?_
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  rfl

end Graph

/-! ### Lemma 6.1 for the branches: `Σ_y #HC(G_y) = #HC(G)` -/

section HC

variable {n : ℕ}

/-- The neighbours of `v` along the edge set `X`. -/
def nbX (X : Finset (Sym2 (Fin n))) (v : Fin n) : Finset (Fin n) := univ.filter fun w => s(v, w) ∈ X

theorem image_nbX (X : Finset (Sym2 (Fin n))) (v : Fin n) :
    (nbX X v).image (fun w => s(v, w)) = X.filter (fun e => v ∈ e) := by
  ext e
  simp only [nbX, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨hw, Sym2.mem_mk_left _ _⟩
  · rintro ⟨he, hv⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
    exact ⟨w, he, rfl⟩

theorem card_nbX {X : Finset (Sym2 (Fin n))} (hX : TwoRegular X) (v : Fin n) : (nbX X v).card = 2 := by
  rw [← card_image_of_injective _ (fun w w' h => Sym2.congr_right.1 h), image_nbX]
  exact hX v

/-- The digit of a Hamiltonian cycle at `v`: `lo · n + hi` for its two neighbours `lo < hi`. -/
def codeX (X : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  if h : (nbX X v).Nonempty then ((nbX X v).min' h).val * n + ((nbX X v).max' h).val else 0

theorem min'_max'_pair {s : Finset (Fin n)} {x y : Fin n} (hxy : x < y) (hs : s = {x, y})
    (h : s.Nonempty) : s.min' h = x ∧ s.max' h = y := by
  subst hs
  constructor
  · refine le_antisymm (min'_le _ _ (by simp)) (le_min' _ _ _ fun z hz => ?_)
    rcases mem_insert.1 hz with rfl | hz
    · exact le_rfl
    · rw [mem_singleton.1 hz]; exact hxy.le
  · refine le_antisymm (max'_le _ _ _ fun z hz => ?_) (le_max' _ _ (by simp))
    rcases mem_insert.1 hz with rfl | hz
    · exact hxy.le
    · rw [mem_singleton.1 hz]

theorem nbX_pair {X : Finset (Sym2 (Fin n))} {v : Fin n} (h2 : (nbX X v).card = 2) :
    ∃ lo hi : Fin n, lo < hi ∧ nbX X v = {lo, hi} ∧ codeX X v = lo.val * n + hi.val := by
  obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.1 h2
  have hne : (nbX X v).Nonempty := ⟨x, by rw [he]; simp⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨h1, h2⟩ := min'_max'_pair h he hne
    exact ⟨x, y, h, he, by rw [codeX, dif_pos hne, h1, h2]⟩
  · have he' : nbX X v = {y, x} := by rw [he, pair_comm]
    obtain ⟨h1, h2⟩ := min'_max'_pair h he' hne
    exact ⟨y, x, h, he', by rw [codeX, dif_pos hne, h1, h2]⟩

theorem codeX_lt (X : Finset (Sym2 (Fin n))) (v : Fin n) : codeX X v < n * n := by
  have hn : 0 < n := Fin.pos v
  unfold codeX
  split_ifs with h
  · have h1 := ((nbX X v).min' h).isLt
    have h2 := ((nbX X v).max' h).isLt
    nlinarith
  · exact Nat.mul_pos hn hn

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem adj_of_mem {X : Finset (Sym2 (Fin n))} (hX : X ∈ hamCycles G) {v w : Fin n}
    (h : s(v, w) ∈ X) : G.Adj v w := by
  have := ((mem_hamCycles_iff G X).1 hX).1 h
  rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this

/-- **The digit at `v` names the two cycle edges at `v`.** -/
theorem pick_iff {X : Finset (Sym2 (Fin n))} (hX : X ∈ hamCycles G) (g y : ℕ) (v : Fin n) :
    (∀ w : Fin n, s(v, w) ∈ X → pickW g (aOf G) y v w = true) ↔
      digitW g (aOf G) y v = codeX X v := by
  have hn : 0 < n := Fin.pos v
  obtain ⟨lo, hi, hlh, hnb, hc⟩ := nbX_pair (card_nbX ((mem_hamCycles_iff G X).1 hX).2.1 v)
  have hmem : ∀ w, s(v, w) ∈ X ↔ w = lo ∨ w = hi := fun w => by
    have : w ∈ nbX X v ↔ w ∈ ({lo, hi} : Finset (Fin n)) := by rw [hnb]
    simpa [nbX] using this
  rw [hc]
  set d := digitW g (aOf G) y v with hd
  have hpick : ∀ w : Fin n, pickW g (aOf G) y v w = true ↔
      d / n < d % n ∧ adjW (aOf G) v (d / n) = true ∧ adjW (aOf G) v (d % n) = true ∧
        (w.val = d / n ∨ w.val = d % n) := fun w => by
    simp only [pickW, pickD, aOf_len, ← hd, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      and_assoc]
  constructor
  · intro h
    have h1 := (hpick lo).1 (h lo ((hmem lo).2 (Or.inl rfl)))
    have h2 := (hpick hi).1 (h hi ((hmem hi).2 (Or.inr rfl)))
    have hlh' : lo.val < hi.val := hlh
    have e1 : lo.val = d / n := by omega
    have e2 : hi.val = d % n := by omega
    rw [e1, e2, Nat.div_add_mod']
  · intro h w hw
    have hlo := lo.isLt
    have hhi := hi.isLt
    have e1 : d / n = lo.val := by
      rw [h]; exact Nat.div_eq_of_lt_le (by nlinarith) (by rw [Nat.succ_mul]; omega)
    have e2 : d % n = hi.val := by
      have := Nat.mod_add_div d n
      rw [e1] at this
      rw [h] at this ⊢
      have hh : n * ↑lo = ↑lo * n := Nat.mul_comm _ _
      omega
    refine (hpick w).2 ⟨by rw [e1, e2]; exact hlh, ?_, ?_, ?_⟩
    · rw [e1, adjW_aOf G v.2 lo.2]; exact adj_of_mem G hX ((hmem lo).2 (Or.inl rfl))
    · rw [e2, adjW_aOf G v.2 hi.2]; exact adj_of_mem G hX ((hmem hi).2 (Or.inr rfl))
    · rw [e1, e2]
      rcases (hmem w).1 hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem sub_brGraph_iff {X : Finset (Sym2 (Fin n))} (hX : X ∈ hamCycles G) (g y : ℕ) :
    X ⊆ (brGraph G g y).edgeFinset ↔
      ∀ v : Fin n, highW g (aOf G) v = true → digitW g (aOf G) y v = codeX X v := by
  have hsub := ((mem_hamCycles_iff G X).1 hX).1
  refine ⟨fun h v hv => (pick_iff G hX g y v).1 fun w hw => ?_, fun h e he => ?_⟩
  · have := h hw
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, brGraph_adj] at this
    have h2 := this.2
    simp only [keepW, hv, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
    exact h2.1
  · induction e using Sym2.ind with
    | _ u w =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, brGraph_adj]
      refine ⟨adj_of_mem G hX he, ?_⟩
      simp only [keepW, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      constructor
      · by_cases hu : highW g (aOf G) u = true
        · exact Or.inr ((pick_iff G hX g y u).2 (h u hu) w he)
        · exact Or.inl (by simpa using hu)
      · by_cases hw : highW g (aOf G) w = true
        · exact Or.inr ((pick_iff G hX g y w).2 (h w hw) u (by rwa [Sym2.eq_swap]))
        · exact Or.inl (by simpa using hw)

/-- The digits of a Hamiltonian cycle, one per vertex of degree `> Θ`. -/
noncomputable def fX (g : ℕ) (X : Finset (Sym2 (Fin n))) : Fin (hlist g (aOf G)).length → Fin (radix (aOf G)) :=
  fun k => ⟨codeX X ⟨(hlist g (aOf G))[k], ((mem_hlist G).1 (List.getElem_mem k.2)).1⟩, by
    rw [radix, aOf_len]; exact codeX_lt X _⟩

/-- The branch of a Hamiltonian cycle. -/
noncomputable def yOf (g : ℕ) (X : Finset (Sym2 (Fin n))) : ℕ := (finFunctionFinEquiv (fX G g X) : ℕ)

theorem yOf_lt (g : ℕ) (X : Finset (Sym2 (Fin n))) : yOf G g X < nBr g (aOf G) :=
  (finFunctionFinEquiv (fX G g X)).isLt

theorem digits_iff {X : Finset (Sym2 (Fin n))} (g : ℕ) {y : ℕ} (hy : y < nBr g (aOf G)) :
    (∀ v : Fin n, highW g (aOf G) v = true → digitW g (aOf G) y v = codeX X v) ↔ y = yOf G g X := by
  set hl := hlist g (aOf G) with hhl
  have hnd : hl.Nodup := hlist_nodup G g
  have e1 : y = yOf G g X ↔ ∀ k : Fin hl.length, y / radix (aOf G) ^ (k : ℕ) % radix (aOf G) =
      (fX G g X k : ℕ) := by
    rw [yOf]
    constructor
    · intro h k
      have : (⟨y, hy⟩ : Fin (radix (aOf G) ^ hl.length)) = finFunctionFinEquiv (fX G g X) :=
        Fin.ext h
      have e := finFunctionFinEquiv_symm_apply_val (⟨y, hy⟩ : Fin (radix (aOf G) ^ hl.length)) k
      have e2 : finFunctionFinEquiv.symm (⟨y, hy⟩ : Fin (radix (aOf G) ^ hl.length)) = fX G g X := by
        rw [this, Equiv.symm_apply_apply]
      rw [e2] at e
      exact e.symm
    · intro h
      have : finFunctionFinEquiv.symm (⟨y, hy⟩ : Fin (radix (aOf G) ^ hl.length)) = fX G g X := by
        funext k; exact Fin.ext (by rw [finFunctionFinEquiv_symm_apply_val]; exact h k)
      rw [← this, Equiv.apply_symm_apply]
  rw [e1]
  constructor
  · intro h k
    have hk := (mem_hlist G).1 (List.getElem_mem k.2)
    have := h ⟨hl[k], hk.1⟩ hk.2
    simp only [digitW, ← hhl, Fin.getElem_fin] at this
    rw [hnd.idxOf_getElem] at this
    exact this
  · intro h v hv
    have hm : v.val ∈ hl := (mem_hlist G).2 ⟨v.2, hv⟩
    have hk : hl.idxOf v.val < hl.length := List.idxOf_lt_length_of_mem hm
    have := h ⟨_, hk⟩
    simp only [fX, ← hhl] at this
    simp only [digitW, ← hhl]
    convert this using 2
    exact Fin.ext (List.getElem_idxOf hk).symm

/-- **Lemma 6.1, branch form.** For `y < nBr`, the Hamiltonian cycles of the branch `y` are the
Hamiltonian cycles of `G` whose branch is `y`. -/
theorem hamCycles_brGraph (g : ℕ) {y : ℕ} (hy : y < nBr g (aOf G)) :
    hamCycles (brGraph G g y) = (hamCycles G).filter fun X => yOf G g X = y := by
  ext X
  rw [mem_filter, mem_hamCycles_iff, mem_hamCycles_iff]
  constructor
  · rintro ⟨hs, hr, hc⟩
    have hX : X ∈ hamCycles G := (mem_hamCycles_iff G X).2
      ⟨hs.trans (SimpleGraph.edgeFinset_mono (brGraph_le G g y)), hr, hc⟩
    refine ⟨(mem_hamCycles_iff G X).1 hX, ?_⟩
    exact ((digits_iff G g hy).1 ((sub_brGraph_iff G hX g y).1 hs)).symm
  · rintro ⟨hX, rfl⟩
    have hX' := (mem_hamCycles_iff G X).2 hX
    exact ⟨(sub_brGraph_iff G hX' g _).2 ((digits_iff G g hy).2 rfl), hX.2.1, hX.2.2⟩

theorem sum_branches (g : ℕ) :
    ∑ y ∈ range (nBr g (aOf G)), (hamCycles (brGraph G g y)).card = (hamCycles G).card := by
  rw [card_eq_sum_card_fiberwise (f := yOf G g) (t := range (nBr g (aOf G)))
    fun X _ => mem_range.2 (yOf_lt G g X)]
  exact sum_congr rfl fun y hy => by rw [hamCycles_brGraph G g (mem_range.1 hy)]

end HC

/-! ### Bounds for the branches -/

section Bounds

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem thetaW_aOf (g : ℕ) : thetaW g (aOf G) = n / g + 2 := by simp [thetaW]

theorem degree_le_of_le {H H' : SimpleGraph (Fin n)} [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (h : H ≤ H') (v : Fin n) : H.degree v ≤ H'.degree v := by
  rw [← H.card_neighborFinset_eq_degree, ← H'.card_neighborFinset_eq_degree]
  exact card_le_card fun w hw => by
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢; exact h hw

/-- Every branch has maximum degree at most `Θ = n/g + 2`. -/
theorem degree_brGraph_le (g y : ℕ) (v : Fin n) : (brGraph G g y).degree v ≤ n / g + 2 := by
  by_cases hv : highW g (aOf G) v = true
  · set d := digitW g (aOf G) y v
    have hsub : (brGraph G g y).neighborFinset v ⊆
        (univ.filter fun w : Fin n => w.val = d / n) ∪ (univ.filter fun w : Fin n => w.val = d % n) := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, brGraph_adj] at hw
      have h2 := hw.2
      simp only [keepW, hv, Bool.not_true, Bool.false_or, Bool.and_eq_true, pickW, pickD, aOf_len,
        Bool.or_eq_true, decide_eq_true_eq] at h2
      simp only [mem_union, mem_filter, mem_univ, true_and]
      exact h2.1.2
    have h1 : ∀ c : ℕ, (univ.filter fun w : Fin n => w.val = c).card ≤ 1 := fun c =>
      Finset.card_le_one.2 fun a ha b hb => by
        simp only [mem_filter, mem_univ, true_and] at ha hb
        exact Fin.ext (ha.trans hb.symm)
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have := (card_le_card hsub).trans (card_union_le _ _)
    have := h1 (d / n)
    have := h1 (d % n)
    generalize n / g = t
    omega
  · have h1 := degree_le_of_le (brGraph_le G g y) v
    rw [highW_aOf, thetaW_aOf] at hv
    omega

theorem card_edge_brGraph_le (g y : ℕ) :
    (brGraph G g y).edgeFinset.card ≤ G.edgeFinset.card :=
  card_le_card (SimpleGraph.edgeFinset_mono (brGraph_le G g y))

/-- At most `2Dg` vertices have degree `> Θ`. -/
theorem hlist_length_le {g D : ℕ} (hg : 1 ≤ g) (hm : G.edgeFinset.card ≤ D * n) :
    (hlist g (aOf G)).length ≤ 2 * D * g := by
  rw [hlist_length]
  have h1 := card_high_mul_le G (thetaW g (aOf G))
  rw [thetaW_aOf] at h1 ⊢
  have h2 : n ≤ g * (n / g + 2) := by
    have := Nat.lt_mul_div_succ n (show 0 < g by omega)
    nlinarith
  have h3 : (high G (n / g + 2)).card * (n / g + 2) ≤ (2 * D * g) * (n / g + 2) := by
    calc _ ≤ 2 * G.edgeFinset.card := h1
      _ ≤ 2 * (D * n) := by omega
      _ ≤ 2 * (D * (g * (n / g + 2))) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

/-- The number of branches is at most `(n+2)^{4Dg}`. -/
theorem nBr_le {g D : ℕ} (hg : 1 ≤ g) (hm : G.edgeFinset.card ≤ D * n) :
    nBr g (aOf G) ≤ (n + 2) ^ (4 * D * g) := by
  unfold nBr radix
  rw [aOf_len]
  calc (n * n) ^ (hlist g (aOf G)).length ≤ ((n + 2) ^ 2) ^ (hlist g (aOf G)).length :=
        Nat.pow_le_pow_left (by nlinarith) _
    _ ≤ ((n + 2) ^ 2) ^ (2 * D * g) :=
        Nat.pow_le_pow_right (by positivity) (hlist_length_le G hg hm)
    _ = (n + 2) ^ (4 * D * g) := by rw [← pow_mul]; ring_nf

end Bounds

section Bad

variable {n : ℕ}

theorem two_le_degree_of_mem {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {X : Finset (Sym2 (Fin n))} (hX : X ∈ hamCycles H) (v : Fin n) : 2 ≤ H.degree v := by
  rw [← card_nbX ((mem_hamCycles_iff H X).1 hX).2.1 v, ← H.card_neighborFinset_eq_degree]
  exact card_le_card fun w hw => by
    rw [SimpleGraph.mem_neighborFinset]
    exact adj_of_mem H hX (mem_filter.1 hw).2

theorem hamCycles_eq_empty {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    (h : n ≤ 2 ∨ ∃ v, H.degree v < 2) : hamCycles H = ∅ := by
  refine eq_empty_of_forall_notMem fun X hX => ?_
  rcases h with h | ⟨v, hv⟩
  · obtain ⟨v⟩ := ((mem_hamCycles_iff H X).1 hX).2.2.nonempty
    have h1 := two_le_degree_of_mem hX v
    have h2 := H.degree_lt_card_verts v
    rw [Fintype.card_fin] at h2
    omega
  · have := two_le_degree_of_mem hX v
    omega

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem degree_brGraph_eq (g y : ℕ) (v : Fin n) :
    ((List.range n).filter (entryW g (aOf G) y v)).length = (brGraph G g y).degree v := by
  rw [len_filter_range, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  rfl

theorem badW_iff (g y : ℕ) :
    badW g (aOf G, y) = true ↔ n ≤ 2 ∨ ∃ v, (brGraph G g y).degree v < 2 := by
  simp only [badW, aOf_len, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  refine or_congr Iff.rfl ⟨fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, ?_⟩, fun ⟨v, h⟩ => ⟨v, v.2, ?_⟩⟩
  · rw [← degree_brGraph_eq]; exact h
  · rw [degree_brGraph_eq]; exact h

theorem card_hamCycles_le (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (hamCycles H).card ≤ 2 ^ (n * n) := by
  have h1 : hamCycles H ⊆ H.edgeFinset.powerset := fun X hX =>
    mem_powerset.2 ((mem_hamCycles_iff H X).1 hX).1
  have h2 := card_le_card h1
  rw [card_powerset] at h2
  refine h2.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  calc H.edgeFinset.card ≤ (Fintype.card (Fin n)).choose 2 := H.card_edgeFinset_le_card_choose_two
    _ ≤ n * n := by rw [Fintype.card_fin]; exact (Nat.choose_le_pow n 2).trans (by rw [pow_two])

end Bad

end Asm

/-! ## The package that the Hamiltonian side supplies -/

open Eight.SecNetworks Printed Finset EthFollowup.Hamiltonian

/-- **An HC network package for `g` nodes**, with the absolute constant `c₀`: everything the
Hamiltonian-specific modules (M7 network instantiation, C1c table procedure) supply.

* One context type `Ctx` and one set of procedures `Np` for all graphs (with unary numbers and
  polynomial-time steps, `Procs.Keeps`), and a polynomial-time reader `prep` of the graph code.
* For every graph `G` with `n ≥ 3` and minimum degree `≥ 2`: a network `net G` on `Fin g`, given by
  `Np` in the context `prep (code G)` with parameters `P B τ S` (`IsNetwork`, Definition 2), of
  value `n · #HC(G)`.
* The bounds, where `μ = mu G` is the largest blob degree sum (Lemma 6.2: `g μ ≤ 2m + gΔ`) and `q`
  is a constant that may depend on `g` (but not on `G`):
  `U ≤ c₀ (m + n) + q`, `P ≤ c₀ μ + q`, `B ≤ q (n+2)^q`, `τ ≤ 2^{c₀ μ} · q (n+2)^q` and
  `S + size (prep (code G)) ≤ q (n+2)^q`.

`LabelPackage` below is the same data in the form of the label-sharing network of
`LabelNetwork.lean` / `LabelProcs.lean`; `LabelPackage.toHCPackage` converts it. -/
structure HCPackage (g c₀ : ℕ) : Type 1 where
  Ctx : Type
  [encCtx : Enc Ctx]
  [sizeCtx : HasSize Ctx]
  [carriedCtx : Carried Ctx]
  Np : Procs Ctx
  keeps : Np.Keeps
  P_unary : Unary Np.P
  B_unary : Unary Np.B
  prep : List Bool → Ctx
  prep_poly : PolyT prep
  q : ℕ
  net : ∀ {n : ℕ}, SimpleGraph (Fin n) → Net g
  P : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  B : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  τ : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  S : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  mu : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  isNet : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    IsNetwork Np (prep (code G)) (net G) (P G) (B G) (τ G) (S G)
  value : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    (net G).value = (n : ℤ) * ((hamCycles G).card : ℤ)
  mu_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) → g * mu G ≤ 2 * G.edgeFinset.card + g * Δ
  U_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    (net G).U ≤ c₀ * (G.edgeFinset.card + n) + q
  P_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    P G ≤ c₀ * mu G + q
  B_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    B G ≤ q * (n + 2) ^ q
  τ_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    τ G ≤ 2 ^ (c₀ * mu G) * (q * (n + 2) ^ q)
  S_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    S G + size (prep (code G)) ≤ q * (n + 2) ^ q

attribute [instance] HCPackage.encCtx HCPackage.sizeCtx HCPackage.carriedCtx

namespace Asm

variable {g c₀ : ℕ}

/-- One branch: `0` if the branch graph has `n ≤ 2` or a vertex of degree `< 2`; otherwise Lemma 1
(the machine `NM`) on its network. -/
def bodyM (g : ℕ) (NM : NetMachine) (pk : HCPackage g c₀) : Stepped (GIn × ℕ) ℤ :=
  Stepped.ite (badW g) (Stepped.const 0)
    (Stepped.mapIn (fun p => pk.prep (brWord g p)) (networkOnSteps g NM pk.Np))

/-- The sum over the branches of Lemma 6.1: `n · #HC(G)`. -/
def mainM (g : ℕ) (NM : NetMachine) (pk : HCPackage g c₀) : Stepped (List Bool) ℤ :=
  Stepped.mapIn read1 (Stepped.sumRange (nBr g) (bodyM g NM pk))

/-- Division by `n` and the binary digits. -/
def finW (p : List Bool × ℤ) : List Bool := Nat.bits (p.2.toNat / ones p.1)

/-- **The machine of Theorem 1.** -/
def hcM (g : ℕ) (NM : NetMachine) (pk : HCPackage g c₀) : Stepped (List Bool) (List Bool) :=
  Stepped.bind (mainM g NM pk) (Stepped.ofFun finW)

theorem finW_polyT : PolyT finW := by
  unfold finW
  exact PolyT.bits (PolyT.div (PolyT.toNat PolyT.id'.snd) (ones_polyT PolyT.id'.fst))

theorem hcM_poly (NM : NetMachine) (pk : HCPackage g c₀) (hN : NM.PolyTimeSteps) :
    Nonempty (IsPolyT (hcM g NM pk)) := by
  obtain ⟨i1⟩ := networkOnSteps_poly g NM pk.Np hN pk.keeps pk.P_unary pk.B_unary
  have : IsPolyT (Stepped.mapIn (fun p => pk.prep (brWord g p)) (networkOnSteps g NM pk.Np)) :=
    IsPolyT.mapIn (PolyT.comp pk.prep_poly (brWord_polyT g))
  have : IsPolyT (Stepped.const (0 : ℤ) : Stepped (GIn × ℕ) ℤ) := IsPolyT.const 0
  have : IsPolyT (bodyM g NM pk) := IsPolyT.ite (badW_polyT g)
  have : IsPolyT (Stepped.sumRange (nBr g) (bodyM g NM pk)) := IsPolyT.sumRange (nBr_polyT g)
  have : IsPolyT (mainM g NM pk) := IsPolyT.mapIn stCertRead.1
  have : IsPolyT (Stepped.ofFun finW) := IsPolyT.ofFun finW_polyT
  exact ⟨IsPolyT.bind⟩


/-! ### Polynomial bounds -/

/-- `x ≤ A · (n+2)^A`. -/
def Pol (A n x : ℕ) : Prop := x ≤ A * (n + 2) ^ A

namespace Pol

variable {A B n x y : ℕ}

theorem mono (h : Pol A n x) (hAB : A ≤ B) : Pol B n x :=
  h.trans (Nat.mul_le_mul hAB (Nat.pow_le_pow_right (by omega) hAB))

theorem le (h : Pol A n y) (hxy : x ≤ y) : Pol A n x := hxy.trans h

theorem add (hx : Pol A n x) (hy : Pol B n y) : Pol (A + B) n (x + y) := by
  have h1 := (hx.mono (Nat.le_add_right A B))
  have h2 := (hy.mono (Nat.le_add_left B A))
  unfold Pol at *
  calc x + y ≤ A * (n + 2) ^ (A + B) + B * (n + 2) ^ (A + B) := by
        have e1 : A * (n + 2) ^ A ≤ A * (n + 2) ^ (A + B) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_add_right A B))
        have e2 : B * (n + 2) ^ B ≤ B * (n + 2) ^ (A + B) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_add_left B A))
        omega
    _ = (A + B) * (n + 2) ^ (A + B) := by ring

theorem mul (hx : Pol A n x) (hy : Pol B n y) : Pol (A * B + A + B) n (x * y) := by
  unfold Pol at *
  have h1 : 1 ≤ n + 2 := by omega
  calc x * y ≤ (A * (n + 2) ^ A) * (B * (n + 2) ^ B) := Nat.mul_le_mul hx hy
    _ = (A * B) * (n + 2) ^ (A + B) := by rw [pow_add]; ring
    _ ≤ (A * B + A + B) * (n + 2) ^ (A * B + A + B) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

theorem const (k : ℕ) {n : ℕ} : Pol k n k := by
  unfold Pol
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

theorem id {n : ℕ} : Pol 1 n n := by unfold Pol; rw [pow_one]; omega

theorem pow_n (k : ℕ) {n : ℕ} : Pol (k + 1) n ((n + 2) ^ k) := by
  unfold Pol
  calc (n + 2) ^ k ≤ (n + 2) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)

theorem pow (hx : Pol A n x) (k : ℕ) : Pol (A ^ k + A * k) n (x ^ k) := by
  unfold Pol at *
  calc x ^ k ≤ (A * (n + 2) ^ A) ^ k := Nat.pow_le_pow_left hx k
    _ = A ^ k * (n + 2) ^ (A * k) := by rw [mul_pow, ← pow_mul]
    _ ≤ (A ^ k + A * k) * (n + 2) ^ (A ^ k + A * k) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

theorem max' (hx : Pol A n x) (hy : Pol B n y) : Pol (A + B) n (max x y) :=
  (hx.add hy).le (max_le_iff.2 ⟨by omega, by omega⟩)

end Pol

theorem size_nat_le' (k : ℕ) : size k ≤ k + 1 := by
  change k.size + 1 ≤ k + 1
  exact Nat.add_le_add_right (Nat.size_le.2 Nat.lt_two_pow_self) 1

theorem size_nat_of_lt {k b : ℕ} (h : k < 2 ^ b) : size k ≤ b + 1 := by
  change k.size + 1 ≤ b + 1
  exact Nat.add_le_add_right (Nat.size_le.2 h) 1

theorem size_int_of_lt {z : ℤ} {b : ℕ} (h : z.natAbs < 2 ^ b) : size z ≤ b + 1 := by
  change z.natAbs.size + 1 ≤ b + 1
  exact Nat.add_le_add_right (Nat.size_le.2 h) 1

theorem size_units (l : List Unit) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_unit, List.length_cons] at ih ⊢
    omega

theorem lt_two_pow_mul_self (n : ℕ) : n + 2 < 2 ^ (n + 2) := Nat.lt_two_pow_self

/-! ### The exponent -/

/-- The exponent of Lemma 1 plus that of `τ`, for one branch, is at most `(δ/4) n + E₀`. -/
theorem exponent_le {e δ : ℝ} {c₀ q g K D n m mu U P : ℕ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK1 : 1 ≤ K)
    (hKg : K ≤ g) (hm : m ≤ D * n) (hmu : g * mu ≤ 2 * m + g * (n / g + 2))
    (hU : U ≤ c₀ * (m + n) + q) (hP : P ≤ c₀ * mu + q) (he : e * c₀ * (D + 1) ≤ δ / 8)
    (hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K) :
    e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K + (c₀ * mu : ℕ) ≤
      δ / 4 * n + ((q + 3 * (2 * c₀ * g + g * q) + 2 * c₀ : ℕ) : ℝ) := by
  have hg1 : 1 ≤ g := hK1.trans hKg
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg1
  have hKgr : (K : ℝ) ≤ g := by exact_mod_cast hKg
  -- g μ ≤ (2D+1) n + 2g
  have hgmu : g * mu ≤ (2 * D + 1) * n + 2 * g := by
    have : g * (n / g) ≤ n := Nat.mul_div_le n g
    nlinarith
  have hgmuR : (g : ℝ) * mu ≤ (2 * D + 1) * n + 2 * g := by exact_mod_cast hgmu
  have hUR : (U : ℝ) ≤ c₀ * (D + 1) * n + q := by
    have : U ≤ c₀ * (D * n + n) + q := hU.trans (by gcongr)
    have : (U : ℝ) ≤ c₀ * (D * n + n) + q := by exact_mod_cast this
    nlinarith
  have hPR : (P : ℝ) ≤ c₀ * mu + q := by exact_mod_cast hP
  set Y : ℝ := c₀ * (2 * D + 1) * n with hY
  have hY0 : 0 ≤ Y := by positivity
  have hgP : (g : ℝ) * P ≤ Y + (2 * c₀ * g + g * q) := by
    calc (g : ℝ) * P ≤ g * (c₀ * mu + q) := by gcongr
      _ = c₀ * (g * mu) + g * q := by ring
      _ ≤ c₀ * ((2 * D + 1) * n + 2 * g) + g * q := by gcongr
      _ = Y + (2 * c₀ * g + g * q) := by rw [hY]; ring
  have hgP0 : 0 ≤ (g : ℝ) * P := by positivity
  have hZ : (0 : ℝ) ≤ 2 * c₀ * g + g * q := by positivity
  have h1 : (g : ℝ) * P / K ≤ Y / K + (2 * c₀ * g + g * q) := by
    calc (g : ℝ) * P / K ≤ (Y + (2 * c₀ * g + g * q)) / K := by gcongr
      _ = Y / K + (2 * c₀ * g + g * q) / K := by rw [add_div]
      _ ≤ Y / K + (2 * c₀ * g + g * q) := by
          gcongr; exact div_le_self hZ (by exact_mod_cast hK1)
  have hmuR : ((c₀ * mu : ℕ) : ℝ) ≤ Y / K + 2 * c₀ := by
    push_cast
    have : (mu : ℝ) ≤ ((2 * D + 1) * n + 2 * g) / g := by
      rw [le_div_iff₀ hgr]; linarith
    calc (c₀ : ℝ) * mu ≤ c₀ * (((2 * D + 1) * n + 2 * g) / g) := by gcongr
      _ = Y / g + 2 * c₀ := by rw [hY]; field_simp
      _ ≤ Y / K + 2 * c₀ := by gcongr
  have hYK : 4 * (Y / K) ≤ δ / 8 * n := by
    rw [hY, mul_div_assoc', div_le_iff₀ hKr]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have heU : e * (U : ℝ) ≤ δ / 8 * n + q := by
    have h2 : e * (U : ℝ) ≤ e * (c₀ * (D + 1) * n + q) := by gcongr
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have h3 : e * (q : ℝ) ≤ q := by nlinarith
    have h4 : (e * c₀ * (D + 1)) * (n : ℝ) ≤ δ / 8 * n := by nlinarith
    nlinarith
  have hePK : e * ((g : ℝ) * P / K) ≤ (g : ℝ) * P / K := by
    have : 0 ≤ (g : ℝ) * P / K := by positivity
    nlinarith
  have e2 : 2 * ((g : ℝ) * P) / K = 2 * ((g : ℝ) * P / K) := by ring
  have hmuR' : (c₀ : ℝ) * mu ≤ Y / K + 2 * c₀ := by exact_mod_cast hmuR
  push_cast
  rw [mul_add, e2]
  linarith


/-! ### One branch -/

section Runs

variable {g c₀ : ℕ} {NM : NetMachine} {C₁ K : ℕ} {e δ : ℝ}

theorem size_aOf {n : ℕ} (G : SimpleGraph (Fin n)) : size (aOf G) = (2 * n + 1) + (2 * (n * n) + 1) := by
  simp only [aOf, size_prod, size_units, LabelSystem.size_word, stMatrixLength n G, List.length_replicate]

/-- The bound on `P + B` of a branch. -/
def pbB (c₀ q D : ℕ) (n : ℕ) : ℕ := c₀ * ((2 * D + 1) * n + 2) + q + q * (n + 2) ^ q

/-- The state bound of a branch. -/
def smB (g c₀ q D C₁ : ℕ) (n : ℕ) : ℕ :=
  ((2 * n + 1) + (2 * (n * n) + 1) + ((n + 2) ^ (4 * D * g) + 1) + 3) +
    (q * (n + 2) ^ q + C₁ * pbB c₀ q D n ^ C₁ + 5)

/-- The step bound of a branch, without the factor `2^{(δ/4) n}`. -/
def wB (g c₀ q D C₁ : ℕ) (n : ℕ) : ℕ :=
  3 * C₁ * 2 ^ (q + 3 * (2 * c₀ * g + g * q) + 2 * c₀) * pbB c₀ q D n ^ C₁ * (q * (n + 2) ^ q) + 1

theorem body_runs (pk : HCPackage g c₀) (hNM : ComputesNetworks NM C₁ g K e)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK1 : 1 ≤ K) (hKg : K ≤ g) {D : ℕ}
    (he : e * c₀ * (D + 1) ≤ δ / 8) (hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hm : G.edgeFinset.card ≤ D * n)
    {y : ℕ} (hy : y < nBr g (aOf G)) :
    ∃ t : ℕ, (bodyM g NM pk).Runs (aOf G, y) t (smB g c₀ pk.q D C₁ n)
        ((n : ℤ) * ((hamCycles (brGraph G g y)).card : ℤ)) ∧
      (t : ℝ) ≤ wB g c₀ pk.q D C₁ n * (2 : ℝ) ^ (δ / 4 * n) := by
  have hg1 : 1 ≤ g := hK1.trans hKg
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 4 * n) := by
    have : (0 : ℝ) ≤ δ / 4 * n := by
      have : 0 ≤ δ := by
        have h0 : (0 : ℝ) ≤ 4 * (c₀ : ℝ) * (2 * D + 1) := by positivity
        have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
        nlinarith
      positivity
    exact Real.one_le_rpow one_le_two this
  have hsy : size y ≤ (n + 2) ^ (4 * D * g) + 1 := by
    have := nBr_le G hg1 hm
    have := size_nat_le' y
    omega
  have hsa := size_aOf G
  by_cases hb : badW g (aOf G, y) = true
  · -- the branch has no Hamiltonian cycle
    have h0 := hamCycles_eq_empty ((badW_iff G g y).1 hb)
    refine ⟨1, ?_, ?_⟩
    · rw [h0, card_empty, Nat.cast_zero, mul_zero]
      refine (Stepped.ite_runs_true hb (Stepped.const_runs (0 : ℤ) (aOf G, y))).mono le_rfl ?_
      have : size (0 : ℤ) = 1 := rfl
      simp only [size_prod] at *
      unfold smB
      omega
    · have : (1 : ℝ) ≤ wB g c₀ pk.q D C₁ n := by
        have : 1 ≤ wB g c₀ pk.q D C₁ n := by unfold wB; omega
        exact_mod_cast this
      nlinarith
  · -- the network of the branch
    have hb' : badW g (aOf G, y) = false := by simpa using hb
    set H := brGraph G g y with hH
    have hgood : ¬ (n ≤ 2 ∨ ∃ v, H.degree v < 2) := fun h => hb ((badW_iff G g y).2 h)
    have h3 : 3 ≤ n := by omega
    have hdeg : ∀ v, 2 ≤ H.degree v := fun v => by
      by_contra h; exact hgood (Or.inr ⟨v, by omega⟩)
    have hcode : brWord g (aOf G, y) = code H := by rw [← read1_code]; exact brWord_code G g y
    have hgiven : Given.IsGivenNetwork (Given.ofProcs pk.Np) Given.noTable (pk.prep (code H))
        (pk.net H) (pk.P H) (pk.B H) (pk.τ H) (pk.S H) :=
      ⟨pk.isNet H h3 hdeg, Given.ofProcs_poly pk.Np pk.keeps pk.P_unary pk.B_unary⟩
    obtain ⟨T, hrun, hT⟩ := (Given.onSteps hNM hgiven).2
    rw [pk.value H h3 hdeg] at hrun
    have hmH : H.edgeFinset.card ≤ D * n := (card_edge_brGraph_le G g y).trans hm
    have hmu := pk.mu_le H h3 hdeg (n / g + 2) (degree_brGraph_le G g y)
    have hU := pk.U_le H h3 hdeg
    have hP := pk.P_le H h3 hdeg
    have hB := pk.B_le H h3 hdeg
    have hτ := pk.τ_le H h3 hdeg
    have hS := pk.S_le H h3 hdeg
    -- μ ≤ (2D+1) n + 2, P + B ≤ pbB
    have hmu' : pk.mu H ≤ (2 * D + 1) * n + 2 := by
      have : g * (n / g) ≤ n := Nat.mul_div_le n g
      have h2 : g * pk.mu H ≤ g * ((2 * D + 1) * n + 2) := by nlinarith
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    have hPB : pk.P H + pk.B H ≤ pbB c₀ pk.q D n := by
      unfold pbB
      have : c₀ * pk.mu H ≤ c₀ * ((2 * D + 1) * n + 2) := Nat.mul_le_mul_left _ hmu'
      omega
    refine ⟨T, ?_, ?_⟩
    · have hr := Stepped.ite_runs_false (M := Stepped.const (0 : ℤ)) hb'
        (Stepped.mapIn_runs (f := fun p => pk.prep (brWord g p)) (a := (aOf G, y))
          (by rw [hcode]; exact hrun))
      refine hr.mono le_rfl ?_
      have : C₁ * (pk.P H + pk.B H) ^ C₁ ≤ C₁ * pbB c₀ pk.q D n ^ C₁ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hPB _)
      unfold smB
      omega
    · -- the exponent
      have hX := exponent_le (q := pk.q) (U := (pk.net H).U) (P := pk.P H) (mu := pk.mu H) he0 he1 hK1
        hKg hmH hmu hU hP he hKδ
      set E₀ : ℕ := pk.q + 3 * (2 * c₀ * g + g * pk.q) + 2 * c₀ with hE₀
      set X : ℝ := e * ((pk.net H).U + (g : ℝ) * (pk.P H) / K) + 2 * ((g : ℝ) * (pk.P H)) / K with hXd
      have hτR : (pk.τ H : ℝ) ≤ (2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ) * ((pk.q * (n + 2) ^ pk.q : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; exact_mod_cast hτ
      have hPBR : ((pk.P H : ℝ) + pk.B H) ^ C₁ ≤ (pbB c₀ pk.q D n : ℝ) ^ C₁ := by
        gcongr; exact_mod_cast hPB
      have h2 : (2 : ℝ) ^ X * (2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (E₀ : ℝ) * (2 : ℝ) ^ (δ / 4 * n) := by
        rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      rw [show (2 : ℝ) ^ (E₀ : ℝ) = (2 : ℝ) ^ E₀ from Real.rpow_natCast 2 E₀] at h2
      calc (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ X * ((pk.P H : ℝ) + pk.B H) ^ C₁) * (pk.τ H) := hT
        _ ≤ 3 * (C₁ * (2 : ℝ) ^ X * (pbB c₀ pk.q D n : ℝ) ^ C₁) *
              ((2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ) * ((pk.q * (n + 2) ^ pk.q : ℕ) : ℝ)) := by
            gcongr
        _ = 3 * C₁ * (pbB c₀ pk.q D n : ℝ) ^ C₁ * ((pk.q * (n + 2) ^ pk.q : ℕ) : ℝ) *
              ((2 : ℝ) ^ X * (2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ)) := by ring
        _ ≤ 3 * C₁ * (pbB c₀ pk.q D n : ℝ) ^ C₁ * ((pk.q * (n + 2) ^ pk.q : ℕ) : ℝ) *
              ((2 : ℝ) ^ E₀ * (2 : ℝ) ^ (δ / 4 * n)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (wB g c₀ pk.q D C₁ n : ℝ) * (2 : ℝ) ^ (δ / 4 * n) := by
            unfold wB
            rw [← hE₀]
            push_cast
            have : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 4 * n) := by positivity
            nlinarith


/-- Polynomial bounds of the explicit functions of `n`. -/
theorem pol_pbB (c₀ q D : ℕ) : ∃ A, ∀ n, Pol A n (pbB c₀ q D n) :=
  ⟨_, fun _ => Pol.add (Pol.add (Pol.mul (Pol.const c₀)
    (Pol.add (Pol.mul (Pol.const (2 * D + 1)) Pol.id) (Pol.const 2))) (Pol.const q))
    (Pol.mul (Pol.const q) (Pol.pow_n q))⟩

theorem pol_smB (g c₀ q D C₁ : ℕ) : ∃ A, ∀ n, Pol A n (smB g c₀ q D C₁ n) := by
  obtain ⟨A, hA⟩ := pol_pbB c₀ q D
  exact ⟨_, fun n => Pol.add
    (Pol.add (Pol.add (Pol.add
      (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.mul Pol.id Pol.id)) (Pol.const 1)))
      (Pol.add (Pol.pow_n (4 * D * g)) (Pol.const 1))) (Pol.const 3))
    (Pol.add (Pol.add (Pol.mul (Pol.const q) (Pol.pow_n q))
      (Pol.mul (Pol.const C₁) (Pol.pow (hA n) C₁))) (Pol.const 5))⟩

theorem pol_wB (g c₀ q D C₁ : ℕ) : ∃ A, ∀ n, Pol A n (wB g c₀ q D C₁ n) := by
  obtain ⟨A, hA⟩ := pol_pbB c₀ q D
  exact ⟨_, fun n => Pol.add (Pol.mul (Pol.mul (Pol.const _) (Pol.pow (hA n) C₁))
    (Pol.mul (Pol.const q) (Pol.pow_n q))) (Pol.const 1)⟩

/-- **The machine, on every graph with at most `Dn` edges**: `#HC(G)` in binary, within
`A · 2^{(δ/2) n}` steps on states of size at most `A (n+2)^A`. -/
theorem hcM_runs (pk : HCPackage g c₀) (hNM : ComputesNetworks NM C₁ g K e)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK1 : 1 ≤ K) (hKg : K ≤ g) (hδ : 0 < δ) {D : ℕ}
    (he : e * c₀ * (D + 1) ≤ δ / 8) (hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K) :
    ∃ A : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
      ∃ T : ℕ, (hcM g NM pk).Runs (code G) T (A * (n + 2) ^ A) (Nat.bits (hamCycles G).card) ∧
        (T : ℝ) ≤ A * (2 : ℝ) ^ (δ / 2 * n) := by
  have hg1 : 1 ≤ g := hK1.trans hKg
  set q := pk.q
  obtain ⟨As, hAs⟩ := pol_smB g c₀ q D C₁
  obtain ⟨Aw, hAw⟩ := pol_wB g c₀ q D C₁
  -- the step bound, without the exponential factor
  have hZ : ∃ A, ∀ n, Pol A n ((n + 2) ^ (4 * D * g) * (wB g c₀ q D C₁ n + 1) + 2) :=
    ⟨_, fun n => Pol.add (Pol.mul (Pol.pow_n (4 * D * g)) (Pol.add (hAw n) (Pol.const 1))) (Pol.const 2)⟩
  obtain ⟨Az, hAz⟩ := hZ
  obtain ⟨Cp, hCp⟩ := exists_pow_le Az (show (0 : ℝ) < δ / 4 by positivity)
  -- the state bound
  have hSt : ∃ A, ∀ n, Pol A n ((2 * (n + 1 + n * n) + 1) + ((2 * n + 1) + (2 * (n * n) + 1)) +
      ((n + 2) ^ (4 * D * g) + 1) + ((n + 2) * (4 * D * g) + n + n * n + 1) +
      smB g c₀ q D C₁ n + (n + n * n + 1) + (2 * (n * n + 1) + 1) + 4) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)))
        (Pol.const 1))
      (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
        (Pol.add (Pol.mul (Pol.const 2) (Pol.mul Pol.id Pol.id)) (Pol.const 1))))
      (Pol.add (Pol.pow_n (4 * D * g)) (Pol.const 1)))
      (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 2)) (Pol.const (4 * D * g)))
        Pol.id) (Pol.mul Pol.id Pol.id)) (Pol.const 1)))
      (hAs n))
      (Pol.add (Pol.add Pol.id (Pol.mul Pol.id Pol.id)) (Pol.const 1)))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1))) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨Ast, hAst⟩ := hSt
  refine ⟨Ast + Az * Cp, fun {n} G _ hm => ?_⟩
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 4 * n) := Real.one_le_rpow one_le_two (by positivity)
  -- the branches
  choose! t ht using fun y (hy : y < nBr g (aOf G)) =>
    body_runs pk hNM he0 he1 hK1 hKg he hKδ G hm hy
  set N := nBr g (aOf G) with hN
  have hNle := nBr_le G hg1 hm
  set v : ℕ → ℤ := fun y => (n : ℤ) * ((hamCycles (brGraph G g y)).card : ℤ) with hv
  have hV : ∀ y < N, (v y).natAbs ≤ n * 2 ^ (n * n) := fun y _ => by
    simp only [hv, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (card_hamCycles_le _)
  have hsum := Stepped.sumRange_runs (M := bodyM g NM pk) (N := nBr g) (a := aOf G) t v
    (n * 2 ^ (n * n)) (smB g c₀ q D C₁ n) (fun y hy => (ht y hy).1) hV
  have hval : ∑ y ∈ range N, v y = (n : ℤ) * ((hamCycles G).card : ℤ) := by
    simp only [hv, ← Finset.mul_sum]
    rw [← Nat.cast_sum, sum_branches G g]
  rw [hval] at hsum
  have hmain : (mainM g NM pk).Runs (code G) _ _ ((n : ℤ) * ((hamCycles G).card : ℤ)) :=
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
  refine ⟨_, hrun.mono le_rfl ?_, ?_⟩
  · -- the state bound
    refine le_trans ?_ ((hAst n).mono (Nat.le_add_right _ _))
    have h1 : size (code G) = 2 * (n + 1 + n * n) + 1 := by
      rw [LabelSystem.size_word, length_code stMatrixLength]
    have h2 := size_aOf G
    have h3 : size (nBr g (aOf G)) ≤ (n + 2) ^ (4 * D * g) + 1 :=
      (size_nat_le' _).trans (by omega)
    have h4 : size (nBr g (aOf G) * (n * 2 ^ (n * n))) ≤ (n + 2) * (4 * D * g) + n + n * n + 1 := by
      apply size_nat_of_lt
      have e1 : (n + 2) ^ (4 * D * g) ≤ 2 ^ ((n + 2) * (4 * D * g)) :=
        calc (n + 2) ^ (4 * D * g) ≤ (2 ^ (n + 2)) ^ (4 * D * g) :=
              Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = 2 ^ ((n + 2) * (4 * D * g)) := (pow_mul _ _ _).symm
      have e2 : n < 2 ^ n := Nat.lt_two_pow_self
      calc nBr g (aOf G) * (n * 2 ^ (n * n)) ≤ 2 ^ ((n + 2) * (4 * D * g)) * (n * 2 ^ (n * n)) :=
            Nat.mul_le_mul_right _ (hNle.trans e1)
        _ < 2 ^ ((n + 2) * (4 * D * g)) * (2 ^ n * 2 ^ (n * n)) := by
            apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
            exact Nat.mul_lt_mul_of_pos_right e2 (by positivity)
        _ = _ := by rw [← pow_add, ← pow_add]; ring_nf
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
    rw [show size (code G, (n : ℤ) * ((hamCycles G).card : ℤ)) =
      size (code G) + size ((n : ℤ) * ((hamCycles G).card : ℤ)) from rfl]
    simp only [max_def]
    split_ifs <;> omega
  · -- the step bound
    have hT1 : ∀ y ∈ range N, ((t y + 1 : ℕ) : ℝ) ≤ (wB g c₀ q D C₁ n + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n) :=
      fun y hy => by
        have := (ht y (mem_range.1 hy)).2
        push_cast
        nlinarith
    have hsumT : ((∑ y ∈ range N, (t y + 1) : ℕ) : ℝ) ≤
        N * ((wB g c₀ q D C₁ n + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n)) := by
      push_cast
      have := Finset.sum_le_sum hT1
      simp only [sum_const, card_range, nsmul_eq_mul] at this
      push_cast at this
      linarith
    have hNR : (N : ℝ) ≤ ((n + 2) ^ (4 * D * g) : ℕ) := by exact_mod_cast hNle
    have hZn : ((((n + 2) ^ (4 * D * g) * (wB g c₀ q D C₁ n + 1) + 2 : ℕ)) : ℝ) ≤
        Az * ((n : ℝ) + 2) ^ Az := by
      have := hAz n
      unfold Pol at this
      exact_mod_cast this
    have hCpn := hCp n
    have e2 : (2 : ℝ) ^ (δ / 2 * n) = (2 : ℝ) ^ (δ / 4 * n) * (2 : ℝ) ^ (δ / 4 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    have hW0 : (0 : ℝ) ≤ ((wB g c₀ q D C₁ n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (δ / 4 * n) := by positivity
    calc (((∑ y ∈ range N, (t y + 1)) + 1 + 1 : ℕ) : ℝ)
        ≤ N * ((wB g c₀ q D C₁ n + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n)) + 2 := by push_cast at hsumT ⊢; linarith
      _ ≤ ((n + 2) ^ (4 * D * g) : ℕ) * ((wB g c₀ q D C₁ n + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n)) +
            2 * (2 : ℝ) ^ (δ / 4 * n) := by gcongr; linarith
      _ = ((((n + 2) ^ (4 * D * g) * (wB g c₀ q D C₁ n + 1) + 2 : ℕ)) : ℝ) * (2 : ℝ) ^ (δ / 4 * n) := by
            push_cast; ring
      _ ≤ (Az * ((n : ℝ) + 2) ^ Az) * (2 : ℝ) ^ (δ / 4 * n) := by gcongr
      _ ≤ (Az * (Cp * (2 : ℝ) ^ (δ / 4 * n))) * (2 : ℝ) ^ (δ / 4 * n) := by gcongr
      _ = (Az * Cp : ℕ) * (2 : ℝ) ^ (δ / 2 * n) := by rw [e2]; push_cast; ring
      _ ≤ ((Ast + Az * Cp : ℕ) : ℝ) * (2 : ℝ) ^ (δ / 2 * n) := by
            gcongr; exact_mod_cast Nat.le_add_left _ _

end Runs
end Asm

open Asm in
/-- **Theorem 1, Turing-machine level, from an HC network package.** Suppose that for some absolute
constant `c₀` there is an HC network package for every number `g ≥ 1` of nodes (`HCPackage g c₀`).
Then for every `δ > 0` and every `D` there are a Turing machine of Mathlib with finite alphabets and
a constant `C` such that, on the code `n` in unary followed by the adjacency matrix
(`GraphProblems.code`) of any graph `G` on `n` vertices with at most `D·n` edges, the machine halts
within `⌊C·2^{δn}⌋` steps with `#HC(G)` in binary (lowest bit first, `Nat.bits`). This is the form of
Corollary 7 of Anthropic's paper (`GraphProblems.CountsColoringsInTime`), restricted to `|E| ≤ Dn`. -/
theorem theorem1_TM (hpkg : ∃ c₀ : ℕ, ∀ g : ℕ, 1 ≤ g → Nonempty (HCPackage g c₀))
    (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        GraphProblems.Outputs M (code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨c₀, hpk⟩ := hpkg
  set η : ℝ := min 1 (δ / (8 * (c₀ + 1) * (D + 1))) with hηd
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨K, hK0, hach⟩ := Given.stEveryEta η hη (⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ + 2)
  obtain ⟨NM, C₁, hpoly, hNM⟩ := Printed.groupingLemma K η hach
  have hK1 : 1 ≤ K := by omega
  have hKg : K ≤ 3 * K ^ 8 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
      _ ≤ 3 * K ^ 8 := Nat.le_mul_of_pos_left _ (by norm_num)
  obtain ⟨pk⟩ := hpk (3 * K ^ 8) (hK1.trans hKg)
  have he : η * c₀ * (D + 1) ≤ δ / 8 := by
    have h1 : η ≤ δ / (8 * (c₀ + 1) * (D + 1)) := min_le_right _ _
    have h2 : η * c₀ * (D + 1) ≤ η * (c₀ + 1) * (D + 1) := by gcongr; linarith
    have h3 : η * (c₀ + 1) * (D + 1) ≤ δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) := by
      gcongr
    have h4 : δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) = δ / 8 := by
      field_simp
    linarith
  have hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K := by
    have h1 : 32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ ≤ K := by
      have := Nat.le_ceil (32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ)
      have h2 : ((⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ : ℕ) : ℝ) ≤ K := by
        exact_mod_cast (by omega : ⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ ≤ K)
      linarith
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  obtain ⟨A, hA⟩ := hcM_runs pk hNM hη.le (min_le_left _ _) hK1 hKg hδ he hKδ
  obtain ⟨inst⟩ := hcM_poly NM pk hpoly
  classical
  obtain ⟨M, C, hfin, hM⟩ := GraphProblems.tm_of_stepped (hcM (3 * K ^ 8) NM pk)
    (ι := Σ n : ℕ, {G : SimpleGraph (Fin n) // G.edgeFinset.card ≤ D * n})
    (fun x => code x.2.1) (fun x => Nat.bits (hamCycles x.2.1).card) (fun x => x.1) hδ A 2 2
    (fun x => by
      simp only [length_code stMatrixLength]
      nlinarith)
    (fun x => hA x.2.1 x.2.2)
  refine ⟨M, C, hfin, fun n G inst hm => ?_⟩
  obtain rfl : inst = fun a b => Classical.propDecidable (G.Adj a b) := Subsingleton.elim _ _
  exact hM ⟨n, G, hm⟩

/-! ## The package in the form of the label-sharing network (C1a, C1b) -/

/-- **An HC network package in label-sharing form**: the data that M7 (the network of Definition 5.1
as a `LabelSystem`) and C1c (the reader `lay`, the parity procedure `par`, the table procedure
`Tp`) supply, with exactly the hypotheses of `labelProcs_given` and `net_is`. The value is stated
as in `value_net`. `toHCPackage` turns it into an `HCPackage`. -/
structure LabelPackage (g c₀ : ℕ) : Type 1 where
  Ctx : Type
  [encCtx : Enc Ctx]
  [sizeCtx : HasSize Ctx]
  [carriedCtx : Carried Ctx]
  lay : Ctx → Lay
  lay_poly : PolyT lay
  par : Ctx × (ℕ × List Bool) → Bool
  par_poly : PolyT par
  Tp : Stepped (Ctx × WQ) ℤ
  Tp_poly : Nonempty (IsPolyT Tp)
  prep : List Bool → Ctx
  prep_poly : PolyT prep
  q : ℕ
  K : ∀ {n : ℕ}, SimpleGraph (Fin n) → Type
  R : ∀ {n : ℕ}, SimpleGraph (Fin n) → Type
  L : ∀ {n : ℕ}, SimpleGraph (Fin n) → Type
  fintypeK : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), Fintype (K G)
  decEqK : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), DecidableEq (K G)
  fintypeR : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), Fintype (R G)
  decEqR : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), DecidableEq (R G)
  fintypeL : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), Fintype (L G)
  decEqL : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), DecidableEq (L G)
  w : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  X : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), LabelSystem g (K G) (R G) (L G)
  C : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), LabelCode (L G) (w G)
  P : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  B : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  τ : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  S : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  mu : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  P_pos : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    1 ≤ P G
  B_pos : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    1 ≤ B G
  τ_pos : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    1 ≤ τ G
  hP : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    ∀ a, #(univ.filter ((X G).Inc a)) * w G + #(univ.filter ((X G).Touch a)) ≤ P G
  hT : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    ∀ a ℓ y, |(X G).T a ℓ y| < 2 ^ B G
  describes : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (X G).Describes (C G) (P G) (B G) (lay (prep (code G)))
  parSpec : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (X G).ParSpec (C G) par (prep (code G))
  tSpec : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n →
    (∀ v, 2 ≤ G.degree v) → (X G).TSpec (C G) Tp (prep (code G)) (τ G) (S G)
  value : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    ∑ ℓ : K G → L G, ∏ a, (X G).T a ℓ (fun j => (X G).par j ℓ) = (n : ℤ) * ((hamCycles G).card : ℤ)
  mu_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) → g * mu G ≤ 2 * G.edgeFinset.card + g * Δ
  U_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    2 * (Fintype.card (K G) * w G + Fintype.card (R G)) ≤ c₀ * (G.edgeFinset.card + n) + q
  P_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    P G ≤ c₀ * mu G + q
  B_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    B G ≤ q * (n + 2) ^ q
  τ_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    τ G ≤ 2 ^ (c₀ * mu G) * (q * (n + 2) ^ q)
  S_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 3 ≤ n → (∀ v, 2 ≤ G.degree v) →
    S G + 2 * size (prep (code G)) + 2 * g + 4 * P G + 8 ≤ q * (n + 2) ^ q

attribute [instance] LabelPackage.encCtx LabelPackage.sizeCtx LabelPackage.carriedCtx
  LabelPackage.fintypeK LabelPackage.decEqK LabelPackage.fintypeR LabelPackage.decEqR
  LabelPackage.fintypeL LabelPackage.decEqL

namespace LabelPackage

variable {g c₀ : ℕ} (lp : LabelPackage g c₀)

/-- **From the label-sharing form to an HC network package**, by `labelProcs_given` (C1b),
`net_is`, `value_net` and `U_eq` (C1a). -/
noncomputable def toHCPackage : HCPackage g c₀ where
  Ctx := lp.Ctx
  Np := labelProcs lp.lay lp.par lp.Tp
  keeps := labelProcs_keeps lp.lay_poly lp.par_poly lp.Tp_poly
  P_unary := Lay.P_unary lp.lay_poly
  B_unary := Lay.B_unary lp.lay_poly
  prep := lp.prep
  prep_poly := lp.prep_poly
  q := lp.q
  net G := (lp.X G).net (lp.C G)
  P G := lp.P G
  B G := lp.B G
  τ G := lp.τ G
  S G := lp.S G + size (lp.prep (code G)) + 2 * g + 4 * lp.P G + 8
  mu G := lp.mu G
  isNet G _ h3 hd :=
    (labelProcs_given (lp.X G) (lp.C G) lp.lay_poly lp.par_poly lp.Tp_poly
      ((lp.X G).net_is (lp.C G) (lp.P_pos G h3 hd) (lp.B_pos G h3 hd) (lp.hP G h3 hd) (lp.hT G h3 hd))
      (lp.describes G h3 hd) (lp.parSpec G h3 hd) (lp.tSpec G h3 hd) (lp.τ_pos G h3 hd)).1
  value G _ h3 hd := by rw [LabelSystem.value_net]; exact lp.value G h3 hd
  mu_le G _ h3 hd := lp.mu_le G h3 hd
  U_le G _ h3 hd := by rw [LabelSystem.U_eq]; exact lp.U_le G h3 hd
  P_le G _ h3 hd := lp.P_le G h3 hd
  B_le G _ h3 hd := lp.B_le G h3 hd
  τ_le G _ h3 hd := lp.τ_le G h3 hd
  S_le G _ h3 hd := by have := lp.S_le G h3 hd; omega

end LabelPackage

/-- **Theorem 1 (TM level) from label-sharing packages.** -/
theorem theorem1_TM_of_label (hpkg : ∃ c₀ : ℕ, ∀ g : ℕ, 1 ≤ g → Nonempty (LabelPackage g c₀))
    (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        GraphProblems.Outputs M (code G) (Nat.bits (hamCycles G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨c₀, h⟩ := hpkg
  exact theorem1_TM ⟨c₀, fun g hg => (h g hg).map LabelPackage.toHCPackage⟩ δ hδ D

end EthFollowup.ExactHC
