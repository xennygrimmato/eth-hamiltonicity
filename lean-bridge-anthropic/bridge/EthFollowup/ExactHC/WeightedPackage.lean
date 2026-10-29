/-
# The weighted (TSP) network package

The weighted analogue of `Package.lean` (C3): for every `g ≥ 1` a `TSPPackage g 6`, the data that the
TSP machine of `TSP.lean` consumes.

## The input word (`tspCode G W w`)
`code G` (n in unary, adjacency matrix), then `W` in unary (`unary W = 1^W 0`), then the `n²` weights
`w s(u, v)` in row-major order of the adjacency matrix, each as a block `wblock W k = 1^k 0 0^{W-k}`
of exactly `W + 1` bits (so the word has length `n + 1 + n² + W + 1 + n²(W + 1)`). The weights are in
unary: the Kronecker integer `n · Σ_H 2^{b·w(H)}` has about `b·n·W` bits, so no machine can write it
in time polynomial in the length of a binary encoding of the weights; the running time of the TSP
theorem is `2^{δn}·poly(n, W)`, polynomial in the length of this word.

## The context and the readers
* `TIn = GIn × (List Unit × List Bool)`: the graph as read by `read1`, `W` in unary, the weight
  blocks. `readT` reads it from `tspCode G W w` (`readT_code`), `wgt c u v` is the weight `w s(u, v)`
  (`wgt_cOf`).
* The precision `bK n = n² + n` (`bK_spec : n · 2^{|E|} < 2^{bK n}`, what `kronecker_decode` needs).
* `rdWW`: the reader of the weighted table procedure (`rdWW_desc : TDescW …`), `parWW`, `layWW`
  (the layout of `Package.lean` with `B = BWw = bK n · W · μ + 2μ + 1`).
* The weighted label system `XSW g G W w = (crossF g G).hcSystemW 0 (2^{bK n}) w`; its value is the
  Kronecker integer (`value_W`), and `Is (PW) (BWw)`.

## The package
`TSPPackage g c₀` mirrors `LabelPackage g c₀` (Assembly.lean) with the instances `(G, W, w)`
(`Good G W w`: `n ≥ 3`, minimum degree `≥ 2`, all weights `≤ W`) and the polynomial bounds in
`n + W` instead of `n`. `exists_tspPackage : ∃ c₀, ∀ g ≥ 1, Nonempty (TSPPackage g c₀)` (`c₀ = 6`).
-/
import EthFollowup.ExactHC.Package
import EthFollowup.ExactHC.WeightedNetwork
import EthFollowup.ExactHC.WeightedTableProc

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian

/-! ## The weighted system shares everything but `T` with the unweighted one -/

namespace Crossing

variable {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
  (X : Crossing G β m) (r : Fin n) (z : ℤ) (w : Sym2 (Fin n) → ℕ)

theorem hcSystemW_enc {q : ℕ} (C : LabelCode Label q) (a : Fin g)
    (x : (Fin m → Label) × (CopyIdx g → Bool)) :
    (X.hcSystemW r z w).enc C a x = (X.hcSystem r).enc C a x := rfl

theorem hcSystemW_locSet (a : Fin g) : (X.hcSystemW r z w).locSet a = (X.hcSystem r).locSet a := rfl

theorem hcSystemW_par : (X.hcSystemW r z w).par = (X.hcSystem r).par := rfl

theorem hcSystemW_rord : (X.hcSystemW r z w).rord = (X.hcSystem r).rord := rfl

theorem hcSystemW_source : (X.hcSystemW r z w).source = (X.hcSystem r).source := rfl

theorem hcSystemW_Inc : (X.hcSystemW r z w).Inc = (X.hcSystem r).Inc := rfl

theorem hcSystemW_Touch : (X.hcSystemW r z w).Touch = (X.hcSystem r).Touch := rfl

theorem hcSystemW_incList (a : Fin g) : (X.hcSystemW r z w).incList a = (X.hcSystem r).incList a := rfl

theorem hcSystemW_heldList (a : Fin g) :
    (X.hcSystemW r z w).heldList a = (X.hcSystem r).heldList a := rfl

theorem hcSystemW_pairData (a b : Fin g) :
    (X.hcSystemW r z w).pairData a b = (X.hcSystem r).pairData a b := rfl

end Crossing

/-! ## The precision -/

/-- The precision `b = n² + n`: `n · 2^{|E|} < 2^b` for every graph on `n` vertices. -/
def bK (n : ℕ) : ℕ := n * n + n

theorem card_edgeFinset_le_sq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ n * n :=
  calc G.edgeFinset.card ≤ (Fintype.card (Fin n)).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ n * n := by rw [Fintype.card_fin]; exact (Nat.choose_le_pow n 2).trans (by rw [pow_two])

theorem bK_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    n * 2 ^ G.edgeFinset.card < 2 ^ bK n := by
  unfold bK
  rw [pow_add]
  calc n * 2 ^ G.edgeFinset.card ≤ n * 2 ^ (n * n) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (card_edgeFinset_le_sq G))
    _ < 2 ^ (n * n) * 2 ^ n := by
        rw [mul_comm]
        exact Nat.mul_lt_mul_of_pos_left Nat.lt_two_pow_self (by positivity)

/-! ## The input word -/

/-- The weight `k ≤ W` as a block of `W + 1` bits: `1^k 0 0^{W-k}`. -/
def wblock (W k : ℕ) : List Bool := unary k ++ List.replicate (W - k) false

theorem length_wblock {W k : ℕ} (h : k ≤ W) : (wblock W k).length = W + 1 := by
  simp [wblock, unary]; omega

theorem ones_wblock (W k : ℕ) : ones (wblock W k) = k := Read.ones_unary_append k _

variable {n : ℕ}

/-- The `n²` weight blocks, in row-major order of the adjacency matrix. -/
noncomputable def wblocks (W : ℕ) (w : Sym2 (Fin n) → ℕ) : List (List Bool) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => wblock W (w s(u, v))

/-- The weight part of the input word. -/
noncomputable def wmat (W : ℕ) (w : Sym2 (Fin n) → ℕ) : List Bool := (wblocks W w).flatten

/-- **The input word of the TSP machine**: `code G`, `W` in unary, the `n²` weights as blocks of
`W + 1` bits in row-major order. -/
noncomputable def tspCode (G : SimpleGraph (Fin n)) (W : ℕ) (w : Sym2 (Fin n) → ℕ) : List Bool :=
  code G ++ (unary W ++ wmat W w)

theorem length_wblocks (W : ℕ) (w : Sym2 (Fin n) → ℕ) : (wblocks W w).length = n * n := by
  simp [wblocks, List.length_flatMap]

theorem mem_wblocks_length {W : ℕ} {w : Sym2 (Fin n) → ℕ} (hw : ∀ e, w e ≤ W) :
    ∀ b ∈ wblocks W w, b.length = W + 1 := by
  intro b hb
  simp only [wblocks, List.mem_flatMap, List.mem_map] at hb
  obtain ⟨u, -, v, -, rfl⟩ := hb
  exact length_wblock (hw _)

theorem length_wmat {W : ℕ} {w : Sym2 (Fin n) → ℕ} (hw : ∀ e, w e ≤ W) :
    (wmat W w).length = n * n * (W + 1) := by
  unfold wmat
  rw [List.length_flatten, List.map_congr_left fun b hb => mem_wblocks_length hw b hb,
    List.map_const', List.sum_replicate, smul_eq_mul, length_wblocks]

theorem length_tspCode (G : SimpleGraph (Fin n)) {W : ℕ} {w : Sym2 (Fin n) → ℕ} (hw : ∀ e, w e ≤ W) :
    (tspCode G W w).length = n + 1 + n * n + (W + 1 + n * n * (W + 1)) := by
  simp only [tspCode, List.length_append, length_code stMatrixLength, unary, List.length_replicate,
    List.length_cons, List.length_nil, length_wmat hw]

/-! ## Reading the input word -/

/-- The weight part of the context: `W` in unary, the weight blocks. -/
abbrev WIn : Type := List Unit × List Bool

/-- The context of the TSP machine: the graph as read by `read1`, and the weights. -/
abbrev TIn : Type := GIn × WIn

/-- **The reader of the input word.** -/
def readT (x : List Bool) : TIn :=
  ((List.replicate (ones x) (), (rest x).take (ones x * ones x)),
    (List.replicate (ones ((rest x).drop (ones x * ones x))) (),
      rest ((rest x).drop (ones x * ones x))))

/-- The context of the instance `(G, W, w)`. -/
noncomputable def cOf (G : SimpleGraph (Fin n)) (W : ℕ) (w : Sym2 (Fin n) → ℕ) : TIn :=
  (aOf G, (List.replicate W (), wmat W w))

theorem readT_code (G : SimpleGraph (Fin n)) (W : ℕ) (w : Sym2 (Fin n) → ℕ) :
    readT (tspCode G W w) = cOf G W w := by
  have hm : (matrix G).length = n * n := stMatrixLength n G
  unfold readT tspCode cOf aOf code
  rw [List.append_assoc, Read.ones_unary_append, Read.rest_unary_append, List.take_left' hm,
    List.drop_left' hm, Read.ones_unary_append, Read.rest_unary_append]

/-- The weight of the pair `(u, v)` read from the context. -/
def wgt (c : TIn) (u v : ℕ) : ℕ := ones (blk (c.2.1.length + 1) c.2.2 (u * c.1.1.length + v))

theorem blk_flatten (k : ℕ) : ∀ (bl : List (List Bool)), (∀ b ∈ bl, b.length = k) → ∀ i : ℕ,
    blk k bl.flatten i = bl.getD i []
  | [], _, i => by simp [blk]
  | b :: bl, hb, 0 => by
    rw [List.flatten_cons, blk_zero, List.take_left' (hb b List.mem_cons_self)]
    rfl
  | b :: bl, hb, i + 1 => by
    rw [List.flatten_cons, blk_succ, List.drop_left' (hb b List.mem_cons_self),
      blk_flatten k bl (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) i]
    rfl

theorem wgt_cOf (G : SimpleGraph (Fin n)) {W : ℕ} {w : Sym2 (Fin n) → ℕ} (hw : ∀ e, w e ≤ W)
    (u v : Fin n) : wgt (cOf G W w) u.val v.val = w s(u, v) := by
  unfold wgt cOf wmat
  simp only [List.length_replicate, aOf_len]
  rw [blk_flatten (W + 1) _ (mem_wblocks_length hw), wblocks,
    Read.getD_flatMap _ n [] v.2 _ (fun _ _ => by simp) u.val]
  simp [List.getD_eq_getElem?_getD, ones_wblock]

/-! ### Polynomial time -/

section Poly

variable {α : Type} [Enc α]

theorem readT_polyT : PolyT readT := by
  have h1 : PolyT fun x : List Bool => List.replicate (ones x) () := ones_unary PolyT.id'
  have h2 : PolyT fun x : List Bool => (rest x).drop (ones x * ones x) := by fun_prop
  have h3 : PolyT fun x : List Bool => List.replicate (ones ((rest x).drop (ones x * ones x))) () :=
    ones_unary h2
  unfold readT
  fun_prop

theorem wgt_unary {c : α → TIn} {u v : α → ℕ} (hc : PolyT c) (hu : PolyT u) (hv : PolyT v) :
    Unary fun x => wgt (c x) (u x) (v x) := by
  unfold wgt
  exact ones_unary (blk_polyT (by fun_prop) (by fun_prop) (by fun_prop))

theorem bK_unary {k : α → ℕ} (hk : Unary k) : Unary fun x => bK (k x) := by
  unfold bK
  exact (hk.mul hk).add hk

end Poly

/-! ## The readers of the weighted network -/

namespace Pkg

section Word

variable (g : ℕ)

/-- **The reader of the weighted table procedure**: the data of `rdW`, then `b` in unary, the weights
of the internal edges (in the order of `esW`) and the weights of the crossing edges (in the order
of `incW`), all in unary. -/
def rdWW (q : TIn × WQ) : TDW :=
  (rdW g (q.1.1, q.2),
    (List.replicate (bK q.1.1.1.length) (),
      ((esW g q.1.1 q.2.1).map fun p => List.replicate (wgt q.1 p.1 p.2) (),
        (incW g q.1.1 q.2.1).map fun k =>
          List.replicate (wgt q.1 (ceW g q.1.1 k).1 (ceW g q.1.1 k).2) ())))

/-- The parity procedure (that of `Package.lean`, on the graph part of the context). -/
def parWW (q : TIn × (ℕ × List Bool)) : Bool := parW g (q.1.1, q.2)

/-- `B = bK n · W · μ + 2μ + 1`. -/
def BWw (c : TIn) : ℕ := bK c.1.1.length * c.2.1.length * muW g c.1 + 2 * muW g c.1 + 1

/-- The layout: that of `Package.lean` with the bound `BWw`. -/
def layWW (c : TIn) : Lay :=
  ((((layW g c.1).1.1.1, List.replicate (BWw g c) ()), (layW g c.1).1.2), (layW g c.1).2)

theorem layWW_P (c : TIn) : (layWW g c).P = (layW g c.1).P := rfl
theorem layWW_w (c : TIn) : (layWW g c).w = (layW g c.1).w := rfl
theorem layWW_codes (c : TIn) : (layWW g c).codes = (layW g c.1).codes := rfl
theorem layWW_na (c : TIn) (a : ℕ) : (layWW g c).na a = (layW g c.1).na a := rfl
theorem layWW_nh (c : TIn) (a : ℕ) : (layWW g c).nh a = (layW g c.1).nh a := rfl
theorem layWW_pair (c : TIn) (a b : ℕ) : (layWW g c).pair a b = (layW g c.1).pair a b := rfl

theorem rdWW_polyT : PolyT (rdWW g) := by
  have h0 : PolyT fun q : TIn × WQ => rdW g (q.1.1, q.2) :=
    PolyT.comp (rdW_polyT g) (g := fun q : TIn × WQ => (q.1.1, q.2)) (by fun_prop)
  have h1 : PolyT fun q : TIn × WQ => List.replicate (bK q.1.1.1.length) () :=
    bK_unary (Unary.of_length (by fun_prop))
  have h2 : PolyT fun p : (TIn × WQ) × (ℕ × ℕ) => List.replicate (wgt p.1.1 p.2.1 p.2.2) () :=
    wgt_unary (by fun_prop) (by fun_prop) (by fun_prop)
  have h3 : PolyT fun p : (TIn × WQ) × ℕ =>
      List.replicate (wgt p.1.1 (ceW g p.1.1.1 p.2).1 (ceW g p.1.1.1 p.2).2) () :=
    wgt_unary (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rdWW
  fun_prop

theorem parWW_polyT : PolyT (parWW g) :=
  PolyT.comp (parW_polyT g) (g := fun q : TIn × (ℕ × List Bool) => (q.1.1, q.2)) (by fun_prop)

theorem BWw_unary : Unary (BWw g) := by
  unfold BWw
  have hmu : Unary fun c : TIn => muW g c.1 := (muW_unary g).comp (by fun_prop)
  exact (((bK_unary (Unary.of_length (by fun_prop))).mul (Unary.of_length (by fun_prop))).mul hmu).add
    (((Unary.const 2).mul hmu).add (Unary.const 1))

theorem layWW_polyT : PolyT (layWW g) := by
  have h1 : PolyT fun c : TIn => layW g c.1 := PolyT.comp (layW_polyT g) (by fun_prop)
  have h2 : PolyT fun c : TIn => List.replicate (BWw g c) () := BWw_unary g
  unfold layWW
  exact PolyT.prodMk (PolyT.prodMk (PolyT.prodMk (PolyT.fst (PolyT.fst (PolyT.fst h1))) h2)
    (PolyT.snd (PolyT.fst h1))) (PolyT.snd h1)

end Word

/-! ### Sizes -/

section Sizes

instance : SL Unit := ⟨fun _ => by rw [len_unit]; show 1 ≤ 2; omega⟩

theorem size_le_len_TDW (d : TDW) : size d ≤ len d := SL.le d

variable (g : ℕ)

/-- The polynomial bound on the word of the data read by `rdWW`. -/
noncomputable def cRW : ℕ := (rdWW_polyT g).choose_spec.choose

theorem len_rdWW (q : TIn × WQ) : len (rdWW g q) ≤ cRW g * (len q + 1) ^ cRW g :=
  (rdWW_polyT g).choose_spec.choose_spec.2 q

theorem size_rdWW (q : TIn × WQ) : size (rdWW g q) ≤ cRW g * (7 * size q + 1) ^ cRW g := by
  refine (size_le_len_TDW _).trans ((len_rdWW g q).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left ?_ _)))
  have := Carried.le q
  omega

/-- The size of the context of `(G, W, w)`. -/
def szC (n W : ℕ) : ℕ := (2 * n + 1 + (2 * (n * n) + 1)) + (2 * W + 1) + (2 * (n * n * (W + 1)) + 1)

theorem size_cOf (G : SimpleGraph (Fin n)) {W : ℕ} {w : Sym2 (Fin n) → ℕ} (hw : ∀ e, w e ≤ W) :
    size (cOf G W w) = szC n W := by
  show size (aOf G) + size ((List.replicate W (), wmat W w)) = _
  rw [size_aOf]
  simp only [szC, size_prod, size_units, LabelSystem.size_word, List.length_replicate, length_wmat hw]
  omega

/-- The state bound of the weighted table procedure. -/
noncomputable def SHW (g : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (W : ℕ) (w : Sym2 (Fin n) → ℕ) : ℕ :=
  2 * (cRW g * (7 * (size (cOf G W w) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cRW g) +
    9 * muW g (aOf G) + 2 * (bK n * W * muW g (aOf G)) + 9

end Sizes

/-! ## The graph side -/

noncomputable section Graph

variable {g : ℕ} [NeZero g] {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (W : ℕ)
  (w : Sym2 (Fin (n + 1)) → ℕ)

variable (g) in
/-- The weighted label system of `(G, W, w)`: Kronecker point `2^{bK (n+1)}`. -/
abbrev XW : LabelSystem g (Fin (mF g G)) (CopyIdx g) Label :=
  (crossF g G).hcSystemW 0 (2 ^ bK (n + 1)) w

theorem wes_eq (hw : ∀ e, w e ≤ W) (a : Fin g) :
    (esW g (aOf G) a.val).map (fun p => List.replicate (wgt (cOf G W w) p.1 p.2) ()) =
      (esF G a).map fun p => List.replicate (w (symP p)) () := by
  rw [← esF_val G a, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, valP, wgt_cOf G hw, symP]

theorem wcl_eq (hw : ∀ e, w e ≤ W) (a : Fin g) :
    (incW g (aOf G) a.val).map (fun k =>
        List.replicate (wgt (cOf G W w) (ceW g (aOf G) k).1 (ceW g (aOf G) k).2) ()) =
      (((crossF g G).chords.delta a).sort (· ≤ ·)).map fun k =>
        List.replicate (w ((crossF g G).edge k)) () := by
  rw [sort_delta G 0, ← incList_val G 0 a, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, ceW_eq, wgt_cOf G hw, Crossing.edge, crossF_s, crossF_t]

/-- **The reader produces the weighted data of the node table** (`TDescW`). -/
theorem rdWW_desc (hw : ∀ e, w e ≤ W) (a : Fin g) (x : (Fin (mF g G) → Label) × (CopyIdx g → Bool)) :
    TDescW G (crossF g G) 0 a x.1 (copyVec a x.2) w (bK (n + 1))
      (rdWW g (cOf G W w, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))) where
  r_eq := (rdW_desc G a x).r_eq
  a_eq := (rdW_desc G a x).a_eq
  va := (rdW_desc G a x).va
  vr_eq := (rdW_desc G a x).vr_eq
  es := ⟨esF G a, esF_nodup G a, mem_esF G a, (esF_val G a).symm, wes_eq G W w hw a⟩
  cl_eq := (rdW_desc G a x).cl_eq
  yl := (rdW_desc G a x).yl
  b_eq := by simp [rdWW, cOf]
  wcl_eq := wcl_eq G W w hw a

theorem BWw_cOf : BWw g (cOf G W w) = bK (n + 1) * W * muW g (aOf G) + 2 * muW g (aOf G) + 1 := by
  simp [BWw, cOf]

/-! ### The specifications -/

theorem hP_W (a : Fin g) :
    #(univ.filter ((XW g G w).Inc a)) * 3 + #(univ.filter ((XW g G w).Touch a)) ≤ PW g (aOf G) := by
  have h := hP_hc G a
  simp only [Crossing.hcSystemW_Inc, Crossing.hcSystemW_Touch]
  exact h

theorem hT_W (hw : ∀ e, w e ≤ W) (a : Fin g) (ℓ : Fin (mF g G) → Label) (y : CopyIdx g → Bool) :
    |(XW g G w).T a ℓ y| < 2 ^ BWw g (cOf G W w) := by
  rw [BWw_cOf]
  exact (crossF g G).abs_hcTW_lt 0 (2 ^ bK (n + 1)) w (muW g (aOf G)) W (bK (n + 1))
    (mu_le_muW G) hw (Crossing.abs_two_pow_le _) a ℓ y

theorem layWW_describes :
    (XW g G w).Describes labelCode (PW g (aOf G)) (BWw g (cOf G W w)) (layWW g (cOf G W w)) := by
  have h := layW_describes (g := g) G 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [layWW_P]; exact h.P_eq
  · simp [Lay.B, layWW]
  · rw [layWW_w]; exact h.w_eq
  · intro u; rw [layWW_codes]; exact h.codes_iff u
  · intro a; rw [layWW_na, Crossing.hcSystemW_incList]; exact h.na_eq a
  · intro a; rw [layWW_nh, Crossing.hcSystemW_heldList]; exact h.nh_eq a
  · intro a b hab; rw [layWW_pair, Crossing.hcSystemW_pairData]; exact h.pair_eq a b hab

theorem parSpec_W : (XW g G w).ParSpec labelCode (parWW g) (cOf G W w) := by
  intro j x hx
  rw [Crossing.hcSystemW_locSet, Crossing.hcSystemW_source] at hx
  rw [Crossing.hcSystemW_enc, Crossing.hcSystemW_par, Crossing.hcSystemW_rord,
    Crossing.hcSystemW_source]
  exact parSpec_hc G j x hx

theorem tSpec_W (hw : ∀ e, w e ≤ W) :
    (XW g G w).TSpec labelCode (tableProcW (rdWW g)) (cOf G W w) (τH g G) (SHW g G W w) := by
  intro a x _
  rw [Crossing.hcSystemW_T, Crossing.hcSystemW_enc]
  have h := tableProcW_runs G (crossF g G) (rdWW g) _ 0 a x.1 (copyVec a x.2) w (bK (n + 1))
    (rdWW_desc G W w hw a x) hw
  have hmu := mu_le_muW G a
  refine h.mono ?_ ?_
  · unfold τH
    exact Nat.mul_le_mul_left 2 ((steps_le_mu (crossF g G) a).trans
      (Nat.pow_le_pow_right (by norm_num) hmu))
  · have h2 := (crossF g G).two_Eint_add_delta_le a
    have hz : (((crossF g G).hcSystem 0).enc labelCode a x).length ≤ PW g (aOf G) := by
      rw [LabelSystem.length_enc]; exact (isNet_hc G).len_le a
    have hq := size_rdWW g (cOf G W w, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))
    have hs : size (cOf G W w, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x)) ≤
        size (cOf G W w) + (g + 1) + (2 * PW g (aOf G) + 1) := by
      show size (cOf G W w) + (size a.val + size (((crossF g G).hcSystem 0).enc labelCode a x)) ≤ _
      rw [LabelSystem.size_word]
      have := LabelSystem.size_fin' a
      omega
    have hq' : size (rdWW g (cOf G W w, (a.val, ((crossF g G).hcSystem 0).enc labelCode a x))) ≤
        cRW g * (7 * (size (cOf G W w) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cRW g :=
      hq.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have h3 : 12 * (Crossing.Eint G (βF g G) a).card + 9 * ((crossF g G).chords.delta a).card ≤
        9 * muW g (aOf G) := by omega
    have h4 : bK (n + 1) * (W * ((Crossing.Eint G (βF g G) a).card +
        ((crossF g G).chords.delta a).card)) ≤ bK (n + 1) * W * muW g (aOf G) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    unfold SHW
    omega

/-- **The value**: the Kronecker integer `(n+1) · Σ_H 2^{bK(n+1) · w(H)}`. -/
theorem value_W :
    ∑ ℓ : Fin (mF g G) → Label, ∏ a, (XW g G w).T a ℓ (fun j => (XW g G w).par j ℓ) =
      (((n + 1) * ∑ H ∈ hamCycles G, 2 ^ (bK (n + 1) * wt w H) : ℕ) : ℤ) := by
  rw [← LabelSystem.value_net (C := labelCode)]
  exact (crossF g G).hcNetW_kron_value_natCast 0 w labelCode (bK (n + 1))

end Graph

/-! ## The package -/

end Pkg

/-- The instances of the TSP package: `n ≥ 3`, minimum degree `≥ 2`, all weights `≤ W`. -/
def Good {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (w : Sym2 (Fin n) → ℕ) :
    Prop :=
  3 ≤ n ∧ (∀ v, 2 ≤ G.degree v) ∧ ∀ e, w e ≤ W

/-- **A TSP network package for `g` nodes** with the absolute constant `c₀`: `LabelPackage g c₀`
(Assembly.lean) for the weighted instances `(G, W, w)`. The value is the Kronecker integer
`n · Σ_{H ∈ HC(G)} 2^{bK n · w(H)}`; the bounds `B`, `τ`, `S` are polynomial in `n + W`; `U`, `P`,
`μ` are bounded as before (they do not depend on the weights). -/
structure TSPPackage (g c₀ : ℕ) : Type 1 where
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
  X : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), ℕ → (Sym2 (Fin n) → ℕ) → LabelSystem g (K G) (R G) (L G)
  C : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), LabelCode (L G) (w G)
  P : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  B : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → (Sym2 (Fin n) → ℕ) → ℕ
  τ : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  S : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → (Sym2 (Fin n) → ℕ) → ℕ
  mu : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ
  P_pos : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → 1 ≤ P G
  B_pos : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → 1 ≤ B G W wt
  τ_pos : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → 1 ≤ τ G
  hP : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → ∀ a, #(univ.filter ((X G W wt).Inc a)) * w G + #(univ.filter ((X G W wt).Touch a)) ≤ P G
  hT : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → ∀ a ℓ y, |(X G W wt).T a ℓ y| < 2 ^ B G W wt
  describes : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → (X G W wt).Describes (C G) (P G) (B G W wt) (lay (prep (tspCode G W wt)))
  parSpec : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → (X G W wt).ParSpec (C G) par (prep (tspCode G W wt))
  tSpec : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → (X G W wt).TSpec (C G) Tp (prep (tspCode G W wt)) (τ G) (S G W wt)
  value : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → ∑ ℓ : K G → L G, ∏ a, (X G W wt).T a ℓ (fun j => (X G W wt).par j ℓ) =
      ((n * ∑ H ∈ hamCycles G, 2 ^ (bK n * Hamiltonian.wt wt H) : ℕ) : ℤ)
  mu_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) → g * mu G ≤ 2 * G.edgeFinset.card + g * Δ
  U_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → 2 * (Fintype.card (K G) * w G + Fintype.card (R G)) ≤ c₀ * (G.edgeFinset.card + n) + q
  P_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → P G ≤ c₀ * mu G + q
  B_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → B G W wt ≤ q * (n + W + 2) ^ q
  τ_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → τ G ≤ 2 ^ (c₀ * mu G) * (q * (n + W + 2) ^ q)
  S_le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    Good G W wt → S G W wt + 2 * size (prep (tspCode G W wt)) + 2 * g + 4 * P G + 8 ≤ q * (n + W + 2) ^ q

attribute [instance] TSPPackage.encCtx TSPPackage.sizeCtx TSPPackage.carriedCtx
  TSPPackage.fintypeK TSPPackage.decEqK TSPPackage.fintypeR TSPPackage.decEqR
  TSPPackage.fintypeL TSPPackage.decEqL

namespace Pkg

section Package

variable (g : ℕ) [NeZero g]

/-- **The weighted label system of a graph** (`XW` for `n ≥ 1`; a dummy for `n = 0`). -/
noncomputable def XSW : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), ℕ → (Sym2 (Fin n) → ℕ) →
    LabelSystem g (Fin (mF g G)) (CopyIdx g) Label
  | 0, G, _, _ => baseSys g (crossF g G)
  | k + 1, G, _, wt => letI := Classical.decRel G.Adj; (crossF g G).hcSystemW 0 (2 ^ bK (k + 1)) wt

/-! ### The polynomial bounds in `n + W` -/

theorem pol_le {A N x y : ℕ} (h : Pol A N y) (hxy : x ≤ y) : Pol A N x := Pol.le h hxy

theorem muW_pol (n W : ℕ) (G : SimpleGraph (Fin n)) : Pol 4 (n + W) (muW g (aOf G)) := by
  have hmu : muW g (aOf G) ≤ n * n + n := by have := muW_le g (aOf G); simpa using this
  have hn : Pol 1 (n + W) n := Pol.le Pol.id (Nat.le_add_right n W)
  exact (Pol.add (Pol.mul hn hn) hn : Pol _ (n + W) (n * n + n)).le hmu

theorem bK_pol (n W : ℕ) : Pol 4 (n + W) (bK n) := by
  have hn : Pol 1 (n + W) n := Pol.le Pol.id (Nat.le_add_right n W)
  exact (Pol.add (Pol.mul hn hn) hn : Pol _ (n + W) (n * n + n))

theorem W_pol (n W : ℕ) : Pol 1 (n + W) W := Pol.le Pol.id (Nat.le_add_left W n)

theorem n_pol (n W : ℕ) : Pol 1 (n + W) n := Pol.le Pol.id (Nat.le_add_right n W)

theorem szC_pol (n W : ℕ) : ∃ A, Pol A (n + W) (szC n W) :=
  ⟨_, (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) (n_pol n W)) (Pol.const 1))
    (Pol.add (Pol.mul (Pol.const 2) (Pol.mul (n_pol n W) (n_pol n W))) (Pol.const 1)))
    (Pol.add (Pol.mul (Pol.const 2) (W_pol n W)) (Pol.const 1)))
    (Pol.add (Pol.mul (Pol.const 2) (Pol.mul (Pol.mul (n_pol n W) (n_pol n W))
      (Pol.add (W_pol n W) (Pol.const 1)))) (Pol.const 1)))⟩

theorem PW_pol (n W : ℕ) (G : SimpleGraph (Fin n)) : Pol (g ^ 2 + 20) (n + W) (PW g (aOf G)) := by
  unfold PW
  exact (Pol.add (Pol.add (Pol.mul (Pol.const 3) (muW_pol g n W G)) (Pol.const (g ^ 2)))
    (Pol.const 1)).mono (by omega)

theorem BWw_cOf_eq (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ) (wt : Sym2 (Fin n) → ℕ) :
    BWw g (cOf G W wt) = bK n * W * muW g (aOf G) + 2 * muW g (aOf G) + 1 := by
  simp [BWw, cOf]

theorem B_boundW : ∃ A : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    BWw g (cOf G W wt) ≤ A * (n + W + 2) ^ A :=
  ⟨_, fun n G W wt => (BWw_cOf_eq g n G W wt).le.trans
    ((Pol.add (Pol.add (Pol.mul (Pol.mul (bK_pol n W) (W_pol n W)) (muW_pol g n W G))
      (Pol.mul (Pol.const 2) (muW_pol g n W G))) (Pol.const 1)) : Pol _ (n + W) _)⟩

/-- The inner polynomial of the state bound. -/
noncomputable def Yb (N : ℕ) : ℕ :=
  7 * (8 * (N + 2) ^ 3 + (g + 1) + (2 * ((g ^ 2 + 20) * (N + 2) ^ (g ^ 2 + 20)) + 1)) + 1

/-- An explicit polynomial in `N = n + W` bounding `S + 2·size(prep) + 2g + 4P + 8`. -/
noncomputable def Eb (N : ℕ) : ℕ :=
  2 * (cRW g * Yb g N ^ cRW g) + 9 * (4 * (N + 2) ^ 4) +
    2 * (4 * (N + 2) ^ 4 * N * (4 * (N + 2) ^ 4)) + 9 + 2 * (8 * (N + 2) ^ 3) + 2 * g +
    4 * ((g ^ 2 + 20) * (N + 2) ^ (g ^ 2 + 20)) + 8

theorem Yb_pol : ∃ A, ∀ N, Pol A N (Yb g N) :=
  ⟨_, fun N => by unfold Yb; exact (Pol.add (Pol.mul (Pol.const 7) (Pol.add (Pol.add
    (Pol.mul (Pol.const 8) (Pol.pow_n 3)) (Pol.const (g + 1)))
    (Pol.add (Pol.mul (Pol.const 2) (Pol.mul (Pol.const (g ^ 2 + 20)) (Pol.pow_n (g ^ 2 + 20))))
      (Pol.const 1)))) (Pol.const 1) : Pol _ N _)⟩

theorem Eb_pol : ∃ A, ∀ N, Pol A N (Eb g N) := by
  obtain ⟨AY, hY⟩ := Yb_pol g
  exact ⟨_, fun N => by unfold Eb; exact (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add
    (Pol.mul (Pol.const 2) (Pol.mul (Pol.const (cRW g)) (Pol.pow (hY N) (cRW g))))
    (Pol.mul (Pol.const 9) (Pol.mul (Pol.const 4) (Pol.pow_n 4))))
    (Pol.mul (Pol.const 2) (Pol.mul (Pol.mul (Pol.mul (Pol.const 4) (Pol.pow_n 4)) Pol.id)
      (Pol.mul (Pol.const 4) (Pol.pow_n 4)))))
    (Pol.const 9))
    (Pol.mul (Pol.const 2) (Pol.mul (Pol.const 8) (Pol.pow_n 3))))
    (Pol.const (2 * g)))
    (Pol.mul (Pol.const 4) (Pol.mul (Pol.const (g ^ 2 + 20)) (Pol.pow_n (g ^ 2 + 20)))))
    (Pol.const 8) : Pol _ N _)⟩

theorem S_boundW : ∃ A : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ) (wt : Sym2 (Fin n) → ℕ),
    (∀ e, wt e ≤ W) →
      SHW g G W wt + 2 * size (cOf G W wt) + 2 * g + 4 * PW g (aOf G) + 8 ≤ A * (n + W + 2) ^ A := by
  have hsz : ∀ n W, szC n W ≤ 8 * (n + W + 2) ^ 3 := by
    intro n W
    unfold szC
    set N := n + W with hN
    have h1 : n ≤ N := by omega
    have h2 : W ≤ N := by omega
    have e3 : (N + 2) ^ 3 = N * N * N + 6 * (N * N) + 12 * N + 8 := by ring
    have a1 : n * n ≤ N * N := Nat.mul_le_mul h1 h1
    have a2 : n * n * (W + 1) ≤ N * N * (N + 1) := Nat.mul_le_mul a1 (by omega)
    have a3 : N * N * (N + 1) = N * N * N + N * N := by ring
    rw [e3]
    omega
  obtain ⟨A₀, hE⟩ := Eb_pol g
  refine ⟨A₀, fun n G W wt hw => le_trans ?_ (hE (n + W))⟩
  have hmu : muW g (aOf G) ≤ 4 * (n + W + 2) ^ 4 := muW_pol g n W G
  have hb : bK n ≤ 4 * (n + W + 2) ^ 4 := bK_pol n W
  have hP : PW g (aOf G) ≤ (g ^ 2 + 20) * (n + W + 2) ^ (g ^ 2 + 20) := PW_pol g n W G
  have hs : size (cOf G W wt) ≤ 8 * (n + W + 2) ^ 3 := by rw [size_cOf G hw]; exact hsz n W
  have hin : 7 * (size (cOf G W wt) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1 ≤ Yb g (n + W) := by
    unfold Yb; omega
  have hp : (7 * (size (cOf G W wt) + (g + 1) + (2 * PW g (aOf G) + 1)) + 1) ^ cRW g ≤
      Yb g (n + W) ^ cRW g :=
    Nat.pow_le_pow_left hin _
  have hp' := Nat.mul_le_mul_left (cRW g) hp
  have h5 : bK n * W * muW g (aOf G) ≤ 4 * (n + W + 2) ^ 4 * (n + W) * (4 * (n + W + 2) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul hb (by omega)) hmu
  unfold SHW Eb
  omega

end Package

section Package2

variable (g : ℕ)

/-- **A TSP network package for every `g ≥ 1`, with `c₀ = 6`.** -/
theorem tspPackage (hg : 1 ≤ g) : Nonempty (TSPPackage g 6) := by
  have : NeZero g := ⟨by omega⟩
  obtain ⟨A, hA⟩ := S_boundW g
  obtain ⟨A', hA'⟩ := B_boundW g
  refine ⟨{
    Ctx := TIn
    lay := layWW g
    lay_poly := layWW_polyT g
    par := parWW g
    par_poly := parWW_polyT g
    Tp := tableProcW (rdWW g)
    Tp_poly := tableProcW_poly (rdWW_polyT g)
    prep := readT
    prep_poly := readT_polyT
    q := A + A' + 2 * g ^ 3 + g ^ 2 + 2
    K := fun G => Fin (mF g G)
    R := fun _ => CopyIdx g
    L := fun _ => Label
    fintypeK := fun _ => inferInstance
    decEqK := fun _ => inferInstance
    fintypeR := fun _ => inferInstance
    decEqR := fun _ => inferInstance
    fintypeL := fun _ => inferInstance
    decEqL := fun _ => inferInstance
    w := fun _ => 3
    X := fun G W wt => XSW g G W wt
    C := fun _ => labelCode
    P := fun G => PW g (aOf G)
    B := fun G W wt => BWw g (cOf G W wt)
    τ := fun G => τH g G
    S := fun G W wt => SHW g G W wt
    mu := fun G => muW g (aOf G)
    P_pos := fun G _ _ _ _ => by unfold PW; omega
    B_pos := fun G _ _ _ _ => by unfold BWw; omega
    τ_pos := fun G _ _ _ _ => by
      unfold τH; have := Nat.one_le_pow (muW g (aOf G)) 8 (by norm_num); omega
    hP := fun {n} G inst W wt ⟨h3, _, hw⟩ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact hP_W G wt
    hT := fun {n} G inst W wt ⟨h3, _, hw⟩ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact hT_W G W wt hw
    describes := fun {n} G inst W wt ⟨h3, _, hw⟩ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show (XW g G wt).Describes labelCode (PW g (aOf G)) (BWw g (cOf G W wt)) (layWW g (readT (tspCode G W wt)))
      rw [readT_code]
      exact layWW_describes G W wt
    parSpec := fun {n} G inst W wt ⟨h3, _, hw⟩ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show (XW g G wt).ParSpec labelCode (parWW g) (readT (tspCode G W wt))
      rw [readT_code]
      exact parSpec_W G W wt
    tSpec := fun {n} G inst W wt ⟨h3, _, hw⟩ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      show (XW g G wt).TSpec labelCode (tableProcW (rdWW g)) (readT (tspCode G W wt)) (τH g G)
        (SHW g G W wt)
      rw [readT_code]
      exact tSpec_W G W wt hw
    value := fun {n} G inst W wt ⟨h3, _, hw⟩ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      exact value_W G wt
    mu_le := fun G _ _ _ _ Δ hΔ => g_muW_le G hΔ
    U_le := fun {n} G inst W wt ⟨h3, _, hw⟩ => by
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
      let _ : DecidableRel G.Adj := Classical.decRel _
      have h1 := card_m_le (g := g) G
      have h2 := Crossing.card_copyIdx_le g
      show 2 * (Fintype.card (Fin (mF g G)) * 3 + Fintype.card (CopyIdx g)) ≤ _
      rw [Fintype.card_fin]
      omega
    P_le := fun G _ _ _ _ => by unfold PW; omega
    B_le := fun {n} G _ W wt _ =>
      Pol.mono (B := A + A' + 2 * g ^ 3 + g ^ 2 + 2) (hA' n G W wt) (by omega)
    τ_le := fun {n} G _ W wt _ => by
      unfold τH
      have h8 : 8 ^ muW g (aOf G) ≤ 2 ^ (6 * muW g (aOf G)) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ≤ (A + A' + 2 * g ^ 3 + g ^ 2 + 2) * (n + W + 2) ^ (A + A' + 2 * g ^ 3 + g ^ 2 + 2) :=
        le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
      calc 2 * 8 ^ muW g (aOf G) ≤ 2 * 2 ^ (6 * muW g (aOf G)) := Nat.mul_le_mul_left 2 h8
        _ ≤ _ := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h2
    S_le := fun {n} G _ W wt ⟨_, _, hw⟩ => by
      show SHW g G W wt + 2 * size (readT (tspCode G W wt)) + 2 * g + 4 * PW g (aOf G) + 8 ≤ _
      rw [readT_code]
      exact Pol.mono (B := A + A' + 2 * g ^ 3 + g ^ 2 + 2) (hA n G W wt hw) (by omega) }⟩

end Package2

end Pkg

/-- **The hypothesis of the TSP theorem holds**: for `c₀ = 6` there is a TSP network package for
every number `g ≥ 1` of nodes. -/
theorem exists_tspPackage : ∃ c₀ : ℕ, ∀ g : ℕ, 1 ≤ g → Nonempty (TSPPackage g c₀) :=
  ⟨6, fun g hg => Pkg.tspPackage g hg⟩

end EthFollowup.ExactHC
