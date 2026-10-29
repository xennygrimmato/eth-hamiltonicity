/-
# The merged path sum, regrouped by nodes (math layer of Theorem Q1, part 2)

`research/quantum-circuits.md` §3.3. Mathlib only.

* `VPart`, `factorize`: a sum over all assignments of a finite set of bits, of a product of node
  factors each depending only on the *crossing* bits and its own *internal* bits, is the sum over the
  crossing bits of the product over nodes of the sums over their internal bits.
* `Good2`, `good2_scan`, `reader_unique`: structural invariants of the scan of `Circuit.lean`: an
  output leg is read by at most one block, and an output leg that a tail reads is read by no block.
* The circuit partition (`cpart`): the bits are the output legs `(t, i)` of the blocks; block `t`
  lies in node `t mod g`; the leg `(t, i)` is internal to a node if its producer and its reader lie
  there, and crossing otherwise. `pathSum_factor`: the merged path sum is the regrouped sum.
-/
import EthFollowup.Quantum.Circuit

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Finset

/-! ## Factorization over a partition of the bits -/

/-- A partition of the bits `V` into crossing bits `cl` and internal bits `il a` of the nodes `a`. -/
structure VPart (V : Type*) (g : ℕ) [DecidableEq V] where
  cl : List V
  il : Fin g → List V
  own : V → Fin g
  cl_nd : cl.Nodup
  il_nd : ∀ a, (il a).Nodup
  mem_il : ∀ v a, v ∈ il a ↔ v ∉ cl ∧ own v = a

namespace VPart

variable {V : Type*} [Fintype V] [DecidableEq V] {g : ℕ} (P : VPart V g)

/-- The bits seen by node `a`: crossing bits from `ℓ`, internal bits of `a` from `w`. -/
def glue (a : Fin g) (ℓ : Fin P.cl.length → Bool) (w : Fin (P.il a).length → Bool) : V → Bool :=
  fun v => if h : v ∈ P.cl then ℓ ⟨P.cl.idxOf v, List.idxOf_lt_length_of_mem h⟩
    else if h' : v ∈ P.il a then w ⟨(P.il a).idxOf v, List.idxOf_lt_length_of_mem h'⟩ else false

theorem mem_own (v : V) (h : v ∉ P.cl) : v ∈ P.il (P.own v) := (P.mem_il v _).2 ⟨h, rfl⟩

/-- Bits ↔ (crossing bits, internal bits of every node). -/
def split : (V → Bool) ≃ (Fin P.cl.length → Bool) × (∀ a, Fin (P.il a).length → Bool) where
  toFun σ := (fun k => σ (P.cl.get k), fun a i => σ ((P.il a).get i))
  invFun p := fun v => if h : v ∈ P.cl then p.1 ⟨P.cl.idxOf v, List.idxOf_lt_length_of_mem h⟩
    else p.2 (P.own v) ⟨(P.il (P.own v)).idxOf v, List.idxOf_lt_length_of_mem (P.mem_own v h)⟩
  left_inv σ := by
    funext v
    by_cases h : v ∈ P.cl
    · simp only [dif_pos h, List.get_eq_getElem, List.getElem_idxOf]
    · simp only [dif_neg h, List.get_eq_getElem, List.getElem_idxOf]
  right_inv p := by
    refine Prod.ext (funext fun k => ?_) (funext fun a => funext fun i => ?_)
    · have hk : P.cl.get k ∈ P.cl := List.get_mem _ _
      simp only [dif_pos hk]
      exact congrArg p.1 (Fin.ext (by simp only [List.get_eq_getElem]; exact List.Nodup.idxOf_getElem P.cl_nd _ _))
    · have hi : (P.il a).get i ∈ P.il a := List.get_mem _ _
      obtain ⟨hn, ho⟩ := (P.mem_il _ a).1 hi
      simp only [dif_neg hn]
      have key : ∀ (b : Fin g) (hb : b = a) (j : Fin (P.il b).length), j.val = i.val → p.2 b j = p.2 a i := by
        intro b hb j hj; subst hb; exact congrArg _ (Fin.ext hj)
      refine key _ ho _ ?_
      show (P.il (P.own ((P.il a).get i))).idxOf ((P.il a).get i) = i.val
      rw [ho]
      simp only [List.get_eq_getElem]
      exact List.Nodup.idxOf_getElem (P.il_nd a) _ _

theorem glue_split (σ : V → Bool) (a : Fin g) (v : V) (hv : v ∈ P.cl ∨ v ∈ P.il a) :
    P.glue a (P.split σ).1 ((P.split σ).2 a) v = σ v := by
  unfold glue split
  by_cases h : v ∈ P.cl
  · simp only [dif_pos h, Equiv.coe_fn_mk, List.get_eq_getElem, List.getElem_idxOf]
  · have h' : v ∈ P.il a := hv.resolve_left h
    simp only [dif_neg h, dif_pos h', Equiv.coe_fn_mk, List.get_eq_getElem, List.getElem_idxOf]

/-- **Factorization over a partition of the bits.** -/
theorem factorize {R : Type*} [CommRing R] (F : Fin g → (V → Bool) → R)
    (hloc : ∀ a σ σ', (∀ v, (v ∈ P.cl ∨ v ∈ P.il a) → σ v = σ' v) → F a σ = F a σ') :
    ∑ σ : V → Bool, ∏ a, F a σ =
      ∑ ℓ : Fin P.cl.length → Bool, ∏ a, ∑ w : Fin (P.il a).length → Bool, F a (P.glue a ℓ w) := by
  have h1 : ∀ ℓ : Fin P.cl.length → Bool, ∏ a, ∑ w : Fin (P.il a).length → Bool, F a (P.glue a ℓ w) =
      ∑ W : (∀ a, Fin (P.il a).length → Bool), ∏ a, F a (P.glue a ℓ (W a)) := by
    intro ℓ
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl fun ℓ _ => h1 ℓ]
  have h2 : ∑ p : (Fin P.cl.length → Bool) × (∀ a, Fin (P.il a).length → Bool),
      ∏ a, F a (P.glue a p.1 (p.2 a)) =
      ∑ ℓ : Fin P.cl.length → Bool, ∑ W : (∀ a, Fin (P.il a).length → Bool), ∏ a, F a (P.glue a ℓ (W a)) :=
    Fintype.sum_prod_type (fun p : (Fin P.cl.length → Bool) × (∀ a, Fin (P.il a).length → Bool) =>
      ∏ a, F a (P.glue a p.1 (p.2 a)))
  rw [← h2]
  refine Fintype.sum_equiv P.split _ _ fun σ => ?_
  exact Finset.prod_congr rfl fun a _ => hloc a _ _ fun v hv => (P.glue_split σ a v hv).symm

end VPart

/-! ## Structural invariants of the scan -/

/-- The default block. -/
def dBlk : Blk := (0, (0, 0), (none, none), ([], []))

/-- Block `t` of a state. -/
def blkAt (st : SS) (t : ℕ) : Blk := st.1.getD t dBlk

/-- The qubit of leg `i` of a block. -/
def legQ (blk : Blk) (i : Bool) : ℕ := if i then blk.2.1.2 else blk.2.1.1

/-- The source of leg `i` of a block. -/
def srcOf (blk : Blk) (i : Bool) : Src := if i then blk.2.2.1.2 else blk.2.2.1.1

/-- A block acts on qubit `q`. -/
def Touches (blk : Blk) (q : ℕ) : Prop := blk.2.1.1 = q ∨ blk.2.1.2 = q

/-- The invariant behind "one reader per leg". -/
structure Good2 (k : ℕ) (st : SS) : Prop where
  len : st.1.length = k
  cur : ∀ q t i, st.2.2.getD q none = some (t, i) →
    t < k ∧ legQ (blkAt st t) i = q ∧ ∀ t', t < t' → t' < k → ¬ Touches (blkAt st t') q
  src : ∀ t' j t i, t' < k → srcOf (blkAt st t') j = some (t, i) →
    t < t' ∧ legQ (blkAt st t) i = legQ (blkAt st t') j ∧
      ∀ t'', t < t'' → t'' < t' → ¬ Touches (blkAt st t'') (legQ (blkAt st t') j)
  dist : ∀ t, t < k → (blkAt st t).2.1.1 ≠ (blkAt st t).2.1.2

theorem getD_set' {α : Type*} (l : List α) (i j : ℕ) (a d : α) :
    (l.set i a).getD j d = if i = j ∧ i < l.length then a else l.getD j d := by
  by_cases h : i = j
  · subst h
    by_cases hi : i < l.length
    · rw [if_pos ⟨rfl, hi⟩]; exact getD_set_eq _ _ _ _ hi
    · rw [if_neg (fun h => hi h.2)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, hi,
        List.getElem?_eq_none (show l.length ≤ i by omega)]
  · rw [if_neg (fun h' => h h'.1)]; exact getD_set_ne _ _ _ h

theorem getD_some_lt {α : Type*} {l : List (Option α)} {q : ℕ} {v : α} (h : l.getD q none = some v) :
    q < l.length := by
  by_contra hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

theorem blkAt_append_lt (st : SS) (blk : Blk) {t : ℕ} (ht : t < st.1.length) :
    blkAt (st.1 ++ [blk], st.2) t = blkAt st t := by
  simp [blkAt, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem blkAt_append_eq (st : SS) (blk : Blk) : blkAt (st.1 ++ [blk], st.2) st.1.length = blk := by
  simp [blkAt, List.getD_eq_getElem?_getD]

theorem good2_init (n : ℕ) : Good2 0 (scanInit n) where
  len := rfl
  cur q t i h := by
    simp only [scanInit, List.getD_eq_getElem?_getD, List.getElem?_replicate] at h
    split_ifs at h <;> simp at h
  src _ _ _ _ h := absurd h (Nat.not_lt_zero _)
  dist _ h := absurd h (Nat.not_lt_zero _)

theorem good2_one {k : ℕ} {st : SS} (hg : Good2 k st) (u : ℕ) (hu : u < 7) (q : ℕ) :
    Good2 k (scanStep st (u, q, q)) := by
  simp only [scanStep, hu, ↓reduceIte]
  exact ⟨hg.len, hg.cur, hg.src, hg.dist⟩

theorem good2_two {k : ℕ} {st : SS} (hg : Good2 k st) (u : ℕ) (hu : ¬ u < 7) (q₁ q₂ : ℕ) (hq : q₁ ≠ q₂) :
    Good2 (k + 1) (scanStep st (u, q₁, q₂)) := by
  rw [scanStep_two _ _ _ _ hu]
  set blk := mkBlk st u q₁ q₂
  have hlen := hg.len
  -- blocks of the new state
  have hb : ∀ t, t < k → blkAt (st.1 ++ [blk], ((st.2.1.set q₁ []).set q₂ [],
      (st.2.2.set q₁ (some (st.1.length, false))).set q₂ (some (st.1.length, true)))) t = blkAt st t :=
    fun t ht => by simpa [blkAt] using blkAt_append_lt st blk (by omega)
  have hk : blkAt (st.1 ++ [blk], ((st.2.1.set q₁ []).set q₂ [],
      (st.2.2.set q₁ (some (st.1.length, false))).set q₂ (some (st.1.length, true)))) k = blk := by
    have := blkAt_append_eq st blk; rw [hlen] at this; simpa [blkAt] using this
  have hk0 : blkAt (st.1 ++ [blk], ((st.2.1.set q₁ []).set q₂ [],
      (st.2.2.set q₁ (some (st.1.length, false))).set q₂ (some (st.1.length, true)))) st.1.length = blk := by
    simpa [blkAt] using blkAt_append_eq st blk
  have hblk1 : blk.2.1.1 = q₁ := rfl
  have hblk2 : blk.2.1.2 = q₂ := rfl
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · -- the current sources
    intro q t i h
    rw [getD_set', List.length_set, getD_set'] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, ?_, fun t' a b => by omega⟩
      rw [hk0]; simp [legQ, hblk2, h1.1]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, ?_, fun t' a b => by omega⟩
      rw [hk0]; simp [legQ, hblk1, h2.1]
    · have hlt := getD_some_lt h
      have hq1 : q₁ ≠ q := fun e => h2 ⟨e, e ▸ hlt⟩
      have hq2 : q₂ ≠ q := fun e => h1 ⟨e, e ▸ hlt⟩
      obtain ⟨ht, hl, hn⟩ := hg.cur q t i h
      refine ⟨by omega, by rw [hb t ht]; exact hl, fun t' h1' h2' => ?_⟩
      by_cases ht' : t' < k
      · rw [hb t' ht']; exact hn t' h1' ht'
      · have : t' = k := by omega
        subst this; rw [hk]; simp only [Touches, hblk1, hblk2]; omega
  · -- the sources of the blocks
    intro t' j t i ht' hs
    by_cases hlt : t' < k
    · rw [hb t' hlt] at hs ⊢
      obtain ⟨h1, h2, h3⟩ := hg.src t' j t i hlt hs
      refine ⟨h1, by rw [hb t (by omega)]; exact h2, fun t'' a b => ?_⟩
      rw [hb t'' (by omega)]; exact h3 t'' a b
    · have : t' = k := by omega
      subst this
      rw [hk] at hs ⊢
      have hs' : st.2.2.getD (legQ blk j) none = some (t, i) := by
        cases j <;> simpa [srcOf, legQ, blk, mkBlk] using hs
      obtain ⟨h1, h2, h3⟩ := hg.cur _ _ _ hs'
      refine ⟨h1, by rw [hb t h1]; exact h2, fun t'' a b => ?_⟩
      rw [hb t'' b]; exact h3 t'' a b
  · intro t ht
    by_cases hlt : t < k
    · rw [hb t hlt]; exact hg.dist t hlt
    · have : t = k := by omega
      subst this; rw [hk]; exact hq

theorem foldl_good2 : ∀ (n : ℕ) (cs : List GC), (∀ c ∈ cs, ValidC n c) → ∀ (k : ℕ) (st : SS), Good2 k st →
    ∃ k', Good2 k' (cs.foldl scanStep st)
  | _, [], _, k, st, hg => ⟨k, hg⟩
  | n, c :: cs, hv, k, st, hg => by
    obtain ⟨u, q₁, q₂⟩ := c
    obtain ⟨_, _, h3⟩ := hv _ List.mem_cons_self
    have hv' : ∀ c ∈ cs, ValidC n c := fun c hc => hv c (List.mem_cons_of_mem _ hc)
    simp only [List.foldl_cons]
    by_cases hu : u < 7
    · have hstep : scanStep st (u, q₁, q₂) = scanStep st (u, q₁, q₁) := by simp [scanStep, hu]
      rw [hstep]
      exact foldl_good2 n cs hv' k _ (good2_one hg u hu q₁)
    · exact foldl_good2 n cs hv' (k + 1) _ (good2_two hg u hu q₁ q₂ (h3 (by omega)))

theorem good2_scan (n : ℕ) (cs : List GC) (hv : ∀ c ∈ cs, ValidC n c) :
    Good2 (scan n cs).1.length (scan n cs) := by
  obtain ⟨k', h⟩ := foldl_good2 n cs hv 0 (scanInit n) (good2_init n)
  unfold scan; rw [h.len]; exact h

/-- **One reader per leg**: two block inputs with the same source are the same input. -/
theorem reader_unique {k : ℕ} {st : SS} (hg : Good2 k st) {t₁ t₂ : ℕ} {j₁ j₂ : Bool} {v : ℕ × Bool}
    (h₁ : t₁ < k) (h₂ : t₂ < k) (e₁ : srcOf (blkAt st t₁) j₁ = some v) (e₂ : srcOf (blkAt st t₂) j₂ = some v) :
    t₁ = t₂ ∧ j₁ = j₂ := by
  obtain ⟨a₁, b₁, c₁⟩ := hg.src t₁ j₁ v.1 v.2 h₁ e₁
  obtain ⟨a₂, b₂, c₂⟩ := hg.src t₂ j₂ v.1 v.2 h₂ e₂
  have hq : legQ (blkAt st t₁) j₁ = legQ (blkAt st t₂) j₂ := b₁.symm.trans b₂
  have touch : ∀ t j, Touches (blkAt st t) (legQ (blkAt st t) j) := fun t j => by
    cases j <;> simp [legQ, Touches]
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact absurd (hq ▸ touch t₁ j₁) (c₂ t₁ a₁ h)
  · subst h
    refine ⟨rfl, ?_⟩
    by_contra hj
    have hd := hg.dist t₁ h₁
    cases j₁ <;> cases j₂ <;> simp_all [legQ]
  · exact absurd (hq.symm ▸ touch t₂ j₂) (c₁ t₂ a₂ h)

/-- **A leg read by a tail is read by no block.** -/
theorem tail_no_reader {k : ℕ} {st : SS} (hg : Good2 k st) {q : ℕ} {v : ℕ × Bool}
    (hc : st.2.2.getD q none = some v) {t' : ℕ} {j : Bool} (ht' : t' < k)
    (e : srcOf (blkAt st t') j = some v) : False := by
  obtain ⟨a₁, b₁, c₁⟩ := hg.cur q v.1 v.2 hc
  obtain ⟨a₂, b₂, -⟩ := hg.src t' j v.1 v.2 ht' e
  apply c₁ t' a₂ ht'
  rw [← b₁, b₂]
  cases j <;> simp [legQ, Touches]

/-! ## The circuit partition and the regrouped path sum -/

section Circ

variable {R : Type*} [CommRing R] (I : Interp R) {n : ℕ} (st : SS) (g : ℕ) [NeZero g]

/-- The node of block `t`. -/
def grp (t : ℕ) : Fin g := ⟨t % g, Nat.mod_lt _ (NeZero.pos g)⟩

/-- Block `blk` reads the leg `v`. -/
def readsB (blk : Blk) (v : ℕ × Bool) : Bool :=
  decide (srcOf blk false = some v) || decide (srcOf blk true = some v)

/-- The block that reads the leg `v` (the first one; there is at most one). -/
def reader (v : ℕ × Bool) : Option ℕ := (List.range st.1.length).find? fun t => readsB (blkAt st t) v

/-- The node of the reader of `v` (that of its producer if no block reads it). -/
def rg (v : ℕ × Bool) : Fin g :=
  match reader st v with
  | some t => grp g t
  | none => grp g v.1

/-- The node of the tail of qubit `q` (that of the producer of the leg it reads; `0` if none). -/
def tailGrp (q : ℕ) : Fin g :=
  match st.2.2.getD q none with
  | some v => grp g v.1
  | none => 0

/-- All legs, in the order `(0,0), (0,1), (1,0), …`. -/
def allV (G : ℕ) : List (Fin G × Bool) := List.finRange G ×ˢ [false, true]

theorem allV_nodup (G : ℕ) : (allV G).Nodup :=
  (List.nodup_finRange G).product (by decide)

theorem mem_allV {G : ℕ} (v : Fin G × Bool) : v ∈ allV G := by
  rcases v with ⟨t, b⟩
  simp only [allV, List.mem_product, List.mem_finRange, true_and]
  cases b <;> simp

/-- A leg is crossing if its producer and its reader lie in different nodes. -/
def crossB (v : Fin st.1.length × Bool) : Bool := decide (grp g v.1.val ≠ rg st g (v.1.val, v.2))

/-- **The circuit partition** of the legs into crossing legs and internal legs of the nodes. -/
def cpart : VPart (Fin st.1.length × Bool) g where
  cl := (allV st.1.length).filter (crossB st g)
  il a := (allV st.1.length).filter fun v => !crossB st g v && decide (grp g v.1.val = a)
  own v := grp g v.1.val
  cl_nd := (allV_nodup _).filter _
  il_nd _ := (allV_nodup _).filter _
  mem_il v a := by simp [List.mem_filter, mem_allV]

/-- The output legs as pairs. -/
def oV {G : ℕ} (σ : Fin G × Bool → Bool) : Fin G → Bool × Bool := fun t => (σ (t, false), σ (t, true))

/-- The factor of node `a`: its blocks and its tails. -/
def nodeF (x y : Basis n) (a : Fin g) (σ : Fin st.1.length × Bool → Bool) : R :=
  (∏ t ∈ Finset.univ.filter (fun t : Fin st.1.length => grp g t.val = a), blockF I x (oV σ) t.val (blkAt st t.val)) *
    ∏ q ∈ Finset.univ.filter (fun q : Fin n => tailGrp st g q.val = a), tailF I x (oV σ) st y q

theorem Wp_eq_prod {k : ℕ} (x : Basis n) (o : Fin k → Bool × Bool) :
    ∀ (bs : List Blk) (t₀ : ℕ), Wp I x o t₀ bs = ∏ i : Fin bs.length, blockF I x o (t₀ + i.val) (bs.getD i.val dBlk)
  | [], _ => by simp [Wp]
  | b :: bs, t₀ => by
    rw [Wp, Wp_eq_prod x o bs (t₀ + 1)]
    show _ = ∏ i : Fin (bs.length + 1), _
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, add_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show t₀ + 1 + i.val = t₀ + (i.val + 1) by ring]

/-- `(Fin G × Bool → Bool) ≃ (Fin G → Bool × Bool)`. -/
def oE (G : ℕ) : (Fin G × Bool → Bool) ≃ (Fin G → Bool × Bool) where
  toFun := oV
  invFun o v := if v.2 then (o v.1).2 else (o v.1).1
  left_inv σ := by funext v; rcases v with ⟨t, b⟩; cases b <;> rfl
  right_inv o := by funext t; rfl

/-- **The merged path sum, regrouped by nodes.** -/
theorem pathSum_regroup (x y : Basis n) :
    pathSum I x st st.1.length y = ∑ σ : Fin st.1.length × Bool → Bool, ∏ a, nodeF I st g x y a σ := by
  unfold pathSum
  refine (Fintype.sum_equiv (oE st.1.length).symm _ _ fun o => ?_)
  have ho : oV ((oE st.1.length).symm o) = o := (oE st.1.length).apply_symm_apply o
  simp only [nodeF, Finset.prod_mul_distrib, ho]
  rw [Finset.prod_fiberwise Finset.univ (fun t : Fin st.1.length => grp g t.val)
      (fun t => blockF I x o t.val (blkAt st t.val)),
    Finset.prod_fiberwise Finset.univ (fun q : Fin n => tailGrp st g q.val) (fun q => tailF I x o st y q),
    Wp_eq_prod I x o st.1 0]
  simp only [zero_add, blkAt]

/-! ### Locality of the node factors -/

theorem reader_eq {k : ℕ} (hg : Good2 k st) (hk : st.1.length = k) {t : ℕ} (ht : t < k) {j : Bool}
    {v : ℕ × Bool} (e : srcOf (blkAt st t) j = some v) : reader st v = some t := by
  have hp : readsB (blkAt st t) v = true := by cases j <;> simp [readsB, e]
  have hs : ((List.range st.1.length).find? fun t => readsB (blkAt st t) v).isSome := by
    rw [List.find?_isSome]; exact ⟨t, List.mem_range.2 (hk ▸ ht), hp⟩
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs
  have h1 := List.find?_some hs'
  have h2 := List.mem_range.1 (List.mem_of_find?_eq_some hs')
  have h3 : ∃ j', srcOf (blkAt st s) j' = some v := by
    simp only [readsB, Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · exact ⟨false, h1⟩
    · exact ⟨true, h1⟩
  obtain ⟨j', h3⟩ := h3
  have := (reader_unique hg (hk ▸ h2) ht h3 e).1
  unfold reader; rw [hs', this]

theorem attached_mem {a : Fin g} {v : Fin st.1.length × Bool}
    (h : grp g v.1.val = a ∨ rg st g (v.1.val, v.2) = a) :
    v ∈ (cpart st g).cl ∨ v ∈ (cpart st g).il a := by
  by_cases hc : crossB st g v = true
  · left; simp [cpart, List.mem_filter, mem_allV, hc]
  · right
    have hc' : grp g v.1.val = rg st g (v.1.val, v.2) := by simpa [crossB] using hc
    simp only [cpart, List.mem_filter, mem_allV, true_and, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq]
    exact ⟨by simpa using hc, by rcases h with h | h <;> [exact h; exact hc'.trans h]⟩

theorem rd_oV {G : ℕ} {σ σ' : Fin G × Bool → Bool} {t : ℕ} (h : ∀ (ht : t < G) b, σ (⟨t, ht⟩, b) = σ' (⟨t, ht⟩, b)) :
    rd (oV σ) t = rd (oV σ') t := by
  unfold rd oV
  split_ifs with ht
  · rw [h ht false, h ht true]
  · rfl

theorem sv_oV {G : ℕ} (x : Basis n) {σ σ' : Fin G × Bool → Bool} (q : ℕ) (s : Src)
    (h : ∀ t i, s = some (t, i) → ∀ (ht : t < G), σ (⟨t, ht⟩, i) = σ' (⟨t, ht⟩, i)) :
    sv x (oV σ) q s = sv x (oV σ') q s := by
  rcases s with _ | ⟨t, i⟩
  · rfl
  · cases i <;> simp only [sv, rd, oV, Bool.false_eq_true, ↓reduceIte] <;> split_ifs with ht
    · simp [h t _ rfl ht]
    · rfl
    · simp [h t _ rfl ht]
    · rfl

/-- **The node factors are local**: node `a` sees only the crossing legs and its own internal legs. -/
theorem nodeF_local (hg : Good n st.1.length st) (hg2 : Good2 st.1.length st) (x y : Basis n) (a : Fin g)
    (σ σ' : Fin st.1.length × Bool → Bool)
    (h : ∀ v, (v ∈ (cpart st g).cl ∨ v ∈ (cpart st g).il a) → σ v = σ' v) :
    nodeF I st g x y a σ = nodeF I st g x y a σ' := by
  unfold nodeF
  congr 1
  · refine Finset.prod_congr rfl fun t ht => ?_
    have hta : grp g t.val = a := (Finset.mem_filter.1 ht).2
    have hout : rd (oV σ) t.val = rd (oV σ') t.val := rd_oV fun ht' b => h _ (attached_mem st g (Or.inl hta))
    have hin : ∀ j, sv x (oV σ) ((blkAt st t.val).2.1.1) (srcOf (blkAt st t.val) j) =
        sv x (oV σ') ((blkAt st t.val).2.1.1) (srcOf (blkAt st t.val) j) ∧
        sv x (oV σ) ((blkAt st t.val).2.1.2) (srcOf (blkAt st t.val) j) =
        sv x (oV σ') ((blkAt st t.val).2.1.2) (srcOf (blkAt st t.val) j) := by
      intro j
      have key : ∀ t' i, srcOf (blkAt st t.val) j = some (t', i) → ∀ (ht' : t' < st.1.length),
          σ (⟨t', ht'⟩, i) = σ' (⟨t', ht'⟩, i) := by
        intro t' i hs ht'
        refine h _ (attached_mem st g (Or.inr ?_))
        show rg st g (t', i) = a
        unfold rg; rw [reader_eq st hg2 rfl t.2 hs]; exact hta
      exact ⟨sv_oV x _ _ key, sv_oV x _ _ key⟩
    have e1 : srcOf (blkAt st t.val) false = (blkAt st t.val).2.2.1.1 := rfl
    have e2 : srcOf (blkAt st t.val) true = (blkAt st t.val).2.2.1.2 := rfl
    have h1 := (hin false).1
    have h2 := (hin true).2
    rw [e1] at h1; rw [e2] at h2
    unfold blockF
    rw [hout, h1, h2]
  · refine Finset.prod_congr rfl fun q hq => ?_
    have hqa : tailGrp st g q.val = a := (Finset.mem_filter.1 hq).2
    unfold tailF
    congr 2
    refine sv_oV x _ _ fun t i hs ht => h _ (attached_mem st g (Or.inl ?_))
    unfold tailGrp at hqa; rw [hs] at hqa; exact hqa

/-- **The circuit path sum, factorized over the nodes.** -/
theorem cmat_factor (cs : List GC) (hv : ∀ c ∈ cs, ValidC n c) (x y : Basis n) :
    cmat (n := n) I cs y x =
      ∑ ℓ : Fin (cpart (scan n cs) g).cl.length → Bool, ∏ a,
        ∑ w : Fin ((cpart (scan n cs) g).il a).length → Bool,
          nodeF I (scan n cs) g x y a ((cpart (scan n cs) g).glue a ℓ w) := by
  rw [cmat_eq_pathSum I cs hv, pathSum_regroup I (scan n cs) g]
  exact VPart.factorize _ _ fun a σ σ' h =>
    nodeF_local I (scan n cs) g (good_scan cs hv) (good2_scan n cs hv) x y a σ σ' h

end Circ

end EthFollowup.Quantum
