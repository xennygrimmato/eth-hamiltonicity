import EthFollowup.Barriers.KstarBasic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

/-!
# Theorem L: `k*(H_t) = Ω(log t)` for the crossing grid (`research/kstar.md` §3)

`H_t = H_{t,t}`: vertices `r_{a,b}`, `c_{a,b}` (`a, b < t`), row paths `r_{a,0} − … − r_{a,t−1}`,
column paths `c_{0,b} − … − c_{t−1,b}` and rungs `r_{a,b} − c_{a,b}`; it is `G − r` for the rooted
graph of the note (root attached to `r_{0,0}`). Here it is `gridAdj t` on `Fin (2t²)`.

* `gridAdj_symm`, `gridAdj_irrefl`, `gridAdj_degree_le`: a simple graph of maximum degree `≤ 3`.
* Lemma L3 (`lift`, `lift_nodup`, `lift_adj`, `lift_inRange`, `isDirCycle_enc`): for rows
  `a0 < a1 < a2 < a3` and columns `b0 < b1 < b2 < b3` (`< t`) the balanced 24-cycle `B` of
  `H_{4,4}` lifts to a directed simple cycle of `H_t` (in the sense of `Kstar.isDirCycle`).
* Lemma L1 for these cycles (`cycleSum_lift`): the label sum of the lift is the sum of the eight
  corner contributions `phiA/phiB/phiC/phiD` (rung turns plus prefix sums of straight turns).
* Ramsey step (`grid_ramsey`): an iterated pigeonhole (rows, then 4-sets of columns) instead of
  Kővári–Sós–Turán; with `N = 16^k` colours, `T(k) = 3N·C(3N+1,4) + 1 ≤ 2^(20k+10)` rows suffice.
* Theorem L (`not_good_of_thr_le`, `theoremL`, `theoremL_log`): a good `k`-bit labelling of `H_t`
  forces `t < 2^(20k+10)`, i.e. `k*(H_t) ≥ (log₂ t − 10)/20`.
-/

namespace Kstar

/-! ## Open-walk turn lists -/

section Lists

variable {α : Type*}

/-- `tAux p l q`: the turns `(v; prev, next)` at the vertices of `l`, where the vertex before `l`
is `p` and the vertex after `l` is `q`. -/
def tAux : α → List α → α → List (α × α × α)
  | _, [], _ => []
  | p, [y], q => [(y, p, q)]
  | p, y :: z :: l, q => (y, p, z) :: tAux y (z :: l) q

theorem zip_eq_tAux : ∀ (p : α) (l : List α) (q : α),
    l.zip ((p :: l.dropLast).zip (l.tail ++ [q])) = tAux p l q
  | _, [], _ => by simp [tAux]
  | p, [y], q => by simp [tAux]
  | p, y :: z :: l, q => by
    have ih := zip_eq_tAux y (z :: l) q
    simp only [List.tail_cons] at ih
    rw [List.dropLast_cons_cons, tAux, ← ih]
    simp

theorem turns_eq_tAux (x : α) (r : List α) :
    turns (x :: r) = tAux ((x :: r).getLast (List.cons_ne_nil x r)) (x :: r) x := by
  rw [← zip_eq_tAux]
  unfold turns
  congr 2
  · rw [List.rotate_eq_drop_append_take (by simp), List.drop_length_sub_one (List.cons_ne_nil x r),
      ← List.dropLast_eq_take]
    rfl
  · simp

theorem tAux_append : ∀ (p : α) (S T : List α) (q x y : α), S.getLast? = some x → T.head? = some y →
    tAux p (S ++ T) q = tAux p S y ++ tAux x T q
  | _, [], _, _, _, _, h, _ => by simp at h
  | p, [s], T, q, x, y, hS, hT => by
    obtain ⟨T', rfl⟩ : ∃ T', T = y :: T' := by
      cases T with
      | nil => simp at hT
      | cons y' T' => simp at hT; exact ⟨T', by rw [hT]⟩
    simp at hS; subst hS
    simp [tAux]
  | p, s :: s' :: S, T, q, x, y, hS, hT => by
    have ih := tAux_append s (s' :: S) T q x y (by simpa using hS) hT
    simp only [List.cons_append] at ih ⊢
    rw [tAux, ih, tAux]
    rfl

theorem tAux_snoc (p : α) (S : List α) (q x y : α) (hS : S.getLast? = some x) :
    tAux p (S ++ [y]) q = tAux p S y ++ [(y, x, q)] := by
  rw [tAux_append p S [y] q x y hS rfl]; rfl

/-- swap the two neighbours of a turn. -/
def swT (τ : α × α × α) : α × α × α := (τ.1, τ.2.2, τ.2.1)

theorem tAux_reverse (p : α) : ∀ (l : List α) (q : α),
    tAux p l.reverse q = ((tAux q l p).map swT).reverse
  | [], _ => by simp [tAux]
  | [x], q => by simp [tAux, swT]
  | x :: z :: l, q => by
    have ih := tAux_reverse p (z :: l) x
    rw [List.reverse_cons, tAux_snoc p _ q z x (by simp), ih, tAux]
    simp [swT]

end Lists

/-! ## Straight segments -/

section Segments

variable {α : Type*}

/-- the segment `f s, f (s+1), …, f e`. -/
def segUp (f : ℕ → α) (s e : ℕ) : List α := (List.range' s (e + 1 - s)).map f

/-- the segment `f s, f (s-1), …, f e` (for `e ≤ s`). -/
def segDown (f : ℕ → α) (s e : ℕ) : List α := (segUp f e s).reverse

theorem segUp_succ (f : ℕ → α) {s e : ℕ} (h : s ≤ e) :
    segUp f s (e + 1) = segUp f s e ++ [f (e + 1)] := by
  unfold segUp
  rw [show e + 1 + 1 - s = (e + 1 - s) + 1 by omega, List.range'_concat]
  simp only [List.map_append, List.map_cons, List.map_nil]
  congr 3; omega

theorem segUp_self (f : ℕ → α) (s : ℕ) : segUp f s s = [f s] := by
  simp [segUp]

theorem segUp_getLast? (f : ℕ → α) {s e : ℕ} (h : s ≤ e) : (segUp f s e).getLast? = some (f e) := by
  induction e, h using Nat.le_induction with
  | base => simp [segUp_self]
  | succ e he _ => rw [segUp_succ f he]; simp

theorem segUp_head? (f : ℕ → α) {s e : ℕ} (h : s ≤ e) : (segUp f s e).head? = some (f s) := by
  unfold segUp
  rw [show e + 1 - s = (e - s) + 1 by omega, List.range'_succ]
  simp

theorem segDown_getLast? (f : ℕ → α) {s e : ℕ} (h : e ≤ s) : (segDown f s e).getLast? = some (f e) := by
  simp [segDown, List.getLast?_reverse, segUp_head? f h]

theorem segDown_head? (f : ℕ → α) {s e : ℕ} (h : e ≤ s) : (segDown f s e).head? = some (f s) := by
  simp [segDown, List.head?_reverse, segUp_getLast? f h]

theorem mem_segUp (f : ℕ → α) (s e : ℕ) (x : α) : x ∈ segUp f s e ↔ ∃ y, s ≤ y ∧ y ≤ e ∧ f y = x := by
  simp only [segUp, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩; exact ⟨y, h1, by omega, rfl⟩
  · rintro ⟨y, h1, h2, rfl⟩; exact ⟨y, ⟨h1, by omega⟩, rfl⟩

theorem mem_segDown (f : ℕ → α) (s e : ℕ) (x : α) : x ∈ segDown f s e ↔ ∃ y, e ≤ y ∧ y ≤ s ∧ f y = x := by
  simp only [segDown, List.mem_reverse, mem_segUp]

theorem nodup_segUp {f : ℕ → α} (hf : Function.Injective f) (s e : ℕ) : (segUp f s e).Nodup :=
  (List.nodup_range').map hf

theorem nodup_segDown {f : ℕ → α} (hf : Function.Injective f) (s e : ℕ) : (segDown f s e).Nodup :=
  List.nodup_reverse.mpr (nodup_segUp hf e s)

/-- the middle (straight) turns of a segment from `s+1` to `e-1`. -/
def midsUp (f : ℕ → α) (s e : ℕ) : List (α × α × α) :=
  (List.range' (s + 1) (e - s - 1)).map (fun x => (f x, f (x - 1), f (x + 1)))

theorem tAux_segUp (f : ℕ → α) {s e : ℕ} (h : s < e) : ∀ p q : α,
    tAux p (segUp f s e) q = (f s, p, f (s + 1)) :: (midsUp f s e ++ [(f e, f (e - 1), q)]) := by
  induction e, h using Nat.le_induction with
  | base =>
    intro p q
    have : segUp f s (s + 1) = [f s, f (s + 1)] := by
      rw [segUp_succ f le_rfl, segUp_self]; rfl
    rw [this]; simp [tAux, midsUp]
  | succ e he ih =>
    intro p q
    rw [segUp_succ f (by omega), tAux_snoc p _ q (f e) _ (segUp_getLast? f (by omega)), ih]
    simp only [midsUp, List.cons_append, List.append_assoc, List.cons.injEq, true_and]
    rw [show e + 1 - s - 1 = (e - s - 1) + 1 by omega, List.range'_concat]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    rw [show s + 1 + 1 * (e - s - 1) = e by omega]
    simp

end Segments

/-! ## The crossing grid `H_t`

Vertices are coded as triples `(κ, a, b)` with `κ ∈ {0,1}` (`0`: row vertex `r_{a,b}`,
`1`: column vertex `c_{a,b}`) and `a, b < t`, and the triple `(κ, a, b)` is the vertex
`κ·t² + a·t + b` of `Fin (2t²)`. -/

/-- adjacency of `H_{t,t}` on triples: row paths, column paths and rungs. -/
def tadj (x y : ℕ × ℕ × ℕ) : Prop :=
  (x.1 = 0 ∧ y.1 = 0 ∧ x.2.1 = y.2.1 ∧ (y.2.2 = x.2.2 + 1 ∨ x.2.2 = y.2.2 + 1)) ∨
  (x.1 = 1 ∧ y.1 = 1 ∧ x.2.2 = y.2.2 ∧ (y.2.1 = x.2.1 + 1 ∨ x.2.1 = y.2.1 + 1)) ∨
  (x.2.1 = y.2.1 ∧ x.2.2 = y.2.2 ∧ ((x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 1 ∧ y.1 = 0)))

instance (x y : ℕ × ℕ × ℕ) : Decidable (tadj x y) := by unfold tadj; infer_instance

/-- decoding a vertex of `Fin (2t²)` into its triple. -/
def dec (t : ℕ) (v : Fin (2 * t * t)) : ℕ × ℕ × ℕ := (v.val / (t * t), v.val % (t * t) / t, v.val % t)

/-- **The crossing grid** `H_t = H_{t,t}` on the vertex set `Fin (2t²)` (this is `G − r`). -/
def gridAdj (t : ℕ) : Fin (2 * t * t) → Fin (2 * t * t) → Bool :=
  fun u v => decide (tadj (dec t u) (dec t v))

/-- the code of a triple. -/
def code (t : ℕ) (x : ℕ × ℕ × ℕ) : ℕ := x.1 * (t * t) + x.2.1 * t + x.2.2

/-- encoding a triple as a vertex (meaningful for in-range triples). -/
def enc (t : ℕ) (ht : 0 < t) (x : ℕ × ℕ × ℕ) : Fin (2 * t * t) :=
  ⟨code t x % (2 * t * t), Nat.mod_lt _ (Nat.mul_pos (Nat.mul_pos two_pos ht) ht)⟩

/-- in-range triples. -/
def InRange (t : ℕ) (x : ℕ × ℕ × ℕ) : Prop := x.1 < 2 ∧ x.2.1 < t ∧ x.2.2 < t

theorem code_lt {t : ℕ} {x : ℕ × ℕ × ℕ} (hx : InRange t x) : code t x < 2 * t * t := by
  obtain ⟨h1, h2, h3⟩ := hx
  unfold code
  have : x.2.1 * t + x.2.2 < t * t := by nlinarith
  have : x.1 * (t * t) ≤ 1 * (t * t) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem dec_enc {t : ℕ} (ht : 0 < t) {x : ℕ × ℕ × ℕ} (hx : InRange t x) : dec t (enc t ht x) = x := by
  obtain ⟨k, a, b⟩ := x
  obtain ⟨h1, h2, h3⟩ := hx
  simp only at h1 h2 h3
  have hlt := code_lt (t := t) (x := (k, a, b)) ⟨h1, h2, h3⟩
  have hr : a * t + b < t * t := by nlinarith
  have htt : 0 < t * t := by positivity
  simp only [dec, enc]
  rw [Nat.mod_eq_of_lt hlt]
  simp only [code]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    rw [add_assoc, Nat.mul_comm k, Nat.mul_add_div htt, Nat.div_eq_of_lt hr, add_zero]
  · simp only
    rw [add_assoc, Nat.mul_comm k, Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mul_comm a,
      Nat.mul_add_div ht, Nat.div_eq_of_lt h3, add_zero]
  · simp only
    rw [show k * (t * t) + a * t + b = (k * t + a) * t + b by ring, Nat.mul_comm, Nat.mul_add_mod,
      Nat.mod_eq_of_lt h3]

theorem enc_injOn {t : ℕ} (ht : 0 < t) {x y : ℕ × ℕ × ℕ} (hx : InRange t x) (hy : InRange t y)
    (h : enc t ht x = enc t ht y) : x = y := by
  rw [← dec_enc ht hx, ← dec_enc ht hy, h]

theorem val_eq_of_dec {t : ℕ} (v : Fin (2 * t * t)) :
    v.val = (dec t v).1 * (t * t) + (dec t v).2.1 * t + (dec t v).2.2 := by
  simp only [dec]
  have h1 := Nat.div_add_mod v.val (t * t)
  have h2 := Nat.div_add_mod (v.val % (t * t)) t
  have h3 : v.val % (t * t) % t = v.val % t := Nat.mod_mod_of_dvd _ (Dvd.intro_left _ rfl)
  rw [h3] at h2
  nlinarith

theorem dec_injective (t : ℕ) : Function.Injective (dec t) := by
  intro u v h
  apply Fin.ext
  rw [val_eq_of_dec u, val_eq_of_dec v, h]

/-! ### `H_t` is a simple graph of maximum degree at most `3` with `2t²` vertices -/

theorem gridAdj_symm (t : ℕ) (u v : Fin (2 * t * t)) : gridAdj t u v = gridAdj t v u := by
  simp only [gridAdj, tadj]
  apply Bool.decide_congr
  omega

theorem gridAdj_irrefl (t : ℕ) (u : Fin (2 * t * t)) : gridAdj t u u = false := by
  simp only [gridAdj, tadj, decide_eq_false_iff_not]
  omega

theorem card_vertices (t : ℕ) : Fintype.card (Fin (2 * t * t)) = 2 * t * t := Fintype.card_fin _

/-- the (at most three) possible neighbours of a triple. -/
def nbrs (x : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  if x.1 = 0 then {(0, x.2.1, x.2.2 + 1), (0, x.2.1, x.2.2 - 1), (1, x.2.1, x.2.2)}
  else {(1, x.2.1 + 1, x.2.2), (1, x.2.1 - 1, x.2.2), (0, x.2.1, x.2.2)}

theorem mem_nbrs {x y : ℕ × ℕ × ℕ} (h : tadj x y) : y ∈ nbrs x := by
  obtain ⟨k, a, b⟩ := x
  obtain ⟨k', a', b'⟩ := y
  simp only [tadj] at h
  unfold nbrs
  split_ifs with hk <;> simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] <;> omega

theorem card_nbrs_le (x : ℕ × ℕ × ℕ) : (nbrs x).card ≤ 3 := by
  unfold nbrs
  split_ifs <;> exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _))

/-- **Maximum degree `≤ 3`.** -/
theorem gridAdj_degree_le (t : ℕ) (v : Fin (2 * t * t)) :
    (Finset.univ.filter (fun u => gridAdj t v u = true)).card ≤ 3 := by
  refine le_trans (Finset.card_le_card_of_injOn (dec t) ?_ (dec_injective t).injOn) (card_nbrs_le (dec t v))
  intro u hu
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, gridAdj,
    decide_eq_true_eq] at hu
  exact mem_nbrs hu

/-! ## Turns, cyclic pairs and relabelling -/

section Transfer

variable {α β : Type*}

theorem turns_eq_of (l : List α) (p q : α) (hp : l.getLast? = some p) (hq : l.head? = some q) :
    turns l = tAux p l q := by
  cases l with
  | nil => simp at hp
  | cons x r =>
    simp only [List.head?_cons, Option.some.injEq] at hq
    subst hq
    rw [turns_eq_tAux]
    congr 1
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x r)] at hp
    exact Option.some.inj hp

theorem zip_zip_proj : ∀ (l A B : List α), B.length ≤ A.length →
    (l.zip (A.zip B)).map (fun τ => (τ.1, τ.2.2)) = l.zip B
  | [], _, _, _ => rfl
  | _ :: _, _, [], _ => by simp
  | _ :: _, [], _ :: _, h => by simp at h
  | x :: l, a :: A, b :: B, h => by
    simp [zip_zip_proj l A B (by simpa using h)]

theorem cyclicPairs_eq (l : List α) : cyclicPairs l = (turns l).map (fun τ => (τ.1, τ.2.2)) := by
  unfold cyclicPairs turns
  rw [zip_zip_proj]
  simp

theorem turns_map (g : α → β) (l : List α) :
    turns (l.map g) = (turns l).map (fun τ => (g τ.1, g τ.2.1, g τ.2.2)) := by
  unfold turns
  rw [List.length_map, ← List.map_rotate, ← List.map_rotate, List.zip_map, List.zip_map]
  rfl

theorem cyclicPairs_map (g : α → β) (l : List α) :
    cyclicPairs (l.map g) = (cyclicPairs l).map (Prod.map g g) := by
  unfold cyclicPairs
  rw [← List.map_rotate, List.zip_map]

theorem cycleSum_map {k : ℕ} (g : α → β) (F : β → β → β → (Fin k → ZMod 2)) (l : List α) :
    cycleSum F (l.map g) = cycleSum (fun x y z => F (g x) (g y) (g z)) l := by
  unfold cycleSum
  rw [turns_map, List.map_map]
  rfl

end Transfer

/-- A list of in-range triples that is a directed cycle of the triple graph maps to a directed
cycle of `H_t`. -/
theorem isDirCycle_enc {t : ℕ} (ht : 0 < t) (L : List (ℕ × ℕ × ℕ)) (hlen : 3 ≤ L.length)
    (hnd : L.Nodup) (hin : ∀ x ∈ L, InRange t x) (hadj : ∀ τ ∈ turns L, tadj τ.1 τ.2.2) :
    isDirCycle (gridAdj t) (L.map (enc t ht)) = true := by
  simp only [isDirCycle, Bool.and_eq_true, decide_eq_true_eq, List.length_map, List.all_eq_true]
  refine ⟨⟨hlen, ?_⟩, ?_⟩
  · exact hnd.map_on (fun x hx y hy h => enc_injOn ht (hin x hx) (hin y hy) h)
  · intro p hp
    rw [cyclicPairs_map, List.mem_map] at hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hp
    have hx : x ∈ L := List.of_mem_zip hxy |>.1
    have hy : y ∈ L := (List.mem_rotate).mp (List.of_mem_zip hxy |>.2)
    rw [cyclicPairs_eq, List.mem_map] at hxy
    obtain ⟨τ, hτ, hτe⟩ := hxy
    simp only [Prod.mk.injEq] at hτe
    simp only [Prod.map, gridAdj, decide_eq_true_eq, dec_enc ht (hin x hx), dec_enc ht (hin y hy)]
    rw [← hτe.1, ← hτe.2]
    exact hadj τ hτ

/-! ## Piece sums and piece adjacency (the local form of Lemma L1) -/

section Pieces

variable {α M : Type*} [AddCommGroup M]

/-- prefix sum of the straight turns in increasing direction. -/
def strUp (F : α → α → α → M) (f : ℕ → α) (y : ℕ) : M :=
  ((List.range y).map (fun x => F (f x) (f (x - 1)) (f (x + 1)))).sum

/-- prefix sum of the straight turns in decreasing direction. -/
def strDn (F : α → α → α → M) (f : ℕ → α) (y : ℕ) : M :=
  ((List.range y).map (fun x => F (f x) (f (x + 1)) (f (x - 1)))).sum

theorem sum_range'_eq (g : ℕ → M) {s e : ℕ} (h : s < e) :
    ((List.range' (s + 1) (e - s - 1)).map g).sum
      = ((List.range e).map g).sum - ((List.range (s + 1)).map g).sum := by
  have hr : List.range e = List.range (s + 1) ++ List.range' (s + 1) (e - s - 1) := by
    rw [List.range_eq_range', List.range_eq_range']
    have := @List.range'_append 0 (s + 1) (e - s - 1) 1
    simp only [one_mul, zero_add] at this
    rw [this]; congr 1; omega
  rw [hr, List.map_append, List.sum_append]; abel

/-- the label sum of an increasing piece. -/
theorem sum_tAux_segUp (F : α → α → α → M) (f : ℕ → α) {s e : ℕ} (h : s < e) (p q : α) :
    ((tAux p (segUp f s e) q).map (fun τ => F τ.1 τ.2.1 τ.2.2)).sum
      = F (f s) p (f (s + 1)) + (strUp F f e - strUp F f (s + 1)) + F (f e) (f (e - 1)) q := by
  rw [tAux_segUp f h, midsUp]
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    List.map_nil, List.sum_nil]
  rw [strUp, strUp, ← sum_range'_eq _ h]
  simp only [Function.comp_def]
  abel

/-- the label sum of a decreasing piece. -/
theorem sum_tAux_segDown (F : α → α → α → M) (f : ℕ → α) {s e : ℕ} (h : e < s) (p q : α) :
    ((tAux p (segDown f s e) q).map (fun τ => F τ.1 τ.2.1 τ.2.2)).sum
      = F (f e) (f (e + 1)) q + (strDn F f s - strDn F f (e + 1)) + F (f s) p (f (s - 1)) := by
  rw [segDown, tAux_reverse, List.map_reverse, List.sum_reverse, List.map_map, tAux_segUp f h, midsUp]
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    List.map_nil, List.sum_nil, Function.comp_def, swT]
  rw [strDn, strDn, ← sum_range'_eq _ h]
  abel

theorem adj_tAux_segUp (R : α → α → Prop) (f : ℕ → α) {s e : ℕ} (h : s < e) (p q : α)
    (hR : ∀ x, s ≤ x → x < e → R (f x) (f (x + 1))) (hq : R (f e) q) :
    ∀ τ ∈ tAux p (segUp f s e) q, R τ.1 τ.2.2 := by
  rw [tAux_segUp f h, midsUp]
  intro τ hτ
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range'_1, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | ⟨x, ⟨h1, h2⟩, rfl⟩ | rfl
  · exact hR s le_rfl h
  · exact hR x (by omega) (by omega)
  · exact hq

theorem adj_tAux_segDown (R : α → α → Prop) (f : ℕ → α) {s e : ℕ} (h : e < s) (p q : α)
    (hR : ∀ x, e < x → x ≤ s → R (f x) (f (x - 1))) (hq : R (f e) q) :
    ∀ τ ∈ tAux p (segDown f s e) q, R τ.1 τ.2.2 := by
  rw [segDown, tAux_reverse, tAux_segUp f h, midsUp]
  intro τ hτ
  simp only [List.mem_reverse, List.map_cons, List.map_append, List.map_map, List.mem_cons,
    List.mem_append, List.mem_map, List.mem_range'_1, List.map_nil, List.not_mem_nil, or_false,
    Function.comp_def, swT] at hτ
  rcases hτ with rfl | ⟨x, ⟨h1, h2⟩, rfl⟩ | rfl
  · exact hq
  · have := hR x (by omega) (by omega); simpa using this
  · exact hR s h le_rfl

end Pieces

/-! ## Lemma L3: the lifted balanced cycle

The balanced 24-cycle `B` of `H_{4,4}` (Lemma L2, `kstar.md` §3), vertex list
`r00 r01 r02 r03 c03 c13 c23 c33 r33 r32 r31 c31 c21 c11 r11 r12 c12 c22 r22 r21 r20 c20 c10 c00`,
lifted to rows `a0 < a1 < a2 < a3` and columns `b0 < b1 < b2 < b3`: eight straight segments
(row `a0` right, column `b3` down, row `a3` left, column `b1` up, row `a1` right, column `b2` down,
row `a2` left, column `b0` up), consecutive segments joined by rungs. -/

/-- row vertex `r_{a,x}`. -/
def rowF (a : ℕ) (x : ℕ) : ℕ × ℕ × ℕ := (0, a, x)
/-- column vertex `c_{y,b}`. -/
def colF (b : ℕ) (y : ℕ) : ℕ × ℕ × ℕ := (1, y, b)

theorem rowF_injective (a : ℕ) : Function.Injective (rowF a) := fun x y h => by
  simpa [rowF] using h
theorem colF_injective (b : ℕ) : Function.Injective (colF b) := fun x y h => by
  simpa [colF] using h

/-- the lift of the balanced cycle `B` (as a list of triples). -/
def lift (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) : List (ℕ × ℕ × ℕ) :=
  segUp (rowF a0) b0 b3 ++ (segUp (colF b3) a0 a3 ++ (segDown (rowF a3) b3 b1 ++
  (segDown (colF b1) a3 a1 ++ (segUp (rowF a1) b1 b2 ++ (segUp (colF b2) a1 a2 ++
  (segDown (rowF a2) b2 b0 ++ segDown (colF b0) a2 a0))))))

/-- order hypotheses on the chosen rows and columns. -/
structure Ord8 (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) : Prop where
  ha01 : a0 < a1
  ha12 : a1 < a2
  ha23 : a2 < a3
  hb01 : b0 < b1
  hb12 : b1 < b2
  hb23 : b2 < b3

section LiftLemmas

variable {a0 a1 a2 a3 b0 b1 b2 b3 : ℕ}

theorem head?_append_of {α : Type*} {S T : List α} {y : α} (h : S.head? = some y) :
    (S ++ T).head? = some y := by simp [List.head?_append, h]

theorem getLast?_append_of {α : Type*} {S T : List α} {x : α} (h : T.getLast? = some x) :
    (S ++ T).getLast? = some x := by simp [List.getLast?_append, h]

/-- the turns of the lift, split into its eight pieces. -/
theorem lift_turns (h : Ord8 a0 a1 a2 a3 b0 b1 b2 b3) :
    turns (lift a0 a1 a2 a3 b0 b1 b2 b3) =
      tAux (colF b0 a0) (segUp (rowF a0) b0 b3) (colF b3 a0) ++
      (tAux (rowF a0 b3) (segUp (colF b3) a0 a3) (rowF a3 b3) ++
      (tAux (colF b3 a3) (segDown (rowF a3) b3 b1) (colF b1 a3) ++
      (tAux (rowF a3 b1) (segDown (colF b1) a3 a1) (rowF a1 b1) ++
      (tAux (colF b1 a1) (segUp (rowF a1) b1 b2) (colF b2 a1) ++
      (tAux (rowF a1 b2) (segUp (colF b2) a1 a2) (rowF a2 b2) ++
      (tAux (colF b2 a2) (segDown (rowF a2) b2 b0) (colF b0 a2) ++
       tAux (rowF a2 b0) (segDown (colF b0) a2 a0) (rowF a0 b0))))))) := by
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := h
  unfold lift
  rw [turns_eq_of _ (colF b0 a0) (rowF a0 b0)
      (getLast?_append_of <| getLast?_append_of <| getLast?_append_of <| getLast?_append_of <|
        getLast?_append_of <| getLast?_append_of <| getLast?_append_of <|
        segDown_getLast? _ (by omega))
      (head?_append_of (segUp_head? _ (by omega)))]
  rw [tAux_append _ _ _ _ (rowF a0 b3) (colF b3 a0) (segUp_getLast? _ (by omega))
      (head?_append_of (segUp_head? _ (by omega)))]
  rw [tAux_append _ _ _ _ (colF b3 a3) (rowF a3 b3) (segUp_getLast? _ (by omega))
      (head?_append_of (segDown_head? _ (by omega)))]
  rw [tAux_append _ _ _ _ (rowF a3 b1) (colF b1 a3) (segDown_getLast? _ (by omega))
      (head?_append_of (segDown_head? _ (by omega)))]
  rw [tAux_append _ _ _ _ (colF b1 a1) (rowF a1 b1) (segDown_getLast? _ (by omega))
      (head?_append_of (segUp_head? _ (by omega)))]
  rw [tAux_append _ _ _ _ (rowF a1 b2) (colF b2 a1) (segUp_getLast? _ (by omega))
      (head?_append_of (segUp_head? _ (by omega)))]
  rw [tAux_append _ _ _ _ (colF b2 a2) (rowF a2 b2) (segUp_getLast? _ (by omega))
      (head?_append_of (segDown_head? _ (by omega)))]
  rw [tAux_append _ _ _ _ (rowF a2 b0) (colF b0 a2) (segDown_getLast? _ (by omega))
      (segDown_head? _ (by omega))]

theorem lift_nodup (h : Ord8 a0 a1 a2 a3 b0 b1 b2 b3) : (lift a0 a1 a2 a3 b0 b1 b2 b3).Nodup := by
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := h
  simp only [lift, List.nodup_append, List.mem_append, mem_segUp, mem_segDown,
    nodup_segUp (rowF_injective _), nodup_segUp (colF_injective _),
    nodup_segDown (rowF_injective _), nodup_segDown (colF_injective _), true_and, rowF, colF]
  and_intros <;> intros <;> aesop (add safe tactic (by omega))


theorem lift_inRange {t : ℕ} (h : Ord8 a0 a1 a2 a3 b0 b1 b2 b3) (ha : a3 < t) (hb : b3 < t) :
    ∀ x ∈ lift a0 a1 a2 a3 b0 b1 b2 b3, InRange t x := by
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := h
  intro x hx
  simp only [lift, List.mem_append, mem_segUp, mem_segDown, rowF, colF] at hx
  rcases hx with ⟨y, hy1, hy2, rfl⟩ | ⟨y, hy1, hy2, rfl⟩ | ⟨y, hy1, hy2, rfl⟩ | ⟨y, hy1, hy2, rfl⟩ |
    ⟨y, hy1, hy2, rfl⟩ | ⟨y, hy1, hy2, rfl⟩ | ⟨y, hy1, hy2, rfl⟩ | ⟨y, hy1, hy2, rfl⟩ <;>
  · simp only [InRange]; omega

theorem lift_length (h : Ord8 a0 a1 a2 a3 b0 b1 b2 b3) : 3 ≤ (lift a0 a1 a2 a3 b0 b1 b2 b3).length := by
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := h
  simp only [lift, segUp, segDown, List.length_append, List.length_map, List.length_reverse,
    List.length_range']
  omega

set_option linter.unusedSimpArgs false in
theorem lift_adj (h : Ord8 a0 a1 a2 a3 b0 b1 b2 b3) :
    ∀ τ ∈ turns (lift a0 a1 a2 a3 b0 b1 b2 b3), tadj τ.1 τ.2.2 := by
  have h' := h
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := h'
  rw [lift_turns h]
  intro τ hτ
  simp only [List.mem_append] at hτ
  rcases hτ with hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ
  · exact adj_tAux_segUp tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]) (by simp [tadj, rowF, colF]) τ hτ
  · exact adj_tAux_segUp tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]) (by simp [tadj, rowF, colF]) τ hτ
  · exact adj_tAux_segDown tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]; omega) (by simp [tadj, rowF, colF]) τ hτ
  · exact adj_tAux_segDown tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]; omega) (by simp [tadj, rowF, colF]) τ hτ
  · exact adj_tAux_segUp tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]) (by simp [tadj, rowF, colF]) τ hτ
  · exact adj_tAux_segUp tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]) (by simp [tadj, rowF, colF]) τ hτ
  · exact adj_tAux_segDown tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]; omega) (by simp [tadj, rowF, colF]) τ hτ
  · exact adj_tAux_segDown tadj _ (by omega) _ _
        (fun x hx1 hx2 => by simp [tadj, rowF, colF]; omega) (by simp [tadj, rowF, colF]) τ hτ

end LiftLemmas

/-! ### Lemma L1 for the lifted cycles: corner contributions

For a labelling `F` of the triple graph, the four corner types of `B`
(`VH+−`, `HV++`, `VH−+`, `HV−−`) contribute `phiA`, `phiB`, `phiC`, `phiD` at a cell `(a, b)`:
the two rung turns at the corner plus the prefix sums of the straight turns of the row and column
segments, attributed to their end corners. -/

section Corners

variable {k : ℕ} (F : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → (Fin k → ZMod 2))

/-- corner `VH+−` (column moving up into the cell, row leaving to the right). -/
def phiA (a b : ℕ) : Fin k → ZMod 2 :=
  F (colF b a) (colF b (a + 1)) (rowF a b) - strDn F (colF b) (a + 1) +
  F (rowF a b) (colF b a) (rowF a (b + 1)) - strUp F (rowF a) (b + 1)

/-- corner `HV++` (row moving right into the cell, column leaving downwards). -/
def phiB (a b : ℕ) : Fin k → ZMod 2 :=
  F (rowF a b) (rowF a (b - 1)) (colF b a) + strUp F (rowF a) b +
  F (colF b a) (rowF a b) (colF b (a + 1)) - strUp F (colF b) (a + 1)

/-- corner `VH−+` (column moving down into the cell, row leaving to the left). -/
def phiC (a b : ℕ) : Fin k → ZMod 2 :=
  F (colF b a) (colF b (a - 1)) (rowF a b) + strUp F (colF b) a +
  F (rowF a b) (colF b a) (rowF a (b - 1)) + strDn F (rowF a) b

/-- corner `HV−−` (row moving left into the cell, column leaving upwards). -/
def phiD (a b : ℕ) : Fin k → ZMod 2 :=
  F (rowF a b) (rowF a (b + 1)) (colF b a) - strDn F (rowF a) (b + 1) +
  F (colF b a) (rowF a b) (colF b (a - 1)) + strDn F (colF b) a

variable {a0 a1 a2 a3 b0 b1 b2 b3 : ℕ}

/-- **Lemma L1 (decomposition), for the lifted cycles**: the label sum of the lift is the sum of
the corner contributions of its eight corners. -/
theorem cycleSum_lift (h : Ord8 a0 a1 a2 a3 b0 b1 b2 b3) :
    cycleSum F (lift a0 a1 a2 a3 b0 b1 b2 b3) =
      phiA F a0 b0 + phiB F a0 b3 + phiC F a3 b3 + phiD F a3 b1 +
      phiA F a1 b1 + phiB F a1 b2 + phiC F a2 b2 + phiD F a2 b0 := by
  have h' := h
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := h'
  unfold cycleSum
  rw [lift_turns h]
  simp only [List.map_append, List.sum_append]
  rw [sum_tAux_segUp F _ (show b0 < b3 by omega), sum_tAux_segUp F _ (show a0 < a3 by omega),
    sum_tAux_segDown F _ (show b1 < b3 by omega), sum_tAux_segDown F _ (show a1 < a3 by omega),
    sum_tAux_segUp F _ (show b1 < b2 by omega), sum_tAux_segUp F _ (show a1 < a2 by omega),
    sum_tAux_segDown F _ (show b0 < b2 by omega), sum_tAux_segDown F _ (show a0 < a2 by omega)]
  unfold phiA phiB phiC phiD
  abel

theorem add_self_vec (x : Fin k → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = z
  revert z; decide

/-- **The planted zero**: if the four corner types take equal values at their two cells, the
lifted cycle has label sum `0`. -/
theorem cycleSum_lift_eq_zero (h : Ord8 a0 a1 a2 a3 b0 b1 b2 b3)
    (hA : phiA F a1 b1 = phiA F a0 b0) (hB : phiB F a1 b2 = phiB F a0 b3)
    (hC : phiC F a2 b2 = phiC F a3 b3) (hD : phiD F a2 b0 = phiD F a3 b1) :
    cycleSum F (lift a0 a1 a2 a3 b0 b1 b2 b3) = 0 := by
  rw [cycleSum_lift F h, hA, hB, hC, hD]
  have : phiA F a0 b0 + phiB F a0 b3 + phiC F a3 b3 + phiD F a3 b1 +
      phiA F a0 b0 + phiB F a0 b3 + phiC F a3 b3 + phiD F a3 b1 =
      (phiA F a0 b0 + phiA F a0 b0) + (phiB F a0 b3 + phiB F a0 b3) +
      (phiC F a3 b3 + phiC F a3 b3) + (phiD F a3 b1 + phiD F a3 b1) := by abel
  rw [this]
  simp only [add_self_vec, add_zero]

end Corners

/-! ## The Ramsey step (iterated pigeonhole, replacing Kővári–Sós–Turán)

Rows first: in each row, among the first `m = 3N + 1` columns some colour occurs on `4` columns;
record (colour, 4-set). Then among `T = 3·N·C(m,4) + 1` rows, four rows record the same pair. -/

theorem grid_ramsey {γ : Type*} [Fintype γ] [DecidableEq γ] (col : ℕ → ℕ → γ) :
    ∃ A B : Finset ℕ, A.card = 4 ∧ B.card = 4 ∧
      A ⊆ Finset.range (3 * Fintype.card γ * (3 * Fintype.card γ + 1).choose 4 + 1) ∧
      B ⊆ Finset.range (3 * Fintype.card γ + 1) ∧ ∃ c, ∀ a ∈ A, ∀ b ∈ B, col a b = c := by
  set N := Fintype.card γ with hN
  set m := 3 * N + 1 with hm
  have row : ∀ a, ∃ p : γ × Finset ℕ, p.2 ∈ (Finset.range m).powersetCard 4 ∧
      ∀ b ∈ p.2, col a b = p.1 := by
    intro a
    obtain ⟨c, -, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.range m) (t := Finset.univ) (f := col a) (n := 3)
      (fun _ _ => Finset.mem_univ _) (by rw [Finset.card_univ, Finset.card_range]; omega)
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (n := 4) (Nat.succ_le_of_lt hc)
    refine ⟨(c, S), Finset.mem_powersetCard.mpr ⟨hS.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
    intro b hb
    exact (Finset.mem_filter.mp (hS hb)).2
  choose sel hsel using row
  obtain ⟨p, hp, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.range (3 * N * m.choose 4 + 1)) (t := Finset.univ ×ˢ (Finset.range m).powersetCard 4)
    (f := sel) (n := 3)
    (fun a _ => Finset.mem_product.mpr ⟨Finset.mem_univ _, (hsel a).1⟩)
    (by
      rw [Finset.card_product, Finset.card_univ, Finset.card_powersetCard, Finset.card_range,
        Finset.card_range]
      exact Nat.lt_succ_of_le (le_of_eq (by ring)))
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq (n := 4) (Nat.succ_le_of_lt hfib)
  have hp2 := Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).2
  refine ⟨A, p.2, hAcard, hp2.2, hA.trans (Finset.filter_subset _ _), hp2.1, p.1, ?_⟩
  intro a ha b hb
  have hsa : sel a = p := (Finset.mem_filter.mp (hA ha)).2
  have := (hsel a).2 b (by rw [hsa]; exact hb)
  rw [hsa] at this
  exact this

/-! ## Theorem L -/

/-- the colours: the four corner values at a cell. -/
abbrev Colour (k : ℕ) := (Fin k → ZMod 2) × (Fin k → ZMod 2) × (Fin k → ZMod 2) × (Fin k → ZMod 2)

theorem card_colour (k : ℕ) : Fintype.card (Colour k) = 16 ^ k := by
  simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
  ring

/-- the explicit threshold `T(k) = 3·16^k·C(3·16^k + 1, 4) + 1`. -/
def thr (k : ℕ) : ℕ := 3 * 16 ^ k * (3 * 16 ^ k + 1).choose 4 + 1

/-- **Theorem L (explicit form).** If `t ≥ T(k)`, the crossing grid `H_t` has no good `k`-bit
turn labelling. -/
theorem not_good_of_thr_le {t k : ℕ} (ht : thr k ≤ t)
    (F : Fin (2 * t * t) → Fin (2 * t * t) → Fin (2 * t * t) → (Fin k → ZMod 2)) :
    ¬ Good (gridAdj t) F := by
  intro hF
  have hN : 1 ≤ 16 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hC : 1 ≤ (3 * 16 ^ k + 1).choose 4 := Nat.choose_pos (by omega)
  have hmT : 3 * 16 ^ k + 1 ≤ thr k := by
    unfold thr
    have : 3 * 16 ^ k ≤ 3 * 16 ^ k * (3 * 16 ^ k + 1).choose 4 := Nat.le_mul_of_pos_right _ hC
    omega
  have ht0 : 0 < t := by unfold thr at ht; omega
  set F' : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → (Fin k → ZMod 2) :=
    fun x y z => F (enc t ht0 x) (enc t ht0 y) (enc t ht0 z) with hF'
  let col : ℕ → ℕ → Colour k := fun a b => (phiA F' a b, phiB F' a b, phiC F' a b, phiD F' a b)
  obtain ⟨A, B, hA, hB, hAr, hBr, c, hc⟩ := grid_ramsey col
  rw [card_colour] at hAr hBr
  set ea := A.orderEmbOfFin hA
  set eb := B.orderEmbOfFin hB
  have hord : Ord8 (ea 0) (ea 1) (ea 2) (ea 3) (eb 0) (eb 1) (eb 2) (eb 3) :=
    ⟨ea.strictMono (by decide), ea.strictMono (by decide), ea.strictMono (by decide),
     eb.strictMono (by decide), eb.strictMono (by decide), eb.strictMono (by decide)⟩
  have hmemA : ∀ i, ea i ∈ A := fun i => A.orderEmbOfFin_mem hA i
  have hmemB : ∀ j, eb j ∈ B := fun j => B.orderEmbOfFin_mem hB j
  have ha3 : ea 3 < t := by
    have := Finset.mem_range.mp (hAr (hmemA 3)); unfold thr at ht; omega
  have hb3 : eb 3 < t := by
    have := Finset.mem_range.mp (hBr (hmemB 3)); omega
  have hcyc := isDirCycle_enc ht0 _ (lift_length hord) (lift_nodup hord) (lift_inRange hord ha3 hb3)
    (lift_adj hord)
  apply hF _ hcyc
  rw [cycleSum_map]
  have hcc : ∀ i j, col (ea i) (eb j) = c := fun i j => hc _ (hmemA i) _ (hmemB j)
  apply cycleSum_lift_eq_zero F' hord
  · have h1 := hcc 1 1; have h0 := hcc 0 0
    have := congrArg Prod.fst (h1.trans h0.symm); exact this
  · have h1 := hcc 1 2; have h0 := hcc 0 3
    have := congrArg (fun x => x.2.1) (h1.trans h0.symm); exact this
  · have h1 := hcc 2 2; have h0 := hcc 3 3
    have := congrArg (fun x => x.2.2.1) (h1.trans h0.symm); exact this
  · have h1 := hcc 2 0; have h0 := hcc 3 1
    have := congrArg (fun x => x.2.2.2) (h1.trans h0.symm); exact this

theorem thr_le (k : ℕ) : thr k ≤ 2 ^ (20 * k + 10) := by
  unfold thr
  set N := 16 ^ k with hN
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by norm_num)
  have h1 : (3 * N + 1).choose 4 ≤ (4 * N) ^ 4 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 4)
  have h2 : 2 ^ (20 * k + 10) = 1024 * N ^ 5 := by
    rw [hN, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, pow_add]; ring_nf
  rw [h2]
  have h3 : 3 * N * (3 * N + 1).choose 4 ≤ 3 * N * (4 * N) ^ 4 := Nat.mul_le_mul_left _ h1
  have h4 : 1 ≤ N ^ 5 := Nat.one_le_pow _ _ hN1
  nlinarith

/-- **Theorem L.** Every good `k`-bit turn labelling of the crossing grid `H_t` (max degree 3,
`2t²` vertices) forces `t < 2^(20k+10)`. -/
theorem theoremL {t k : ℕ}
    (F : Fin (2 * t * t) → Fin (2 * t * t) → Fin (2 * t * t) → (Fin k → ZMod 2))
    (hF : Good (gridAdj t) F) : t < 2 ^ (20 * k + 10) := by
  by_contra h
  exact not_good_of_thr_le ((thr_le k).trans (not_lt.mp h)) F hF

/-- **Theorem L, logarithmic form**: `k*(H_t) ≥ (log₂ t − 10)/20`, i.e. a good `k`-bit labelling
of `H_t` (`t ≥ 1`) has `log₂ t < 20k + 10`. -/
theorem theoremL_log {t k : ℕ} (ht : t ≠ 0)
    (F : Fin (2 * t * t) → Fin (2 * t * t) → Fin (2 * t * t) → (Fin k → ZMod 2))
    (hF : Good (gridAdj t) F) : Nat.log 2 t < 20 * k + 10 :=
  Nat.log_lt_of_lt_pow ht (theoremL F hF)

/-! ## Sanity checks on instances (kernel `decide`) -/

/-- the vertex list of `B` in `H_{4,4}` (as in `Scratch/Kstar/Instances.lean`, `r(a,b) = 4a+b`,
`c(a,b) = 16+4a+b`) is the lift with rows and columns `0,1,2,3`. -/
example : (lift 0 1 2 3 0 1 2 3).map (enc 4 (by norm_num)) =
    ([0, 1, 2, 3, 19, 23, 27, 31, 15, 14, 13, 29, 25, 21, 5, 6, 22, 26, 10, 9, 8, 24, 20, 16] :
      List (Fin 32)) := by decide

/-- a lift into `H_9` is a directed cycle (instance of Lemma L3). -/
example : isDirCycle (gridAdj 9) ((lift 1 3 4 8 0 2 5 7).map (enc 9 (by norm_num))) = true := by
  decide

end Kstar
