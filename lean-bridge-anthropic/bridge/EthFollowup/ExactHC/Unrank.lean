/-
# Ranking the subsets of a given size (module A1, file 1)

`research/hc-degree-theorem.md` §2 (combinatorial number system) and §7. A subset of `{0,…,e-1}` of
size `s` is written as its indicator word `bs : List Bool` (`bs.length = e`, `cnt bs = s` trues).

* `rank bs`: the rank of `bs` among the words of its length and number of trues, in the order
  "words starting with `false` first" (`rank (false :: bs) = rank bs`,
  `rank (true :: bs) = C(|bs|, cnt bs + 1) + rank bs`); `rank_lt : rank bs < C(|bs|, cnt bs)`.
* `unrank e s r`: the greedy inverse; `unrank_rank`, `unrank_spec` (for `r < C(e,s)`: length `e`,
  `s` trues, `rank (unrank e s r) = r`).
* `cw e s = Nat.size (C(e,s) - 1)`, the number of bits of a rank: `choose_le_two_pow_cw`,
  `two_pow_cw_le : 2^{cw e s} ≤ 2·C(e,s)` (for `C(e,s) ≥ 1`), `cw_le : cw e s ≤ e`.
* The *rank code* of a word of labels `ls : List L` with default `dflt`: the rank of the set of
  non-default places in `cw e s` bits, then a `w`-bit code `cd l` of every non-default label
  (`encR`); `decR` decodes and returns `none` off the image (`decR_encR`, `encR_of_decR`).
* `rawCodes`: the decoded labels as numbers (`0` for the default, `ofWord chunk + 1` otherwise).
* Polynomial time: `choose_polyT` (first argument in unary), `rank_polyT`, `unrank_polyT` (length in
  unary), `cw_polyT`, `cw_unary`, `rawCodes_polyT`.
-/
import ToTuring.Poly.IsPoly
import ToTuring.Lib.List3
import ToTuring.Lib.List1b
import ToTuring.Lib.Nat1b
import ToTuring.Closure.Cases
import ToTuring.Closure.Fold
import StepMachines.Prog.Chunks

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace Rank

open Groundwork

/-! ### Rank and unrank -/

/-- The number of `true`s of a word. -/
def cnt (bs : List Bool) : ℕ := bs.count true

@[simp] theorem cnt_nil : cnt [] = 0 := rfl
@[simp] theorem cnt_false (bs : List Bool) : cnt (false :: bs) = cnt bs := by
  simp [cnt]
@[simp] theorem cnt_true (bs : List Bool) : cnt (true :: bs) = cnt bs + 1 := by
  simp [cnt]

theorem cnt_le_length (bs : List Bool) : cnt bs ≤ bs.length := List.count_le_length

/-- The rank of a word among the words of the same length and the same number of `true`s. -/
def rank : List Bool → ℕ
  | [] => 0
  | false :: bs => rank bs
  | true :: bs => Nat.choose bs.length (cnt bs + 1) + rank bs

theorem rank_lt : ∀ bs : List Bool, rank bs < Nat.choose bs.length (cnt bs)
  | [] => by simp [rank]
  | false :: bs => by
    have := rank_lt bs
    simp only [rank, cnt_false, List.length_cons]
    exact lt_of_lt_of_le this (Nat.choose_le_choose _ (Nat.le_succ _))
  | true :: bs => by
    have := rank_lt bs
    simp only [rank, cnt_true, List.length_cons, Nat.choose_succ_succ']
    omega

/-- The greedy inverse of `rank`. -/
def unrank : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | e + 1, s, r =>
    if r < Nat.choose e s then false :: unrank e s r else true :: unrank e (s - 1) (r - Nat.choose e s)

theorem unrank_rank : ∀ bs : List Bool, unrank bs.length (cnt bs) (rank bs) = bs
  | [] => rfl
  | false :: bs => by
    simp only [List.length_cons, cnt_false, rank, unrank, if_pos (rank_lt bs), unrank_rank bs]
  | true :: bs => by
    simp only [List.length_cons, cnt_true, rank, unrank]
    rw [if_neg (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel_left, unrank_rank bs]

theorem unrank_spec : ∀ (e s r : ℕ), r < Nat.choose e s →
    (unrank e s r).length = e ∧ cnt (unrank e s r) = s ∧ rank (unrank e s r) = r
  | 0, s, r, h => by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp at h; subst h; simp [unrank, rank]
    · rw [Nat.choose_eq_zero_of_lt hs] at h; omega
  | e + 1, s, r, h => by
    by_cases hr : r < Nat.choose e s
    · obtain ⟨h1, h2, h3⟩ := unrank_spec e s r hr
      simp only [unrank, if_pos hr, List.length_cons, cnt_false, rank, h1, h2, h3, and_self]
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := by
        rcases Nat.eq_zero_or_pos s with rfl | hs
        · simp at h hr; omega
        · exact ⟨s - 1, by omega⟩
      rw [Nat.choose_succ_succ'] at h
      obtain ⟨h1, h2, h3⟩ := unrank_spec e s' (r - Nat.choose e (s' + 1)) (by omega)
      simp only [unrank, if_neg hr, Nat.add_sub_cancel]
      refine ⟨by simp [h1], by simp [h2], ?_⟩
      simp only [rank, h1, h2, h3]
      omega

theorem rank_injective {bs bs' : List Bool} (hl : bs.length = bs'.length) (hc : cnt bs = cnt bs')
    (h : rank bs = rank bs') : bs = bs' := by
  rw [← unrank_rank bs, ← unrank_rank bs', hl, hc, h]

/-! ### The width of a rank -/

/-- The number of bits of a rank among `C(e,s)` values: `⌈log₂ C(e,s)⌉` (as `Nat.size (C - 1)`). -/
def cw (e s : ℕ) : ℕ := Nat.size (Nat.choose e s - 1)

theorem choose_le_two_pow_cw (e s : ℕ) : Nat.choose e s ≤ 2 ^ cw e s := by
  have := Nat.lt_size_self (Nat.choose e s - 1)
  unfold cw; omega

theorem rank_lt_two_pow_cw (bs : List Bool) : rank bs < 2 ^ cw bs.length (cnt bs) :=
  lt_of_lt_of_le (rank_lt bs) (choose_le_two_pow_cw _ _)

theorem two_pow_size_le (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.size x ≤ 2 * x := by
  by_contra h
  have h1 : x < 2 ^ (Nat.size x - 1) := by
    rcases Nat.eq_zero_or_pos (Nat.size x) with h0 | h0
    · rw [Nat.size_eq_zero] at h0; omega
    · have : 2 ^ Nat.size x = 2 * 2 ^ (Nat.size x - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
  have := Nat.size_le.2 h1
  have : Nat.size x ≠ 0 := by
    intro h0; rw [Nat.size_eq_zero] at h0; omega
  omega

/-- Rounding up costs at most a factor two: `2^{cw e s} ≤ 2·C(e,s)` when `C(e,s) ≥ 1`. -/
theorem two_pow_cw_le (e s : ℕ) (h : 1 ≤ Nat.choose e s) : 2 ^ cw e s ≤ 2 * Nat.choose e s := by
  unfold cw
  rcases Nat.eq_or_lt_of_le h with h1 | h1
  · rw [← h1]; simp
  · exact (two_pow_size_le _ (by omega)).trans (by omega)

theorem cw_le (e s : ℕ) : cw e s ≤ e := by
  unfold cw
  rw [Nat.size_le]
  have := Nat.choose_le_two_pow e s
  have : 0 < 2 ^ e := Nat.two_pow_pos e
  omega

/-! ### The rank code of a word of labels -/

section Code

variable {L : Type} [DecidableEq L] (dflt : L) (w : ℕ) (cd : L → List Bool) (dc : List Bool → L)

/-- The indicator word of the non-default places. -/
def nd (ls : List L) : List Bool := ls.map fun l => decide (l ≠ dflt)

@[simp] theorem length_nd (ls : List L) : (nd dflt ls).length = ls.length := List.length_map _

theorem cnt_nd (ls : List L) : cnt (nd dflt ls) = (ls.filter fun l => decide (l ≠ dflt)).length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    by_cases h : l = dflt
    · simp [nd, h] at ih ⊢; exact ih
    · simp [nd, h, List.filter_cons] at ih ⊢; simpa [cnt] using ih

/-- **The rank code**: the rank of the set of non-default places in `cw e s` bits, then the codes
of the non-default labels in order. -/
def encR (e s : ℕ) (ls : List L) : List Bool :=
  toWord (cw e s) (rank (nd dflt ls)) ++ (ls.filter fun l => decide (l ≠ dflt)).flatMap cd

/-- Labels from an indicator word and the codes of the non-default labels. -/
def fill : List Bool → List Bool → List L
  | [], _ => []
  | false :: bs, z => dflt :: fill bs z
  | true :: bs, z => dc (z.take w) :: fill bs (z.drop w)

/-- The raw decoding (without the check). -/
def rawR (e s : ℕ) (z : List Bool) : List L :=
  fill dflt w dc (unrank e s (ofWord (z.take (cw e s)))) (z.drop (cw e s))

/-- **The decoder**: `some` of the raw decoding if it is a word of `e` labels with `s` non-default
ones whose code is `z`; `none` otherwise. -/
def decR (e s : ℕ) (z : List Bool) : Option (List L) :=
  if encR dflt cd e s (rawR dflt w dc e s z) = z ∧ (rawR dflt w dc e s z).length = e ∧
      cnt (nd dflt (rawR dflt w dc e s z)) = s then some (rawR dflt w dc e s z) else none

variable {w cd dc}

theorem length_flatMap_cd (hcd : ∀ l, (cd l).length = w) (ls : List L) :
    (ls.flatMap cd).length = w * ls.length := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp only [List.flatMap_cons, List.length_append, hcd, ih, List.length_cons]; ring

theorem length_encR (hcd : ∀ l, (cd l).length = w) (e s : ℕ) (ls : List L)
    (hs : cnt (nd dflt ls) = s) : (encR dflt cd e s ls).length = cw e s + w * s := by
  rw [encR, List.length_append, length_toWord, length_flatMap_cd hcd, ← cnt_nd, hs]

theorem fill_nd (hcd : ∀ l, (cd l).length = w) (hdc : ∀ l, l ≠ dflt → dc (cd l) = l) :
    ∀ ls : List L, fill dflt w dc (nd dflt ls) ((ls.filter fun l => decide (l ≠ dflt)).flatMap cd) = ls
  | [] => rfl
  | l :: ls => by
    by_cases h : l = dflt
    · have e1 : nd dflt (l :: ls) = false :: nd dflt ls := by simp [nd, h]
      rw [e1, List.filter_cons_of_neg (by simp [h]), fill, fill_nd hcd hdc ls, h]
    · have e1 : nd dflt (l :: ls) = true :: nd dflt ls := by simp [nd, h]
      rw [e1, List.filter_cons_of_pos (by simpa using h), List.flatMap_cons, fill,
        List.take_left' (hcd l), List.drop_left' (hcd l), hdc l h, fill_nd hcd hdc ls]

theorem rawR_encR (hcd : ∀ l, (cd l).length = w) (hdc : ∀ l, l ≠ dflt → dc (cd l) = l)
    {e s : ℕ} {ls : List L} (he : ls.length = e) (hs : cnt (nd dflt ls) = s) :
    rawR dflt w dc e s (encR dflt cd e s ls) = ls := by
  unfold rawR encR
  rw [List.take_left' (length_toWord _ _), List.drop_left' (length_toWord _ _)]
  have hr : rank (nd dflt ls) < 2 ^ cw e s := by
    have := rank_lt_two_pow_cw (nd dflt ls)
    rwa [length_nd, he, hs] at this
  rw [ofWord_toWord hr, ← he, ← hs, ← length_nd dflt ls, unrank_rank, fill_nd dflt hcd hdc]

/-- The decoder inverts the code on the words of `e` labels with `s` non-default ones. -/
theorem decR_encR (hcd : ∀ l, (cd l).length = w) (hdc : ∀ l, l ≠ dflt → dc (cd l) = l)
    {e s : ℕ} {ls : List L} (he : ls.length = e) (hs : cnt (nd dflt ls) = s) :
    decR dflt w cd dc e s (encR dflt cd e s ls) = some ls := by
  unfold decR
  rw [rawR_encR dflt hcd hdc he hs, if_pos ⟨rfl, he, hs⟩]

/-- What the decoder returns is a word of `e` labels with `s` non-default ones, coded by `z`. -/
theorem encR_of_decR {e s : ℕ} {z : List Bool} {ls : List L} (h : decR dflt w cd dc e s z = some ls) :
    encR dflt cd e s ls = z ∧ ls.length = e ∧ cnt (nd dflt ls) = s := by
  unfold decR at h
  split_ifs at h with h'
  · cases h; exact h'

end Code

/-! ### Labels as numbers -/

/-- Numbers of the labels from an indicator word and the `w`-bit chunks: `0` for a `false`, and
`ofWord chunk + 1` for a `true`. -/
def fillN (w : ℕ) : List Bool → List Bool → List ℕ
  | [], _ => []
  | false :: bs, z => 0 :: fillN w bs z
  | true :: bs, z => (ofWord (z.take w) + 1) :: fillN w bs (z.drop w)

/-- The decoded labels of a block, as numbers. -/
def rawCodes (e s w : ℕ) (z : List Bool) : List ℕ :=
  fillN w (unrank e s (ofWord (z.take (cw e s)))) (z.drop (cw e s))

theorem fill_map {L : Type} (dflt : L) (w : ℕ) (dc : List Bool → L) (code : L → ℕ)
    (h0 : code dflt = 0) (h1 : ∀ u : List Bool, code (dc (u.take w)) = ofWord (u.take w) + 1) :
    ∀ (bs z : List Bool), (fill dflt w dc bs z).map code = fillN w bs z
  | [], _ => rfl
  | false :: bs, z => by simp [fill, fillN, h0, fill_map dflt w dc code h0 h1 bs z]
  | true :: bs, z => by simp [fill, fillN, h1, fill_map dflt w dc code h0 h1 bs (z.drop w)]

theorem rawR_map {L : Type} (dflt : L) (w : ℕ) (dc : List Bool → L) (code : L → ℕ)
    (h0 : code dflt = 0) (h1 : ∀ u : List Bool, code (dc (u.take w)) = ofWord (u.take w) + 1)
    (e s : ℕ) (z : List Bool) : (rawR dflt w dc e s z).map code = rawCodes e s w z :=
  fill_map dflt w dc code h0 h1 _ _

/-! ### Polynomial time -/

section Poly

variable {α : Type} [Enc α]

/-- The binomial coefficients by the product formula. -/
def chStep (n : ℕ) (c i : ℕ) : ℕ := c * (n - i) / (i + 1)

theorem foldl_chStep (n : ℕ) : ∀ j : ℕ, (List.range j).foldl (chStep n) 1 = Nat.choose n j
  | 0 => by simp
  | j + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_chStep n j, List.foldl_cons, List.foldl_nil, chStep,
      ← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos j)]

theorem choose_eq_fold (n k : ℕ) :
    Nat.choose n k = if k ≤ n then (List.range (min k n)).foldl (chStep n) 1 else 0 := by
  split_ifs with h
  · rw [min_eq_left h, foldl_chStep]
  · exact Nat.choose_eq_zero_of_lt (by omega)

theorem size_choose_le (n k : ℕ) : Nat.size (Nat.choose n k) ≤ n + 1 := by
  rw [Nat.size_le]
  exact lt_of_le_of_lt (Nat.choose_le_two_pow n k) (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))

theorem len_nat_le_of_size {x b : ℕ} (h : Nat.size x ≤ b) : len x ≤ 3 * b + 2 := by
  rw [len_nat]; omega

theorem le_len_replicate (k : ℕ) : k ≤ len (List.replicate k ()) := by
  rw [len_units, List.length_replicate]; omega

/-- **The binomial coefficients in polynomial time**, the first argument given in unary. -/
theorem choose_polyT {n k : α → ℕ} (hn : Unary n) (hk : PolyT k) :
    PolyT fun x => Nat.choose (n x) (k x) := by
  have hn' : PolyT n := hn.poly
  have hm : Unary fun x => min (k x) (n x) :=
    Unary.of_le hn (PolyT.min' hk hn') fun x => min_le_right _ _
  have hr : PolyT fun x => List.range (min (k x) (n x)) := PolyT.range hm
  have hf : PolyT fun x => (List.range (min (k x) (n x))).foldl (chStep (n x)) 1 := by
    obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hn
    refine PolyT.foldl (l := fun x => List.range (min (k x) (n x))) (a := fun _ => 1)
      (g := fun x c i => chStep (n x) c i) hr (PolyT.const 1) ?_
      ⟨fun N => 3 * (t N + 1) + 2, ((PB.const 3).mul (ht.add (PB.const 1))).add (PB.const 2), fun x j => ?_⟩
    · have : PolyT fun p : α × ℕ × ℕ => n p.1 := hn'.comp PolyT.id'.fst
      unfold chStep; fun_prop
    · rw [List.take_range, foldl_chStep]
      have h1 := size_choose_le (n x) (min j (min (k x) (n x)))
      have h2 := le_len_replicate (n x)
      have h3 := hlen x
      exact len_nat_le_of_size (by omega)
  have hd : PolyT fun x => decide (k x ≤ n x) := PolyT.decide_le hk hn'
  exact (PolyT.ite' hd hf (PolyT.const 0)).congr fun x => (choose_eq_fold _ _).symm

theorem rank_eq_sum : ∀ bs : List Bool, rank bs = ((List.range bs.length).map fun j =>
    (bs.getD j false).toNat * Nat.choose (bs.length - 1 - j) (cnt (bs.drop (j + 1)) + 1)).sum
  | [] => rfl
  | b :: bs => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    have ih := rank_eq_sum bs
    have e : ((List.range bs.length).map ((fun j => ((b :: bs).getD j false).toNat *
        Nat.choose (bs.length + 1 - 1 - j) (cnt ((b :: bs).drop (j + 1)) + 1)) ∘ Nat.succ)) =
        (List.range bs.length).map fun j =>
          (bs.getD j false).toNat * Nat.choose (bs.length - 1 - j) (cnt (bs.drop (j + 1)) + 1) := by
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp, List.getD_cons_succ, List.drop_succ_cons]
      congr 2
      omega
    rw [e, ← ih]
    cases b <;> simp [rank]

/-- **The rank in polynomial time.** -/
theorem rank_polyT {bs : α → List Bool} (h : PolyT bs) : PolyT fun x => rank (bs x) := by
  have hr : PolyT fun x => List.range (bs x).length := PolyT.range (Unary.of_length h)
  have hb : PolyT fun p : α × ℕ => bs p.1 := h.comp PolyT.id'.fst
  have hn : Unary fun p : α × ℕ => (bs p.1).length - 1 - p.2 :=
    Unary.of_le (Unary.of_length hb) (by fun_prop) fun p => by omega
  have hk : PolyT fun p : α × ℕ => cnt ((bs p.1).drop (p.2 + 1)) + 1 := by unfold cnt; fun_prop
  have hc := choose_polyT hn hk
  have hm : PolyT fun x => ((List.range (bs x).length).map fun j =>
      ((bs x).getD j false).toNat * Nat.choose ((bs x).length - 1 - j) (cnt ((bs x).drop (j + 1)) + 1)) := by
    refine PolyT.map (f := fun x j => ((bs x).getD j false).toNat *
      Nat.choose ((bs x).length - 1 - j) (cnt ((bs x).drop (j + 1)) + 1)) ?_ hr
    fun_prop
  exact (PolyT.sum hm).congr fun x => (rank_eq_sum (bs x)).symm

/-- One step of the greedy unranking, on (output, number of trues left, rank left). -/
def urStep (E : ℕ) (st : List Bool × ℕ × ℕ) (i : ℕ) : List Bool × ℕ × ℕ :=
  if st.2.2 < Nat.choose (min i E) st.2.1 then (st.1 ++ [false], st.2.1, st.2.2)
  else (st.1 ++ [true], st.2.1 - 1, st.2.2 - Nat.choose (min i E) st.2.1)

theorem foldl_urStep (E : ℕ) : ∀ e ≤ E, ∀ (acc : List Bool) (s r : ℕ),
    ((List.range e).reverse.foldl (urStep E) (acc, s, r)).1 = acc ++ unrank e s r
  | 0, _, acc, s, r => by simp [unrank]
  | e + 1, he, acc, s, r => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    have hmin : min e E = e := min_eq_left (by omega)
    by_cases hr : r < Nat.choose e s
    · rw [urStep, hmin, if_pos hr, foldl_urStep E e (by omega)]
      simp [unrank, hr]
    · rw [urStep, hmin, if_neg hr, foldl_urStep E e (by omega)]
      simp [unrank, hr]

/-- **The unranking in polynomial time**, the length given in unary. -/
theorem unrank_polyT {e s r : α → ℕ} (he : Unary e) (hs : PolyT s) (hr : PolyT r) :
    PolyT fun x => unrank (e x) (s x) (r x) := by
  have hl : PolyT fun x => (List.range (e x)).reverse := by
    have := PolyT.range he; fun_prop
  have hn : Unary fun p : α × (List Bool × ℕ × ℕ) × ℕ => min p.2.2 (e p.1) :=
    Unary.of_le (he.comp PolyT.id'.fst) (PolyT.min' (by fun_prop) ((he.comp PolyT.id'.fst).poly))
      fun p => min_le_right _ _
  have hc := choose_polyT hn (k := fun p : α × (List Bool × ℕ × ℕ) × ℕ => p.2.1.2.1) (by fun_prop)
  have hg : PolyT fun p : α × (List Bool × ℕ × ℕ) × ℕ => urStep (e p.1) p.2.1 p.2.2 := by
    unfold urStep; fun_prop
  have hf : PolyT fun x => ((List.range (e x)).reverse.foldl (urStep (e x)) ([], s x, r x)) := by
    refine PolyT.foldl_add (g := fun x st i => urStep (e x) st i) hl (by fun_prop) hg
      ⟨fun _ => 3, PB.const 3, fun x c i _ => ?_⟩
    obtain ⟨acc, s', r'⟩ := c
    have ha : ∀ b : Bool, len (acc ++ [b]) = len acc + 3 := fun b => by
      have := len_append acc [b]
      rw [len_cons, len_nil, len_bool] at this; omega
    unfold urStep
    split_ifs
    · simp only [len_pair, ha]; omega
    · simp only [len_pair, ha]
      have h1 := len_nat_mono (Nat.sub_le s' 1)
      have h2 := len_nat_mono (Nat.sub_le r' (Nat.choose (min i (e x)) s'))
      omega
  exact (PolyT.fst hf).congr fun x => by rw [foldl_urStep (e x) (e x) le_rfl]; rfl

theorem cw_polyT {e s : α → ℕ} (he : Unary e) (hs : PolyT s) : PolyT fun x => cw (e x) (s x) := by
  have := choose_polyT he hs
  unfold cw; fun_prop

theorem cw_unary {e s : α → ℕ} (he : Unary e) (hs : PolyT s) : Unary fun x => cw (e x) (s x) :=
  Unary.of_le he (cw_polyT he hs) fun x => cw_le _ _

/-- One step of `fillN` on (output, chunks left). -/
def fnStep (w : ℕ) (st : List ℕ × List Bool) (b : Bool) : List ℕ × List Bool :=
  if b then (st.1 ++ [ofWord (st.2.take w) + 1], st.2.drop w) else (st.1 ++ [0], st.2)

theorem foldl_fnStep (w : ℕ) : ∀ (bs : List Bool) (out : List ℕ) (z : List Bool),
    (bs.foldl (fnStep w) (out, z)).1 = out ++ fillN w bs z
  | [], out, z => by simp [fillN]
  | false :: bs, out, z => by
    rw [List.foldl_cons, fnStep, if_neg (by simp), foldl_fnStep w bs]; simp [fillN]
  | true :: bs, out, z => by
    rw [List.foldl_cons, fnStep, if_pos rfl, foldl_fnStep w bs]; simp [fillN]

theorem fillN_polyT (w : ℕ) {bs z : α → List Bool} (hb : PolyT bs) (hz : PolyT z) :
    PolyT fun x => fillN w (bs x) (z x) := by
  have hg : PolyT fun p : α × (List ℕ × List Bool) × Bool => fnStep w p.2.1 p.2.2 := by
    unfold fnStep; fun_prop
  have hf : PolyT fun x => ((bs x).foldl (fnStep w) ([], z x)) := by
    refine PolyT.foldl_add (g := fun _ st b => fnStep w st b) hb (by fun_prop) hg
      ⟨fun _ => 3 * (w + 2) + 6, PB.const _, fun x c b _ => ?_⟩
    obtain ⟨out, rest⟩ := c
    have ha : ∀ k : ℕ, len (out ++ [k]) = len out + len k + 2 := fun k => by
      have := len_append out [k]
      rw [len_cons, len_nil] at this; omega
    unfold fnStep
    split_ifs
    · simp only [len_pair, ha]
      have h1 : len (rest.drop w) ≤ len rest := by
        rw [len_bools, len_bools, List.length_drop]; omega
      have h2 : Nat.size (ofWord (rest.take w) + 1) ≤ w + 1 := by
        rw [Nat.size_le]
        have := ofWord_lt (rest.take w)
        have : (rest.take w).length ≤ w := List.length_take_le _ _
        have : 2 ^ (rest.take w).length ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) this
        rw [pow_succ]; omega
      have := len_nat_le_of_size h2
      omega
    · simp only [len_pair, ha]
      have : len (0 : ℕ) = 2 := rfl
      omega
  exact (PolyT.fst hf).congr fun x => by rw [foldl_fnStep]; rfl

/-- **The decoded labels of a block as numbers, in polynomial time** (`e` in unary). -/
theorem rawCodes_polyT (w : ℕ) {e s : α → ℕ} {z : α → List Bool} (he : Unary e) (hs : PolyT s)
    (hz : PolyT z) : PolyT fun x => rawCodes (e x) (s x) w (z x) := by
  have hc := cw_unary he hs
  have hc' := hc.poly
  have hu := unrank_polyT he hs (r := fun x => ofWord ((z x).take (cw (e x) (s x)))) (by fun_prop)
  unfold rawCodes
  exact fillN_polyT w hu (by fun_prop)

end Poly

end Rank

end EthFollowup.ExactHC
