/-
# Input encoding of a list of numbers in equal-length blocks (module H2, pure Mathlib)

`scratchpad/plans/roots-plan.md` §2. The input of the root-finding machines is the list
`m :: a` (modulus, then the coefficients `a_0, …, a_d`), every number written little-endian and
right-padded to the common block length `blockLen l` (the longest encoding in the list).

* `blockLen l := (l.map fun v => (encodeNat v).length).foldr max 0` (FROZEN);
  `encodeList l := (l.map fun v => padR (blockLen l) (encodeNat v)).flatten` (FROZEN).
* `length_encodeList : (encodeList l).length = l.length * blockLen l`, `encodeList_div_length`
  (`|w| / |l| = blockLen l` for `l ≠ []`), `encodeList_pair : encodeList [m, a] = encodePair m a`.
* The block reader `leBlk nb j w := leVal ((w.drop (j * (w.length / nb))).take (w.length / nb))`
  (the `j`-th of `nb` equal blocks); `leBlk_encodeList : leBlk l.length j (encodeList l) = l.getD j 0`
  for `j < l.length`; `leBlk_lt : leBlk nb j w < 2 ^ (w.length / nb)`.
* `lt_two_pow_blockLen : v ∈ l → v < 2 ^ blockLen l`; `blockLen_cons_of_le`: when every
  coefficient is `≤ m`, `blockLen (m :: a) = (encodeNat m).length`.

Standard axioms only.
-/
import EthFollowup.ModP.Encode

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Computability

/-- The common block length: the longest binary encoding in the list. -/
def blockLen (l : List ℕ) : ℕ := (l.map fun v => (encodeNat v).length).foldr max 0

/-- The input word of a list of numbers: equal-length little-endian blocks. -/
def encodeList (l : List ℕ) : List Bool := (l.map fun v => padR (blockLen l) (encodeNat v)).flatten

/-- The value of the `j`-th of `nb` equal blocks of `w` (little-endian). -/
def leBlk (nb j : ℕ) (w : List Bool) : ℕ :=
  leVal ((w.drop (j * (w.length / nb))).take (w.length / nb))

/-! ## The block length -/

theorem le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.foldr_cons]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem length_encodeNat_le_blockLen {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    (encodeNat v).length ≤ blockLen l :=
  le_foldr_max (List.mem_map.2 ⟨v, hv, rfl⟩)

theorem blockLen_le {l : List ℕ} {B : ℕ} (h : ∀ v ∈ l, (encodeNat v).length ≤ B) :
    blockLen l ≤ B :=
  foldr_max_le fun x hx => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    exact h v hv

theorem lt_two_pow_length_encodeNat (v : ℕ) : v < 2 ^ (encodeNat v).length := by
  have := leVal_lt (encodeNat v)
  rwa [leVal_encodeNat] at this

/-- Every entry is `< 2 ^ blockLen l`. -/
theorem lt_two_pow_blockLen {l : List ℕ} {v : ℕ} (hv : v ∈ l) : v < 2 ^ blockLen l :=
  (lt_two_pow_length_encodeNat v).trans_le
    (Nat.pow_le_pow_right (by norm_num) (length_encodeNat_le_blockLen hv))

theorem getD_lt_two_pow_blockLen (l : List ℕ) (j : ℕ) : l.getD j 0 < 2 ^ blockLen l := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem _ _ hj]; exact lt_two_pow_blockLen (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; exact pow_pos (by norm_num) _

/-- The length of `encodeNat` is monotone. -/
theorem length_encodeNat_mono {u v : ℕ} (h : u ≤ v) : (encodeNat u).length ≤ (encodeNat v).length := by
  have key : ∀ N : ℕ, (encodeNat N).length = Nat.size N := by
    intro N
    have hN := leVal_encodeNat N
    -- characterise the length by `2^(len-1) ≤ N < 2^len` (no leading zeros)
    have hle : N < 2 ^ (encodeNat N).length := lt_two_pow_length_encodeNat N
    apply le_antisymm
    · -- the top bit of a nonempty `encodeNat` is `true`
      cases hc : (N : Num) with
      | zero =>
        have : N = 0 := by rw [← Num.to_of_nat N, hc]; rfl
        subst this; simp [encodeNat, hc, encodeNum]
      | pos p =>
        have hNp : N = (p : ℕ) := by rw [← Num.to_of_nat N, hc]; rfl
        have hen : encodeNat N = encodePosNum p := by simp [encodeNat, hc, encodeNum]
        rw [hen]
        have top : ∀ q : PosNum, 2 ^ ((encodePosNum q).length - 1) ≤ (q : ℕ) := by
          intro q
          induction q with
          | one => simp [encodePosNum]
          | bit1 q ih =>
            simp only [encodePosNum, List.length_cons, Nat.add_sub_cancel, PosNum.cast_bit1]
            have h1 : 1 ≤ (encodePosNum q).length := by cases q <;> simp [encodePosNum]
            have : 2 ^ (encodePosNum q).length = 2 * 2 ^ ((encodePosNum q).length - 1) := by
              rw [← pow_succ']; congr 1; omega
            rw [this]; simp; omega
          | bit0 q ih =>
            simp only [encodePosNum, List.length_cons, Nat.add_sub_cancel, PosNum.cast_bit0]
            have h1 : 1 ≤ (encodePosNum q).length := by cases q <;> simp [encodePosNum]
            have : 2 ^ (encodePosNum q).length = 2 * 2 ^ ((encodePosNum q).length - 1) := by
              rw [← pow_succ']; congr 1; omega
            rw [this]; simp; omega
        have ht := top p
        rw [← hNp] at ht
        have h1 : 1 ≤ (encodePosNum p).length := by cases p <;> simp [encodePosNum]
        have : (encodePosNum p).length - 1 < Nat.size N := Nat.lt_size.2 ht
        omega
    · exact Nat.size_le.2 hle
  rw [key, key]; exact Nat.size_le_size h

/-- If every coefficient is `≤ m`, the block length is the length of `m`. -/
theorem blockLen_cons_of_le {m : ℕ} {a : List ℕ} (h : ∀ c ∈ a, c ≤ m) :
    blockLen (m :: a) = (encodeNat m).length := by
  apply le_antisymm
  · apply blockLen_le
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact le_rfl
    · exact length_encodeNat_mono (h v hv)
  · exact length_encodeNat_le_blockLen (by simp)

/-! ## The word -/

theorem length_flatten_const {xs : List (List Bool)} {L : ℕ} (h : ∀ b ∈ xs, b.length = L) :
    xs.flatten.length = xs.length * L := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    rw [List.flatten_cons, List.length_append, h b (by simp), ih fun c hc => h c (by simp [hc]),
      List.length_cons]
    ring

theorem drop_flatten_const {xs : List (List Bool)} {L : ℕ} (h : ∀ b ∈ xs, b.length = L) (j : ℕ) :
    xs.flatten.drop (j * L) = (xs.drop j).flatten := by
  induction xs generalizing j with
  | nil => simp
  | cons b xs ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.flatten_cons, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
        List.drop_left' (h b (by simp)), ih (fun c hc => h c (by simp [hc])) j]
      rfl

theorem length_block {l : List ℕ} {b : List Bool}
    (hb : b ∈ l.map fun v => padR (blockLen l) (encodeNat v)) : b.length = blockLen l := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
  exact length_padR_of_le (length_encodeNat_le_blockLen hv)

theorem length_encodeList (l : List ℕ) : (encodeList l).length = l.length * blockLen l := by
  rw [encodeList, length_flatten_const (fun b hb => length_block hb), List.length_map]

theorem encodeList_div_length {l : List ℕ} (hl : l ≠ []) :
    (encodeList l).length / l.length = blockLen l := by
  rw [length_encodeList]
  exact Nat.mul_div_cancel_left _ (List.length_pos_iff.2 hl)

/-- Sanity: the two-entry list is the pair encoding of (A). -/
theorem encodeList_pair (m a : ℕ) : encodeList [m, a] = encodePair m a := by
  have hb : blockLen [m, a] = pairLen m a := by
    simp [blockLen, pairLen]
  simp [encodeList, encodePair_eq, hb]

/-! ## The block reader -/

/-- The `j`-th block of `encodeList l` is the `j`-th entry. -/
theorem leBlk_encodeList {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    leBlk l.length j (encodeList l) = l.getD j 0 := by
  have hl : l ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [leBlk, encodeList_div_length hl, encodeList,
    drop_flatten_const (fun b hb => length_block hb), ← List.map_drop]
  rw [List.drop_eq_getElem_cons hj, List.map_cons, List.flatten_cons,
    List.take_left' (length_padR_of_le (length_encodeNat_le_blockLen (List.getElem_mem _))),
    leVal_padR, leVal_encodeNat, List.getD_eq_getElem _ _ hj]

/-- Any block value is `< 2 ^ (|w| / nb)`. -/
theorem leBlk_lt (nb j : ℕ) (w : List Bool) : leBlk nb j w < 2 ^ (w.length / nb) := by
  unfold leBlk
  refine (leVal_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  rw [List.length_take]; exact min_le_left _ _

/-! ## Sanity checks -/

example : encodeList [7, 2] = encodePair 7 2 := by decide
example : blockLen [7, 1, 1, 1] = 3 := by decide
example : encodeList [7, 1, 1, 1] =
    [true, true, true, true, false, false, true, false, false, true, false, false] := by decide
example : leBlk 4 1 (encodeList [7, 1, 2, 1]) = 1 := by decide
example : leBlk 4 2 (encodeList [7, 1, 2, 1]) = 2 := by decide

end EthFollowup.ModP
