/-
# Prefix search for the minimum of a finite set (module M3, pure Mathlib)

Generic version of `Factoring.Search.searchWith_inv` with `Nat.minFac N` replaced by `S.min'`:
for `S ⊆ [0, 2^n)` and an oracle `cnt` with
`0 < cnt (π ++ [false]) ↔ ∃ y ∈ S, y / 2^(n - |π| - 1) = ofWord (π ++ [false])` for `|π| < n`,
`Search.searchWith cnt n` is the big-endian word of `S.min'` (`searchWith_eq_min'`), and if `S`
is empty the search returns `List.replicate n true` (`searchWith_eq_replicate`).

* `minStep_inv`, `minSearch_inv`: the invariant `ofWord π = S.min' / 2^(n - |π|)`.
* `searchWith_eq_min'`, `searchWith_eq_word_min'`, `searchWith_prefix_min'` (prefix form of the
  oracle hypothesis: `searchWith_eq_min'_of_prefix`).
* `searchWith_eq_replicate` (oracle `0` on all queries), `searchWith_eq_replicate_of_empty`,
  `ofWord_replicate_true`, `searchWith_eq_minOr` (both cases at once).

Standard axioms only.
-/
import EthFollowup.Factoring.Search
import Mathlib.Data.Finset.Max

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset EthFollowup.Factoring.Search

/-- One round keeps the invariant `ofWord π = S.min' / 2^(n - |π|)`. -/
theorem minStep_inv {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty) {cnt : List Bool → ℕ}
    {π : List Bool} (ht : π.length < n)
    (hcnt : 0 < cnt (π ++ [false]) ↔
      ∃ y ∈ S, y / 2 ^ (n - (π ++ [false]).length) = ofWord (π ++ [false]))
    (hπ : ofWord π = S.min' hS / 2 ^ (n - π.length)) :
    ofWord (searchStep cnt π) = S.min' hS / 2 ^ (n - (π.length + 1)) := by
  set m := S.min' hS
  set s := n - (π.length + 1)
  have hs : n - π.length = s + 1 := by omega
  have hdiv : m / 2 ^ (s + 1) = m / 2 ^ s / 2 := by rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hs, hdiv] at hπ
  have hlen : n - (π ++ [false]).length = s := by simp [s]
  have hkey : 0 < cnt (π ++ [false]) ↔ m / 2 ^ s = 2 * ofWord π := by
    rw [hcnt, hlen, ofWord_append_singleton, hπ]
    simp only [Bool.toNat_false, Nat.add_zero]
    constructor
    · rintro ⟨y, hy, h⟩
      have hmy : m ≤ y := S.min'_le y hy
      have := Nat.div_le_div_right (c := 2 ^ s) hmy
      omega
    · intro h
      exact ⟨m, S.min'_mem hS, h⟩
  rw [searchStep]
  split_ifs with h
  · rw [ofWord_append_singleton, ← hkey.1 h]; simp
  · rw [ofWord_append_singleton, hπ]
    rw [hkey, hπ] at h
    simp only [Bool.toNat_true]
    omega

/-- The invariant after `k ≤ n` rounds. -/
theorem minSearch_inv {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSn : ∀ y ∈ S, y < 2 ^ n)
    {cnt : List Bool → ℕ}
    (hcnt : ∀ π : List Bool, π.length < n → (0 < cnt (π ++ [false]) ↔
      ∃ y ∈ S, y / 2 ^ (n - (π ++ [false]).length) = ofWord (π ++ [false])))
    {k : ℕ} (hk : k ≤ n) :
    ofWord (searchWith cnt k) = S.min' hS / 2 ^ (n - k) := by
  induction k with
  | zero =>
    have hm : S.min' hS < 2 ^ n := hSn _ (S.min'_mem hS)
    rw [Nat.div_eq_of_lt (by simpa using hm)]; rfl
  | succ k ih =>
    have h := minStep_inv (cnt := cnt) (π := searchWith cnt k) hS (by simp; omega)
      (hcnt _ (by simp; omega)) (by rw [ih (by omega), length_searchWith])
    rw [searchWith_succ, h, length_searchWith]

/-- **The search finds `S.min'`** (numeric form of the oracle hypothesis). -/
theorem searchWith_eq_min' {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSn : ∀ y ∈ S, y < 2 ^ n)
    {cnt : List Bool → ℕ}
    (hcnt : ∀ π : List Bool, π.length < n → (0 < cnt (π ++ [false]) ↔
      ∃ y ∈ S, y / 2 ^ (n - (π ++ [false]).length) = ofWord (π ++ [false]))) :
    ofWord (searchWith cnt n) = S.min' hS := by
  rw [minSearch_inv hS hSn hcnt le_rfl, Nat.sub_self, pow_zero, Nat.div_one]

theorem searchWith_eq_word_min' {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSn : ∀ y ∈ S, y < 2 ^ n) {cnt : List Bool → ℕ}
    (hcnt : ∀ π : List Bool, π.length < n → (0 < cnt (π ++ [false]) ↔
      ∃ y ∈ S, y / 2 ^ (n - (π ++ [false]).length) = ofWord (π ++ [false]))) :
    searchWith cnt n = word n (S.min' hS) :=
  (word_eq_iff (hSn _ (S.min'_mem hS)) (length_searchWith _ _)).2 (searchWith_eq_min' hS hSn hcnt)

/-- The search with the oracle hypothesis in prefix form: `0 < cnt (π ++ [false])` iff some
`y ∈ S` has `π ++ [false]` as a prefix of its `n`-bit word. -/
theorem searchWith_eq_min'_of_prefix {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSn : ∀ y ∈ S, y < 2 ^ n) {cnt : List Bool → ℕ}
    (hcnt : ∀ π : List Bool, π.length < n →
      (0 < cnt (π ++ [false]) ↔ ∃ y ∈ S, π ++ [false] <+: word n y)) :
    ofWord (searchWith cnt n) = S.min' hS := by
  refine searchWith_eq_min' hS hSn fun π hπ => ?_
  rw [hcnt π hπ]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, ((prefix_word_iff (hSn y hy) (by simp; omega)).1 h).symm⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, (prefix_word_iff (hSn y hy) (by simp; omega)).2 h.symm⟩

/-- The search result is a prefix of the word of `S.min'` after every `k ≤ n` rounds. -/
theorem searchWith_prefix_min' {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSn : ∀ y ∈ S, y < 2 ^ n) {cnt : List Bool → ℕ}
    (hcnt : ∀ π : List Bool, π.length < n → (0 < cnt (π ++ [false]) ↔
      ∃ y ∈ S, y / 2 ^ (n - (π ++ [false]).length) = ofWord (π ++ [false])))
    {k : ℕ} (hk : k ≤ n) :
    searchWith cnt k <+: word n (S.min' hS) := by
  rw [prefix_word_iff (hSn _ (S.min'_mem hS)) (by simpa using hk), length_searchWith]
  exact minSearch_inv hS hSn hcnt hk

/-! ## The empty case -/

/-- An oracle that is `0` on all queried words drives the search to `1 1 … 1`. -/
theorem searchWith_eq_replicate {n : ℕ} {cnt : List Bool → ℕ}
    (h0 : ∀ π : List Bool, π.length < n → cnt (π ++ [false]) = 0) {k : ℕ} (hk : k ≤ n) :
    searchWith cnt k = List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [searchWith_succ, ih (by omega), searchStep, h0 _ (by simp; omega)]
    simp [List.replicate_succ']

theorem ofWord_replicate_true (k : ℕ) : ofWord (List.replicate k true) = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', ofWord_append_singleton, ih, pow_succ]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [Bool.toNat_true]
    omega

/-- With the counting oracle of an empty set the search returns `1 1 … 1`. -/
theorem searchWith_eq_replicate_of_empty {n : ℕ} {S : Finset ℕ} (hS : S = ∅)
    {cnt : List Bool → ℕ}
    (hcnt : ∀ π : List Bool, π.length < n → (0 < cnt (π ++ [false]) ↔
      ∃ y ∈ S, y / 2 ^ (n - (π ++ [false]).length) = ofWord (π ++ [false]))) :
    searchWith cnt n = List.replicate n true :=
  searchWith_eq_replicate (fun π hπ => by
    have := hcnt π hπ
    subst hS
    simp only [notMem_empty, false_and, exists_false, iff_false] at this
    omega) le_rfl

/-- Both cases at once: the value of the search is `S.min'` or, for empty `S`, `2^n - 1`. -/
theorem searchWith_eq_minOr {n : ℕ} {S : Finset ℕ} (hSn : ∀ y ∈ S, y < 2 ^ n)
    {cnt : List Bool → ℕ}
    (hcnt : ∀ π : List Bool, π.length < n → (0 < cnt (π ++ [false]) ↔
      ∃ y ∈ S, y / 2 ^ (n - (π ++ [false]).length) = ofWord (π ++ [false]))) :
    ofWord (searchWith cnt n) = if hS : S.Nonempty then S.min' hS else 2 ^ n - 1 := by
  split_ifs with hS
  · exact searchWith_eq_min' hS hSn hcnt
  · rw [searchWith_eq_replicate_of_empty (Finset.not_nonempty_iff_eq_empty.1 hS) hcnt,
      ofWord_replicate_true]

/-! ## Sanity checks -/

/-- Least element of `{3, 5, 6}` in 3 bits via its prefix-counting oracle. -/
example : searchWith (fun π => (({3, 5, 6} : Finset ℕ).filter
    fun y => y / 2 ^ (3 - π.length) = ofWord π).card) 3 = [false, true, true] := by decide

end EthFollowup.ModP
