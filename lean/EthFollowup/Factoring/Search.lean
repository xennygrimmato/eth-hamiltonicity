/-
# Binary search for `Nat.minFac` with a divisor-counting oracle (module F6a, pure Mathlib)

* `word n d`: the big-endian `n`-bit word of `d` (bit `n-1` first); `ofWord`: its value.
  `ofWord_word`, `word_ofWord`, `ofWord_inj`, `ofWord_lt`, `word_add` (high/low split),
  `prefix_word_iff` (a word `π` of length `t ≤ n` is a prefix of `word n d` iff
  `ofWord π = d / 2^(n-t)`), `ofWord_lt_iff_lex` (lexicographic = numeric on equal lengths).
* `D N n' n π`: the number of pairs `(p, q) ∈ [0, 2^n')²` with `p * q = N` and
  `p / 2^(n - |π|) = ofWord π`; `D_eq_card_divisors`: for `1 ≤ N < 2^n`, `n ≤ n'`, it counts
  the divisors `d ∣ N` with that prefix.
* `cnt' N n' n π := D N n' n π - [1 has prefix π]` (`cnt'_eq`: divisors `≠ 1` with prefix `π`).
* `searchStep cnt π` (one oracle query), `searchWith cnt k := (searchStep cnt)^[k] []`,
  `search N n := searchWith (cnt' N n n) n`.
  `searchWith_eq_minFac`: for any oracle agreeing in positivity with `cnt'` on the queried words,
  `ofWord (searchWith cnt n) = Nat.minFac N` when `2 ≤ N < 2^n`; `search_eq_minFac`, `search_eq_word`.
* `N = 0, 1`: `minFac_zero'`, `minFac_one'`; `minFacVia_eq` (all `N`).
* `Computability.encodeNat` (little-endian `PosNum` bits): `length_encodeNat` (`= Nat.size N`),
  `lt_two_pow_length_encodeNat`, `two_pow_length_encodeNat_le`.

Standard axioms only.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring.Search

open Finset

/-! ## Big-endian words -/

/-- The big-endian `n`-bit word of `d`: bits `n-1, …, 0`. -/
def word : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, d => d.testBit n :: word n d

/-- The value of a big-endian word. -/
def ofWord (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + b.toNat) 0

@[simp] theorem word_zero (d : ℕ) : word 0 d = [] := rfl

theorem word_succ (n d : ℕ) : word (n + 1) d = d.testBit n :: word n d := rfl

@[simp] theorem length_word (n d : ℕ) : (word n d).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [word_succ, ih]

@[simp] theorem ofWord_nil : ofWord [] = 0 := rfl

theorem ofWord_append_singleton (l : List Bool) (b : Bool) :
    ofWord (l ++ [b]) = 2 * ofWord l + b.toNat := by
  simp [ofWord, List.foldl_append]

theorem foldl_ofWord (l : List Bool) (a : ℕ) :
    l.foldl (fun a b => 2 * a + b.toNat) a = a * 2 ^ l.length + ofWord l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons, ofWord]
    rw [ih, ih (2 * 0 + b.toNat), ofWord]
    ring

theorem ofWord_cons (b : Bool) (l : List Bool) :
    ofWord (b :: l) = b.toNat * 2 ^ l.length + ofWord l := by
  rw [ofWord, List.foldl_cons, foldl_ofWord]; simp [ofWord]

theorem ofWord_lt (l : List Bool) : ofWord l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [ofWord_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem ofWord_word (n d : ℕ) : ofWord (word n d) = d % 2 ^ n := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [word_succ, ofWord_cons, ih, length_word, Nat.toNat_testBit, Nat.mod_pow_succ]
    ring

theorem ofWord_word_of_lt {n d : ℕ} (h : d < 2 ^ n) : ofWord (word n d) = d := by
  rw [ofWord_word, Nat.mod_eq_of_lt h]

theorem ofWord_inj {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length)
    (h : ofWord l₁ = ofWord l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons b₁ l₁ ih => cases l₂ with
    | nil => simp at hl
    | cons b₂ l₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [ofWord_cons, ofWord_cons, hl] at h
      have h₁ := ofWord_lt l₁
      have h₂ := ofWord_lt l₂
      rw [hl] at h₁
      have hb : b₁ = b₂ := by
        cases b₁ <;> cases b₂ <;> simp at h ⊢ <;> omega
      subst hb
      rw [ih hl (by omega)]

theorem word_ofWord (l : List Bool) : word l.length (ofWord l) = l :=
  ofWord_inj (by simp) (by rw [ofWord_word_of_lt (ofWord_lt l)])

theorem word_eq_iff {n d : ℕ} {l : List Bool} (hd : d < 2 ^ n) (hl : l.length = n) :
    l = word n d ↔ ofWord l = d := by
  constructor
  · rintro rfl; exact ofWord_word_of_lt hd
  · intro h; exact ofWord_inj (by simp [hl]) (by rw [h, ofWord_word_of_lt hd])

/-- High/low split of a word: the top `t` bits are the word of `d / 2^s`. -/
theorem word_add (t s d : ℕ) : word (t + s) d = word t (d / 2 ^ s) ++ word s d := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_right_comm, word_succ, ih, word_succ, Nat.testBit_div_two_pow]
    rfl

theorem div_lt_of_lt_two_pow {n d t : ℕ} (hd : d < 2 ^ n) (ht : t ≤ n) :
    d / 2 ^ (n - t) < 2 ^ t := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' ht]
  exact hd

/-- A word `π` of length `≤ n` is a prefix of `word n d` iff `ofWord π = d / 2^(n - |π|)`. -/
theorem prefix_word_iff {n d : ℕ} {π : List Bool} (hd : d < 2 ^ n) (ht : π.length ≤ n) :
    π <+: word n d ↔ ofWord π = d / 2 ^ (n - π.length) := by
  have hsplit : word n d = word π.length (d / 2 ^ (n - π.length)) ++ word (n - π.length) d := by
    rw [← word_add, Nat.add_sub_cancel' ht]
  have hlt := div_lt_of_lt_two_pow hd ht
  rw [hsplit]
  constructor
  · intro h
    rw [List.prefix_iff_eq_take, List.take_left' (length_word _ _)] at h
    have e := congrArg ofWord h
    rwa [ofWord_word_of_lt hlt] at e
  · intro h
    have e := (word_eq_iff hlt rfl).2 h
    refine ⟨word (n - π.length) d, ?_⟩
    nth_rewrite 1 [e]
    rfl

/-- Lexicographic order on words of equal length is numeric order. -/
theorem ofWord_lt_iff_lex {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length) :
    ofWord l₁ < ofWord l₂ ↔ List.Lex (· < ·) l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => simp
    | cons _ _ => simp at hl
  | cons b₁ l₁ ih => cases l₂ with
    | nil => simp at hl
    | cons b₂ l₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [List.cons_lex_cons_iff, ofWord_cons, ofWord_cons, hl, ← ih hl, Bool.lt_iff]
      have h₁ := ofWord_lt l₁
      have h₂ := ofWord_lt l₂
      rw [hl] at h₁
      cases b₁ <;> cases b₂ <;> simp <;> omega

/-! ## The counting function and divisors -/

/-- `#{(p, q) ∈ [0, 2^n')² : p * q = N ∧ p / 2^(n - |π|) = ofWord π}`. -/
def D (N n' n : ℕ) (π : List Bool) : ℕ :=
  ((range (2 ^ n') ×ˢ range (2 ^ n')).filter
    (fun pq : ℕ × ℕ => pq.1 * pq.2 = N ∧ pq.1 / 2 ^ (n - π.length) = ofWord π)).card

theorem D_eq_card_divisors {N n' n : ℕ} (π : List Bool) (hN : 1 ≤ N) (hNn : N < 2 ^ n)
    (hn : n ≤ n') :
    D N n' n π = ((Nat.divisors N).filter (fun d => d / 2 ^ (n - π.length) = ofWord π)).card := by
  have hpow : 2 ^ n ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn
  have hset : (range (2 ^ n') ×ˢ range (2 ^ n')).filter
      (fun pq : ℕ × ℕ => pq.1 * pq.2 = N ∧ pq.1 / 2 ^ (n - π.length) = ofWord π) =
      (Nat.divisorsAntidiagonal N).filter
        (fun pq : ℕ × ℕ => pq.1 / 2 ^ (n - π.length) = ofWord π) := by
    ext ⟨p, q⟩
    simp only [mem_filter, mem_product, mem_range, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨-, h, h'⟩; exact ⟨⟨h, by omega⟩, h'⟩
    · rintro ⟨⟨h, -⟩, h'⟩
      have hp : p ≤ N := Nat.le_of_dvd hN ⟨q, h.symm⟩
      have hq : q ≤ N := Nat.le_of_dvd hN ⟨p, by rw [← h, mul_comm]⟩
      exact ⟨⟨by omega, by omega⟩, h, h'⟩
  rw [D, hset, ← Nat.map_div_right_divisors, filter_map, card_map]
  rfl

/-- The count with the trivial divisor `1` removed. -/
def cnt' (N n' n : ℕ) (π : List Bool) : ℕ :=
  D N n' n π - if 1 / 2 ^ (n - π.length) = ofWord π then 1 else 0

theorem cnt'_eq {N n' n : ℕ} (π : List Bool) (hN : 1 ≤ N) (hNn : N < 2 ^ n) (hn : n ≤ n') :
    cnt' N n' n π =
      ((Nat.divisors N).filter (fun d => d ≠ 1 ∧ d / 2 ^ (n - π.length) = ofWord π)).card := by
  have he : (Nat.divisors N).filter (fun d => d ≠ 1 ∧ d / 2 ^ (n - π.length) = ofWord π) =
      ((Nat.divisors N).filter (fun d => d / 2 ^ (n - π.length) = ofWord π)).erase 1 := by
    ext d; simp only [mem_filter, mem_erase]; tauto
  rw [cnt', D_eq_card_divisors π hN hNn hn, he]
  split_ifs with h1
  · rw [card_erase_of_mem]
    simp only [mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd N, by omega⟩, h1⟩
  · rw [erase_eq_of_notMem (by simp [h1]), Nat.sub_zero]

theorem cnt'_pos_iff {N n' n : ℕ} (π : List Bool) (hN : 1 ≤ N) (hNn : N < 2 ^ n) (hn : n ≤ n') :
    0 < cnt' N n' n π ↔
      ∃ d, d ∣ N ∧ d ≠ 1 ∧ d / 2 ^ (n - π.length) = ofWord π := by
  rw [cnt'_eq π hN hNn hn, card_pos, filter_nonempty_iff]
  simp only [Nat.mem_divisors]
  constructor
  · rintro ⟨d, ⟨hd, -⟩, h⟩; exact ⟨d, hd, h⟩
  · rintro ⟨d, hd, h⟩; exact ⟨d, ⟨hd, by omega⟩, h⟩

/-- "`1` has prefix `π`" is the numeric test in `cnt'`. -/
theorem one_prefix_iff {n : ℕ} {π : List Bool} (hn : 1 ≤ n) (ht : π.length ≤ n) :
    π <+: word n 1 ↔ 1 / 2 ^ (n - π.length) = ofWord π := by
  rw [prefix_word_iff (Nat.one_lt_two_pow (by omega)) ht, eq_comm]

/-! ## The search -/

/-- One round: one query of the oracle `cnt` on `π ++ [false]`. -/
def searchStep (cnt : List Bool → ℕ) (π : List Bool) : List Bool :=
  if 0 < cnt (π ++ [false]) then π ++ [false] else π ++ [true]

/-- `k` rounds from the empty word. -/
def searchWith (cnt : List Bool → ℕ) (k : ℕ) : List Bool := (searchStep cnt)^[k] []

/-- The search with the exact oracle `cnt'`. -/
def search (N n : ℕ) : List Bool := searchWith (cnt' N n n) n

theorem searchWith_succ (cnt : List Bool → ℕ) (k : ℕ) :
    searchWith cnt (k + 1) = searchStep cnt (searchWith cnt k) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem length_searchWith (cnt : List Bool → ℕ) (k : ℕ) :
    (searchWith cnt k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [searchWith_succ, searchStep]; split_ifs <;> simp [ih]

/-- One round keeps the invariant `ofWord π = minFac N / 2^(n - |π|)`. -/
theorem step_inv {N n' n : ℕ} {cnt : List Bool → ℕ} {π : List Bool} (hN : 2 ≤ N)
    (hNn : N < 2 ^ n) (hn : n ≤ n') (ht : π.length < n)
    (hcnt : 0 < cnt (π ++ [false]) ↔ 0 < cnt' N n' n (π ++ [false]))
    (hπ : ofWord π = Nat.minFac N / 2 ^ (n - π.length)) :
    ofWord (searchStep cnt π) = Nat.minFac N / 2 ^ (n - (π.length + 1)) := by
  set m := Nat.minFac N
  set s := n - (π.length + 1)
  have hs : n - π.length = s + 1 := by omega
  have hdiv : m / 2 ^ (s + 1) = m / 2 ^ s / 2 := by rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hs, hdiv] at hπ
  have hlen : n - (π ++ [false]).length = s := by simp [s]
  have hkey : 0 < cnt (π ++ [false]) ↔ m / 2 ^ s = 2 * ofWord π := by
    rw [hcnt, cnt'_pos_iff _ (by omega) hNn hn, hlen, ofWord_append_singleton, hπ]
    simp only [Bool.toNat_false, Nat.add_zero]
    constructor
    · rintro ⟨d, hd, hd1, h⟩
      have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
      have hmd : m ≤ d := Nat.minFac_le_of_dvd (by omega) hd
      have := Nat.div_le_div_right (c := 2 ^ s) hmd
      omega
    · intro h
      exact ⟨m, Nat.minFac_dvd N, (Nat.minFac_prime (by omega)).one_lt.ne', h⟩
  rw [searchStep]
  split_ifs with h
  · rw [ofWord_append_singleton, ← hkey.1 h]; simp
  · rw [ofWord_append_singleton, hπ]
    rw [hkey, hπ] at h
    simp only [Bool.toNat_true]
    omega

theorem searchWith_inv {N n' n : ℕ} {cnt : List Bool → ℕ} (hN : 2 ≤ N) (hNn : N < 2 ^ n)
    (hn : n ≤ n')
    (hcnt : ∀ π : List Bool, π.length < n →
      (0 < cnt (π ++ [false]) ↔ 0 < cnt' N n' n (π ++ [false])))
    {k : ℕ} (hk : k ≤ n) :
    ofWord (searchWith cnt k) = Nat.minFac N / 2 ^ (n - k) := by
  induction k with
  | zero =>
    have hm : Nat.minFac N < 2 ^ n := lt_of_le_of_lt (Nat.minFac_le (by omega)) hNn
    rw [Nat.div_eq_of_lt (by simpa using hm)]; rfl
  | succ k ih =>
    have h := step_inv (cnt := cnt) (π := searchWith cnt k) hN hNn hn (by simp; omega)
      (hcnt _ (by simp; omega)) (by rw [ih (by omega), length_searchWith])
    rw [searchWith_succ, h, length_searchWith]

/-- The invariant as a prefix statement. -/
theorem searchWith_prefix {N n' n : ℕ} {cnt : List Bool → ℕ} (hN : 2 ≤ N) (hNn : N < 2 ^ n)
    (hn : n ≤ n')
    (hcnt : ∀ π : List Bool, π.length < n →
      (0 < cnt (π ++ [false]) ↔ 0 < cnt' N n' n (π ++ [false])))
    {k : ℕ} (hk : k ≤ n) :
    searchWith cnt k <+: word n (Nat.minFac N) := by
  have hm : Nat.minFac N < 2 ^ n := lt_of_le_of_lt (Nat.minFac_le (by omega)) hNn
  rw [prefix_word_iff hm (by simpa using hk), length_searchWith]
  exact searchWith_inv hN hNn hn hcnt hk

/-- **The search finds `minFac N`** for any oracle agreeing in positivity with `cnt'` on the
queried words. -/
theorem searchWith_eq_minFac {N n' n : ℕ} {cnt : List Bool → ℕ} (hN : 2 ≤ N) (hNn : N < 2 ^ n)
    (hn : n ≤ n')
    (hcnt : ∀ π : List Bool, π.length < n →
      (0 < cnt (π ++ [false]) ↔ 0 < cnt' N n' n (π ++ [false]))) :
    ofWord (searchWith cnt n) = Nat.minFac N := by
  rw [searchWith_inv hN hNn hn hcnt le_rfl, Nat.sub_self, pow_zero, Nat.div_one]

/-- The same for an oracle equal to `cnt'` on all words of length `≤ n`. -/
theorem searchWith_eq_minFac' {N n' n : ℕ} {cnt : List Bool → ℕ} (hN : 2 ≤ N) (hNn : N < 2 ^ n)
    (hn : n ≤ n') (hcnt : ∀ π : List Bool, π.length ≤ n → cnt π = cnt' N n' n π) :
    ofWord (searchWith cnt n) = Nat.minFac N :=
  searchWith_eq_minFac hN hNn hn fun π hπ => by
    rw [hcnt _ (by simp; omega)]

theorem search_eq_minFac {N n : ℕ} (hN : 2 ≤ N) (hNn : N < 2 ^ n) :
    ofWord (search N n) = Nat.minFac N :=
  searchWith_eq_minFac' hN hNn le_rfl fun _ _ => rfl

theorem search_eq_word {N n : ℕ} (hN : 2 ≤ N) (hNn : N < 2 ^ n) :
    search N n = word n (Nat.minFac N) := by
  have hm : Nat.minFac N < 2 ^ n := lt_of_le_of_lt (Nat.minFac_le (by omega)) hNn
  exact (word_eq_iff hm (length_searchWith _ _)).2 (search_eq_minFac hN hNn)

/-! ## The cases `N = 0, 1` -/

theorem minFac_zero' : Nat.minFac 0 = 2 := Nat.minFac_zero

theorem minFac_one' : Nat.minFac 1 = 1 := Nat.minFac_one

/-! ## Mathlib's `encodeNat` (little-endian `PosNum` bits) -/

theorem encodePosNum_bounds (p : PosNum) :
    (p : ℕ) < 2 ^ (Computability.encodePosNum p).length ∧
      2 ^ (Computability.encodePosNum p).length ≤ 2 * (p : ℕ) := by
  induction p with
  | one => simp [Computability.encodePosNum]
  | bit1 p ih =>
    simp only [Computability.encodePosNum, List.length_cons, PosNum.cast_bit1, pow_succ]
    omega
  | bit0 p ih =>
    simp only [Computability.encodePosNum, List.length_cons, PosNum.cast_bit0, pow_succ]
    omega

theorem encodeNat_bounds (N : ℕ) :
    N < 2 ^ (Computability.encodeNat N).length ∧
      (N ≠ 0 → 2 ^ (Computability.encodeNat N).length ≤ 2 * N) := by
  have hN := Num.to_of_nat N
  unfold Computability.encodeNat
  cases h : (N : Num) with
  | zero =>
    rw [h] at hN
    simp [Computability.encodeNum, ← hN]
  | pos p =>
    rw [h] at hN
    have := encodePosNum_bounds p
    simp only [Computability.encodeNum]
    rw [← hN]
    exact ⟨this.1, fun _ => this.2⟩

theorem lt_two_pow_length_encodeNat (N : ℕ) : N < 2 ^ (Computability.encodeNat N).length :=
  (encodeNat_bounds N).1

theorem two_pow_length_encodeNat_le {N : ℕ} (hN : N ≠ 0) :
    2 ^ (Computability.encodeNat N).length ≤ 2 * N :=
  (encodeNat_bounds N).2 hN

theorem length_encodeNat (N : ℕ) : (Computability.encodeNat N).length = Nat.size N := by
  apply le_antisymm
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · have := lt_two_pow_length_encodeNat 0
      have h : (Computability.encodeNat 0).length = 0 := by decide
      rw [h]; exact Nat.zero_le _
    · have h2 := two_pow_length_encodeNat_le hN.ne'
      by_contra hlt
      rw [not_le] at hlt
      have := (Nat.size_le).1 (Nat.le_sub_one_of_lt hlt)
      have hl : 1 ≤ (Computability.encodeNat N).length := by omega
      have : 2 ^ (Computability.encodeNat N).length = 2 * 2 ^ ((Computability.encodeNat N).length - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hl]
      omega
  · exact Nat.size_le.2 (lt_two_pow_length_encodeNat N)

theorem search_encodeNat_eq_minFac {N : ℕ} (hN : 2 ≤ N) :
    ofWord (search N (Computability.encodeNat N).length) = Nat.minFac N :=
  search_eq_minFac hN (lt_two_pow_length_encodeNat N)

/-- `Nat.minFac` for every `N`: the cases `N = 0, 1` directly, the search otherwise. -/
def minFacVia (N : ℕ) : ℕ :=
  if N < 2 then (if N = 0 then 2 else 1) else ofWord (search N (Computability.encodeNat N).length)

theorem minFacVia_eq (N : ℕ) : minFacVia N = Nat.minFac N := by
  unfold minFacVia
  split_ifs with h h0
  · subst h0; exact Nat.minFac_zero.symm
  · have : N = 1 := by omega
    subst this; exact Nat.minFac_one.symm
  · exact search_encodeNat_eq_minFac (by omega)

/-! ## Sanity checks on small instances -/

example : word 4 6 = [false, true, true, false] := by decide
example : ofWord [true, false, true] = 5 := by decide
example : D 6 3 3 [false, true] = 2 := by decide
example : cnt' 6 3 3 [false] = 2 := by decide
example : search 15 4 = [false, false, true, true] := by decide

end EthFollowup.Factoring.Search
