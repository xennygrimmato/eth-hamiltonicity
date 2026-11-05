/-
# The search specifications of the root finders and their answers (roots-plan.md §3–§4, H5)

On the input `w` (blocks of length `|w| / nb`, `nb = d + 2` resp. `d + 3`), with the readers
`rdBlk nb j w` (value of block `j`), `rdCo d w` (coefficients, blocks `1..d+1`, reduced mod block 0)
and `rdCoN d w` (nextRoot: blocks `2..d+2`; block 1 is `lo`):

* `specP d : SearchSpec` (least root): `pre := m < 2`, `small := []`, `step := stepPos`,
  `fin := finR (d+2)` (`Nat.bits (y if y < m else m)`, `y = ofWord π.reverse`); **no root ⇒ `m`**.
* `specNext d : SearchSpec` (least root `≥ lo`): as `specP` with `nb = d + 3`,
  `small := Nat.bits (min lo m)` (`nextRootP 0 a lo = 0`, `nextRootP 1 a lo = min lo 1`).
* `specCnt d : GR.QuerySpec` (number of roots): `pre := m = 0`, `small := []`, `q1 = q2 := []`,
  `fin := Nat.bits c₁`.
* PolyT of all fields; lengths (`finR_length`, `specP_small_length`, `specNext_small_length`,
  `specCnt_length`).
* **`specP_answer`**, **`specNext_answer`**, **`specCnt_answer`** on any word, and on the input
  `encodeList (m :: a)` (resp. `encodeList (m :: lo :: a)`), `a.length = d + 1`:
  **`specP_answer_list`** `= encodeNat (minRootP m a)`, **`specNext_answer_list`**
  `= encodeNat (nextRootP m a lo)`, **`specCnt_answer_list`** `= encodeNat (rootSetP m a).card`.
  The count hypotheses `hQ` carry the premise `2 ≤ m` (`specP`, `specNext`) resp. `0 < m` (`specCnt`).

Standard axioms only.
-/
import EthFollowup.ModP.SpecSq
import EthFollowup.ModP.HornerCount
import EthFollowup.ModP.EncodeList

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork EthFollowup.Factoring Finset

/-! ## Readers (definitions as agreed with E2 in roots-interface.md) -/

/-- The value of the `j`-th of `nb` equal blocks of `w`. -/
def rdBlk (nb j : ℕ) (w : List Bool) : ℕ :=
  Groundwork.ofWord ((w.drop (j * (w.length / nb))).take (w.length / nb))

/-- The coefficients of the root problem (blocks `1..d+1`), reduced modulo block `0`. -/
def rdCo (d : ℕ) (w : List Bool) : List ℕ :=
  (List.range (d + 1)).map fun i => rdBlk (d + 2) (i + 1) w % rdBlk (d + 2) 0 w

/-- The coefficients of the next-root problem (blocks `2..d+2`), reduced modulo block `0`. -/
def rdCoN (d : ℕ) (w : List Bool) : List ℕ :=
  (List.range (d + 1)).map fun i => rdBlk (d + 3) (i + 2) w % rdBlk (d + 3) 0 w

theorem rdBlk_eq_leBlk (nb j : ℕ) (w : List Bool) : rdBlk nb j w = leBlk nb j w := by
  rw [rdBlk, leBlk, gofWord_eq_leVal]

theorem rdBlk_lt (nb j : ℕ) (w : List Bool) : rdBlk nb j w < 2 ^ (w.length / nb) := by
  rw [rdBlk_eq_leBlk]; exact leBlk_lt nb j w

theorem rdBlk_polyT (nb j : ℕ) : PolyT (rdBlk nb j) := by
  unfold rdBlk; fun_prop

theorem rdBlk_encodeList {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    rdBlk l.length j (encodeList l) = l.getD j 0 := by
  rw [rdBlk_eq_leBlk, leBlk_encodeList hj]

theorem map_range_getD_mod (a : List ℕ) (m : ℕ) {d : ℕ} (hlen : a.length = d + 1) :
    (List.range (d + 1)).map (fun i => a.getD i 0 % m) = a.map (· % m) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

theorem rdBlk_encodeList_zero (d m : ℕ) (a : List ℕ) (hlen : a.length = d + 1) :
    rdBlk (d + 2) 0 (encodeList (m :: a)) = m := by
  have h := rdBlk_encodeList (l := m :: a) (j := 0) (by simp)
  rw [List.length_cons, hlen] at h
  simpa using h

theorem rdCo_encodeList (d m : ℕ) (a : List ℕ) (hlen : a.length = d + 1) :
    rdCo d (encodeList (m :: a)) = a.map (· % m) := by
  have hl : (m :: a).length = d + 2 := by simp [hlen]
  have hb : ∀ i < d + 1, rdBlk (d + 2) (i + 1) (encodeList (m :: a)) = a.getD i 0 := by
    intro i hi
    have h := rdBlk_encodeList (l := m :: a) (j := i + 1) (by simp; omega)
    rw [hl] at h; simpa using h
  rw [rdCo, rdBlk_encodeList_zero d m a hlen, ← map_range_getD_mod a m hlen]
  apply List.map_congr_left
  intro i hi
  rw [hb i (List.mem_range.1 hi)]

theorem rdBlk_encodeList_zero' (d m lo : ℕ) (a : List ℕ) (hlen : a.length = d + 1) :
    rdBlk (d + 3) 0 (encodeList (m :: lo :: a)) = m := by
  have h := rdBlk_encodeList (l := m :: lo :: a) (j := 0) (by simp)
  rw [List.length_cons, List.length_cons, hlen] at h
  simpa using h

theorem rdBlk_encodeList_one (d m lo : ℕ) (a : List ℕ) (hlen : a.length = d + 1) :
    rdBlk (d + 3) 1 (encodeList (m :: lo :: a)) = lo := by
  have h := rdBlk_encodeList (l := m :: lo :: a) (j := 1) (by simp)
  rw [List.length_cons, List.length_cons, hlen] at h
  simpa using h

theorem rdCoN_encodeList (d m lo : ℕ) (a : List ℕ) (hlen : a.length = d + 1) :
    rdCoN d (encodeList (m :: lo :: a)) = a.map (· % m) := by
  have hl : (m :: lo :: a).length = d + 3 := by simp [hlen]
  have hb : ∀ i < d + 1, rdBlk (d + 3) (i + 2) (encodeList (m :: lo :: a)) = a.getD i 0 := by
    intro i hi
    have h := rdBlk_encodeList (l := m :: lo :: a) (j := i + 2) (by simp; omega)
    rw [hl] at h; simpa using h
  rw [rdCoN, rdBlk_encodeList_zero' d m lo a hlen, ← map_range_getD_mod a m hlen]
  apply List.map_congr_left
  intro i hi
  rw [hb i (List.mem_range.1 hi)]

/-! ## Facts on the targets used here (namespace `SH`, to avoid clashes with HornerCount) -/

namespace SH

theorem polyEvalMod_map_mod (m : ℕ) (a : List ℕ) (x : ℕ) :
    polyEvalMod m (a.map (· % m)) x = polyEvalMod m a x := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    simp only [polyEvalMod, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, Nat.add_mod_mod]

theorem rootSetP_map_mod (m : ℕ) (a : List ℕ) : rootSetP m (a.map (· % m)) = rootSetP m a := by
  simp only [rootSetP, polyEvalMod_map_mod]

/-- The least-root set `{x < m | lo ≤ x, f(x) ≡ 0}`. -/
def rootSetGe (m : ℕ) (a : List ℕ) (lo : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun x => lo ≤ x ∧ polyEvalMod m a x = 0

theorem rootSetGe_map_mod (m : ℕ) (a : List ℕ) (lo : ℕ) :
    rootSetGe m (a.map (· % m)) lo = rootSetGe m a lo := by
  simp only [rootSetGe, polyEvalMod_map_mod]

theorem mem_rootSetP {m : ℕ} {a : List ℕ} {x : ℕ} :
    x ∈ rootSetP m a ↔ x < m ∧ polyEvalMod m a x = 0 := by
  simp [rootSetP]

theorem mem_rootSetGe {m : ℕ} {a : List ℕ} {lo x : ℕ} :
    x ∈ rootSetGe m a lo ↔ x < m ∧ lo ≤ x ∧ polyEvalMod m a x = 0 := by
  simp [rootSetGe]

theorem minRootP_eq_minOr (m : ℕ) (a : List ℕ) :
    minRootP m a = if hS : (rootSetP m a).Nonempty then (rootSetP m a).min' hS else m := by
  unfold minRootP
  rw [Nat.find_eq_iff]
  split_ifs with hS
  · have hmem := (rootSetP m a).min'_mem hS
    rw [mem_rootSetP] at hmem
    refine ⟨Or.inr hmem, fun k hk h => ?_⟩
    rcases h with h | h
    · omega
    · have : k ∈ rootSetP m a := mem_rootSetP.2 h
      exact absurd ((rootSetP m a).min'_le k this) (by omega)
  · refine ⟨Or.inl rfl, fun k hk h => ?_⟩
    rcases h with h | h
    · omega
    · exact hS ⟨k, by simp [rootSetP, h.1, h.2]⟩

theorem nextRootP_eq_minOr (m : ℕ) (a : List ℕ) (lo : ℕ) :
    nextRootP m a lo = if hS : (rootSetGe m a lo).Nonempty then (rootSetGe m a lo).min' hS else m := by
  unfold nextRootP
  rw [Nat.find_eq_iff]
  split_ifs with hS
  · have hmem := (rootSetGe m a lo).min'_mem hS
    rw [mem_rootSetGe] at hmem
    refine ⟨Or.inr ⟨hmem.2.1, hmem.1, hmem.2.2⟩, fun k hk h => ?_⟩
    rcases h with h | h
    · omega
    · have : k ∈ rootSetGe m a lo := mem_rootSetGe.2 ⟨h.2.1, h.1, h.2.2⟩
      exact absurd ((rootSetGe m a lo).min'_le k this) (by omega)
  · refine ⟨Or.inl rfl, fun k hk h => ?_⟩
    rcases h with h | h
    · omega
    · exact hS ⟨k, by simp [rootSetGe, h.1, h.2.1, h.2.2]⟩

theorem minRootP_map_mod (m : ℕ) (a : List ℕ) : minRootP m (a.map (· % m)) = minRootP m a := by
  rw [minRootP_eq_minOr, minRootP_eq_minOr]; simp only [rootSetP_map_mod]

theorem nextRootP_map_mod (m : ℕ) (a : List ℕ) (lo : ℕ) :
    nextRootP m (a.map (· % m)) lo = nextRootP m a lo := by
  rw [nextRootP_eq_minOr, nextRootP_eq_minOr]; simp only [rootSetGe_map_mod]

theorem polyEvalMod_one (a : List ℕ) (x : ℕ) : polyEvalMod 1 a x = 0 := by
  cases a with
  | nil => rfl
  | cons c a => simp only [polyEvalMod, List.foldr_cons, Nat.mod_one]

theorem minRootP_lt_two (m : ℕ) (a : List ℕ) (hm : m < 2) : minRootP m a = 0 := by
  rw [minRootP_eq_minOr]
  split_ifs with hS
  · have := (rootSetP m a).min'_mem hS
    rw [mem_rootSetP] at this
    omega
  · by_contra h
    have hm1 : m = 1 := by omega
    exact hS ⟨0, by simp [rootSetP, hm1, polyEvalMod_one]⟩

theorem nextRootP_lt_two (m : ℕ) (a : List ℕ) (lo : ℕ) (hm : m < 2) :
    nextRootP m a lo = min lo m := by
  rw [nextRootP_eq_minOr]
  split_ifs with hS
  · have := (rootSetGe m a lo).min'_mem hS
    rw [mem_rootSetGe] at this
    omega
  · rcases (by omega : m = 0 ∨ m = 1) with h | h
    · subst h; simp
    · subst h
      rcases Nat.eq_zero_or_pos lo with hl | hl
      · exact absurd ⟨0, by simp [rootSetGe, hl, polyEvalMod_one]⟩ hS
      · omega

end SH

/-! ## The output and the specifications -/

/-- The output of the root searches: the found `y` if `y < m` (`m` = block 0 of `nb`), else `m`. -/
def finR (nb : ℕ) (q : List Bool × List Bool) : List Bool :=
  Nat.bits (if Groundwork.ofWord q.2.reverse < rdBlk nb 0 q.1 then Groundwork.ofWord q.2.reverse
    else rdBlk nb 0 q.1)

/-- **The least root** of a degree-`≤ d` polynomial modulo `m`. -/
def specP (d : ℕ) : SearchSpec where
  pre w := decide (rdBlk (d + 2) 0 w < 2)
  small _ := []
  step := stepPos
  fin := finR (d + 2)

/-- **The least root `≥ lo`**. -/
def specNext (d : ℕ) : SearchSpec where
  pre w := decide (rdBlk (d + 3) 0 w < 2)
  small w := Nat.bits (min (rdBlk (d + 3) 1 w) (rdBlk (d + 3) 0 w))
  step := stepPos
  fin := finR (d + 3)

/-- **The number of roots**: one count of the empty pattern. -/
def specCnt (d : ℕ) : GR.QuerySpec where
  pre w := decide (rdBlk (d + 2) 0 w = 0)
  small _ := []
  q1 _ := []
  q2 _ := []
  fin q := Nat.bits q.2.1

/-! ## PolyT -/

theorem finR_polyT (nb : ℕ) : PolyT (finR nb) := by
  have h := rdBlk_polyT nb 0
  have hm : PolyT fun q : List Bool × List Bool => rdBlk nb 0 q.1 := by fun_prop
  have hy : PolyT fun q : List Bool × List Bool => Groundwork.ofWord q.2.reverse := by fun_prop
  unfold finR
  exact PolyT.bits (PolyT.ite' (PolyT.decide_lt hy hm) hy hm)

theorem specP_pre_polyT (d : ℕ) : PolyT (specP d).pre := by
  have h := rdBlk_polyT (d + 2) 0
  show PolyT fun w : List Bool => decide (rdBlk (d + 2) 0 w < 2); fun_prop

theorem specP_small_polyT (d : ℕ) : PolyT (specP d).small := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specP_step_polyT (d : ℕ) : PolyT (specP d).step := stepPos_polyT

theorem specP_fin_polyT (d : ℕ) : PolyT (specP d).fin := finR_polyT (d + 2)

theorem specNext_pre_polyT (d : ℕ) : PolyT (specNext d).pre := by
  have h := rdBlk_polyT (d + 3) 0
  show PolyT fun w : List Bool => decide (rdBlk (d + 3) 0 w < 2); fun_prop

theorem specNext_small_polyT (d : ℕ) : PolyT (specNext d).small := by
  have h0 := rdBlk_polyT (d + 3) 0
  have h1 := rdBlk_polyT (d + 3) 1
  show PolyT fun w : List Bool => Nat.bits (min (rdBlk (d + 3) 1 w) (rdBlk (d + 3) 0 w))
  exact PolyT.bits (PolyT.min' h1 h0)

theorem specNext_step_polyT (d : ℕ) : PolyT (specNext d).step := stepPos_polyT

theorem specNext_fin_polyT (d : ℕ) : PolyT (specNext d).fin := finR_polyT (d + 3)

theorem specCnt_pre_polyT (d : ℕ) : PolyT (specCnt d).pre := by
  have h := rdBlk_polyT (d + 2) 0
  show PolyT fun w : List Bool => decide (rdBlk (d + 2) 0 w = 0); fun_prop

theorem specCnt_small_polyT (d : ℕ) : PolyT (specCnt d).small := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specCnt_q1_polyT (d : ℕ) : PolyT (specCnt d).q1 := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specCnt_q2_polyT (d : ℕ) : PolyT (specCnt d).q2 := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specCnt_fin_polyT (d : ℕ) : PolyT (specCnt d).fin := by
  show PolyT fun q : List Bool × ℕ × ℕ => Nat.bits q.2.1; fun_prop

/-! ## Lengths -/

theorem rdBlk_lt_two_pow_length (nb j : ℕ) (w : List Bool) : rdBlk nb j w < 2 ^ w.length :=
  (rdBlk_lt nb j w).trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _))

theorem finR_length (nb : ℕ) (w π : List Bool) : (finR nb (w, π)).length ≤ 1 * (w.length + 2) := by
  unfold finR
  dsimp only
  have hm := rdBlk_lt_two_pow_length nb 0 w
  split_ifs with h <;> exact (bits_length_le (k := w.length) (by omega)).trans (by omega)

theorem specP_step_length (d : ℕ) (q : (List Bool × ℕ × List Bool) × ℤ) :
    ((specP d).step q).length = q.1.2.2.length + 1 := stepPos_length q

theorem specP_fin_length (d : ℕ) (w π : List Bool) :
    ((specP d).fin (w, π)).length ≤ 1 * (w.length + 2) := finR_length (d + 2) w π

theorem specP_small_length (d : ℕ) (w : List Bool) : ((specP d).small w).length ≤ 1 * (w.length + 2) := by
  show ([] : List Bool).length ≤ _; simp

theorem specNext_step_length (d : ℕ) (q : (List Bool × ℕ × List Bool) × ℤ) :
    ((specNext d).step q).length = q.1.2.2.length + 1 := stepPos_length q

theorem specNext_fin_length (d : ℕ) (w π : List Bool) :
    ((specNext d).fin (w, π)).length ≤ 1 * (w.length + 2) := finR_length (d + 3) w π

theorem specNext_small_length (d : ℕ) (w : List Bool) :
    ((specNext d).small w).length ≤ 1 * (w.length + 2) := by
  show (Nat.bits (min (rdBlk (d + 3) 1 w) (rdBlk (d + 3) 0 w))).length ≤ _
  have hm := rdBlk_lt_two_pow_length (d + 3) 0 w
  exact (bits_length_le (k := w.length) (lt_of_le_of_lt (min_le_right _ _) hm)).trans (by omega)

theorem specCnt_length {c₀ : ℕ} (pk : CntPackage c₀) (d : ℕ) (w : List Bool)
    (hOk : (specCnt d).pre w = false → pk.Ok w) :
    (GR.answerQ pk (specCnt d) w).length ≤ (pk.qb + 2) * (w.length + 2) := by
  unfold GR.answerQ
  split_ifs with h
  · show ([] : List Bool).length ≤ _; simp
  · have hf : (specCnt d).pre w = false := by simpa using h
    have e := pk.Q_lt w [] (hOk hf) (by simp)
    show (Nat.bits (pk.Q w [])).length ≤ _
    exact (bits_length_le e).trans (by nlinarith)

/-! ## The answers -/

/-- The core of both searches: with the rounds `R w = n` and positive counts exactly on the
prefixes of the elements of `S ⊆ [0, m)`, `m < 2^n`, the output `finR` is `min S` or `m`. -/
theorem answer_finR {c₀ : ℕ} (pk : CntPackage c₀) (sp : SearchSpec) (nb : ℕ) (w : List Bool)
    (S : Finset ℕ) (hs : sp.step = stepPos) (hf : sp.fin = finR nb)
    (hpre : sp.pre w = false) (hR : pk.R w = w.length / nb)
    (hSm : ∀ y ∈ S, y < rdBlk nb 0 w)
    (hcnt : ∀ π : List Bool, π.length < w.length / nb → (0 < pk.Q w (π ++ [false]) ↔
        ∃ y ∈ S, y / 2 ^ (w.length / nb - (π ++ [false]).length) = Search.ofWord (π ++ [false]))) :
    GR.answer pk sp w = Nat.bits (if hS : S.Nonempty then S.min' hS else rdBlk nb 0 w) := by
  unfold GR.answer
  rw [if_neg (by simp [hpre]), hR, seq_stepPos pk sp hs, hf]
  have hmn : rdBlk nb 0 w < 2 ^ (w.length / nb) := rdBlk_lt nb 0 w
  have hSn : ∀ y ∈ S, y < 2 ^ (w.length / nb) := fun y hy => (hSm y hy).trans hmn
  have hval := searchWith_eq_minOr (cnt := pk.Q w) hSn hcnt
  unfold finR
  dsimp only
  rw [FR.ofWord_reverse, hval]
  by_cases hS : S.Nonempty
  · rw [dif_pos hS, dif_pos hS, if_pos (hSm _ (S.min'_mem hS))]
  · rw [dif_neg hS, dif_neg hS, if_neg (by omega)]

/-- **Least root on any word**: with `R w = |w|/(d+2)` rounds and the root counts of the prefixes
(for `m ≥ 2`), the answer is `minRootP m (rdCo d w)`. -/
theorem specP_answer {c₀ : ℕ} (pk : CntPackage c₀) (d : ℕ) (w : List Bool)
    (hR : pk.R w = w.length / (d + 2))
    (hQ : 2 ≤ rdBlk (d + 2) 0 w → ∀ π : List Bool, π.length < w.length / (d + 2) →
      pk.Q w (π ++ [false]) = ((Finset.range (rdBlk (d + 2) 0 w)).filter fun x =>
        polyEvalMod (rdBlk (d + 2) 0 w) (rdCo d w) x = 0 ∧
          x / 2 ^ (w.length / (d + 2) - (π ++ [false]).length) = Search.ofWord (π ++ [false])).card) :
    GR.answer pk (specP d) w = Nat.bits (minRootP (rdBlk (d + 2) 0 w) (rdCo d w)) := by
  set m := rdBlk (d + 2) 0 w with hm
  by_cases hpre : m < 2
  · unfold GR.answer
    have : (specP d).pre w = true := by simp only [specP, decide_eq_true_eq]; exact hpre
    rw [if_pos this, SH.minRootP_lt_two m _ hpre]; rfl
  · have hpf : (specP d).pre w = false := by simp only [specP, decide_eq_false_iff_not]; exact hpre
    rw [answer_finR pk (specP d) (d + 2) w (rootSetP m (rdCo d w)) rfl rfl hpf hR, SH.minRootP_eq_minOr]
    · intro y hy
      exact (SH.mem_rootSetP.1 hy).1
    · intro π hπ
      rw [hQ (by omega) π hπ, Finset.card_pos]
      constructor
      · rintro ⟨y, hy⟩
        rw [Finset.mem_filter, Finset.mem_range] at hy
        exact ⟨y, SH.mem_rootSetP.2 ⟨hy.1, hy.2.1⟩, hy.2.2⟩
      · rintro ⟨y, hy, h⟩
        rw [SH.mem_rootSetP] at hy
        exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_range.2 hy.1, hy.2, h⟩⟩

/-- **Least root**: on the input `encodeList (m :: a)`, `a.length = d + 1`, the answer is
`encodeNat (minRootP m a)`. -/
theorem specP_answer_list {c₀ : ℕ} (pk : CntPackage c₀) (d m : ℕ) (a : List ℕ)
    (hlen : a.length = d + 1)
    (hR : pk.R (encodeList (m :: a)) = (encodeList (m :: a)).length / (d + 2))
    (hQ : 2 ≤ m → ∀ π : List Bool, π.length < (encodeList (m :: a)).length / (d + 2) →
      pk.Q (encodeList (m :: a)) (π ++ [false]) = ((Finset.range m).filter fun x =>
        polyEvalMod m (a.map (· % m)) x = 0 ∧
          x / 2 ^ ((encodeList (m :: a)).length / (d + 2) - (π ++ [false]).length) =
            Search.ofWord (π ++ [false])).card) :
    GR.answer pk (specP d) (encodeList (m :: a)) = Computability.encodeNat (minRootP m a) := by
  have h := specP_answer pk d (encodeList (m :: a)) hR
    (by rw [rdBlk_encodeList_zero d m a hlen, rdCo_encodeList d m a hlen]; exact hQ)
  rw [h, rdBlk_encodeList_zero d m a hlen, rdCo_encodeList d m a hlen, SH.minRootP_map_mod,
    bits_eq_encodeNat]

/-- **Least root `≥ lo` on any word** (`m` = block 0, `lo` = block 1 of `d + 3`). -/
theorem specNext_answer {c₀ : ℕ} (pk : CntPackage c₀) (d : ℕ) (w : List Bool)
    (hR : pk.R w = w.length / (d + 3))
    (hQ : 2 ≤ rdBlk (d + 3) 0 w → ∀ π : List Bool, π.length < w.length / (d + 3) →
      pk.Q w (π ++ [false]) = ((Finset.range (rdBlk (d + 3) 0 w)).filter fun x =>
        rdBlk (d + 3) 1 w ≤ x ∧ polyEvalMod (rdBlk (d + 3) 0 w) (rdCoN d w) x = 0 ∧
          x / 2 ^ (w.length / (d + 3) - (π ++ [false]).length) = Search.ofWord (π ++ [false])).card) :
    GR.answer pk (specNext d) w =
      Nat.bits (nextRootP (rdBlk (d + 3) 0 w) (rdCoN d w) (rdBlk (d + 3) 1 w)) := by
  set m := rdBlk (d + 3) 0 w with hm
  set lo := rdBlk (d + 3) 1 w with hlo
  by_cases hpre : m < 2
  · unfold GR.answer
    have : (specNext d).pre w = true := by simp only [specNext, decide_eq_true_eq]; exact hpre
    rw [if_pos this, SH.nextRootP_lt_two m _ lo hpre]; rfl
  · have hpf : (specNext d).pre w = false := by
      simp only [specNext, decide_eq_false_iff_not]; exact hpre
    rw [answer_finR pk (specNext d) (d + 3) w (SH.rootSetGe m (rdCoN d w) lo) rfl rfl hpf hR,
      SH.nextRootP_eq_minOr]
    · intro y hy
      exact (SH.mem_rootSetGe.1 hy).1
    · intro π hπ
      rw [hQ (by omega) π hπ, Finset.card_pos]
      constructor
      · rintro ⟨y, hy⟩
        rw [Finset.mem_filter, Finset.mem_range] at hy
        exact ⟨y, SH.mem_rootSetGe.2 ⟨hy.1, hy.2.1, hy.2.2.1⟩, hy.2.2.2⟩
      · rintro ⟨y, hy, h⟩
        rw [SH.mem_rootSetGe] at hy
        exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_range.2 hy.1, hy.2.1, hy.2.2, h⟩⟩

/-- **Least root `≥ lo`**: on the input `encodeList (m :: lo :: a)` the answer is
`encodeNat (nextRootP m a lo)`. -/
theorem specNext_answer_list {c₀ : ℕ} (pk : CntPackage c₀) (d m lo : ℕ) (a : List ℕ)
    (hlen : a.length = d + 1)
    (hR : pk.R (encodeList (m :: lo :: a)) = (encodeList (m :: lo :: a)).length / (d + 3))
    (hQ : 2 ≤ m → ∀ π : List Bool, π.length < (encodeList (m :: lo :: a)).length / (d + 3) →
      pk.Q (encodeList (m :: lo :: a)) (π ++ [false]) = ((Finset.range m).filter fun x =>
        lo ≤ x ∧ polyEvalMod m (a.map (· % m)) x = 0 ∧
          x / 2 ^ ((encodeList (m :: lo :: a)).length / (d + 3) - (π ++ [false]).length) =
            Search.ofWord (π ++ [false])).card) :
    GR.answer pk (specNext d) (encodeList (m :: lo :: a)) =
      Computability.encodeNat (nextRootP m a lo) := by
  have h := specNext_answer pk d (encodeList (m :: lo :: a)) hR
    (by rw [rdBlk_encodeList_zero' d m lo a hlen, rdBlk_encodeList_one d m lo a hlen,
      rdCoN_encodeList d m lo a hlen]; exact hQ)
  rw [h, rdBlk_encodeList_zero' d m lo a hlen, rdBlk_encodeList_one d m lo a hlen,
    rdCoN_encodeList d m lo a hlen, SH.nextRootP_map_mod, bits_eq_encodeNat]

/-- **Number of roots on any word**: with the count of the empty pattern (for `m > 0`), the answer
is `#(rootSetP m (rdCo d w))`. -/
theorem specCnt_answer {c₀ : ℕ} (pk : CntPackage c₀) (d : ℕ) (w : List Bool)
    (hQ : 0 < rdBlk (d + 2) 0 w → pk.Q w [] = (rootSetP (rdBlk (d + 2) 0 w) (rdCo d w)).card) :
    GR.answerQ pk (specCnt d) w = Nat.bits (rootSetP (rdBlk (d + 2) 0 w) (rdCo d w)).card := by
  unfold GR.answerQ
  by_cases h0 : rdBlk (d + 2) 0 w = 0
  · have : (specCnt d).pre w = true := by simp only [specCnt, decide_eq_true_eq]; exact h0
    rw [if_pos this, h0]; rfl
  · have : (specCnt d).pre w = false := by simp only [specCnt, decide_eq_false_iff_not]; exact h0
    rw [if_neg (by simp [this])]
    show Nat.bits (pk.Q w []) = _
    rw [hQ (by omega)]

/-- **Number of roots**: on the input `encodeList (m :: a)` the answer is `encodeNat #(rootSetP m a)`. -/
theorem specCnt_answer_list {c₀ : ℕ} (pk : CntPackage c₀) (d m : ℕ) (a : List ℕ)
    (hlen : a.length = d + 1)
    (hQ : 0 < m → pk.Q (encodeList (m :: a)) [] = (rootSetP m (a.map (· % m))).card) :
    GR.answerQ pk (specCnt d) (encodeList (m :: a)) =
      Computability.encodeNat (rootSetP m a).card := by
  have h := specCnt_answer pk d (encodeList (m :: a))
    (by rw [rdBlk_encodeList_zero d m a hlen, rdCo_encodeList d m a hlen]; exact hQ)
  rw [h, rdBlk_encodeList_zero d m a hlen, rdCo_encodeList d m a hlen, SH.rootSetP_map_mod,
    bits_eq_encodeNat]

end EthFollowup.ModP
