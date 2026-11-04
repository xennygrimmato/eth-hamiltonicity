/-
# The search specifications of (A) square roots mod m and (B) the least QNR, and their answers (B6)

`scratchpad/plans/modp-plan.md` §5 (instantiations). For every `CntPackage pk` whose rounds and
counts are the instance counts on the queries the run makes, the answer of the generic search
`GR.answer pk sp w` is the target:

* (A) `specA` (reader `rdM w := ofWord (take (|w|/2) w)`, `rdA w := ofWord (drop (|w|/2) w)`):
  `specA_answer`: `GR.answer pk specA w = Nat.bits (minRoot (rdM w) (rdA w))` when `pk.R w = |w|/2`
  and `pk.Q w (π ++ [0]) = S3A n' (|w|/2) m (a % m) (π ++ [0])` (`|π| < |w|/2`, `|w|/2 ≤ n'`);
  **`specA_answer_pair`**: on `encodePair m a` the answer is `encodeNat (minRoot m a)`.
* (B) `specB` (`p := ofWord w`, `n := |w|`; the step turns the count `S3B` of `π ++ [0]` into the
  non-residue count `nrOf`): **`specB_answer_prime`**: for prime `p`, `GR.answer pk specB (encodeNat p)
  = encodeNat (lqnr p)` when `pk.R w = |w|` and `pk.Q w (π ++ [0]) = S3B n' |w| p (π ++ [0])`;
  **`specB_answer_le`**: for EVERY package and word, the answer is `Nat.bits y` for some `y ≤ ofWord w`.
* PolyT of all fields (`specA_*_polyT`, `specB_*_polyT`), the length conditions (`stepPos_length`,
  `stepB_length`, `finA_length`, `finB_length`, small lengths).

Standard axioms only.
-/
import EthFollowup.ModP.GRate
import EthFollowup.ModP.MinSearch
import EthFollowup.ModP.QRCount
import EthFollowup.ModP.Encode

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork EthFollowup.Factoring

/-! ## Words -/

theorem gofWord_eq_leVal (w : List Bool) : Groundwork.ofWord w = leVal w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [Groundwork.ofWord, leVal_cons, ih]

theorem gofWord_encodeNat (N : ℕ) : Groundwork.ofWord (Computability.encodeNat N) = N := by
  rw [gofWord_eq_leVal, leVal_encodeNat]

theorem bits_eq_encodeNat (N : ℕ) : Nat.bits N = Computability.encodeNat N :=
  (FR.encodeNat_eq_bits N).symm

theorem bits_length_le {y : ℕ} {k : ℕ} (h : y < 2 ^ k) : (Nat.bits y).length ≤ k := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le.2 h

/-! ## The step "keep `0` iff the count is positive" -/

/-- One round: `π ++ [0]` iff the count is positive. -/
def stepPos (q : (List Bool × ℕ × List Bool) × ℤ) : List Bool :=
  if 0 < q.2.toNat then q.1.2.2 ++ [false] else q.1.2.2 ++ [true]

theorem stepPos_polyT : PolyT stepPos := by unfold stepPos; fun_prop

theorem stepPos_length (q : (List Bool × ℕ × List Bool) × ℤ) :
    (stepPos q).length = q.1.2.2.length + 1 := by
  unfold stepPos; split_ifs <;> simp

/-- With the step `stepPos`, the rounds are F6a's `searchWith` with the oracle `Q w`. -/
theorem seq_stepPos {c₀ : ℕ} (pk : CntPackage c₀) (sp : SearchSpec) (hs : sp.step = stepPos)
    (w : List Bool) (y : ℕ) : GR.seq pk sp w y = Search.searchWith (pk.Q w) y := by
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [GR.seq_succ, ih, Search.searchWith_succ, hs]
    simp only [stepPos, Search.searchStep, Int.toNat_natCast]

/-! ## (A) the least square root modulo `m` -/

/-- The modulus: the value of the first half of the word. -/
def rdM (w : List Bool) : ℕ := Groundwork.ofWord (w.take (w.length / 2))

/-- The residue: the value of the second half of the word. -/
def rdA (w : List Bool) : ℕ := Groundwork.ofWord (w.drop (w.length / 2))

/-- The output of (A): the found `y` if it is a root `< m`, else `m`. -/
def finA (q : List Bool × List Bool) : List Bool :=
  Nat.bits (if Groundwork.ofWord q.2.reverse < rdM q.1 then
    (if Groundwork.ofWord q.2.reverse * Groundwork.ofWord q.2.reverse % rdM q.1 = rdA q.1 % rdM q.1
      then Groundwork.ofWord q.2.reverse else rdM q.1) else rdM q.1)

/-- **The search of (A)**: `m < 2` directly (`minRoot 0 a = minRoot 1 a = 0`), else the binary
search over the roots and the check. -/
def specA : SearchSpec where
  pre w := decide (rdM w < 2)
  small _ := []
  step := stepPos
  fin := finA

theorem specA_pre_polyT : PolyT specA.pre := by
  show PolyT fun w : List Bool => decide (Groundwork.ofWord (w.take (w.length / 2)) < 2); fun_prop

theorem specA_small_polyT : PolyT specA.small := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specA_step_polyT : PolyT specA.step := stepPos_polyT

theorem specA_fin_polyT : PolyT specA.fin := by
  show PolyT finA; unfold finA rdM rdA; fun_prop

theorem rdM_lt (w : List Bool) : rdM w < 2 ^ (w.length / 2) := by
  have := Groundwork.ofWord_lt (w.take (w.length / 2))
  rwa [List.length_take, min_eq_left (Nat.div_le_self _ _)] at this

theorem finA_length (w π : List Bool) : (specA.fin (w, π)).length ≤ 1 * (w.length + 2) := by
  show (finA (w, π)).length ≤ _
  unfold finA
  dsimp only
  have hm := rdM_lt w
  have h2 : 2 ^ (w.length / 2) ≤ 2 ^ w.length := Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
  split_ifs with h1 h2' <;>
    (refine (bits_length_le (k := w.length) (by omega)).trans (by omega))

theorem specA_small_length (w : List Bool) : (specA.small w).length ≤ 1 * (w.length + 2) := by
  show ([] : List Bool).length ≤ _; simp

/-- **(A) on any word**: with `R w = |w|/2` rounds and counts `S3A` of the reduced residue, the answer
is `minRoot (rdM w) (rdA w)`. -/
theorem specA_answer {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) {n' : ℕ}
    (hR : pk.R w = w.length / 2) (hn' : w.length / 2 ≤ n')
    (hQ : ∀ π : List Bool, π.length < w.length / 2 →
      pk.Q w (π ++ [false]) = S3A n' (w.length / 2) (rdM w) (rdA w % rdM w) (π ++ [false])) :
    GR.answer pk specA w = Nat.bits (minRoot (rdM w) (rdA w)) := by
  unfold GR.answer
  by_cases hpre : rdM w < 2
  · have : specA.pre w = true := by simp only [specA, decide_eq_true_eq]; exact hpre
    rw [if_pos this]
    show ([] : List Bool) = _
    rcases (by omega : rdM w = 0 ∨ rdM w = 1) with h | h
    · rw [h, minRoot_zero]; rfl
    · rw [h, minRoot_one]; rfl
  · have : specA.pre w = false := by simp only [specA, decide_eq_false_iff_not]; exact hpre
    rw [if_neg (by simp [this]), hR, seq_stepPos pk specA rfl]
    have hmn : rdM w < 2 ^ (w.length / 2) := rdM_lt w
    have hmn' : rdM w ≤ 2 ^ n' := hmn.le.trans (Nat.pow_le_pow_right (by norm_num) hn')
    have hSn : ∀ y ∈ rootSet (rdM w) (rdA w), y < 2 ^ (w.length / 2) := by
      intro y hy
      simp only [rootSet, Finset.mem_filter, Finset.mem_range] at hy
      omega
    have hcnt : ∀ π : List Bool, π.length < w.length / 2 → (0 < pk.Q w (π ++ [false]) ↔
        ∃ y ∈ rootSet (rdM w) (rdA w),
          y / 2 ^ (w.length / 2 - (π ++ [false]).length) = Search.ofWord (π ++ [false])) := by
      intro π hπ
      rw [hQ π hπ]
      exact S3A_pos_iff (π ++ [false]) hmn'
    have hval := searchWith_eq_minOr (cnt := pk.Q w) hSn hcnt
    show finA (w, Search.searchWith (pk.Q w) (w.length / 2)) = _
    unfold finA
    dsimp only
    rw [FR.ofWord_reverse, hval]
    by_cases hS : (rootSet (rdM w) (rdA w)).Nonempty
    · rw [dif_pos hS, ← minRoot_eq_min' hS]
      have hmem := minRoot_mem hS
      simp only [rootSet, Finset.mem_filter, Finset.mem_range] at hmem
      rw [if_pos hmem.1, if_pos hmem.2]
    · rw [dif_neg hS, minRoot_eq_of_empty (Finset.not_nonempty_iff_eq_empty.1 hS),
        if_neg (by omega)]

theorem rdM_encodePair (m a : ℕ) : rdM (encodePair m a) = m := by
  rw [rdM, gofWord_eq_leVal, leVal_take_half]

theorem rdA_encodePair (m a : ℕ) : rdA (encodePair m a) = a := by
  rw [rdA, gofWord_eq_leVal, leVal_drop_half]

/-- **(A)**: on the input `encodePair m a` the answer is `encodeNat (minRoot m a)`. -/
theorem specA_answer_pair {c₀ : ℕ} (pk : CntPackage c₀) (m a : ℕ) {n' : ℕ}
    (hR : pk.R (encodePair m a) = (encodePair m a).length / 2)
    (hn' : (encodePair m a).length / 2 ≤ n')
    (hQ : ∀ π : List Bool, π.length < (encodePair m a).length / 2 →
      pk.Q (encodePair m a) (π ++ [false]) =
        S3A n' ((encodePair m a).length / 2) m (a % m) (π ++ [false])) :
    GR.answer pk specA (encodePair m a) = Computability.encodeNat (minRoot m a) := by
  have h := specA_answer pk (encodePair m a) hR hn'
    (by rw [rdM_encodePair, rdA_encodePair]; exact hQ)
  rw [h, rdM_encodePair, rdA_encodePair, bits_eq_encodeNat]

/-! ## (B) the least quadratic non-residue -/

/-- `2 ^ (|w| - |π|)`, the block size of the prefix `π`. -/
def blkS (w π : List Bool) : ℕ := 2 ^ (w.length - π.length)

@[fun_prop] theorem blkS_polyT {α : Type} [Enc α] {w π : α → List Bool} (hw : PolyT w) (hπ : PolyT π) :
    PolyT fun x => blkS (w x) (π x) := by
  unfold blkS
  have hu : Unary fun x => (w x).length - (π x).length :=
    Unary.of_le (Unary.of_length hw) (by fun_prop) (fun _ => Nat.sub_le _ _)
  exact PolyT.two_pow hu

/-- The non-residue count of the prefix `π'` computed from the triple count `k`
(`nrOf (|w|) (ofWord w) π' k`, with the library's word values). -/
def nrOfG (w π' : List Bool) (k : ℕ) : ℕ :=
  (min ((Groundwork.ofWord π'.reverse + 1) * blkS w π') (Groundwork.ofWord w) -
      min (Groundwork.ofWord π'.reverse * blkS w π') (Groundwork.ofWord w)) -
    (if Groundwork.ofWord π'.reverse = 0 then 1 else 0) -
    (k - (if Groundwork.ofWord π'.reverse = 0 then 1 else 0)) / 2

theorem nrOfG_eq (w π' : List Bool) (k : ℕ) :
    nrOfG w π' k = nrOf w.length (Groundwork.ofWord w) π' k := by
  simp only [nrOfG, nrOf, rangeCount, z0, blkS, FR.ofWord_reverse]

/-- `nrOfG` on a triple. -/
def nrT (t : List Bool × List Bool × ℕ) : ℕ := nrOfG t.1 t.2.1 t.2.2

theorem nrT_polyT : PolyT nrT := by
  have hc : PolyT fun t : List Bool × List Bool × ℕ => Groundwork.ofWord t.2.1.reverse := by fun_prop
  have hp : PolyT fun t : List Bool × List Bool × ℕ => Groundwork.ofWord t.1 := by fun_prop
  have hk : PolyT fun t : List Bool × List Bool × ℕ => t.2.2 := by fun_prop
  have hb : PolyT fun t : List Bool × List Bool × ℕ => blkS t.1 t.2.1 :=
    blkS_polyT (by fun_prop) (by fun_prop)
  have hz : PolyT fun t : List Bool × List Bool × ℕ =>
      if Groundwork.ofWord t.2.1.reverse = 0 then 1 else 0 :=
    PolyT.ite' (PolyT.decide_eq hc (PolyT.const 0)) (PolyT.const 1) (PolyT.const 0)
  have h1 := PolyT.min' (PolyT.mul (PolyT.add hc (PolyT.const 1)) hb) hp
  have h2 := PolyT.min' (PolyT.mul hc hb) hp
  exact PolyT.sub (PolyT.sub (PolyT.sub h1 h2) hz) (PolyT.div (PolyT.sub hk hz) (PolyT.const 2))

/-- One round of (B): keep `0` iff some non-residue has the prefix `π ++ [0]`. -/
def stepB (q : (List Bool × ℕ × List Bool) × ℤ) : List Bool :=
  if 0 < nrT (q.1.1, q.1.2.2 ++ [false], q.2.toNat) then q.1.2.2 ++ [false] else q.1.2.2 ++ [true]

/-- The output of (B): the found `y` if `y < p`, else `p`. -/
def finB (q : List Bool × List Bool) : List Bool :=
  Nat.bits (if Groundwork.ofWord q.2.reverse < Groundwork.ofWord q.1 then Groundwork.ofWord q.2.reverse
    else Groundwork.ofWord q.1)

/-- **The search of (B)**: `p < 3` directly (`lqnr p = p`), else the binary search over the
non-residues, the counts of non-residues computed from the triple counts. -/
def specB : SearchSpec where
  pre w := decide (Groundwork.ofWord w < 3)
  small w := Nat.bits (Groundwork.ofWord w)
  step := stepB
  fin := finB

theorem specB_pre_polyT : PolyT specB.pre := by
  show PolyT fun w : List Bool => decide (Groundwork.ofWord w < 3); fun_prop

theorem specB_small_polyT : PolyT specB.small := by
  show PolyT fun w : List Bool => Nat.bits (Groundwork.ofWord w); fun_prop

theorem specB_step_polyT : PolyT specB.step := by
  have := nrT_polyT
  show PolyT stepB; unfold stepB; fun_prop

theorem specB_fin_polyT : PolyT specB.fin := by
  show PolyT finB; unfold finB; fun_prop

theorem stepB_length (q : (List Bool × ℕ × List Bool) × ℤ) :
    (specB.step q).length = q.1.2.2.length + 1 := by
  show (stepB q).length = _; unfold stepB; split_ifs <;> simp

theorem finB_length (w π : List Bool) : (specB.fin (w, π)).length ≤ 1 * (w.length + 2) := by
  show (finB (w, π)).length ≤ _
  unfold finB
  dsimp only
  have hp := Groundwork.ofWord_lt w
  split_ifs with h <;> exact (bits_length_le (k := w.length) (by omega)).trans (by omega)

theorem specB_small_length (w : List Bool) : (specB.small w).length ≤ 1 * (w.length + 2) := by
  show (Nat.bits (Groundwork.ofWord w)).length ≤ _
  exact (bits_length_le (Groundwork.ofWord_lt w)).trans (by omega)

theorem seq_specB {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) (y : ℕ) :
    GR.seq pk specB w y = Search.searchWith
      (fun π' => nrOf w.length (Groundwork.ofWord w) π' (pk.Q w π')) y := by
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [GR.seq_succ, ih, Search.searchWith_succ]
    simp only [specB, stepB, nrT, Search.searchStep, Int.toNat_natCast, nrOfG_eq]

/-- **(B) for EVERY package and word**: the answer is the binary word of some `y ≤ ofWord w`. -/
theorem specB_answer_le {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) :
    ∃ y ≤ Groundwork.ofWord w, GR.answer pk specB w = Nat.bits y := by
  unfold GR.answer
  split_ifs
  · exact ⟨_, le_rfl, rfl⟩
  · show ∃ y ≤ _, finB _ = _
    unfold finB
    split_ifs with h
    · exact ⟨_, h.le, rfl⟩
    · exact ⟨_, le_rfl, rfl⟩

/-- **(B) on any word with a prime value**: with `R w = |w|` rounds and the counts `S3B`, the answer
is `lqnr p`. -/
theorem specB_answer {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) {n' : ℕ}
    (hp : (Groundwork.ofWord w).Prime) (hR : pk.R w = w.length) (hn' : w.length ≤ n')
    (hQ : ∀ π : List Bool, π.length < w.length →
      pk.Q w (π ++ [false]) = S3B n' w.length (Groundwork.ofWord w) (π ++ [false])) :
    GR.answer pk specB w = Nat.bits (lqnr (Groundwork.ofWord w)) := by
  unfold GR.answer
  set p := Groundwork.ofWord w
  set n := w.length
  by_cases hpre : p < 3
  · have : specB.pre w = true := by simp only [specB, decide_eq_true_eq]; exact hpre
    rw [if_pos this]
    show Nat.bits p = _
    have h2 := hp.two_le
    have : p = 2 := by omega
    rw [this, lqnr_small.2.2]
  · have : specB.pre w = false := by simp only [specB, decide_eq_false_iff_not]; exact hpre
    rw [if_neg (by simp [this]), hR, seq_specB]
    have hpn : p < 2 ^ n := Groundwork.ofWord_lt w
    have hpn' : p ≤ 2 ^ n' := hpn.le.trans (Nat.pow_le_pow_right (by norm_num) hn')
    have hp2 : p ≠ 2 := by omega
    have hSn : ∀ y ∈ nrSet p, y < 2 ^ n := by
      intro y hy
      simp only [nrSet, Finset.mem_filter, Finset.mem_range] at hy
      omega
    have hcnt : ∀ π : List Bool, π.length < n →
        (0 < nrOf n p (π ++ [false]) (pk.Q w (π ++ [false])) ↔
          ∃ y ∈ nrSet p, y / 2 ^ (n - (π ++ [false]).length) = Search.ofWord (π ++ [false])) := by
      intro π hπ
      rw [hQ π hπ]
      exact nrOf_S3B_pos_iff (π ++ [false]) hp hp2 hpn'
    have hne := nrSet_nonempty hp (by omega)
    have hval := searchWith_eq_min' (cnt := fun π' => nrOf n p π' (pk.Q w π')) hne hSn hcnt
    show finB (w, _) = _
    unfold finB
    dsimp only
    rw [FR.ofWord_reverse, hval, ← lqnr_eq_min' hne, if_pos (lqnr_lt hp (by omega))]

/-- **(B)**: on the input `encodeNat p`, `p` prime, the answer is `encodeNat (lqnr p)`. -/
theorem specB_answer_prime {c₀ : ℕ} (pk : CntPackage c₀) {p n' : ℕ} (hp : p.Prime)
    (hR : pk.R (Computability.encodeNat p) = (Computability.encodeNat p).length)
    (hn' : (Computability.encodeNat p).length ≤ n')
    (hQ : ∀ π : List Bool, π.length < (Computability.encodeNat p).length →
      pk.Q (Computability.encodeNat p) (π ++ [false]) =
        S3B n' (Computability.encodeNat p).length p (π ++ [false])) :
    GR.answer pk specB (Computability.encodeNat p) = Computability.encodeNat (lqnr p) := by
  have h := specB_answer pk (Computability.encodeNat p) (n' := n')
    (by rw [gofWord_encodeNat]; exact hp) hR hn' (by rw [gofWord_encodeNat]; exact hQ)
  rw [h, gofWord_encodeNat, bits_eq_encodeNat]

/-- **(B), general inputs**: on `encodeNat p` the answer is `encodeNat y` for some `y ≤ p`. -/
theorem specB_answer_encodeNat_le {c₀ : ℕ} (pk : CntPackage c₀) (p : ℕ) :
    ∃ y ≤ p, GR.answer pk specB (Computability.encodeNat p) = Computability.encodeNat y := by
  obtain ⟨y, hy, h⟩ := specB_answer_le pk (Computability.encodeNat p)
  rw [gofWord_encodeNat] at hy
  exact ⟨y, hy, by rw [h, bits_eq_encodeNat]⟩

end EthFollowup.ModP
