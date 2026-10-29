/-
# The label-sharing network with per-pair codes (module A1, file 2)

`research/hc-degree-theorem.md` Definition 2.2, Lemmas 2.3–2.4, Theorem 2.5 (first part), §7.
`LabelNetwork.lean` writes every item with one fixed-width code. Here a pair `{a,b}` of nodes
shares ONE word of `cap a b` bits for all its items together (`PairCode`): an injective code `enc a b`
of the words of labels on `pairItems a b` that have exactly `s a b` non-default labels (the *fibre*
of the profile entry `s a b`), with a decoder `dec a b` that returns `none` off the image.

For a `LabelSystem X` and a `PairCode C` of `X` (profile `C.s`), the network `X.netP C : Net g`:

* a setting of `a` is `encP a x`: for every `b ≠ a` in increasing order the block
  `C.enc a b (pairLab a b x.1)` (`cap a b` bits), then the copy bits held by `a`;
  `S a` is the image of the local states whose profile row is `C.s a` (`locSetP`);
  `len a = sumCap a + #held a`; block `b` of `z` is `blockAt a b z` (offset `offP a b`);
* `W a z = T a (decP a z)`; on `{a,b}`: `c a b = cap a b + #(copy bits on {a,b})`,
  `projP a b x = C.enc a b (pairLab a b x.1) ++ copies`, `f`, `Ψ` as in `LabelNetwork`.

Main results:

* `value_netP : (X.netP C).value = ∑ ℓ with (∀ a b, a ≠ b → cntP a b ℓ = C.s a b), ∏ a, T a ℓ (par · ℓ)`;
* `netP_is` : `Definition 2` from `∑_{b≠a} c a b ≤ P` and `|T| < 2^B` on the local states;
* `sum_c_eqP`, `U_eqP : U = ∑_a ∑_{b≠a} cap a b + 2·#R`;
* for the procedures: `blockAt_encP`, `drop_sumCap_encP`, `dec_encP`, `mem_SP`, `mem_SP_iff`;
* **the rank code** `rankPC X s hs hd` (labels `Label`, default `N`): `cap a b = cw(e_ab, s_ab) + 2 s_ab`
  with `e_ab = |pairItems a b|`; `decR_isSome_iff` (a block is valid iff it has the right length and
  its rank field is `< C(e,s)`), `labNum_decLab` (the decoded labels as numbers, via `rawCodes`).
-/
import EthFollowup.ExactHC.LabelNetwork
import EthFollowup.ExactHC.Unrank
import EthFollowup.ExactHC.Blobs

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Eight.SecNetworks Groundwork Finset

/-! ### Blocks of variable width -/

section Blocks

variable {g : ℕ}

/-- The nodes other than `a`, in increasing order. -/
def othersL (g : ℕ) (a : Fin g) : List (Fin g) := (List.finRange g).filter fun b => decide (b ≠ a)

theorem mem_othersL {a b : Fin g} : b ∈ othersL g a ↔ b ≠ a := by simp [othersL]

theorem othersL_pairwise (a : Fin g) : (othersL g a).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange g).filter _

theorem othersL_nodup (a : Fin g) : (othersL g a).Nodup := (List.nodup_finRange g).filter _

theorem length_flatMap_eq (l : List (Fin g)) (f : Fin g → List Bool) (cap : Fin g → ℕ)
    (hf : ∀ c ∈ l, (f c).length = cap c) : (l.flatMap f).length = (l.map cap).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      hf c List.mem_cons_self, ih fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')]

theorem drop_add_eq {α : Type} (l : List α) (a b : ℕ) : l.drop (a + b) = (l.drop a).drop b := by
  simp [List.drop_drop, Nat.add_comm]

/-- Reading block `b` of a concatenation of blocks, at the offset of the earlier blocks. -/
theorem take_drop_flatMap (l : List (Fin g)) (hl : l.Pairwise (· < ·)) (f : Fin g → List Bool)
    (cap : Fin g → ℕ) (hf : ∀ c ∈ l, (f c).length = cap c) (rest : List Bool) {b : Fin g} (hb : b ∈ l) :
    ((l.flatMap f ++ rest).drop (((l.filter fun c => decide (c < b)).map cap).sum)).take (cap b) = f b := by
  induction l with
  | nil => simp at hb
  | cons c l ih =>
    have hl' := List.pairwise_cons.1 hl
    by_cases hcb : c = b
    · subst hcb
      have h0 : (l.filter fun c' => decide (c' < c)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c' hc'
        have := hl'.1 c' hc'
        simp only [decide_eq_true_eq]; exact not_lt.2 this.le
      rw [List.filter_cons_of_neg (by simp), h0, List.map_nil, List.sum_nil, List.drop_zero,
        List.flatMap_cons, List.append_assoc, List.take_left' (hf c List.mem_cons_self)]
    · have hb' : b ∈ l := by
        rcases List.mem_cons.1 hb with h | h
        · exact absurd h.symm hcb
        · exact h
      have hcb' : c < b := hl'.1 b hb'
      rw [List.filter_cons_of_pos (by simpa using hcb'), List.map_cons, List.sum_cons,
        List.flatMap_cons, List.append_assoc, drop_add_eq, List.drop_left' (hf c List.mem_cons_self)]
      exact ih hl'.2 (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) hb'

/-- A word is the concatenation of its blocks. -/
theorem flatMap_blocks (l : List (Fin g)) (hl : l.Pairwise (· < ·)) (cap : Fin g → ℕ)
    (off : Fin g → ℕ) (hoff : ∀ b ∈ l, off b = ((l.filter fun c => decide (c < b)).map cap).sum)
    (z : List Bool) :
    l.flatMap (fun b => (z.drop (off b)).take (cap b)) = z.take ((l.map cap).sum) := by
  induction l generalizing z off with
  | nil => simp
  | cons c l ih =>
    have hl' := List.pairwise_cons.1 hl
    have hc : off c = 0 := by
      rw [hoff c List.mem_cons_self, List.filter_cons_of_neg (by simp)]
      have h0 : (l.filter fun c' => decide (c' < c)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c' hc'
        simp only [decide_eq_true_eq]; exact not_lt.2 (hl'.1 c' hc').le
      rw [h0]; rfl
    have hrest : ∀ b ∈ l, off b = cap c + ((l.filter fun c' => decide (c' < b)).map cap).sum := by
      intro b hb
      rw [hoff b (List.mem_cons_of_mem _ hb), List.filter_cons_of_pos (by simpa using hl'.1 b hb),
        List.map_cons, List.sum_cons]
    rw [List.flatMap_cons, hc, List.drop_zero, List.map_cons, List.sum_cons, List.take_add]
    congr 1
    have := ih hl'.2 (fun b => off b - cap c) (fun b hb => by rw [hrest b hb]; omega) (z.drop (cap c))
    rw [← this]
    refine List.flatMap_congr fun b hb => ?_
    rw [List.drop_drop, hrest b hb]
    congr 2
    omega

end Blocks

section Bits

variable {ι : Type} [DecidableEq ι]

theorem decY_not_memP : ∀ (js : List ι) (z : List Bool) (j : ι), j ∉ js → decY js z j = false
  | [], _, _, _ => rfl
  | j' :: js, z, j, hj => by
    have hj' : j ≠ j' ∧ j ∉ js := by simpa using hj
    simp only [decY]
    rw [Function.update_of_ne hj'.1]
    exact decY_not_memP js _ j hj'.2

theorem map_decYP : ∀ (js : List ι), js.Nodup → ∀ u : List Bool, u.length = js.length →
    js.map (decY js u) = u
  | [], _, u, hu => by simpa using (List.length_eq_zero_iff.1 hu).symm
  | j :: js, hn, u, hu => by
    have hj := List.nodup_cons.1 hn
    obtain ⟨b, u, rfl⟩ : ∃ b u', u = b :: u' := by
      cases u with
      | nil => simp at hu
      | cons b u' => exact ⟨b, u', rfl⟩
    simp only [List.map_cons, decY, Function.update_self, List.headD_cons, List.tail_cons]
    congr 1
    rw [List.map_congr_left fun j' hj' => Function.update_of_ne (fun h => hj.1 (h ▸ hj') : j' ≠ j) _ _]
    exact map_decYP js hj.2 u (by simpa using hu)

end Bits

/-! ### Per-pair codes -/

namespace LabelSystem

variable {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L] (X : LabelSystem g K R L)

/-- The labels of the items on the pair `{a,b}`, in order. -/
def pairLab (a b : Fin g) (ℓ : K → L) : List L := (X.pairItems a b).map ℓ

/-- The profile entry of `ℓ` on `{a,b}`: the number of non-default labels on the pair. -/
def cntP (a b : Fin g) (ℓ : K → L) : ℕ :=
  ((X.pairLab a b ℓ).filter fun l => decide (l ≠ X.dflt)).length

theorem pairLab_comm (a b : Fin g) (ℓ : K → L) : X.pairLab a b ℓ = X.pairLab b a ℓ := by
  rw [pairLab, pairLab, X.pairItems_comm]

theorem cntP_comm (a b : Fin g) (ℓ : K → L) : X.cntP a b ℓ = X.cntP b a ℓ := by
  rw [cntP, cntP, pairLab_comm]

theorem length_pairLab (a b : Fin g) (ℓ : K → L) :
    (X.pairLab a b ℓ).length = (X.pairItems a b).length := List.length_map _

theorem pairLab_congr {a b : Fin g} {ℓ ℓ' : K → L} (h : ∀ k, X.OnPair a b k → ℓ k = ℓ' k) :
    X.pairLab a b ℓ = X.pairLab a b ℓ' :=
  List.map_congr_left fun k hk => h k (X.mem_pairItems.1 hk)

/-- The other end of an item at `a`. -/
def other (a : Fin g) (k : K) : Fin g := if X.lo k = a then X.hi k else X.lo k

theorem other_ne {a : Fin g} {k : K} (h : X.Inc a k) : X.other a k ≠ a := by
  unfold other
  have := X.lo_ne_hi k
  split_ifs with h'
  · rw [← h']; exact this.symm
  · rcases h with h | h
    · exact absurd h h'
    · rw [← h]; exact this

theorem onPair_other {a : Fin g} {k : K} (h : X.Inc a k) : X.OnPair a (X.other a k) k := by
  unfold other
  split_ifs with h'
  · exact Or.inl ⟨h', rfl⟩
  · rcases h with h | h
    · exact absurd h h'
    · exact Or.inr ⟨rfl, h⟩

theorem other_eq {a b : Fin g} {k : K} (hab : a ≠ b) (h : X.OnPair a b k) : X.other a k = b := by
  unfold other
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, h2]
  · rw [if_neg (by rw [h1]; exact Ne.symm hab), h1]

theorem inc_of_onPair {a b : Fin g} {k : K} (h : X.OnPair a b k) : X.Inc a k := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

theorem getD_pairLab_idxOf {a b : Fin g} {k : K} (hk : X.OnPair a b k) (ℓ : K → L) :
    (X.pairLab a b ℓ).getD ((X.pairItems a b).idxOf k) X.dflt = ℓ k := by
  have hm : k ∈ X.pairItems a b := X.mem_pairItems.2 hk
  have hi := List.idxOf_lt_length_of_mem hm
  rw [pairLab, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
    List.getElem_idxOf]

theorem cntP_restrict (a b : Fin g) (ℓ : K → L) : X.cntP a b (X.restrict a ℓ) = X.cntP a b ℓ := by
  unfold cntP
  rw [X.pairLab_congr fun k hk => X.restrict_of_inc ℓ (X.inc_of_onPair hk)]

/-- **A per-pair code** for the label system `X` and the profile `s`: for every pair `(a,b)` an
injective code `enc a b` of the words of labels on `pairItems a b` with exactly `s a b`
non-default labels, by words of `cap a b` bits, and a decoder `dec a b` with `none` off the image.
The data are symmetric in `a, b` (both ends write the same word). -/
structure PairCode where
  s : Fin g → Fin g → ℕ
  s_symm : ∀ a b, s a b = s b a
  cap : Fin g → Fin g → ℕ
  cap_symm : ∀ a b, cap a b = cap b a
  enc : Fin g → Fin g → List L → List Bool
  enc_symm : ∀ a b, enc a b = enc b a
  dec : Fin g → Fin g → List Bool → Option (List L)
  len_enc : ∀ a b (ls : List L), ls.length = (X.pairItems a b).length →
    (ls.filter fun l => decide (l ≠ X.dflt)).length = s a b → (enc a b ls).length = cap a b
  dec_enc : ∀ a b (ls : List L), ls.length = (X.pairItems a b).length →
    (ls.filter fun l => decide (l ≠ X.dflt)).length = s a b → dec a b (enc a b ls) = some ls
  enc_dec : ∀ a b (z : List Bool) (ls : List L), dec a b z = some ls →
    ls.length = (X.pairItems a b).length ∧ (ls.filter fun l => decide (l ≠ X.dflt)).length = s a b ∧
      enc a b ls = z

namespace PairCode

variable {X} (C : X.PairCode)

/-- The offset of block `b` in a setting of `a`: the widths of the blocks of the nodes `c < b`. -/
def offP (a b : Fin g) : ℕ := (((othersL g a).filter fun c => decide (c < b)).map (C.cap a)).sum

/-- The total width of the blocks of `a`. -/
def sumCap (a : Fin g) : ℕ := ((othersL g a).map (C.cap a)).sum

/-- Block `b` of a setting `z` of `a`. -/
def blockAt (a b : Fin g) (z : List Bool) : List Bool := (z.drop (C.offP a b)).take (C.cap a b)

/-- The bit string of a local state of `a`: the blocks, then the copy bits held by `a`. -/
def encP (a : Fin g) (x : (K → L) × (R → Bool)) : List Bool :=
  (othersL g a).flatMap (fun b => C.enc a b (X.pairLab a b x.1)) ++ (X.heldList a).map x.2

/-- The decoded labels of a setting of `a`. -/
def decLab (a : Fin g) (z : List Bool) : K → L := fun k =>
  if X.Inc a k then
    ((C.dec a (X.other a k) (C.blockAt a (X.other a k) z)).getD []).getD
      ((X.pairItems a (X.other a k)).idxOf k) X.dflt
  else X.dflt

/-- Decoding a setting of `a` into a local state. -/
def decP (a : Fin g) (z : List Bool) : (K → L) × (R → Bool) :=
  (C.decLab a z, decY (X.heldList a) (z.drop (C.sumCap a)))

/-- The local states of `a` whose profile row is `s a`. -/
def locSetP (a : Fin g) : Finset ((K → L) × (R → Bool)) :=
  (X.locSet a).filter fun x => ∀ b, b ≠ a → X.cntP a b x.1 = C.s a b

/-- The shared bits of `{a,b}` as seen from `a`. -/
def projP (a b : Fin g) (x : (K → L) × (R → Bool)) : List Bool :=
  C.enc a b (X.pairLab a b x.1) ++
    (X.pairCopies a b).map fun j => if X.holder j = a then x.2 j else X.par j x.1

end PairCode

/-- **The label-sharing network with per-pair codes.** -/
def netP (C : X.PairCode) : Net g where
  len a := C.sumCap a + (X.heldList a).length
  S a := (C.locSetP a).image (C.encP a)
  W a z := X.T a (C.decP a z).1 (C.decP a z).2
  Ψ a b z z' := if C.projP a b (C.decP a z) = C.projP b a (C.decP b z') then 1 else 0
  c a b := C.cap a b + (X.pairCopies a b).length
  f a b z θ := if C.projP a b (C.decP a z) = θ then 1 else 0

namespace PairCode

variable {X} (C : X.PairCode)

/-! #### Encoding and decoding -/

theorem mem_locSetP {a : Fin g} {x : (K → L) × (R → Bool)} :
    x ∈ C.locSetP a ↔ x ∈ X.locSet a ∧ ∀ b, b ≠ a → X.cntP a b x.1 = C.s a b := by
  simp [locSetP]

theorem length_enc_pair {a b : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) (hb : b ≠ a) :
    (C.enc a b (X.pairLab a b x.1)).length = C.cap a b :=
  C.len_enc a b _ (X.length_pairLab a b _) ((C.mem_locSetP.1 hx).2 b hb)

theorem length_encP {a : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) :
    (C.encP a x).length = (X.netP C).len a := by
  simp only [encP, netP, List.length_append, List.length_map, sumCap]
  rw [length_flatMap_eq _ _ (C.cap a) fun b hb => C.length_enc_pair hx (mem_othersL.1 hb)]

theorem blockAt_encP {a b : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) (hb : b ≠ a) :
    C.blockAt a b (C.encP a x) = C.enc a b (X.pairLab a b x.1) :=
  take_drop_flatMap _ (othersL_pairwise a) _ _ (fun c hc => C.length_enc_pair hx (mem_othersL.1 hc))
    _ (mem_othersL.2 hb)

theorem drop_sumCap_encP {a : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) :
    (C.encP a x).drop (C.sumCap a) = (X.heldList a).map x.2 := by
  unfold encP
  rw [List.drop_left']
  rw [length_flatMap_eq _ _ (C.cap a) fun b hb => C.length_enc_pair hx (mem_othersL.1 hb)]
  rfl

theorem decLab_encP {a : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) :
    C.decLab a (C.encP a x) = x.1 := by
  have hx' := C.mem_locSetP.1 hx
  have hl := hx'.1
  simp only [locSet, mem_filter, mem_univ, true_and] at hl
  funext k
  unfold decLab
  split_ifs with h
  · have hb := X.other_ne h
    rw [C.blockAt_encP hx hb, C.dec_enc _ _ _ (X.length_pairLab _ _ _) (hx'.2 _ hb), Option.getD_some,
      X.getD_pairLab_idxOf (X.onPair_other h)]
  · exact (hl.1 k h).symm

theorem dec_encP {a : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) :
    C.decP a (C.encP a x) = x := by
  have hl := (C.mem_locSetP.1 hx).1
  simp only [locSet, mem_filter, mem_univ, true_and] at hl
  unfold decP
  rw [C.decLab_encP hx, C.drop_sumCap_encP hx, decY_map x.2 (X.heldList a) (X.rord_nodup.filter _)]
  refine Prod.ext rfl (funext fun j => ?_)
  simp only [mem_heldList]
  split_ifs with h
  · rfl
  · exact (hl.2 j h).symm

theorem mem_SP {a : Fin g} {z : List Bool} :
    z ∈ (X.netP C).S a ↔ ∃ x ∈ C.locSetP a, C.encP a x = z := by
  simp [netP]

theorem getD_decLab {a b : Fin g} (hab : a ≠ b) {z : List Bool} {ls : List L}
    (hd : C.dec a b (C.blockAt a b z) = some ls) : X.pairLab a b (C.decLab a z) = ls := by
  obtain ⟨hlen, -, -⟩ := C.enc_dec _ _ _ _ hd
  have hn : (X.pairItems a b).Nodup := X.kord_nodup.filter _
  refine List.ext_getElem (by rw [length_pairLab, hlen]) fun i h1 h2 => ?_
  simp only [LabelSystem.pairLab, List.getElem_map]
  have hk : X.OnPair a b (X.pairItems a b)[i] := X.mem_pairItems.1 (List.getElem_mem _)
  unfold decLab
  rw [if_pos (X.inc_of_onPair hk), X.other_eq hab hk, hd, Option.getD_some,
    hn.idxOf_getElem, List.getD_eq_getElem]

/-- **Membership in `S a`**: the right length, and every block decodes. -/
theorem mem_SP_iff (a : Fin g) (z : List Bool) :
    z ∈ (X.netP C).S a ↔ z.length = (X.netP C).len a ∧
      ∀ b, b ≠ a → (C.dec a b (C.blockAt a b z)).isSome := by
  rw [C.mem_SP]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨C.length_encP hx, fun b hb => ?_⟩
    rw [C.blockAt_encP hx hb, C.dec_enc _ _ _ (X.length_pairLab _ _ _) ((C.mem_locSetP.1 hx).2 b hb)]
    rfl
  · rintro ⟨hl, hb⟩
    have hsome : ∀ b, b ≠ a → ∃ ls, C.dec a b (C.blockAt a b z) = some ls := fun b h =>
      Option.isSome_iff_exists.1 (hb b h)
    refine ⟨C.decP a z, ?_, ?_⟩
    · rw [C.mem_locSetP]
      refine ⟨?_, fun b h => ?_⟩
      · simp only [locSet, mem_filter, mem_univ, true_and, decP]
        refine ⟨fun k hk => ?_, fun j hj => decY_not_memP _ _ j (fun h => hj (X.mem_heldList.1 h))⟩
        simp only [decLab, if_neg hk]
      · obtain ⟨ls, hls⟩ := hsome b h
        obtain ⟨-, hs, -⟩ := C.enc_dec _ _ _ _ hls
        unfold cntP
        rw [show (C.decP a z).1 = C.decLab a z from rfl, C.getD_decLab (Ne.symm h) hls, hs]
    · unfold encP decP
      simp only
      have hblocks : (othersL g a).flatMap (fun b => C.enc a b (X.pairLab a b (C.decLab a z))) =
          (othersL g a).flatMap (fun b => C.blockAt a b z) := by
        refine List.flatMap_congr fun b hb => ?_
        have hb' := mem_othersL.1 hb
        obtain ⟨ls, hls⟩ := hsome b hb'
        rw [C.getD_decLab (Ne.symm hb') hls]
        exact (C.enc_dec _ _ _ _ hls).2.2
      have hcat : (othersL g a).flatMap (fun b => C.blockAt a b z) = z.take (C.sumCap a) :=
        flatMap_blocks _ (othersL_pairwise a) (C.cap a) (C.offP a) (fun b _ => rfl) z
      have hn2 : (X.heldList a).Nodup := X.rord_nodup.filter _
      rw [hblocks, hcat, map_decYP _ hn2 _ (by simp [hl, netP]), List.take_append_drop]

/-! #### The consistent settings -/

/-- The global labellings of profile `s`. -/
def profSet : Finset (K → L) := univ.filter fun ℓ => ∀ a b, a ≠ b → X.cntP a b ℓ = C.s a b

theorem xOf_memP {ℓ : K → L} (hℓ : ℓ ∈ C.profSet) (a : Fin g) : X.xOf ℓ a ∈ C.locSetP a := by
  rw [C.mem_locSetP]
  refine ⟨X.xOf_mem ℓ a, fun b hb => ?_⟩
  show X.cntP a b (X.restrict a ℓ) = C.s a b
  rw [X.cntP_restrict]
  exact (mem_filter.1 hℓ).2 a b (Ne.symm hb)

theorem projP_xOf (ℓ : K → L) (a b : Fin g) :
    C.projP a b (X.xOf ℓ a) =
      C.enc a b (X.pairLab a b ℓ) ++ (X.pairCopies a b).map fun j => X.par j ℓ := by
  unfold projP
  congr 1
  · congr 1
    exact X.pairLab_congr fun k hk => X.restrict_of_inc ℓ (X.inc_of_onPair hk)
  · refine List.map_congr_left fun j hj => ?_
    rw [X.mem_pairCopies] at hj
    by_cases h : X.holder j = a
    · simp [xOf, copyY, h]
    · have hs : X.source j = a := by tauto
      simp only [h, if_false, xOf]
      rw [← hs, X.par_restrict]

theorem projP_xOf_symm (ℓ : K → L) (a b : Fin g) :
    C.projP a b (X.xOf ℓ a) = C.projP b a (X.xOf ℓ b) := by
  rw [C.projP_xOf, C.projP_xOf, X.pairLab_comm, C.enc_symm, X.pairCopies_comm]

/-- Consistent local states of profile `s` come from their glued labelling. -/
theorem eq_xOf_glueP (x : Fin g → (K → L) × (R → Bool)) (hx : ∀ a, x a ∈ C.locSetP a)
    (hc : ∀ a b, a ≠ b → C.projP a b (x a) = C.projP b a (x b)) :
    x = fun a => X.xOf (X.glue x) a := by
  have hsplit : ∀ a b, a ≠ b →
      X.pairLab a b (x a).1 = X.pairLab a b (x b).1 ∧
      ((X.pairCopies a b).map fun j => if X.holder j = a then (x a).2 j else X.par j (x a).1) =
        (X.pairCopies a b).map fun j => if X.holder j = b then (x b).2 j else X.par j (x b).1 := by
    intro a b hab
    have h := hc a b hab
    unfold projP at h
    rw [X.pairCopies_comm b a, X.pairLab_comm b a, C.enc_symm b a] at h
    have hl1 := C.length_enc_pair (hx a) (Ne.symm hab)
    have hl2 : (C.enc a b (X.pairLab a b (x b).1)).length = C.cap a b := by
      rw [C.enc_symm, X.pairLab_comm, C.length_enc_pair (hx b) hab, C.cap_symm]
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hl1, hl2])
    refine ⟨?_, h2⟩
    have e1 := C.dec_enc a b _ (X.length_pairLab _ _ _) ((C.mem_locSetP.1 (hx a)).2 b (Ne.symm hab))
    have e2 : C.dec a b (C.enc a b (X.pairLab a b (x b).1)) = some (X.pairLab a b (x b).1) := by
      have := C.dec_enc a b (X.pairLab a b (x b).1) (X.length_pairLab _ _ _) (by
        have := (C.mem_locSetP.1 (hx b)).2 a hab
        rw [cntP, pairLab_comm] at this
        rw [this, C.s_symm])
      exact this
    rw [h1, e2] at e1
    exact (Option.some.inj e1).symm
  have F1 : ∀ k, (x (X.lo k)).1 k = (x (X.hi k)).1 k := fun k => by
    have h := (hsplit _ _ (X.lo_ne_hi k)).1
    have hk : X.OnPair (X.lo k) (X.hi k) k := Or.inl ⟨rfl, rfl⟩
    have := congrArg (fun l => l.getD ((X.pairItems (X.lo k) (X.hi k)).idxOf k) X.dflt) h
    simpa only [X.getD_pairLab_idxOf hk] using this
  have F2 : ∀ j, (x (X.holder j)).2 j = X.par j (x (X.source j)).1 := fun j => by
    have h := (List.map_inj_left.1 (hsplit _ _ (X.holder_ne j)).2) j
      (X.mem_pairCopies.2 (Or.inl ⟨rfl, rfl⟩))
    simpa [X.holder_ne j, Ne.symm (X.holder_ne j)] using h
  have G1 : ∀ a k, X.Inc a k → (x a).1 k = X.glue x k := by
    rintro a k (h | h)
    · subst h; rfl
    · subst h; exact (F1 k).symm
  have G2 : ∀ a, (x a).1 = X.restrict a (X.glue x) := by
    intro a; funext k
    have ha := (C.mem_locSetP.1 (hx a)).1
    simp only [locSet, mem_filter, mem_univ, true_and] at ha
    by_cases h : X.Inc a k
    · rw [X.restrict_of_inc _ h, G1 a k h]
    · simp only [restrict, h, if_false]; exact ha.1 k h
  funext a
  have ha := (C.mem_locSetP.1 (hx a)).1
  simp only [locSet, mem_filter, mem_univ, true_and] at ha
  refine Prod.ext (G2 a) ?_
  funext j
  simp only [xOf, copyY]
  by_cases h : X.holder j = a
  · subst h
    rw [if_pos rfl, F2 j, G2 (X.source j), X.par_restrict]
  · rw [if_neg h]; exact ha.2 j h

/-- The setting induced by a global labelling. -/
def zOfP (ℓ : K → L) : Fin g → List Bool := fun a => C.encP a (X.xOf ℓ a)

theorem zOfP_injOn : Set.InjOn C.zOfP (C.profSet : Set (K → L)) := by
  intro ℓ hℓ ℓ' hℓ' h
  funext k
  have h1 := congrArg (fun z => (C.decP (X.lo k) (z (X.lo k))).1 k) h
  simp only [zOfP, C.dec_encP (C.xOf_memP hℓ _), C.dec_encP (C.xOf_memP hℓ' _)] at h1
  simpa [xOf, X.restrict_of_inc _ (Or.inl rfl : X.Inc (X.lo k) k)] using h1

theorem glue_mem_profSet (x : Fin g → (K → L) × (R → Bool)) (hx : ∀ a, x a ∈ C.locSetP a)
    (he : x = fun a => X.xOf (X.glue x) a) : X.glue x ∈ C.profSet := by
  refine mem_filter.2 ⟨mem_univ _, fun a b hab => ?_⟩
  have h1 := (C.mem_locSetP.1 (hx a)).2 b (Ne.symm hab)
  rw [congrFun he a] at h1
  rwa [show (X.xOf (X.glue x) a).1 = X.restrict a (X.glue x) from rfl, X.cntP_restrict] at h1

/-- **The value of the network with per-pair codes** (Theorem 2.5, first part): the sum over the
global labellings of profile `s` of the product of the node tables, fed the correct copy bits. -/
theorem value_netP :
    (X.netP C).value = ∑ ℓ ∈ C.profSet, ∏ a, X.T a ℓ fun j => X.par j ℓ := by
  have hsub : C.profSet.image C.zOfP ⊆ Fintype.piFinset (X.netP C).S := by
    intro z hz
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hz
    exact Fintype.mem_piFinset.2 fun a => mem_image.2 ⟨_, C.xOf_memP hℓ a, rfl⟩
  have hzero : ∀ z ∈ Fintype.piFinset (X.netP C).S, z ∉ C.profSet.image C.zOfP →
      (∏ a, (X.netP C).W a (z a)) * ∏ p ∈ pairs (Fin g), (X.netP C).Ψ p.1 p.2 (z p.1) (z p.2) = 0 := by
    intro z hz hni
    by_contra hne
    apply hni
    have hS := Fintype.mem_piFinset.1 hz
    have hΨ := right_ne_zero_of_mul hne
    rw [prod_ne_zero_iff] at hΨ
    choose x hx hxz using fun a => mem_image.1 (hS a)
    have hcp : ∀ p ∈ pairs (Fin g), C.projP p.1 p.2 (x p.1) = C.projP p.2 p.1 (x p.2) := by
      intro p hp
      have := hΨ p hp
      simp only [netP, ← hxz, C.dec_encP (hx _)] at this
      by_contra h'
      exact this (if_neg h')
    have hc : ∀ a b, a ≠ b → C.projP a b (x a) = C.projP b a (x b) := by
      intro a b hab
      rcases lt_or_gt_of_ne hab with h | h
      · exact hcp (a, b) (by simp [pairs, h])
      · exact (hcp (b, a) (by simp [pairs, h])).symm
    have hxe := C.eq_xOf_glueP x hx hc
    refine mem_image.2 ⟨X.glue x, C.glue_mem_profSet x hx hxe, ?_⟩
    funext a
    rw [← hxz a, zOfP]
    exact congrArg (C.encP a) (congrFun hxe a).symm
  rw [Net.value, ← sum_subset hsub hzero, sum_image C.zOfP_injOn]
  refine sum_congr rfl fun ℓ hℓ => ?_
  have hW : ∀ a, (X.netP C).W a (C.zOfP ℓ a) = X.T a ℓ fun j => X.par j ℓ := by
    intro a
    simp only [netP, zOfP, C.dec_encP (C.xOf_memP hℓ _)]
    exact X.T_xOf ℓ a
  have hΨ : ∀ p ∈ pairs (Fin g), (X.netP C).Ψ p.1 p.2 (C.zOfP ℓ p.1) (C.zOfP ℓ p.2) = 1 := by
    intro p _
    simp only [netP, zOfP, C.dec_encP (C.xOf_memP hℓ _)]
    rw [if_pos (C.projP_xOf_symm ℓ _ _)]
  rw [prod_congr rfl hΨ, prod_const_one, mul_one]
  exact prod_congr rfl fun a _ => hW a

/-! #### Counting: `∑_b c a b`, `U`, and Definition 2 -/

theorem sum_othersL (a : Fin g) (h : Fin g → ℕ) :
    ((othersL g a).map h).sum = ∑ b ∈ univ.erase a, h b := by
  rw [← List.sum_toFinset _ (othersL_nodup a)]
  congr 1
  ext b
  simp [mem_othersL]

theorem sumCap_eq (a : Fin g) : C.sumCap a = ∑ b ∈ univ.erase a, C.cap a b := sum_othersL a _

theorem sum_c_eqP (a : Fin g) :
    ∑ b ∈ univ.erase a, (X.netP C).c a b =
      ∑ b ∈ univ.erase a, C.cap a b + #(univ.filter (X.Touch a)) := by
  simp only [netP, sum_add_distrib, pairCopies, length_filter_of_complete _ X.rord_nodup X.mem_rord]
  rw [X.sum_card_copyOn]

theorem lenP_le_sum_c (a : Fin g) : (X.netP C).len a ≤ ∑ b ∈ univ.erase a, (X.netP C).c a b := by
  rw [sum_c_eqP]
  simp only [netP, sumCap_eq, heldList, length_filter_of_complete _ X.rord_nodup X.mem_rord]
  refine Nat.add_le_add_left (card_le_card fun j hj => ?_) _
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact Or.inl hj

/-- **The total `U`**: twice the block widths over the pairs, plus each copy bit on both ends. -/
theorem U_eqP : (X.netP C).U = ∑ a, ∑ b ∈ univ.erase a, C.cap a b + 2 * Fintype.card R := by
  unfold Net.U
  simp only [sum_c_eqP, sum_add_distrib, X.sum_card_touch]

theorem projP_length {a b : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ C.locSetP a) (hb : b ≠ a) :
    (C.projP a b x).length = (X.netP C).c a b := by
  simp [projP, netP, C.length_enc_pair hx hb]

/-- **Definition 2 for the network with per-pair codes.** -/
theorem netP_is {P B : ℕ} (hP1 : 1 ≤ P) (hB : 1 ≤ B)
    (hP : ∀ a, ∑ b ∈ univ.erase a, (X.netP C).c a b ≤ P)
    (hT : ∀ a, ∀ x ∈ C.locSetP a, |X.T a x.1 x.2| < 2 ^ B) : (X.netP C).Is P B := by
  have h01 : ∀ p : Prop, [Decidable p] → |(if p then (1 : ℤ) else 0)| < 2 ^ B := by
    intro p _
    have : (1 : ℤ) < 2 ^ B := one_lt_pow₀ (by norm_num) (by omega)
    split_ifs <;> simp [this]
  refine
    { P_pos := hP1
      B_pos := hB
      len_S := ?_
      len_le := fun a => (C.lenP_le_sum_c a).trans (hP a)
      Ψ_symm := ?_
      c_symm := ?_
      fact := ?_
      i := hP
      ii_W := ?_
      ii_Ψ := fun a b _ z _ z' _ => h01 _
      ii_f := fun a b _ z _ θ _ => h01 _ }
  · intro a z hz
    obtain ⟨x, hx, rfl⟩ := C.mem_SP.1 hz
    exact C.length_encP hx
  · intro a b _ z _ z' _
    simp only [netP]
    by_cases h : C.projP a b (C.decP a z) = C.projP b a (C.decP b z')
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro a b
    simp only [netP, C.cap_symm a b, X.pairCopies_comm a b]
  · intro a b hab z hz z' _
    obtain ⟨x, hx, rfl⟩ := C.mem_SP.1 hz
    simp only [netP]
    simp_rw [boole_mul]
    have hm : C.projP a b (C.decP a (C.encP a x)) ∈ words (C.cap a b + (X.pairCopies a b).length) := by
      rw [mem_words, C.dec_encP hx]
      exact C.projP_length hx (Ne.symm hab)
    rw [sum_ite_eq, if_pos hm]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  · intro a z hz
    obtain ⟨x, hx, rfl⟩ := C.mem_SP.1 hz
    simp only [netP, C.dec_encP hx]
    exact hT a x hx

end PairCode

end LabelSystem

/-! ### The rank code of the labels -/

namespace Rank

/-- The labels as numbers (`N ↦ 0`, `l0 ↦ 1`, …, `l3 ↦ 4`). -/
def labNum : Label → ℕ
  | .N => 0
  | .l0 => 1
  | .l1 => 2
  | .l2 => 3
  | .l3 => 4

/-- The 2-bit code of a label `≠ N`. -/
def labCd (l : Label) : List Bool := toWord 2 (labNum l - 1)

/-- Reading a 2-bit code. -/
def labDc (u : List Bool) : Label :=
  match ofWord u with
  | 0 => .l0
  | 1 => .l1
  | 2 => .l2
  | _ => .l3

theorem length_labCd (l : Label) : (labCd l).length = 2 := length_toWord _ _

theorem labDc_labCd (l : Label) (h : l ≠ .N) : labDc (labCd l) = l := by
  cases l <;> first | exact absurd rfl h | decide

theorem labDc_ne (u : List Bool) : labDc u ≠ .N := by
  unfold labDc; split <;> simp

theorem labCd_labDc {u : List Bool} (hu : u.length = 2) : labCd (labDc u) = u := by
  match u, hu with
  | [b0, b1], _ => cases b0 <;> cases b1 <;> decide

theorem labNum_labDc (u : List Bool) : labNum (labDc (u.take 2)) = ofWord (u.take 2) + 1 := by
  have h : ofWord (u.take 2) < 4 := by
    have := ofWord_lt (u.take 2)
    have : (u.take 2).length ≤ 2 := List.length_take_le _ _
    have : 2 ^ (u.take 2).length ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  unfold labDc
  generalize ofWord (u.take 2) = v at h ⊢
  rcases v with _ | _ | _ | _ | v <;> simp [labNum] <;> omega

theorem nd_fill (bs u : List Bool) : nd Label.N (fill Label.N 2 labDc bs u) = bs := by
  induction bs generalizing u with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · simp [fill, nd] at ih ⊢; exact ih u
    · simp only [fill, nd, List.map_cons] at ih ⊢
      rw [ih]; simp [labDc_ne]

theorem flatMap_fill (bs u : List Bool) (hu : 2 * cnt bs ≤ u.length) :
    ((fill Label.N 2 labDc bs u).filter fun l => decide (l ≠ Label.N)).flatMap labCd =
      u.take (2 * cnt bs) := by
  induction bs generalizing u with
  | nil => simp [fill]
  | cons b bs ih =>
    cases b
    · simp only [fill, cnt_false] at hu ⊢
      rw [List.filter_cons_of_neg (by simp)]
      exact ih u hu
    · simp only [fill, cnt_true] at hu ⊢
      rw [List.filter_cons_of_pos (by simpa using labDc_ne _), List.flatMap_cons,
        labCd_labDc (by rw [List.length_take]; omega), ih (u.drop 2) (by rw [List.length_drop]; omega),
        show 2 * (cnt bs + 1) = 2 + 2 * cnt bs by ring, List.take_add]

/-- **A block is valid iff it has the right length and its rank field is in range.** -/
theorem decR_isSome_iff (e s : ℕ) (z : List Bool) :
    (decR Label.N 2 labCd labDc e s z).isSome ↔
      z.length = cw e s + 2 * s ∧ ofWord (z.take (cw e s)) < Nat.choose e s := by
  constructor
  · intro h
    obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨h1, h2, h3⟩ := encR_of_decR Label.N hls
    subst h1
    refine ⟨length_encR Label.N length_labCd e s ls h3, ?_⟩
    unfold encR
    rw [List.take_left' (length_toWord _ _), ofWord_toWord (by
      have := rank_lt_two_pow_cw (nd Label.N ls); rwa [length_nd, h2, h3] at this)]
    have := rank_lt (nd Label.N ls)
    rwa [length_nd, h2, h3] at this
  · rintro ⟨hl, hr⟩
    obtain ⟨u1, u2, u3⟩ := unrank_spec e s _ hr
    have hraw : nd Label.N (rawR Label.N 2 labDc e s z) = unrank e s (ofWord (z.take (cw e s))) := by
      unfold rawR; exact nd_fill _ _
    have hlen : (rawR Label.N 2 labDc e s z).length = e := by
      rw [← length_nd Label.N, hraw, u1]
    have hcnt : cnt (nd Label.N (rawR Label.N 2 labDc e s z)) = s := by rw [hraw, u2]
    have henc : encR Label.N labCd e s (rawR Label.N 2 labDc e s z) = z := by
      unfold encR
      rw [hraw, u3]
      have h1 : toWord (cw e s) (ofWord (z.take (cw e s))) = z.take (cw e s) := by
        have := toWord_ofWord (z.take (cw e s))
        rwa [List.length_take, min_eq_left (by omega)] at this
      rw [h1]
      unfold rawR
      rw [flatMap_fill _ _ (by rw [u2, List.length_drop]; omega), u2]
      rw [show 2 * s = (z.drop (cw e s)).length by rw [List.length_drop]; omega, List.take_length,
        List.take_append_drop]
    unfold decR
    rw [if_pos ⟨henc, hlen, hcnt⟩]
    rfl

end Rank

namespace LabelSystem

open Rank

variable {g : ℕ} {K R : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  (X : LabelSystem g K R Label)

theorem cnt_nd_eq (ls : List Label) (hd : X.dflt = Label.N) :
    cnt (nd Label.N ls) = (ls.filter fun l => decide (l ≠ X.dflt)).length := by
  rw [cnt_nd, hd]

/-- **The rank code** for the profile `s` (labels `Label`, default `N`): block width
`cap a b = cw(e_ab, s_ab) + 2 s_ab` with `e_ab = |pairItems a b|`. -/
def rankPC (s : Fin g → Fin g → ℕ) (hs : ∀ a b, s a b = s b a) (hd : X.dflt = Label.N) : X.PairCode where
  s := s
  s_symm := hs
  cap a b := cw (X.pairItems a b).length (s a b) + 2 * s a b
  cap_symm a b := by rw [X.pairItems_comm, hs]
  enc a b := encR Label.N labCd (X.pairItems a b).length (s a b)
  enc_symm a b := by rw [X.pairItems_comm, hs]
  dec a b := decR Label.N 2 labCd labDc (X.pairItems a b).length (s a b)
  len_enc a b ls _ h2 := length_encR Label.N length_labCd _ _ ls (by rw [X.cnt_nd_eq ls hd, h2])
  dec_enc a b ls h1 h2 := decR_encR Label.N length_labCd labDc_labCd h1 (by rw [X.cnt_nd_eq ls hd, h2])
  enc_dec a b z ls h := by
    obtain ⟨h1, h2, h3⟩ := encR_of_decR Label.N h
    exact ⟨h2, by rw [← X.cnt_nd_eq ls hd, h3], h1⟩

variable {X} {s : Fin g → Fin g → ℕ} {hs : ∀ a b, s a b = s b a} {hd : X.dflt = Label.N}

@[simp] theorem rankPC_cap (a b : Fin g) :
    (X.rankPC s hs hd).cap a b = cw (X.pairItems a b).length (s a b) + 2 * s a b := rfl

/-- **Membership in `S a` for the rank code**, at word level: the right length, and the rank field
of every block is in range and the block has the right length. -/
theorem mem_SP_rank_iff (a : Fin g) (z : List Bool) :
    z ∈ (X.netP (X.rankPC s hs hd)).S a ↔ z.length = (X.netP (X.rankPC s hs hd)).len a ∧
      ∀ b, b ≠ a → ((X.rankPC s hs hd).blockAt a b z).length =
          cw (X.pairItems a b).length (s a b) + 2 * s a b ∧
        ofWord (((X.rankPC s hs hd).blockAt a b z).take (cw (X.pairItems a b).length (s a b))) <
          Nat.choose (X.pairItems a b).length (s a b) := by
  rw [PairCode.mem_SP_iff]
  exact and_congr Iff.rfl (forall_congr' fun b => imp_congr_right fun _ => decR_isSome_iff _ _ _)

/-- **The decoded labels as numbers** (for the table procedure): for `z ∈ S a` and an item `k` at
`a`, with `b` its other end, the number of the label of `k` is entry `idx k` of `rawCodes` of
block `b`. -/
theorem labNum_decLab {a : Fin g} {z : List Bool} (hz : z ∈ (X.netP (X.rankPC s hs hd)).S a) {k : K}
    (hk : X.Inc a k) :
    labNum ((X.rankPC s hs hd).decLab a z k) =
      (rawCodes (X.pairItems a (X.other a k)).length (s a (X.other a k)) 2
        ((X.rankPC s hs hd).blockAt a (X.other a k) z)).getD
        ((X.pairItems a (X.other a k)).idxOf k) 0 := by
  have hv := ((X.rankPC s hs hd).mem_SP_iff a z).1 hz
  obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.1 (hv.2 _ (X.other_ne hk))
  have hraw : ls = rawR Label.N 2 labDc (X.pairItems a (X.other a k)).length (s a (X.other a k))
      ((X.rankPC s hs hd).blockAt a (X.other a k) z) := by
    have h := hls
    simp only [rankPC, decR] at h
    split_ifs at h
    exact (Option.some.inj h).symm
  unfold PairCode.decLab
  rw [if_pos hk, hls, Option.getD_some, ← rawR_map Label.N 2 labDc labNum rfl labNum_labDc, ← hraw,
    show (0 : ℕ) = labNum (X.dflt) by rw [hd]; rfl, List.getD_map]

end LabelSystem

end EthFollowup.ExactHC
