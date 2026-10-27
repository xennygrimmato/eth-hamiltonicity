/-
# A generic label-sharing network in Anthropic's `Net g` format (module C1a)

Abstract setting (independent of Hamiltonian cycles), packaged as `LabelSystem g K R L`:

* nodes `Fin g`; a finite type `K` of *crossing items*, item `k` sits on the pair of distinct nodes
  `lo k < hi k`; labels of items lie in a finite alphabet `L`;
* a finite type `R` of *copy bits*: bit `j` is held by node `holder j` and must equal the parity
  `par j ℓ`, which depends only on the labels of the items incident to `source j ≠ holder j`;
* for each node `a` an integer table `T a ℓ y`, depending only on the labels of the items incident to
  `a` and on the copy bits held by `a`.

Fixed enumerations `kord`, `rord` of `K` and `R` fix the bit layout. Labels are written with a
fixed-width code `LabelCode L w` (`finCode q` : `Fin (q+1)` in `⌈log₂ (q+1)⌉` binary bits).

The network `X.net C : Eight.SecNetworks.Net g`:

* a setting of `a` is `enc a (ℓ, y)` = codes of `ℓ k` for the items `k` incident to `a` (in the order
  `kord`), followed by the bits `y j` held by `a` (in the order `rord`); `S a` is the set of these
  (with `ℓ`, `y` defaulted off the incident items / held bits); `len a = deg a · w + #held a`;
* `W a z = T a (dec z)`;
* on the pair `{a,b}`: `c a b = #(items on {a,b}) · w + #(copy bits on {a,b})`;
  `proj a b x` = codes of the labels of the items on `{a,b}`, then for each copy bit `j` on `{a,b}`:
  `y j` if `a` holds it, `par j ℓ` if `a` is its source;
  `f a b z θ = [proj a b (dec z) = θ]`, `Ψ a b z z' = [proj a b (dec z) = proj b a (dec z')]`.

Main results:

* `value_net : (X.net C).value = ∑ ℓ : K → L, ∏ a, X.T a ℓ (fun j => X.par j ℓ)` (Theorem 5.3 pattern);
* `net_is` : `(X.net C).Is P B` from `1 ≤ P`, `1 ≤ B`, `|T a ℓ y| < 2^B` and
  `∀ a, deg a · w + #touch a ≤ P` (`touch a` = copy bits held by or sourced at `a`);
  `net_is'` : the same with the hypothesis `∀ a, ∑ b ≠ a, c a b ≤ P`;
* `sum_c_eq : ∑ b ≠ a, c a b = deg a · w + #touch a`, `len_le_sum_c`,
  `U_eq : (X.net C).U = 2 * (card K * w + card R)`.
-/
import Eight.SecNetworks_Defs

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Eight.SecNetworks Groundwork Finset

/-! ### Fixed-width codes of labels -/

/-- A code of the labels `L` by words of exactly `w` bits, with a left inverse. -/
structure LabelCode (L : Type) (w : ℕ) where
  enc : L → List Bool
  dec : List Bool → L
  len : ∀ l, (enc l).length = w
  dec_enc : ∀ l, dec (enc l) = l

/-- The binary code of `Fin (q+1)` with `⌈log₂ (q+1)⌉` bits, lowest bit first. -/
def finCode (q : ℕ) : LabelCode (Fin (q + 1)) (Nat.clog 2 (q + 1)) where
  enc i := toWord (Nat.clog 2 (q + 1)) i.val
  dec z := ⟨min (ofWord z) q, by omega⟩
  len _ := length_toWord _ _
  dec_enc i := by
    have h : i.val < 2 ^ Nat.clog 2 (q + 1) :=
      lt_of_lt_of_le i.isLt (Nat.le_pow_clog (by norm_num) _)
    ext
    simp only [ofWord_toWord h]
    omega

section Codes

variable {L : Type} {w : ℕ} (C : LabelCode L w) {ι : Type} [DecidableEq ι]

/-- The codes of the labels `ℓ k`, `k ∈ ks`, concatenated. -/
def encL (ks : List ι) (ℓ : ι → L) : List Bool := ks.flatMap fun k => C.enc (ℓ k)

theorem length_encL (ks : List ι) (ℓ : ι → L) : (encL C ks ℓ).length = ks.length * w := by
  induction ks with
  | nil => simp [encL]
  | cons k ks ih =>
    simp only [encL, List.flatMap_cons, List.length_append, C.len, List.length_cons] at ih ⊢
    rw [ih]; ring

/-- Decoding of `encL`: reads `w` bits per item of `ks`; the default `d` elsewhere. -/
def decL (d : L) : List ι → List Bool → ι → L
  | [], _ => fun _ => d
  | k :: ks, z => Function.update (decL d ks (z.drop w)) k (C.dec (z.take w))

theorem decL_encL (d : L) (ℓ : ι → L) :
    ∀ (ks : List ι), ks.Nodup → ∀ rest : List Bool,
      decL C d ks (encL C ks ℓ ++ rest) = fun k => if k ∈ ks then ℓ k else d
  | [], _, _ => by funext k; simp [decL]
  | k :: ks, h, rest => by
    have hk := List.nodup_cons.1 h
    have e : encL C (k :: ks) ℓ ++ rest = C.enc (ℓ k) ++ (encL C ks ℓ ++ rest) := by
      simp [encL]
    rw [e, decL, List.take_left' (C.len _), List.drop_left' (C.len _), decL_encL d ℓ ks hk.2 rest,
      C.dec_enc]
    funext k'
    by_cases h' : k' = k
    · subst h'; simp
    · simp [h']

theorem encL_inj {ks : List ι} {ℓ ℓ' : ι → L} (h : encL C ks ℓ = encL C ks ℓ') :
    ∀ k ∈ ks, ℓ k = ℓ' k := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [encL, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [C.len, C.len])
    intro k' hk'
    rcases List.mem_cons.1 hk' with rfl | hk'
    · have := congrArg C.dec h1
      simpa [C.dec_enc] using this
    · exact ih h2 k' hk'

theorem encL_congr {ks : List ι} {ℓ ℓ' : ι → L} (h : ∀ k ∈ ks, ℓ k = ℓ' k) :
    encL C ks ℓ = encL C ks ℓ' := by
  unfold encL
  exact List.flatMap_congr fun k hk => by rw [h k hk]

end Codes

section Bits

variable {ι : Type} [DecidableEq ι]

/-- Decoding of `js.map y`: one bit per element of `js`; `false` elsewhere. -/
def decY : List ι → List Bool → ι → Bool
  | [], _ => fun _ => false
  | j :: js, z => Function.update (decY js z.tail) j (z.headD false)

theorem decY_map (y : ι → Bool) :
    ∀ (js : List ι), js.Nodup → decY js (js.map y) = fun j => if j ∈ js then y j else false
  | [], _ => by funext j; simp [decY]
  | j :: js, h => by
    have hj := List.nodup_cons.1 h
    simp only [List.map_cons, decY, List.tail_cons, List.headD_cons, decY_map y js hj.2]
    funext j'
    by_cases h' : j' = j
    · subst h'; simp
    · simp [h']

end Bits

theorem length_filter_of_complete {ι : Type} [Fintype ι] [DecidableEq ι] (l : List ι)
    (hn : l.Nodup) (hc : ∀ x, x ∈ l) (p : ι → Prop) [DecidablePred p] :
    (l.filter fun x => decide (p x)).length = #(univ.filter p) := by
  rw [← List.toFinset_card_of_nodup (hn.filter _)]
  congr 1
  ext x
  simp [hc]

/-! ### Label systems -/

/-- The abstract data of a label-sharing network on the nodes `Fin g`. -/
structure LabelSystem (g : ℕ) (K R L : Type) where
  /-- a fixed enumeration of the items (fixes the bit layout) -/
  kord : List K
  kord_nodup : kord.Nodup
  mem_kord : ∀ k, k ∈ kord
  /-- a fixed enumeration of the copy bits -/
  rord : List R
  rord_nodup : rord.Nodup
  mem_rord : ∀ j, j ∈ rord
  /-- item `k` sits on the pair `lo k < hi k` -/
  lo : K → Fin g
  hi : K → Fin g
  lo_lt : ∀ k, lo k < hi k
  /-- copy bit `j` is held by `holder j` and computed by `source j` -/
  holder : R → Fin g
  source : R → Fin g
  holder_ne : ∀ j, holder j ≠ source j
  /-- the default label (used off the items incident to a node) -/
  dflt : L
  /-- the value that copy bit `j` must have -/
  par : R → (K → L) → Bool
  /-- the node tables -/
  T : Fin g → (K → L) → (R → Bool) → ℤ
  par_local : ∀ j (ℓ ℓ' : K → L), (∀ k, (lo k = source j ∨ hi k = source j) → ℓ k = ℓ' k) →
    par j ℓ = par j ℓ'
  T_local : ∀ a (ℓ ℓ' : K → L) (y y' : R → Bool), (∀ k, (lo k = a ∨ hi k = a) → ℓ k = ℓ' k) →
    (∀ j, holder j = a → y j = y' j) → T a ℓ y = T a ℓ' y'

namespace LabelSystem

variable {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L] (X : LabelSystem g K R L) {w : ℕ} (C : LabelCode L w)

/-- Item `k` is incident to node `a`. -/
abbrev Inc (a : Fin g) (k : K) : Prop := X.lo k = a ∨ X.hi k = a

/-- Item `k` sits on the pair `{a,b}`. -/
abbrev OnPair (a b : Fin g) (k : K) : Prop :=
  (X.lo k = a ∧ X.hi k = b) ∨ (X.lo k = b ∧ X.hi k = a)

/-- Copy bit `j` travels over the pair `{a,b}`. -/
abbrev CopyOn (a b : Fin g) (j : R) : Prop :=
  (X.holder j = a ∧ X.source j = b) ∨ (X.holder j = b ∧ X.source j = a)

/-- Copy bit `j` is held by or computed at `a`. -/
abbrev Touch (a : Fin g) (j : R) : Prop := X.holder j = a ∨ X.source j = a

/-- The items incident to `a`, in the order `kord`. -/
def incList (a : Fin g) : List K := X.kord.filter fun k => decide (X.Inc a k)
/-- The copy bits held by `a`, in the order `rord`. -/
def heldList (a : Fin g) : List R := X.rord.filter fun j => decide (X.holder j = a)
/-- The items on the pair `{a,b}`, in the order `kord`. -/
def pairItems (a b : Fin g) : List K := X.kord.filter fun k => decide (X.OnPair a b k)
/-- The copy bits on the pair `{a,b}`, in the order `rord`. -/
def pairCopies (a b : Fin g) : List R := X.rord.filter fun j => decide (X.CopyOn a b j)

/-- Local states of `a`: labels on the incident items, copy bits held by `a`; default elsewhere. -/
def locSet (a : Fin g) : Finset ((K → L) × (R → Bool)) :=
  univ.filter fun x => (∀ k, ¬ X.Inc a k → x.1 k = X.dflt) ∧ (∀ j, X.holder j ≠ a → x.2 j = false)

/-- The bit string of a local state of `a`. -/
def enc (a : Fin g) (x : (K → L) × (R → Bool)) : List Bool :=
  encL C (X.incList a) x.1 ++ (X.heldList a).map x.2

/-- Decoding a setting of `a` into a local state. -/
def dec (a : Fin g) (z : List Bool) : (K → L) × (R → Bool) :=
  (decL C X.dflt (X.incList a) z, decY (X.heldList a) (z.drop ((X.incList a).length * w)))

/-- The `c a b` shared bits as seen from `a`. -/
def proj (a b : Fin g) (x : (K → L) × (R → Bool)) : List Bool :=
  encL C (X.pairItems a b) x.1 ++
    (X.pairCopies a b).map fun j => if X.holder j = a then x.2 j else X.par j x.1

/-- **The label-sharing network.** -/
def net : Net g where
  len a := (X.incList a).length * w + (X.heldList a).length
  S a := (X.locSet a).image (X.enc C a)
  W a z := X.T a (X.dec C a z).1 (X.dec C a z).2
  Ψ a b z z' := if X.proj C a b (X.dec C a z) = X.proj C b a (X.dec C b z') then 1 else 0
  c a b := (X.pairItems a b).length * w + (X.pairCopies a b).length
  f a b z θ := if X.proj C a b (X.dec C a z) = θ then 1 else 0

/-! #### Basic facts -/

theorem mem_incList {a : Fin g} {k : K} : k ∈ X.incList a ↔ X.Inc a k := by
  simp [incList, X.mem_kord]

theorem mem_heldList {a : Fin g} {j : R} : j ∈ X.heldList a ↔ X.holder j = a := by
  simp [heldList, X.mem_rord]

theorem mem_pairItems {a b : Fin g} {k : K} : k ∈ X.pairItems a b ↔ X.OnPair a b k := by
  simp [pairItems, X.mem_kord]

theorem mem_pairCopies {a b : Fin g} {j : R} : j ∈ X.pairCopies a b ↔ X.CopyOn a b j := by
  simp [pairCopies, X.mem_rord]

theorem pairItems_comm (a b : Fin g) : X.pairItems a b = X.pairItems b a := by
  unfold pairItems
  exact List.filter_congr fun k _ => by simp only [decide_eq_decide]; tauto

theorem pairCopies_comm (a b : Fin g) : X.pairCopies a b = X.pairCopies b a := by
  unfold pairCopies
  exact List.filter_congr fun j _ => by simp only [decide_eq_decide]; tauto

theorem lo_ne_hi (k : K) : X.lo k ≠ X.hi k := (X.lo_lt k).ne

theorem dec_enc {a : Fin g} {x : (K → L) × (R → Bool)} (hx : x ∈ X.locSet a) :
    X.dec C a (X.enc C a x) = x := by
  simp only [locSet, mem_filter, mem_univ, true_and] at hx
  unfold dec enc
  rw [decL_encL C X.dflt x.1 (X.incList a) (X.kord_nodup.filter _), List.drop_left' (length_encL C _ _),
    decY_map x.2 (X.heldList a) (X.rord_nodup.filter _)]
  refine Prod.ext (funext fun k => ?_) (funext fun j => ?_)
  · simp only [mem_incList]
    split_ifs with h
    · rfl
    · exact (hx.1 k h).symm
  · simp only [mem_heldList]
    split_ifs with h
    · rfl
    · exact (hx.2 j h).symm

theorem length_enc (a : Fin g) (x : (K → L) × (R → Bool)) :
    (X.enc C a x).length = (X.net C).len a := by
  simp [enc, net, length_encL]

theorem length_proj (a b : Fin g) (x : (K → L) × (R → Bool)) :
    (X.proj C a b x).length = (X.net C).c a b := by
  simp [proj, net, length_encL]

/-! #### The consistent settings -/

/-- `ℓ` restricted to the items incident to `a`. -/
def restrict (a : Fin g) (ℓ : K → L) : K → L := fun k => if X.Inc a k then ℓ k else X.dflt

/-- The correct copy bits held by `a`. -/
def copyY (a : Fin g) (ℓ : K → L) : R → Bool :=
  fun j => if X.holder j = a then X.par j ℓ else false

/-- The local state of `a` induced by a global labelling `ℓ`. -/
def xOf (ℓ : K → L) (a : Fin g) : (K → L) × (R → Bool) := (X.restrict a ℓ, X.copyY a ℓ)

/-- The setting induced by a global labelling. -/
def zOf (ℓ : K → L) : Fin g → List Bool := fun a => X.enc C a (X.xOf ℓ a)

theorem restrict_of_inc {a : Fin g} {k : K} (ℓ : K → L) (h : X.Inc a k) :
    X.restrict a ℓ k = ℓ k := by
  simp [restrict, h]

theorem par_restrict (j : R) (ℓ : K → L) : X.par j (X.restrict (X.source j) ℓ) = X.par j ℓ :=
  X.par_local j _ _ fun _ hk => X.restrict_of_inc ℓ hk

theorem xOf_mem (ℓ : K → L) (a : Fin g) : X.xOf ℓ a ∈ X.locSet a := by
  simp only [locSet, mem_filter, mem_univ, true_and, xOf, restrict, copyY]
  exact ⟨fun k hk => by simp [hk], fun j hj => by simp [hj]⟩

theorem T_xOf (ℓ : K → L) (a : Fin g) :
    X.T a (X.xOf ℓ a).1 (X.xOf ℓ a).2 = X.T a ℓ fun j => X.par j ℓ :=
  X.T_local a _ _ _ _ (fun k hk => X.restrict_of_inc ℓ hk) fun j hj => by simp [xOf, copyY, hj]

theorem proj_xOf (ℓ : K → L) (a b : Fin g) :
    X.proj C a b (X.xOf ℓ a) =
      encL C (X.pairItems a b) ℓ ++ (X.pairCopies a b).map fun j => X.par j ℓ := by
  unfold proj
  congr 1
  · refine encL_congr C fun k hk => ?_
    rw [mem_pairItems] at hk
    exact X.restrict_of_inc ℓ (by rcases hk with h | h; exacts [Or.inl h.1, Or.inr h.2])
  · refine List.map_congr_left fun j hj => ?_
    rw [mem_pairCopies] at hj
    by_cases h : X.holder j = a
    · simp [xOf, copyY, h]
    · have hs : X.source j = a := by tauto
      simp only [h, if_false, xOf]
      rw [← hs, X.par_restrict]

theorem proj_xOf_symm (ℓ : K → L) (a b : Fin g) :
    X.proj C a b (X.xOf ℓ a) = X.proj C b a (X.xOf ℓ b) := by
  rw [X.proj_xOf, X.proj_xOf, X.pairItems_comm, X.pairCopies_comm]

/-- The global labelling glued from local states (read at the low end of each item). -/
def glue (x : Fin g → (K → L) × (R → Bool)) : K → L := fun k => (x (X.lo k)).1 k

/-- Consistent local states come from their glued labelling. -/
theorem eq_xOf_glue (x : Fin g → (K → L) × (R → Bool)) (hx : ∀ a, x a ∈ X.locSet a)
    (hc : ∀ a b, a ≠ b → X.proj C a b (x a) = X.proj C b a (x b)) :
    x = fun a => X.xOf (X.glue x) a := by
  -- agreement of the two ends of an item, and correctness of the copies
  have hsplit : ∀ a b, a ≠ b →
      encL C (X.pairItems a b) (x a).1 = encL C (X.pairItems a b) (x b).1 ∧
      ((X.pairCopies a b).map fun j => if X.holder j = a then (x a).2 j else X.par j (x a).1) =
        (X.pairCopies a b).map fun j => if X.holder j = b then (x b).2 j else X.par j (x b).1 := by
    intro a b hab
    have h := hc a b hab
    unfold proj at h
    rw [X.pairItems_comm b a, X.pairCopies_comm b a] at h
    exact List.append_inj h (by rw [length_encL, length_encL])
  have F1 : ∀ k, (x (X.lo k)).1 k = (x (X.hi k)).1 k := fun k =>
    encL_inj C (hsplit _ _ (X.lo_ne_hi k)).1 k (X.mem_pairItems.2 (Or.inl ⟨rfl, rfl⟩))
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
    have ha := hx a
    simp only [locSet, mem_filter, mem_univ, true_and] at ha
    by_cases h : X.Inc a k
    · rw [X.restrict_of_inc _ h, G1 a k h]
    · simp only [restrict, h, if_false]; exact ha.1 k h
  funext a
  have ha := hx a
  simp only [locSet, mem_filter, mem_univ, true_and] at ha
  refine Prod.ext (G2 a) ?_
  funext j
  simp only [xOf, copyY]
  by_cases h : X.holder j = a
  · subst h
    rw [if_pos rfl, F2 j, G2 (X.source j), X.par_restrict]
  · rw [if_neg h]; exact ha.2 j h

theorem zOf_injective : Function.Injective (X.zOf C) := by
  intro ℓ ℓ' h
  funext k
  have h1 := congrArg (fun z => (X.dec C (X.lo k) (z (X.lo k))).1 k) h
  simp only [zOf, X.dec_enc C (X.xOf_mem _ _)] at h1
  simpa [xOf, X.restrict_of_inc _ (Or.inl rfl : X.Inc (X.lo k) k)] using h1

/-! #### Theorem 5.3 pattern: the value -/

/-- **The value of the label-sharing network** is the sum over all global labellings of the product
of the node tables, each fed the correct copy bits. -/
theorem value_net : (X.net C).value = ∑ ℓ : K → L, ∏ a, X.T a ℓ fun j => X.par j ℓ := by
  have hsub : univ.image (X.zOf C) ⊆ Fintype.piFinset (X.net C).S := by
    intro z hz
    obtain ⟨ℓ, -, rfl⟩ := mem_image.1 hz
    exact Fintype.mem_piFinset.2 fun a => mem_image.2 ⟨_, X.xOf_mem ℓ a, rfl⟩
  have hzero : ∀ z ∈ Fintype.piFinset (X.net C).S, z ∉ univ.image (X.zOf C) →
      (∏ a, (X.net C).W a (z a)) * ∏ p ∈ pairs (Fin g), (X.net C).Ψ p.1 p.2 (z p.1) (z p.2) = 0 := by
    intro z hz hni
    by_contra hne
    apply hni
    have hS := Fintype.mem_piFinset.1 hz
    have hΨ := right_ne_zero_of_mul hne
    rw [prod_ne_zero_iff] at hΨ
    -- the local states
    choose x hx hxz using fun a => mem_image.1 (hS a)
    have hcp : ∀ p ∈ pairs (Fin g), X.proj C p.1 p.2 (x p.1) = X.proj C p.2 p.1 (x p.2) := by
      intro p hp
      have := hΨ p hp
      simp only [net, ← hxz, X.dec_enc C (hx _)] at this
      by_contra h'
      exact this (if_neg h')
    have hc : ∀ a b, a ≠ b → X.proj C a b (x a) = X.proj C b a (x b) := by
      intro a b hab
      rcases lt_or_gt_of_ne hab with h | h
      · exact hcp (a, b) (by simp [pairs, h])
      · exact (hcp (b, a) (by simp [pairs, h])).symm
    have hxe := X.eq_xOf_glue C x hx hc
    refine mem_image.2 ⟨X.glue x, mem_univ _, ?_⟩
    funext a
    rw [← hxz a, zOf]
    exact congrArg (X.enc C a) (congrFun hxe a).symm
  rw [Net.value, ← sum_subset hsub hzero, sum_image fun ℓ _ ℓ' _ h => X.zOf_injective C h]
  refine sum_congr rfl fun ℓ _ => ?_
  have hW : ∀ a, (X.net C).W a (X.zOf C ℓ a) = X.T a ℓ fun j => X.par j ℓ := by
    intro a
    simp only [net, zOf, X.dec_enc C (X.xOf_mem _ _)]
    exact X.T_xOf ℓ a
  have hΨ : ∀ p ∈ pairs (Fin g), (X.net C).Ψ p.1 p.2 (X.zOf C ℓ p.1) (X.zOf C ℓ p.2) = 1 := by
    intro p _
    simp only [net, zOf, X.dec_enc C (X.xOf_mem _ _)]
    rw [if_pos (X.proj_xOf_symm C ℓ _ _)]
  rw [prod_congr rfl hΨ, prod_const_one, mul_one]
  exact prod_congr rfl fun a _ => hW a

/-! #### Counting: Σ_b c a b, U, and Definition 2 -/

theorem c_eq (a b : Fin g) :
    (X.net C).c a b = #(univ.filter (X.OnPair a b)) * w + #(univ.filter (X.CopyOn a b)) := by
  simp only [net, pairItems, pairCopies,
    length_filter_of_complete _ X.kord_nodup X.mem_kord,
    length_filter_of_complete _ X.rord_nodup X.mem_rord]

theorem len_eq (a : Fin g) :
    (X.net C).len a = #(univ.filter (X.Inc a)) * w + #(univ.filter fun j => X.holder j = a) := by
  simp only [net, incList, heldList,
    length_filter_of_complete _ X.kord_nodup X.mem_kord,
    length_filter_of_complete _ X.rord_nodup X.mem_rord]

theorem sum_card_onPair (a : Fin g) :
    ∑ b ∈ univ.erase a, #(univ.filter (X.OnPair a b)) = #(univ.filter (X.Inc a)) := by
  rw [card_eq_sum_card_fiberwise (f := fun k => if X.lo k = a then X.hi k else X.lo k)
    (t := univ.erase a)]
  · refine sum_congr rfl fun b hb => ?_
    have hb' := (mem_erase.1 hb).1
    congr 1
    ext k
    have := X.lo_ne_hi k
    simp only [mem_filter, mem_univ, true_and]
    grind
  · intro k hk
    replace hk : X.Inc a k := (mem_filter.1 hk).2
    have := X.lo_ne_hi k
    rw [coe_erase, coe_univ]
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    grind

theorem sum_card_copyOn (a : Fin g) :
    ∑ b ∈ univ.erase a, #(univ.filter (X.CopyOn a b)) = #(univ.filter (X.Touch a)) := by
  rw [card_eq_sum_card_fiberwise (f := fun j => if X.holder j = a then X.source j else X.holder j)
    (t := univ.erase a)]
  · refine sum_congr rfl fun b hb => ?_
    have hb' := (mem_erase.1 hb).1
    congr 1
    ext j
    have := X.holder_ne j
    simp only [mem_filter, mem_univ, true_and]
    grind
  · intro j hj
    replace hj : X.Touch a j := (mem_filter.1 hj).2
    have := X.holder_ne j
    rw [coe_erase, coe_univ]
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    grind

/-- The bits on the pairs at `a`: `deg a · w` label bits and one bit per copy touching `a`. -/
theorem sum_c_eq (a : Fin g) :
    ∑ b ∈ univ.erase a, (X.net C).c a b = #(univ.filter (X.Inc a)) * w + #(univ.filter (X.Touch a)) := by
  simp only [c_eq, sum_add_distrib, ← sum_mul, sum_card_onPair, sum_card_copyOn]

theorem len_le_sum_c (a : Fin g) : (X.net C).len a ≤ ∑ b ∈ univ.erase a, (X.net C).c a b := by
  rw [len_eq, sum_c_eq]
  refine Nat.add_le_add_left (card_le_card fun j hj => ?_) _
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact Or.inl hj

theorem sum_card_inc : ∑ a, #(univ.filter (X.Inc a)) = 2 * Fintype.card K := by
  simp only [card_filter]
  rw [sum_comm]
  have : ∀ k : K, (∑ a : Fin g, if X.Inc a k then 1 else 0) = 2 := by
    intro k
    rw [← card_filter]
    have e : univ.filter (fun a => X.Inc a k) = {X.lo k, X.hi k} := by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
    rw [e, card_pair (X.lo_ne_hi k)]
  rw [sum_congr rfl fun k _ => this k, sum_const, card_univ, smul_eq_mul, mul_comm]

theorem sum_card_touch : ∑ a, #(univ.filter (X.Touch a)) = 2 * Fintype.card R := by
  simp only [card_filter]
  rw [sum_comm]
  have : ∀ j : R, (∑ a : Fin g, if X.Touch a j then 1 else 0) = 2 := by
    intro j
    rw [← card_filter]
    have e : univ.filter (fun a => X.Touch a j) = {X.holder j, X.source j} := by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
    rw [e, card_pair (X.holder_ne j)]
  rw [sum_congr rfl fun j _ => this j, sum_const, card_univ, smul_eq_mul, mul_comm]

/-- **The total U**: every item contributes `w` bits and every copy one bit, on both ends. -/
theorem U_eq : (X.net C).U = 2 * (Fintype.card K * w + Fintype.card R) := by
  unfold Net.U
  simp only [sum_c_eq, sum_add_distrib, ← sum_mul, sum_card_inc, sum_card_touch]
  ring

/-- **Definition 2 for the label-sharing network**, with the bound on the shared bits at each node. -/
theorem net_is' {P B : ℕ} (hP1 : 1 ≤ P) (hB : 1 ≤ B)
    (hP : ∀ a, ∑ b ∈ univ.erase a, (X.net C).c a b ≤ P)
    (hT : ∀ a ℓ y, |X.T a ℓ y| < 2 ^ B) : (X.net C).Is P B := by
  have h01 : ∀ p : Prop, [Decidable p] → |(if p then (1 : ℤ) else 0)| < 2 ^ B := by
    intro p _
    have : (1 : ℤ) < 2 ^ B := one_lt_pow₀ (by norm_num) (by omega)
    split_ifs <;> simp [this]
  refine
    { P_pos := hP1
      B_pos := hB
      len_S := ?_
      len_le := fun a => (X.len_le_sum_c C a).trans (hP a)
      Ψ_symm := ?_
      c_symm := ?_
      fact := ?_
      i := hP
      ii_W := fun a z _ => hT a _ _
      ii_Ψ := fun a b _ z _ z' _ => h01 _
      ii_f := fun a b _ z _ θ _ => h01 _ }
  · intro a z hz
    obtain ⟨x, -, rfl⟩ := mem_image.1 hz
    exact X.length_enc C a x
  · intro a b _ z _ z' _
    simp only [net]
    by_cases h : X.proj C a b (X.dec C a z) = X.proj C b a (X.dec C b z')
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro a b
    simp only [net, X.pairItems_comm a b, X.pairCopies_comm a b]
  · intro a b _ z _ z' _
    simp only [net]
    simp_rw [boole_mul]
    have hm : X.proj C a b (X.dec C a z) ∈
        words ((X.pairItems a b).length * w + (X.pairCopies a b).length) :=
      mem_words.2 (X.length_proj C a b _)
    rw [sum_ite_eq, if_pos hm]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl

/-- **Definition 2 for the label-sharing network**: `P` bounds, at every node, the label bits of the
incident items plus the copy bits touching the node. -/
theorem net_is {P B : ℕ} (hP1 : 1 ≤ P) (hB : 1 ≤ B)
    (hP : ∀ a, #(univ.filter (X.Inc a)) * w + #(univ.filter (X.Touch a)) ≤ P)
    (hT : ∀ a ℓ y, |X.T a ℓ y| < 2 ^ B) : (X.net C).Is P B :=
  X.net_is' C hP1 hB (fun a => (X.sum_c_eq C a).trans_le (hP a)) hT

end LabelSystem

end EthFollowup.ExactHC
