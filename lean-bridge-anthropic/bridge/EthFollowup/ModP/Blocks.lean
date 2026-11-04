/-
# Generic index blocks (module L0 of the ArithNet library)

`scratchpad/plans/modp-plan.md`, ADDENDUM §B ("Index bookkeeping"); interface `modp-interface.md` (L0).

A *layout* is a list `dims : List (List ℕ)`: family `f` is the box `∏ (dims[f])` of coordinate
tuples `xs` (`InBox (dims[f]) xs`, i.e. `xs[i] < dims[f][i]`). The families are laid out one after
another (`off`), each box in mixed radix (`enc`: `x₀ + d₀ (x₁ + d₁ (x₂ + …))`, inverse `dec`).

* mixed radix: `enc`, `dec`, `InBox` (`inBox_cons`, `enc_lt`, `dec_enc`, `enc_dec`, `dec_inBox`,
  `length_dec`, `length_of_inBox`);
* blocks over a list of sizes: `off`, `fam`, `loc` (`fam_off_add`, `loc_off_add`, `off_fam_add_loc`,
  `fam_lt`, `loc_lt`, `off_add_lt`);
* layouts: `Valid dims f xs`, `idx dims f xs`, `total dims`, decoders `fOf dims j`, `cOf dims j`
  with the four round trips `idx_lt`, `fOf_idx`, `cOf_idx`, `idx_fOf_cOf`, `valid_fOf_cOf`.

These replace the nested `if` chains of `Factoring.Params.wireOf/vertOf`.
Pure Mathlib. Standard axioms only.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP.Blocks

/-! ## Mixed radix -/

/-- `xs` lies in the box `ds`: same length, `xs[i] < ds[i]`. -/
def InBox : List ℕ → List ℕ → Prop
  | [], [] => True
  | d :: ds, x :: xs => x < d ∧ InBox ds xs
  | _, _ => False

instance instDecInBox : ∀ ds xs : List ℕ, Decidable (InBox ds xs)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id
  | d :: ds, x :: xs =>
    have := instDecInBox ds xs
    inferInstanceAs (Decidable (x < d ∧ InBox ds xs))

@[simp] theorem inBox_nil : InBox [] [] := trivial
@[simp] theorem inBox_cons {d x : ℕ} {ds xs : List ℕ} : InBox (d :: ds) (x :: xs) ↔ x < d ∧ InBox ds xs :=
  Iff.rfl
@[simp] theorem inBox_nil_cons {x : ℕ} {xs : List ℕ} : ¬ InBox [] (x :: xs) := id
@[simp] theorem inBox_cons_nil {d : ℕ} {ds : List ℕ} : ¬ InBox (d :: ds) [] := id

/-- Mixed-radix encoding `x₀ + d₀ (x₁ + d₁ (…))`. -/
def enc : List ℕ → List ℕ → ℕ
  | d :: ds, x :: xs => x + d * enc ds xs
  | _, _ => 0

/-- Mixed-radix decoding. -/
def dec : List ℕ → ℕ → List ℕ
  | [], _ => []
  | d :: ds, j => j % d :: dec ds (j / d)

@[simp] theorem enc_cons (d x : ℕ) (ds xs : List ℕ) : enc (d :: ds) (x :: xs) = x + d * enc ds xs := rfl
@[simp] theorem enc_nil (xs : List ℕ) : enc [] xs = 0 := by cases xs <;> rfl
@[simp] theorem dec_nil (j : ℕ) : dec [] j = [] := rfl
@[simp] theorem dec_cons (d : ℕ) (ds : List ℕ) (j : ℕ) : dec (d :: ds) j = j % d :: dec ds (j / d) := rfl

theorem length_of_inBox : ∀ {ds xs : List ℕ}, InBox ds xs → xs.length = ds.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, length_of_inBox h.2]

@[simp] theorem length_dec : ∀ (ds : List ℕ) (j : ℕ), (dec ds j).length = ds.length
  | [], _ => rfl
  | _ :: ds, _ => by simp [length_dec ds]

theorem enc_lt : ∀ {ds xs : List ℕ}, InBox ds xs → enc ds xs < ds.prod
  | [], [], _ => by simp
  | d :: ds, x :: xs, h => by
    have ih := enc_lt h.2
    have hx : x < d := h.1
    simp only [enc_cons, List.prod_cons]
    have h1 : x + d * enc ds xs < d * (enc ds xs + 1) := by rw [mul_add, mul_one]; omega
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ ih)

theorem dec_enc : ∀ {ds xs : List ℕ}, InBox ds xs → dec ds (enc ds xs) = xs
  | [], [], _ => rfl
  | d :: ds, x :: xs, h => by
    have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) h.1
    simp only [enc_cons, dec_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.1,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h.1, zero_add, dec_enc h.2]

theorem enc_dec : ∀ {ds : List ℕ} {j : ℕ}, j < ds.prod → enc ds (dec ds j) = j
  | [], j, h => by simp at h; simp [h]
  | d :: ds, j, h => by
    simp only [List.prod_cons] at h
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    have h' : j / d < ds.prod := (Nat.div_lt_iff_lt_mul hd).2 (by rw [mul_comm]; exact h)
    simp only [dec_cons, enc_cons, enc_dec h', Nat.mod_add_div]

theorem dec_inBox : ∀ {ds : List ℕ} {j : ℕ}, j < ds.prod → InBox ds (dec ds j)
  | [], _, _ => trivial
  | d :: ds, j, h => by
    simp only [List.prod_cons] at h
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    have h' : j / d < ds.prod := (Nat.div_lt_iff_lt_mul hd).2 (by rw [mul_comm]; exact h)
    exact ⟨Nat.mod_lt _ hd, dec_inBox h'⟩

/-! ## Blocks over a list of sizes -/

/-- The offset of block `f`: `sz[0] + … + sz[f-1]`. -/
def off : List ℕ → ℕ → ℕ
  | _, 0 => 0
  | [], _ + 1 => 0
  | s :: sz, f + 1 => s + off sz f

/-- The block containing `j` (`sz.length` beyond the end). -/
def fam : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: sz, j => if j < s then 0 else fam sz (j - s) + 1

/-- The position of `j` inside its block. -/
def loc : List ℕ → ℕ → ℕ
  | [], j => j
  | s :: sz, j => if j < s then j else loc sz (j - s)

@[simp] theorem off_zero (sz : List ℕ) : off sz 0 = 0 := by cases sz <;> rfl
@[simp] theorem off_cons_succ (s : ℕ) (sz : List ℕ) (f : ℕ) : off (s :: sz) (f + 1) = s + off sz f := rfl

theorem fam_off_add : ∀ {sz : List ℕ} {f i : ℕ}, i < sz.getD f 0 → fam sz (off sz f + i) = f
  | [], _, _, h => by simp at h
  | s :: sz, 0, i, h => by simp only [List.getD_cons_zero] at h; simp [fam, h]
  | s :: sz, f + 1, i, h => by
    simp only [List.getD_cons_succ] at h
    simp only [off_cons_succ, fam, show ¬ (s + off sz f + i < s) by omega, ↓reduceIte,
      show s + off sz f + i - s = off sz f + i by omega, fam_off_add h]

theorem loc_off_add : ∀ {sz : List ℕ} {f i : ℕ}, i < sz.getD f 0 → loc sz (off sz f + i) = i
  | [], _, _, h => by simp at h
  | s :: sz, 0, i, h => by simp only [List.getD_cons_zero] at h; simp [loc, h]
  | s :: sz, f + 1, i, h => by
    simp only [List.getD_cons_succ] at h
    simp only [off_cons_succ, loc, show ¬ (s + off sz f + i < s) by omega, ↓reduceIte,
      show s + off sz f + i - s = off sz f + i by omega, loc_off_add h]

theorem off_fam_add_loc : ∀ (sz : List ℕ) (j : ℕ), off sz (fam sz j) + loc sz j = j
  | [], j => by simp [fam, loc]
  | s :: sz, j => by
    by_cases h : j < s
    · simp [fam, loc, h]
    · simp only [fam, loc, h, ↓reduceIte, off_cons_succ]
      have := off_fam_add_loc sz (j - s)
      omega

theorem fam_lt : ∀ {sz : List ℕ} {j : ℕ}, j < sz.sum → fam sz j < sz.length
  | [], _, h => by simp at h
  | s :: sz, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < s
    · simp [fam, hj]
    · simp only [fam, hj, ↓reduceIte, List.length_cons]
      have := fam_lt (sz := sz) (j := j - s) (by omega)
      omega

theorem loc_lt : ∀ {sz : List ℕ} {j : ℕ}, j < sz.sum → loc sz j < sz.getD (fam sz j) 0
  | [], _, h => by simp at h
  | s :: sz, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < s
    · simp [fam, loc, hj]
    · simp only [fam, loc, hj, ↓reduceIte, List.getD_cons_succ]
      exact loc_lt (by omega)

theorem off_add_lt : ∀ {sz : List ℕ} {f i : ℕ}, i < sz.getD f 0 → off sz f + i < sz.sum
  | [], _, _, h => by simp at h
  | s :: sz, 0, i, h => by
    simp only [List.getD_cons_zero] at h; simp only [off_zero, List.sum_cons]; omega
  | s :: sz, f + 1, i, h => by
    simp only [List.getD_cons_succ] at h
    simp only [off_cons_succ, List.sum_cons]
    have := off_add_lt h
    omega

/-! ## Layouts -/

/-- The sizes of the families of a layout. -/
def sizes (dims : List (List ℕ)) : List ℕ := dims.map List.prod

/-- The total number of indices of a layout. -/
def total (dims : List (List ℕ)) : ℕ := (sizes dims).sum

/-- `(f, xs)` is a valid element of the layout. -/
def Valid (dims : List (List ℕ)) (f : ℕ) (xs : List ℕ) : Prop :=
  f < dims.length ∧ InBox (dims.getD f []) xs

instance (dims : List (List ℕ)) (f : ℕ) (xs : List ℕ) : Decidable (Valid dims f xs) := by
  unfold Valid; infer_instance

/-- The index of `(f, xs)`. -/
def idx (dims : List (List ℕ)) (f : ℕ) (xs : List ℕ) : ℕ := off (sizes dims) f + enc (dims.getD f []) xs

/-- The family of index `j`. -/
def fOf (dims : List (List ℕ)) (j : ℕ) : ℕ := fam (sizes dims) j

/-- The coordinates of index `j`. -/
def cOf (dims : List (List ℕ)) (j : ℕ) : List ℕ := dec (dims.getD (fOf dims j) []) (loc (sizes dims) j)

theorem sizes_getD {dims : List (List ℕ)} {f : ℕ} (h : f < dims.length) :
    (sizes dims).getD f 0 = (dims.getD f []).prod := by
  simp [sizes, List.getD_eq_getElem?_getD, h]

theorem length_sizes (dims : List (List ℕ)) : (sizes dims).length = dims.length := by simp [sizes]

theorem idx_lt {dims : List (List ℕ)} {f : ℕ} {xs : List ℕ} (h : Valid dims f xs) :
    idx dims f xs < total dims :=
  off_add_lt (by rw [sizes_getD h.1]; exact enc_lt h.2)

theorem fOf_idx {dims : List (List ℕ)} {f : ℕ} {xs : List ℕ} (h : Valid dims f xs) :
    fOf dims (idx dims f xs) = f :=
  fam_off_add (by rw [sizes_getD h.1]; exact enc_lt h.2)

theorem cOf_idx {dims : List (List ℕ)} {f : ℕ} {xs : List ℕ} (h : Valid dims f xs) :
    cOf dims (idx dims f xs) = xs := by
  unfold cOf
  rw [fOf_idx h, idx, loc_off_add (by rw [sizes_getD h.1]; exact enc_lt h.2), dec_enc h.2]

theorem fOf_lt {dims : List (List ℕ)} {j : ℕ} (h : j < total dims) : fOf dims j < dims.length := by
  have := fam_lt (sz := sizes dims) h
  rwa [length_sizes] at this

theorem valid_fOf_cOf {dims : List (List ℕ)} {j : ℕ} (h : j < total dims) :
    Valid dims (fOf dims j) (cOf dims j) := by
  refine ⟨fOf_lt h, dec_inBox ?_⟩
  have := loc_lt (sz := sizes dims) h
  rwa [← fOf, sizes_getD (fOf_lt h)] at this

theorem idx_fOf_cOf {dims : List (List ℕ)} {j : ℕ} (h : j < total dims) :
    idx dims (fOf dims j) (cOf dims j) = j := by
  unfold idx cOf
  have := loc_lt (sz := sizes dims) h
  rw [← fOf, sizes_getD (fOf_lt h)] at this
  rw [enc_dec this, fOf, off_fam_add_loc]

theorem length_cOf (dims : List (List ℕ)) (j : ℕ) :
    (cOf dims j).length = (dims.getD (fOf dims j) []).length := length_dec _ _

/-- The index of `(f, xs)` within its family. -/
theorem idx_eq (dims : List (List ℕ)) (f : ℕ) (xs : List ℕ) :
    idx dims f xs = off (sizes dims) f + enc (dims.getD f []) xs := rfl

end EthFollowup.ModP.Blocks
