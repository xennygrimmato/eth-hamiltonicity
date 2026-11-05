/-
# Padding a counted-network package (module B1 of `scratchpad/repnum-plan.md`)

`scratchpad/repnum-plan.md` §0 D3 and §4 B1. A generic transformer on `CntPackage`s: the input word
`w` is padded by `|w| + c₃` zeros, `padW c₃ w = w ++ 0^{|w|+c₃}` (`|padW c₃ w| = 2|w| + c₃`,
`ofWord (padW c₃ w) = ofWord w`), and the padded package answers `pk.Q (padW c₃ w) π`. Its rounds
are `R' w = |w|` (the query words of length at most `|w|` must be admissible for the padded word:
the hypothesis `hR`), its side condition `Ok' w = pk.Ok (padW c₃ w)`, and all its bounds hold with
the constant `c₀ · padK c₃`, `q' = q (c₃+2)^q`, `qb' = qb (c₃+2)`; the depth term uses
`dg (2L + c₃) ≤ 2^{log₂(c₃+2)+2} · dg L` (`dg_pad`).

* `padW`, `length_padW`, `padW_polyT`, `gofWord_padW`;
* `log_mul_le`, `dg_pad`, `div_mul_le'`, `padK`;
* **`CntPackage.padded`**, `padded_Q`, `padded_R`, `padded_Ok`, `padded_qb`, `padded_q`;
* `GR.answerQ_padded`, **`GR.queryM_TM_padded`** (the rate theorem `GR.queryM_TM` for the padded
  package, with the hypotheses stated on the original package).

Standard axioms only.
-/
import EthFollowup.ModP.CntPackage
import EthFollowup.ModP.GRate

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork EthFollowup.Factoring

/-! ## The padded word -/

/-- **The padded word** `w ++ 0^{|w| + c₃}`. -/
def padW (c₃ : ℕ) (w : List Bool) : List Bool := w ++ (List.range (w.length + c₃)).map fun _ => false

theorem length_padW (c₃ : ℕ) (w : List Bool) : (padW c₃ w).length = 2 * w.length + c₃ := by
  simp only [padW, List.length_append, List.length_map, List.length_range]; omega

theorem padW_polyT (c₃ : ℕ) : PolyT (padW c₃) :=
  PolyT.append PolyT.id' (PolyT.map (f := fun _ _ => false) (PolyT.const false)
    (PolyT.range (Unary.add (Unary.of_length PolyT.id') (Unary.const c₃))))

theorem gofWord_replicate_false (m : ℕ) : Groundwork.ofWord (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ, Groundwork.ofWord, ih]; rfl

theorem gofWord_append_replicate_false (w : List Bool) (m : ℕ) :
    Groundwork.ofWord (w ++ List.replicate m false) = Groundwork.ofWord w := by
  induction w with
  | nil => exact gofWord_replicate_false m
  | cons a w ih => simp only [List.cons_append, Groundwork.ofWord, ih]

theorem gofWord_padW (c₃ : ℕ) (w : List Bool) : Groundwork.ofWord (padW c₃ w) = Groundwork.ofWord w := by
  rw [padW, List.map_const', List.length_range, gofWord_append_replicate_false]

/-! ## The constant adjustment -/

theorem log_mul_le (x y : ℕ) : Nat.log 2 (x * y) ≤ Nat.log 2 x + Nat.log 2 y + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) x
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) y
  have h3 : x * y < 2 ^ (Nat.log 2 x + Nat.log 2 y + 2) := by
    calc x * y < 2 ^ (Nat.log 2 x).succ * 2 ^ (Nat.log 2 y).succ := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (Nat.log 2 x + Nat.log 2 y + 2) := by rw [← pow_add]; congr 1; omega
  have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero hx.ne' hy.ne') h3
  omega

/-- `2L + c₃ + g + 2 ≤ (c₃ + 2)(L + g + 2)`. -/
theorem pad_len_le (L c₃ g : ℕ) : 2 * L + c₃ + g + 2 ≤ (c₃ + 2) * (L + g + 2) := by
  have := Nat.le_mul_of_pos_right c₃ (show 0 < L + g + 2 by omega)
  rw [add_mul]; omega

theorem one_le_dg (L : ℕ) : 1 ≤ dg L := by unfold dg; exact Nat.one_le_two_pow

/-- **The depth term of the padded word.** -/
theorem dg_pad (L c₃ : ℕ) : dg (2 * L + c₃) ≤ 2 ^ (Nat.log 2 (c₃ + 2) + 2) * dg L := by
  have hν : ν (2 * L + c₃) ≤ Nat.log 2 (c₃ + 2) + ν L + 1 := by
    unfold ν
    calc Nat.log 2 (2 * L + c₃ + 2) ≤ Nat.log 2 ((c₃ + 2) * (L + 2)) :=
          Nat.log_mono_right (by have := pad_len_le L c₃ 0; simpa using this)
      _ ≤ Nat.log 2 (c₃ + 2) + Nat.log 2 (L + 2) + 1 := log_mul_le _ _
  unfold dg
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `a y / g ≤ a (y / g) + a`. -/
theorem div_mul_le' (a y g : ℕ) : a * y / g ≤ a * (y / g) + a := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  apply Nat.div_le_of_le_mul
  have h1 := Nat.div_add_mod y g
  have h2 := Nat.mod_lt y hg
  have h3 : a * (y % g) ≤ a * g := Nat.mul_le_mul_left _ h2.le
  calc a * y = a * (g * (y / g) + y % g) := by rw [h1]
    _ = g * (a * (y / g)) + a * (y % g) := by ring
    _ ≤ g * (a * (y / g)) + g * a := by rw [mul_comm g a]; omega
    _ = g * (a * (y / g) + a) := by ring

/-- The constant factor of the padded package. -/
def padK (c₃ : ℕ) : ℕ := (c₃ + 2) * 2 ^ (Nat.log 2 (c₃ + 2) + 2)

theorem le_padK (c₃ : ℕ) : c₃ + 2 ≤ padK c₃ := Nat.le_mul_of_pos_right _ (by positivity)

/-- The rounds-per-length bound of the padded package. -/
theorem pad_P_le (L c₃ g : ℕ) :
    (2 * L + c₃ + 2) / g + dg (2 * L + c₃) ≤ padK c₃ * ((L + 2) / g + dg L) := by
  have h1 : (2 * L + c₃ + 2) / g ≤ (c₃ + 2) * ((L + 2) / g) + (c₃ + 2) :=
    (Nat.div_le_div_right (by have := pad_len_le L c₃ 0; simpa using this)).trans
      (div_mul_le' _ _ _)
  have h2 := dg_pad L c₃
  have h3 := one_le_dg L
  have h4 : 4 ≤ 2 ^ (Nat.log 2 (c₃ + 2) + 2) := by
    rw [pow_add]; have : 1 ≤ 2 ^ Nat.log 2 (c₃ + 2) := Nat.one_le_two_pow; omega
  unfold padK
  generalize (2 * L + c₃ + 2) / g = A at *
  generalize dg (2 * L + c₃) = D' at *
  generalize (L + 2) / g = X at *
  generalize dg L = D at *
  generalize 2 ^ (Nat.log 2 (c₃ + 2) + 2) = E at *
  have ha : 2 ≤ c₃ + 2 := by omega
  generalize c₃ + 2 = a at *
  have h5 : a + E ≤ a * E := by nlinarith
  have h6 : a * X ≤ a * E * X := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have h7 : a + E * D ≤ a * E * D := by
    have : a ≤ a * D := Nat.le_mul_of_pos_right _ (by omega)
    have : (a + E) * D ≤ a * E * D := Nat.mul_le_mul_right _ h5
    nlinarith
  nlinarith

/-- The polynomial bounds of the padded package. -/
theorem pad_poly_le {X : ℕ} (q c₃ L g : ℕ) (h : X ≤ q * (2 * L + c₃ + g + 2) ^ q) :
    X ≤ q * (c₃ + 2) ^ q * (L + g + 2) ^ (q * (c₃ + 2) ^ q) := by
  have hq : q ≤ q * (c₃ + 2) ^ q := Nat.le_mul_of_pos_right _ (by positivity)
  calc X ≤ q * (2 * L + c₃ + g + 2) ^ q := h
    _ ≤ q * ((c₃ + 2) * (L + g + 2)) ^ q :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (pad_len_le L c₃ g) _)
    _ = q * (c₃ + 2) ^ q * (L + g + 2) ^ q := by rw [mul_pow, mul_assoc]
    _ ≤ q * (c₃ + 2) ^ q * (L + g + 2) ^ (q * (c₃ + 2) ^ q) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hq)

/-! ## The padded package -/

namespace CntPackage

/-- **The padded package**: `Q' w π = pk.Q (padW c₃ w) π`, `R' w = |w|`, `Ok' w = pk.Ok (padW c₃ w)`;
the networks, procedures and reader are those of `pk` on the padded word. -/
def padded {c₀ : ℕ} (pk : CntPackage c₀) (c₃ : ℕ) (hR : ∀ w, w.length ≤ pk.R (padW c₃ w)) :
    CntPackage (c₀ * padK c₃) where
  Ctx := pk.Ctx
  Np := pk.Np
  keeps := pk.keeps
  P_unary := pk.P_unary
  B_unary := pk.B_unary
  prep y := pk.prep (y.1, (padW c₃ y.2.1, y.2.2))
  prep_poly := PolyT.comp pk.prep_poly (PolyT.prodMk (PolyT.fst PolyT.id')
    (PolyT.prodMk ((padW_polyT c₃).comp (PolyT.fst (PolyT.snd PolyT.id'))) (PolyT.snd (PolyT.snd PolyT.id'))))
  q := pk.q * (c₃ + 2) ^ pk.q
  Q w π := pk.Q (padW c₃ w) π
  R w := w.length
  R_le _ := le_rfl
  R_poly := (Unary.of_length PolyT.id').poly
  qb := pk.qb * (c₃ + 2)
  Ok w := pk.Ok (padW c₃ w)
  Q_lt w π hOk hπ := by
    have h := pk.Q_lt (padW c₃ w) π hOk (hπ.trans (hR w))
    rw [length_padW] at h
    refine h.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by simpa using pad_len_le w.length c₃ 0)
  net g w π := pk.net g (padW c₃ w) π
  P g w π := pk.P g (padW c₃ w) π
  B g w π := pk.B g (padW c₃ w) π
  τ g w π := pk.τ g (padW c₃ w) π
  S g w π := pk.S g (padW c₃ w) π
  isNet g w π hg hOk hπ := pk.isNet g (padW c₃ w) π hg hOk (hπ.trans (hR w))
  value g w π hg hOk hπ := pk.value g (padW c₃ w) π hg hOk (hπ.trans (hR w))
  U_le g w π hg hOk hπ := by
    have h := pk.U_le g (padW c₃ w) π hg hOk (hπ.trans (hR w))
    rw [length_padW] at h
    refine h.trans ?_
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ((by simpa using pad_len_le w.length c₃ 0 :
      2 * w.length + c₃ + 2 ≤ (c₃ + 2) * (w.length + 2)).trans ?_)
    exact Nat.mul_le_mul_right _ (le_padK c₃)
  P_le g w π hg hOk hπ := by
    have h := pk.P_le g (padW c₃ w) π hg hOk (hπ.trans (hR w))
    rw [length_padW] at h
    refine h.trans ?_
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (pad_P_le w.length c₃ g)
  B_le g w π hg hOk hπ := by
    have h := pk.B_le g (padW c₃ w) π hg hOk (hπ.trans (hR w))
    rw [length_padW] at h
    exact pad_poly_le pk.q c₃ w.length g h
  τ_le g w π hg hOk hπ := by
    have h := pk.τ_le g (padW c₃ w) π hg hOk (hπ.trans (hR w))
    rw [length_padW] at h
    exact pad_poly_le pk.q c₃ w.length g h
  S_le g w π hg hOk hπ := by
    have h := pk.S_le g (padW c₃ w) π hg hOk (hπ.trans (hR w))
    rw [length_padW] at h
    exact pad_poly_le pk.q c₃ w.length g h

variable {c₀ : ℕ} (pk : CntPackage c₀) (c₃ : ℕ) (hR : ∀ w, w.length ≤ pk.R (padW c₃ w))

theorem padded_Q (w π : List Bool) : (pk.padded c₃ hR).Q w π = pk.Q (padW c₃ w) π := rfl
theorem padded_R (w : List Bool) : (pk.padded c₃ hR).R w = w.length := rfl
theorem padded_Ok (w : List Bool) : (pk.padded c₃ hR).Ok w = pk.Ok (padW c₃ w) := rfl
theorem padded_qb : (pk.padded c₃ hR).qb = pk.qb * (c₃ + 2) := rfl
theorem padded_q : (pk.padded c₃ hR).q = pk.q * (c₃ + 2) ^ pk.q := rfl

end CntPackage

/-! ## The rate theorem for the padded package -/

namespace GR

variable {c₀ : ℕ} (pk : CntPackage c₀) (c₃ : ℕ) (hR : ∀ w, w.length ≤ pk.R (padW c₃ w))
  (qs : QuerySpec)

theorem answerQ_padded (w : List Bool) : answerQ (pk.padded c₃ hR) qs w =
    if qs.pre w then qs.small w else qs.fin (w, pk.Q (padW c₃ w) (qs.q1 w), pk.Q (padW c₃ w) (qs.q2 w)) :=
  rfl

/-- **`GR.queryM_TM` for the padded package**: the queries of `qs` are answered by `pk` on the
padded word `padW c₃ w`; the side condition is `pk.Ok (padW c₃ w)`, and the queries must have
length at most `|w|`. -/
theorem queryM_TM_padded (hpre : PolyT qs.pre) (hsmall : PolyT qs.small) (hq1p : PolyT qs.q1)
    (hq2p : PolyT qs.q2) (hfin : PolyT qs.fin) {ob : ℕ}
    (hlen : ∀ w, (answerQ (pk.padded c₃ hR) qs w).length ≤ ob * (w.length + 2))
    (hOk : ∀ w, qs.pre w = false → pk.Ok (padW c₃ w))
    (hq1 : ∀ w, qs.pre w = false → (qs.q1 w).length ≤ w.length)
    (hq2 : ∀ w, qs.pre w = false → (qs.q2 w).length ≤ w.length) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ w : List Bool, GraphProblems.Outputs M w (answerQ (pk.padded c₃ hR) qs w)
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * w.length / Real.sqrt (Real.logb 2 (w.length + 2)))⌋₊ :=
  queryM_TM (pk.padded c₃ hR) qs hpre hsmall hq1p hq2p hfin hlen hOk hq1 hq2

end GR

end EthFollowup.ModP
