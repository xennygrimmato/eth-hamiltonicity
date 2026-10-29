/-
# The spread lemma (`research/permanent/rho-lower-bound.md` Theorem 3.3)

Source (`rho-lower-bound.md` §3.1–3.2): for a two-order piece on a graded space with
`D(E) = dim V_E`, `f(E) = log₂ D(E)`, terms `j ∈ T` of degrees `r_j`, the certified costs are
"c^row := ⌈log₂ R^row⌉, c^col := ⌈log₂ R^col⌉" with "R^row := Σ_{j∈T} D(h+r_j)" and
"R^col := Σ_{j∈T} D(h−r_j)" (Lemma 3.2; Theorem B uses `Nat.clog 2 (Rrow h s)`).

> **Theorem 3.3.** For a two-order piece with degrees r_j, j ∈ T, put
> r_max := max{r_j : D(h+r_j) > 0} and r_min := min{r_j : D(h−r_j) > 0}. Then
>
>     c^row + c^col ≥ f(h + r_max) + f(h − r_min).                                  (3.1)
>
> For the slices of a locality identity of order H with degrees r_i = s − h_0 + i, i = 0..H …,
> the slice s satisfies, whenever both weights are ≥ 0,
>
>     c^row_s + c^col_s ≥ f(h − h_0 + s + H) + f(h + h_0 − s),                       (3.2)
>
> in particular for h_0 = h, H = 2h and |s| ≤ 2h:  c^row_s + c^col_s ≥ f(2h+s) + f(2h−s), and
> c^row_0 + c^col_0 ≥ 2 f(2h).
>
> *Proof.* log₂ Σ_j D(h+r_j) ≥ max_j f(h+r_j) ≥ f(h+r_max), same for the columns. ∎

## What is proved (abstract form)

Only the numbers `D : ℤ → ℕ` (dimensions), `h`, the finite term set `T` and the degrees `r` enter;
the operators and the two-order identity are not used by the proof and are not modelled. We use
`f(E) = Real.logb 2 (D E)` (so `f(E) = 0` when `D(E) = 0`, where the source has `−∞`; this only
weakens nothing, since then the source inequality is vacuous).

* `logb_le_clog_sum` — `f(h + r_j) ≤ ⌈log₂ R^row⌉` for **every** `j ∈ T`;
* `spread_any` — `c^row + c^col ≥ f(h + r_{j₁}) + f(h − r_{j₂})` for all `j₁, j₂ ∈ T`;
* `spread_lemma` — (3.1) with `r_max`, `r_min` defined as in the source (`Finset.max'`/`min'`);
* `spread_slice` — (3.2), with no sign hypothesis needed;
* `spread_slice_symm`, `spread_slice_zero` — the two specialisations.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.Spread

open Finset

/-- `log₂ x ≤ ⌈log₂ N⌉` whenever `x ≤ N` (natural numbers). -/
theorem logb_le_clog {x N : ℕ} (h : x ≤ N) : Real.logb 2 x ≤ Nat.clog 2 N := by
  rcases Nat.eq_zero_or_pos x with h0 | hpos
  · simp [h0]
  · have h1 : (x : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 N := by
      exact_mod_cast h.trans (Nat.le_pow_clog (by norm_num) N)
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hpos) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this

variable {τ : Type*} (D : ℤ → ℕ) (h : ℤ) (T : Finset τ) (r : τ → ℤ)

/-- `R^row = Σ_{j∈T} D(h + r_j)`. -/
def Rrow : ℕ := ∑ j ∈ T, D (h + r j)

/-- `R^col = Σ_{j∈T} D(h − r_j)`. -/
def Rcol : ℕ := ∑ j ∈ T, D (h - r j)

theorem logb_le_clog_sum {j : τ} (hj : j ∈ T) :
    Real.logb 2 (D (h + r j)) ≤ Nat.clog 2 (Rrow D h T r) :=
  logb_le_clog (Finset.single_le_sum (f := fun j => D (h + r j)) (fun _ _ => Nat.zero_le _) hj)

theorem logb_le_clog_sum_col {j : τ} (hj : j ∈ T) :
    Real.logb 2 (D (h - r j)) ≤ Nat.clog 2 (Rcol D h T r) :=
  logb_le_clog (Finset.single_le_sum (f := fun j => D (h - r j)) (fun _ _ => Nat.zero_le _) hj)

/-- The spread bound for any pair of terms. -/
theorem spread_any {j₁ j₂ : τ} (h₁ : j₁ ∈ T) (h₂ : j₂ ∈ T) :
    Real.logb 2 (D (h + r j₁)) + Real.logb 2 (D (h - r j₂)) ≤
      (Nat.clog 2 (Rrow D h T r) : ℝ) + Nat.clog 2 (Rcol D h T r) :=
  add_le_add (logb_le_clog_sum D h T r h₁) (logb_le_clog_sum_col D h T r h₂)

/-- **`rho-lower-bound.md` Theorem 3.3, (3.1)**, with `r_max := max{r_j : D(h+r_j) > 0}` and
`r_min := min{r_j : D(h−r_j) > 0}` (both sets assumed nonempty, as the source's max/min need). -/
theorem spread_lemma
    (hrow : ((T.filter fun j => 0 < D (h + r j)).image r).Nonempty)
    (hcol : ((T.filter fun j => 0 < D (h - r j)).image r).Nonempty) :
    Real.logb 2 (D (h + ((T.filter fun j => 0 < D (h + r j)).image r).max' hrow)) +
      Real.logb 2 (D (h - ((T.filter fun j => 0 < D (h - r j)).image r).min' hcol)) ≤
      (Nat.clog 2 (Rrow D h T r) : ℝ) + Nat.clog 2 (Rcol D h T r) := by
  obtain ⟨j₁, hj₁, e₁⟩ := Finset.mem_image.1 (Finset.max'_mem _ hrow)
  obtain ⟨j₂, hj₂, e₂⟩ := Finset.mem_image.1 (Finset.min'_mem _ hcol)
  rw [← e₁, ← e₂]
  exact spread_any D h T r (Finset.mem_filter.1 hj₁).1 (Finset.mem_filter.1 hj₂).1

/-- **(3.2)**: the slice `s` of a locality identity of order `H`, degrees `r_i = s − h₀ + i`
(`i = 0..H`), satisfies `c^row_s + c^col_s ≥ f(h − h₀ + s + H) + f(h + h₀ − s)`. -/
theorem spread_slice (h₀ s : ℤ) (H : ℕ) :
    Real.logb 2 (D (h - h₀ + s + H)) + Real.logb 2 (D (h + h₀ - s)) ≤
      (Nat.clog 2 (Rrow D h (range (H + 1)) (fun i => s - h₀ + i)) : ℝ) +
        Nat.clog 2 (Rcol D h (range (H + 1)) (fun i => s - h₀ + i)) := by
  have := spread_any D h (range (H + 1)) (fun i : ℕ => s - h₀ + i)
    (j₁ := H) (j₂ := 0) (by simp) (by simp)
  have e1 : h + (s - h₀ + (H : ℤ)) = h - h₀ + s + H := by ring
  have e2 : h - (s - h₀ + ((0 : ℕ) : ℤ)) = h + h₀ - s := by push_cast; ring
  rw [e1, e2] at this
  exact this

/-- (3.2) with `h₀ = h`, `H = 2h`: `c^row_s + c^col_s ≥ f(2h + s) + f(2h − s)`. -/
theorem spread_slice_symm (hn : ℕ) (s : ℤ) :
    Real.logb 2 (D (2 * hn + s)) + Real.logb 2 (D (2 * hn - s)) ≤
      (Nat.clog 2 (Rrow D hn (range (2 * hn + 1)) (fun i => s - hn + i)) : ℝ) +
        Nat.clog 2 (Rcol D hn (range (2 * hn + 1)) (fun i => s - hn + i)) := by
  have := spread_slice D hn hn s (2 * hn)
  have e1 : (hn : ℤ) - hn + s + ((2 * hn : ℕ) : ℤ) = 2 * hn + s := by push_cast; ring
  have e2 : (hn : ℤ) + hn - s = 2 * hn - s := by ring
  rw [e1, e2] at this
  exact this

/-- The slice `s = 0`: `c^row_0 + c^col_0 ≥ 2 f(2h)`. -/
theorem spread_slice_zero (hn : ℕ) :
    2 * Real.logb 2 (D (2 * hn)) ≤
      (Nat.clog 2 (Rrow D hn (range (2 * hn + 1)) (fun i => 0 - hn + i)) : ℝ) +
        Nat.clog 2 (Rcol D hn (range (2 * hn + 1)) (fun i => 0 - hn + i)) := by
  have := spread_slice_symm D hn 0
  simp only [add_zero, sub_zero] at this
  linarith

end EthFollowup.Barriers.Spread
