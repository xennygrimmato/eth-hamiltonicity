/-
# Reduced binary quadratic forms of negative discriminant (module ClassForms, pure Mathlib)

* `hForm D` (addendum §B, verbatim): the number of triples `(b, a, c) ∈ [-N, N] × [0, N]²`, `N = |D|`,
  with `b² - 4ac = D`, `|b| ≤ a ≤ c` and `b ≥ 0` when `|b| = a` or `a = c` (Gauss/Cox reduced forms
  `a x² + b x y + c y²`). `redForms D` is the same finset (`hForm D = #redForms D`, `rfl`);
  `mem_redForms_iff` (`D < 0`): the box is no restriction.
* The two query counts over the network's box `[0, B)³` (variables `(a, b, c)`):
  `hQ1 B N = #{b² + N = 4ac, b ≤ a, a ≤ c}` (forms with `b ≥ 0`), `hQ2 B N = #{b² + N = 4ac, 0 < b < a < c}`
  (forms with `b < 0`, via `b ↦ -b`). **`hForm_split`**: `hForm (-N) = hQ1 B N + hQ2 B N` for `0 < N < B`.
* `IsFundDisc D` (local definition; Mathlib 0df444a has no `FundamentalDiscriminant`):
  `D ≡ 1 (mod 4)` squarefree, or `D = 4m`, `m ≡ 2, 3 (mod 4)` squarefree.
  `primitive_of_fund`: every form of fundamental discriminant is primitive;
  `hForm_eq_card_primitive`: `hForm D = #{primitive reduced forms of discriminant D}`.

Standard axioms only.
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-! ## The definitions -/

/-- Gauss reduced forms `(b, a, c)` of discriminant `D` (Cox's convention), `N := |D|`. -/
def hForm (D : ℤ) : ℕ :=
  ((Finset.Icc (-(D.natAbs : ℤ)) D.natAbs ×ˢ Finset.Icc 0 (D.natAbs : ℤ) ×ˢ
      Finset.Icc 0 (D.natAbs : ℤ)).filter
    fun t : ℤ × ℤ × ℤ => t.1 * t.1 - 4 * t.2.1 * t.2.2 = D ∧ |t.1| ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
      ((|t.1| = t.2.1 ∨ t.2.1 = t.2.2) → 0 ≤ t.1)).card

/-- The finset counted by `hForm`. -/
def redForms (D : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(D.natAbs : ℤ)) D.natAbs ×ˢ Finset.Icc 0 (D.natAbs : ℤ) ×ˢ
      Finset.Icc 0 (D.natAbs : ℤ)).filter
    fun t : ℤ × ℤ × ℤ => t.1 * t.1 - 4 * t.2.1 * t.2.2 = D ∧ |t.1| ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
      ((|t.1| = t.2.1 ∨ t.2.1 = t.2.2) → 0 ≤ t.1)

theorem hForm_eq_card (D : ℤ) : hForm D = (redForms D).card := rfl

/-- Query 1 (variables `t = (a, b, c)` over `[0, B)³`): `b·b + N = 4·(a·c)`, `b ≤ a`, `a ≤ c`. -/
def hQ1 (B N : ℕ) : ℕ :=
  ((range B ×ˢ range B ×ˢ range B).filter fun t : ℕ × ℕ × ℕ =>
    t.2.1 * t.2.1 + N = 4 * (t.1 * t.2.2) ∧ t.2.1 ≤ t.1 ∧ t.1 ≤ t.2.2).card

/-- Query 2: `b·b + N = 4·(a·c)`, `0 < b`, `b < a`, `a < c` (the forms with `b < 0`, negated). -/
def hQ2 (B N : ℕ) : ℕ :=
  ((range B ×ˢ range B ×ˢ range B).filter fun t : ℕ × ℕ × ℕ =>
    t.2.1 * t.2.1 + N = 4 * (t.1 * t.2.2) ∧ 0 < t.2.1 ∧ t.2.1 < t.1 ∧ t.1 < t.2.2).card

/-! ## Size bounds -/

/-- A reduced form with `b ≥ 0` of discriminant `-N < 0` has `c ≤ N`. -/
theorem form_le {N a b c : ℕ} (hN : 0 < N) (h : b * b + N = 4 * (a * c)) (hba : b ≤ a)
    (hac : a ≤ c) : c ≤ N := by
  have h1 : b * b ≤ a * c := Nat.mul_le_mul hba (hba.trans hac)
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      have : b = 0 := by omega
      subst this
      simp at h; omega
    · exact h0
  have h2 : c ≤ a * c := Nat.le_mul_of_pos_left c ha
  generalize b * b = X at h h1
  generalize a * c = Y at h h1 h2
  omega

/-- Integer form: a reduced form of discriminant `D < 0` lies in the box of `hForm`. -/
theorem form_le_int {D a b c : ℤ} (hD : D < 0) (h : b * b - 4 * a * c = D) (hba : |b| ≤ a)
    (hac : a ≤ c) : 0 ≤ a ∧ c ≤ -D := by
  have ha0 : 0 ≤ a := le_trans (abs_nonneg b) hba
  have ha1 : 1 ≤ a := by
    by_contra hlt
    have ha : a = 0 := by omega
    subst ha
    have hb : b = 0 := abs_nonpos_iff.1 hba
    subst hb
    simp at h; omega
  have hbb : b * b ≤ a * c := by
    have e := abs_mul_abs_self b
    have h1 := mul_le_mul hba hba (abs_nonneg b) ha0
    have h2 := mul_le_mul_of_nonneg_left hac ha0
    linarith
  have hc0 : 0 ≤ c := le_trans ha0 hac
  have hc : c ≤ a * c := by nlinarith [mul_nonneg (sub_nonneg.2 ha1) hc0]
  constructor
  · exact ha0
  · linarith

/-- `D < 0`: membership in `redForms D` is exactly reducedness (the box is no restriction). -/
theorem mem_redForms_iff {D : ℤ} (hD : D < 0) (t : ℤ × ℤ × ℤ) :
    t ∈ redForms D ↔ t.1 * t.1 - 4 * t.2.1 * t.2.2 = D ∧ |t.1| ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
      ((|t.1| = t.2.1 ∨ t.2.1 = t.2.2) → 0 ≤ t.1) := by
  obtain ⟨b, a, c⟩ := t
  simp only [redForms, mem_filter, mem_product, mem_Icc]
  have hN : (D.natAbs : ℤ) = -D := by rw [Int.natCast_natAbs, abs_of_neg hD]
  rw [hN]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨ha0, hc⟩ := form_le_int hD h1 h2 h3
    have := abs_le.1 h2
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨ha0, by linarith⟩, by linarith, hc⟩, h1, h2, h3, h4⟩

/-! ## The split into the two query counts -/

theorem hQ1_eq {N B : ℕ} (hN : 0 < N) (hB : N < B) :
    hQ1 B N = ((redForms (-(N : ℤ))).filter fun t => 0 ≤ t.1).card := by
  have hD : ((-(N : ℤ)).natAbs : ℤ) = N := by simp
  unfold hQ1
  apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => ((t.2.1 : ℤ), (t.1 : ℤ), (t.2.2 : ℤ)))
    (fun t : ℤ × ℤ × ℤ => (t.2.1.toNat, t.1.toNat, t.2.2.toNat))
  · rintro ⟨a, b, c⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq, redForms, mem_filter,
      mem_Icc, hD] at h ⊢
    obtain ⟨-, he, hba, hac⟩ := h
    have hc := form_le hN he hba hac
    have he' : (b : ℤ) * b + N = 4 * (a * c) := by exact_mod_cast he
    refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals first | omega | linarith | exact abs_le.2 ⟨by omega, by omega⟩
  · rintro ⟨b, a, c⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq, redForms, mem_filter,
      mem_Icc, hD] at h ⊢
    obtain ⟨⟨⟨⟨-, hbN⟩, ⟨ha0, haN⟩, hc0, hcN⟩, he, hba, hac, -⟩, hb0⟩ := h
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
    obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hc0
    simp only [Int.toNat_natCast]
    have hba' := (abs_le.1 hba).2
    have he' : ((b * b + N : ℕ) : ℤ) = ((4 * (a * c) : ℕ) : ℤ) := by push_cast; linarith
    exact ⟨⟨by omega, by omega, by omega⟩, by exact_mod_cast he', by omega, by omega⟩
  · rintro ⟨a, b, c⟩ -
    simp
  · rintro ⟨b, a, c⟩ h
    simp only [coe_filter, redForms, mem_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at h
    obtain ⟨⟨⟨-, ⟨ha0, -⟩, hc0, -⟩, -⟩, hb0⟩ := h
    simp [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0, Int.toNat_of_nonneg hc0]

theorem hQ2_eq {N B : ℕ} (hN : 0 < N) (hB : N < B) :
    hQ2 B N = ((redForms (-(N : ℤ))).filter fun t => ¬ 0 ≤ t.1).card := by
  have hD : ((-(N : ℤ)).natAbs : ℤ) = N := by simp
  unfold hQ2
  apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => (-(t.2.1 : ℤ), (t.1 : ℤ), (t.2.2 : ℤ)))
    (fun t : ℤ × ℤ × ℤ => (t.2.1.toNat, (-t.1).toNat, t.2.2.toNat))
  · rintro ⟨a, b, c⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq, redForms, mem_filter,
      mem_Icc, hD] at h ⊢
    obtain ⟨-, he, hb0, hba, hac⟩ := h
    have hc := form_le hN he hba.le hac.le
    have he' : (b : ℤ) * b + N = 4 * (a * c) := by exact_mod_cast he
    have habs : |(-(b : ℤ))| = b := by rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [habs]
    refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals first | omega | linarith
  · rintro ⟨b, a, c⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq, redForms, mem_filter,
      mem_Icc, hD] at h ⊢
    obtain ⟨⟨⟨⟨hbN', -⟩, ⟨ha0, haN⟩, hc0, hcN⟩, he, hba, hac, himp⟩, hb0⟩ := h
    obtain ⟨b', hb'⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 (le_of_lt (not_le.1 hb0)))
    obtain rfl : b = -(b' : ℤ) := by omega
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
    obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hc0
    have habs : |(-(b' : ℤ))| = b' := by rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [habs] at hba himp
    simp only [neg_neg, Int.toNat_natCast]
    have hne1 : (b' : ℤ) ≠ a := fun h => hb0 (himp (Or.inl h))
    have hne2 : (a : ℤ) ≠ c := fun h => hb0 (himp (Or.inr h))
    have he' : ((b' * b' + N : ℕ) : ℤ) = ((4 * (a * c) : ℕ) : ℤ) := by push_cast; linarith
    exact ⟨⟨by omega, by omega, by omega⟩, by exact_mod_cast he', by omega, by omega, by omega⟩
  · rintro ⟨a, b, c⟩ -
    simp
  · rintro ⟨b, a, c⟩ h
    simp only [coe_filter, redForms, mem_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at h
    obtain ⟨⟨⟨-, ⟨ha0, -⟩, hc0, -⟩, -⟩, hb0⟩ := h
    simp [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg (neg_nonneg.2 (le_of_lt (not_le.1 hb0))),
      Int.toNat_of_nonneg hc0]

/-- **The (E) split**: `hForm (-N) = hQ1 B N + hQ2 B N` for `0 < N < B`. -/
theorem hForm_split (N : ℕ) (hN : 0 < N) {B : ℕ} (hB : N < B) :
    hForm (-(N : ℤ)) = hQ1 B N + hQ2 B N := by
  rw [hForm_eq_card, hQ1_eq hN hB, hQ2_eq hN hB, card_filter_add_card_filter_not]

/-! ## Fundamental discriminants and primitivity -/

/-- Fundamental discriminant (local definition). -/
def IsFundDisc (D : ℤ) : Prop :=
  (D % 4 = 1 ∧ Squarefree D) ∨ (D % 4 = 0 ∧ (D / 4 % 4 = 2 ∨ D / 4 % 4 = 3) ∧ Squarefree (D / 4))

theorem not_isUnit_prime {q : ℕ} (hq : q.Prime) : ¬ IsUnit (q : ℤ) := by
  rw [Int.isUnit_iff]
  have := hq.two_le
  omega

/-- No prime divides all three coefficients of a form of fundamental discriminant. -/
theorem prime_not_dvd_of_fund {D a b c : ℤ} (hD : IsFundDisc D) (h : b * b - 4 * a * c = D)
    {q : ℕ} (hq : q.Prime) (ha : (q : ℤ) ∣ a) (hb : (q : ℤ) ∣ b) (hc : (q : ℤ) ∣ c) : False := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨c', rfl⟩ := hc
  have hDq : D = (q : ℤ) * q * (b' * b' - 4 * a' * c') := by rw [← h]; ring
  rcases hD with ⟨-, hsq⟩ | ⟨h4, h23, hsq⟩
  · exact not_isUnit_prime hq (hsq _ ⟨_, hDq⟩)
  · have hD4 : D = 4 * (D / 4) := by omega
    set m := D / 4 with hm
    by_cases h2 : q = 2
    · subst h2
      have hm' : m = b' * b' - 4 * (a' * c') := by push_cast at hDq; linarith
      obtain ⟨k, hk | hk⟩ : ∃ k, b' = 2 * k ∨ b' = 2 * k + 1 := ⟨b' / 2, by omega⟩
      · subst hk
        have : m = 4 * (k * k - a' * c') := by rw [hm']; ring
        omega
      · subst hk
        have : m = 4 * (k * k + k - a' * c') + 1 := by rw [hm']; ring
        omega
    · have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
      have hq4 : ¬ (q : ℤ) ∣ 4 := by
        intro h4'
        have : q ∣ 4 := by exact_mod_cast h4'
        have : q ∣ 2 * 2 := this
        rcases hq.dvd_mul.1 this with h' | h' <;>
          exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')
      have e : 4 * m = (q : ℤ) * (q * (b' * b' - 4 * a' * c')) := by rw [← hD4, hDq]; ring
      have hqm : (q : ℤ) ∣ m := by
        rcases hqZ.dvd_or_dvd ⟨_, e⟩ with h' | h'
        · exact absurd h' hq4
        · exact h'
      obtain ⟨m', hm'⟩ := hqm
      have e2 : 4 * m' = (q : ℤ) * (b' * b' - 4 * a' * c') := by
        have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
        apply mul_left_cancel₀ hq0
        rw [← e, hm']; ring
      have hqm' : (q : ℤ) ∣ m' := by
        rcases hqZ.dvd_or_dvd ⟨_, e2⟩ with h' | h'
        · exact absurd h' hq4
        · exact h'
      obtain ⟨m'', hm''⟩ := hqm'
      exact not_isUnit_prime hq (hsq _ ⟨m'', by rw [hm', hm'']; ring⟩)

/-- **Every form of fundamental discriminant is primitive.** -/
theorem primitive_of_fund {D a b c : ℤ} (hD : IsFundDisc D) (h : b * b - 4 * a * c = D) :
    Int.gcd a (Int.gcd b c) = 1 := by
  by_contra hg
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hg
  have hqg' : (q : ℤ) ∣ (Int.gcd a (Int.gcd b c) : ℤ) := by exact_mod_cast hqg
  have h1 : (q : ℤ) ∣ a := hqg'.trans (Int.gcd_dvd_left _ _)
  have h23 : (q : ℤ) ∣ (Int.gcd b c : ℤ) := hqg'.trans (Int.gcd_dvd_right _ _)
  exact prime_not_dvd_of_fund hD h hq h1 (h23.trans (Int.gcd_dvd_left _ _))
    (h23.trans (Int.gcd_dvd_right _ _))

/-- The primitive reduced forms `(b, a, c)` (`gcd(a, b, c) = 1`) of discriminant `D`. -/
def primRedForms (D : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (redForms D).filter fun t => Int.gcd t.2.1 (Int.gcd t.1 t.2.2) = 1

/-- For a fundamental discriminant, `hForm` counts the primitive reduced forms. -/
theorem hForm_eq_card_primitive {D : ℤ} (hD : IsFundDisc D) (_hneg : D < 0) :
    hForm D = (primRedForms D).card := by
  rw [hForm_eq_card, primRedForms, filter_true_of_mem]
  intro t ht
  simp only [redForms, mem_filter] at ht
  exact primitive_of_fund (a := t.2.1) (b := t.1) (c := t.2.2) hD ht.2.1

/-! ## Sanity checks (addendum values; small `N` by kernel evaluation) -/

example : hForm (-3) = 1 ∧ hForm (-4) = 1 ∧ hForm (-7) = 1 ∧ hForm (-8) = 1 := by decide +kernel
example : hForm (-15) = 2 ∧ hForm (-20) = 2 := by decide +kernel
example : hQ1 16 15 = 2 ∧ hQ2 16 15 = 0 ∧ hQ1 24 23 = 2 ∧ hQ2 24 23 = 1 := by decide +kernel

end EthFollowup.ModP
