/-
# Parity of the number of primes via chain counts (Executor P, step P0; primes-plan.md)

* `chainCount L n` : the number of chains `(d_1, …, d_L)` with `d_1² ∣ n`, `d_{k+1}² ∣ d_k`
  (recursively `C_0 = 1`, `C_{L+1}(n) = Σ_{d ∣ n, d² ∣ n} C_L(d)`).
* `tauLt m` : the number of factorisations `m = a·b` with `a < b` (`= ⌊τ(m)/2⌋`).
* `chainCount_mod_two` (Lemma A): `C_L(n) ≡ [n squarefree] (mod 2)` for `1 ≤ n < 2^{2^L}`.
* `primeParity` (one-count form): `Σ_{m ∈ [A,B]} τ^<(m)·C_L(m) ≡ #{primes in [A,B]} (mod 2)`
  for `B < 2^{2^L}`.
* `primeCounting_eq_card`: `π(x) = #{p ∈ [1,x] prime}`.

Proof of Lemma A: write `n = b²a` with `a` squarefree; `{d : d² ∣ n} = divisors b`; the number
of squarefree divisors of `b` is `≡ Σ_{d ∣ b} μ(d) = [b = 1] = [n squarefree] (mod 2)`.
One-count form: for squarefree `m ≥ 2`, `τ(m) = 2τ^<(m)`; `τ^<(p) = 1`; for squarefree
composite `m = p·q` (coprime) `τ^<(m) = 2τ^<(q)` is even.

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset

/-- Chain count `C_L(n)`. -/
def chainCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | L+1, n => ∑ d ∈ n.divisors.filter (fun d => d * d ∣ n), chainCount L d

/-- `τ^<(m) = #{(a, b) : a·b = m, a < b}`. -/
def tauLt (m : ℕ) : ℕ := ((Nat.divisorsAntidiagonal m).filter fun p => p.1 < p.2).card

/-! ### Lemma A -/

theorem dvd_of_mul_self_dvd {a b d : ℕ} (ha : Squarefree a) (hb : 0 < b)
    (h : d * d ∣ b * b * a) : d ∣ b := by
  have hg : 0 < Nat.gcd d b := Nat.gcd_pos_of_pos_right _ hb
  obtain ⟨g, d', b', hg0, hcop, rfl, rfl⟩ := Nat.exists_coprime' hg
  have h1 : d' * d' * (g * g) ∣ b' * b' * a * (g * g) := by
    have : d' * g * (d' * g) = d' * d' * (g * g) := by ring
    have h2 : b' * g * (b' * g) * a = b' * b' * a * (g * g) := by ring
    rw [← this, ← h2]; exact h
  have h3 : d' * d' ∣ b' * b' * a := Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos hg0 hg0) h1
  have hX : Nat.Coprime d' (b' * b') := Nat.Coprime.mul_right hcop hcop
  have hc : Nat.Coprime (d' * d') (b' * b') := (Nat.Coprime.mul_right hX.symm hX.symm).symm
  have h4 : d' * d' ∣ a := hc.dvd_of_dvd_mul_left h3
  have h5 : d' = 1 := Nat.isUnit_iff.1 (ha d' h4)
  subst h5
  exact ⟨b', by ring⟩

theorem zmod_moebius (d : ℕ) :
    ((ArithmeticFunction.moebius d : ℤ) : ZMod 2) = if Squarefree d then 1 else 0 := by
  by_cases hd : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hd, if_pos hd]
    have : ((-1 : ℤ) : ZMod 2) = 1 := by decide
    push_cast
    rw [show (-1 : ZMod 2) = 1 by decide, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd, if_neg hd]
    simp

theorem card_sqf_divisors_zmod (b : ℕ) :
    ((b.divisors.filter Squarefree).card : ZMod 2) = if b = 1 then 1 else 0 := by
  have hmu := congrArg (fun f => f b) (ArithmeticFunction.moebius_mul_coe_zeta)
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmu
  rw [Finset.natCast_card_filter]
  have : (∑ a ∈ b.divisors, if Squarefree a then (1 : ZMod 2) else 0) =
      ((∑ i ∈ b.divisors, ArithmeticFunction.moebius i : ℤ) : ZMod 2) := by
    push_cast
    exact Finset.sum_congr rfl (fun d _ => (zmod_moebius d).symm)
  rw [this, hmu]
  split_ifs <;> simp

theorem sqDiv_eq {a b : ℕ} (ha : Squarefree a) (hb : 0 < b) (ha0 : 0 < a) :
    (b * b * a).divisors.filter (fun d => d * d ∣ b * b * a) = b.divisors := by
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  have hn : b * b * a ≠ 0 := by positivity
  constructor
  · rintro ⟨_, h⟩
    exact ⟨dvd_of_mul_self_dvd ha hb h, hb.ne'⟩
  · rintro ⟨h, -⟩
    have h2 : d * d ∣ b * b * a := Dvd.dvd.mul_right (Nat.mul_dvd_mul h h) a
    exact ⟨⟨(Dvd.intro_left _ rfl).trans h2 |>.trans (dvd_refl _), hn⟩, h2⟩

theorem key_zmod {n : ℕ} (hn : 1 ≤ n) :
    (((n.divisors.filter (fun d => d * d ∣ n)).filter Squarefree).card : ZMod 2) =
      if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, ha0, hb0, hab, ha⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hn' : n = b * b * a := by rw [← hab, sq]
  subst hn'
  rw [sqDiv_eq ha hb0 ha0, card_sqf_divisors_zmod]
  have : b = 1 ↔ Squarefree (b * b * a) := by
    constructor
    · rintro rfl; simpa using ha
    · intro h
      exact Nat.isUnit_iff.1 (h b (Dvd.intro a rfl))
  by_cases hb : b = 1
  · rw [if_pos hb, if_pos (this.1 hb)]
  · rw [if_neg hb, if_neg (fun h => hb (this.2 h))]

theorem chainCount_zmod {L n : ℕ} (h1 : 1 ≤ n) (h : n < 2 ^ 2 ^ L) :
    (chainCount L n : ZMod 2) = if Squarefree n then 1 else 0 := by
  induction L generalizing n with
  | zero =>
    have : n = 1 := by simp at h; omega
    subst this
    simp [chainCount]
  | succ L ih =>
    simp only [chainCount]
    push_cast
    rw [Finset.sum_congr rfl (g := fun d => if Squarefree d then (1 : ZMod 2) else 0)]
    · rw [Finset.sum_boole]
      exact key_zmod h1
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdn, hn0⟩, hdd⟩ := hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
      apply ih hd1
      by_contra hc'
      have hc := Nat.le_of_not_lt hc'
      have h2 : 2 ^ 2 ^ (L + 1) = 2 ^ 2 ^ L * 2 ^ 2 ^ L := by
        rw [pow_succ, pow_mul, sq]
      have h3 : 2 ^ 2 ^ L * 2 ^ 2 ^ L ≤ d * d := Nat.mul_le_mul hc hc
      have h4 : d * d ≤ n := Nat.le_of_dvd (by omega) hdd
      omega

theorem zmod_two_to_mod {k : ℕ} {P : Prop} [Decidable P] (h : (k : ZMod 2) = if P then 1 else 0) :
    k % 2 = if P then 1 else 0 := by
  split_ifs at h ⊢
  · have := (ZMod.natCast_eq_natCast_iff' k 1 2).1 (by simpa using h); simpa using this
  · have := (ZMod.natCast_eq_natCast_iff' k 0 2).1 (by simpa using h); simpa using this

theorem chainCount_mod_two {L n : ℕ} (h1 : 1 ≤ n) (h : n < 2 ^ 2 ^ L) :
    chainCount L n % 2 = if Squarefree n then 1 else 0 :=
  zmod_two_to_mod (chainCount_zmod h1 h)

/-! ### one-count form -/

theorem card_antidiag (m : ℕ) : (Nat.divisorsAntidiagonal m).card = m.divisors.card := by
  rw [← Nat.map_div_right_divisors, card_map]

theorem card_divisors_eq_two_tauLt {m : ℕ} (hm : Squarefree m) (h2 : 2 ≤ m) :
    m.divisors.card = 2 * tauLt m := by
  rw [← card_antidiag]
  have hsplit := (Finset.card_filter_add_card_filter_not
    (s := Nat.divisorsAntidiagonal m) (fun p => p.1 < p.2))
  have hsplit2 := (Finset.card_filter_add_card_filter_not
    (s := (Nat.divisorsAntidiagonal m).filter (fun p => ¬ p.1 < p.2)) (fun p => p.2 < p.1))
  have hdiag : ((Nat.divisorsAntidiagonal m).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => ¬ p.2 < p.1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨⟨hpm, -⟩, h1⟩, h2'⟩ := hp
    have he : p.1 = p.2 := by omega
    rw [← he] at hpm
    have : p.1 = 1 := Nat.isUnit_iff.1 (hm p.1 ⟨1, by rw [hpm, mul_one]⟩)
    rw [this] at hpm; omega
  have hswap : (((Nat.divisorsAntidiagonal m).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => p.2 < p.1)).card = ((Nat.divisorsAntidiagonal m).filter (fun p => p.1 < p.2)).card := by
    refine Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
    all_goals intro p hp
    all_goals first
      | exact Prod.swap_swap p
      | (rw [mem_filter, mem_filter] at hp; rw [mem_filter, Nat.swap_mem_divisorsAntidiagonal]
         exact ⟨hp.1.1, hp.2⟩)
      | (rw [mem_filter] at hp; rw [mem_filter, mem_filter, Nat.swap_mem_divisorsAntidiagonal]
         exact ⟨⟨hp.1, fun h => lt_asymm hp.2 h⟩, hp.2⟩)
  rw [hdiag, card_empty, add_zero] at hsplit2
  unfold tauLt
  omega

theorem tauLt_prime {p : ℕ} (hp : p.Prime) : tauLt p = 1 := by
  have h := card_divisors_eq_two_tauLt hp.squarefree hp.two_le
  rw [Nat.Prime.divisors hp, card_pair (Ne.symm hp.one_lt.ne')] at h
  omega

theorem tauLt_even {m : ℕ} (hm : Squarefree m) (h2 : 2 ≤ m) (hnp : ¬ m.Prime) :
    2 ∣ tauLt m := by
  set p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨q, hq⟩ : p ∣ m := Nat.minFac_dvd m
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
      · omega
      · rw [mul_one] at hq; exact absurd (hq ▸ hp) hnp
    · exact h
  have hqs : Squarefree q := Squarefree.of_mul_right (hq ▸ hm)
  have hcop : Nat.Coprime p q := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨r, rfl⟩
    have : IsUnit p := hm p ⟨r, by rw [hq]; ring⟩
    exact hp.not_isUnit this
  have e1 := card_divisors_eq_two_tauLt hm h2
  have e2 := card_divisors_eq_two_tauLt hqs hq2
  have e3 : m.divisors.card = 2 * (2 * tauLt q) := by
    rw [hq, Nat.Coprime.card_divisors_mul hcop, Nat.Prime.divisors hp,
      card_pair (Ne.symm hp.one_lt.ne'), e2]
  exact ⟨tauLt q, by omega⟩

theorem term_zmod {L m : ℕ} (h : m < 2 ^ 2 ^ L) :
    ((tauLt m * chainCount L m : ℕ) : ZMod 2) = if m.Prime then 1 else 0 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · simp [tauLt, Nat.not_prime_zero]
    · have h0 : tauLt 1 = 0 := by
        unfold tauLt; rw [Nat.divisorsAntidiagonal_one, Finset.filter_singleton]; simp
      rw [h0, zero_mul, if_neg Nat.not_prime_one]; simp
  · push_cast
    rw [chainCount_zmod (by omega) h]
    by_cases hs : Squarefree m
    · rw [if_pos hs, mul_one]
      by_cases hp : m.Prime
      · rw [if_pos hp, tauLt_prime hp]; simp
      · rw [if_neg hp]
        obtain ⟨k, hk⟩ := tauLt_even hs hm hp
        rw [hk]; push_cast
        rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
    · rw [if_neg hs, mul_zero, if_neg (fun hp => hs hp.squarefree)]

theorem primeParity {L A B : ℕ} (hB : B < 2 ^ 2 ^ L) :
    (∑ m ∈ Finset.Icc A B, tauLt m * chainCount L m) % 2 =
      ((Finset.Icc A B).filter Nat.Prime).card % 2 := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ 2).1
  push_cast [← Nat.cast_mul]
  rw [Finset.sum_congr rfl (g := fun m => if m.Prime then (1 : ZMod 2) else 0)]
  · rw [Finset.sum_boole]
  · intro m hm
    rw [mem_Icc] at hm
    exact_mod_cast term_zmod (L := L) (by omega)

theorem primeCounting_eq_card (x : ℕ) :
    Nat.primeCounting x = ((Finset.Icc 1 x).filter Nat.Prime).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  congr 1
  ext p
  simp only [Nat.primesBelow, mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_lt.le, by omega⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by omega, h2⟩

end EthFollowup.Primes
