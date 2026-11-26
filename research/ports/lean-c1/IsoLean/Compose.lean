import IsoLean.Toeplitz
import IsoLean.Isolation

/-!
# Composition: Toeplitz hashing isolates with probability `≥ 3/16` for a good `k`,
and `≥ 3/(16 n)` for `k` uniform in `{2, …, n+1}`.

`succProb n k S` is the probability, over uniform `(a, b) ∈ F₂^{n+k-1} × F₂^k`, that exactly one
`x ∈ S` has `h_{a,b}(x) = 0`.

Edge case: the range `{2, …, n+1}` is empty for `n = 0`, so we assume `1 ≤ n`.
-/

open Finset

namespace IsoLean

/-- For `1 ≤ N ≤ 2^n` (`n ≥ 1`) there is `k ∈ [2, n+1]` with `2^k ≤ 4N` and `2N ≤ 2^k`,
i.e. `2^{k-2} ≤ N ≤ 2^{k-1}`. -/
lemma exists_window (n N : ℕ) (hn : 1 ≤ n) (h1 : 1 ≤ N) (h2 : N ≤ 2 ^ n) :
    ∃ k, 2 ≤ k ∧ k ≤ n + 1 ∧ 2 ^ k ≤ 4 * N ∧ 2 * N ≤ 2 ^ k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · exact ⟨2, le_refl _, le_refl _, by norm_num; omega, by norm_num at h2 ⊢; omega⟩
    · by_cases hN : N ≤ 2 ^ n
      · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih hn' hN
        exact ⟨k, hk1, by omega, hk3, hk4⟩
      · refine ⟨n + 2, by omega, le_refl _, ?_, ?_⟩
        · rw [pow_succ, pow_succ]; omega
        · rw [pow_succ] at h2 ⊢; omega

/-- Success probability of the Toeplitz hash at output length `k`. -/
noncomputable def succProb (n k : ℕ) (S : Finset (Fin n → ZMod 2)) : ℚ :=
  ((univ.filter (fun p => hits (hash n k) S 0 p = 1)).card : ℚ) / (2 ^ (n + k - 1) * 2 ^ k)

lemma succProb_nonneg (n k : ℕ) (S : Finset (Fin n → ZMod 2)) : 0 ≤ succProb n k S := by
  unfold succProb; positivity

/-- The Toeplitz family satisfies the hypotheses of `isolation` at `y₀ = 0`, hence
`3/16 ≤ succProb` whenever `2^k ≤ 4|S| ≤ 3·2^k`. -/
theorem toeplitz_isolation (n k : ℕ) (S : Finset (Fin n → ZMod 2))
    (h1 : 2 ^ k ≤ 4 * S.card) (h2 : 4 * S.card ≤ 3 * 2 ^ k) :
    3 / 16 ≤ succProb n k S := by
  have hY : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by simp
  have hH : Fintype.card ((Fin (n + k - 1) → ZMod 2) × (Fin k → ZMod 2))
      = 2 ^ (n + k - 1) * 2 ^ k := by simp
  have hu : ∀ x, (univ.filter (fun p => hash n k p x = (0 : Fin k → ZMod 2))).card
      * Fintype.card (Fin k → ZMod 2) = Fintype.card ((Fin (n + k - 1) → ZMod 2) × (Fin k → ZMod 2)) := by
    intro x
    have := hash_uniform (F := ZMod 2) n k x 0
    rw [hY, hH]; simpa using this
  have hpw : ∀ x x', x ≠ x' → (univ.filter (fun p => hash n k p x = (0 : Fin k → ZMod 2) ∧ hash n k p x' = 0)).card
      * Fintype.card (Fin k → ZMod 2) ^ 2
        = Fintype.card ((Fin (n + k - 1) → ZMod 2) × (Fin k → ZMod 2)) := by
    intro x x' hxx'
    have := hash_pairwise (F := ZMod 2) n k x x' hxx' 0 0
    rw [hY, hH]; simpa using this
  have hiso := isolation (hash n k) S 0 hu hpw (by rw [hY]; exact h1) (by rw [hY]; exact h2)
  rw [hH] at hiso
  unfold succProb
  rw [le_div_iff₀ (by positivity)]
  have : ((3 * (2 ^ (n + k - 1) * 2 ^ k) : ℕ) : ℚ) ≤
      ((16 * (univ.filter (fun p => hits (hash n k) S 0 p = 1)).card : ℕ) : ℚ) := by
    exact_mod_cast hiso
  push_cast at this
  linarith

/-- **Composition, existence form.** For nonempty `S ⊆ F₂ⁿ` (`n ≥ 1`) some `k ∈ {2, …, n+1}`
gives isolation probability `≥ 3/16`. -/
theorem exists_good_k (n : ℕ) (hn : 1 ≤ n) (S : Finset (Fin n → ZMod 2)) (hS : S.Nonempty) :
    ∃ k ∈ Icc 2 (n + 1), 3 / 16 ≤ succProb n k S := by
  have hcard : S.card ≤ 2 ^ n := by
    have := card_le_univ S
    simpa [Fintype.card_fun] using this
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_window n S.card hn (card_pos.mpr hS) hcard
  exact ⟨k, mem_Icc.mpr ⟨hk1, hk2⟩, toeplitz_isolation n k S hk3 (by omega)⟩

/-- **Composition, averaged form.** With `k` uniform in `{2, …, n+1}` (`n` values) and then
`(a, b)` uniform, the probability of isolating a unique element of `S` is `≥ 3/(16 n)`. -/
theorem avg_succProb (n : ℕ) (hn : 1 ≤ n) (S : Finset (Fin n → ZMod 2)) (hS : S.Nonempty) :
    3 / (16 * n) ≤ (1 / (n : ℚ)) * ∑ k ∈ Icc 2 (n + 1), succProb n k S := by
  obtain ⟨k, hk, hgood⟩ := exists_good_k n hn S hS
  have hsingle : succProb n k S ≤ ∑ k ∈ Icc 2 (n + 1), succProb n k S :=
    single_le_sum (fun j _ => succProb_nonneg n j S) hk
  have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity)]
  have : (1 / (n : ℚ)) * (∑ k ∈ Icc 2 (n + 1), succProb n k S) * (16 * n)
      = 16 * ∑ k ∈ Icc 2 (n + 1), succProb n k S := by
    field_simp
  rw [this]
  linarith

/-- Sanity: the range `{2, …, n+1}` has exactly `n` values, so `1/n` is the uniform weight. -/
lemma card_range_k (n : ℕ) : (Icc 2 (n + 1)).card = n := by
  simp

end IsoLean
