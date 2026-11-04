/-
# The lower-bound argument of Anthropic's Section 7 for an arbitrary size function, infinitely often

`CircuitLowerBound.no_linear_circuits` (Anthropic, proof/consequences/CircuitLowerBound/Main.lean)
takes `StAlg` (circuits of ≤ c₀(m+1) gates) and concludes `¬HasLinearCircuits L0`. Here:

* `StAlgS s`: `StAlg` with the circuit-size bound `C.length ≤ s m` for a size function s fixed in
  advance (no quantifier over c₀);
* `no_circuits_io`: from `StAlgS s` and the other interface statements: for every N₀ there is
  n ≥ N₀ such that no circuit with ≤ s(n) gates decides `L0` on the words of length n
  (referee issue 1: the i.o. form; the hypothesis «circuits exist» is used only at lengths of the
  chain, which start beyond N₀).

The proof is that of `no_linear_circuits`, with N₀ threaded into the start of the chain.
-/
import CircuitLowerBound.Main
import CircuitLowerBoundInfinitelyOftenStatement

set_option linter.unusedSectionVars false

namespace EthFollowup.Circuits

open ENP Groundwork Turing CircuitLowerBound

/-- `StAlg` for a fixed size function s. -/
def StAlgS (sz : ℕ → ℕ) : Prop := ∃ N : TM2ComputableAux Bool Bool, (∀ k, Finite (N.tm.Γ k)) ∧
  (∀ m T : ℕ, Acc N m T → Sat (Phi m)) ∧
  ∀ e : MCode, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → codeOf (nu m) = e → pos m ≤ top (nu m) →
    ∀ C : Circuit, C.length ≤ sz m → (∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2) → Acc N m (2 ^ (m / 8))

/-- The language `L0` has no circuits of size s(n) at infinitely many lengths n. -/
theorem no_circuits_io (hTab : StTab) (hCode : StCode) (hChain : StChain) (hV : StVars) (hG : StGreedy)
    {sz : ℕ → ℕ} (hAlg : StAlgS sz) : ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ¬DecidedAt L0 (sz n) n := by
  intro N₀
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  obtain ⟨N, hfin, hsound, hcomp⟩ := hAlg
  obtain ⟨e, he⟩ := hTab N hfin
  obtain ⟨m₀, hm₀⟩ := hcomp e
  obtain ⟨a, ha, hae⟩ := hCode e (m₀ + N₀ + (4 * (kb e + lam e) + 64))
  have h2a : a < 2 ^ a := Nat.lt_two_pow_self
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℕ, ∀ s, p s = 2 ^ a * (2 * s + 1) := ⟨_, fun _ => rfl⟩
  have hnu : ∀ s, nu (p s) = a := fun s => by rw [hp]; exact (hChain a s).1
  have hpos : ∀ s, pos (p s) = s := fun s => by rw [hp]; exact (hChain a s).2
  have hnext : ∀ s, next (p s) = p (s + 1) := fun s => by rw [next, hnu, hp, hp, pow_succ]; ring
  have hbig : ∀ s, 2 ^ a ≤ p s := fun s => by rw [hp]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h3 : ∀ s, p (s + 1) ≤ 3 * p s := fun s => by
    rw [hp, hp]
    have : 0 < 2 ^ a := by positivity
    nlinarith
  have hacc : ∀ s, s ≤ top a → Sat (Phi (p s)) → Acc N (p s) (2 ^ (p s / 8)) := by
    intro s hs hsat
    obtain ⟨C, hlen, hC⟩ := hcon (p s) (by have := hbig s; omega)
    exact hm₀ (p s) (by have := hbig s; omega) (by rw [hnu, hae]) (by rw [hnu, hpos]; exact hs) C hlen
      (sat_by_circuit hG hV hC hsat)
  have hlink : ∀ s, s < top a → (Sat (Phi (p s)) ↔ Sat (Phi (p (s + 1)))) := by
    intro s hs
    obtain ⟨hfit, htime⟩ := room (e := e) (L := p s) (P := p (s + 1)) (by have := hbig s; omega) (h3 s)
    have hPhi : Phi (p s) = tabF e (p s) (p (s + 1)) := by
      unfold Phi
      rw [hnu, hpos, hnext, hae, if_pos hs, if_pos hfit]
    rw [hPhi, he _ _ hfit]
    exact ⟨fun h => hsound _ _ h, fun h => (hacc (s + 1) hs h).mono (Nat.pow_le_pow_right (by norm_num) htime)⟩
  have hall : ∀ s, s ≤ top a → (Sat (Phi (p 0)) ↔ Sat (Phi (p s))) := by
    intro s
    induction s with
    | zero => intro _; exact Iff.rfl
    | succ s ih => intro hs; exact (ih (by omega)).trans (hlink s hs)
  have hp0 : p 0 = 2 ^ a := by rw [hp]; ring
  obtain ⟨hfit, htime⟩ := room (e := e) (L := 2 ^ a) (P := 2 ^ a) (by omega) (by omega)
  have hfirst : Sat (Phi (p 0)) ↔ Sat (tabF e (2 ^ a) (2 ^ a)) := by
    rw [he _ _ hfit]
    constructor
    · intro h
      have := hacc 0 (Nat.zero_le _) h
      rw [hp0] at this
      exact this.mono (Nat.pow_le_pow_right (by norm_num) htime)
    · intro h
      rw [hp0]
      exact hsound _ _ h
  have hlast : Sat (Phi (p (top a))) ↔ ¬Sat (tabF e (2 ^ a) (2 ^ a)) := by
    unfold Phi
    rw [hnu, hpos, hae, if_neg (lt_irrefl _), if_pos rfl]
    by_cases h : Sat (tabF e (2 ^ a) (2 ^ a))
    · rw [if_pos ⟨hfit, h⟩]
      exact ⟨fun h' => absurd h' not_sat_nil_clause, fun h' => absurd h h'⟩
    · rw [if_neg fun h' => h h'.2]
      exact ⟨fun _ => h, fun _ => sat_nil⟩
  have := (hall (top a) le_rfl).trans hlast
  rw [hfirst] at this
  exact (iff_not_self this)

end EthFollowup.Circuits
