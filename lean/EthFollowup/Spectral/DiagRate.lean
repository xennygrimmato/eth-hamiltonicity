/-
Exploratory file (`research/next/v2`).  Not imported by the root module and not a claimed result.

The price per bit of a label shared by a finite set of sites, as a set function.  The axioms are the ones
OpenAI's `Euclidean geometry in the asymptotic spectrum of tensors` (24 Nov 2026) proves in every spectral
space: a single site is free, more sites cost more, and the rate is submodular on intersecting sets
(Proposition "Copying a common label").  From them: the spanning-tree bound, and the window for three sites
at the tips of a tripod once the matrix multiplication exponent `9/4` is used as an input.
-/
import Mathlib

namespace EthFollowup.Spectral

/-- Shared-label rates on finite sets of sites. -/
structure DiagRate (S : Type*) [DecidableEq S] where
  δ : Finset S → ℝ
  single : ∀ a, δ {a} = 0
  mono : ∀ {A B : Finset S}, A.Nonempty → A ⊆ B → δ A ≤ δ B
  submod : ∀ {A B : Finset S}, (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B

namespace DiagRate

variable {S : Type*} [DecidableEq S] (R : DiagRate S)

theorem nonneg {A : Finset S} (hA : A.Nonempty) : 0 ≤ R.δ A := by
  obtain ⟨a, ha⟩ := hA
  have h := R.mono (A := {a}) (B := A) (Finset.singleton_nonempty a) (by simpa using ha)
  rw [R.single] at h; exact h

/-- Gluing two sets along a common site costs at most the sum. -/
theorem union_le {A B : Finset S} (h : (A ∩ B).Nonempty) : R.δ (A ∪ B) ≤ R.δ A + R.δ B := by
  have h1 := R.submod h
  have h2 := R.nonneg h
  linarith

/-- Two wires sharing an end supply a three-site label. -/
theorem triple_le (a b c : S) : R.δ {a, b, c} ≤ R.δ {a, b} + R.δ {b, c} := by
  have hU : ({a, b} : Finset S) ∪ {b, c} = {a, b, c} := by
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hI : (({a, b} : Finset S) ∩ {b, c}).Nonempty := ⟨b, by simp⟩
  have := R.union_le hI
  rwa [hU] at this

/-- Steiner bound through a centre `o`. -/
theorem steiner (a b c o : S) : R.δ {a, b, c} ≤ R.δ {a, o} + R.δ {b, o} + R.δ {c, o} := by
  have h1 : R.δ {a, o, b} ≤ R.δ {a, o} + R.δ {o, b} := R.triple_le a o b
  have hU : ({a, o, b} : Finset S) ∪ {o, c} = {a, b, c, o} := by
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hI : (({a, o, b} : Finset S) ∩ {o, c}).Nonempty := ⟨o, by simp⟩
  have h2 := R.union_le hI
  rw [hU] at h2
  have hsub : ({a, b, c} : Finset S) ⊆ {a, b, c, o} := by
    intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h3 := R.mono (A := {a, b, c}) (B := {a, b, c, o}) ⟨a, by simp⟩ hsub
  have hob : R.δ {o, b} = R.δ {b, o} := by rw [Finset.pair_comm]
  have hoc : R.δ {o, c} = R.δ {c, o} := by rw [Finset.pair_comm]
  linarith

/-- **Tripod window.**  Three tips at distance 1 from a centre and 2 from each other.  The spanning-tree bound
gives rate at most 3.  If the perimeter of every triangle is at most `9/4` times its shared-label rate (the
price form of `ω ≤ 9/4`), the rate is at least `8/3`. -/
theorem tripod_window (a b c o : S)
    (hao : R.δ {a, o} = 1) (hbo : R.δ {b, o} = 1) (hco : R.δ {c, o} = 1)
    (hab : R.δ {a, b} = 2) (hbc : R.δ {b, c} = 2) (hac : R.δ {a, c} = 2)
    (hω : R.δ {a, b} + R.δ {b, c} + R.δ {a, c} ≤ 9 / 4 * R.δ {a, b, c}) :
    8 / 3 ≤ R.δ {a, b, c} ∧ R.δ {a, b, c} ≤ 3 := by
  have h := R.steiner a b c o
  constructor <;> linarith

end DiagRate

end EthFollowup.Spectral
