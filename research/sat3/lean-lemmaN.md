# Lean formalisation: Lemma N and the star-lemma bookkeeping

File: `research/ports/lean/PortsLean/LemmaN.lean`, imported from `PortsLean.lean`. Lean v4.36.0, Mathlib v4.36.0.
No `sorry`, no new axioms, no `native_decide` (one plain `decide`, on two finsets of `Fin 2`). Every theorem below
prints `[propext, Classical.choice, Quot.sound]` under `#print axioms`. Full `lake build`: completed successfully,
18290 jobs (18288 before; Mathlib not rebuilt).

Sources: `q2-notes.md` §2.2 (Lemma N), §3.3 (star lemma, Theorem T arithmetic); `review-q2.md` item 6 (K ≥ 4).

## (a) Lemma N: proved, in the paper's form

```lean
theorem lemmaN {α : Type*} [PseudoMetricSpace α] (K : ℕ) (hK : 4 ≤ K) (heven : Even K)
    (x : Fin K → α) :
    ∃ A B : Finset (Fin K), Disjoint A B ∧ A ∪ B = univ ∧ A.card = K / 2 ∧ B.card = K / 2 ∧
      ∀ y₀ y₁ : α,
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (x u) (x v)
          ≤ ((K : ℝ) - 1) * (∑ i ∈ A, dist (x i) y₀ + ∑ i ∈ B, dist (x i) y₁)
```

The cut is chosen before y₀, y₁ (∃ A B, ∀ y₀ y₁), as in the paper. Points need not be distinct (`x` is any map,
`PseudoMetricSpace`).

Supporting statements. A cut is `b : Fin K → Bool` with signs `sg b i = if b i then 1 else -1`; balanced means
`∑ i, sg b i = 0`; `cuts K` is the finset of balanced cuts; the same-side indicator is `(1 + sg b u * sg b v)/2`.

```lean
-- deterministic core: EVERY balanced cut, all suppliers (y true = y₀, y false = y₁)
theorem core {α : Type*} [PseudoMetricSpace α] {K : ℕ} (x : Fin K → α) (b : Fin K → Bool)
    (hb : ∑ i, sg b i = 0) (y : Bool → α) :
    ∑ u, ∑ v, (1 + sg b u * sg b v) / 2 * dist (x u) (x v)
      ≤ ((K : ℝ) - 2) * ∑ i, dist (x i) (y (b i))

def M (K : ℕ) (u v : Fin K) : ℝ := ∑ b ∈ cuts K, sg b u * sg b v
lemma M_off {K : ℕ} (hK : 2 ≤ K) {u v : Fin K} (huv : u ≠ v) :
    M K u v = -((cuts K).card : ℝ) / ((K : ℝ) - 1)

-- averaging over all balanced cuts
theorem sum_cuts_same {α : Type*} [PseudoMetricSpace α] {K : ℕ} (hK : 2 ≤ K) (x : Fin K → α) :
    ∑ b ∈ cuts K, ∑ u, ∑ v, (1 + sg b u * sg b v) / 2 * dist (x u) (x v)
      = ((cuts K).card : ℝ) * (((K : ℝ) - 2) / ((K : ℝ) - 1) * ((∑ u, ∑ v, dist (x u) (x v)) / 2))

lemma sum_pairs {α : Type*} [PseudoMetricSpace α] {K : ℕ} (x : Fin K → α) :
    ∑ u, ∑ v, dist (x u) (x v) = 2 * ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (x u) (x v)
```

`core` is the paper's "Σ_same d ≤ (K/2 − 1)·star" on ordered pairs (the ordered sum is twice the unordered one).
The averaging step is done exactly, not by a probability argument: `M_off` (the pair correlation over all balanced
cuts is −#cuts/(K−1) for u ≠ v) follows from the transposition (v w) fixing u (so M u v = M u w) and Σ_v sg b v = 0.
This is the paper's "a pair is on the same side with probability (K/2−1)/(K−1)". Then some balanced cut reaches the
average (`Finset.exists_le_of_sum_le`), and dividing by K − 2 > 0 gives the lemma. Nonemptiness of the set of cuts
uses `Even K`; `K ≥ 4` is used only as K − 2 > 0, so the proof covers exactly the even K ≥ 4 of the corrected statement.

**K = 2 (referee's remark), proved false:**

```lean
theorem lemmaN_false_K2 :
    ¬ ∃ A B : Finset (Fin 2), Disjoint A B ∧ A ∪ B = univ ∧ A.card = 2 / 2 ∧ B.card = 2 / 2 ∧
      ∀ y₀ y₁ : ℝ,
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (![(0 : ℝ), 1] u) (![(0 : ℝ), 1] v)
          ≤ ((2 : ℝ) - 1) * (∑ i ∈ A, dist (![(0 : ℝ), 1] i) y₀
              + ∑ i ∈ B, dist (![(0 : ℝ), 1] i) y₁)
```

(two points of ℝ at distance 1; for either cut put y₀, y₁ on the two points.)

**Divergence from the paper statement:** none in content. Formal choices: indices `Fin K`; "partition into halves"
is `Disjoint A B ∧ A ∪ B = univ ∧ A.card = K/2 ∧ B.card = K/2`; Σ_{u<v} is over the order of `Fin K`.

## (b) Star-lemma bookkeeping and Theorem T arithmetic: proved (arithmetic only)

The tensor statements of the star lemma (row-wise restrictions, (ii)–(iii)) are **not** formalised. Only the bits
counts and the arithmetic of Theorem T's proof are formalised:

```lean
-- (i) per row: 2a bits on each of the K−1 edges = a(K−1) as own-star centre + a as a leaf of each other star
theorem star_row_bits (K a : ℕ) (v : Fin K) :
    ∑ _u ∈ univ.erase v, 2 * a = a * (K - 1) + ∑ _u ∈ univ.erase v, a

-- (iv) hosted bits: q^{h₀} ≤ 2^a ⇒ K·h₀·log₂ q ≤ K·a
theorem star_hosted_bits (K h₀ a : ℕ) (q : ℝ) (hq : 1 ≤ q) (hqa : q ^ h₀ ≤ (2 : ℝ) ^ a) :
    (K : ℝ) * h₀ * Real.logb 2 q ≤ (K : ℝ) * a

-- overhead 2a(K−1)/(K a) = 2(K−1)/K < 2
theorem star_overhead (K a : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ a) :
    (2 * a * ((K : ℝ) - 1)) / ((K : ℝ) * a) = 2 * ((K : ℝ) - 1) / K ∧
      2 * ((K : ℝ) - 1) / K < 2

-- b₀ = ⌈C₀w⌉ ≤ 2C₀w when C₀w ≥ 1
theorem ceil_le_two_mul (t : ℝ) (ht : 1 ≤ t) : (⌈t⌉₊ : ℝ) ≤ 2 * t

-- h = K·h₀, h₀ = ⌊⌊λ/2⌋/b₀⌋ (natural-number division), λ written l
theorem thmT_arith (K l b₀ : ℕ) (w C₀ : ℝ) (hC : 0 < C₀) (hb : 1 ≤ b₀) (hl : 2 * b₀ ≤ l)
    (hw : (b₀ : ℝ) ≤ 2 * C₀ * w) :
    ((K * ((l / 2) / b₀) : ℕ) : ℝ) * K * w ≥ (K : ℝ) ^ 2 * l / (12 * C₀)
```

**Divergences / implicit hypotheses made explicit:**
- The notes' step "w/b₀ ≥ 1/(2C₀)" with b₀ = ⌈C₀w⌉ needs C₀w ≥ 1 (`ceil_le_two_mul`); the notes leave this implicit
  (it holds for K large since w grows with K). `thmT_arith` takes `b₀ ≤ 2C₀w` as a hypothesis.
- "⌊λ/2⌋ ≥ λ/3" needs λ ≥ 2 and "⌊x/b₀⌋ ≥ x/(2b₀)" needs x ≥ b₀; both follow from λ ≥ λ₀(K) = 2b₀, b₀ ≥ 1, which is
  the notes' hypothesis (`hl`, `hb`).
- `star_hosted_bits` needs q ≥ 1 (a tensor side); `star_overhead` needs a ≥ 1, K ≥ 1 (the notes have a ≥ 1, K ≥ 2).
