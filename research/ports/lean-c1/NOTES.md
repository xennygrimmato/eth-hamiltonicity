# lean-c1: isolation lemmas behind C1 (c1d1/notes.md §C1.2, specs S1/S2)

Toolchain: Lean v4.36.0 and Mathlib v4.36.0, the same manifest as `../lean` (package renamed to `IsoLean`).
Build: `lake build`. It completes with no errors, no `sorry`, no `axiom` and no `native_decide`.

Files:
- `IsoLean/Toeplitz.lean`
- `IsoLean/Isolation.lean`
- `IsoLean/Compose.lean`
- `IsoLean/Tseitin.lean`

All theorems are in namespace `IsoLean`.

## Target 1: Toeplitz hash is pairwise independent (PROVED)

The indexing is the notes' indexing (C1.2): `(T_a)_{j,i} = a_{n-1+j-i}`, with `a : Fin (n+k-1) → F`.

```lean
def tIdx (n k : ℕ) (j : Fin k) (i : Fin n) : Fin (n + k - 1) := ⟨n - 1 - i + j, _⟩
def toeplitzMul (n k) (a : Fin (n + k - 1) → F) (z : Fin n → F) : Fin k → F :=
  fun j => ∑ i, a (tIdx n k j i) * z i
def hash (n k) (p : (Fin (n + k - 1) → F) × (Fin k → F)) (x : Fin n → F) := toeplitzMul n k p.1 x + p.2

theorem toeplitz_surjective (n k) (z : Fin n → F) (hz : z ≠ 0) :
    Function.Surjective (toeplitzLin (F := F) n k z)          -- any field F
theorem toeplitz_fiber_card [Fintype F] ... (hz : z ≠ 0) (s) :
    #{a | toeplitzMul n k a z = s} * q ^ k = q ^ (n + k - 1)  -- q = |F|
theorem hash_uniform ... : #{p | hash n k p x = s} * q^k = q^(n+k-1) * q^k
theorem hash_pairwise ... (hxy : x ≠ y) (s t) :
    #{p | hash n k p x = s ∧ hash n k p y = t} * (q ^ k) ^ 2 = q ^ (n + k - 1) * q ^ k
theorem hash_pairwise_F2 (n k) (x y : Fin n → ZMod 2) (hxy : x ≠ y) (s t) :
    #{p | hash n k p x = s ∧ hash n k p y = t} * 4 ^ k = 2 ^ ((n + k - 1) + k)
theorem hash_pairwise_F2' ... : #{p | hash n k p x = s ∧ hash n k p y = t} = 2 ^ (n - 1)
```

**How surjectivity is proved.** It is the triangular argument in dual form.

1. If the range is proper, there is a nonzero functional `w` with `∑_j w_j (T_a z)_j = 0` for every `a`.
2. Apply this with `a = e_l`.
3. Take `j*`, the largest index with `w_{j*} ≠ 0`, and `i*`, the smallest index with `z_{i*} ≠ 0`.
4. The equation for `l = n-1-i*+j*` keeps only the term `w_{j*} z_{i*} ≠ 0`, which is a contradiction.

The lemma holds over any field. The notes' statement and indexing are correct. With `a` of length `n+k-1`, the statement is true for all `n, k`.

## Target 2: Isolation bound (PROVED, constant 3/16 on a wider window)

Setting: a general finite family `h : H → X → Y` with counting measure, `M = |Y|` and `N = |S|`. The hypotheses are needed only at `y₀`:

```lean
(hu  : ∀ x, #{p | h p x = y0} * M = |H|)
(hpw : ∀ x x', x ≠ x' → #{p | h p x = y0 ∧ h p x' = y0} * M ^ 2 = |H|)
```

```lean
theorem isolation_exact : (|H| : ℤ) * (N*M - N^2 + N) ≤ M^2 * #{p | hits h S y0 p = 1}
theorem isolation (h1 : M ≤ 4 * N) (h2 : 4 * N ≤ 3 * M) :
    3 * |H| ≤ 16 * #{p | hits h S y0 p = 1}
theorem isolation_notes_window (h1 : M ≤ 4 * N) (h2 : 2 * N ≤ M) : same conclusion
```

Here `hits h S y0 p = #{x ∈ S | h p x = y0}`.

The proof uses the pointwise inequality `[c = 1] ≥ 2c − c²`, which is the Bonferroni bound `Σ Pr[h(x)=y₀] − Σ_{x≠x'} Pr[both]`. It then computes the first and second moments exactly, and uses `16(NM − N²) − 3M² = (4N − M)(3M − 4N) ≥ 0`.

Remarks:
- The notes' C3 (window `2^{k-2} ≤ N ≤ 2^{k-1}`, constant 3/16) is **true**. The same constant holds on the larger window `M/4 ≤ N ≤ 3M/4`, and 3/16 is attained at the two ends, `q = 1/4` and `q = 3/4`.
- The 1/8 constant requested by the task is implied.
- The uniform-marginal hypothesis `hu` must be assumed separately. It follows from `hpw` only when a second point exists, and it is needed when `|S| = 1`.

## Target 3: Composition (PROVED)

```lean
lemma exists_window (n N) (hn : 1 ≤ n) (h1 : 1 ≤ N) (h2 : N ≤ 2 ^ n) :
    ∃ k, 2 ≤ k ∧ k ≤ n + 1 ∧ 2 ^ k ≤ 4 * N ∧ 2 * N ≤ 2 ^ k
noncomputable def succProb (n k) (S : Finset (Fin n → ZMod 2)) : ℚ :=
  #{p | hits (hash n k) S 0 p = 1} / (2 ^ (n + k - 1) * 2 ^ k)
theorem toeplitz_isolation (h1 : 2 ^ k ≤ 4 * S.card) (h2 : 4 * S.card ≤ 3 * 2 ^ k) :
    3 / 16 ≤ succProb n k S
theorem exists_good_k (n) (hn : 1 ≤ n) (S) (hS : S.Nonempty) :
    ∃ k ∈ Icc 2 (n + 1), 3 / 16 ≤ succProb n k S
theorem avg_succProb (n) (hn : 1 ≤ n) (S) (hS : S.Nonempty) :
    3 / (16 * n) ≤ (1 / n) * ∑ k ∈ Icc 2 (n + 1), succProb n k S
lemma card_range_k (n) : (Icc 2 (n + 1)).card = n
```

The target value is `y₀ = 0`. The average over `k` is exactly the success probability when `k` is uniform in `{2, …, n+1}` and `(a, b)` is then uniform.

**Discrepancy (minor).** The claim "such k exists in {2, …, n+1}" is false for `n = 0`, because the range is empty. The theorems therefore assume `n ≥ 1`.

## Target 4: Tseitin parsimony (PROVED)

```lean
inductive Circuit (n : ℕ) : ℕ → Type
  | nil : Circuit n 0
  | snoc {g} : Circuit n g → ((Fin (n + g) → Bool) → Bool) → Circuit n (g + 1)
def eval : Circuit n g → (Fin n → Bool) → Fin (n + g) → Bool
def Consistent : Circuit n g → (Fin (n + g) → Bool) → Prop  -- every gate wire = gate(earlier wires)
def inputs (w : Fin (n + g) → Bool) : Fin n → Bool

def Circuit.consistentEquiv (c : Circuit n g) : {w // Consistent c w} ≃ (Fin n → Bool)
theorem Circuit.card_consistent (c) (P) :
    Nat.card {w // Consistent c w ∧ P w} = Nat.card {x // P (eval c x)}
theorem Circuit.card_tseitin (c) (F : (Fin n → Bool) → Prop) (out : Finset (Fin (n + g))) :
    Nat.card {w // Consistent c w ∧ (F (inputs w) ∧ ∀ o ∈ out, w o = false)}
      = Nat.card {x // F x ∧ ∀ o ∈ out, eval c x o = false}
theorem gateClauses_iff (G : Bool → Bool → Bool) (u v w) :
    (∀ α β, u ≠ α ∨ v ≠ β ∨ w = G α β) ↔ w = G u v
```

`gateClauses_iff` covers the clause level: the four width-3 clauses of a fan-in-2 gate are equivalent to the gate constraint. So `Consistent` is exactly the conjunction of the Tseitin clauses when every gate has fan-in 2.

## `#print axioms`

```
toeplitz_surjective, toeplitz_fiber_card, hash_uniform, hash_pairwise, hash_pairwise_F2,
hash_pairwise_F2', isolation_exact, isolation, isolation_notes_window, exists_window,
toeplitz_isolation, exists_good_k, avg_succProb, Circuit.card_consistent, Circuit.card_tseitin:
    [propext, Classical.choice, Quot.sound]
Circuit.consistentEquiv: [propext, Quot.sound]
gateClauses_iff: no axioms
```
