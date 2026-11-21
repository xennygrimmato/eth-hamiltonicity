# node notebook: Heath-Brown exact ψ with μ inside big nodes (the "one live switch")

Owner: node. Inputs read: p1/notebook.md §3, §7 (V2); w2/notebook.md Idea 9; p2/notebook.md §0; prime-finding.md
§§2–4; iterated-product.md §§0–3; factoring-engine.md §3; anthropic-api.md §§2.1–2.2 (the Lean statements of the cost
theorem). Scripts: `hb_check.py` (→ `hb_check.out`), `cost_model.py` (→ `cost_model.out`).

## 0. Verdict: NO

The switch is off. Heath-Brown's route to exact ψ(J) is a correct signed integer count, and the engine counts
signed weights exactly. But the cost theorem prices a node of P bits at about e_K·K·ln K·P in the exponent, and HB
needs nodes of n/h bits together with a product of fold 2h−1. In the tree model this forces a certified exponent of
at least e_K·n·log₂K. The rate the engine actually has is e_K ≍ 1/√log K, so that bound is ≥ Θ(n√log K) ≥ Θ(n).
That is not N^{o(1)}, and not even below √N. Two workarounds fail for the same reason:
- recursive μ as a sub-system (nested HB, Linnik, or the inverse series);
- an outer loop over the μ-part.

The only door left is exactly the iterated-product question already on record: an engine rate e_K = o(1/log K), or a
K-fold product verifier with cut o(n·√log K). It is not a new escape. Polymath4 is not solved here.

## 1. What the engine's cost theorem actually requires (question (a))

Statement (Lean, `GroupingExplicit` + Theorem A(b); anthropic-api.md l.160–210) [K]:

  T ≤ ( K^g + 2^{e_K·K²·L} · (K(L+B′))^{C₀K²} · 2^{2gP/K} · τ ) · (g(P+B))^{C₁},  with  L = ⌈(U + 2ζgP)/K²⌉,

where:
- the network has g nodes, each with a setting of ≤ P bits;
- U is the total number of shared bits;
- |W| < 2^B;
- τ is the price of one node-table query;
- e_K ≤ (3x₀+6)/√log K, with x₀ ≥ 18.

Admissible shapes (`Cases`):
- (i) g = 3K⁸ and ζ = 1/(2K);
- (ii) K | g, every pairwise cut ≤ P/g, and K·ln(2gK) ≤ 2ζ²g with ζ ≤ 1.

So the exponent is

  E = e_K·(U + 2ζgP) + 2gP/K + g log₂K + O(K² log(nB)) + log₂τ.

**What one big node costs [R], by reading off the theorem.**
- In case (i), 2ζgP + 2gP/K·(1/e) ≥ 3K⁷P(1 + 2/e_K). A node of P bits therefore needs P = o(n/K⁷). This is the
  team's "P ≤ n/K⁷"; precisely, it is P ≤ n/(K⁷√log n) up to constants.
- In case (ii), 2ζgP ≥ K·ln(2gK)·P/ζ ≥ 2K ln K·P. Nodes of P = n/(K^{1+o(1)}) bits are allowed, but no larger.
- In every case g ≥ K, and the exponent pays at least e_K·K·ln K·P for node size P.

**Weights.**
- W and Ψ are ℤ-valued, and the value Σ_z Π W·Ψ is an exact integer. Signed weights such as μ, C(K,j), or
  ⌊B log m⌋ are free, up to the poly(B) factor. So **yes, the engine counts over ℤ** [K: `Net.value : ℤ`].
- The price of a node weight is only τ, the time to evaluate it. For μ(d) on P bits this is 2^{O(P/√log P)}, which
  is harmless.
- The only constraint is that a weight may depend only on the labels inside one node. Hence the weighted variable
  must fit in P bits.

**HB in this model.** Take HB with h pieces:

  μ(m) = Σ_{j≤h} (−1)^{j−1} C(h,j)(μ_{≤z}^{*j} * 1^{*(j−1)})(m),  valid for m ≤ z^h.

- **Exact ψ.** This gives ψ(J) = (1/B)·[count with log-slot weight ⌊B log e⌋] + O(#tuples·2^h/B), with B = x².
  Note: ψ(J) is not an integer, so p1's "round(E/B)" should read "to within 10⁻⁶". That is enough, because
  ψ(J) ≠ 0 ⇒ ψ(J) ≥ log 2.
- **Node size.** The μ-variables have up to n/h bits, so P ≥ n/h.
- **Cut.** The heavy tuples have all 2h−1 factors of size ≈ n/(2h). A product tree whose leaf-clusters have ≤ P
  bits has U ≥ n·log₂(n/P) − O(n). This holds in the tree model, [R] from iterated-product.md §3 (Lean
  `cost_ge_entropy`).

**Theorem N1 [R, relative to the stated cost theorem and the tree model].** Every HB-type network for exact ψ has

  E ≥ e_K · n · min_{t∈(0,1]} [ log₂(1/t) + 2K ln K · t ] ≥ e_K · n · log₂K   (t = P/n).

Proof: insert P ≥ n/h ≥ … and U ≥ n log₂(n/P) into E above. Minimise over t: the minimum is at
t = 1/(2K ln K·ln 2), and the value is ≥ log₂K + log₂ln K + O(1). ∎

With e_K ≤ (3x₀+6)/√log K, the bound the theorem gives is ≥ 60·√log₂K·n ≥ 60n. That is worse than a sieve. The
numerics (`cost_model.out`) minimise the full exponent over K and P:

| rate e_K | min E/n | at log₂K | beats √N (E < n/2)? |
|---|---|---|---|
| 60/√log₂K (the theorem) | 179 | 1 | no |
| 1/√log₂K (constant 1) | 3.56 | 1 | no |
| 0.1/√log₂K (hypothetical) | 0.43 | 5 | yes, but only N^{0.43} at a fixed K |

As K → ∞ the bound grows like √log K. So no constant improvement can ever give N^{o(1)**}: x^{o(1)} via HB holds iff
e_K·log K → 0.

**Answer to (a).** No. A node carrying a weight on n/h bits with h = 2^{o(√log n)} is forbidden:
- In case (i) with K = n^{1/40}, it costs 2^{6K⁷n/h} = 2^{n^{1+7/40−o(1)}}.
- If the engine level K is lowered so the node fits (K ≤ h^{1+o(1)}), the rate degrades to e_K ≈ 1/√log h. The fold
  2h−1 then costs e_K·n·log h ≈ n√log h, which is not o(n).

The obstruction is not the "weight" itself but its locality: a weight must live in one node, and node volume is
taxed at rate ≈ K.

## 2. Workarounds (question (b)), each with its verdict

**(b1) μ on the long variable as a recursively counted sub-system: closes, same cost.**
μ(d) on D bits can be produced by HB again, with h′ pieces on D/h′-bit variables plus a (2h′−1)-fold product.
- Cut recursion: U(D) = D·log₂(2h′) + Σ_i U(D_i), where Σ D_i ≤ D and U(D) = O(D) once D ≤ P.
- Solution: U(D) = D·log₂(2h′)·⌈log_{h′}(D/P)⌉ ≥ D·log₂(D/P). Nesting therefore reproduces the one-shot bound
  exactly; it is the entropy bound again.
- The inverse series μ = Σ_j (−1)^j (ζ−1)^{*j} has fold up to D, so its cut is D log D. That is worse.

**Fold lower bound [R in the size-box slot model].** Suppose a witness system for μ on D bits:
- writes d as an ordered product over F slots;
- puts weights only on slots of ≤ P bits;
- uses predicates depending only on slot sizes.

Take d squarefree with r = D/P′ primes, each of P′ > P bits. Every weighted slot is then 1, and the value is a
combination of k^{ω} with 1 ≤ k ≤ F. Since (−1)^ω, 1^ω, …, F^ω are linearly independent on ω = 1..F+2, matching μ
forces F ≥ r − 1 ≈ D/P. With tree cuts this gives U ≥ D log(D/P) again. With arbitrary cheap predicates this is
only [C]: it is the Vandermonde wall of prime-finding.md §4 and p3 §8 (K* = Ω_max − 1).

**(b2) Linnik's identity on z-rough numbers: dead.**
- On z-rough m, Linnik's identity has fold ≤ n/log₂z = h. But it needs the weight [m z-rough] on the n-bit variable.
- Exact roughness is either:
  - Legendre (μ on z-smooth d, fold π(z)); or
  - Buchstab (prime weights on n/h-bit variables, the same node-size problem); or
  - Bezout (w1 I5, z = O(n) only, then fold n/log n, the iterated product).
- Each route lands on N1 or on the iterated product.

**(b3) Outer loop over the μ-part (Vaughan/HB hybrid): classical √x.**
- Loop over D = d₁⋯d_j ≤ Y outside the engine, with precomputed a_j(D) = μ_{≤z}^{*j}(D) (sieve, Y^{1+o(1)}). The
  inner unweighted (j−1)-fold divisor sums are cheap: cut n log h, which is o(n√log n) for h = 2^{o(√log n)}.
- The terms with D > Y need either the weighted j-fold product (N1), or an outer loop over E = J/D ≤ 2x/Y.
- So the cost is ≥ min(Y, x/Y)·x^{o(1)} ≥ √x. This is the Type-I/II √x balance of combinatorial methods
  (Deléglise–Rivat x^{2/3}, Lagarias–Odlyzko x^{1/2}).

**Over ℤ versus GF(2) [R/N].** There is no issue. Signed counts are exact. The mini-engine (`hb_check.py`)
enumerates the HB witness tuples (μ-slots ≤ z, 1-slots, a log-slot with weight ⌊x² log e⌋) and multiplies node
weights:

| J | h | tuples | |value/B − ψ(J)| |
|---|---|---|---|
| [1000, 1100] | 2 | 6,388 | 4.5e-6 |
| [1000, 1100] | 3 | 40,582 | 4.5e-6 |
| [5000, 5060] | 3 | 56,732 | 8.8e-8 |
| [20000, 20030] | 4 | 213,315 | 1.6e-8 |

The array form of the μ-identity has 0 mismatches for n ≤ 10⁶ (h = 2, 3) and n ≤ 10⁵ (h = 2, 3, 4).

Each sub-system is unique-witness, since a tuple is its own witness. But at these sizes a μ-variable has 5–10 of
the n = 17–20 bits, i.e. n/h bits, which is above the node load allowed by the cost theorem for any K with e_K < 1.
The identity is not the catch. The node load is.

## 3. Cost recursion (question (c))

To find a prime: bisect on θ(J) = ψ(J) − Σ_{k≥2} θ(J^{1/k}). There are n+1 rounds, and each round needs one ψ at
scale N plus a recursion at scales N^{1/k}:

  T_find(N) ≤ (n+1)·[T_ψ(N) + Σ_{k=2}^{n} T_θ(N^{1/k})] = (n+1)·T_ψ(N)·(1+o(1)),  T_ψ(N) = 2^{E},
  E ≥ e_K·n·log₂K (N1).

**Does this beat √N?** It does iff e_K·log₂K < 1/2 at some level K:
- The theorem gives e_K·log₂K ≥ 60√log₂K, so no.
- Even a rate of 1/√log K gives √log₂K ≥ 1, so no.
- N^{o(1)} would need e_K·log K → 0. For the engine's own analysis (√log rate) that is false.

## 4. The catch, and what would reopen the switch

1. **The catch.** The engine's √log K saving is a √log K factor smaller than the log K that any product of fold
   ≥ K (needed because node size ≤ n/K^{1+o(1)}) costs in cut. It is the same barrier as iterated-product.md §0.4
   and prime-finding.md §4, seen from the weight side.
2. **What would reopen it** [C, open, either one suffices]:
   - (i) an engine whose rate satisfies e_K = o(1/log K). This is not excluded: the only query lower bound I see is
     e_K ≥ (K−1)/K²;
   - (ii) a K-fold product verifier with cut o(n√log K), beating the Lean-proved tree bound by leaving the tree model.
   No lower bound is known for either. A super-linear lower bound for (ii) would be a circuit lower bound
   (iterated-product.md §5).
3. **Small correction to p1 V2.** ψ(J) is real, so "round(E/B)" should be "E/B to within 1/(polylog)". Nonzero
   detection still works, because ψ(J) > 0 ⇒ ψ(J) ≥ log 2.
4. **Correction to the team's node rule.** Shape (ii) of `Cases` allows nodes of n/K^{1+o(1)} bits, not only
   n/K⁷ (shape (i)). This does not help here, because N1 already uses shape (ii).
