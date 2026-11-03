# A signed #SAT encoding of Hamiltonian-cycle counting at vertex granularity

Status (2026-11-03): **the linear-size target is not reached.** What is proved and checked:

* the identity `n·#HC(G) = #(φ∧¬z) − #(φ∧z)` for an explicit width-3 CNF `φ` built from the
  singleton-blob (g = n) instance of the paper's blob factorisation;
* the CNF has `Θ(m log n)` variables and clauses, **not** `O(m)`; all of the log factor comes from
  one quadratic form over GF(2), the parity of crossings among the "mixed" chords;
* the proposed `O(m)` prefix-sum circuit for that parity is identically zero on valid labellings
  (the halving step cannot be done by prefix sums), and the hierarchical-blob fallback does not give
  `O(m log log m)` (Section 4.4);
* the crossing parity is, up to `O(m)` local gates, **the parity of the number of cycles** of the
  mixed 2-regular subgraph (Whitney's formula, Lemma W). So a linear-size encoding of this kind
  exists iff the sign of a permutation whose arcs lie in `G` has `O(m)`-size circuits (or `O(m)`-size
  signed witnesses). That is the connectivity barrier in its exact form. No lower bound is known
  for it, and no linear upper bound is known either.

With `Θ(m log n)` variables neither lab's top-level theorem gives anything below `2^m`
(Section 6). Scripts: `research/scripts/linenc_lib.py`, `linenc_A_signs.py`, `linenc_B_cnf.py`,
`linenc_C_sizes.py`. Each prints PASS/FAIL, and all pass; their outputs are in the matching `.out` files.

---

## 1. Setting

`G = (V,E)`, with `n ≥ 3` and `m = |E|`. The root is `r ∈ V`, with degree `d_r`. A bijection
`pos : V → {0,…,n−1}` is the vertex order; the vertices are placed on a circle in this order.
For `e = {i,j}` we write `a_e < b_e` for its two positions. Generators are
`ψ̄_v, ψ_v (v ≠ r)`, with `ψ̄_r = ψ_r = 0`, and `Ω_V = Π_v ψ̄_vψ_v`, as in the paper, §3.

**Labellings.** These are as in the paper's Table 1 with the singleton partition `β = pos`, except
that label 0 is split into its two monomials. Each edge then has six states:

| state | monomial | gives ψ̄ to | gives ψ to |
|---|---|---|---|
| `N` | (edge unused) | – | – |
| `one` | 1 | – | – |
| `D_i` | `ψ̄_iψ_i` | i | i |
| `D_j` | `ψ̄_jψ_j` | j | j |
| `A_ij` (an arc i→j, "mixed") | `−ψ̄_iψ_j` | i | j |
| `A_ji` (an arc j→i, "mixed") | `−ψ̄_jψ_i` | j | i |

A labelling `η` is *valid* if every vertex has exactly two used edges, every `v ≠ r` receives exactly one
`ψ̄_v` and exactly one `ψ_v`, and no monomial mentions `r`. By `Cor. hc-berezin` and multilinearity,
`n·#HC(G) = Σ_{η valid} κ(η)`, where `κ(η) := [Ω_V](Π_{e used} monomial_e(η)) ∈ {±1}`. (Invalid
labellings have coefficient 0.)

## 2. The sign of a valid labelling

**Lemma S1 (sign rule at g = n).** For every vertex order and every crossing order,
`κ(η) = Π_v [ω_v](R_v(η)) · Π_v σ_v(η) · (−1)^{Cross(η)}`. Here `R_v` is the ordered product of the
pieces at `v`, `σ_v` is the paper's local sign (the pairs of odd edges meeting at `v`), and `Cross(η)` is the
number of unordered pairs of mixed edges with four distinct endpoints whose chords interleave.

*Proof.* This is Prop. "Sign rule", Lemma "Block factorisation" and Prop. "Sign factorisation" of the
paper, for the partition `β = pos`. The proofs use only the homogeneity of the pieces, so splitting
label 0 into `one` and `D_t` is harmless. With singleton blobs, two chords meet iff the edges share a
vertex. Disjoint chords contribute `I(k,l)` by Lemma "disjoint chords", and `P_ab = x_{ab}` (the
mixed indicator of the edge between the vertices at positions a and b).
Check (i) of `linenc_A_signs.py` compares this with the exterior-algebra coefficient. ∎

**Lemma S2 (closed form).** `κ(η) = (−1)^{c(η)}`, where `c(η)` is the number of cycles formed by the
mixed arcs.

*Proof.* Diagonal monomials are exactly `ω_v` and are central, so they contribute `+1`. The mixed arcs
form vertex-disjoint directed cycles that avoid `r` (each `v ≠ r` has at most one outgoing ψ̄ and one
incoming ψ). A simple graph has no 2-cycles, so every such cycle has length `L ≥ 3`. The cycle
`v_1→…→v_L→v_1` contributes `Π(−ψ̄_{v_k}ψ_{v_{k+1}}) = (−1)^L ψ̄_1ψ_2ψ̄_2ψ_3⋯ψ̄_Lψ_1`. Moving `ψ_1` left
past `2L−2` generators costs nothing, and the `L−1` swaps `ψ_kψ̄_k = −ψ̄_kψ_k` cost `(−1)^{L−1}`.
The total is `(−1)^{2L−1} = −1` per cycle. Even blocks commute. ∎

So the sign is exactly *−1 per mixed cycle*. The whole difficulty of the encoding is computing the
parity of the number of cycles.

**Lemma W (Whitney, local form).** For a valid labelling, write `u = pred(v)` and `w = succ(v)` along the
mixed arcs, and let `ρ_v := [pos u < pos w < pos v] ⊕ [pos v < pos w < pos u]`. Then
`c(η) ≡ Cross(η) + Σ_v ρ_v (mod 2)`.

*Proof.* Put vertex `v` at `P_v = exp(2πi·pos(v)/n)`. Since `P_w − P_u = e^{iπ(p_u+p_w)/n}·2i·sin(π(p_w−p_u)/n)`,
the direction of the chord `u→w` is `π(p_u+p_w)/n + π/2 + π[p_w<p_u] (mod 2π)`. The exterior turning
angle at `v` is `τ_v ∈ (−π,π)` (it is never `±π`, because `u ≠ w`). Hence
`nτ_v/π = (p_w−p_u) + n([p_w<p_v] − [p_v<p_u]) + 2n·c_v` for an integer `c_v`. Summing over a cycle
gives `Σ(p_w−p_u) = 0`, and `Σ_v[p_{succ v}<p_v] = Σ_v[p_v<p_{pred v}]`, since both count the descending
arcs. So the rotation number of the inscribed polygon is `rot = Στ_v/2π = Σ_v c_v`. The four cases of
the order of `p_u, p_v, p_w` give `c_v = −1` if `p_u<p_w<p_v`, `c_v = +1` if `p_v<p_w<p_u`, and `c_v = 0`
otherwise, so `c_v ≡ ρ_v`. Whitney's theorem says `rot(γ) ≡ 1 + #self-crossings(γ) (mod 2)` for a
normal closed curve. Smoothing the corners is harmless, since `|τ_v| < π`, and general position holds
after a perturbation that keeps the cyclic order, because interleaving and `ρ_v` depend only on that
order. Two vertex-disjoint closed curves cross an even number of times. Summing over the cycles gives
`Cross ≡ c + Σρ_v`. ∎

So `κ(η) = (−1)^{Cross(η) ⊕ ⊕_v ρ_v(η)}`. Here `ρ_v` is local (it depends on the two mixed edges at `v`
and their orientation), and `Cross` is the only global term. Lemma W also shows that the
**converse** holds: any circuit for `Cross` on valid inputs gives one for `c mod 2` with `O(m)` extra gates.

## 3. The crossing-parity circuit

The input is `x ∈ {0,1}^E` (here `x_e = [e mixed]`). Every edge is a point `(a_e, b_e)` with `a_e < b_e`.

**Lemma C.** For every `x`, `Cross(x) ≡ Dom(x) + DT(x) (mod 2)`, where
`Dom = #{(e,f) : a_e<a_f, b_e<b_f}` and `DT = #{(e,f) : b_e ≤ a_f}`, both counted over ordered pairs
of active points. Moreover, `Dom mod 2` has a circuit of at most `2m⌈log₂n⌉ + n` XOR/AND gates,
and `DT mod 2` has one of at most `2m + 3n` gates.

*Proof.* Take an ordered pair with `a_e<a_f` and `b_e<b_f`. Then `b_e` and `a_f` compare in one of
three ways. If `b_e<a_f`, the chords are disjoint. If `b_e=a_f`, they touch at a vertex. If
`b_e>a_f`, then `a_e<a_f<b_e<b_f`, and they interleave with four distinct ends. Conversely, every
disjoint or touching ordered pair (e before f) satisfies `a_e<a_f` and `b_e<b_f`, and every
interleaving unordered pair occurs exactly once with `a_e<a_f`. Pairs that share a low or a high end
are excluded by the strict inequalities. Hence `Cross = Dom − DT` exactly, and the claim holds mod 2.

`DT`: let `HE(t) = ⊕{x_e : b_e = t}`, `LE(t) = ⊕{x_f : a_f = t}` and `H(t) = ⊕_{s≤t} HE(s)`. Then
`DT = ⊕_t H(t) ∧ LE(t)`.

`Dom`: use divide and conquer on the `a`-interval `[lo,hi]`, split at `mid`. Points with `a ≤ mid`
form `L`, and the others form `R`. Then `Dom(P) = Dom(L) ⊕ Dom(R) ⊕ ⊕_{f∈R} x_f ∧ Pre(f)`, where
`Pre(f)` is the parity of the active `e ∈ L` with `b_e < b_f`. Pairs inside one half are handled by the
recursion. For a pair across the halves, `a_e < a_f` holds automatically, so it is counted iff
`b_e < b_f`. Sort `L ∪ R` by `(b, R before L)`. This order is fixed when the circuit is built. A running
XOR over the `L`-points then gives every `Pre(f)` (ties `b_e = b_f` are correctly excluded). This costs
at most `|L| + 2|R| + 1` gates per node, which is at most 2 per point per level plus 1 per node, over
`⌈log₂ n⌉` levels. ∎

Checks (iv) of `linenc_A_signs.py` compare this with brute force on 9087 valid labellings and 4800
random `x`: PASS.

## 4. Why the `O(m)` route fails

**4.1 The proposal is identically zero.** On a valid labelling every vertex has 0 or 2 mixed edges, so
`p_v = ⊕_{f∋v} x_f = 0` and `S(t) ≡ 0`. The proposed circuit
`⊕_e x_e(S(b−1)⊕S(a)) ⊕ (spurious corrections)` computes `Σ_e x_e·c(e) mod 2`, where `c(e)` is the
number of mixed chords interleaving `e`. Every interleaving pair is counted twice, so this is
`2·Cross ≡ 0`. Check (v) confirms that it is 0 on all 9087 valid labellings and wrong whenever
`Cross = 1` (358 cases).

**4.2 The halving is a 2D problem.** `Cross` needs `Σ_e x_e c(e) mod 4`. Now `c(e) =
(cut of the interval (a,b)) − (spurious)`, and `cut = 2·#active vertices inside − 2·#mixed edges nested inside`.
The first count is a 1D prefix. The second, summed over `e`, is the number of *nested* pairs, which
is again a quadratic form, and `Cross + Nest` is the only combination that prefix sums give. Counting
only the `f` with `a<c<b<d`, as proposed, is a dominance query in the rectangle `(a,b)×(b,∞)`. Every
variant ends in 2D dominance parity.

**4.3 It is the cycle-parity barrier.** By Lemmas S2 and W, an `O(m)` circuit (or `O(m)` signed
witness) for `Cross` on valid inputs is the same thing as one for `c(η) mod 2`, the sign of a
permutation whose arcs are edges of `G`. Prefix tricks cannot compute it locally, because it is not a
local-plus-linear function. A 2-switch inside one cycle merges or splits according to the cycle's
orientation, and that orientation is invisible locally. Transfer-matrix or Cut&Count-style local
weights give `μ^{#cycles}` only with `μ ∈ ℕ`: for local weights `tr(M^L) = Σλ_i^L` and positive
multiplicities. They never give `(−1)^{#cycles}` without the geometry, that is, without `Cross`.

**4.4 The hierarchical fallback.** Split the positions into `g` blocks. Pairs of chords whose block
chords are disjoint are handled by bundle parities, with `O(g²+m)` gates via 2D prefix XOR. That
leaves three kinds of pair, and each chord `(u,v)` takes part in all three subproblems:

* chords sharing one block: a dominance problem at that block, on (position in block, target block);
* chords in the same bundle: dominance on (position in A, position in B);
* internal chords: recursion.

For a chord, that is the half-edge problems at both of its blocks plus its bundle cell. In the worst
case this gives `f(N) ≤ 2f(N^{1/3}) + f(N^{2/3}) + O(1)` gates per point, that is,
`f = Θ((log N)^{1.39})`. That is worse than binary divide and conquer. Any one-coordinate split
satisfies `f(N) = f(N/g) + f(g) + O(1)`, so `f = Θ(log N)`, for every `g`. A cost of `O(m log log m)`
would need the block-level work to be `o(1)` per point per level, and no construction for that is known.
(Offline 2D dominance counting in `O(n√log n)` RAM time, by Chan–Pătraşcu, uses word packing, which
circuits do not have. It is right at the `√log` threshold of Section 6 anyway.)

## 5. The CNF φ (what is proved)

**Theorem.** For every `G` with `n ≥ 3`, every `r` and every vertex order, the following width-3 CNF
`φ` with output variable `z` satisfies `n·#HC(G) = #(φ∧¬z) − #(φ∧z)`, and `#φ` equals the number of valid labellings.

Variables and clauses:

* **Primary**: `u_e` (e used), and `b_{e,v}`, `p_{e,v}` (e gives `ψ̄_v` / `ψ_v`) for `v ∈ e∖{r}`.
  That makes `5m − 2d_r` variables.
* **Edge**: at most one `b`, at most one `p`, `b ⇒ some p`, `p ⇒ some b`, `b,p ⇒ u`. That makes
  `10m − 6d_r` clauses. These leave exactly the 6 states of Section 1.
* **Vertex**: exactly-2 over `{u_e}` at every `v`, and exactly-1 over `{b_{e,v}}` and over `{p_{e,v}}`
  at `v ≠ r`. These use sequential counters whose registers are defined by equivalences. Exactly-1 over
  `d` literals costs `d−1` variables and `4d−3` clauses; exactly-2 costs `2(d−1)` variables and `8d−9`
  clauses. In total: `8m − 2d_r − 4n + 2` variables and `32m − 8d_r − 15n + 6` clauses.
* **Local sign**:
  * `x_e = b_{e,i} ⊕ p_{e,i}` (mixed), for the edges not at `r`;
  * `I_e(v) = p_{e,v}∧¬b_{e,v}` (an in-arc) and `O_e(v) = b_{e,v}∧¬p_{e,v}` (an out-arc);
  * `ρ_v`, computed by a prefix chain over `v`'s neighbours sorted by position, below `v` and above
    `v` separately.

  All of this takes at most `11(m − d_r)` variables.
* **Crossing**: Lemma C on the inputs `x_e`, with at most `2m'⌈log₂ n⌉ + 2m' + 4n + 1` variables,
  where `m' = m − d_r`.
* **Output**: `z = Cross ⊕ ⊕_v ρ_v`.

Every gate is Tseitin-encoded (XOR: 4 clauses; AND/OR: 3 clauses; `s ↔ a∨(x∧c)`: 4 clauses), so
every valid labelling has exactly one extension.

*Proof.* Valid labellings correspond bijectively to the assignments of the primary variables that
satisfy the edge and vertex clauses. Each one has a unique extension, and in it
`z = Cross ⊕ ⊕ρ_v ≡ c(η)` by Lemmas C and W. So `#(φ∧¬z) − #(φ∧z) = Σ_η (−1)^{c(η)} = Σ_η κ(η)` by
Lemma S2, and this is `n·#HC(G)` by Section 1. ∎

**Size.** The number of variables is at most `2m'⌈log₂n⌉ + 26m + O(n)`, and the number of clauses is
at most about `4×` that. Both are `Θ(m log n)`. The measured values (`linenc_C_sizes.out`, random
3- and 4-regular graphs) are below. The crossing variables per `m log₂ n` stay at about `1.55` and do
not fall.

| n | m | vars | clauses | vars/m |
|---|---|---|---|---|
| 256 | 384 | 11 730 | 40 101 | 30.6 |
| 1024 | 1536 | 51 944 | 178 767 | 33.8 |
| 4096 | 6144 | 226 162 | 782 639 | 36.8 |
| 4096 | 8192 | 313 912 | 1 089 895 | 38.3 |

**Verification** (`linenc_B_cnf.out`). There were 120 random graphs with `n = 6…9`, `m ≤ 2n+1`, random
`r` and random vertex order. The models were counted exactly by a DPLL counter. Every instance passed:
the identity held, `#φ` equalled the number of valid labellings, and the width was at most 3.
**Ablations**, each of which must fail somewhere:

| ablation | wrong on |
|---|---|
| drop `Cross` | 26/120 |
| drop the touching correction `b_e = a_f` | 53/120 |
| drop the local `ρ_v` (the analogue of `Π σ_v`) | 54/120 |
| add a spurious `(−1)^{#mixed}` | 53/120 |
| `O(m)` prefix circuit instead of `Cross` | 26/120 |

**Task A** (`linenc_A_signs.out`). There were 160 graphs (`n ≤ 9`), 9087 valid labellings,
random generator, vertex and crossing orders. All checks passed: (i) Lemma S1 against the Koszul sign;
(ii) `κ = (−1)^c`; (iii) Lemma W; (iv) Lemma C; (v) the `O(m)` proposal is ≡ 0; and
(vi) `Σ_η κ(η) = n·#HC(G)`.

## 6. Consequences via the top-level theorems

* **OpenAI**, `exact_count_and_sat` (`OAI/…/SqrtLogSpace/Final.lean`). For each width `k ≥ 2` it gives one
  machine with time `≤ C·(bits+1)^d·2^{A·ρ(N_v)}`, where `ρ(N) = N (ln ln(N+16))²/√ln(N+16)`. The
  constants depend on `k`, and the bound depends only on the number `N_v` of **variables**.
* **Anthropic**, `MainTheorem` (`MainResults.lean`). It gives time `2^{C·min(k·m_c/√log m_c, k²·N_v·loglog N_v/√log N_v)}`,
  with one `C` for all `k`.
* **With this encoding** (`k = 3`, `N_v, m_c = Θ(m log n)`): OpenAI gives
  `2^{O(m √log n (log log n)²)}` and Anthropic gives `2^{O(m √log n)}`. Both are worse than `2^m`, so
  there is **no consequence**. Two `#SAT` calls and a subtraction are cheap. The obstruction is only the
  size.
* **What would suffice**: `N_v = o(m√log m/(log log m)²)` for OpenAI, or `min(m_c, N_v log log N_v) =
  o(m√log m)` for Anthropic. That is, any encoding of size `m·(log m)^{1/2−ε}` would give `2^{o(m)}`
  #HC through the top-level theorems only. A linear encoding would give `2^{O(m/√log m)}` through
  Anthropic (the order of the paper's Theorem 1.2, but without (H_A)) and `2^{O(m(loglog m)²/√log m)}`
  through OpenAI. Clause count and width do not help. Anthropic's variable term charges `k²`, and
  fan-in-`k` gates cut the D&C only by a factor `k`.
* **Existing results** (hexagon:2610.00672): Theorems 1.1–1.3 and TSP assume three internal results of
  [A]. Only the parity theorem (`count_cutCNF`, linear size, mod 2) and randomized decision (a)
  rest on the top-level theorems alone. That remains the situation.
* **Table 3 corollaries.** Mod-2 versions (Cut&Count) are already linear and need no sign. Every
  exact-count row that uses the fermionic sign inherits the same cycle-parity term:
  * directed HC and arborescences (signs of permutations);
  * spanning forests and `T(x,1)` (matrix-forest Berezin forms);
  * Steiner tree and FVS via determinants.

  So none of them survives at linear size either. TSP by Kronecker substitution does not survive a
  signed `#SAT` call at all at any useful size. The weight `2^{b·w(H)}` with `b = Θ(n log n)` has to be
  realised by `b·w_e` free variables per used edge, which makes `N_v ≥ Θ(m W n log n)`.

## 7. Literature (web search, 2026-11-03)

* SAT encodings of HC have been surveyed and compared by Zhou (ModRef 2019, CP 2024: vertex elimination
  `O(n³)` vars / `O(n⁴)` clauses) and by Velev–Gao (absolute/permutation encodings, `Θ(n²)`–`Θ(n³)`).
  The smallest known encodings give each vertex a `⌈log₂ n⌉`-bit index and use an LFSR, a binary adder
  or Chinese remaindering (Johnson; Heule, *Chinese Remainder Encoding for Hamiltonian Cycles*, SAT
  2021). These have `O(n log n)` variables and `O(m log n)` clauses, which Heule calls "quasilinear in the
  number of edges". A parsimonious variant (index = position from `r`) is folklore. All of them are
  `Θ(m log n)`, like ours. Ours offers no improvement in size; its only novelty is that it is signed and
  fermionic.
* No linear-size SAT or #SAT encoding of HC was found, and no lower bound either. The literature
  treats connectivity as the expensive part (e.g. Ohashi–Soh–Le Berre). There are no superlinear
  lower bounds for explicit XOR circuits, which is why a lower bound for permutation sign or
  dominance parity is out of reach; cancellation-free and bounded-depth `Ω(n log n)` bounds exist.
* Cut&Count (Cygan et al.) gives only `2^{#components}`, which is exact mod 2.
  Cygan–Kratsch–Nederlof: the GF(2)-rank of the matchings connectivity matrix is `2^{t/2−1}`. Over
  the rationals, the rank-based lower bound for counting HC (Curticapean–Lindzey–Nederlof, arXiv 1709.02311) does
  not give a superlinear bound on encoding size for sparse graphs, since the rank is at most
  `2^{|E_side|}`.
* Verdict: the reduction "linear-size signed encoding ⇔ linear-size circuit for the sign of a
  permutation supported on `G` (or for 2D-dominance parity)" (Lemma W + Lemma C) seems not to be
  written down. Treat it as a new, small observation. The linear encoding itself remains open.

## 8. What a Lean formalisation would need (for the Θ(m log n) theorem, or for a future O(m) one)

1. Lemma S2, from `blob_factorisation` at `β = pos` (`ExactHC/Main.lean`, `Blobs.lean`,
   `SignRule.lean`), specialised to singleton blobs with label 0 split. Alternatively, prove
   `κ = (−1)^{#mixed cycles}` directly. Lemma W is *not* needed for correctness if `z` is defined as
   `Π_v(top R_v·σ_v)·(−1)^{Cross}`. In that case use Lemma S1 as it stands and Tseitin-encode the
   local factor. Lemma W is what makes the local factor `O(deg)`.
2. Tseitin parsimony for XOR/AND/OR gates and the sequential counters (unique extension). This is
   the analogue of the chain lemmas in `HamiltonianAllGraphs.lean` (`chain_iff`, `stepCNF_eval`).
3. Lemma C (the D&C circuit) and the size bounds.
4. The composition: `n·#HC = numSat(φ∧¬z) − numSat(φ∧z)`, with two calls, exactly as
   `AnthropicHamiltonian.lean` feeds `cutCNF` to `MainTheorem` (padding with `pad`, `cnfToList`, AllOccur),
   and `HamiltonianAllGraphs.lean` feeds it to `exact_count_and_sat`. With `Θ(m log n)` variables the
   resulting bound is worse than brute force, so this is worth doing only once Section 6's threshold is met.
