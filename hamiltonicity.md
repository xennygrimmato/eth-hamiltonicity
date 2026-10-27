# Hamiltonicity in subexponential time on sparse graphs

Branch `eth-followup`, 27 Oct 2026. Tags as in `findings.md`: **[Lean]** machine-checked in this
repo (or upstream), **[Paper]** proved in the OpenAI manuscript, **[Mine]** my derivation.

## Summary

Refuting ETH does not by itself give fast algorithms for Hamiltonian Cycle (HC). ETH lower
bounds for HC come from linear reductions **from** 3-SAT **to** HC. The standard statement is
"unless ETH fails, there is no `2^{o(n+m)}` algorithm for Hamiltonian Cycle" (Cygan et al.,
*Parameterized Algorithms*, Ch. 14, as stated on Cygan's FPT-school slides, lecture 10, slide 21;
Lokshtanov–Marx–Saurabh's ETH survey, Thm 3.3, for Hamiltonian Path). The maximum-degree-3 version
needs an additional standard linear-size degree-reduction gadget. An algorithm needs the reverse:
an encoding of HC as a counting problem on `O(n)` Boolean variables. Connectivity is the obstacle,
because no linear-size SAT encoding of Hamiltonicity is known.

Cut&Count (Cygan, Nederlof, Pilipczuk, Pilipczuk, van Rooij, Wojtaszczyk, FOCS 2011) removes the
obstacle **modulo 2**. Combined with the OpenAI #k-SAT algorithm, it gives:

| # | Result | Status |
|---|---|---|
| 1 | Parity of the number of Hamiltonian cycles, max degree `Δ`: deterministic `poly(n)·2^{O_Δ(ρ(n))}` time, polynomial space | **[Lean]**: identity, width and reduction proved here; the machine theorem is conditional on openai/math's Lean theorem `exact_count_and_sat` |
| 1′ | Same for **every** graph, with one machine and no degree bound, in `2^{O(ρ(5|E|+3n))}`; subexponential whenever `|E| = o(n√log n/(log log n)²)` | **[Lean]**: `hamParity_allGraphs` (`HamiltonianAllGraphs.lean`), same conditionality as 1 |
| 2 | `#HC mod q` for each fixed `q`: deterministic `2^{O_{q,Δ}(ρ(n))}` for max degree `Δ`, or `2^{O_q(ρ(n+|E|))}` with the §3 counter | [Mine]: §4 |
| 3 | **Deciding and finding a Hamiltonian cycle**, `|E| ≤ Dn`: randomized one-sided error `2^{O_D(ρ(n))}`, polynomial space | [Mine]: the paper's Proposition 3.4 and Lemmas 4.7–4.8 applied to new factors, plus isolation (§5). Rests on the paper's *internal* lemmas in their general-algebra form, not on the Lean theorem; the bit-complexity adaptation is not written out |
| 3′ | **Deciding a Hamiltonian cycle, trusting only the top-level theorem**, max degree `Δ`: for every `δ > 0`, randomized one-sided error, success probability `≥ exp(−δ|E|)` per trial, so `2^{δn}` time | **[Lean], end to end**, conditional only on `exact_count_and_sat`. `decision_sound`: no Hamiltonian cycle means an even count for every hash. `hamDecision_fraction`: otherwise at least an `exp(−δ|E|)` fraction of hashes give an odd count. `hamDecision_subexponential`: one machine computes that parity for every hash |
| 4 | Directed versions: parity for max in/out-degree `Δ`, and decision with success `≥ exp(−δ|A|)` per trial. Björklund–Husfeldt compute this parity for **all** digraphs in `1.619^n`; this improves on them only for bounded in/out-degree | **[Lean]** for both: `DirectedHamiltonianParity.lean` and `DirectedHamiltonianDecision.lean` (`dir_decision_sound`, `dirHamDecision_fraction`, `dirHamDecision_subexponential`), same conditionality as 1 |
| 4′ | **TSP** on graphs with `|E| ≤ Dn` and integer weights `≤ poly(n)`: the optimum, randomized, `2^{O_D(ρ(n))}` | [Mine]: §5, same caveats as 3 |
| 5 | Other Cut&Count problems on sparse graphs (Steiner Tree, Connected Vertex Cover, Connected Dominating Set, Longest Path/Cycle): randomized `2^{O(ρ(n))}` | **Conjectural**: a sketch in §7, details not checked |

Here `ρ(N) = N(log log N)²/√log N`. For the parity and mod-`q` results (1, 1′, 2, and the parity
part of 4), the paper's sharper Appendix D (tensor contraction, not Lean-verified) improves the
exponent to `O(N/√log N)` with `N = n+|E|`. That improvement does **not** cover the weighted,
isolation-based results 3, 4′ and 5: Theorem D.1 (p. 53) requires the truncation order to satisfy
`ℓ ≤ Cs`, and those results need `ℓ = Θ(n|E|)` or more.

**Prior state of the art.** No subexponential algorithm for HC on *general* sparse graphs was
known, and ETH said none exists. (Planar, bounded-genus and minor-free graphs have `2^{O(√n)}`
algorithms via treewidth.) The best general bounds I found are:

* Björklund (arXiv 2009.11780, 2020): randomized polynomial-space `2^{n−Ω(n/δ)}` for directed
  graphs with average outdegree `δ`. This matches Björklund–Williams (ICALP 2019), which needs
  exponential space.
* Björklund–Husfeldt (FOCS 2013, arXiv 1301.7250): parity of directed Hamiltonian cycles in
  deterministic `O(1.619^n)`, for all digraphs.
* Undirected graphs: Björklund's `1.657^n` (2010), and `(2−ε_Δ)^n` for bounded degree by
  Björklund–Husfeldt–Kaski–Koivisto (2008).

So results 1′ and 3 are exponential improvements for every fixed average degree.

**What each result is conditional on.**

* Results 1, 1′, 2 and the parity part of 4 need only the OpenAI top-level #k-SAT theorem. That
  theorem is Lean-proved upstream as `exact_count_and_sat` and enters `lean/` as a hypothesis.
  `lean-bridge/` removes it: I rebuilt the upstream proof from source (axioms `propext`,
  `Classical.choice`, `Quot.sound` only). Against it, `hamParity_allGraphs_unconditional`,
  `hamParity_unconditional`, `dirHamParity_unconditional`, `hamDecision_unconditional` and
  `dirHamDecision_unconditional` are closed theorems with the same three axioms (README,
  *Independent verification*). The upstream proof's mathematics is still under expert review;
  Lean guarantees only that it proves the comparator statement as formalised.
* Results 3, 4′ and 5 need more. They use the paper's internal Proposition 3.4 and Lemmas 4.7–4.8
  in the generality the paper states: arbitrary polynomial factors over any commutative
  ℚ-algebra. The Lean development does not export that general form. They also need a
  bit-complexity adaptation of Appendix B.2 that I have not written out (§5).

**Not obtained.** Deterministic decision, the exact count `#HC`, and dense graphs. §8 explains
why the method stalls on exact counts.

---

## 1. The parity identity [Lean]

Let `G` be a graph on `[n]` with root `r`. Take Boolean variables `x_e` for `e ∈ E(G)` and `c_v`
for `v ∈ V(G)`. The CNF `cutCNF G r` (`lean/EthFollowup/HamiltonianParity.lean`) imposes three
constraints:

* **vertex:** exactly two of the `x_e` with `e ∋ v` are true, a constraint on `deg(v)` variables;
* **edge:** for an edge `uw`, `x_{uw} → (c_u ↔ c_w)`, on three variables;
* **root:** `c_r = false`.

Every local constraint becomes CNF clauses through one generic encoding (`constraintCNF`: one
clause per forbidden local pattern). The width is `max(Δ, 3)` and there are `|E| + n` variables.

A model is a pair `(X, c)`. Here `X` is a **2-factor**, a spanning edge set in which every vertex
has degree 2, and `c` is a cut with `c_r = 0` that no edge of `X` crosses. Hence

```
#cutCNF(G, r) = Σ_{X 2-factor} #{rooted cuts consistent with X} = Σ_X 2^{cc(X) − 1}
```

The Lean proof `count_cutCNF` proves the first equality by an explicit bijection. For the parity,
`cuts_card_mod_two` shows that the number of consistent rooted cuts is 1 when `X` is connected.
When `X` is not connected the number is even: flipping every vertex reachable from a vertex `v`
outside the root's component is a fixed-point-free involution (`Finset.sum_involution`). A
connected 2-factor is exactly a Hamiltonian cycle, viewed as an edge set (`hamCycles`), so

```
count_cutCNF_mod_two :  (#cutCNF(G, r) : ZMod 2) = (#hamCycles(G) : ZMod 2)
```

**Sanity check.** Evaluating both sides in Lean on small graphs gives these values:

| graph | `#cutCNF` | `#hamCycles` | `#2-factors` |
|---|---|---|---|
| K₄ | 3 | 3 | 3 |
| triangular prism | **5** | 3 | 4 (3 HCs + the two triangles, which contribute `2^{2−1} = 2`) |
| C₅ | 1 | 1 | 1 |
| K₃,₃ | 6 | 6 | 6 |

**Axioms.** `#print axioms` on `count_cutCNF`, `count_cutCNF_mod_two`, `cutCNF_width` and
`hamParity_subexponential` reports only `propext`, `Classical.choice` and `Quot.sound`.

## 2. The machine [Lean; unconditional via `lean-bridge/`]

`hamParity_subexponential Δ h` assumes the comparator statement at width `max Δ 3`, which is
proved upstream as `OAI…SqrtLogSpace.exact_count_and_sat`. Under that hypothesis it produces one
fixed machine with the following behaviour on every graph `G` with maximum degree `≤ Δ`:

* the input is the canonical encoding of the relabelled CNF `cutCNFFin G r`;
* the machine halts with a number `N` on its count tape, and `N ≡ #HC(G) (mod 2)`;
* the time is at most `C(L+1)^d · 2^{A·ρ(|E|+n)}`, where `|E| + n ≤ (1 + Δ/2)n`;
* the space is at most `S(L+1)^e` at every prefix.

`L` is the encoding length, `poly_Δ(n)`. Building `cutCNFFin G r` from `G` takes polynomial time;
that step is not formalised as a machine.

## 3. Unbounded degree [Lean]

`HamiltonianAllGraphs.lean` replaces each vertex constraint with a sequential counter. With the
incident edges of `v` listed as `e₀, …, e_{d−1}`, two bits per prefix `i ∈ {0, …, d}` hold the
number of selected edges among the first `i` (0, 1 or 2). The constraints are: the start value is
0; each step satisfies `value(i+1) = value(i) + x_{e_i} ≤ 2` (five variables); the final value
is 2.

`chain_iff_ext` shows the counter bits are forced to the prefix counts. `count_bigCNF` shows the
model count equals that of `cutCNF`, by an explicit bijection. The formula has width 5 and
`5|E| + 3n` variables (`card_bvar`, via the handshake lemma). So `hamParity_allGraphs` gives one
machine, the comparator at `k = 5`, for all graphs.

## 4. `#HC mod q` [Mine]

Give each vertex a colour in `[q]`, encoded in `⌈log₂ q⌉` bits with a constraint forbidding
invalid codes. The root gets colour 0, and selected edges force equal colours. A 2-factor then has
`q^{cc(X)−1}` consistent colourings, so the count is `Σ_X q^{cc(X)−1} ≡ #HC (mod q)`. For fixed
`q` this keeps a linear number of variables and bounded width.

## 5. Deciding and finding a Hamiltonian cycle [Mine]

The decision version does not obviously go through CNF counting alone. Isolation needs weights,
and the obvious encodings of weights in a CNF cost a `log n` factor in the number of variables,
which kills the gain. Sparse-hash isolation in the style of Calabro–Impagliazzo–Kabanets–Paturi is
not ruled out, and I have not explored it. The
paper's interpolation counter does accept weights.

**The paper's tool.** Proposition 3.4 (p. 25) sums `Σ_{x∈{0,1}^N} Π_f Φ_f(x|_{I_f})` for
arbitrary polynomial factors with coefficients in **any commutative ℚ-algebra** `A` (§3.1, p. 21:
"The proof also works with coefficients in any commutative ℚ-algebra"). Its requirements are:

* the product of the factors has degree `d = O(N)` in independent incidence indeterminates;
* Definition 3.1 holds for the design, which Lemma 4.7 constructs and Lemma 4.8 parametrises
  whenever factor scopes `w` and incidences `b` are at most `(log N)^β`.

The resulting exponent is (3.16), `O(N(log log N)²/√log N)`. The paper itself uses
`A = ℚ[V]/(V^ℓ)` in §5.

**Instance.** Assume maximum degree `Δ`; unbounded degree reduces to this case by §3 together
with copying `c_v` along an equality chain. Draw independent uniform weights
`w_e ∈ {1, …, 2|E|}` and set `A = ℚ[y]/(y^ℓ)` with `ℓ = 2n|E| + 1`. The factors are:

* vertex `v`: the multilinear polynomial of "exactly two of the `x_e`, `e ∋ v`", of degree `≤ Δ`;
* edge `uw`: `(1 − x_e(c_u + c_w − 2c_u c_w)) · (1 + (y^{w_e} − 1)x_e)`, of degree `≤ 3` after
  multilinearisation;
* root: `1 − c_r`.

Then `d ≤ Σ_v deg v + 3|E| + 1 = O(n)`, `w ≤ max(Δ, 3)` and `b ≤ 2Δ + 2`, so Lemma 4.8 applies
with `β = 1`. The sum equals

```
Σ_x Π_f Φ_f = Σ_{X 2-factor} 2^{cc(X)−1} · y^{w(X)}     (exactly, in ℤ[y]/(y^ℓ)),
```

so the coefficient of `y^W` is congruent mod 2 to the number of Hamiltonian cycles of weight `W`.

**Isolation.** By Mulmuley–Vazirani–Vazirani, if `G` has a Hamiltonian cycle then with
probability `≥ 1/2` the minimum-weight Hamiltonian cycle is unique. Its weight class then has an
odd coefficient. If `G` has no Hamiltonian cycle, every coefficient is even. So the test "is some
coefficient odd" errs only on yes-instances, with probability `≤ 1/2`, and `t` repetitions bring
this to `2^{−t}`.

**Cost.** Elements of `A` carry `ℓ = O(n²)` rational coefficients. `ℓ` enters only through the
`Jℓ` stored coefficients per element of `A[z]/(z^J)`, `O(J²ℓ²)` operations per multiplication, and
`ℓ` Hermite interpolations (Appendix B.3), all polynomial. The fixed-denominator bit-length
argument of Appendix B.2 *should* go through: the factors are multilinear with integer
coefficients of norm `2^{O(Δ)}`, and multiplying by `y^{w_e}` does not grow norms. The paper itself
verifies bit complexity only for its §5 factors (end of the proof of Prop. 3.4, p. 25), and I
have not written the adapted bounds out. Granting that, the time is `poly(n) · 2^{O_Δ(ρ(n))}` and
the space is polynomial.

**TSP with bounded weights.** Take integer weights `0 ≤ c_e ≤ W = poly(n)`. Set
`w_e = N₀ c_e + ρ_e`, where `ρ_e` is uniform in `[2|E|]` and `N₀ = 2n|E| + 1`. Every tour of
minimum `w`-weight is an optimal tour, and by isolation it is unique among optimal tours with
probability `≥ 1/2`. An odd coefficient at index `W'` implies a Hamiltonian cycle `H` of
`w`-weight `W'`, and then `⌊W'/N₀⌋ = c(H) ≥ OPT` because `Σ_{e∈H} ρ_e ≤ 2n|E| < N₀`. (Coefficients
below the minimum need not be 0, since non-Hamiltonian 2-factors contribute even amounts, but they
are never odd.) So the smallest index with an odd coefficient, divided by `N₀` and rounded down, is
never below `OPT`, and it equals `OPT` with probability `≥ 1/2`. Taking the minimum over `t` runs fails with probability `≤ 2^{−t}`. Here
`ℓ = n(N₀W + 2|E|) + 1` is still polynomial.

**Search.** Delete edges one at a time, keeping a deletion whenever the amplified test still
reports a Hamiltonian cycle. This costs `|E|` tests, each with error `2^{−2n}`.

**What has to be checked.** Proposition 3.4 and Lemmas 4.5–4.8 depend on the factors only
through their scopes, the degree bound and evaluation cost. The paper states them in exactly this
generality, but its bit-complexity appendix is written for the §5 factors. B.2 needs only integer
factor coefficients of bounded norm and one common denominator `d_den^{deg}`, and both hold here.
I checked this at the level of the B.2 inequalities but did not write the bounds out in full.

## 5a. Decision through CNF counting alone [Lean + cited lemma]

§5 needs the paper's internal counting routine over the algebra `ℚ[y]/(y^ℓ)`. The variant here
uses only the top-level Lean theorem, at the price of a weaker bound.

**Deterministic half [Lean].** `HamiltonianIsolation.lean` adds an arbitrary CNF `H` on the edge
variables to the Cut&Count formula and proves

```
count_cutCNFWith_mod_two :  #(cutCNF G r ∧ H) ≡ #{X ∈ hamCycles G : H(1_X)}   (mod 2).
```

In particular the count is even when `G` has no Hamiltonian cycle (`parity_of_none`), and odd
when exactly one Hamiltonian cycle satisfies `H` (`parity_of_unique`). `hamIso_subexponential`
packages this as one machine per `(Δ, k)` that works for every graph of maximum degree `Δ` and
every width-`k` edge constraint `H`. `xorCNF` encodes a GF(2) equation `Σ_{e∈R} x_e = b` as a
width-`|R|` CNF.

**Isolation [Lean, following CIKP].** This follows Calabro, Impagliazzo, Kabanets and Paturi,
*The complexity of Unique k-SAT: an isolation lemma for k-CNFs* (CCC 2003; JCSS 2008), Lemma 3.
Their lemma is *stated* for solution sets of k-CNFs, but its proof (pp. 4–7) uses only that the
set is a set. `IsolationLemma.lean` re-proves it for an arbitrary finite `S ⊆ {0,1}^ι`, as a
counting statement with no real numbers:

* `two_mul_card_separating` (Claim 4, exact): for points at distance `δ`, exactly
  `2^{k−1}(N^k − (N−δ)^k)` of the `(2N)^k` sparse equations separate them. An equation here is
  `k` coordinates drawn with replacement, plus `k` coefficients.
* `two_mul_card_bad_le`, `card_survivors_le`, `card_hash_nonempty` (Step I): the union bound over
  far pairs, the Hamming-ball bound on semi-isolated survivors, and averaging.
* `exists_isolating_set`, `card_isolating_DA` (Step II): with a farthest pair of the survivors,
  fixing `d ≥ 2r` coordinates to the right values leaves one point.
* `isolation_count` combines them. If `m` satisfies the union-bound condition
  `2|S|·(2^k(N^k + (N−r)^k))^m ≤ 2^m (2^k N^k)^m`, then the fraction of hashes `(A, b, D, α)`
  with `|D| = d` that leave exactly one point is at least `|S| / (2 · V(r) · 2^m · C(N,d) · 2^d)`.
  Here `V(r)` is the number of coordinate sets of size `< r`.

`HamiltonianDecision.lean` turns each hash into an edge CNF `hashCNF` of width `max k 1` and
proves two facts. `decision_sound`: with no Hamiltonian cycle, every hash gives an even count.
`decision_complete`: with `S = HC(G)`, at least that fraction of hashes give an odd count.

**The analytic estimate [Lean].** `IsolationAnalysis.lean` proves the classical bound
`Σ_{i≤pN} C(N,i) ≤ exp(N·H(p))` for `p ≤ 1/2` from the binomial theorem (`sum_choose_le_exp`,
with Mathlib's `Real.binEntropy`). It chooses `m = ⌈log(2|S|)/log ρ⌉` (`exists_m`), and then
picks `ε`, `τ` (by continuity of the entropy terms at 0), `k` and `N₀`. `isolation_fraction`:
for every `δ > 0` there are `k` and `N₀` such that every `S` with `N ≥ N₀` admits parameters
whose isolating fraction is at least `exp(−δN)`. `hamDecision_fraction` instantiates it with
`S = HC(G)`.

**Algorithm.** For each candidate `(m, d)`, polynomially many, repeat `t·exp(δ|E|)` times: draw
a hash and run the machine of `hamDecision_subexponential`. The only part not modelled in Lean
is this outer loop of independent trials, which turns "a fraction `≥ exp(−δ|E|)` of hashes
succeed" into "error `≤ e^{−t}`". Answer "yes"
if some run returns an odd count. The test never says yes wrongly (`parity_of_none`), and it fails
to find an existing Hamiltonian cycle with probability `≤ e^{−t}` (`parity_of_unique` plus the
lemma). The time is `2^{c(ε)|E| + O_{Δ,ε}(ρ(|E|+n))}`, where `|E| ≤ Δn/2` and `h` is binary
entropy. Since `h(2ε) → 0`, for every `δ > 0` a suitable `ε` gives time `2^{δn}` for all large
`n`.

**Trade-off.** This is weaker than §5, which gives `2^{O(ρ(n))}`. It is stronger in trust. Every step is checked in
Lean, conditional only on the top-level theorem. It does not use the paper's internal lemmas or
any unwritten bit-complexity adaptation.

## 6. Directed graphs [Lean for parity]

Use arc variables, with exactly one selected out-arc and one selected in-arc at each vertex, and
the same cut constraints on selected arcs. Models are cycle covers paired with consistent rooted
cuts, so the count is `Σ_{cycle covers X} 2^{cc(X)−1}`. The connected cycle covers are the
directed Hamiltonian cycles.

`DirectedHamiltonianParity.lean` proves `count_dirCutCNF_mod_two` by reusing the undirected parity
lemma on the underlying edge set. It also proves `dirHamParity_subexponential`, one machine for
all digraphs of maximum in- and out-degree `Δ`. On the complete digraphs `K₃` and `K₄` without
loops it evaluates to `(#models, #DHC, #cycle covers) = (2, 2, 2)` and `(12, 6, 9)`. For `K₄`,
the 3 covers by two 2-cycles contribute 2 each. Decision and search carry over from §5
unchanged.

## 7. Other Cut&Count problems on sparse graphs [conjectural sketch]

Cut&Count's recipe is local constraints, plus consistent rooted cuts over the solution's vertex
set, plus a cardinality counter, plus isolation. The cut must use Cut&Count's three states: a
vertex outside the solution (`x_v = 0`) is forced to `c_v = 0` and carries no free side.
Otherwise every solution picks up a factor `2^{n−|X|}` and the parity argument collapses. In the
setting of §5 each ingredient becomes a bounded-scope factor. Counters become extra powers of `y`,
so `ℓ` stays polynomial, and fixing the root inside the solution costs a factor `n` (try every
root).

This should cover Steiner Tree with any terminal set, Connected Vertex Cover, Connected Dominating
Set, and Longest Path or Cycle with at least `k` vertices. Each would run in randomized
`2^{O(ρ(n))}` on graphs with `O(n)` edges. I have not checked the details, so these are
conjectures, not results. For context: Bonnet's *fine-grained complexity days* slides list MIS,
Dominating Set, 3-Colouring, Vertex Cover, Feedback Vertex Set and Hamiltonian Cycle as needing
`2^{Ω(n)}` under ETH. ETH-based lower bounds for the connected variants and Steiner Tree are
plausible via linear reductions from Vertex Cover and Dominating Set, but I have not found them
cited. Feedback Vertex Set needs Cut&Count's marker formulation (Cygan et al., §3), which I have
not checked.

## 8. Why the exact count is out of reach (a small barrier) [Mine]

Every result above extracts `[X connected]` from `Σ_{c consistent} Π_v ω(v, c_v)`, a sum over
consistent colourings `c : V → [q]` with local weights. Componentwise, `X` contributes

```
Π_{components C ∌ r} h(C),     h(C) = Σ_{j∈[q]} Π_{v∈C} ω(v, j).
```

An **exact** filter needs `h(C) = 0` for every possible non-root cycle `C`.

**Claim.** Work over a field of characteristic 0. With vertex-uniform weights, `ω(v, j) = z_j`,
an exact filter for all graphs on `n` vertices forces `q ≥ n − 4`.

*Proof.* `z_0 ≠ 0`, since otherwise Hamiltonian cycles contribute 0; normalise `z_0 = 1`. The
root's own cycle has at least 3 vertices, so a non-root cycle has length `k ∈ {3, …, n−3}`. Every
such length occurs: in the disjoint union of `C_{n−k}` (containing `r`) and `C_k`, the only
2-factor is disconnected. So the filter needs `Σ_{j=0}^{q−1} z_j^k = 0` for `k = 3, …, n−3`.

Drop the `z_j` equal to 0, which contribute `0^k = 0`. Group the rest into distinct nonzero values
`λ_i` with positive integer multiplicities. This gives an exponential polynomial with at most `q`
distinct nonzero bases and positive coefficients that vanishes at `n − 5` consecutive integers. If
`n − 5 ≥ q`, the (scaled) Vandermonde matrix on those integers forces every coefficient to 0. That
is a contradiction, because `λ = 1` has multiplicity at least 1. ∎

Conversely, `q = n − 2` colours with `z_j = ζ^j`, `ζ` a primitive `(n−2)`-th root of unity, give
`Σ_j ζ^{jk} = 0` for `1 ≤ k ≤ n−3`. So the threshold lies in `[n−4, n−2]`.

Exact counting this way therefore needs about `log₂ n` bits per vertex and `Θ((n+|E|) log n)`
wires. That puts the exponent at `(n+|E|)√log n` up to `(log log)` factors, which is worse than
brute force. This is why the method gives counts modulo fixed `q` (§4) but not `#HC`. The positive
multiplicities are nonzero only in characteristic 0 (or larger than `q`), which is exactly how the
mod-2 and mod-`q` filters escape. Non-uniform weights are not covered by this argument, and I leave
that case open.

**Remark (why the decision stays randomized) [Mine].** The test only ever asks for the parity of
`|S ∩ H|`, with `S = HC(G) ⊆ {0,1}^N` and `H` a constraint on the edges. Suppose a fixed list
`H_1, …, H_F` gave an odd intersection for *every* nonempty `S ⊆ {0,1}^N`. Let `χ_i ∈ GF(2)^{2^N}`
be the indicator of `H_i`. Then no nonzero vector is orthogonal to all `χ_i`, so they span
`GF(2)^{2^N}` and `F ≥ 2^N`. Adaptivity does not help: the run on which every answer is "even" is
one fixed sequence of queries. So a deterministic subexponential test of this kind must use the
structure of Hamiltonian-cycle sets, not just that they are sets. CIKP-style isolation is
oblivious, which is why it needs randomness.

## 9. Files

* `lean/EthFollowup/CNFKit.lean`: generic local-constraint to CNF encoding, union and indexed-union
  evaluation, and relabelling that preserves the count and width.
* `lean/EthFollowup/HamiltonianParity.lean`: the Cut&Count CNF, `count_cutCNF`,
  `cuts_card_mod_two`, `count_cutCNF_mod_two`, `cutCNF_width`, and the machine theorem
  `hamParity_subexponential`.
* `lean/EthFollowup/HamiltonianAllGraphs.lean`: the counter encoding for unbounded degree
  (`count_bigCNF`, `bigCNF_width`, `card_bvar`, `hamParity_allGraphs`).
* `lean/EthFollowup/HamiltonianIsolation.lean`: Cut&Count restricted by an arbitrary edge CNF
  (`count_cutCNFWith_mod_two`, `parity_of_none`, `parity_of_unique`, `xorCNF`,
  `hamIso_subexponential`).
* `lean/EthFollowup/IsolationLemma.lean`: the CIKP isolation lemma for arbitrary finite sets,
  in counting form (`two_mul_card_separating`, `card_hash_nonempty`, `card_isolating_DA`,
  `isolation_count`).
* `lean/EthFollowup/HamiltonianDecision.lean`: hashes as edge CNFs, `decision_sound`,
  `decision_complete`, `hamDecision_subexponential`.
* `lean/EthFollowup/IsolationAnalysis.lean`: the entropy bound, the choice of parameters, and
  `isolation_fraction`.
* `lean/EthFollowup/HamiltonianDecisionFraction.lean`: `hamDecision_fraction` (success
  `exp(−δ|E|)`).
* `lean/EthFollowup/HashCNF.lean`: hashes as CNFs over any finite coordinate type.
* `lean/EthFollowup/DirectedHamiltonianDecision.lean`: directed decision (soundness, success
  `exp(−δ|A|)`, machine).
* `lean/EthFollowup/DirectedHamiltonianParity.lean`: the directed analogue
  (`count_dirCutCNF_mod_two`, `dirCutCNF_width`, `dirHamParity_subexponential`).
* `lean/EthFollowup/Examples.lean`: evaluated checks, run with `lake env lean`.
* `lean/EthFollowup/Axioms.lean`: the axiom audit.

## References (checked this session)

* Cygan, Nederlof, Pilipczuk, Pilipczuk, van Rooij, Wojtaszczyk, *Solving connectivity problems
  parameterized by treewidth in single exponential time*, FOCS 2011 (Cut&Count).
* Björklund, *An asymptotically fast polynomial space algorithm for Hamiltonicity detection in
  sparse directed graphs*, arXiv 2009.11780.
* Björklund, Husfeldt, *The parity of directed Hamiltonian cycles*, FOCS 2013, arXiv 1301.7250.
* Cygan, FPT school lecture 10 slides (fptschool.mimuw.edu.pl/slides/lec10.pdf), slide 21:
  "Unless ETH fails, there is no `2^{o(n+m)}` time algorithm for … Hamiltonian Cycle"; matches
  Cygan et al., *Parameterized Algorithms*, Ch. 14 (theorem number not confirmed).
* Lokshtanov, Marx, Saurabh, *Lower bounds based on the Exponential Time Hypothesis* (survey),
  Thm 3.3 (Hamiltonian Path).
* Björklund, Williams, ICALP 2019 (exponential-space `2^{n−Ω(n/δ)}` directed Hamiltonicity).
* Bonnet, *fine-grained complexity days* slides (perso.ens-lyon.fr/edouard.bonnet).
* The note was adversarially reviewed by an independent agent pass on 27 Oct 2026. Its findings
  (the §8 range, the TSP justification, the Appendix D scope, and the conditionality of 3/4′/5)
  are incorporated above.
* Calabro, Impagliazzo, Kabanets, Paturi, *The complexity of Unique k-SAT: an isolation lemma
  for k-CNFs*, CCC 2003 / JCSS 74(3) 2008, Lemma 3 and its proof (read this session).
* Mulmuley, Vazirani, Vazirani, *Matching is as easy as matrix inversion*, Combinatorica 1987
  (isolation lemma).
