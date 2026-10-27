# Findings: follow-ups to the OpenAI ETH refutation

Branch `eth-followup`. Written 27 Oct 2026 against the sources below. Every claim is tagged
**[Lean]** (proved in openai/math's Lean development), **[Paper]** (proved in the manuscript,
not in Lean), or **[Mine]** (my own derivation or extrapolation; not verified by anyone else).

## Update (27 Oct, later): Hamiltonicity

The headline new result is in `hamiltonicity.md`: Hamiltonian Cycle on sparse graphs is no
longer ETH-hard. The Lean results take OpenAI's theorem `exact_count_and_sat` as a hypothesis in
`lean/`. `lean-bridge/` discharges it: I built openai/math's proof from source (11,492 jobs; axioms
only `propext`, `Classical.choice`, `Quot.sound`), and the instantiated theorems
(`*_unconditional`) carry the same three axioms and no hypothesis. See README, *Independent
verification*. The mathematics of the upstream proof is still under expert review. Lean checks that
it proves the comparator statement, not whether that statement is the right formalisation.

* **Parity of the number of Hamiltonian cycles, every graph:** one machine,
  `2^{O(ρ(5|E|+3n))}` time, polynomial space. **[Lean]** (`hamParity_allGraphs`), via a Cut&Count
  CNF whose model count is `≡ #HC (mod 2)`. The directed version is also in Lean.
* **Deciding Hamiltonicity, maximum degree `Δ`:** for every `δ > 0`, randomized one-sided error,
  success `≥ exp(−δ|E|)` per trial. **[Lean], end to end**: a formal counting proof of the
  Calabro–Impagliazzo–Kabanets–Paturi isolation lemma for arbitrary sets, its entropy estimate,
  soundness, completeness and the machine. Only the loop of independent trials is not modelled.
* **Faster, paper-level:** randomized `2^{O(ρ(n))}` decision and TSP with polynomial weights for
  `|E| = O(n)`, via the paper's internal Prop. 3.4 over `ℚ[y]/(y^ℓ)` [Mine; reviewed].

An independent agent reviewed `hamiltonicity.md`, and its corrections are incorporated.

## 0. Sources checked

| Source | Identity |
|---|---|
| Manuscript `paper.pdf` (67 pp., "17 October 2026, revised 25 October 2026") | sha256 `5b1612dc…8123` |
| openai/math commit | `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` (26 Oct 2026) |
| `lean/docs/378.md` | sha256 `a2f7b390…31f79` |
| `lean/ComparatorChallenges/SubexponentialSAT.lean` | sha256 `4183b205…6685` |
| Lean proof directory | `lean/OAI/Algorithms/SubexponentialSAT/`, 3,977 `.lean` files, entry `SqrtLogSpace/Final.lean` |
| complexitylib issue #1226 | read in full (31 comments as of 27 Oct) |
| Williams, *Improving exhaustive search implies superpolynomial lower bounds* (full version, people.csail.mit.edu/rrw/improved-algs-lbs2.pdf) | Theorems 1.2, 3.4, 3.5, 6.1, Lemma 3.2 quoted below |
| Jahanjou–Miles–Viola, *Local reductions*, ECCC TR13-099 rev. 3 | Theorem 1, Corollary 2 quoted below |
| Golovnev–Kulikov, *Circuit depth reductions* (arXiv 1811.04828) | Theorem 2.1 (Valiant [Val77, Cal08, Vio09]) quoted below |

I did **not** build the Lean development (3,977 files; complexitylib also reports no outside
build). The `#print axioms` lines at the end of `SqrtLogSpace/Final.lean` are the authors' own
check. The comparator file is a statement template whose proof is `sorry`; the proof lives in
`SqrtLogSpace/Final.lean` (`exact_count_and_sat`, derived from `compiled_exact_count_and_sat`).

What the Lean theorem says, precisely (`exact_count_and_sat`, Final.lean): for each `k ≥ 2`
there exist a fixed machine and reals `C, A, S > 0`, naturals `d, e > 0`, chosen **before**
`n` and `F`, such that for every `k`-CNF `F` on `Fin n` the machine halts with the exact count
in time `≤ C (L+1)^d 2^{A · n (log log(n+16))² / √log(n+16)}` (natural logs, `L` = encoding
length) and visits `≤ S (L+1)^e` cells at every prefix. So `O_k` means: `A = A(k)` exists, with
no explicit formula exported by the statement.

---

## 1. Task 1 (gatekeeper): how the constants depend on k

### 1.1 Which algorithm is which

The manuscript contains three algorithms with different `k`-behaviour:

| Route | Where | Time exponent (log₂ of time, up to poly factors) | Status |
|---|---|---|---|
| **R1** interpolation on the original variables (sparsify → Tanner parity tests → greedy tests → Thm 2.2 counter) | §§3–6, App. A–B, Prop. 6.4 | `O_k(ρ(n))`, `ρ(n) = n (log log n)²/√log n` | **[Lean]** (this is the comparator bound) |
| **R2** tensor contraction, fixed density `m ≤ Dn` | App. D.2, Thm D.1 | `O_{k,D}(n/√log n)` | **[Paper]** only |
| **R3** tensor contraction, arbitrary density (sparsify → parity tests → Lemma D.2) | App. D.3 | `O_k(n log log n/√log n)` | **[Paper]** only |
| **R0** "weaker" route: sparsify, then Tovey copy to 3-occurrence 3-CNF | §2.8 | `O_k(n (log log n)^{k+1}/(log n)^{1/(2k)})` | [Paper], superseded |

### 1.2 Route R1 (the Lean-verified bound): exponent ≈ c · k · (k + O(1)) · ρ(n)

Chain of dependence, with manuscript locations:

1. **Sparsification** (Lemma 6.3, App. A.3, pp. 46–47). With `σ = 1/s`, `s = ⌊√λ/ν²⌋`,
   `λ = ⌈log₂ n⌉`, `ν = ⌈log₂ λ⌉` (Prop. 6.4, p. 43). The branching threshold `M` is the least
   power of two `≥ Γ = 2(3^{k-1} − 1)` with `Γ ⌈log₂(4CM)⌉ ≤ σM`, `C = 4 Σ_{j≤k-2} (3M)^j`.
   Solving: `M ≈ 2(k−1)·3^{k−1}·s·log₂ s · (1+o(1))`, i.e. `M = Θ(k 3^k √log n / log log n)`.
   Leaf occurrence bound `B = 2Σ_{j<k} M^j ≤ 4M^{k−1}` (p. 47), so
   `log₂ B ≈ (k−1)(log₂ k + 1.58 k + ½ log₂ λ)` — **the `3^{k²}` lives here** [Mine, from the paper's formulas].
   The tree has `(Cn+1)² 2^{σn}` nodes: the exponent `σn = n ν²/√λ` is **k-free**; `k` enters only
   the polynomial factor `(Cn)²` with `C = O((3M)^{k−2})`.
2. **Tanner code** (Lemma 6.1, p. 40): `P = 20000 B² µ²`, `D0 = 320000 B² µ³`, `µ = ⌊log₂ m⌋+1`.
   Deterministic exhaustive searches cost `exp(poly(B, log m))`; concretely the local-code search is
   `2^{c_G d_G} = 2^{Θ(D0²/B)} = 2^{Θ(B³ µ⁶)}`. Polynomial in `n` only while `3 log₂ B < λ`.
3. **Greedy test selection** (Lemma 6.2, p. 42): `3n(2m)^P` counter calls per leaf, i.e.
   `2^{Θ(P log m)} = 2^{Θ(B² λ³)}` calls. Polynomial in `n` only while `2 log₂ B < λ`.
4. **Theorem 2.2 inputs** (§6.3, §5.5, pp. 38–39, 43): each test has `≤ 2^k max(D0,P)`
   monomials, scope `w ≤ k·max(D0,P) = k·D0`, so `w = (log n)^{k+2+o(1)}·2^{O(k²)}`; after branching on
   heavy variables the incidence bound is `b ≤ b0 = ⌈M'/n⌉⌈√λ⌉ ≈ 6w√λ`. Lemma 4.8 needs
   `b, w ≤ λ^β`; hence **`β ≈ k + 3.5 + 1.58k²/log₂λ`** (for fixed `k` and large `n`, `β → k + 4` after ceiling).
5. **Lemma 4.8 parameters** (p. 34): `r = ⌊√λ/ν²⌋`, `Q = ⌊λ/(128ν)⌋`, `R = (β+3)⌈√λ⌉`,
   `τ = 1/(rλ)`, `D = r^{2Q} ≤ 2^{λ/128}`. The three costs (3.16), p. 26, are
   `(R/Q) log(2Q/R) + τ log(2D+1) + 1/r`; only the first depends on `β`, linearly.
6. **Degree** (5.5), p. 37: `d_H = kR(m_test + 2(ℓ−1)) ≤ 8knR` because the lifted tests have
   degree `k` and `m_test ≤ 6n`, `ℓ = n+1`. The Taylor cost `log C_q` (3.15) is
   `≤ q log(Q/R) + 2nR/Q` with `q = d_H/Q`, so it carries **a second factor `k`**.

Putting 5 and 6 together, the dominant term of the exponent of R1 is

```
log₂ time  ≲  c₀ · k · (β+3) · n (log log n)² / √log n  +  (lower-order k-free terms  n ν²/√λ from 1/r and τ log(2D+1))
           ≈  c₀ · k · (k + 7) · ρ(n)             with c₀ an absolute constant (≈ 8·128·(ln 2)/2 in natural-log units; not optimised)
```

So **`A(k) = Θ(k²)`** for the manuscript's parameter choices **[Mine, derived from the paper's
displayed formulas]**. Two remarks:

* The `R = (β+3)⌈√λ⌉` choice is wasteful: the tail bound only needs `R²/(8Q) ≥ (β+2)ν ln 2`,
  i.e. `R = Θ(√(βλ))`, which would make the Taylor cost `Θ(k√β)` and so `A(k) = Θ(k^{3/2})` [Mine].
* The `3^{k²}` from sparsification does **not** enter the exponent of `n`; it enters the
  threshold `n₀(k)` beyond which the asymptotics hold (`n₀(k) ≥ 2^{Ω(k²)}`) and the polynomial
  factors.

**Where the Lean development stands on this.** Lean exports no formula for `A`, but the pieces
are visible:

* `SqrtLog/CostAssemblyFinal.lean:53`:
  `exponentConstant (k q : ℕ) : ℝ := 707 + 4*(384*((k*30*(256*(28*q+312))) + 1) + 1)`
  ≈ `3.3·10⁹ · k · q`, where `q` is the polylog degree of the leaf occurrence/scope bound
  (the paper's `β`; see `ProducedQueryRuntimeBound.runtimeExponent`, which feeds
  `exponentConstant k (resourceExponent qi + 1)`). This confirms the product structure `k·β`.
* Lean's sparsifier is **not** the manuscript's Appendix A.3 accounting. `SparsificationConstants.lean`
  (used by `SqrtLog/SparsifyDyadic.lean:29`) defines `L M (j+2) = (j+1)! · (M·C M (j+1) − 1)^{j+1}`
  and `occurrenceCap M k = 2 Σ_{j≤k} L M j`. Evaluating the definitions numerically gives
  `occurrenceCap M k = Θ(M^{(k−1)·(k−1)!})` (`M^1, M^4, M^18, M^96, M^600` for `k = 2..6`), versus the
  paper's `4M^{k−1}`. So in Lean `β_Lean = Θ((k−1)·(k−1)!)` and the exported constant grows at
  least like **`A_Lean(k) = Ω(k · k!)`** [Mine, from the Lean definitions; the outer `Classical.choose`
  exponents `markedExponent k`, `acceptedExponent k` in `SqrtLog/OuterNativeKernels.lean` are
  non-constructive, so this is a lower bound on what the Lean proof can export, not the exact value].
  For fixed `k` this is irrelevant; for `k = k(n)` it is far more restrictive than the paper.

### 1.3 Does R1 survive for k = k(n)?

Constraints, in order of bite (paper parameters, with `λ = log₂ n`):

| Constraint | Source step | Condition |
|---|---|---|
| exponent must be `o(n)` | step 5–6: `k(β+3) ν² ≪ √λ` with `β ≈ k` | **`k = o((log n)^{1/4} / log log n)`** (paper's `R`); `k = o((log n)^{1/3}/(log log n)^{4/3})` with optimised `R` |
| Tanner search polynomial | step 2: `3 log₂ B < λ`, `log₂ B ≈ 1.58k²` | `k ≲ 0.46 √(log₂ n)` |
| greedy calls `2^{o(ρ)}` | step 3: `2 log₂ B < λ` | `k ≲ 0.56 √(log₂ n)` |
| Lemma 4.8 balance `2(b+w)D² ≤ M'` | `β log₂ λ ≤ (63/64) λ` | `k ≲ λ/log λ` (never binding) |
| Lean route | `β_Lean = Θ(k·k!)` | `k = O(log log n / log log log n)` |

**Answer to the gatekeeper question (R1): the method does not survive `k = log n`, let alone
`k = n^ε`.** Even ignoring the exponent, the deterministic Tanner/greedy constructions stop being
polynomial at `k ≈ 0.46√log₂ n` because the sparsification constant `B` is `2^{Θ(k²)}`. The
binding constraint is the exponent itself: the algorithm is subexponential only for
`k = o((log n)^{1/4}/log log n)`. **[Mine]**

### 1.4 Route R2 (fixed density, Appendix D.2): k enters only linearly, and width can be unbounded

Theorem D.1 (p. 53) is stated with **no `k` at all**: a bipartite Boolean tensor network with
`≤ Cs` edges, max degree `≤ ⌈s^{9/10}⌉`, poly(s) vertices, entries in `(ℤ/2^{P₀})[V]/(V^ℓ)` with
`P₀, ℓ ≤ Cs`, entries computable in time `(s+L)^b 2^{A s^{9/10}}`, is contracted in time
`(s+L)^{O(1)} 2^{O(s/√log s)}` with constants depending only on `C, A, b`.

The clause network of D.2 (p. 54) has one clause vertex of degree `≤ k` per clause and equality
trees for variables: `≤ km` clause ports, the equality trees add `≤ km` internal edges, and the
subdivision doubles, so **`≤ 4km` edges** [Mine, counting the construction on p. 54]. A clause wider
than `s^{9/10}` is first split into a tree of trivalent OR tensors (still `O(k)` wires, no new summed
variables), which keeps the max-degree hypothesis. Taking `s := 4km + n` (so `P₀ = n+1 ≤ s`) and `C := 1`:

> **Corollary (width-free form of Thm 1.1's density bound) [Mine, immediate from Thm D.1 as
> stated].** Let `F` be a CNF on `n` variables of total length `N = Σ_C |C|` (any widths). Then `#F`
> is computable deterministically in time `poly(n+N) · 2^{c (n+N)/√log(n+N)}` and polynomial
> space, for an **absolute** constant `c`. Requirements: `k ≤ s^{9/10}` (always), entry evaluation
> trivial (OR of literals).

Consequences: for `m ≤ Dn` the exponent is `c(1 + 4kD)·n/√log n` — the `O_{k,D}` of Theorem 1.1
is **linear in `kD`**; the method survives **any** `k = k(n)` as long as `N = o(n√log n)`
(e.g. `k = √log n / ω(1)` at `m = n`, or `k = log n` at `m = n/log n`). It fails for
`k = n^ε` at `m ≥ n` (then `N ≥ n^{1+ε}`). The paper only states the fixed-`k`, fixed-`D` version
(p. 54: "exponent `O_{k,D}(n/√log n)`").

The same reading gives `#Circuit-SAT` for fan-in-2 circuits with `S` gates in `2^{O(S/√log S)}`
(a gate is a degree-3 tensor; this is what Cor. 1.4 uses via a 3-CNF encoding).

### 1.5 Route R3 (arbitrary density, Appendix D.3)

Lemma D.2 (p. 54) inherits the sparsification/Tanner/greedy constants of R1 (so the same
`k ≲ 0.46√log₂ n` ceiling), and its wire count is `M ≤ J² + K log₂(e(N+K)/K)` with
`K = k(a + 2(ℓ−1)) ≤ 8kn` and `N ≤ 6nk·2^k·B²λ³` ((D.1), (D.3), p. 55). Hence
`M ≈ 8kn(k + 3)ν + O(k³ n)` and the exponent is **`O(k² n log log n/√log n + k³ n/√log n)`**
[Mine]. Subexponential iff `k = o((log n)^{1/4}/√log log n)`.

### 1.6 Summary table for Task 1

| Route | exponent (log₂ time, leading term) | k-regime where time is `2^{o(n)}` | verified |
|---|---|---|---|
| R1 interpolation | `c₀ k(k+7) · n(log log n)²/√log n` (paper), `Ω(k·k!)·ρ(n)` (Lean) | `k = o((log n)^{1/4}/log log n)` | Lean (fixed k) |
| R2 tensor, length `N` | `c (n+N)/√log(n+N)`, `c` absolute | `N = o(n√log n)`, any width | paper only |
| R3 tensor, any density | `c k² n log log n/√log n` | `k = o((log n)^{1/4}/√log log n)` | paper only |

**Decision for later tasks**: anything needing width `≥ (log n)^{1/4}` with `≥ n` clauses (in
particular Valiant-style width `n^ε` CNFs, Task 5) is out of reach of all three routes; anything
that reduces to a CNF/tensor network of **linear total length** is in `2^{O(n/√log n)}` via R2;
anything with bounded width and arbitrary density is in `2^{O(n log log n/√log n)}` via R3, or
`2^{O(ρ(n))}` if we insist on the Lean-verified bound.

---

## 2. Task 2: easy corollaries

Direction matters. SERF reductions in Impagliazzo–Paturi–Zane go **from** 3-SAT **to** the target
problems (that is how ETH transfers hardness to them). For algorithms we need the reverse: a
reduction from the target to fixed-width CNF (or to a tensor network) that keeps the number of
Boolean variables linear in the natural parameter. The table lists what the three routes give.
`v` = vertices, `e` = edges, `ρ(n) = n(log log n)²/√log n`. "R1" bounds are **[Lean]**-backed for
fixed `k` (the comparator theorem applied to the encoding; the encodings themselves are my
reductions, two of them formalised in this repo). "R2/R3" bounds are **[Paper]** + the width-free
reading of Theorem D.1 in §1.4 **[Mine]**.

| Problem | Encoding (variables / width / clauses) | Exact counting time | Notes |
|---|---|---|---|
| Independent Set (#IS) | `v` / 2 / `e` clauses `¬x_u∨¬x_v` | R1: `2^{O(ρ(v))}` any density; R2: `2^{O((v+e)/√log(v+e))}` | paper Cor. 1.3; **formalised** in `lean/EthFollowup/IndependentSet.lean` (`count_indepCNF`, `indepSet_count_subexponential`) |
| Vertex Cover (#VC) | `v` / 2 / `e` clauses `x_u∨x_v` | same as IS | **formalised** (`count_coverCNF`, `vertexCover_count_subexponential`) |
| Clique (#Clique) | IS in the complement: `v` / 2 / `C(v,2)−e` | R1: `2^{O(ρ(v))}` (density forces R1/R3, not R2) | |
| `q`-Coloring (#q-Col), fixed `q` | `qv` / `q` / `v + e·q + v·C(q,2)` | R1 with `k = q`: `2^{O_q(ρ(v))}`; R2: `2^{O(q(v+e)/√log)}` | paper Cor. 1.3 |
| Set Splitting, sets of size `≤ k` | one var per element / `k` / `2·#sets` | R1: `2^{O_k(ρ(N))}`, `N` = universe size | paper §1.1.3 |
| Dominating Set (#DS), max degree `Δ` | `v` / `Δ+1` / `v` | R1 with `k = Δ+1` (fixed `Δ`); R2 for any `Δ`: `2^{O((v+e)/√log(v+e))}` since total length is `2e+v` | **width-free R2 is what makes general sparse graphs work** [Mine] |
| Dominating Set, dense graphs | width unbounded, total length `Θ(e)` | **not covered**: R2 needs `v+e = o(v√log v)`; R1/R3 need width `o((log v)^{1/4})`; a circuit encoding of the big ORs costs `Θ(e)` auxiliary variables | open |
| Perfect matchings (#PM) | one var per edge, "exactly one" per vertex | R2: `2^{O(e/√log e)}` directly (degree-`d` "exactly-one" tensors); paper Cor. 1.3 gives `2^{o(v+e)}` via circuit-to-3-CNF | refutes Curticapean's #ETH-based bound at `e = O(v)` (paper §1.1.2) |
| Hamiltonian Path/Cycle | Cut&Count CNF: `|E|+n` vars / `max(Δ,3)` / `O(n2^Δ+|E|)` | parity: deterministic `2^{O(ρ(n+|E|))}`; decision: randomized `2^{O_D(ρ(n))}` for `|E| ≤ Dn` | **see `hamiltonicity.md`**; parity identity **formalised** (`HamiltonianParity.lean`). The earlier "not covered" verdict was wrong: Cut&Count gives a linear-size encoding modulo 2 |
| Max-Cut / Max-2-SAT (exact, linear `e`) | see Task 6: generating-polynomial ring | R2: `2^{O((v+e)/√log(v+e))}` | [Mine, §6] |

Explicit forms, e.g. for #IS on a graph with `v` vertices and `e` edges (encoding length
`L = O((v+e) log v)`):

* R1 (Lean-backed for the fixed machine at `k = 2`): `time ≤ C (L+1)^d 2^{A ρ(v)}` with the
  `k = 2` constants of `exact_count_and_sat`.
* R2 (paper, width-free reading): `time ≤ poly(v+e) 2^{c (v+e)/√log(v+e)}`, absolute `c`.

For sparse graphs (`e = O(v)`) R2 is strictly better: `2^{O(v/√log v)}` vs `2^{O(v (log log v)²/√log v)}`.

### 2.1 What was formalised

`lean/EthFollowup/Comparator.lean` is a verbatim copy of openai/math's comparator file with the
`sorry`'d theorem turned into `ExactCountAndSatStatement k hk : Prop` (no axioms added, no `sorry`).
`lean/EthFollowup/IndependentSet.lean` proves, unconditionally:

* `count_indepCNF : SAT.count (indepCNF G) = (indepSets G).card`
* `count_coverCNF : SAT.count (coverCNF G) = (vertexCovers G).card`
* `indepCNF_width / coverCNF_width : WidthAtMost 2 _`

and, **conditional on the upstream theorem at `k = 2` passed as a hypothesis**,
`indepSet_count_subexponential` and `vertexCover_count_subexponential`: one fixed machine, run on
`encodeCNF (indepCNF G)`, halts with the number of independent sets on its count tape within the
comparator's time bound and polynomial visited space at every prefix. `lake build` succeeds and
`#print axioms` (`EthFollowup/Axioms.lean`) reports only `propext, Classical.choice, Quot.sound` for all
four theorems (no `sorryAx`). Linking the hypothesis to
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` is done in `lean-bridge/`. I
later built openai/math's development from source (11,492 jobs, standard axioms only).
`indepSet_count_subexponential_unconditional` builds against it with only `propext`,
`Classical.choice` and `Quot.sound` (README, *Independent verification*).

---

## 4. Task 4: where the √log n comes from, and a barrier for the method

### 4.1 Route R1 (interpolation): the label set `D = r^{2Q}`

Exponent per unit `n` (eq. (3.16), p. 26): `E = (R/Q)·log(2Q/R) + τ·log(2D+1) + 1/r`. The
constraints that tie the parameters together (all from §4):

1. **Balance** (Lemma 4.5, (4.13)): `2(b+w)D² ≤ M ≈ n`, with `D = r^{2Q}` (4.2). Hence
   `2Q·log₂ r ≤ ½ log₂ n − O(β log log n)`.
2. **Tail** (Lemma 4.7, (4.8)): `Pr[Bin(Q, (r−1)/2r) ∉ I] ≤ τ/(rb)`, `|I| = R`. Hoeffding is tight
   up to constants here, so `R ≥ c√(Q·(β ν + log r))`.
3. **Taylor**: `(R/Q)·log(2Q/R) ≥ √((βν+log r)/Q) · Ω(log(Q/R))`.

Substituting 1 into 3: `(R/Q)log(2Q/R) ≥ Ω(√((βν)(log r)/λ) · ν)`. Together with the `1/r` term,

```
E ≥ Ω( 1/r + ν^{3/2} √(β log r / λ) ) ≥ Ω( ν^{3/2} √β / √λ )      for every r ≥ 2.
```

So **every instantiation of Definition 3.1 produced by the §4 construction has exponent
`Ω(n (log log n)^{3/2}/√log n)`**; the paper's `n(log log n)²/√log n` is within a `√log log n`
factor of the best this design can do **[Mine]**. The single culprit is `D = r^{2Q}`: the auxiliary
coordinate set is the full product `([r]^Q)²` of all group schedules (4.2), because the
commuting-swap eigenbasis argument of Lemma 4.1 needs the tensor-product structure, and Lemma 4.5
needs `D² ≲ n` to place `≤ 2M/D` incidences per label. This forces `Q·log r ≲ log n`, i.e. "few
interpolation points **or** few groups", and the `√` is the geometric mean of the two costs.

**What would break it.** A family of replacement rows with the properties of Lemma 4.3 (degree
`R ≪ Q`, kernel condition at every `t ∈ [Q]`, `≤ ϵD` measurement rows with `{0,±1}` entries) but
with coordinate count `D = poly(r, Q)` instead of `r^{2Q}`. Then `r = Q = n^{ε}` would be allowed and
`E = Õ(n^{−ε/2})`, i.e. a `2^{n^{1−ε/2}}`-time `#k`-SAT algorithm. I see no reason this is impossible
and no construction; it is the sharpest open question this analysis produces. The obstacle is that
Lemma 4.2's support bound comes from expanding `f_I(W₀)` in products of `≤ R−1` swaps, which needs
`Q` independent commuting involutions — the label set is exactly the product of their orbits.

### 4.2 Routes R2/R3 (tensor contraction): the number of 2-adic levels

Theorem D.1's recursion (D.4.2–D.4.7) deforms wires over the integer grid `S = {−L,…,L−1}` with
`L = 2^a`, and at a node `t` of 2-adic valuation `i < u` expands cross-group interactions in
"modes" of weight `b+1` whose coefficients are divisible by `2^{b+1}` (D.12). Children per active
call: `exp(O(√(M p_t / D_t)))` (D.15) with `p_t = Θ(M D_t/u)` (D.11), i.e. `exp(O(M/√u))`, where
`u` is the number of valuation levels that carry positive Hermite multiplicity.

Two facts pin `u`:

* `u ≤ a = log₂ L` (levels are valuations of differences inside the grid), and `L ≤ ∆ ≤ s^{9/10}`
  because the new packet vertex has `2L` ports and its entry costs `exp(O(L log s))` (D.4.6). So
  **`u = O(log s)`**, hence `exp(Ω(M/√log s))` children at the root.
* The precision loss `Θ(M D/u)` is optimal for *any* multiplicity profile `q(·)` on `u` levels
  [Mine]: Hermite needs `Σ_i q(i)·L/2^{i+1} ≥ 3ML` (p. 60), so `q(0) = Ω(M)`; `q` decreases to `0` at
  level `u`, so some decrement `q(i) − q(i+1) ≥ Ω(M/u)`; by (D.10) the loss at that level is
  `Ω(D_i · M/u)`, and the mode count there is `exp(Ω(√(M · M/u)))`.

So **within the 2-adic Cauchy-deformation framework the exponent is `Ω(s/√log s)`**, matching the
theorem. Beating `2^{n/(log n)^c}` for `c > 1/2` would need either `ω(log s)` usable "levels" (a
different valuation structure; a totally ramified extension gives finer valuations but not more
levels per grid size), or a recovery scheme whose loss is `o(MD/u)` (ruled out above for Hermite
with any taper), or a deformation whose cross-group terms are not organised by a single valuation.

### 4.3 Verdict

Both routes are stuck at `n/√log n · polylog` for structural reasons, and the two obstructions are
different (`D = r^{2Q}` vs. `u ≤ log₂ L`). `2^{n/(log n)^c}` with `c > 1/2` requires a new idea in
one of the two places named above; nothing in the manuscript suggests the constant `1/2` is an
artefact of bookkeeping. **[Mine]**

---

## 5. Task 5 (moonshot): circuit lower bounds

### 5.1 Statements verified from primary sources

Williams, *Improving exhaustive search implies superpolynomial lower bounds*, full version
(people.csail.mit.edu/rrw/improved-algs-lbs2.pdf), pp. 11, 20–21, verbatim:

> **Theorem 1.2** If CIRCUIT SAT on n variables and m gates is in O(2^{(1−δ)n} poly(m))
> (co-non)deterministic time for some δ > 0, then there is ε > 0 and a language in E^NP that does not
> have 2^{εn} size circuits.

> **Lemma 3.2 (Folklore)** Let C be any class of circuits. If E^NP has (non-uniform) circuits of size
> S(n) from class C, then NTIME[2^n] has universal witness circuits of size S(n) from class C.

> **Theorem 6.1** If the Exponential Time Hypothesis is false, then E^NP does not have linear size
> circuits.

(The proof of Theorem 6.1 is a sketch in the paper; the manuscript's Cor. 1.4 proof, p. 51–52,
redoes it quantitatively with JMV's local reduction.)

Jahanjou–Miles–Viola, *Local reductions*, ECCC TR13-099 rev. 3, p. 2–3, verbatim:

> **Corollary 2.** For each of the following classes C, if the satisfiability of circuits in C can be
> solved in time 2^n/n^{ω(1)} then there is a problem f ∈ E^NP that is not solvable by circuits in C:
> (1) linear-size circuits, (2) linear-size series-parallel circuits, (3) linear-size log-depth
> circuits, (4) quasi-polynomial-size SYM-AND circuits.

> **Corollary 3.** In Items (1), (2), and (3) of Corollary 2 we can substitute, respectively, the
> following assumptions: (1′) The exponential time hypothesis (ETH) [IP01] is false; i.e., for every
> ǫ > 0, 3SAT is in time 2^{ǫn}, (2′) The strong exponential time hypothesis (SETH) is false [IP01];
> i.e., there is ǫ < 1 such that for every k, kSAT is in time 2^{ǫn}, (3′) there is α > 0 such that
> n^α-SAT is in time 2^{n−ω(n/ log log n)}.
> ("a kSAT instance has n variables and O(n)^k clauses.")

Valiant's depth reduction, as stated in Golovnev–Kulikov (arXiv 1811.04828, Theorem 2.1, citing
[Val77, Cal08, Vio09]), verbatim:

> For every c ≥ 1 and ε > 0 there exists a δ > 0 such that every circuit C of size cn and depth
> c log n can be computed as (1) an OR_{2^{δn/log log n}} ∘ AND ∘ OR_{n^ε} circuit, (2) and as an
> OR_{2^{εn}} ∘ AND ∘ OR_{2^{(log n)^{1−δ}}} circuit.

So the brief's "OR of `2^{O(n/log log n)}` CNFs of width `n^ε`" is item (1), with the AND fan-in
(number of clauses) unbounded — each depth-reduced output is an arbitrary function of `n^ε` inputs,
i.e. up to `2^{n^ε}` clauses.

### 5.2 Parameter check against Task 1

| Lower-bound target | Algorithm needed (verified statement) | What the ETH paper supplies | Gap |
|---|---|---|---|
| `E^NP ⊄ SIZE(O(n))` | JMV Cor. 2(1): SAT of linear-size circuits in `2^n/n^{ω(1)}` | R2 on the circuit's own tensor network: `2^{O(S/√log S)}` for size `S` (any depth) | **achieved**; paper Cor. C.1 |
| `E^NP ⊄ SIZE(c n√log n)` | same, with size `S = N√log N/c'` | R2 exponent `cS/√log S ≤ N − ω(log N)` iff `S ≤ N√log N/c'` | **achieved**; paper Cor. 1.4 (p. 51–52) |
| `E^NP ⊄` linear-size **log-depth** (JMV Cor. 2(3)) | either SAT for that class in `2^n/n^{ω(1)}`, or Cor. 3(3′): `n^α`-SAT in `2^{n−ω(n/log log n)}` | already implied by the previous row (log-depth linear circuits are linear circuits) | **achieved, and Valiant's depth reduction is unnecessary**: R2 contracts the circuit directly, so the depth-3 normal form buys nothing [Mine] |
| `E^NP ⊄ SIZE(n^{1+ε})` | Circuit-SAT for `N` inputs and `S = N^{1+ε}` gates in `2^N/N^{ω(1)}` (JMV framework) | R2: `2^{O(N^{1+ε}/√log N)}` ≫ `2^N` | **out of reach**: the exponent must scale with the number of *input* bits, not with the circuit size |
| `E^NP ⊄ SIZE(2^{εn})` | Williams Thm 1.2: Circuit-SAT in `2^{(1−δ)N} poly(S)` for poly-size `S` | as above | out of reach |
| the `n^α`-SAT route (Cor. 3(3′)) | width `n^α`, up to `2^{n^α}` clauses, time `2^{n − ω(n/log log n)}` | R1: width `o((log n)^{1/4})`; R2: total length `o(n√log n)` | width gap `n^α` vs `(log n)^{1/4}`; length gap `2^{n^α}` vs `n√log n` |

**Conclusion.** The moonshot as phrased (Valiant + Williams) reproduces exactly what the paper
already has (Cor. 1.4), because the method handles *unrestricted* linear-size circuits natively and
the depth reduction only matters when one can solve wide CNFs, which the method cannot. The
genuinely new target this exposes is:

> **Needed:** a `#CNF`/tensor algorithm whose exponent is `o(n_free)` where `n_free` counts the
> *free* variables, in the presence of `poly(n)` auxiliary variables that are *functions* of the free
> ones (gate variables of a size-`n^{1+ε}` circuit). Equivalently, projected counting
> `#{x : ∃y φ(x,y)}` for a 3-CNF `φ` with `|y| = n^{1+ε}` and `y` determined by `x`, in time
> `2^{(1−δ)|x|}`.

Both routes charge for every variable (R1: group size `2n/r` over all `n`; R2: every wire), so this
needs a structural change, not parameter tuning. Williams's footnote 6 (p. 3) notes that even for
general CNF-SAT no algorithm "of the kind required in Theorem 1.2 is known"; the ETH paper does not
change this because its savings vanish once width or total length grows.

---

## 6. Task 6: neighbouring problems

All items here are **[Mine]** unless marked; each is a reading of Theorem D.1 / §3's "any commutative
`ℚ`-algebra" remark (p. 21) rather than a new technique.

### 6.1 Exact Max-k-SAT and the full satisfied-clause distribution — linear density: yes

Theorem D.1 allows entries in `B_{P₀,ℓ} = (ℤ/2^{P₀})[V]/(V^ℓ)` with `ℓ ≤ Cs`. Put `ℓ = m+1`,
`P₀ = n+1`, and give clause `c` the tensor entry `V^{[c satisfied]}` (equivalently `1 + (V−1)·sat_c`).
The contraction is `Σ_x V^{#sat(x)} mod (2^{n+1}, V^{m+1})`: every coefficient is `≤ 2^n`, so this
is the exact distribution of the number of satisfied clauses over all `2^n` assignments.
`OPT(F)` is the largest exponent with nonzero coefficient and the coefficient is the number of
optimal assignments. Time `poly · 2^{O((n+km)/√log(n+km))}`; for `m ≤ Dn`, `2^{O(n/√log n)}` with the
constant linear in `kD`. This upgrades Cor. 1.2 (randomized, additive `εm` error) to **exact,
deterministic Max-k-SAT and #Max-k-SAT at linear density**. Special cases: exact Max-Cut and
Max-2-SAT on graphs with `e = O(v)` edges in `2^{O(v/√log v)}`.

The same works in R1 at linear density (coefficient algebra `A = ℚ[V]/(V^{m+1})`, factor degree
`≤ km = O(n)`, heavy-variable branching as in §5.5), giving `2^{O_{k,D}(ρ(n))}`; the bit-size bounds
of App. B would have to be redone for these factors (straightforward: entries are `0/1`).

### 6.2 Exact Max-k-SAT at arbitrary density: open under this method

Sparsification preserves the set of satisfying assignments, not the satisfied-clause counts, and the
parity tests of §6 detect violations mod 2 rather than counting them. Without sparsification the
generating polynomial has degree `km`, which is `polylog(n)·n` or worse, breaking the Taylor budget
`d = O(n)` of Prop. 3.4 and the wire budget `O(n log log n)` of Lemma D.2. I see no fix; Cor. 1.2's
additive-error approximation remains the best this method gives at high density.

### 6.3 Weighted counting, #CSP, partition functions — sparse instances: yes

For `Z = Σ_x Π_c w_c(x|_{S_c})` with `|S_c| ≤ k`, `m` constraints, integer weights `0 ≤ w_c ≤ W`:
tensor entries `w_c mod 2^{P₀}` with `P₀ = n + 1 + ⌈m log₂(W+1)⌉`. Theorem D.1 as stated needs
`P₀ ≤ Cs`, fine for `W = O(1)`. For `W = poly(n)` the precision is `O(s log s)`; the proof's
precision bookkeeping (D.11) allows a root precision `s·λ^{O(1)}` ("this extra factor `2^u`
dominates every fixed power of `λ`", p. 61), so the same proof covers polynomially bounded weights
with no change to the exponent. Rational weights: clear denominators; negative weights: shift.
Hence **arity-`k` #CSP with poly-bounded weights and `m = O(n)` constraints in `2^{O(n/√log n)}`**,
which includes Ising/Potts/Tutte-type partition functions on sparse graphs — the problems whose
`2^{Ω(v)}` lower bounds Dell–Husfeldt–Marx–Taslaman–Wahlén derived from #ETH (the paper already
notes #ETH is refuted, §1.1.2). Dense instances (`m = Θ(n²)`) are not covered (same reason as 6.2).

### 6.4 Gap-3-SAT, random instances, and what is *not* covered

* Gap-3-SAT is decided outright (exact SAT), as the paper states (§1.1.1). Nothing further to do.
* Random `k`-SAT: the worst-case bound applies; nothing problem-specific.
* Projected counting `#∃`, QBF, and anything where the exponent must count only *some* of the
  variables: not covered (see §5.2).
* Width growing with `n` beyond `(log n)^{1/4}` with `≥ n` clauses: not covered (Task 1).

---

## 7. Recommended next steps, in order of expected value per effort

0. **Done after this memo:** Hamiltonicity on sparse graphs (`hamiltonicity.md`): parity
   deterministic and Lean-backed, decision randomized via Prop. 3.4 with isolation.

1. **Lean (cheap, high value for the catalogue):** wire `EthFollowup/IndependentSet.lean` to the
   upstream theorem by adding openai/math as a `lake` dependency, so `indepSet_count_subexponential`
   becomes unconditional; then add `q`-coloring and Set Splitting the same way (both are
   count-preserving encodings with `qv` / `N` variables).
2. **Paper-level, new theorem with a short proof:** write up §1.4 + §6.1 + §6.3 as corollaries of
   Theorem D.1: width-free `#CNF` in `2^{O(N/√log N)}`, exact Max-k-SAT and weighted #CSP at linear
   density. These are genuinely not stated in the manuscript and they refute natural "Max-SAT ETH"
   and "#CSP ETH" style hypotheses at linear density. Risk: depends on Theorem D.1, which is **not**
   Lean-verified.
3. **Proof complexity (medium):** prove the soundness-only statement of §3.4; then attempt PV
   formalisability of the counter's correctness. A positive answer gives `2^{o(n)}` EF refutations of
   random 3-CNFs.
4. **Exponent (hard):** search for replacement designs with `D = poly(r,Q)` (§4.1). This is the one
   place where a new construction would give `2^{n^{1−δ}}`.
5. **Circuits (hard, likely blocked):** projected counting with exponent `o(n_free)` (§5.2). I would
   not start here.
