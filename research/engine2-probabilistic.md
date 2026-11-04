# The engine rate, probabilistic / structural side: six mechanisms, two new negative theorems, one ranking

4 Nov 2026. Companion to `permanent/clique-evaluation.md` (direct attacks, §4.3 the two-grouping cap),
`permanent/rate.md` (α' = log₂(1/ρ)), `permanent/rho-lower-bound.md` (ρ ≥ 1/√2 for graded pieces),
`permanent/parity-barrier.md` (OpenAI's template), `permanent/permanent-attack.md` §3/§8 (what the dense
permanent needs), `tutte-plane.md` §4.1 (what e_K = o(1/log K) unlocks). Algebraic routes (tensor rank,
representation theory, new pieces) are the other agent's; nothing here duplicates them.
Scripts: `scripts/engine2p_*.py` (outputs `.out`, each prints PASS/FAIL). Lean (scratch, all `sorry`-free,
no `native_decide`): `lean/EthFollowup/Scratch/Engine2p/Accounting.lean`, `Instances.lean`.
Tags: **[R]** proved here, **[L]** Lean-proved (general), **[Li]** Lean-checked on instances, **[N]** numerical,
**[C]** heuristic.

## 0. Summary

**Problem.** (K,λ)-clique: Z = Σ_{x ∈ ({0,1}^λ)^E} Π_a T_a(x|_{δ(a)}), cost 2^{e_K K²λ}. Brute force e = (K−1)/(2K);
query bound (K−1)/K²; Anthropic e_K = Θ((log K)^{−1/2}); proved cap e_K ≥ c/log K for every recursion of
Theorem A's shape (two groupings, min, 2^{o(λ)} pieces per rectangle). Target: e_K = o(1/log K), or a proof that
no "oblivious" algorithm has it.

**Verdict.** None of the six mechanisms asked for (randomised hashing / isolation / collision sieves;
structural restriction to low-rank tables; communication / oblivious lower bounds; representative sets;
non-uniform dense/sparse schedules; fine-grained hypotheses) changes the rate, and for each the reason is an
exact accounting (§1–§6). Two of the kills are new theorems that go beyond what the project had:

* **Theorem A (covering bound, §7) [R]+[N].** The two-grouping cap ρ ≥ 1/2 of `clique-evaluation.md` §4.3
  extends to *every* family 𝒢 of groupings of the g² grid nodes (all set partitions, chosen adaptively per
  term, randomised or not): the level saving is ρ_eff ≥ 1/2 − O(√(log|𝒢|/|R|)) − (free fraction) ≥
  1/2 − O(√(log g)/g) for |𝒢| ≤ Bell(g²). Proof: probabilistic method (random term ι, Hoeffding, union bound
  over 𝒢) plus a counting lemma: under any grouping into blocks of size ≤ g at most a 2/g fraction of the
  rectangles see the free cut (xv|yu). Checked exactly at g = 3 (all 12 644 partitions) and on all
  2 627 625 balanced partitions at g = 4, where the adversary still forces exactly |R|/2 (`engine2p_covering.py`).
  Consequence: **α' ≤ 1 for every "expand into 2^{o(N)} terms, pick the best grouping" level**, randomised
  included; the ceiling 2^{O(U/log U)} of the framework is not a feature of the row/column pair.
* **Lemma B (decomposition convexity, §1) [L].** Any algorithm that decomposes the equality tensor on edges
  into terms of smaller rank (random hashes, prefix fixing, random projections, Walsh slices) and recurses on
  each term as a *general* clique instance has exponent ≥ e K²λ, with equality only at brute force. Randomness
  cannot enter through the equality tensor; it can only enter through structure of the *tables*, which the
  model treats as black boxes. Every "sieve" (Björklund's collision gain included) is a multiplicative
  2^{−o(N)} saving, never a rate.

Smaller exact facts: the schedule is irrelevant to the rate (optimal schedules beat Anthropic's by a factor
1.7 in e, never in α'; §5, [L] for the inequality, [N] for the DP); structural restriction to low cut rank gives
exactly the subset DP (e = Θ(κ), κ = cut-rank fraction) and the permanent sits at κ = Θ(1/log K), so
"e = o(κ) for low-rank tables" is per(A) ∈ 2^{o(n)} restated (§2); decision instead of counting does not lower
the cap (supports of permutation matrices force full rank; §4); isolation costs only O(K(λ + log K)) extra
bits, so randomised decision reduces to ⊕-clique evaluation — but the ρ ≥ 1/2 and covering caps are
field-independent (§1.4); no standard hypothesis gains or loses from e_K = o(1/log K): "global witness"
problems (OV, k-SUM, Subset Sum, k-Clique, Hyperclique) cost n^{Ω(k√K)}-type factors in any clique encoding
(the pairwise-check lemma of §6), while local ones are already subexponential.

**Ranking (§8):** (1) Theorem A → write the general "expansion-class" lower bound (the negative result the
brief asks for; the remaining gap is non-product terms and sub-instances not arising from groupings);
(2) ⊕-pieces over F₂ (the only place where randomisation changes the *problem*; open, but capped at α' = 1);
(3)–(6) closed. **Single most promising next step:** §8.

## 1. Mechanism 1: randomised algorithms (hashing, restrictions, isolation, collision sieves)

### 1.1 What randomness can act on [R]
Z is linear in each table and in the equality tensor 𝒯 = ⊗_e I_D. An algorithm that is "oblivious" to the
tables (reads them, does arithmetic) can randomise only (a) the decomposition of 𝒯, (b) the grouping /
contraction schedule, (c) the arithmetic itself (e.g. modular reduction, interpolation points). (c) is
constant-factor: Z is an integer < 2^{B+E λ}·…, CRT over poly many primes or one random prime of poly bits
changes nothing in the exponent; interpolation (T_a ↦ T_a + tS_a, Z(t) of degree K) needs K+1 equally hard
evaluations. (b) is §7. (a) is Lemma B:

**Lemma B (decomposition convexity) [L: `Engine2p.split_exponent_ge`, `brute_force_is_E`].** Suppose on every
edge I_D = Σ_{j≤m} A_j with rank A_j ≤ D/m (any field; m ≥ 2^{λ−λ'} terms of rank 2^{λ'}), and each of the m^E
resulting instances is evaluated as a (K, λ − log₂m)-clique at exponent e. Then the total exponent is
E log₂m + eK²(λ − log₂m) ≥ eK²λ, because E = K(K−1)/2 ≥ eK² for every achievable e (e ≤ (K−1)/(2K)). Equality iff
e is brute force. The same inequality with "λ₁ bits brute-forced per edge" is the prefix lemma of §5. ∎
`engine2p_schedule.py` (A),(B): minimum of the difference over a grid of (K, e, λ, split) is exactly 0 (PASS).

Random *hashes* h_e : {0,1}^λ → [m]: the collision matrix E_h = [h(x) = h(v)] has rank m and I = E_h − (E_h − I);
the correction E_h − I is block-diagonal with blocks J_s − I_s, det = (−1)^{s−1}(s−1) ≠ 0 for s ≥ 2
[Li: `detJI2/3/4`], so it has *full* rank D: the "colliding pairs" carry all the information. Averaging over a
pairwise-uniform family gives E_h[E_h] = I + (J − I)/m exactly [Li: `hash_identity_m2`, m = 2, all 16 maps
Fin 4 → Fin 2], hence I = (m/(m−1))(E_h[E_h] − J/m); expanding the product over edges gives 2^E signed terms,
each an expectation over independent hashes on its edges — the expectation is a sum over the family
(size ≥ D² per edge), i.e. ≥ 2^{2λE} terms: worse than brute force. Walsh/Fourier slices are the same (Lemma B
with A_j = projectors; `clique-evaluation.md` §4.4). **Dead.**

### 1.2 Björklund's collision gain and "below all subsets" [R]
Fix the labels outside a node set S: Z = Σ_{x_out} (Π_{c∉S} T_c)·Z_S(T|_{x_out}), Z_S an (|S|,λ)-clique with
restricted tables. The gain of arXiv 1211.0391 is that the number of *distinct* small instances
(p^{|S|·2^{(|S|−1)λ}} over F_p) is below the number 2^{λ(E − C(|S|,2))} of outer labellings, so one tabulates and
counts multiplicities. Here that requires |S| = 2 and 2^{λ+1} log p < λK²/2, i.e. λ ≤ 2 log K − O(log log K),
and the multiplicity vector c(f,g) = Σ_{x_out} Π_{c∉S}T_c·[T_a|_{x_out} = f][T_b|_{x_out} = g] is itself a
(K,λ)-clique with two vector-valued tables of output dimension p^{2^{λ+1}} — as hard as Z (Z is a linear
functional of c). Björklund computes c by a DP that uses the *linear* structure of walk counts in the
permanent; general tables have no such structure, and for #SAT tables the same gain is the Chan–Williams
2^{n − n/O(k)}: a saving of rate 1, i.e. a factor 2^{−o(N)} on top of any exponent. Iterating it inside the
recursion: the level's sub-instances are the ι-terms, 2^{Θ(N)}-bit objects, pairwise distinct; no collisions.
**Constant-factor at best; the rate is untouched.**

### 1.3 Isolation for decision (SAT, Hamiltonicity) [R]
Decision needs Z ≠ 0 for non-negative tables. Valiant–Vazirani / Mulmuley–Vazirani–Vazirani: random weights
w_e : {0,1}^λ → [2ED] on (edge,label) pairs isolate a unique minimum-weight satisfying labelling w.p. ≥ 1/2.
The constraint "total weight = W" is a global linear constraint, but in a clique it is cheap: route partial sums
along a Hamiltonian cycle of K_K (node a adds w_{ab}(x_{ab}) for b > a), adding log(K²·2ED) = λ + O(log K) bits to
K edges: U' = U(1 + O(1/K)) (Lemma 8 regroups). W ranges over ≤ K²·2ED = 2^{λ+O(log K)} values, a factor
negligible against 2^{eK²λ}. So **randomised decision at rate e reduces to evaluating Σ_x [w(x)=W]Π T_a mod 2
at rate e**: a ⊕-(K,λ)-clique. This is the one place where randomisation changes the *problem*: over F₂.

### 1.4 ⊕-cliques: pieces over F₂ [R]+[N]
Everything in Theorem A is field-agnostic except Theorem B's pieces: Σ_s Q_s = h!·Id (Lemma 10), and h! ≡ 0
mod 2 for h ≥ 2 (`engine2p_f2pieces.py`), so the Appendix-B pieces do not exist over F₂ (nor over F_p for p ≤ h);
their binomial coefficients C(2h,i) collapse by Lucas. Conversely the caps are field-independent: ρ ≥ 1/2
(rank subadditivity over any field, `rho-lower-bound.md` Cor. 2.2) and Theorem A below. So ⊕-pieces could at
best give α' = 1 (2^{O(U/log U)}), a landmark but not the target. Exhaustive data at λ = 1 (SWAP on two bits,
all 65 536 two-piece decompositions over F₂; 3-piece with two low-rank pieces; F₃ restricted): the optimum
is the trivial row split (two pieces of row-rank 2 and col-rank 2, product 4 = N²), the ρ = 1/2 profile, over
every field — the question only becomes field-sensitive at λ ≥ 2 with |I| ≪ 2^λ pieces, beyond exhaustive
search. **Open, algebraic, flagged for the other agent; capped at α' = 1 regardless.**

**Mechanism 1 verdict: killed for the rate.** Lean status: Lemma B [L]; hash identity and J−I invertibility
[Li]; isolation bit-count [R, not formalised]; ⊕-pieces: not formalised (open).

## 2. Mechanism 2: structural restriction to "low piece-rank" tables

### 2.1 Which parameter the permanent's tables have [R]
Laplace network (`permanent-attack.md` §3): row node a (rows R_a, p = n/h) sees the labels T_{ab} ⊆ C_b
(pattern-wise, Σ_b lg C(q, N_{ab}) ≈ P = (n/h) lg(eh) bits) and has table per(A[R_a, ∪_b T_{ab}]). Across any
cut of its legs into (L | R): per(A[R_a, S_L ∪ S_R]) = Σ_{I ⊆ R_a} per(A[I, S_L])·per(A[R_a∖I, S_R]), so
**cut rank ≤ 2^{p} = 2^{P/lg(eh)}** (and this is a nonnegative factorisation, so nonnegative rank is the same;
the column node [T_{·b} partition C_b] has Boolean cut rank ≤ 2^{q}). A generic table has cut rank 2^{P/2}.
Define κ := (log cut rank)/P; the permanent's tables have κ ≈ 1/lg(eh) ≈ 1/lg K. In the Walsh basis the same
table is a degree-p multilinear polynomial in the n column indicators ("Walsh sparsity" C(n,p) ≤ 2^{p lg(eh)}),
and the partition constraint relaxed by inclusion–exclusion over sets is Ryser. CP (tensor) rank, by contrast,
is full: Σ over ordered partitions of R_a into labelled blocks, h^{p} = 2^{P}.

### 2.2 What low cut rank buys, exactly [R]
Hierarchical (tree-tensor) cut rank 2^{κP} at every node lets a contraction order keep intermediate
tensors T_S of rank ≤ 2^{κ Σ_{a∈S} P_a} across (S | S^c) *provided the hidden indices are explicit and
consistent along the order*; for the Laplace network the hidden index is "set of columns used so far" and the
order is the row groups: this is the 2^n subset DP (Bellman–Held–Karp / Ryser's twin). In clique units
U ≈ 16 n lg K, so e_DP = n/(K²λ) ≈ 1/(16 lg K) = Θ(κ). Hence:

**Proposition 2.1.** For tables of cut-rank fraction κ, e_K(𝒞_κ) ≤ O(κ) + O(1/K) by the DP along the explicit
factorisation, and the dense permanent is the instance κ = Θ(1/log K). Reaching per(A) ∈ 2^{o(n)} through the
engine needs e_K(𝒞_κ) = o(κ) on that instance — which *is* the statement "beat the subset DP by an unbounded
factor in the exponent". No parameter among {cut rank, nonnegative rank, Boolean rank, Walsh sparsity, CP
rank} separates the permanent's tables from the hardness: each one recovers exactly one classical 2^{Θ(n)}
algorithm (DP, Ryser) and nothing below. ∎

Could a restricted-class rate improvement still be *useful* if it reached only e = o(1/log K) for κ ≤ 1/log K?
Yes — that is precisely the target restricted to the only instance we care about; but there is no reason
the restriction makes it easier: the general ρ ≥ 1/2 and covering caps (§7) hold for the equality tensor and
never look at the tables. **Mechanism 2 verdict: no useful restriction; equivalent to the problem.**
Lean: not formalised (Proposition 2.1 is an accounting statement about a model, not a finite identity).

## 3. Mechanism 3: communication / oblivious lower bounds

### 3.1 What the model is [R]
"Access tables by point queries, do arithmetic" = arithmetic circuits (over ℚ or ℤ) for the degree-K
set-multilinear form Z in N_in = K·2^{(K−1)λ} inputs. Anthropic's algorithm is a *set-multilinear circuit*
(every gate is multilinear and homogeneous in the partition of inputs by node: modified tables are linear in
one table, supernode tables are products over disjoint node sets, sums over ι add such terms). So the natural
lower-bound model is set-multilinear circuits of unbounded depth.

### 3.2 What is provable, and what the target costs [R]
* Query model: e ≥ (K−1)/K² (tight for queries). Nothing more in that model (`barrier.md` Lemma 2.2).
* Set-multilinear **ABPs / ROABPs** in any order (Nisan's rank method): the partial-derivative matrix between
  nodes S and S^c has rank 2^{λ|S||S^c|} (the labels of the crossing edges are read on both sides), so width
  ≥ 2^{λK²/4}: e ≥ 1/4 — the flattening bound of `clique-evaluation.md` §4.2, and the FMM level stays at 2/9.
* Unbounded-depth set-multilinear circuits: the best known lower bounds for *any* explicit polynomial are
  Ω(n^{4/3}/log² n) for multilinear circuits (Raz–Yehudayoff) and superpolynomial only at constant depth
  (Limaye–Srinivasan–Tavenas). The target "e_K ≥ c/log K for all algorithms" at λ = 1 is a lower bound of
  2^{cK²/log K} = N_in^{Ω(K/log K)} for a degree-K polynomial in N_in = K2^{K−1} variables: a super-polynomial
  circuit lower bound for an explicit family (growing degree), far beyond current technique even in the
  set-multilinear model. At K = 3 it contains ω > 2.
* Adversary arguments for sums over cliques work only against algorithms whose sub-computations are
  themselves clique sums with the same equality structure — that is the expansion class, and there the bound
  is Theorem A (§7), which is the honest "oblivious" lower bound we can prove: it covers any family of
  groupings, adaptive or randomised, but not non-product terms.

**Mechanism 3 verdict:** the unconditional version for all algorithms is out of reach (it would be a
breakthrough in algebraic complexity by itself); the structured version is Theorem A. Lean: the Nisan
flattening rank 2^{λ|S||S^c|} is a one-line fact, not formalised; Theorem A's ingredients are in §7.

## 4. Mechanism 4: representative sets / colour coding over shared blocks

* Representative families (Fomin–Lokshtanov–Saurabh; Marx's matroid version) replace a family of independent
  sets by a q-representative subfamily of size C(p+q, p): an *existence* tool, it loses counts, so it cannot
  touch Z. The equality constraints have no matroid: the solution space is a product (free), and "x_{ab} = x_{ba}"
  is a partition-type identification, not independence.
* For **decision** with 0/1 tables (SAT, HC via §1.3) the question becomes whether *decision pieces* can beat
  ρ = 1/2: nonnegative A_s with Σ_s A_s having the support of F = [x=v][y=u]. Both flattenings of F are permutation
  matrices; any matrix with that support is P·D with D diagonal positive, of full rank N². So the rank
  subadditivity argument (`clique-evaluation.md` §4.3, `rho-lower-bound.md` Cor. 2.2) applies verbatim: some
  piece has row rank ≥ N²/|I|, some has col rank ≥ N²/|I|, and the adversary of §7 forces ρ_eff ≥ 1/2 − o(1).
  **Decision does not lower the cap** — and with §1.3 it cannot be easier than ⊕-counting anyway.
* Colour coding over blocks (random colouring of the D labels into few classes, require "colourful"
  labellings) is Lemma B with A_j = colour-class projectors plus a correction of full rank. Dead.

**Mechanism 4 verdict: killed.** Lean: the support-rank fact (permutation support ⇒ full rank) not
formalised; the adversary half is `adversary_two_groupings` [L] (general n).
