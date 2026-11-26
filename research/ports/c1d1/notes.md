# c1d1: characteristic p (C1) and the engine gap (D1)

Theory notes, 26 Nov 2026. Nothing here is committed, machine-checked or refereed.

Tags: **[R]** proved here in full from classical facts; **[D]** derived here, unreviewed, and resting on the
cited inputs; **[K]** quoted (K-OA = OpenAI's unrefereed 24 Nov release; K-AN = Anthropic's paper); **[C]**
conjecture; **[X]** dead, with the reason.

Inputs and their status:
- **HC 13.1** (K-OA): enumerable contraction, read from `survey/oa/preprints/Circuit…/paper.txt` l.3069–3137.
- **IM 7.1** (K-OA): ports in characteristic 0 ⇒ 3-SAT in 2^{O(v^{1−δ})}; text l.1687–1750 of the
  integer-multiplication paper.
- **Theorem R** (`ports/rebase/notebook.md`): contracting over a field of characteristic 0 ⇒ 3-SAT in
  2^{O(n^{1−δ})}. **Unreviewed; its Lemma 1 (guess count) is with a referee. Every use below is flagged "(R?)".**
- **Flat floor and win-win** (`next/review-link.md`, reviewed, "correct with fixes"; corrected statements used).
- **AN thm_alt** (K-AN, Lean): ¬Contracting(k) ⇒ Flat(k).
- **EG 1.2** (K-OA): over every field there is a spectral flat of every dimension (exact Euclidean prices).

Notation. v or n = number of variables. "Power-saving" = time 2^{O(v^{1−δ})}·poly(input length), some δ > 0.
- **WETH** (variable-count Weak ETH, IM §1): no deterministic power-saving algorithm decides 3-SAT.
- **rWETH**: no randomised power-saving algorithm with one-sided error decides 3-SAT (never accepts an
  unsatisfiable formula; accepts a satisfiable one with probability ≥ 1/2). rWETH ⇒ WETH.
- **⊕_pWETH**: no deterministic power-saving algorithm computes #3-SAT mod p.
- **UWETH**: no deterministic power-saving algorithm solves the promise problem Unique-3-SAT.
- **nuWETH**: no deterministic power-saving algorithm with poly(v) advice bits (depending on v only) decides 3-SAT.

---

## Summary

**C1 (settled positively, [D]).** Isolation is free in the power-saving regime.
- Ports in characteristic p (HC 13.1), or contracting over a field of characteristic p (R?), gives a randomised
  one-sided-error algorithm for 3-SAT in 2^{O(v^{1−δ})} with **the same δ as in characteristic 0**.
- The reason: both mod-p counters accept more than 3-CNF (bit networks; weighted nondeterministic programs), a
  pairwise-independent hash has a circuit of size v^{1+o(1)} (Toeplitz hash = polynomial multiplication over
  F₂), and Valiant–Vazirani succeeds with probability ≥ 3/(16v).
- Purely classical version [R]: ¬⊕_pWETH ⇒ ¬UWETH ⇒ ¬rWETH. So **rWETH ⇒ UWETH ⇒ ⊕_pWETH for every p**.
- Derandomisation: free non-uniformly (so nuWETH is refuted too), free uniformly under the
  Impagliazzo–Wigderson hypothesis. No unconditional uniform route.
- The Calabro–Impagliazzo–Kabanets–Paturi lemma is the wrong tool here (§C1.6).
- Consequence for Theorems S and M: under rWETH **no characteristic has ports** (given HC 13.1, IM 7.1). M1 then
  holds in its printed form, without the reading (H1₀). S is unchanged.

**D1 (a true gap theorem at the level of the exponent of log, and a precise obstruction to the sharp form).**
- [D] For tower engines whose levels are p-merge grid levels with all-crossing configurations from a finite list
  and node growth K ↦ K^β: if the certified rate beats exponent ½·log_β p on log K by a fixed γ > 0 (for
  Anthropic's rectangle levels: exponent 1/2), then the flat hypothesis fails over that field, hence contracting
  holds over its closure, hence 3-SAT has a power-saving algorithm (deterministic in characteristic 0 (R?),
  randomised in characteristic p by C1).
- [X] The sharp form "2^{o(n/√log n)} forces ¬flat" does **not** follow. Deficits η(λ) → 0 below the floor are
  compatible with the flat hypothesis as Anthropic states it (prices are limits, with no rate), and over the
  ≤ log log n levels they can accumulate to any factor (log n)^{o(1)}. They cannot accumulate to (log n)^γ.
- [D, given EG 1.2] If flats are exact prices (OpenAI), the deficit per level is O(√(log λ/λ)), nothing
  accumulates, and the class has rate exactly Θ((log K)^{−1/2}): the theorem's hypothesis is then vacuous and
  what remains is an unconditional optimality statement for the class.
- [X] The strategist's network-rewriting formulation (via MM Lemma 4.1) does not go through as stated (§D1.6).

---

# Part C1. Characteristic p

## C1.1 What the mod-p counters accept [K, checked against the texts]

**OpenAI side.** HC Theorem 13.1, verbatim: "Fix a characteristic admitting ports. There is an η > 0 such that
every closed bit network of volume at most s and maximum degree at most s^{1/20}, **over any field of this
characteristic**, has a formula for its contraction using 2^{O(s^{1−η})} arithmetic operations and local entry
queries. The topology determines the formula, which can be generated deterministically in 2^{O(s^{1−η})} bit
operations and **uses fixed prime-field constants**. In characteristic zero, for integer entries of polynomial bit
length, evaluation takes the same number of bit operations plus the time for the queries."
- A bit network: arbitrary tables {0,1}^{arity} → field at the vertices, one bit per wire, sum over all wires.
- So in characteristic p, with {0,1}-valued tables read in F_p, the output is the contraction mod p, in
  2^{O(s^{1−η})} operations in F_p. Nothing restricts the tables to clause indicators: XOR, AND, equality and
  pinning tables are all allowed.
- Characteristic 0 is used in IM 7.1 in exactly one place: the last line, "Accept if any leaf contraction is
  positive" (an integer count).

**Anthropic side (R?).** The model of AN §I is a nondeterministic program with ring-weighted runs; sum(z) is the
weighted number of accepting runs. Theorem R evaluates sum(z) for any τ-plain instance in 2^{O(τ^{H/(H+187)})}
ring operations. In characteristic p the ring maps to a finite field, and sum(z) is known mod p (rebase Cor. 1′).
Any verifier that runs in τ steps is an admissible instance, so a hash test is added by adding steps.

So neither algorithm needs the instance to be a 3-CNF. This is what makes isolation cheap.

## C1.2 A hash with a near-linear circuit [R]

**Definition (Toeplitz hash).** For 1 ≤ k ≤ n+1, a ∈ F₂^{n+k−1}, b ∈ F₂^k, define h_{a,b} : F₂ⁿ → F₂^k by
h_{a,b}(x)_j = b_j + Σ_{i=0}^{n−1} a_{n−1+j−i}·x_i (0 ≤ j < k). Equivalently, h_{a,b}(x) − b is the list of
coefficients of t^{n−1}, …, t^{n+k−2} in the product a(t)·x(t) in F₂[t].

**Lemma C1 (pairwise independence).** For a, b uniform and x ≠ y in F₂ⁿ, the pair (h(x), h(y)) is uniform on
F₂^k × F₂^k.

*Proof.* Let z = x − y ≠ 0 and let i* be the least index with z_{i*} = 1. Row j of T_a z is
a_{n−1+j−i*} + Σ_{i>i*} z_i a_{n−1+j−i}. The index n−1+j−i* is larger than every index used in rows j′ < j and
larger than the other indices of row j. So, going through j = 0, 1, …, k−1, each row is a fresh uniform bit plus a
function of earlier coordinates of a; hence T_a z is uniform on F₂^k. For fixed a, h(x) = T_a x + b is uniform
because b is. Since T_a z depends only on a, the pair (h(x), h(x) − h(y)) is uniform, and so is (h(x), h(y)). ∎

**Lemma C2 (circuit size).** x ↦ h_{a,b}(x) is computed by a circuit of XOR and AND gates of fan-in 2 with
O(n log n log log n) gates, constructible in polynomial time.

*Proof.* It is one multiplication of polynomials of degree < 2n+1 over F₂, which has bilinear circuits of size
O(n log n log log n) [Schönhage 1977; Cantor–Kaltofen 1991], followed by k additions of the bits of b. ∎

Remark [K, not re-proved]. Ishai–Kushilevitz–Ostrovsky–Sahai (STOC 2008) give pairwise-independent families
(affine, by Baron–Ishai–Ostrovsky 2013, Prop. 8) computable by circuits of size O(n). Using them replaces
"δ′ < δ" by "δ′ = δ" in Lemma C4 and nothing else. Lemma C2 needs only textbook fast multiplication.

**Lemma C3 (Valiant–Vazirani with any pairwise-independent family)** [classical]. Let ∅ ≠ S ⊆ F₂ⁿ and let k
satisfy 2^{k−2} ≤ |S| ≤ 2^{k−1} (such k exists in {2, …, n+1}). Then Pr_{a,b}[ |S ∩ h^{−1}(0)| = 1 ] ≥ 3/16.

*Proof.* With q = |S|/2^k ∈ [1/4, 1/2]: the probability is ≥ Σ_{x∈S} (Pr[h(x)=0] − Σ_{y≠x} Pr[h(x)=h(y)=0])
≥ |S|(2^{−k} − |S|2^{−2k}) = q(1−q) ≥ 3/16. ∎

So for k uniform in {2, …, n+1}: unique solution with probability ≥ 3/(16n).

## C1.3 The classical transfer lemma [R]

**Lemma C4.** Let p be a prime and δ > 0. Suppose a deterministic algorithm, on 3-CNFs with v variables, runs in
2^{O(v^{1−δ})}·poly and either (a) computes the number of satisfying assignments mod p, or merely (b) answers
"yes" on formulas with exactly one satisfying assignment and "no" on unsatisfiable ones. Then for every δ′ < δ
there is a randomised algorithm for 3-SAT in time 2^{O(v^{1−δ′})}·poly that never accepts an unsatisfiable
formula and accepts every satisfiable one with probability ≥ 1/2.

*Proof.* (a) gives (b): output "yes" iff the count is nonzero mod p. Given F on n variables, repeat 16n times:
draw k ∈ {2, …, n+1}, a, b; let C be the circuit of Lemma C2; form F′ = F ∧ Tseitin(C) ∧ (outputs of C are 0),
where Tseitin(C) has one new variable and at most four clauses of width ≤ 3 per gate. F′ is a 3-CNF with
v′ = O(n log n log log n) variables, and every x extends uniquely to the gate variables, so
#F′ = |S_F ∩ h^{−1}(0)|. Run the algorithm on F′; accept if any run says "yes". If F is unsatisfiable, every F′
is, and all answers are "no". If F is satisfiable, each round produces a uniquely satisfiable F′ with probability
≥ 3/(16n) (Lemma C3), so some round does with probability ≥ 1 − e^{−3} > 1/2. The time is
16n·2^{O(v′^{1−δ})} = 2^{O(n^{1−δ}(log n)^{2})} ≤ 2^{O(n^{1−δ′})}. ∎

**Corollary C5 [R].** rWETH ⇒ UWETH ⇒ ⊕_pWETH for every prime p. (Contrapositive of Lemma C4.)

**What is special about the power-saving regime [R, remark].** Lemma C4 uses a blow-up v ↦ v^{1+o(1)} of the
number of variables, which the class of bounds 2^{O(v^{1−δ})} absorbs (δ′ < δ). In the usual regime 2^{εv} the
same reduction is useless unless the blow-up is linear. Conversely the power-saving regime demands success
probability ≥ 2^{−v^{1−δ}}, which Valiant–Vazirani (1/poly) meets and a 2^{−εv} isolation lemma does not. So the
power-saving regime is *more* demanding on the success probability and *less* demanding on the variable count
than the 2^{εv} regime. The strategist's obstacle ("VV costs volume ≈ v²") is about dense random parity
matrices, not about isolation: a structured hash removes it.

## C1.4 The theorems [D]

**Theorem C1-OA (ports in characteristic p).** Let p be a prime. Assume characteristic p admits ports and HC
Theorem 13.1 as printed. Then for some δ > 0 there is a randomised algorithm that, on a 3-CNF with v variables,
runs in 2^{O(v^{1−δ})} bit operations times a polynomial in the input length, never accepts an unsatisfiable
formula, and accepts a satisfiable one with probability ≥ 1/2. Any δ < min{α, 1 − (1+4α)(1−η)} works, with η from
HC 13.1 for characteristic p and 0 < α < 1/4 such that (1+4α)(1−η) < 1: **the same formula as in IM 7.1.**
In particular rWETH implies that no characteristic admits ports.

*Proof.*
1. Sparsify F exactly as in the proof of IM 7.1 (r = ⌈v^α⌉): 2^{O(v^{1−α} log v)} leaves F_j, each with
   O(v^{1+4α}) clauses, F ≡ ∨_j F_j, and every F_j implies F (each child implies its parent).
2. Repeat 16v times: draw k, a, b as in Lemma C3 (one draw for all leaves). For each leaf build the closed bit
   network N_j: the IM 7.1 network of F_j (clause indicators, trees of ternary equality tables, degree ≤ 3), plus,
   attached to one extra copy of each variable, the circuit of Lemma C2 with one ternary table per gate
   ([w = u⊕u′] or [w = u∧u′]), equality tables at fan-outs, the bits of a and b pinned by unary tables e_{a_i},
   e_{b_j}, and each output pinned to 0 by e_0. All tables are {0,1}-valued; the degree is ≤ 3; the volume is
   s = O(v^{1+4α} + v log v log log v) = O(v^{1+4α}).
3. Every assignment x has exactly one compatible labelling of all copy and gate wires, so the contraction of N_j
   over F_p equals |{x : F_j(x) ∧ h_{a,b}(x) = 0}| mod p. Compute it by HC 13.1 in 2^{O(s^{1−η})} operations in
   F_p. Accept if some contraction is nonzero.
4. Soundness: if F is unsatisfiable, every count is 0. Completeness: if F is satisfiable then with probability
   ≥ 3/(16v) per round F ∧ [h = 0] has exactly one solution x₀. Each leaf's solution set is contained in that of
   F ∧ [h = 0], so each leaf count is 0 or 1, and the leaf satisfied by x₀ has count 1 ≢ 0 mod p. Note that the
   leaves need not be disjoint.
5. Time: 16v · 2^{O(v^{1−α} log v)} · 2^{O(v^{(1+4α)(1−η)})}. ∎

**Theorem C1-AN (contracting in characteristic p) (R?).** If the contracting hypothesis holds over a field of
characteristic p, the same conclusion holds with any δ < 187/(5H+187), H the constant of AN Thm J.4, exactly as in
Theorem R.

*Proof sketch.* In §2.3 of the rebase notebook replace the instance z_j = (P, ⟨F_j⟩) by (P′, ⟨F_j, C⟩), where C
is the circuit of Lemma C2 written as a gate list and P′ is the fixed program that guesses x, checks F_j, then
evaluates C gate by gate (values kept in a balanced tree: O(log) steps per gate) and fails unless all outputs are
0. Then τ₀ and |z| grow by O(n log² n log log n), which is below L = O(n^{1+4α} log n), and sum(z) =
2^e·|{x : F_j(x), h(x)=0}| with 2^e a unit mod p for p odd. For p = 2 remove the padding (use a tree with exactly
n leaves) so that e = 0. The rest is steps 4–5 above with Theorem R's Corollary 1′ in place of HC 13.1. ∎
(The p = 2 padding point is a small correction to rebase Cor. 1′: 2^e·#SAT is 0 mod 2 when e > 0.)

**A caveat on "#3-SAT mod p" itself [D].** Rebase Cor. 1′ and the strategist's item (ii) say that the mod-p
*count* of a 3-CNF follows. That needs a count-preserving sparsification: the sunflower branching printed in IM
§7 is not a partition (an assignment can satisfy the centre and all petals). Fix: let the second child add, besides
the petals, the negation of the centre as unit clauses (kept as clauses, not propagated). Then the two children
partition the parent's solutions, the potential argument of IM §7 is unchanged apart from at most two extra units
per branch, and #F = Σ_j #F_j. Alternatively cite the counting sparsification lemma of
Dell–Husfeldt–Marx–Taslaman–Wahlén (2014) with ε = v^{−α} (constants to be checked in that regime).
Theorem C1 does **not** need this.

## C1.5 Derandomisation [D]

1. **Non-uniform: free.** There are at most 2^{8v³} 3-CNFs on v variables. For a fixed satisfiable F, a list of
   N independent triples (k, a, b) fails with probability ≤ (1 − 3/(16v))^N < 2^{−8v³} once N = 64v⁴. So one list
   of 64v⁴ triples (O(v⁵) bits, depending on v only) works for all 3-CNFs on v variables. Hence ports in
   characteristic p, or contracting in characteristic p (R?), gives a deterministic power-saving algorithm with
   O(v⁵) advice bits: **nuWETH is refuted as well.**
2. **Uniform, under a standard hypothesis: free.** Suppose some function in DTIME(2^{O(m)}) has circuit complexity
   ≥ 2^{εm} for all large m (Impagliazzo–Wigderson 1997). Then for every T there is a generator
   {0,1}^{O(log T)} → {0,1}^T computable in poly(T) time that fools circuits of size T. The acceptance test of
   Theorem C1 for fixed F is a deterministic computation of time T = 2^{O(v^{1−δ})}·poly in the random bits, so
   enumerating the seeds costs poly(T) = 2^{O(v^{1−δ})}·poly. **The family of bounds 2^{O(v^{1−δ})} is closed under
   polynomials, so in this regime BPTIME derandomises with no loss in δ.** Under that hypothesis, WETH alone
   excludes ports and contracting in every characteristic.
3. **Unconditional and uniform: no route [C].** One needs an explicit list of 2^{O(v^{1−δ})} hash functions
   isolating a solution of every sparse satisfiable 3-CNF. A random list of size poly(v) works, but certifying a
   list is as hard as the problem. A positive answer would put 3-SAT in deterministic power-saving time relative
   to a ⊕3-SAT oracle; nothing known gives that (compare Dell–Kabanets–van Melkebeek–Watanabe on the isolation
   probability). I rate it out of reach.

## C1.6 The "easy alternative": Unique-k-SAT hardness under ETH [K + D]

[K, CIKP, JCSS 2008, Lemma 3, checked against the paper]: for k ∈ ℕ and ε ∈ (0, 1/4) a randomised polynomial-time
reduction maps an n-variable k-CNF φ to an n-variable k′-CNF φ′, k′ = max{⌈(1/ε) ln(2/ε)⌉, k}; unsatisfiable
stays unsatisfiable; a satisfiable φ becomes uniquely satisfiable with probability ≥ (32n·2^{3h(2ε)n})^{−1}.
Construction: m ≤ (1+4ε)n + 2 random parities on k′ variables each, then a random assignment to 2εn random
variables. Consequences drawn there: s_k ≤ σ_k + O(ln²k/k), hence lim s_k = lim σ_k.

- **As a black box: useless here [X].** With k′ fixed, ε is a constant and the success probability is 2^{−Θ(εn)}.
  The 2^{Θ(εn)} repetitions exceed any 2^{n^{1−δ}} budget. "ETH for k-SAT ⇔ ETH for Unique-k-SAT in the limit"
  is a statement about the constants s_k in 2^{s_k n} and says nothing about the power-saving regime.
- **Opened up, with ε = n^{−β}: works but is dominated [D].** Success probability 2^{−O(n^{1−β} log n)}, width
  k′ ≈ n^β log n. As a k′-CNF each parity is 2^{k′−1} clauses, which is useless; with native parities (bit
  networks, or Tseitin with k′ new variables per parity) the added volume is n^{1+β} log n. Taking β = 4α gives
  the same δ as Theorem C1, at the price of 2^{Õ(n^{1−β})} repetitions instead of 16n, and with no gain.
- CIKP was designed to keep the variable set fixed and the width bounded, which the 2^{εn} regime needs and this
  regime does not. Lemma C4 is the statement that plays its role here.

## C1.7 What this does to Theorems S and M (`mm/anti/notebook.md`)

Current hypotheses there:
- **S1–S3** (Ω(n√log n) gates for F₂[x]-multiplication, integer multiplication, cyclic shift): WETH, through
  "characteristic 0 has no ports" (IM 7.1, IM Lemma 8.2; the circuits are embedded as rational networks).
- **M1** (Ω(n²√log n) for matrix products; also F_p-network bounds): printed MM Lemma 4.1 for a finite field, plus
  the open hypothesis "some prime p has no ports".
- **M2**: WETH plus the reading (H1₀) that MM Lemma 4.1 holds in characteristic 0.

After C1 [D]:

| Result | Hypothesis sufficient after C1 | What it rests on |
|---|---|---|
| S1–S3 | WETH (unchanged) | IM 7.1, IM Lemma 8.2 |
| M1 (all parts, including F_p-networks and parity-nondeterministic circuits for p = 2) | any one of: rWETH; nuWETH; UWETH; ⊕_pWETH for one prime p (with the disjoint sparsification of C1.4); WETH + the Impagliazzo–Wigderson hypothesis | HC 13.1 in characteristic p, printed MM Lemma 4.1 |
| M2 | WETH + (H1₀) (unchanged) | IM 7.1 |
| "No characteristic has ports" | rWETH (or nuWETH) | HC 13.1, IM 7.1 |

- So the cleanest single hypothesis for S and M together is **rWETH**: it implies WETH (for S) and excludes ports
  in characteristic 2 (for M1 as printed, with k = F₂). The reading (H1₀) is no longer needed for the matrix
  bounds. rWETH is not exotic: CIKP define the constants s_k with randomised algorithms.
- The weakest hypothesis that gives M1 alone is ⊕₂WETH ("no deterministic power-saving algorithm for ⊕3-SAT"),
  which follows from rWETH by Corollary C5.
- Dichotomy form: for each prime p, either 3-SAT has a randomised one-sided power-saving algorithm, or
  characteristic p has no ports and M1 holds with k = F_p.
- S for networks over F_p (rather than circuits embedded over ℚ) would need IM Lemma 8.2 in characteristic p. The
  input "no ports in characteristic p" is now available under rWETH; the lemma itself is a reading of a printed
  proof, like (H1₀). Not done here.

---

# Part D1. The engine gap

## D1.1 The class

Fix a field k, integers p ≥ 2 and β ≥ 2, and a finite list 𝒞 of configurations.

**Level.** A (p, β, 𝒞)-level on K′ nodes with strings of λ bits consists of:
- p merges (partitions of the nodes), after any one of which the merged instance is handed to a solver for at
  most K nodes, where K′ ≥ K^β;
- a partition of the edges into copies of configurations from 𝒞, in each of which every edge crosses every merge,
  plus a remainder carrying a fraction ξ of the edge bits;
- for each C ∈ 𝒞 an exact identity Σ_{i∈I} A_i = d·f_C over k with d ≠ 0 and |I| ≤ 2^{τ(λ)}, where τ(λ)/λ → 0 is
  a function fixed for the engine;
- evaluation rule: every choice of one piece per copy is a term; a term is evaluated under the merge that
  minimises its total merged-edge bits Σ_copies c_m(A_i); c_m is the D1 cost (log of bond dimensions, minimised
  over network representations on the groups).

The **level factor** ρ is (worst term's merged bits)/(raw bits). Anthropic's level is the case p = 2, β = 2,
𝒞 = {crossing}, ξ = 2/(g+1), ρ = 1/√2 with the App. B pieces.

**Engine.** A (p, β, 𝒞)-engine is, for each n, a tower of L = L(n) levels with factors ρ_1, …, ρ_L (the pieces
may depend on the level and on n), node counts K_0 < K_1 < … < K_L with K_{ℓ+1} ≥ K_ℓ^β, K_0 ≥ 2 fixed, all
string lengths ≥ λ_min(n) → ∞, and remainders ξ_ℓ → 0 uniformly. Its **certified exponent** is the output e_L
of the recursion e_{ℓ+1} = ρ_ℓ e_ℓ + (non-negative terms), e_0 > 0 fixed; its certified running time on n-variable
3-CNFs is 2^{O(e_L·n)}·poly. In particular e_L ≥ e_0·Π_ℓ ρ_ℓ and L ≤ log_β(log K_L/log K_0).

Its **log-exponent** is α′ = liminf_n (−log e_L)/(log log K_L). Anthropic's engine has α′ = 1/2
(e_L = Θ((log K_L)^{−1/2})), and log K_L = Θ(log n), so the time is 2^{O(n/√log n)}.

The theorem below is about certified exponents. The statement "true running time ≥ certified" needs a lower
bound for every algorithm of the class (the analogue of Majdoddin's Thm 4.13); I have not checked that proof and
do not claim it. [C]

## D1.2 The level floor and its converse [D, from the reviewed flat floor and win-win]

**Lemma D1 (level floor).** If FH holds over k, every (p, β, 𝒞)-level has
ρ ≥ (1−ξ)(1/√p − ε_𝒞(λ)), where ε_𝒞(λ) → 0 as λ → ∞ depends only on 𝒞, τ and k.

*Proof.* By the flat floor theorem (review-link, corrected statement), for each C ∈ 𝒞 and each λ some piece
i*_C has c_m(A_{i*}) ≥ (E_C/√p − ε_C(λ))λ **for every merge m at once**. The term that uses i*_C on every copy
of C costs at least that under every merge, so the minimum over merges is at least Σ_copies (E_C/√p − ε_C)λ.
𝒞 is finite, so ε_𝒞 = max_C ε_C/E_C works. ∎

**Lemma D2 (converse, level form).** If a level has ρ ≤ (1−ξ)(1/√p − η), then for some C ∈ 𝒞 used at that level
**every** piece has min_m c_m(A_i) ≤ (E_C/√p − η)λ.

*Proof.* Otherwise choose for each C a piece violating the inequality; that term costs more than
(1/√p − η)·(raw bits of the copies) under every merge. ∎

The simultaneity "for every merge at once" is what makes mixed levels work: a level cannot hide behind
configurations that are each cheap under a different merge.

## D1.3 The gap theorem [D]

**Theorem D (engine gap, exponent form).** Let k be a field and let a (p, β, 𝒞)-engine over k have log-exponent
α′ > ½·log_β p along some infinite set of n. (For p = β = 2, Anthropic's type: α′ > 1/2, i.e. certified time
2^{O(n/(log n)^{1/2+γ})} with γ > 0.) Then:
1. the flat hypothesis fails over k and over every extension of k;
2. the contracting hypothesis holds over the algebraic closure k̄ (AN thm_alt);
3. if char k = 0: 3-SAT (and #3-SAT, with the disjoint sparsification of C1.4) has a deterministic algorithm in
   2^{O(n^{1−δ})}·poly (Theorem R, R?; or Theorem A of `ideas-ports.md` with IM 7.1);
4. if char k = p′ > 0: 3-SAT has a randomised one-sided-error algorithm in 2^{O(n^{1−δ})}·poly, a deterministic
   one with O(n⁵) advice bits, and #3-SAT mod p′ has a deterministic one (Theorem C1-AN, R?).

*Proof.* Put θ = β^{−α′} < 1/√p. Along the given n, e_0·Π_ℓ ρ_ℓ ≤ e_L ≤ (log K_L)^{−α′+o(1)} and
β^L ≤ log K_L/log K_0, so the geometric mean of ρ_1, …, ρ_L is at most θ^{1−o(1)} (if L stays bounded then e_L
is bounded below and α′ = 0). Hence for large n some level ℓ(n) has ρ ≤ θ′ := (θ + 1/√p)/2, and since ξ_ℓ → 0,
ρ ≤ (1−ξ)(1/√p − η) with η = (1/√p − θ)/3 > 0. By Lemma D2 some C ∈ 𝒞 has every piece below (E_C/√p − η)λ at
λ = λ_{ℓ(n)} ≥ λ_min(n). 𝒞 is finite, so one C occurs for infinitely many n, with λ → ∞ and at most
2^{τ(λ)} = 2^{o(λ)} pieces. That is the hypothesis of the win-win theorem (review-link). Its conclusion is 1 and
2. Then 3 and 4 are Theorem R and Theorem C1-AN applied to k̄. ∎

**Corollary D′ (contrapositive).**
- Under WETH (R?): over every field of characteristic 0, every (p, β, 𝒞)-engine has α′ ≤ ½·log_β p. For
  Anthropic's type: certified time ≥ 2^{n/(log n)^{1/2+o(1)}}.
- Under rWETH (R?): the same over every field.
This extends rebase Cor. 2 (one level, one configuration) to whole towers with level-dependent pieces.

**The gap, in words.** For algorithms of Anthropic's type the exponent on log n is at most 1/2, or else 3-SAT is
in 2^{O(n^{1−δ})}. The second alternative is not reached by the engine itself: it is a different algorithm,
which exists because the engine's pieces refute flatness.

**What the theorem does not cover.**
- Levels with more merges than "dimensions" (p > β). For Δ₃ with rows, columns and diagonals, p = 3, β = 2, the
  threshold is ½·log₂3 ≈ 0.79, not 1/2. Under FH an engine of that type with α′ ∈ (1/2, 0.79] is not excluded;
  whether one exists is open (Route 1 of `next/ideas-3sat.md`). So "beating exponent 1/2 forces ¬flat" is
  **false as a statement about all tower engines** unless the three-merge floor can be raised; it is true for
  p ≤ β (rectangle levels, product-merge levels).
- Configurations with edges internal to some merge, growing lists 𝒞, non-tower algorithms. Under FH the general
  oblivious floor of `vpvnp/b1` is polynomial (e_K ≥ 1/(16√K)), so FH alone does not exclude power saving by
  other kinds of algorithm.

## D1.4 Sub-constant improvements: what accumulates and what cannot [D]

Write ρ_ℓ = (1/√p)(1 − η_ℓ) for a (p, p, 𝒞)-engine (so the benchmark is e = (log K)^{−1/2}). Then
e_L·(log K_L)^{1/2} ≳ Π_ℓ (1 − η_ℓ), with L ≤ log_p log K_L ≤ log log n.

1. **A deficit that depends only on the level cannot hide.** If η_ℓ ≥ η > 0 at a fixed level for infinitely many
   n, the win-win applies at that level, since λ → ∞ there. So an "accumulating" engine must have
   max_ℓ η_ℓ(n) → 0 as n → ∞.
2. **Accumulation is arithmetically possible.** Example: η_ℓ(n) = L(n)^{−1/2} for all ℓ ≤ L(n). No level is below
   the floor by a constant, yet Π(1−η_ℓ) ≈ e^{−√L} → 0: certified time
   2^{O(n/(√log n · e^{√(log log n)}))} = 2^{o(n/√log n)}.
3. **FH as stated does not forbid it.** The flat floor is c_m ≥ (E/√p)λ − r(λ) with r(λ) = o(λ) and no rate:
   r(λ) = inf_{M,ε} [O(λ/M) + ελ·O(1) + c(C, M, ε)·τ(λ)], where c(C, M, ε) is the scale at which the
   Euclidean set (legs at distance M, hubs) is an ε-approximate price. AN's FH says only that c is finite. A
   deficit r(λ)/λ ≈ 1/√(log log λ) is consistent with FH and suffices for item 2.
4. **But the accumulation is bounded.** By Lemma D1, η_ℓ ≤ √p·ε_𝒞(λ_min(n)) =: ε_n → 0 for all ℓ, so
   Π(1−η_ℓ) ≥ (1−ε_n)^L ≥ (log K_L)^{−O(ε_n)} = (log K_L)^{−o(1)}.

**Conclusion [D].** Under FH: e_L ≥ (log K_L)^{−1/2−o(1)}, and nothing better follows from FH alone. The link
"rate beating ⇒ a piece below the floor by a constant η" holds exactly for improvements by a fixed power
(log n)^γ. For improvements by (log n)^{o(1)} — in particular for 2^{o(n/√log n)} — it fails:

**[X] Sharp gap from the win-win.** "A (2,2,{crossing})-engine with certified time 2^{o(n/√log n)} forces ¬FH"
is not derivable, by items 2–3. It becomes derivable under an effective flat hypothesis:

**Proposition D3 (sharp form under a rate) [D].** Suppose FH holds over k with a rate such that
ε_𝒞(λ)·log log λ → 0 (for instance c(C, M, ε) ≤ exp(exp(o(1/ε))) for the configurations of 𝒞, with τ = O(log λ)).
Then every (p, p, 𝒞)-engine over k has e_L ≥ (1−o(1))·e_0·(log_p-normalised) (log K_L)^{−1/2}·const, i.e. certified
time 2^{Ω(n/√log n)}. Contrapositive: an engine of this type with certified time 2^{o(n/√log n)} refutes FH **with
that rate**. It does not by itself refute FH, and so does not give contracting.

*Proof.* Π_ℓ(1−η_ℓ) ≥ 1 − L·ε_n and L ≤ log log n ≈ log log λ_min up to constants (λ_min ≥ n^{7/9} in the
engine's parameters). ∎

## D1.5 If OpenAI's flats theorem holds: what remains meaningful [D given K-OA]

EG Theorem 1.2: over every field there are spectral flats of every dimension, with wire prices **exactly**
Euclidean; on each finite set S the prices are δ(S)·log₂F_S for one spectral point F_S. OA spectral points are AN
spectral points, so FH holds over every field, with ε = 0 and scale c = δ(S) = O(M·E) for the far-leg set.

- Then r(λ) = inf_M [O(λ/M) + O(M·τ(λ))] = O(√(λ·τ(λ))): relative deficit O(√(log λ/λ)) for polynomially many
  pieces. Summed over ≤ log log n levels with λ ≥ n^{7/9} this is negligible.
- Using 2^{τ} pieces with large τ does not help: it buys at most O(√(λτ)) bits per copy at a level whose bits
  are worth a factor e_ℓ in the exponent, and costs τ bits per copy in the number of terms. The net gain is at
  most O(e_ℓ²λ) per copy, a relative gain O(e_ℓ), and Σ_ℓ e_ℓ converges. So the total gain is a constant factor.
- **Consequence.** Given EG 1.2, every (p, β, 𝒞)-engine has e_L ≥ c·(log K_L)^{−(1/2)log_β p}; for Anthropic's
  type the rate Θ((log K)^{−1/2}) is optimal up to a constant, over every field, unconditionally. Hypothesis 1 of
  Theorem D never holds, and the "jump" never happens. OA's own Corollary 6.2 is the one-level, two-term case of
  this (limit √(t²+u²) for the crossing).

What is still meaningful in that world:
1. **Theorem D as a theorem from Anthropic's side alone.** It uses thm_alt, the price method and Theorem R; no
   OpenAI input. It gives the dichotomy "exponent ≤ 1/2 for the class, or power-saving 3-SAT" without trusting
   EG 1.2, and Corollary D′ under WETH or rWETH. If EG 1.2 has a gap, Theorem D is the surviving statement.
2. **Nothing by field or characteristic:** EG 1.2 is claimed over every field, so there is no uncovered field.
3. **The right theorem for the OA world is the one with "contracting" in place of "¬flat".** Flat and contracting
   are not exclusive (Euclidean pull-backs to Mat_μ(F₂) have D(μ)²/D(1)² < 2). If contracting fails, √rk on
   Mat_μ(F₂) is a price for every μ (AN D.3), and these are non-Euclidean (building) prices. The same price
   method with √rk placements gives floors that hold under ¬contracting; any engine beating such a floor proves
   contracting, hence power-saving 3-SAT, **even if flats exist**. This is non-vacuous exactly on configurations
   where a √rk placement beats the best Euclidean one. The first candidate is Δ₃ with three merges (Euclidean
   floor 1/√3, window up to 1/√2). See spec S3.

## D1.6 The network-rewriting formulation (strategist's [C], via MM Lemma 4.1) [X as stated]

Proposed: "an exact expansion of every volume-s network into terms with fewer shared bits, fixed topology per
term, in 2^{O(s/(log s)^c)}, c > 1/2, forces ports."

- **MM Lemma 4.1 does not apply.** It needs one fixed topology that realises the wires of every permutation in
  the support. A rewriting algorithm has one layout per term (HC 13.1: "a history specifies the layout"), and the
  network is fixed, not a family of permutations.
- **What the price method gives for such expansions [D].** If the wire product W = Σ_{h≤T} ⊗_{P∈Π_h} a_{h,P}
  (each term a product over the pieces of a partition Π_h of the legs), then for every spectral point on legs and
  hubs: log₂T ≥ Σ_e d(e) − max_h min_{hubs} Σ_ℓ d(ℓ, o_{Π_h(ℓ)}). (Each a_{h,P} is a restriction of the star of
  wires from its legs to a hub.)
- **Why this is weak against term-dependent partitions [D, heuristic].** The right side is positive only if every
  admissible piece is a tight cluster while wire ends are far apart. When the algorithm may choose any partition
  into pieces of size m, pieces can mix far points and the star cost per crossing wire is ≥ its length up to a
  1/m correction (checked for orthonormal and simplex placements: saving 1/(2m) per leg). So the bound is about
  log T ≳ s/m, which for m = s^{1/2} is 2^{√s}, far from s/√log s. The engine's class escapes this only because
  it has p fixed merges, which is exactly the hypothesis of Lemma D1.
- So a gap theorem for general rewriting algorithms needs an idea beyond the price method and Lemma 4.1. Open.

---

# Specs for executors

**S1 (compiled code, 30 min; sanity for C1.2).** For n ≤ 10, k ≤ n+1: enumerate all a ∈ F₂^{n+k−1} and verify
that for every z ≠ 0 the map a ↦ T_a z is exactly balanced (each value of F₂^k taken 2^{n−1} times), with
(T_a)_{j,i} = a_{n−1+j−i}. Then for random S ⊆ F₂ⁿ with 2^{k−2} ≤ |S| ≤ 2^{k−1}, compute exactly
Pr_{a,b}[|S ∩ h^{−1}(0)| = 1] and check ≥ 3/16.

**S2 (Lean, 2–3 h).** (i) `toeplitz_uniform`: for z ≠ 0 in (Fin n → ZMod 2), the map a ↦ T_a z from
(Fin (n+k−1) → ZMod 2) to (Fin k → ZMod 2) has all fibres of equal cardinality. (ii) `vv_isolation`: for a
pairwise-independent h and 2^{k−2} ≤ |S| ≤ 2^{k−1}, the probability of exactly one zero in S is ≥ 3/16.
(iii) `parsimonious_tseitin`: for a Boolean circuit C, the number of satisfying assignments of
F ∧ Tseitin(C) ∧ (out = 0) equals |{x : F(x) ∧ C(x) = 0}|.

**S3 (compiled code, 3 h; D1.5 item 3).** Δ₃ with rows, columns and diagonals (9 edges, 18 legs, 3 merges × 3
hubs). Place every leg and hub at a point of Mat_μ(F₂), μ = 2 (16 points) and μ = 3 (512 points), with metric
√rk(a−b); several legs may share a point. For a placement compute b_m = (L − H_m)/δ_m (notation of b2 §1), and
the value max over convex combinations of placements of min_m b_m (b2's symmetrisation is allowed). Search by
simulated annealing with restarts, also over scaled copies (legs at "distance M" realised by using
Mat_μ ⊂ Mat_{μ′}). Report the best value against the Euclidean 3√3 ≈ 5.196 and the two-merge 9/√2 ≈ 6.364.
- Value > 3√3: a floor that holds under ¬contracting and exceeds the flat floor, so a three-merge engine in the
  window would prove contracting even if flats exist. That makes the gap theorem non-vacuous in the OA world.
- Value ≤ 3√3 after an exhaustive enough search at μ = 2: record that √rk prices add nothing on Δ₃.
Calibrate first on the crossing: the unit square {0, e₁₁, e₂₂, e₁₁+e₂₂} must reproduce 2‖λ‖₂.

**S4 (referee, 2 h).** (a) HC 13.1 in characteristic p: confirm from the proof that the map scalars lie in F_p (or
a fixed finite extension) and that nothing in §13 uses characteristic 0 before the final paragraph. (b) The
disjoint sunflower branching of C1.4: redo the depth and leaf count of IM §7 with the extra unit clauses.
(c) In Theorem C1-AN: the cost of evaluating a gate list in the AN program model (claimed O(log) per gate), and
the padding remark for p = 2.

**S5 (reader, 2 h; D1.1).** Majdoddin's Thm 4.13 (every grid algorithm has 1/e(K) ≤ log₂K): does its proof go
through with the floor ρ ≥ 1/√2 − o(1) in place of ρ ≥ 1/2, giving 1/e(K) ≤ C·√(log K) under FH for the true
running time of every algorithm in the class? If yes, Theorem D and Corollary D′ can be stated for running times
rather than certified exponents.

---

# What I would do next

1. Have a referee check C1.4 (it is short) and S4. If it holds, state in the note for the user: "ports in any
   characteristic refutes randomised Weak ETH; under rWETH no characteristic has ports", and move M1 to the single
   hypothesis rWETH.
2. Run S3. It is the only computation here whose outcome changes what the gap theorem means given OpenAI's
   release.
3. S5, to turn "certified exponent" into "running time".
4. Do not spend more on the sharp o(·) gap from Anthropic's side: D1.4 shows it needs a rate in FH that the
   paper's proof of thm_alt (compactness) does not supply.
