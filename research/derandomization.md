# Track E: deterministic Hamiltonicity from deterministic residues

27 Oct 2026. Tags: **[Proved]** means a proof is written here (not Lean-checked). **[Cited]** means a
published result. **[Conj]** means a conjecture. **[Exp]** means an experiment, with its script named.

Primitives assumed (from `hamiltonicity.md`; G has bounded degree, N = |E|, p and q are small):

* (R) `#HC(G; F forced, D deleted) mod q`, and more generally `#(HC(G) ∩ C) mod q` for a
  linear-size CNF side constraint C;
* (W) `P_G(w) mod p`, where `P_G(w) = Σ_{H∈HC(G)} Π_{e∈H} w_e` and `w ∈ {0,…,p−1}^E`;
* (X) the exact integers `F_R(q) = Σ_{X 2-factor of R} q^{cc(X)−1}` for q ≤ Q.

All of them run in deterministic `2^{o(n)}` when `log q = o(√log n)`.

---

## 1. Summary

1. **A better randomized algorithm, using only the top-level theorem** [Proved]. Draw uniform weights
   `w ∈ F_p^E` and test whether `P_G(w) ≢ 0 (mod p)`. By Alon–Füredi the test succeeds with
   probability `≥ p^{−n/(p−1)}`. Take `p ≈ √log n`. The CNF then has length `O(N log² p)` and width
   `O(log p)`, so Anthropic's Lean Main Theorem, which is uniform in k, gives one-sided
   `2^{O(n (log log n)²/√log n)} = 2^{O(ρ(n))}`. This beats §5a's `2^{δn}`. It matches §5 without
   using any internal lemma (§3).
2. **Non-uniform derandomization is free** [Proved]. One fixed list of `2^{o(n)}` weight vectors
   works for every bounded-degree graph on n vertices. So no information-theoretic barrier exists
   once G is known. Any barrier has to be about *uniformity*, that is, about explicit hitting sets.
3. **Hardness ⇒ derandomization** [Proved, standard]. If E needs #P-oracle circuits of size
   `2^{γℓ}`, then the test of item 1 derandomizes to deterministic `2^{o(n)}`. This is the analogue
   of Klivans–van Melkebeek for Valiant–Vazirani.
4. **Black-box barrier** [Proved]. Suppose an algorithm sees `S = HC(G)` only through
   `Σ_{x∈S} w(x) mod q` with q ≤ Q, adaptively, with *arbitrary* weight functions w. Then it needs
   `F ≥ (2^N/lcm(1..Q) − 1)/ln Q` queries. The proof uses the Davenport constant. It generalizes the
   parity barrier of §8 and is a deterministic counterpart of Dell–Kabanets–van Melkebeek–Watanabe.
5. **Low-support strategies are characterized exactly** [Proved]. Let
   `t_q(G) = min{|T| : #{H ⊇ T} ≢ 0 mod q}`. Every query (restriction, weighted or CNF-constrained)
   that depends on H only through `H ∩ S` with `|S| < t_q` returns 0 mod q. Restriction search is
   therefore deterministic `2^{o(n)}` **iff** `t_Q(G) = o(n)`. Also `t_q(G) ≤ log₂ #HC(G)`
   (Theorem 1, a Reed–Muller dual-distance argument), and the bound is tight.
6. **Adversaries** [Exp + Proved]. Diamond necklaces give `t_2 = n/4`, but `t_3 = 0`. A necklace of
   gadgets whose route counts are divisible by every q ≤ Q has `t_Q ≥ n/s(Q)`, where s(Q) ≥ Ω(Q) is
   the gadget size. This is o(n) when Q → ∞, so necklaces are **not** a barrier.
7. **Open crux** [Conj R]. Is `t_Q(G) = o(n)` for all bounded-degree Hamiltonian G as Q → ∞? If so,
   decision is deterministic `2^{o(n)}`. A set-system relaxation allows `t_Q ≈ log₂#HC − O(Q)`, so
   any proof has to use graph structure.

---

## 2. Restrictions, support, and t_q

Let `c_T = #{H ∈ HC(G) : T ⊆ H}` for an edge set T.

**Lemma 1 (duality) [Proved].** For any q, the following three quantities are equal:

* `min{|D| : #HC(G−D) ≢ 0 mod q}`;
* `min{|T| : c_T ≢ 0 mod q}`;
* `min{|F|+|D| : #HC(G; F forced, D deleted) ≢ 0 mod q}`.

Call the common value `t_q(G)`, and set `t_Q = min_{q≤Q} t_q`.

*Proof.* Inclusion–exclusion gives `#HC(G; F, D) = Σ_{T⊆D} (−1)^{|T|} c_{F∪T}`. In the other
direction, `c_T = Σ_{D⊆T} (−1)^{|D|} #HC(G−D)`, by Möbius inversion. Both identities hold over ℤ,
hence mod q. ∎

**Lemma 2 (support) [Proved].** Suppose a query has the form `Σ_H f(H ∩ S) mod q` with `|S| < t_q`.
This covers every weighting `w` with `w_e = 1` off S and every CNF side constraint on the variables
`x_S`. Such a query returns 0.

*Proof.* `#{H : H ∩ S = A} = Σ_{A⊆T⊆S} (−1)^{|T∖A|} c_T ≡ 0`. ∎

Two consequences follow. Every strategy, adaptive or not, that only asks queries of support < t_Q
sees only zeros. And the search over all restrictions of size ≤ s costs `Σ_{j≤s} C(N,j)2^j` primitive
calls. So:

> **Restriction search decides Hamiltonicity deterministically in `2^{o(n)}` iff `t_Q(G) = o(n)` for
> all Hamiltonian G**, with `Q = 2^{(log n)^{1/2−ε}}`.

**Smith/Thomason degeneracy.** In a cubic graph every `c_e` is even, so `t_2 ≠ 1`. In the
experiments, `t_2 ∈ {0, 2, 3, 4}` for cubic graphs. By Thomason's lollipop argument the route count
of a cubic 2-terminal gadget is even: the gadget plus an extra vertex z joined to both terminals has
odd degree everywhere except at the two ends of the edge za. Experiment E3 confirms this, with
**all** route counts observed even. Odd primes therefore need gadgets with at least 2p routes. The
smallest gadgets found have r = 6 at k = 10 vertices and r = 10 at k = 14.

**Theorem 1 [Proved].** For every prime p, `t_p(G) ≤ log₂ #HC(G)`. For composite q, `t_q ≤ t_p`
whenever p | q.

*Proof.* Fix a Hamiltonian cycle H₀. For each H let `D_H = H₀ ∖ H`, and let
`v(D) = #{H : D_H = D} mod p` for D ⊆ H₀. Then v(∅) = 1, because only H₀ has `D_H = ∅`.

Now take S ⊆ H₀. On one hand `#HC(G−S) = Σ_{D⊇S} v(D)`. On the other, Lemma 1 makes this ≡ 0 for
|S| < t. So v, viewed as a function on `{0,1}^{H₀}`, is orthogonal over F_p to every multilinear
monomial of degree < t. Over any field this orthogonal complement is exactly
`{(−1)^{|x|} g(x) : deg g ≤ n−t}`. It contains that set because `Σ_x (−1)^{|x|} h(x)` is ± the top
coefficient of h, and the two dimensions add up to 2^n.

A nonzero multilinear g of degree ≤ n−t is nonzero on at least `2^t` points of the cube. Hence there
are at least 2^t distinct sets D_H, so `#HC ≥ 2^t`. ∎

**Tightness.** The diamond necklace has `t_2 = log₂ #HC = n/4`. Annealing (E2) finds cubic graphs
with `t_2 = log₂#HC` exactly: 8 cycles and t = 3 at n = 12 and 16, and 16 cycles and t = 4 at
n = 20.

**Corollary [Proved].** Run restriction search up to size `⌊log₂ #2f(G)⌋`. The number of 2-factors,
`#2f = F(1)`, is computed exactly by (X). If nothing is found, answer "no". This gives deterministic
decision in time `C(N, log₂#2f)·2^{O(ρ)}`, which is subexponential whenever `log #2f = o(n/log n)`.
That condition is weak: bridgeless cubic graphs have exponentially many 2-factors.

**The relaxation is too weak [Proved].** Abstractly, take v(D) = 1 on even-size D and v(D) = L−1 on
odd-size D, over a t-dimensional subcube, with `L = lcm(1..Q)`. This satisfies the conditions mod
every q ≤ Q with only `#HC ≈ 2^{t−1}L` cycles. So the set-system relaxation allows
`t_Q ≈ log₂#HC − O(Q)`. Realizing this in bounded-degree graphs requires multiplicities that depend
on a *global parity*.

My attempts all failed for the same reason. 2-strand "braid with trace closure" constructions do
realize parity-dependent connectivity, but the closure gadget carrying the `−1 ≡ L−1` multiplicity
has only O(Q) vertices, and touching it with O(1) edges kills the cancellation.

**Conj R.** For bounded degree, `t_Q(G) ≤ n·f(Q)` with `f(Q) → 0` (I would guess `Õ(1/Q)`).

* Evidence: random graphs have t = O(1) (E1). Necklaces give `f ≥ 1/s(Q)`. Annealing never beat
  the necklace ratio.
* If true: deterministic `2^{O(n f log(1/f)) + O(n/(log n)^ε)}`.
* If false: some family has robust divisibility on Ω(n) disjoint "sources" for every small modulus
  at once.

---

## 3. Weighted test over F_p (randomized, top-level theorem only)

`P_G` is multilinear of degree n with 0/1 coefficients, so it is a nonzero polynomial over every F_p
when G is Hamiltonian, and it is identically 0 otherwise.

**Alon–Füredi** [Cited, Alon–Füredi 1993]. A polynomial of degree d that does not vanish on the grid
`A₁×…×A_N` is nonzero on at least `min{Π y_i : 1≤y_i≤|A_i|, Σy_i ≥ Σ|A_i|−d}` points. With
`A_i = F_p` and d = n, the extremal point puts deficit p−1 on n/(p−1) coordinates. So

```
Pr_w[P_G(w) ≢ 0] ≥ p^{−n/(p−1)} = 2^{−n log p/(p−1)}.
```

**Encoding.** The CNF has the following parts:

* p colours on each vertex, ⌈log p⌉ bits with a comparator `c_v < p`;
* the root coloured 0;
* bitwise `x_e → (c_u^i ↔ c_v^i)`;
* weight bits z_e with `x_e = 0 → z_e = 0` and `x_e = 1 → z_e < w_e`, using O(log p) clauses of
  width O(log p);
* the vertex constraint "exactly two".

Its model count is `Σ_X p^{cc(X)−1} Π_{e∈X} w_e ≡ P_G(w) (mod p)`. A weight w_e = 0 is a deletion.
The total is `m = O(N log p)` clauses of width `k = O(log p)`, so km = O(N log² p).

**Cost.** Anthropic's Main Theorem gives `2^{O(N log² p/√log N)}` per test. With `p ≈ √log n`, the
test takes `2^{O(n(log log n)²/√log n)}` and succeeds with probability
`2^{−O(n log log n/√log n)}`. The total is randomized one-sided `2^{O(ρ(n))}`.

This compares with the existing results as follows:

* §5a: `2^{δn}`, via CIKP.
* §5: the same bound, but it needs the paper's internal lemmas and a bit-complexity check that has
  not been written out.

[Exp E4, `derand_fp_weights.py`] The empirical rates are always far above the guaranteed bound.
Random cubic graphs with n = 24 give 0.134 at p = 7 (bound 4·10⁻⁴). The diamond necklace with
n = 20 gives 0.086 (bound 1.5·10⁻³).

**Non-uniform derandomization [Proved].** There are at most `n^{Δn}` graphs. Take
`M = ⌈Δ n ln n · p^{n/(p−1)}⌉ + 1` independent random weight vectors. By a union bound, with
positive probability they hit every Hamiltonian G. So a fixed advice list of `2^{o(n)}` vectors
gives deterministic `2^{O(ρ(n))}` circuits. This is why "strengthen the oblivious bound to the
realizable families HC(G′)" **fails** once G is known: oblivious families of size `2^{o(n)}` exist.

**Conditional uniform derandomization [Proved, standard].** The test `T_G(w) = [P_G(w) ≢ 0 mod p]` is
a poly-size circuit with one #P-oracle gate, and it accepts a fraction `ε ≥ 2^{−o(n)}` of inputs.
Assume `E ⊄ i.o.-SIZE^{#P}(2^{γℓ})`. The relativized Impagliazzo–Wigderson construction then gives
generators with seed `O(log(1/ε) + log n)/γ = o(n)` that fool oracle circuits of size `1/ε`. So the
deterministic time is `2^{O(ρ(n)/γ)}`. This parallels Klivans–van Melkebeek's derandomization of
Valiant–Vazirani. Unconditionally, any generic hitting-set generator for all dense
`2^{o(n)}`-time-recognizable sets yields circuit lower bounds (the standard HSG ⇒ hard function
argument). So a black-box derandomization of this test is a lower-bound result in disguise. A
white-box algorithm exploiting G is not covered by this argument.

---

## 4. Black-box barrier (Davenport)

**Theorem 2 [Proved].** Let U be a set of size M. An adaptive deterministic algorithm queries an
oracle for an unknown S ⊆ U. Query i chooses a modulus `q_i ≤ Q` and an arbitrary `w_i : U → ℤ`, and
receives `Σ_{x∈S} w_i(x) mod q_i`. If the algorithm distinguishes S = ∅ from every nonempty S using
F queries, then

```
M ≤ D(⊕_i ℤ_{q_i}) − 1 ≤ L_Q (1 + F ln Q),     L_Q = lcm(1..Q) = e^{(1+o(1))Q}.
```

*Proof.* Look at the run on S = ∅. All of its answers are 0, so it is one fixed query sequence.
Map each x ∈ U to `v_x = (w_i(x) mod q_i)_i ∈ G = ⊕ℤ_{q_i}`. If M ≥ D(G), some nonempty S has
`Σ_{x∈S} v_x = 0`. That S then follows the same run and gets the same answer. The upper bound on D
is `D(G) ≤ exp(G)(1+ln(|G|/exp(G)))` [Cited: van Emde Boas–Kruyswijk 1967, Meshulam 1990], with
`|G| ≤ Q^F`. ∎

For `U = {0,1}^N` and `Q = 2^{(log N)^{1/2}}`, this gives `F ≥ 2^{N−o(N)}`. For q = 2 alone,
D = F + 1 recovers the bound of §8. The theorem covers restrictions, CIKP hashes, F_p weights,
mixed moduli and adaptivity.

**Relation to DKMW** [Cited]. Dell–Kabanets–van Melkebeek–Watanabe (CCC 2012, CC 2013) show the
following. Randomized isolation, including the "odd number of solutions" variant, with success
above 2/3 would put NP in P/poly. Black-box isolation has success O(1/n). Theorem 2 is the
deterministic, exponential-scale analogue. Together with §3, the picture is:

* black-box access needs `2^{N−o(N)}` queries;
* non-uniform white-box access needs only `2^{o(n)}`;
* uniform white-box access follows from hardness assumptions, and is open unconditionally.

So deterministic parity-to-decision for HC is a specific instance of derandomizing a dense RP-type
test. It is "derandomized VV for one NP language at exponential scale", and needs no isolation.

---

## 5. Exact integer counts (X)

Write `F_R(q) = Σ_k a_k(R) q^{k−1}`, where `a_k` is the number of 2-factors of R with k cycles and
`a_1 = #HC`.

**Residues.** `F_R(q) mod q = a_1 mod q`. If `#2f(R) < L_Q`, the values recover a_1 exactly, but a
nonzero a_1 is then already visible in some residue. Exact values add nothing to *detection* through
residues; they only let one *prune* "no" branches.

**Positivity ("cone") certificates.** If `(F_R(1..Q))` lies outside `cone{(q^{k−1})_{q≤Q} : k≥2}`
(LP infeasibility), then `a_1 > 0`. The simplest instance is `F(2) < 2F(1)`. This is strictly
stronger than residues [Exp E5, `derand_exact.py`]:

* diamond necklaces have `t_res = n/4` for Q = 2 but are certified at size 0 by the cone test;
* random cubic graphs with n ≤ 20 are certified at size ≤ 1.

**The cone can be neutralized** [Exp]. Truncate the necklace, replacing each vertex by a triangle.
This adds an all-triangle 2-factor and many mixtures, and leaves #HC unchanged. With Q = 2 or 3 the
cone test then gains nothing (`t_ex = t_res = m`, for m = 2, 3). With Q ≥ 4, cone-only certificates
work again at size 1. The exponential curve is a Chebyshev system, so the cone is cyclic and
neighborly in dimension ≥ 4, and sparse profiles `a_1 v_1 + v_K` lie outside it. An adversary needs a
dense ("interior") 2-factor profile that is robust under small restrictions.

**Status [Conj].** The cone test widens the gap between adversary and algorithm but probably does
not close it. Abstractly, any profile with a_1 hidden in the interior defeats it, and the §8
Vandermonde barrier says exact filters need Q ≥ n−4.

---

## 6. Experiments (scripts in `research/scripts/derand_*.py`)

| exp | setting | result |
|---|---|---|
| E1 `derand_random.py` | random cubic n = 12…36 (40–100 samples each) | #HC ≡ 0 mod 2 in 37–62% of Hamiltonian samples. **Never** ≡ 0 mod all of {2,3,4,5,7}. t_2 ∈ {0,2,3}, never 1 (Smith). t_3 ≤ 2. Smith violations 0. Theorem-1 violations 0 |
| E1 | random 4-regular n = 14, 18 | t_2 ≤ 3 (n = 14), ≤ 1 (n = 18); t_all = 0 always |
| E2 `derand_adversary.py` | annealing on cubic graphs, maximizing t_Q | Q={2}: t = 3 (n = 12, 16), t = 4 (n = 20), always with #HC = 2^t (Theorem 1 tight). Diamond necklace: n/4 = 3, 4, 5. Q={2,3}: t = 2 at n = 16, 20 |
| E3 `derand_gadgets.py` | random cubic 2-terminal gadgets k ≤ 14 | route counts all even (Thomason). Smallest r ≡ 0 mod 3: k = 10, r = 6. Mod 5: k = 14, r = 10. Best τ/k: 1/4 for {2}, 1/10 for {2,3}, 1/14 for {5} |
| E4 `derand_fp_weights.py` | F_p weight test | empirical success ≫ Alon–Füredi bound in every case |
| E5 `derand_exact.py` | exact counts, cone LP | necklace: t_res = 3, 4, 5 vs t_ex = 0. Truncated necklace: t_ex = t_res for Q ≤ 3, t_cone = 1 for Q ≥ 4 |

Caveat: at n ≤ 36 the counts are tiny, typically 2^{3–10}, so residues mod all q ≤ 7 almost
always detect directly. Small n says little about the regime `log #HC ≫ Q`. Hence the emphasis on
t_q and structured adversaries.

## 7. What would settle it

* **Positive:** prove Conj R, even in the form `t_Q ≤ n/ω(1)` for Q → ∞. One route is a
  "divisibility-source" decomposition: robust p-divisibility under t restrictions forces t
  edge-disjoint local structures, each carrying ≥ log p routes.
* **Negative (for restriction and weight search):** build a bounded-degree family with
  `t_Q ≥ cn` for `Q = 2^{(log n)^{1/2}}`. That needs a global-parity multiplicity twist robust to
  touches, which is what §2 shows no local gadget achieves.
* **Either way:** uniform deterministic decision via black-box use of the residue oracle is impossible
  (Theorem 2). Non-black-box use is equivalent to explicit hitting sets for `{P_G mod p}`, which
  follow from circuit-hardness assumptions (§3).
