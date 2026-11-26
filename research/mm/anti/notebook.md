# anti — "n² is impossible even at the bit level": statements and proofs

Executor **anti**, 26 Nov 2026. Written as I go.

**Standing assumption (user's decision).** OpenAI's family 379 (24 Nov 2026) is taken as given. We do not
verify it. Every [R] below is "proved from the paper's displayed statements", nothing more.

Tags: **[K]** quoted from the paper or a companion (verbatim where in quotation marks); **[R]** proved here from
[K] statements, full proof given; **[C]** conjecture / opinion; **[L]** literature outside the release
(from memory or web search, flagged when not checked).

Sources (sparse clone, scratchpad `survey/oa`):
- [MM] "The matrix multiplication exponent is nine fourths", `preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.txt`.
- [42] "Euclidean geometry in the asymptotic spectrum of tensors" (same release), `paper.txt`.
- [43] = [MM]'s reference [43], "Circuit lower bounds for Hamiltonian cycle and the permanent" (fetched; pdftotext).
- [FT] "The logarithmic exponent of finite Fourier transforms" (fetched; pdftotext).
- `lean/docs/379.md`, `lean/ComparatorChallenges/MatrixExponent.lean`.

Note on numbering: the brief calls [MM]'s reference [43] "network complexity"; in [MM]'s bibliography [42] is the
Euclidean-geometry paper and [43] is the Hamiltonian-cycle/permanent paper. Both are used in §4 of [MM].

---

## Step 1. The paper's network lower bounds, exactly

### 1.1 The model [K, MM §2.1, verbatim]

> "A bit tensor of arity u is a function {0,1}^u → k. In a tensor network each vertex carries such a table. A wire
> pairs two argument positions, and each unpaired position is a named exterior bit. For a fixed setting of the
> exterior bits, multiply the vertex entries and sum over all settings of the internal wires. This gives the tensor
> represented by the network. A network is trivalent if each vertex has arity at most three. Its size counts the
> vertices and exterior bits. Its volume counts the vertices and all wires, including the exterior wires. These
> counts agree up to an absolute factor by trivalency."

Points to note.
- **All wires are bits.** The internal summation is over {0,1} per wire. Field elements occur only as *table
  entries*. So "non-Boolean field values on wires" cannot arise; the only non-Boolean objects are the k-valued
  entries of tables and the k-valued value of the represented tensor.
- **Tables are arbitrary.** Any function {0,1}^{≤3} → k, no restriction ("gate tables allowed" = all).
- **"Computes" = represents exactly.** The represented tensor must equal the target as a function {0,1}^{ext} → k,
  entry by entry, in k. For a 0/1 target (a predicate) this means: value 1 ∈ k on accepted settings, 0 on rejected.
  [43, §12.2] adds: "Loops, parallel wires and disconnected networks are allowed."
- **Fields.** Theorem 2.2 is for finite fields k; σ depends on k. Lemma 4.1 is stated for "the field", and its
  hypothesis (no ports) depends only on the characteristic [42, remark after Def. 11.1, quoted in 1.4].
- vol_k(T) = "minimum trivalent volume over k".

### 1.2 Theorem 2.2 [K, MM p. 7, verbatim]

> "For w ≥ 1, let D_w be the zero-one tensor for a list of 2^w words of 2w bits each. Its value is one exactly when
> the words are pairwise distinct. It has n_w = 2w·2^w exterior bits. The tensor D_w^{⊗t} tests distinctness
> separately within each of t independently specified lists. The network may connect vertices across lists."
>
> "**Theorem 2.2 (Volume of list distinctness).** There is a constant σ > 0, depending only on k, such that for all
> sufficiently large w and every integer 1 ≤ t ≤ 2^w, vol_k(D_w^{⊗t}) > t·n_w·w^σ.  (2.2)"

**Value of σ.** Not explicit. The proof splits into two cases that the paper does not decide:
- no ports (§4.2): "this proves (2.2) for any fixed 0 < σ < 1/2" [K];
- ports (§4.3): "Choose b > max{2, 2/ξ} and 0 < σ < min{a/4, bδ/4, 1/4}" [K], with a from [42, Prop. 14.1] and
  δ, ξ from [43, Thm 12.1], none given numerically.
So the unconditional content is: *some* σ = σ(k) > 0; σ < 1/4 is all one can safely assume is available in the
ports case, and its actual value is ineffective (a, δ unspecified).

### 1.3 "Prop. 2.3" — what it is [K, MM p. 8]

Correction to the brief: **Proposition 2.3 is "Over every finite field k, ω_k ≥ 9/4."** The Boolean-circuit
embedding is a sentence *inside its proof*, applied to one specific circuit (a sorting network):

> "A sorting network on 2^w records uses O(2^w w²) comparisons [8]. Comparing and conditionally exchanging two
> 2w-bit words takes O(w) Boolean gates. After sorting, the conjunction of the inequalities between adjacent words
> computes D_w. To realize this circuit as a tensor network, use the zero-one table of each gate, copy bits at
> fan-outs with equality tables, and pin the output to one. For each accepted input there is exactly one consistent
> assignment of the internal wires. This gives a trivalent network over k of size m_0 = O(n_w w²)."

The general embedding "Boolean circuit of size s ↦ trivalent network of size O(s)" is not stated as a result; it is
the obvious generalisation, which I prove in Step 2 (Lemma E).

### 1.4 Ports [K]

[MM §4.2]: "A class of Hadamard spaces has ports if it admits regular graphs of unbounded order and common bounded
degree with the following property. For every placement of their vertices into any space of the class, the mean
squared distance of two independent uniform vertices is at most a fixed constant times the mean squared edge length.
A field has ports when its Hadamard spectral spaces have this property [42, Definition 11.1]."

[42, Def. 11.1 and the remark after it]: "A field has ports if it admits a family of regular, symmetric multigraphs
of unbounded order and bounded degree, and a constant γ such that V(x) ≤ γ E_G(x) for every graph in the family and
every assignment into a spectral space over the field. [...] **This property depends only on the characteristic**,
since it concerns only joint prices of binary wires (Lemma 2.3)."

[42, Prop. 11.2]: "If a finite field F has a largest spectral flat dimension k, then F has ports." [43, §1]: "Either
outcome gives a circuit lower bound (Figure 1). The proof requires no classification of the characteristics."
So **which characteristics have ports is open in the release.**

### 1.5 Lemma 4.1 — the "no ports" routing lemma [K, MM p. 13, verbatim]

> "**Lemma 4.1 (Uniform destinations).** Let the field have no ports. Consider a fixed trivalent topology with r
> input bits and r output bits. Suppose that for every permutation in the support of a distribution, some choice of
> vertex tables realizes the r independent wires joining each input to its assigned output. If each input has a
> uniform destination on a set of q ≥ 2 outputs, the topology has size Ω(r√(log q)). The destination sets may depend
> on the input."

Key sentences of the proof (verbatim), which fix the reading of the hypotheses:
> "Give each exterior bit its own equality leaf. [...] Let α be the law of a uniform oriented edge, and let µ be the
> joint law of a uniform input and its random destination. For any placement in a spectral space with distance d,
> r E_µ d ≤ m E_α d. Indeed, for each permutation the network tensors locally contract the product of its internal
> bit wires to the prescribed exterior wires. Monotonicity and additivity of prices bound the sum of the destination
> distances by the sum of the internal edge lengths. Average over the permutations [...]"
> "[...] Every pair has ν-mass at most 2/(rq), so H_ν(Y|X) = H_ν(X,Y) − H_ν(X) ≥ log₂(rq/2) − log₂ r = log₂(q/2)."

Reading [R, from the proof text]:
- "permutation" = a bijection from the r input bits to the r output bits; "realizes the r independent wires" = the
  represented tensor is exactly ⊗_i (e₀⊗e₀ + e₁⊗e₁) on the pairs (input i, output π(i)).
- The topology (graph + which positions are exterior) is fixed; **the tables may depend on the permutation.**
- Only the **marginal** law of each input's destination enters (through µ and the bound µ(pair) ≤ 1/(rq)); the
  destinations of different inputs may be arbitrarily correlated.
- The constant in Ω depends on the field (through the no-ports subclass of [43, Thm 6.1]) and nothing else.

Its use in the paper [K]: "In a network for Tag(h,h)^{⊗t}, pin each list's tags to a uniform permutation. The
topology realizes a permutation of r = tNh payload bits. Each input bit has q = N possible destinations [...]. By
Lemma 4.1, 2V + O(tNh) ≥ c·tNh√h." — i.e. the paper itself uses *pinning of input bits to permutation-dependent
values* as the way the tables vary. This is the precedent for our reductions.

### 1.6 The ports case, §4.3 [K, MM p. 14]

> "Fix a finite field with ports. We use the signed counting tensor U_ℓ* on ℓ exterior bits [...]. The exact batch
> lower bound [43, Theorem 12.1] gives δ, ξ > 0 such that, for all sufficiently large ℓ,
> vol_k((U_ℓ*)^{⊗j}) > j·ℓ^{1+δ}  (1 ≤ j ≤ 2^{ℓ^ξ})."
> "The descent with tagged permutations [42, Proposition 14.1] supplies a constant a > 0. [...] given a trivalent
> network of size s in the range N ≤ s ≤ N⁴, with e exterior bits, it constructs a network for d copies of its
> tensor using trivalent gates and Tag(h,h) tests. Its size S [...] satisfies S ≤ Cd·s·h^{−a} + e(log h)^C,
> log₂ d = O((log h)²)."

Then: cheap D_w^{⊗t} ⇒ (two-list construction of §4.1) cheap Tag(h,h)^{⊗t} ⇒ (descent iterated L times)
U_ℓ*-batch of volume o(jℓ^{1+δ}), contradiction. The objects consumed are **Tag(h,h) tests: 2^h records with
h-bit tags and h-bit payloads, one independent permutation per test.** [43, Thm 12.1] is stated as "Fix a finite
field F of characteristic χ" — unconditional on ports [K].

### 1.7 Tag tensors [K]

[MM §4.1]: "Tag(h,h) [...] takes N records (j_i, x_i) and an ordered list of N payloads y_j, with h bits per tag or
payload. Its value is one when i ↦ j_i is a permutation and x_i = y_{j_i} for every i." [MM §16]: Tag(h,w) is the
same with w-bit payloads. §4.1 shows vol(Tag(h,h)^{⊗t}) ≤ 2·vol(D_w^{⊗t}) + O(tNh).

### 1.8 Lean status [K, lean/docs/379.md]

- Formalised (Comparator statements): `square_exponent` (ω = 9/4 over every field, formal division-free circuits),
  `dual_exponent` (α = 1/2), `rectangular_exponent`; Fourier bounds; formal polynomial multiplication **upper**
  bound O_ε(n(1+log n)^{1/2+ε}) "using integer-coefficient circuits that specialize to every field"; VF⊊VBP⊊VP⊊VNP;
  HC/permanent superpolynomial; integer multiplication on tapes (upper bound; lower bound under Weak ETH).
- Not listed: Theorem 2.2, Lemma 4.1, any Boolean-circuit corollary. "The paper's lower bound of ⌈n^{9/4}/2⌉ [...]
  remains unformalized." "The paper's Ω(Jn√log n) lower bound for J independent [formal polynomial] products
  remains unformalized."
- The clone has only Comparator statements (`theorem square_exponent ... := by sorry` in
  `ComparatorChallenges/MatrixExponent.lean`), not proofs. Since the paper's proof of ω ≥ 9/4 goes through Theorem
  2.2, a Lean proof following the paper would contain it internally, but **we cannot check whether the Lean proof
  contains Theorem 2.2 or Lemma 4.1 in any form.** Treat both as paper-only.

