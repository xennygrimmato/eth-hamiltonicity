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

---

## Step 2. Corollary A: an explicit superlinear Boolean circuit lower bound

### 2.1 The embedding lemma [R]

Circuits: acyclic, gates of fan-in ≤ 2 from the full binary basis B₂ (all 16 functions), unbounded fan-out, no depth
bound. Size s = number of gates. Constants may be removed by substituting them into the gates they feed (the result
is a gate of fan-in ≤ 1), so assume none. For a gate basis of fan-in ≤ f, first replace each gate by a B₂-circuit
of size ≤ C_f (any f-ary function has one); everything below changes by the factor C_f.

**Lemma E (circuits as networks).** Let C be a B₂-circuit with inputs x₁..x_N, s gates and outputs y₁..y_m (each
output is an input or a gate). Let k be any field (finite or not). Then:
(a) there is a trivalent k-network with exterior bits x₁..x_N, y₁..y_m that represents the 0/1 tensor
    Γ_C(x, y) = [y = C(x)], with volume ≤ 16s + 4N + 4m;
(b) if m = 1, attaching to y₁ the arity-1 table e₁ (value 1 at bit 1, 0 at bit 0) gives a network for the 0/1
    tensor [C(x) = 1] with volume ≤ 16s + 4N + 6;
(c) if C has extra inputs z₁..z_g ("witness bits") and the z-positions are closed by arity-1 tables ≡ 1, the network
    represents x ↦ #{z : C(x,z) = 1}·1_k, with volume ≤ 16s + 4(N+g) + 6 + 2g.

*Proof.* Call *signals* the N inputs and the s gate outputs. For a signal σ let f_σ = number of gate inputs reading
σ plus number of outputs equal to σ; Σ_σ f_σ ≤ 2s + m.
- Gate g with inputs u, v (or only u): one vertex of arity 3 (resp. 2) with table (a, b, c) ↦ [c = g(a,b)]
  (resp. (a, c) ↦ [c = g(a)]). Its last position is the *source* of signal g.
- Input x_i: its source is an exterior position x_i.
- Copying ("copy bits at fan-outs with equality tables"): a chain of j ≥ 1 equality vertices EQ₃(a,b,c) = [a=b=c]
  has j+2 free positions all forced equal. For a gate signal with f_σ ≥ 2 wire its source to a chain of f_σ − 1 EQ₃
  (leaving f_σ free positions); with f_σ = 1 wire the source directly; with f_σ = 0 wire it to an arity-1 table ≡ 1.
  For an input signal we need f_σ + 1 positions, one exterior: chain of f_σ − 1 EQ₃ if f_σ ≥ 2, an EQ₂ vertex if
  f_σ = 1, an arity-1 table ≡ 1 carrying the exterior position if f_σ = 0.
- Wire each free copy position to the gate input it feeds; for each output y_j leave one free copy position of the
  output's signal exterior, named y_j.
Count: vertices V ≤ s + Σ_σ max(f_σ − 1, 1) ≤ s + (2s + m) + (N + s) = 4s + N + m. Every vertex has ≤ 3 positions
and every wire (internal or exterior) uses at least one position, so wires ≤ 3V and volume ≤ 4V.
Correctness: fix exterior values x, y. A setting of the internal wires has nonzero product only if all copies of
each signal carry one value (equality tables) and each gate's output copy equals the gate function of its input
copies (gate tables). Going through the gates in topological order this forces every signal to its value in C(x);
so there is **at most one** nonzero term, it exists iff y = C(x), and it is the product of table entries all equal
to 1. Hence the value is exactly 1 ∈ k if y = C(x) and exactly 0 otherwise, in every characteristic (no sum of
several nonzero terms ever occurs). This is the paper's sentence "For each accepted input there is exactly one
consistent assignment of the internal wires", now for every input and with the outputs exterior. (b): summing y₁
against e₁ gives [C(x)=1]; +1 vertex +1 wire. (c): for each fixed z the previous argument gives one term of value
[C(x,z)=1]; the ≡1 leaves sum over z. ∎

Remarks. (i) The wires carry bits only; there are no field values on wires to worry about. (ii) Tables used: 0/1
gate graphs, EQ₂, EQ₃, e₁, ≡1 — all defined over the prime field; the network exists over every field.
(iii) Fan-out is paid for with ≤ 2s + m + N extra vertices, hence O(s + N + m) in all.

### 2.2 Corollary A [R from Thm 2.2]

**Corollary A.** Fix any finite field k and let σ = σ(k) > 0 be the constant of Theorem 2.2. For all sufficiently
large w, with N = n_w = 2w·2^w:
1. every B₂-circuit computing list distinctness LD_N = D_w (1 iff the 2^w words of 2w bits are pairwise distinct)
   has more than N(w^σ − 4)/16 − 1 gates; since w ≥ ½·log₂N for large w, this is **≥ c·N·(log N)^σ**;
2. (direct sum) for 1 ≤ t ≤ 2^w, every B₂-circuit with one output computing ⋀_{l≤t} D_w(x^{(l)}) on t disjoint
   blocks — or with t outputs computing all t answers — has more than t·N(w^σ − 4)/16 − 1 − t gates;
3. (nondeterministic) if C(x, z) has g witness bits and #{z : C(x,z)=1} ≡ D_w(x) (mod char k) for every x, then
   16s + 4N + 6g + 6 > N·w^σ. In particular this holds for unambiguous circuits (≤ 1 witness, any k) and for
   parity circuits (k = F₂).

*Proof.* 1: Lemma E(b) gives a trivalent k-network for D_w of volume ≤ 16s + 4N + 6, so by (2.2) with t = 1,
16s + 4N + 6 > N·w^σ. 2: the AND of t blocks is one circuit computing D_w^{⊗t} as a 0/1 function, so (2.2) applies
with this t (a t-output circuit plus an AND-tree of t−1 gates is such a circuit). 3: Lemma E(c) and (2.2). ∎

Other input lengths: for n_w ≤ N < n_{w+1} (and n_{w+1} < 2.2·n_w), let LD_N be D_w on the first n_w bits; the
bound Ω(N (log N)^σ) holds for all large N.

**Checks of every step (the brief's list).**
- *Fan-out*: paid explicitly (equality chains), linear cost. Unbounded fan-out allowed.
- *Constants*: absorbed into gates, or realised by arity-1 tables e_b; linear cost.
- *The output pin*: an arity-1 table e₁ on the output position; this is literally the paper's "pin the output to
  one".
- *Field values*: wires are bits by definition of the model; the represented value is exactly 0 or 1 because at
  most one internal assignment contributes. Works over every k, so we may use whichever k we like; σ(k) depends
  on the k chosen.
- *Basis*: any finite basis of bounded fan-in (constant-factor loss). Not formulas-only, not depth-restricted.
- *What is not covered*: nothing about randomised circuits that err (the network must be exact).

**Upper bound for calibration [R + L].** D_w has B₂-circuits of size O(N log N): AKS sorting network,
O(2^w·w) comparators [L: Ajtai–Komlós–Szemerédi 1983], each comparator on 2w-bit words O(w) gates, total
O(2^w w²) = O(N log N); then 2^w − 1 adjacent comparisons and an AND-tree, O(N). (The paper uses a sorting network
with O(2^w w²) comparisons and gets m₀ = O(n_w w²) = O(N log² N); AKS saves one log.) The function is in uniform AC⁰ (OR over pairs of
AND of XNORs, negated; quadratic size). So **c·N(log N)^σ ≤ size(LD_N) ≤ C·N log N.**

**Positioning [L].** The best lower bounds for explicit functions for B₂-circuits are linear: 3.1n − o(n) (Li–Yang,
STOC 2022), (3 + 1/86)n (Find–Golovnev–Hirsch–Kulikov, FOCS 2016), 3n (Blum 1984); 5n − o(n) over U₂
(Iwama–Morizumi 2002). No superlinear bound for an explicit function in NP was known. Corollary A, if Theorem 2.2
holds, is the first, and for a function in AC⁰ ∩ (size N log N). As the idea agent says, this is the release's
most checkable claim in classical vocabulary; either it is a major corollary or Theorem 2.2 is where an error sits.

