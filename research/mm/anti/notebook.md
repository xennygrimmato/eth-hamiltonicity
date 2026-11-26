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

---

## Step 3. Corollary B: routing lower bounds for multiplication problems

### 3.0 The extra ingredient found here: Weak ETH ⇒ no ports in characteristic 0 [K]

Source [Int] = "The logarithmic exponent of integer multiplication on tapes" (family 379), pdftotext of `paper.pdf`.

**Definition (verbatim, [Int] §1).** "The assumption for the converse is variable-count Weak ETH. It says that for no
fixed 0 < δ < 1 can a deterministic algorithm decide 3-SAT on v variables in time 2^{O(v^{1−δ})} times a polynomial
in the input length [41, 52]. For example, a running time of 2^{O(v/log v)} is compatible with this hypothesis."
[Int] also says it "is equivalent to the Stearns–Hunt hypothesis for CNF satisfiability [41, Theorem 2.4].
Subexponential algorithms for 3-SAT [16, 46] refute the original Exponential Time Hypothesis [33] and are
compatible with this weaker assumption."

*Status in-world.* Family 378 ("The Exponential Time Hypothesis is False") counts k-CNF solutions in
(n+m)^{O_k(1)}·2^{n/(log n)^{1/2+o(1)}} [K, CONTENTS.md]. That refutes ETH but is compatible with variable-count
Weak ETH. **Weak ETH fails exactly if some deterministic algorithm decides 3-SAT in 2^{O(v^{1−δ})}·poly(L) for a
fixed δ > 0** — e.g. 2^{v^{0.999}}. Saving only a polylog or 2^{√log}-type factor in the exponent (2^{v/(log v)^c})
does not refute it.

**Theorem 7.1 of [Int] (verbatim).** "(Expansion and 3-SAT). If characteristic zero admits ports, then for some δ > 0
a deterministic algorithm decides 3-SAT on v variables in 2^{O(v^{1−δ})} bit operations times a polynomial in the
input length. In particular, under variable-count Weak ETH, characteristic zero does not admit ports."

**Lemma 8.2 of [Int] (verbatim, the parts used).** "(Short edges and distant terminals). Assume Weak ETH. Let a
multigraph have P₀ vertices, maximum degree D, and edge widths at most Db. For all sufficiently large P₀ there is a
placement in some X ∈ 𝒳 and a point o ∈ X with the following properties. Write P for the least power of two at
least P₀. All constants below depend only on D.
  S ≤ C_D·b·P/√(log P),  (8.2)
  E_{a∈A, t∈B} (d(x_a, x_t) − 1)² ≤ C_D·P/(N log P),  (8.3)
[...] Here A, B are any two lists of N vertices distinct within each list, the draws from the two lists are
independent and uniform [...]. These bounds are uniform over the lists". Here S is the supply price (8.1):
"S = Σ_{e=uv} q_e d(x_u, x_v)" with q_e the width of edge e.

**Price bound of [Int] §7.1 (verbatim).** "Place each vertex u at x_u in a member of 𝒳. Applying the vertex tables
as local maps to the product of the edge wires gives the contraction. Tables at coincident sites can be applied
jointly. It follows by monotonicity and additivity of the price that any product of equality wires obtained in this
way costs at most Σ_{e=uv} q_e d(x_u, x_v)." And: "a q-bit wire between two sites at distance d costs qd." 𝒳 is "the
class of complete CAT(0) spaces carrying compatible spectral prices for rational tensors"; networks are "rational
tensor networks" (tables with rational entries).

Remark [R]. The proof of Lemma 8.2 uses Weak ETH only through Theorem 7.1 ("Under Weak ETH (Theorem 7.1), the
logarithmic obstruction [49, Theorem 4.2] [...] applies to 𝒳 (a class of Hadamard spaces without ports)"). So
everything below holds under the weaker hypothesis "characteristic 0 has no ports"; Weak ETH is the printed route to
it.

### 3.1 Pinning lemma (our argument) [R]

**Lemma P.** Let Net be a trivalent network (over Q, or over any field) whose exterior bits are partitioned into
X (inputs, |X| = r), Y (outputs, |Y| = r) and Z (control). Suppose that for each π in a family Π of bijections X → Y
there is z_π ∈ {0,1}^Z such that Net(x, y, z_π) = ∏_{i∈X} [y_{π(i)} = x_i] for all x, y. Attach to each control
position z an arity-1 vertex with table e_{z_π(z)}. Then for each π ∈ Π the resulting network Net_π
(a) has the same graph and the same exterior positions X ∪ Y for every π — only the leaf tables depend on π;
(b) is trivalent and has size(Net_π) = size(Net) (|Z| new vertices, |Z| fewer exterior bits);
(c) represents exactly the product of the r wires (x_i, y_{π(i)}).
*Proof.* Contracting e_b against a position is evaluation at b. ∎

This is how an **input-dependent** routing enters: π is encoded in input bits (the control Z), the topology is
fixed, and only tables vary — exactly the hypothesis form of [MM] Lemma 4.1 ("for every permutation in the support of
a distribution, some choice of vertex tables realizes the r independent wires") and the way [MM] itself applies it
("pin each list's tags to a uniform permutation"). A fixed π (|Π| = 1) gives nothing — correctly, since then the map
is free wiring. Output positions that must be 0 on the family (high bits of integer outputs, ∞-flags) are pinned the
same way with e₀; unneeded outputs are closed with ≡1 leaves (Σ_y [y = f] = 1).

### 3.2 Theorem S (shifts: polynomial and integer multiplication) — printed statements only [R]

**Routing lemma for cyclic families (our argument from [Int] Lemma 8.2 + §7.1).** Assume variable-count Weak ETH.
There are c > 0 and r₀ such that for r ≥ r₀: if a trivalent rational network with exterior bits X = {x_0..x_{r−1}},
Y = {y_0..y_{r−1}}, Z, has the property of Lemma P for Π = {all r cyclic shifts i ↦ i + s mod r}, then
size(Net) ≥ c·r·√(log r).

*Proof.* Take Net_s from Lemma P. Give each exterior bit its own equality leaf (arity 2; one wire, one exterior
position); call the leaves a_i (on x_i) and t_j (on y_j). This at most doubles the size and keeps degree ≤ 3, all
widths 1, and the graph is the same for all s. Let P₀ = number of vertices, P its power-of-two ceiling; P₀ ≥ 2r.
Suppose P₀ ≤ ε r √(log r). Apply [Int] Lemma 8.2 to this graph (D = 3, b = 1) with lists A = (a_i), B = (t_j),
N = r. By (8.3), E_{A×B}(d − 1)² ≤ C·P/(r log P) ≤ 2Cε√(log r)/log P ≤ 2Cε/√(log r) → 0, so E_{A×B} d ≥ 1/2 for
large r. For each s, Net_s represents ⊗_i wire(a_i, t_{i+s}), so by the §7.1 price bound and "a 1-bit wire costs its
distance", Σ_i d(x_{a_i}, x_{t_{i+s}}) ≤ S. Averaging over s: (i, i+s) with i, s uniform is uniform on A × B, so
r·E_{A×B} d ≤ S. With (8.2): r/2 ≤ C·P/√(log P) ≤ 2Cε r √(log r)/√(log P) ≤ 2Cε r (as P ≥ r). For ε < 1/(4C) this is
false. Hence P₀ > ε r √(log r), and size(Net) ≥ P₀/2 − O(1) ≥ c r √(log r). ∎

Why this uses only printed statements: Lemma 8.2 already controls *all pairs* (product law on A × B), and the cyclic
family makes the demand law equal to that product law (q = r). For matrices this fails; see 3.3.

**Theorem S1 (polynomial multiplication over F₂, conditional form).** Assume variable-count Weak ETH. Every
B₂-circuit computing the product of two polynomials of degree < n over F₂ (inputs a, b ∈ F₂ⁿ, outputs the 2n − 1
coefficients) has at least c·n√(log n) gates, for an absolute c > 0 and all large n.

*Proof.* Let C have s gates. Add n − 1 XOR gates computing d_j = c_j ⊕ c_{j+n} (j ≤ n−2), d_{n−1} = c_{n−1}, i.e.
a·b mod (xⁿ − 1). Lemma E(a) (over Q) gives a network for [d = a·b mod (xⁿ−1)] with X = a, Y = d, Z = b, volume
≤ 16(s + n) + 4·2n + 4n. For b = x^t (one-hot e_t), c = a·x^t has c_{i+t} = a_i and other c_j = 0; the window
[t, t+n−1] contains exactly one of j, j+n for each j ≤ n−2, and contains n−1; so d_{(i+t) mod n} = a_i: the cyclic
shift by t. The routing lemma with r = n gives 16(s+n) + 12n ≥ c'n√(log n). ∎

**Theorem S2 (integer multiplication).** Same hypothesis and conclusion for B₂-circuits multiplying two n-bit
integers (full 2n-bit product). *Proof.* Identical with b = 2^t: a·2^t has no carries, bits c_{i+t} = a_i, so the
same XOR fold gives the cyclic rotation. ∎

**Theorem S3 (cyclic shift with binary shift amount).** Same hypothesis: every B₂-circuit computing
(a, t) ↦ rot_t(a), a ∈ {0,1}ⁿ, t ∈ {0..n−1} in binary (n a power of 2), has ≥ c·n√(log n) gates. *Proof.* Pin the
⌈log₂ n⌉ bits of t (Z = t). ∎ So the one-hot versus binary encoding of the shift is immaterial for the lower bound;
it also is for upper bounds up to O(n) (one-hot decoder of log n bits: O(n) gates; one-hot to binary encoder: O(n)).

**Theorem S-dichotomy (unconditional, given the release).** For a fixed absolute c > 0, at least one holds:
(i) 3-SAT on v variables is decidable deterministically in 2^{O(v^{1−δ})}·poly(L) bit operations for some fixed
    δ > 0 (variable-count Weak ETH fails); indeed characteristic 0 admits ports, which implies (i) by [Int] Thm 7.1;
(ii) for all large n, every B₂-circuit for F₂[x]-multiplication of length n, for n-bit integer multiplication, and
    for cyclic shifting (one-hot or binary amount) has ≥ c·n√(log n) gates.
*Proof.* Contrapositive of S1–S3 via [Int] Thm 7.1 and the remark in 3.0. ∎

**Exact list of printed statements used by S1–S3 and the dichotomy.** [Int] Theorem 7.1; [Int] Lemma 8.2 ((8.2),
(8.3)); [Int] §7.1 price bound and wire price. Nothing from [MM]. Our own: Lemma E, Lemma P, the XOR fold, the
averaging-over-shifts computation.

**Tightness.** [FT] Theorem 7.1 (verbatim): "For every α > 1/2, a division-free circuit over K computes the 2n − 1
coefficients of the product of two length-n polynomials in O_α(n(1 + log n)^α) binary additions, subtractions and
multiplications. The count includes multiplication by prescribed scalars and the implied constant is uniform over all
fields K." Lean-formalised ("Lean proves an O_ε(n(1+log n)^{1/2+ε}) upper bound using integer-coefficient circuits
that specialize to every field", 379.md). Over K = F₂ every gate is XOR or AND, so **B₂-size(F₂[x]-mult) ≤
C_α n(log n)^α**. Hence under Weak ETH:
  c·n·(log n)^{1/2} ≤ B₂-size(F₂[x]-multiplication, length n) ≤ C_α·n·(log n)^α for every α > 1/2 —
the logarithmic exponent of Boolean polynomial multiplication over F₂ is exactly 1/2 [R].
Corollary [R, unconditional from FT Thm 7.1]: cyclic shift by a binary amount has B₂-circuits of size
O_α(n(log n)^α) (decode t, multiply by x^t, fold), beating the textbook barrel shifter's n log n; with S3 its log
exponent is exactly 1/2 under Weak ETH.
Integer multiplication: the release gives a multitape TM in n(log n)^{1/2+o(1)} (Lean); converting to circuits costs
a log factor (oblivious simulation, [L] Pippenger–Fischer 1979), so the circuit upper bound I can state is
O(n log n) [L: Harvey–van der Hoeven, Ann. Math. 2021; that their method yields Boolean circuits of that size is
from memory, check]. Gap: n√log n ≤ size ≤ n log n (or n(log n)^{1/2+o(1)} if the tape algorithm is made a circuit
without loss — not claimed by the release).

### 3.3 Theorem M (matrix products) — uses Lemma 4.1's entropy step [R]

The reduction (Lemma E + Lemma P). Let C be a B₂-circuit with s gates computing MM_n over R. Lemma E(a): a network
for [C = A·B] of volume ≤ 16s + 4·2n² + 4n² = 16s + 12n². Control Z = bits of A; inputs X = bits of B; outputs
Y = bits of C. For π ∈ S_n let A = P_π with (P_π)_{a,i} = [a = π(i)]. Then (P_π B)_{a,j} = B_{π^{-1}(a), j} over F₂
(one nonzero term), over the Boolean semiring (one true disjunct), over (min,+) with P_π having 0 on the support and
+∞ elsewhere (encoding ∞ by a flag bit), and over Z with 0/1 encodings (pin the higher output bits to 0). So the
pinned network realizes r = n²·b wires (b = payload bits per entry) from bit (i, j, ·) to (π(i), j, ·). With π
uniform on S_n, each input's destination is uniform on the q = n positions of its column: **q = n while r = n²**.

**Why Lemma 8.2 of [Int] is not enough here.** The demand law µ (uniform input, destination uniform in its column)
has density r/q = n relative to the product law on A × B, so (8.3) only gives
E_µ(d − 1)² ≤ n·C P/(n² log P) = C P/(n log P), which is not small when P ≈ n²√log n. One needs a placement adapted
to µ itself. That is exactly what [MM] Lemma 4.1's proof does with the graph-entropy bound and minimax:
"The graph entropy bound [43, Corollary 5.2] [...] gives H_ν(Y|X) ≤ C(1 + β_ν) [...] Every pair has ν-mass at most
2/(rq), so H_ν(Y|X) ≥ log₂(q/2). It follows that β_ν ≥ c log q [...] Bilinear minimax [...] gives a single D = d²
∈ K for which E_ν D ≥ c log q for every such law."

**Theorem M1 (conditional form, route 1: as printed).** Assume [MM] Lemma 4.1 and that some prime p has no ports
(take k = F_p). Then there is c > 0 such that for all n ≥ 2 every B₂-circuit computing the n×n product over F₂, or
over the Boolean semiring, has at least c·n²√(log n) − n² gates. More generally:
 (a) every trivalent F_p-network representing [C = AB] has size ≥ c n²√(log n); in particular unambiguous and
     (p = 2) parity-nondeterministic circuits;
 (b) (min,+) with entries in {0..2^b − 1} ∪ {∞}: ≥ c n² b √(log n) − O(n² b) gates — superlinear in the input size
     n²(b+1) by √log n for every b ≥ 1;
 (c) integer matrices with b-bit entries and full outputs: ≥ c n² b √(log n) − O(n²(b + log n)); this exceeds the
     I/O size n²(2b + log n) only when b ≫ √(log n) (trivial for 0/1 integer matrices);
 (d) rectangular n×n by n×m: ≥ c·nm√(log n) − O(n² + nm); J independent products: ≥ c·J n²√(log n) − O(Jn²);
 (e) via fixed embeddings (pins and ≡1 closures, [R] one line each): inverse of 3n×3n unitriangular matrices over
     F₂ (the (1,3) block of [[I,A,0],[0,I,B],[0,0,I]]⁻¹ is AB), transitive closure of 3n-vertex digraphs (three-layer
     graph), and squaring of 3n×3n matrices over F₂ (the (1,3) block of [[0,A,0],[0,0,B],[0,0,0]]² is AB). In each
     case the fixed zero/identity entries are pinned by e₀/e₁ leaves and the unneeded outputs closed by ≡1 leaves,
     which keeps Lemma P applicable; the bound is Ω(n²√log n) in terms of the n of the embedded product.
*Proof.* Size(Net_π) = size(Net) ≤ 16s + 12n² by Lemma P(b); Lemma 4.1 with r = n² (resp. n²b, nm, Jn²), q = n.
For (b),(c) the extra output bits are pinned by e₀ (Lemma P remark). ∎

**Theorem M2 (conditional form, route 2: Weak ETH).** Assume variable-count Weak ETH and that [MM] Lemma 4.1 holds
for a field of characteristic 0 (reading (H1₀) below). Then the conclusions of M1 hold (with networks over Q in (a)).

**Theorem M-dichotomy.** Under (H1₀): either 3-SAT has a deterministic 2^{O(v^{1−δ})}·poly(L) algorithm for some
δ > 0, or every B₂-circuit multiplying n×n matrices over F₂ (or Boolean, or (min,+)) has Ω(n²√(log n)) gates.
In words: **flat n² bit operations for matrix multiplication is impossible unless 3-SAT is solvable in time
2^{v^{1−δ}}.**

**(H1₀), stated exactly.** [MM] Lemma 4.1 reads "Let the field have no ports", without "finite"; it sits in §4 of
a paper that fixed "a finite field k" in §2. Its proof uses: closure of the class of Hadamard spectral spaces under
isometry, rescaling, closed convex subspaces, pointed ultralimits ([MM] §3, stated for "a field"); "[43, Theorem 6.1]
gives a subclass with the same properties and no ports, closed also under finite ℓ₂ products"; "[43, Corollary
5.2]". [43] states these for every characteristic: "If χ has no ports, Theorem 6.1 gives a subclass of X_χ that still
has no ports and is closed under finite ℓ₂ products, positive rescaling, closed convex subspaces and pointed
ultralimits" (§2.3); Cor. 5.2 is for "a class of Hadamard spaces without ports" with no field condition; [43] works
explicitly in characteristic 0 ("For characteristic zero, specialization to a suitable prime..."), and [Int] runs the
same machinery over Q. I checked that no step of the printed proof uses finiteness of the field. So (H1₀) is a
reading of a printed proof, not a new claim; I rate the risk low but it *is* a reading, which is why M2 is listed
separately from M1 and from the printed-only Theorem S.

**What M needs beyond the papers' proved statements.** M1: nothing beyond [MM] Lemma 4.1 as printed, plus the open
hypothesis "some prime has no ports". M2/dichotomy: [Int] Thm 7.1 (printed) plus (H1₀). Our own: Lemma E, Lemma P,
the semiring check of P_π B.

### 3.4 The crux: input-dependent routing — checked

- The permutation must be *data*: it is the matrix A (n² bits, of which only the n log₂ n bits of π vary on the
  family). A fixed π is wiring and costs 0; Lemma 4.1 with q = 1 gives nothing — consistent.
- Lemma 4.1 allows tables to depend on π and needs a single topology: Lemma P gives exactly that.
- Correlation: the n² destinations are all functions of one π (strongly correlated). Lemma 4.1 uses only the
  marginal law of each destination ("µ be the joint law of a uniform input and its random destination"; "every pair
  has ν-mass at most 2/(rq)"). Uniform marginal on q = n outputs holds. ✓
- Exactness: P_π B is exactly a product of wires; for any non-permutation A it is not, so we never use other A.
- The bound is really a bound for the sub-problem (P, B) ↦ PB ("move n records of n bits by a permutation given as
  data").

### 3.5 Sanity check: the sub-problem is easy, so the method caps at n² log n [R + L]

- P_π B in O(n² log n) gates: encode each column of P (one-hot → ⌈log₂ n⌉-bit index π(i), O(n) gates per column by a
  tree, O(n²) total); sort the records (π(i), B_i) by key with an AKS network ([L] O(n log n) comparators), each
  comparator O(log n) for the key and O(n) for the conditional swap of the payload: O(n² log n). Output row a = B_{π⁻¹(a)}.
  (Batcher instead of AKS: O(n² log² n).)
- Matrix–vector product over F₂: Θ(n²) (input size n²; n² AND + XOR). Nothing to prove.
- Hence **c n²√(log n) ≤ size(P_π·B) ≤ C n² log n**: the matrix theorem is tight for the routing sub-problem up to
  √(log n) at most. Under the network coding conjecture the sub-problem would need n² log n [C, by the
  Afshani–Freksen–Kamma–Larsen argument], so the remaining √log is the gap between Lemma 4.1 and NCC.
- For shifts the bound is tight up to (log n)^ε (3.2).

### 3.6 The ports case: not covered, and what is missing [R + C]

If **all** characteristics have ports, Weak ETH fails (by [Int] Thm 7.1, char 0 having ports gives the 3-SAT
algorithm). So the only world in which our matrix bound has no proof from the release is a world with a
2^{v^{1−δ}} 3-SAT algorithm. Still, can the unconditional Theorem 2.2 (both cases) give a matrix bound directly?
- One would need a reduction from D_w^{⊗t} or Tag(h,h)^{⊗t} to MM_n with n² = O(t·n_w) and overhead o(t n_w w^σ).
  I found none, and the obvious routes fail for a reason that looks structural:
  1. A one-hot permutation matrix has N² bits for N log N bits of tags; to keep the overhead linear in the payload
     the records must be ≈ N bits wide. So MM naturally implements Tag(h, W) with W ≈ 2^h: **one** permutation, wide
     records.
  2. The ports-case proof consumes Tag(h,h) tests with **independent** permutations per h-bit payload. Forcing all
     n/h chunks of a row to share one permutation is a *restriction* of Tag(h,h)^{⊗n/h}; a restriction of a hard
     tensor can be easy — wrong direction.
  3. Getting m independent permutations from products costs a factor m: C = Σ_l A_l B_l with B_l supported on column
     block l realises m independent row permutations of n×(n/m) blocks, but needs an n × mn by mn × n product, i.e.
     m square products. Reaching h-bit payloads (m = n/h) multiplies the cost by n/h.
- Missing statement (would suffice): "in a characteristic with ports, vol(Tag(h, W)) ≥ c·2^h·W·h^γ for some γ > 0
  and all W ≥ 2^h" (wide single-permutation routing), or a version of the descent [42, Prop. 14.1] with wide Tag
  gates. [C]: the paper itself shows (Thm 16.1(2)) that wide Tag(h,w), w ≥ h^a, would become O(n w h^ζ) if ω < 9/4,
  i.e. it treats wide routing as the kind of thing compression can make cheap; I would not bet that wide routing is
  hard in port characteristics.
- γ: our exponent is γ = 1/2, from Lemma 4.1 / Lemma 8.2. It is **not** Theorem 2.2's σ. Do not write (log n)^σ for
  matrices.

---

## Step 2′ (addendum). Corollary A rests on a Lean-formalised statement [K, Lean source read, not built]

The clone contains Lean source under `lean/OAI/` (not only Comparator statements). Found by the "note" executor and
re-read by me:

`lean/OAI/LinearAlgebra/MatrixExponent/BatchDescent/Hard.lean`
```
theorem hard (F : Type) [Field F] [Finite F] : Tagged.Hard F :=
  Processor.hard_of_descent (descent fun bad => compilation_of_encoded (encoded bad))

theorem manyList_full (F : Type) [Field F] [Finite F] :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
      1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) → Realizes F w t m →
      (t : ℝ) * listBits w * (w : ℝ) ^ η < m
```
with (`Network.lean`, `ListBounds.lean`) `listBits w = 2*w*2^w`; `Net F a b k v` = networks built from tables of
total bit-arity ≤ 3 (`h : wd a + wd b ≤ 3`) by juxtaposition, contraction over shared bits, trace (internal
cycles) and rewiring, v = number of vertices; `Realizes F w t m` = ∃ v, a `Net` for `distinctPower F w t` (product
over t lists of [list is Nodup]) with m = v + t·listBits w (vertices + exterior bits = the paper's *size*).
Also `Tagged/Hard.lean`: "Power-of-logarithm lower bound for verifying one permutation":
`Hard F := ∃ σ > 0, ∀ᶠ w, ∀ m, Net F (inputs w (word w)) .unit (tag F w (word w)) m → 2^w * w * w^σ ≤ m`
(a single Tag(w,w) test). `grep sorry` over `lean/OAI/LinearAlgebra/MatrixExponent` returns nothing; we did not
build the project and did not audit axioms.

Consequences.
- **Corollary A holds for every finite field with no ports / no Weak ETH hypothesis, resting on a Lean theorem**
  (as read). With size m instead of volume, Lemma E gives m ≤ (4s + N + 1) + N, so every B₂-circuit for LD_N
  (N = 2w·2^w) has s > N(w^η − 2)/4 − 1. Direct sum now for all t ≤ 2^{w^{1+η}}.
- The Lean top level has no ports split (route "descent + resists", `Processor.hard_of_descent`); [MM] Lemma 4.1
  does not appear in it. So the matrix theorems of Step 3 still need Lemma 4.1 (paper-only) or [Int] (paper-only).

## Step 3.7. Can distinctness (or Tag) be reduced to matrix multiplication? (lead's second route) [R + C]

Goal: from a B₂-circuit of size S(n) for MM_n, build a network for D_w^{⊗t} (or Tagged.Hard's Tag(w,w)) on
≈ n² input bits with overhead o(n²·w^η). Since η is an unknown small constant, the MM inputs used must total
n²·(log n)^{o(1)} bits and the glue must cost n²·(log n)^{o(1)} gates.

**Obstruction 1: information density of a permutation matrix (kills one-hot routing) [R].** The only data-dependent
routing a single product does is P·B (or B·Q) with P a 0/1 matrix built from the data. An n×n permutation matrix
has n² bits but carries log₂ n! ≈ n log n bits. To route records of width W by P one needs n² control bits and
moves nW payload bits. Within budget this forces W ≈ n: wide records. The hard instances that are formalised or
proved unconditionally have narrow records: Tag(h,h) (`Tagged.Hard`: 2^w records of w bits) and D_w (2^w words of
2w bits). Embedding Tag(h,h) as P_π (N×N) times B (N×h) costs ≥ N² gates just to produce P_π from the tags (each
of the N² entries is a distinct function of the tags), against a target lower bound N h^{1+σ} ≪ N². The loss is a
factor ≈ N/(h^{1+σ}) — everything.

**Obstruction 2: products by permutation matrices generate a tiny group (kills radix-pass pipelines) [R].**
Put the n² bits on an n×n grid. B ↦ P_σ B Q_τ acts as (i, j) ↦ (σ(i), τ(j)); transposition swaps coordinates.
These maps form the group S_n ≀ S₂ of order 2(n!)², and compositions stay in it. A pipeline of k matrix products,
each with one factor a data-dependent permutation matrix, interleaved with *fixed* wirings, realises at most
(2(n!)²)^k · (number of fixed pipelines = 1) distinct bit-routings, i.e. ≤ 2^{2kn log₂ n + k}. Routing Tag(h,h)^{⊗t}
with tNh = Θ(n²) payload bits requires (N!)^t = 2^{(1−o(1))·tNh} = 2^{Θ(n²)} distinct routings (one per tag
pattern, all distinct as tensors). Hence k = Ω(n/log n) products, total cost ≥ (n/log n)·n² — no lower bound for
MM_n can come out. A radix pass ("one-hot matrix of a digit × record matrix") is such a step, so **radix sorting by
matrix products is ruled out unless the glue circuitry between passes does most of the routing itself**. Glue of
size O(n²) does have enough entropy (2^{O(n²)} settings) to escape this count, so the count is not a proof that no
mixed reduction exists; but the glue would then be a linear-size circuit doing near-arbitrary routing of h-bit
records with the help of a few row-uniform permutations, which nothing suggests is possible [C].

**Obstruction 3: counting-type reductions.** Rank counting (rank_i = #{j: x_j < x_i}) or collision counting via
one-hot bucket matrices needs M×M matrices for M = 2^w records, i.e. M² ≫ N = 2wM entries. With n² ≈ N one has
n ≪ M buckets, too few to separate the records. [R for these specific schemes.]

**Verdict.** No reduction from list distinctness or narrow tagged permutations to square matrix multiplication with
near-linear overhead is available; the natural ones lose a factor n/polylog(n). The matrix bound stays on the
wide-routing route (Lemma 4.1 or [Int]), and the **Weak-ETH dichotomy remains the main statement**. What would be
needed is an unconditional lower bound for *wide* single-permutation routing, e.g. `Tagged.Hard` with payload
`word W`, W ≥ 2^w — the Lean `Hard` explicitly says "Only square payloads at powers of two are required".

---

## Step 4. Comparison with what was known [L]

| Result | Model | Bound | Conditional? |
|---|---|---|---|
| Raz, STOC 2002 / SICOMP 32(5) 2003, "On the complexity of matrix product" | arithmetic circuits over ℝ/ℂ with coefficients of absolute value ≤ 1 | Ω(n² log n) | no, but restricted model |
| Raz–Shpilka, SICOMP 2003 | bounded-depth circuits with arbitrary gates (any function per gate) | n²·λ_d(n), λ_d slowly growing | no; bounded depth |
| Shpilka, FOCS 2001 / SICOMP 2003, "Lower bounds for matrix product" | bilinear/quadratic circuits over F₂ (resp. F_p) | 3n² − o(n²) (resp. (2.5 + 1.5/(p³−1))n²) | no; algebraic |
| Bläser, FOCS 1999 | bilinear rank, any field | 5/2·n² − 3n | no; algebraic |
| Pratt 1975; Paterson 1975; Mehlhorn–Galil 1976 | monotone circuits, Boolean product | n³ ANDs | no; monotone |
| Pippenger–Valiant 1976 (shifting graphs) | routing by vertex-disjoint paths (no coding) | Ω(n log n) for all cyclic shifts | no; no coding |
| Afshani–Freksen–Kamma–Larsen, ICALP 2019 | Boolean circuits, bounded fan-in **and fan-out** | Ω(n log n) for integer multiplication | yes: network coding conjecture |
| Farhadi–Hajiaghayi–Larsen–Shi, STOC 2019 | external-memory sorting (and sorting circuits) | Ω(n log n)-type | yes: network coding conjecture |
| Asharov–Lin–Shi, SODA 2021 | Boolean circuits | sorting k-bit keys in o(n log n) for small k | upper bound; shows NCC-type bounds need long keys |
| [MM] (release) | formal arithmetic circuits | ⌈n^{9/4}/2⌉ nonscalar gates | given release |
| [Int] (release) | multitape TMs | Ω(n√log n) for integer multiplication | Weak ETH |
| — | **general Boolean circuits, matrix multiplication** | **nothing above the trivial Θ(n²)** (I know of no superlinear bound; Shpilka's paper lists "Can matrix product be computed by a circuit of size O(n²)?" as open) | — |

Rows from memory except Raz (confirmed by search: ECCC TR02-012, SICOMP 32(5) 2003) and Shpilka (confirmed:
arXiv cs/0201001, ECCC TR01-060). Treat the rest as [L, unchecked details].

**Positioning of our statements (honest).**
- Theorem S / M are, as far as I know, the first superlinear lower bounds for multiplication problems in the
  **general Boolean circuit model** (unbounded fan-out, any basis, coding allowed) under a *complexity-theoretic*
  hypothesis (Weak ETH) rather than the network coding conjecture, which is a combinatorial conjecture about
  information flow. They are the √log analogues of AFKL (log there), with AFKL's fan-out restriction removed.
- They are conditional on (a) the release being correct — unrefereed, two days old; (b) Weak ETH (or no ports in
  some characteristic); (c) for matrices, [MM] Lemma 4.1 (paper-only) and, on the Weak-ETH route, its char-0
  reading (H1₀).
- Corollary A is conditional only on (a), and is backed by a Lean statement (as read). It is the strongest claim:
  first superlinear B₂-circuit lower bound for an explicit function (in AC⁰). Before the release the record was
  3.1n − o(n) (Li–Yang 2022).
- None of this approaches n^{2+ε}: the method gives polylog factors at most (ideas-n2 §3.3), and the matrix bound is
  really a bound on routing n rows by a data-given permutation, a sub-problem of cost ≤ n² log n.

## Step 5. Upper bounds for calibration [K + L]

Boolean-circuit size of n×n multiplication:
- Over F₂: a bilinear algorithm over F₂ of rank R at side n₀ recurses to B₂-circuits of size O(n^{log_{n₀} R}); with
  the release's exponent over every field ([MM] Thm 1.1, upper bound due to Amanov–van den Berg–Zuiddam [5]):
  **n^{9/4+o(1)}**. Before the release: n^{ω+o(1)}, ω < 2.3714 [L: Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou 2024].
  Polylog savings at the leaves (table lookup; ideas-n2 §4(a)) are invisible under the o(1).
- Boolean semiring: via integer products with O(log n)-bit entries, n^{9/4+o(1)}. Combinatorial: n³/2^{Ω(√log n)}-type.
- (min,+): no subcubic-by-a-power circuit from the release; the RAM algorithms quoted in ideas-n2 §4(d) are
  n^{3−c} for tiny c.
- Sub-problems: P_π·B ≤ O(n² log n) (3.5); matrix–vector Θ(n²).

**The gap for F₂ (and Boolean):**
  c·n²·√(log n)  ≤  B₂-size(MM_n over F₂)  ≤  n^{9/4+o(1)},
lower bound under Weak ETH + (H1₀) (or Lemma 4.1 + a prime without ports); trivially ≥ n² unconditionally.
For polynomial multiplication over F₂: c·n√(log n) ≤ size ≤ C_α n(log n)^α (α > 1/2) — closed in the log exponent.
For integer multiplication: c·n√(log n) ≤ size ≤ O(n log n).

## Step 6. Plain statements

**Tweet-length paragraph.** If OpenAI's 24 Nov network bounds hold, then "matrix multiplication in n² operations"
is impossible even for bit-level algorithms, by a √log n factor: either 3-SAT on v variables can be solved in time
2^{v^{0.999}} (a breakthrough far beyond OpenAI's own ETH refutation, which saves only a √log in the exponent), or
every Boolean circuit multiplying two n×n matrices over F₂ — or Boolean, or (min,+) matrices — needs at least
c·n²·√(log n) gates. The hard core is just moving n rows by a permutation that is part of the input. The same
dichotomy gives c·n√(log n) for multiplying polynomials over F₂ or integers, and there it is tight up to
(log n)^ε, because the release also gives n(log n)^{1/2+ε} circuits. This says nothing about n^{2.01}: the true
bit complexity of matrix multiplication is somewhere between n²√(log n) and n^{9/4}.

**Three sentences for the story agent.** OpenAI's new results imply that no bit-level algorithm can multiply
matrices with "just n²" operations — unless 3-SAT has a dramatically faster algorithm than anyone, including
OpenAI, has found (time 2^{v^{1−δ}}). The penalty is modest, a factor √(log n), and it comes from the cost of
shuffling rows into a data-dependent order, not from arithmetic. For multiplying polynomials over F₂ the same
penalty is matched by an upper bound, so there the answer is essentially exact: n·√(log n) bit operations.

---

## Summary of theorems and exactly what they use

| # | Statement | Printed statements used (verbatim in this notebook) | Extra hypothesis | Our argument |
|---|---|---|---|---|
| A | B₂-size(LD_N) > N(w^η − 2)/4 − 1 = Ω(N (log N)^η), direct sum for t ≤ 2^{w^{1+η}}; also unambiguous/parity circuits | Lean `manyList_full` (= [MM] Thm 2.2, wider t) | none (every finite field) | Lemma E |
| S1–S3 | F₂[x]-mult, integer mult, cyclic shift (binary or one-hot amount): ≥ c n√log n gates | [Int] Thm 7.1, Lemma 8.2, §7.1 price bound | variable-count Weak ETH | Lemma E, Lemma P, XOR fold, shift averaging |
| S-dich. | Weak ETH fails (2^{O(v^{1−δ})} 3-SAT) **or** S1–S3 | same | none | contrapositive |
| M1 | MM over F₂ / Boolean / (min,+) / b-bit integers / rectangular / batched (+ inverse, closure, squaring): ≥ c n²√log n − O(n²) | [MM] Lemma 4.1 | some prime has no ports | Lemma E, Lemma P, P_π B |
| M2 | same | [MM] Lemma 4.1 read for char 0 (H1₀); [Int] Thm 7.1 | Weak ETH | same |
| M-dich. | Weak ETH fails **or** M | same | (H1₀) | contrapositive |
| neg. | No near-linear reduction distinctness/Tag(h,h) → MM by permutation-matrix products | — | — | density + S_n≀S₂ counting (§3.7) |

Not proved: any bound in the ports case from Theorem 2.2 directly (missing: wide-record Tag lower bound); any
n^{2+ε}; exponent above 1/2 on the log.
