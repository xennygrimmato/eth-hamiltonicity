# n² matrix multiplication after "ω = 9/4": what is still open, targets, and consequences for our notes

26 Nov 2026. Idea agent (Fable). Informal research notes; nothing here is claimed.
Working assumption, by the user's decision: OpenAI's family 379 (24 Nov 2026) is correct. We did not verify it.
§8 says what changes if it is not.

Tags: **[P]** read in OpenAI's text (paper.txt / intro.tex / lean/docs/379.md in the scratchpad clone);
**[K]** known literature; **[S]** seen only as a search result or abstract, not read in full;
**[D]** derived here, unreviewed; **[C]** opinion or conjecture.

## 0. Verdict in ten lines

1. Algebraic n^{2+o(1)} is dead over every field [P]. Formal arithmetic circuits (+, −, ×, ÷) need ≥ n^{9/4}/2 nonscalar
   gates; rank and border rank of ⟨n,n,n⟩ are ≥ n^{9/4}.
2. The bound does **not** transfer to computing the product *as a function* over F₂. An F₂-arithmetic circuit that only has to
   be right on 0/1 inputs is a Boolean circuit over {XOR, AND}; Strassen's degree-2 truncation fails under x² = x [D, §3.1].
3. The proof method can give Boolean circuits only polylog factors above n², never n^{2+ε} [D, §3.3]. Conditionally ("no
   ports") it does give Ω(n²·√log n) for every Boolean circuit multiplying n×n matrices over F₂ [D, §3.2]. So the honest
   target is **n²·polylog(n) bit operations over F₂**, not n².
4. Nothing known rules out an n^{9/4−ε} bit algorithm over F₂, and nothing known suggests one. Functional algorithms do not
   tensor, so a small-size gap buys no exponent [D, §3.1].
5. The release contains an unadvertised corollary that experts can check: a superlinear Boolean circuit lower bound for an
   explicit function in P [D from P, §2].
6. Things that are n^{2+o(1)} theorems now, given the release: n×√n by √n×n products (α = 1/2 exactly); fully sparse
   products in m^{4/3+o(1)}; randomised verification. See §4(f), §4(g).
7. Flat hypothesis: the companion theorem is our FH, with equality, one spectral point per configuration, over every
   field [P, §7]. The flat floors become theorems; two-merge pieces at 1/√2 are optimal; the circle is the limit.
8. Recommendation (§9): T1, the Boolean lower bound for F₂ matrix multiplication and the "formal versus functional"
   separation package. Cool, cheap to start, and it tells the user precisely in which sense n² is and is not possible.

## 1. Experiments for the lab (each ≤ 3 hours, with a pass/fail criterion)

Read §3.1 first: **no experiment below can show an exponent.** n^{1/4} is smaller than (log₂ n)² until n ≈ 2^{44}, so
"n²·polylog" and "n^{9/4}" cannot be told apart by timing. Experiments here decide small exact questions or calibrate.

**E1. AND-count of the 2×2 product over F₂ as a function.** (lead's starter; hypothesis H11)
- Object: f: {0,1}⁸ → {0,1}⁴, (A,B) ↦ AB over F₂. Circuits: XOR and NOT free, count AND gates; an AND gate takes two affine
  forms in the 8 inputs and all earlier AND outputs. Correctness on all 256 inputs only.
- Known: bilinear rank 7 over F₂ (Strassen; Winograd/Hopcroft–Kerr lower bound) [K]; the dimension bound gives ≥ 4 [D].
- Method: SAT with native XOR (CryptoMiniSat) or exact multiplicative-complexity synthesis; 256-row truth-table encoding;
  break symmetries (GL₂(F₂)³ sandwich action, gate order).
- Calibration first (15 min): the same encoder must return 6 for three-term binary polynomial multiplication and
  3 for two-term (Morse, arXiv:2608.30238 [S]: Mul₀..Mul₄ = 0, 1, 3, 6, 9 unrestricted).
- PASS (sensational): a circuit with ≤ 6 ANDs verified on all 256 inputs. That answers the Boyar–Find question negatively
  for matrix multiplication.
- FAIL-certified: UNSAT at 6 with a DRAT proof. Then "the unrestricted multiplicative complexity of the 2×2 product over F₂
  is 7" is a small certifiable statement (check novelty against Morse and Boyar–Find before saying so).
- TIMEOUT: report the largest t proved UNSAT and the restricted classes closed (E1b).
- E1b (fallback, same budget): restrict to AND-depth 2 (gates fed by affine forms plus first-level gates). UNSAT here is
  a first step of target T3.
- **What a gap would buy asymptotically: nothing by itself** (§3.1). A functional circuit uses x² = x and commutativity,
  both false in M_m(F₂), so it cannot be applied to blocks. Value of a PASS: it kills the belief "quadratic circuits are
  optimal for quadratic maps over F₂", the only reason to expect the 9/4 bound to survive for AND-count. Value of a
  FAIL: one more data point for that belief. **Push E1 to a certificate at 2×2; try ⟨2,2,3⟩ (rank 11) only if 2×2 closes in
  under an hour; do not go further.** My prior for a gap at 2×2: 5%.

**E2. Word-RAM baselines over F₂** (lead's starter). Calibration only.
- Implement or install M4RI-style M4RM + Strassen–Winograd; count word operations (not seconds) for n = 2^{10}..2^{14}.
- Report ops/n² and ops/(n^{2.25}/(log₂ n)^{9/8}) (the leaf-lookup prediction, §4(a)).
- PASS: the counts track n^{log₂7}/polylog with the predicted leaf factor within 2×. FAIL: they do not; find the
  accounting error. Do not fit exponents.

**E3. Kronecker packing with fast integer multiplication** (lead's starter).
- Verify the cost model of §4(c) on Python/GMP integers: (i) one dot product per big multiplication, L = 2b + ⌈log₂ n⌉
  bits per slot; (ii) whole product in one multiplication of ~n³L-bit integers (bivariate packing).
- PASS: measured limb-operation counts match n³L/w for (i) and M(n³L)/w for (ii) within 2×, confirming "n² word
  operations only when w ≥ nL". FAIL: a packing found that uses asymptotically fewer than n³L/w word operations for
  w = Θ(log n). I expect PASS; a FAIL would be a real finding and should be reported at once.

**E4. Lookup tables in the free-XOR model** (lead's starter, my reading of it).
- Claim to test [C]: table lookup never lowers the AND-count. A Four-Russians table (all 2^k XOR-combinations of k rows
  of B) is free to build, but using it means computing (a, R) ↦ Σ_{l≤k} a_l·R_l, the product ⟨1,k,n⟩, of bilinear rank k·n.
  A multiplexer over the 2^k table rows costs more ANDs, not fewer. Only the dimension bound (≥ n) is proved.
- Experiment: exact unrestricted AND-count (SAT, as E1) of ⟨1,2,2⟩ (6 inputs, 2 outputs, rank 4) and ⟨1,2,3⟩ (8 inputs,
  3 outputs, rank 6).
- PASS: minima 4 and 6, so tables give nothing in this model and their word-RAM gain is pure word parallelism.
  FAIL: fewer; then the Boyar–Find question already fails for the simplest rectangular product and T3 gets a new tool.
  This is cheaper than E1 and a good first run of the encoder.

**E5. The zoo of derived exponents under the exact rectangular formula.**
- Formula [P]: for weights x ≥ y ≥ z > 0, ω(x,y,z) = x + y + max(0, (x+y)z − xy)² / (4xyz).
- Recompute: fully sparse product (Abboud–Bringmann–Fischer–Künnemann: σ with ω(σ−1, 2−σ, 1+r−σ) = σ), Yuster–Zwick
  sparse, Zwick's APSP (ω(1,μ,1) = 1+2μ), all-edge triangle, bounded-difference (min,+), k-clique, rank/determinant of
  sparse matrices.
- Already done by hand [D]: fully sparse with m_out = m_in gives σ = 4/3 exactly; Zwick gives μ = 1/2, i.e. n^{2.5}.
- PASS: a table "algorithm, exponent at ω = 9/4 and α = 1/2, exponent if ω were 2, equal or not". Each row is checked by a
  script that solves the defining equation. This is the list of places where "ω = 2 behaviour" survives.

**E6. Row routing by a permutation matrix, tiny cases.**
- Function: (P, B) ↦ PB for P an n×n permutation matrix (don't-care elsewhere), B ∈ F₂^{n×n}. Exact minimum circuit size
  over the full binary basis for n = 2, 3 (SAT).
- PASS: values recorded and compared with the Beneš count; purpose is only to make §3.2's object concrete. Low priority.

**E7. The cyclic-algebra form of M_n(F₂).**
- Check numerically for n = 2..8: M_n(F₂) ≅ F_{2^n}[x; Frob]/(xⁿ − 1), i.e. AB ↔ c_k = Σ_{i+j≡k} a_i·b_j^{2^i}, with
  F₂-linear (hence XOR-only) conversions both ways.
- PASS: conversion matrices produced and the identity verified on random inputs. This is set-up for T3, not a result.

## 2. The unadvertised corollary: a superlinear Boolean circuit lower bound (neutral statement)

**What the paper proves on the way** [P, "The matrix multiplication exponent is nine fourths", §2.1 and §4].
- A *bit tensor* of arity u is a function {0,1}^u → k, k a finite field. A *trivalent network* is a graph whose vertices
  carry bit tensors of arity ≤ 3; wires pair argument positions; unpaired positions are exterior bits. Its value at a
  setting of the exterior bits is the sum over all settings of internal wires of the product of the vertex entries.
  Size = vertices + exterior bits; volume = vertices + wires.
- D_w is the 0/1 tensor on n_w = 2w·2^w exterior bits (a list of 2^w words of 2w bits) that is 1 exactly when the words
  are pairwise distinct.
- **Theorem 2.2 [P].** For every finite field k there is σ = σ(k) > 0 with vol_k(D_w^{⊗t}) > t·n_w·w^σ for all large w and
  all 1 ≤ t ≤ 2^w. The network may share work among the t independent lists.
- The exponent: in the "no ports" case any fixed σ < 1/2 (Lemma 4.1); in the "ports" case σ < min{a/4, bδ/4, 1/4} for
  constants a, δ, b from the companion papers, not made explicit [P, §4.2–4.3].
- **Embedding of Boolean circuits [P, proof of Prop. 2.3].** "Use the zero-one table of each gate, copy bits at fan-outs
  with equality tables, and pin the output to one. For each accepted input there is exactly one consistent assignment of
  the internal wires."

**Corollary [D from P].** Let N = n_w = 2w·2^w, so w = log₂N − log₂log₂N − O(1). Every Boolean circuit computing list
distinctness on N bits has at least c·N·(log N)^σ gates, for some σ > 0 and c > 0.
- *Derivation.* A circuit with s gates of fan-in 2 has ≤ 2s gate-input wires, so all fan-outs are realised by ≤ 2s + N
  equality vertices of arity 3. Gates are arity-3 vertices. The output pin is one vertex. Volume ≤ C·s + C·N.
  Theorem 2.2 at t = 1 gives C·s + C·N > N·w^σ.
- *Basis.* Any gate set of bounded fan-in, in particular the full binary basis B₂ and the De Morgan basis U₂ (a gate of
  fan-in f is a table of arity f+1, expandable to O(2^f) trivalent vertices). Unbounded fan-out. No depth restriction.
- *Stronger models covered.* (i) Tensor networks themselves, so also nondeterministic circuits in which the number of
  accepting witnesses is 1 mod p on accepted inputs and 0 mod p on rejected ones (p = char k; any prime, since the theorem
  holds for every finite field). In particular unambiguous and parity-nondeterministic circuits. (ii) Batches: t ≤ 2^w
  independent instances cost t times as much (no amortisation), a direct-sum statement.
- *The function.* Element distinctness of 2^w words of 2w bits. It is in P, in uniform AC⁰ (an AND over pairs of an OR of
  XORs), and has circuits of size O(N log²N) by sorting networks [P, Prop. 2.3].

**Comparison with the record [K].**
- Full binary basis: 3.1n − o(n), Li–Yang (STOC 2022), for affine dispersers; before it (3 + 1/86)n,
  Find–Golovnev–Hirsch–Kulikov (FOCS 2016); 3n − o(n), Blum (1984).
- Basis U₂: 5n − o(n), Iwama–Morizumi (2002) after Lachish–Raz.
- So no superlinear bound for any explicit function in NP was known. The corollary would be the first, for a function in
  AC⁰. The earlier in-world statement of this kind is weaker in the function: "superlinear circuit lower bounds for a
  language in E^NP on infinitely many input lengths", from the ETH paper (family 378) [P, CONTENTS.md].

**Why it was considered out of reach, in two lines [K/C].**
- All explicit bounds come from gate elimination, which provably stalls at small constants c·n
  (Golovnev–Hirsch–Knop–Kulikov 2018). Natural proofs do not obviously forbid n·polylog bounds, but candidate
  pseudorandom functions of quasi-linear size (Miles–Viola; Ishai–Kushilevitz–Ostrovsky–Sahai) make any "natural"
  argument suspect even there.
- The closest earlier results are conditional on the network coding conjecture: n log n for integer multiplication
  (Afshani–Freksen–Kamma–Larsen, ICALP 2019) and for sorting (Farhadi–Hajiaghayi–Larsen–Shi, STOC 2019).

**What the proof uses instead [P, my reading].**
- *No ports (Lemma 4.1).* A metric argument. Every spectral point gives a distance on the network's vertices such that
  each internal bit-wire costs at most its length and r demanded wires cost at least the sum of their end-to-end
  distances: r·E d(demand) ≤ m·E d(edge). Because spectral points are monotone under *all* local linear maps, "coding
  at the vertices" cannot help. This is the network coding conjecture made true in the tensor model. A graph-entropy bound
  then finds a placement in which demands are √(log q) longer than edges. The property is not natural in the
  Razborov–Rudich sense in any obvious way: it applies to functions that embed routing, and the metric is supplied by
  an existence theorem for spectral points, not by a test on truth tables.
- *Ports (§4.3).* Diagonalisation. A lower bound vol((U_ℓ*)^{⊗j}) > j·ℓ^{1+δ} for a universal signed counting tensor
  (companion [43, Thm 12.1]) plus a "descent" that would turn cheap distinctness tests into a compression of U_ℓ*.
  Diagonal arguments are not natural.
- *Which case holds is not decided* [P]. "Has ports" depends only on the characteristic (companion, Def. 11.1 and the
  remark after it). The companion proves "a largest flat dimension ⇒ ports", and then that there is no largest flat, so
  the implication no longer decides it. Note that Hilbert space and trees both satisfy the Poincaré inequality for
  expanders, so "no ports" needs exotic CAT(0) spectral spaces. [C]: the ports case is the likelier one.

**Status in the Lean [P, lean/docs/379.md].** The catalogue lists `square_exponent`, the dual exponent and the rectangular
formula as formalised. It does not list the Boolean corollary, and it lists the per-n bound ⌈n^{9/4}/2⌉ as unformalised.
Whether Theorem 2.2 is inside the dependency cone of `square_exponent` we have not checked.

**Why this is the most checkable point of the release.** It is a statement in classical Boolean circuit complexity, in
its own vocabulary, with a three-line derivation from two displayed statements of the paper. A circuit-complexity expert
can assess it without tensor geometry. Stated neutrally: either this is the release's largest unadvertised corollary,
or Theorem 2.2 is where an error would sit.

**Other lower bounds the same release claims or implies [P, CONTENTS.md and docs/379.md].**
- Linear circuits for the DFT of order N: Ω(N√log N) binary linear gates with *unbounded* coefficients, and an upper
  bound N(log N)^{1/2+ε}; both in Lean. Context [K]: Morgenstern (1973) proved N log N only for bounded coefficients;
  Valiant (1977) introduced rigidity to attack unbounded coefficients in logarithmic depth; no superlinear bound for
  general linear circuits was known. The upper bound contradicts the folklore belief that N log N is optimal.
- Batched DFTs: no amortisation, even with different groups; also for Zariski limits with low-rank plus sparse errors (a
  rigidity-flavoured statement).
- Formal polynomial multiplication: Ω(J·n·√log n) for J independent products (paper only, not formalised), upper bound
  n(log n)^{1/2+ε} (Lean).
- Integer multiplication on multitape Turing machines: n(log n)^{1/2+o(1)} upper bound (Lean); the matching lower bound
  only under Weak ETH. [D]: in the no-ports case Lemma 4.1 applied to shifts (multiply by 2^s, s uniform; r = n bits,
  q = n destinations) would give an unconditional Ω(n√log n) *circuit* bound for integer multiplication. Not claimed by
  the paper; same derivation as §3.2.
- VF ⊊ VBP ⊊ VP ⊊ VNP over every field (Lean); Hamiltonian cycle and (char ≠ 2) permanent superpolynomial (Lean),
  exp(c(log N)²/(log log N)²) (paper only).
- Elsewhere in the repository: depth-3 OR–AND–OR circuits 2^{ω(√n)} for a language in P (family 112).

## 3. What the 9/4 bound means for computing the product over F₂

### 3.1 Formal versus functional: why nothing transfers, and why small gaps do not amplify [D]

**Set-up.** MM_n: F₂^{n²} × F₂^{n²} → F₂^{n²}. Three models, from weakest to strongest.
- (B) bilinear circuits: ANDs of (linear form in A) × (linear form in B). AND-count = rank over F₂.
- (Q) quadratic circuits: ANDs of two affine forms in all inputs. AND-count ≥ rank/2.
- (U) unrestricted XOR–AND circuits: an AND may take earlier AND outputs. Counting all gates this is general Boolean
  circuit size up to a constant; counting only ANDs it is *multiplicative complexity* c_∧.

**Fact 1.** In (B) and (Q), functional = formal. A bilinear polynomial is multilinear, and multilinear polynomials over F₂
are determined by their values on {0,1}^N. So OpenAI's bound applies: ≥ n^{9/4} ANDs in (B), ≥ n^{9/4}/2 in (Q) [P + D].

**Fact 2.** In (U) the bound says nothing.
- Strassen's reduction to quadratic circuits takes the homogeneous degree-2 part gate by gate. That needs a grading.
  The ring of Boolean functions F₂[x]/(x_i² − x_i) is only filtered: x·xy = xy, and (a+b)·ab = 0, so a product of high-degree
  functions can have low degree and can contribute to the quadratic part of an output.
- Example: x²y computes the function xy and has zero bilinear part.
- OpenAI's Lemma 2.4 uses dual numbers u² = v² = 0 at a point where the circuit is regular, for formal identities over
  an infinite field. A functional circuit over F₂ does not specialise to a formal identity over any infinite field.
- The convention is stated in the theorem itself: "requires formal polynomial identities even over finite fields" [P].

**Fact 3. Functional algorithms do not tensor.**
- A (U)-circuit for MM_m is an identity in the Boolean ring only. Entries of a block matrix lie in M_{n/m}(F₂), which is
  not commutative and has x² ≠ x. So the circuit cannot be applied recursively to blocks.
- Hence: no "functional rank is submultiplicative", no tensor-power trick, no asymptotic exponent from a finite identity.
  A gap at size 2 or 3 gives a constant-factor saving at that base size and nothing more.
- Precedent [K]: Winograd's 1968 inner-product trick uses commutativity, saves a factor 2 in multiplications, and does
  not recurse for the same reason.
- The same fact blocks the *lower* bound: OpenAI's Lemma 2.5 and Theorem 2.1 feed on tensor powers of one bilinear
  identity. A functional algorithm provides none.

**Fact 4. What is known about (U) versus (Q) [K, S].**
- Mirwald–Schnorr (TCS 1992): for one quadratic form and for pairs of quadratic forms over F₂, quadratic circuits are
  optimal. One form: c_∧ = rank/2.
- General systems of quadratic forms over F₂: open. This is the Boyar–Find question (2018).
- Morse (arXiv:2608.30238, Aug 2026, with Lean) [S]: for four-term binary polynomial multiplication the unrestricted
  count is 9, equal to the quadratic one. "Failure of nonlinear feedback" at that size; five terms open.
- Lower bounds for c_∧(MM_n): only the dimension bound n² (the n² outputs are independent modulo affine functions, and
  every output is an XOR of inputs and AND-gate outputs) [D]. Best explicit c_∧ bounds in general are linear in the
  number of inputs plus outputs (Find; Boyar–Find) [S].
- Over infinite fields the question does not arise (Strassen). It is purely a small-field phenomenon: a gap needs an
  intermediate value of individual degree ≥ q.

**Fact 5. A separation between formal and functional complexity is already a theorem, given the release, for multilinear
polynomials [D].**
- Let g_n(x) = [the edge set x is exactly one directed Hamiltonian cycle on n vertices]. g_n is in P.
- Let f_n be its algebraic normal form, the unique multilinear polynomial over F₂ agreeing with g_n on 0/1 inputs. Its
  coefficient at x_S is ⊕_{T⊆S} g_n(T). No set of fewer than n edges contains a Hamiltonian cycle, and a set of exactly n
  edges contains one only if it is one. So f_n = HC_n + (terms of degree > n).
- A formal F₂-arithmetic circuit of size s for f_n gives one of size O(s·n²) for its degree-n component HC_n
  (homogenisation). By the release, HC_n needs superpolynomially many gates over every field [P, Lean].
- So f_n is a multilinear polynomial with polynomial Boolean complexity as a function and superpolynomial formal
  arithmetic complexity over F₂. Before the release this was known only conditionally (if every easy function had an easy
  normal form, ⊕P ⊆ P/poly, because the top coefficient is a parity count).
- This is the coarse version of the user's question. The bilinear, fine-grained version (matrix multiplication: n^{9/4}
  formal versus ? functional) is open, and the trick does not apply to it because a bilinear map *is* its own normal form.

**Answer to "plausible, known, or ruled out?"**
- Ruled out: by nothing. No lower bound above n² (conditionally n²√log n, §3.2) is known for any non-algebraic model.
- Known: in the superpolynomial multilinear regime, yes (Fact 5). For bilinear maps, no instance is known. The small
  cases that have been settled all say "no gap" (Fact 4).
- Plausible: [C] an AND-count gap for MM at some size, 10–15%. An n^{9/4−ε} bit algorithm over F₂, 1–2%. Fifty years of
  non-algebraic tricks (tables, word packing, regularity) have produced only polylog or 2^{√log} factors.

### 3.2 Does Lemma 4.1 give Ω(n²·√log n) for Boolean circuits multiplying matrices over F₂? [D from P]

**Lemma 4.1 [P, verbatim content].** Let the field have no ports. Consider a fixed trivalent topology with r input bits
and r output bits. Suppose that for every permutation in the support of a distribution, some choice of vertex tables
realises the r independent wires joining each input to its assigned output. If each input has a uniform destination on a
set of q ≥ 2 outputs (the sets may depend on the input), the topology has size Ω(r·√log q).

**Derivation.**
1. Let C be a Boolean circuit with s gates of bounded fan-in computing (A,B) ↦ AB over F₂, n×n.
2. Turn C into a trivalent network over a finite field k as in §2, but leave the n² output bits exterior instead of
   pinning them. The network has 3n² exterior bits and represents the 0/1 tensor [C = AB]. Size O(s + n²).
3. For a permutation π of [n], pin A to the permutation matrix P_π. Pinning replaces each exterior bit of A by a
   constant vector contracted into its neighbour, which changes tables and not the topology.
4. The pinned network represents [C = P_π B] = Π_{i,j} [c_{π(i),j} = b_{i,j}]: exactly r = n² independent binary wires,
   joining input bit (i,j) to output bit (π(i), j).
5. With π uniform on S_n, the destination of (i,j) is uniform on the q = n positions of column j.
6. Lemma 4.1 gives O(s + n²) ≥ c·n²·√log n, so s = Ω(n²·√log n).

**Hypotheses, stated plainly.**
- (H1) OpenAI's Lemma 4.1 as printed.
- (H2) *Some* finite field has no ports. The circuit is Boolean, so we may choose k. Ports depend only on the
  characteristic, so (H2) reads: some prime characteristic has no ports. Undecided in the paper; see §2.
- Nothing else. The argument uses only A ∈ {permutation matrices}.

**Scope of the conclusion [D].**
- It holds for every ring and semiring in which P_π·B permutes rows: F₂, Z, the Boolean semiring, (min,+).
- It holds for tensor networks, hence for parity-nondeterministic and unambiguous circuits.
- It is really a bound for "permute n records of n bits by a permutation given as a matrix". The upper bound for that
  sub-problem is O(n² log n) (sorting network on n-bit records), so the bound cannot exceed n² log n by this route.
- Same shape as the conditional bounds of Afshani et al. and Farhadi et al., with √log in place of log and the network
  coding conjecture replaced by (H2).

**The ports case: not covered, and why [D].**
- Theorem 2.2 holds there too, but for D_w and Tag(h,h): N = 2^h records with h-bit payloads and *independent*
  permutations for the t lists.
- Matrix multiplication moves whole rows: n-bit records, and a block-diagonal A gives n/N lists whose n/h payload chunks
  share one permutation. Shared permutations are a restriction of the independent-list tensor, which is the wrong
  direction for a lower bound. Counting only one h-bit chunk per row certifies volume n·h, not n².
- So in the ports case no superlinear bound for matrix multiplication follows from the printed statements. It would
  need the descent of [42, Prop. 14.1] run with "wide-record routing gates" (matrix products) in place of Tag(h,h) gates.
  The 9/4 paper's Theorem 2.1 is exactly such a statement for *algebraic* matrix multiplication; a Boolean version is
  target T1(b).

**Bottom line.** "No Boolean circuit of size O(n²)" is a theorem under (H1)+(H2), and open otherwise. Nothing in sight
excludes n²·polylog(n). The honest positive target is "n² polylog(n) bit operations over F₂".

### 3.3 Why this method can never give n^{2+ε} for Boolean circuits [D]

- Any price argument for a network on bits has the form (number of wires) × (edge length) ≥ Σ (demand distances).
- In a bounded-degree network with V vertices, demand distances exceed edge lengths by at most the diameter, O(log V);
  nonpositive curvature brings this to √log (the paper's entropy bound). So price arguments give at most polylog factors
  over the number of demanded bit-wires, here n².
- Grouping the bits into three parties does not help. One checks that T_n is a restriction of the graph tensor
  G = Σ_{A,B} e_A ⊗ e_B ⊗ e_{AB} (send e_u to e_{ij} if u = E_{ij} and to 0 otherwise, on each leg), so every spectral
  point F has F(T_n) ≤ F(G). But a network may sit at one site, and then the 2n² exterior wires to the other two sites
  already pay more than the price (log n)·(perimeter) of T_n.
- The arithmetic bound gets its polynomial strength from tensor powers (asymptotic rank, repeated compression). §3.1
  Fact 3 says functions have no tensor powers.
- So extending 9/4, or any n^{2+ε}, to Boolean circuits needs a new idea. It would be a circuit lower bound N^{1+ε/2} in
  the input length N = 2n² for an explicit function. That is not literally P versus NP, but it is the standard wall of
  Boolean circuit complexity (polynomially superlinear size for an explicit function), where natural-proof and
  PRF-based objections do apply. Say so to the user; do not target it.

## 4. The map of what is still open

Notation: ω = 9/4 means the arithmetic exponent of the release. "9/4-transfer" = whether the lower bound applies.

### (a) Product over a fixed finite field, especially F₂, by bits

- **Problem.** Given A, B ∈ F₂^{n×n} as bits, output AB. Models: word RAM with w = Θ(log n); Boolean circuits; AND-count.
- **Upper bounds.** Word RAM: n^{9/4+o(1)}; leaf lookup on b×b blocks with 2b² ≤ log n saves (log n)^{9/8}, invisible
  under the o(1) [D]. Four Russians alone: n³/log²n (Arlazarov et al. 1970) [K]. Circuits: n^{9/4+o(1)}.
- **Lower bounds.** Circuits: 2n² trivially; Ω(n²√log n) under (H1)+(H2) [D, §3.2]. Bounded depth with arbitrary gates:
  superlinear n²·λ_d(n) (Raz–Shpilka 2001) [K]. Depth-2 wires: Ω(n³)-type entropy bounds (Jukna 2008) [S].
  Time–space: T·S = Ω(n³) for branching programs (Abrahamson 1991) [K]. Bilinear/quadratic over F₂: 3n² − o(n²)
  (Shpilka 2001) [S], now n^{9/4} [P]. Small cases: rank of 3×3 over F₂ ≥ 21 (two Sept 2026 preprints) [S].
- **9/4-transfer.** To bilinear and quadratic circuits: yes. To anything else: no (§3.1).
- **Related classical question [K].** Can AND gates help to compute *linear* maps over F₂? Open. For fixed A, B ↦ AB is
  such a map.
- **Interest.** Maximal. An n^{9/4−ε} bit algorithm would be the first bilinear map on which non-algebraic provably beats
  algebraic. An n²·polylog algorithm would be "ω = 2 for computers".
- **Reductions worth knowing.** Average case = worst case over F₂ (item (e)). Boolean product ≤ F₂ product with random
  column masks and O(log n) repetitions [K]. So an n² polylog algorithm over F₂ gives triangle detection in n² polylog.

### (b) Boolean matrix multiplication and combinatorial algorithms

- **Problem.** (AB)_{ik} = OR_j (a_{ij} AND b_{jk}).
- **Upper bounds.** Any algorithm: n^{9/4+o(1)} via integers. Combinatorial: n³/2^{Ω((log n)^{1/7})},
  Abboud–Fischer–Kelley–Lovett–Meka (STOC 2024) [K]; n³/2^{Ω(√log n)}, deterministic, Cui–Liu–Woodruff
  (arXiv:2611.06717, 4 Nov 2026, with Lean) [S], answering the AFKLM question. Nothing truly subcubic.
- **Lower bounds.** Monotone circuits need exactly n³ ANDs (Pratt 1975; Paterson 1975; Mehlhorn–Galil 1976) [K]. General
  circuits: as (a), since P_π B is the same over the Boolean semiring.
- **9/4-transfer.** None. The Boolean semiring is not a field and no formal identity is required. The belief "BMM needs
  the ring exponent" has no theorem behind it.
- **Interest.** High. This is the weakest genuine matrix product, so the most plausible place for n^{2+o(1)}. But the
  combinatorial frontier is at 2^{√log} savings. [C] 1% in our hands.

### (c) Integer matrices on a RAM with word tricks and Kronecker packing

Entries of b bits, word size w, slot width L = 2b + ⌈log₂ n⌉. M(m) = m(log m)^{1/2+o(1)} is the release's integer
multiplication cost in bit operations [P, tapes paper].
- **Row packing.** X_i = Σ_j a_{ij} 2^{jL}, Y_k = Σ_j b_{jk} 2^{(n−1−j)L}; slot n−1 of X_i·Y_k is c_{ik}. n² multiplications of
  nL-bit integers: n²·M(nL) ≈ n³L·polylog bit operations. No gain; each product computes 2n−1 slots and uses one.
- **Whole-matrix packing.** One multiplication of integers of about 2n³L bits (three index ranges must be kept apart).
  M(n³L): again n³L·polylog.
- **In word operations.** n³L/w up to log factors. This is O(n²) exactly when w ≥ nL, a word holding a whole row with
  carries. With w = Θ(log n) and F₂ entries, slots need log of the block length, so the gain is w/log w: weaker than Four
  Russians.
- **Combined with fast multiplication.** Recursion to leaves of side n₀, leaves by packing: (n/n₀)^{9/4}·n₀³L/w. Polylog.
- **Large entries [K, from memory, check before citing].** Harvey–van der Hoeven (2018): n×n integer matrices with b-bit
  entries in O(n²·M(b)) once b is very large compared with n; the transform cost n²·b·(log factor) then dominates the
  pointwise products n^ω·b. With ω = 9/4 and M(b) = b√log b this needs √log b ≳ n^{1/4}, i.e. b ≳ 2^{√n} [D].
- **9/4-transfer.** Bit algorithms on integers are not arithmetic circuits (they use carries, shifts, truncation), so no
  transfer. But every known method is algebraic underneath.
- **Verdict.** "n² polylog by packing" is true only for words as long as rows, or entries of 2^{√n} bits. Quantified in E3.

### (d) (min,+) product and APSP

- **Upper bounds [S].** Alman–Vassilevska Williams, Oct 2026, "Truly subquadratic 3SUM and truly subcubic APSP via
  triangles in sparse lopsided graphs": APSP with polynomially bounded weights in n^{2.9995} (the brief's figure is
  n^{2.99942}; formalised by Anthropic, arXiv:2610.06783 per the brief, which I could not open). Saha–Ye
  (arXiv:2610.20297, 14 Oct 2026): (min,+) in Õ(n^{2.9964}), from the "thin matrix product theorem" plus the phased
  approach of Bringmann–Grandoni–Saha–Vassilevska Williams.
- **Bounded weights [K + D].** Weights in [−W, W]: W·n^{ω} via polynomial entries, now W·n^{9/4}. Zwick's directed APSP:
  n^{2+μ} with ω(1,μ,1) = 1+2μ; the exact formula gives μ = 1/2, so n^{2.5+o(1)}, the "ω = 2" value, already attained.
- **New frontier [C].** n^{2.5} is the natural barrier: every known subcubic route passes through bounded-weight or
  bounded-difference products that cost n^{2.5} even with ideal rectangular multiplication. An honest next target is
  n^{3−c} with c not microscopic; n^{2.5} would be the analogue of "ω = 2" here.
- **9/4-transfer.** None directly. (min,+) is not a ring. §3.2 gives the same conditional n²√log n circuit bound.
- **Does the ETH counting engine give anything?** No, and there is a new consistency check [D].
  - The engine evaluates sums of products with equality edges and signed integer pieces. (min,+) has no cancellation.
  - For the ring product, tr(ABC) is a triangle of three λ-bit wires, λ = log₂ n, with nodes of 2λ bits. The engine's
    saving is asymptotic in the number of bounded-arity nodes; here there are three nodes of unbounded arity. Our earlier
    dead end stands (`next/LOGBOOK.md`, "Matrix multiplication exponent via price geometry", x2).
  - Consistency check: the engine uses only ring operations on node values. By Baur–Strassen an arithmetic evaluation
    of tr(ABC) in T operations gives the product in O(T). So **no contraction engine built from ring operations can
    evaluate the triangle below n^{9/4}**. Any future claimed improvement of the pieces must respect this; the sentence in
    `research/README.md` ("2^{O(S/√log S)} times the cost of evaluating W") must be read with bounded-arity W.

### (e) Randomised, quantum, average-case, approximate

- **Verification.** Freivalds: O(n²) randomised [K]. Given 9/4, this is a provable gap between checking and computing in
  the arithmetic model [D]. Deterministic O(n²) verification on a small-word RAM: open; Korec–Wiedermann (2014) do it with
  O(n²) operations on very long integers; Künnemann (ESA 2018) relates derandomisation to sparse polynomial problems [K].
  Delegation: with a prover, the product is obtained and checked in O(n²).
- **Output-sensitive and sparse.** See (g).
- **Average case over F₂.** Worst-case to average-case reductions with Õ(1) overhead: Asadi–Golovnev–Gur–Shinkar (STOC
  2022); Hirahara–Shimizu (2023; ICALP 2025: agreement 1/p + ε suffices over F_p); Gola–Shinkar–Singh (2024);
  Shinkar–Singh (2025) [S]. So neither random inputs nor "51% of entries right" is easier. No n² there.
- **Approximate over ℝ.** Frobenius-norm error ε‖A‖‖B‖ in O(n²/ε²) by sampling (Drineas–Kannan–Mahoney 2006); compressed
  products Õ(n² + nb) for b heavy entries (Pagh 2012) [K]. An honest n², for a different problem.
- **Quantum.** Output size forces Ω(n²). Verification in O(n^{5/3}) (Buhrman–Špalek 2006). Boolean product: Θ(n√ℓ)
  queries for ℓ ones in the output (Jeffery–Kothari–Magniez 2012). Time–space: Kornerup et al., arXiv:2401.05321 (rev.
  Oct 2025): T = Ω(n³/√S) for the ring product, Ω(n^{2.5}/S^{1/4}) for the Boolean one [S]. At S = n² both are trivial.
- **9/4-transfer to quantum.** None; quantum algorithms read entries as data. [C] A quantum n^{2+o(1)} time algorithm for
  the dense product is not excluded and nothing points to it.

### (f) Rectangular products

- **Statement [P, Lean].** ω(x,y,z) = x + y + max(0,(x+y)z − xy)²/(4xyz) for x ≥ y ≥ z; dual exponent α = 1/2.
- So ω(1,1,z) = 2 for z ≤ 1/2 and 2 + (2z−1)²/(4z) above: 2.017 at z = 0.6, 2.057 at 0.7, 2.113 at 0.8, 2.178 at 0.9 [D].
  The cost is quadratically flat just above √n.
- **Nothing left algebraically.** What is left is to *use* it (E5): each algorithm whose analysis needs only
  ω(1,1,1/2) = 2 now runs at its "ω = 2" exponent, and each one that needs ω(1,1,1) is frozen at a known worse value.
- **Open edges [C].** The o(1) terms (is n×√n in n²·polylog?); uniformity and explicitness of the algorithms; the same
  three models as in (a) for the functional version.

### (g) Restricted matrix classes

- **Thin and low rank [D from P].** A = UV with inner dimension r = n^z given: AB costs n^{ω(1,1,z)+o(1)}. For r ≤ √n this is
  n^{2+o(1)} for the full n×n output.
- **Sparse [D from K + P].** Fully sparse (inputs and output have m nonzeros): the ABFK exponent solves
  ω(σ−1, 2−σ, 2−σ) = σ. With the exact formula the correction term is (2−σ)(3σ−4), zero at σ = 4/3, so the time is
  m^{4/3+o(1)}: the value ABFK state for ω = 2. Deterministic versions: Bennett–Gajulapalli–Golovnev–Warton
  (APPROX/RANDOM 2026) [S].
- **Structured [K, check constants].** Displacement rank d: Õ(d^{ω−1}·n) on generators
  (Bostan–Jeannerod–Mouilleron–Schost 2017), now d^{5/4}·n. Circulant, Toeplitz, Cauchy-like and hierarchical matrices
  are quasi-linear on their compressed representations, and by the release's DFT result cost N(log N)^{1/2+o(1)}.
- **Distributed [S].** "Sparse matrix multiplication exponent 1.5 in the low-bandwidth model" (arXiv:2611.15201).
- **9/4-transfer.** These are consequences of the theorem, not threatened by it.

## 5. Ranked targets

Odds are mine, conditional on the release being right, for a team of Opus executors over about two weeks.

### T1. Boolean lower bound for matrix multiplication over F₂, and the separation package (recommended)

- **Idea.** Three statements, increasing in difficulty.
  - (a) The corollary of §2 and the conditional theorem of §3.2, written as a referee-ready note: "under no-ports, every
    Boolean circuit for n×n matrix multiplication over any semiring has Ω(n²√log n) gates; O(n²) is impossible".
  - (b) The same without (H2): run the ports-case descent with matrix-product gates instead of Tag(h,h) gates.
  - (c) Fact 5 of §3.1 as a theorem with a Lean statement on top of OpenAI's `HamiltonianCycle` bound: an explicit
    multilinear family, easy as a function, superpolynomially hard formally over F₂.
- **Why now.** Lemma 4.1 and Theorem 2.2 did not exist before 24 Nov. Our team already works in the price language
  (b2 notebook, review-link).
- **Main risk.** (a) inherits everything from one lemma we have not verified; (b) may need the whole compression
  machinery; (c) is easy and may be judged folklore.
- **First experiment (≤ 3 h).** Write (a) and (c) in full, with every use of the paper's statements quoted. Pass: an
  adversarial referee finds no gap beyond (H1), (H2). In parallel E6.
- **Odds.** (a) 85%; (c) 90%, 50% that it is new enough to matter; (b) 15%.
- **Why it is "n²".** It is the precise answer to the user's wish: algebraically impossible; non-algebraically exactly
  n² impossible (conditionally), n² polylog open.

### T2. The corollary audit as a public note

- **Idea.** A two-page neutral note: "Theorem 2.2 of the 9/4 paper implies Ω(N(log N)^σ) Boolean circuits for element
  distinctness", with the derivation of §2, the list of famous bounds implied, and the questions for experts.
- **Why now.** No expert reading of the 24 Nov manuscripts is public (`next/LOGBOOK.md`, 26 Nov). This is the fastest
  route to independent scrutiny of the whole family, and scrutiny decides whether any of our targets stand.
- **Main risk.** Reputational if we misread the model. Mitigation: quote, do not paraphrase; state what we did not check.
- **First experiment.** Locate Theorem 2.2 and Lemma 4.1 in the Lean tree by name and report whether they are in the
  dependency cone of `square_exponent` (a grep, not a build).
- **Odds.** 95% to produce; impact depends on the answer.

### T3. Multiplicative complexity of the product over F₂ by unrestricted circuits (Boyar–Find for matrix multiplication)

- **Idea.** Define ω_∧(F₂): the exponent of the least number of AND gates, XOR free, functional correctness. It lies in
  [2, 9/4]. Decide small cases exactly (E1); prove "quadratic is optimal" for restricted classes (AND-depth 2, bounded
  formal degree); or find a non-quadratic family.
- **Why now.** The 9/4 theorem turns an old side question into the question of whether "ω = 2" survives in the most
  classical cost measure. Morse's August result gives a proof technique and a Lean precedent.
- **Tools to try.** The cyclic-algebra form (E7): the product is one multiplication in F_{2^n}[x; Frob]/(xⁿ − 1), and all
  Frobenius twists are free in this model. The Boolean ring is F₂^{2^N}, so AND-count is a straight-line complexity
  with pointwise products.
- **Main risk.** No amplification (§3.1 Fact 3): only an explicit infinite family can move the exponent. A lower bound
  n^{2+ε} here would imply a polynomially superlinear Boolean circuit bound, so only restricted classes are provable.
- **First experiment.** E1 with calibration, then E1b.
- **Odds.** Certified exact value at 2×2: 60%. A gap at 2×2 or ⟨2,2,3⟩: 5%. A theorem for AND-depth 2: 25%. An asymptotic
  family below n^{9/4}: 1–2%.

### T4. The derived-exponent atlas ("where ω = 2 survives")

- **Idea.** A table of every standard algorithm whose exponent is a function of ω(·,·,·), evaluated with the exact
  formula, marking those now at their ideal value: n×√n products, fully sparse m^{4/3}, Zwick APSP n^{2.5}, thin products.
- **Why now.** The exact formula is two days old; nobody has published the atlas.
- **Main risk.** Others will do it within days; errors in transcribing each algorithm's balance equation.
- **First experiment.** E5.
- **Odds.** 90% to complete; modest but real value, and the most quotable "n² theorems" for the user.

### T5. n²·polylog bit operations over F₂ (the user's literal wish)

- **Idea.** Look for a non-algebraic algorithm. Candidate entry points, none convincing:
  - structure-versus-randomness as in combinatorial BMM (AFKLM; Cui–Liu–Woodruff), with parity instead of OR;
  - exploit α = 1/2: any decomposition of a general product into O(polylog) products with inner dimension √n;
  - the cyclic-algebra form with free Frobenius;
  - run OpenAI's Theorem 2.1 forwards: the hypothetical compression used "ω < 9/4"; which of its steps become true
    for *networks* without that hypothesis?
- **Why now.** For the first time the algebraic and non-algebraic questions are provably different questions.
- **Main risk.** Almost certain failure; and by §3.2 the target must be n² polylog, not n².
- **First experiment.** A decomposition search: can a random n×n product over F₂ be written as a sum of few products
  ⟨n, √n, n⟩ after non-linear preprocessing? Count dimensions for n = 16, 64. Pass: fewer than √n thin products suffice
  for some preprocessing class. I expect fail.
- **Odds.** < 1%.

### T6. Deterministic n^{2+o(1)} verification of matrix products

- **Idea.** Derandomise Freivalds on a standard RAM, or prove verification as hard as computation for deterministic
  algorithms in some model.
- **Why now.** With computing fixed at 9/4, verification is the natural surviving "n²" and the gap is now provable in
  the arithmetic model. Our Finding 4 (deterministic identity testing from VP ≠ VNP) is the wrong grain, but the
  release's Fourier and polynomial-multiplication circuits are new fine-grained tools.
- **Main risk.** A known hard open problem; hitting-set constructions cost n³ in bits.
- **First experiment.** Literature pass (Künnemann 2018 and successors) and one page on what a deterministic n² verifier
  over F₂ must look like. Pass: a concrete conjecture with a falsifiable small case.
- **Odds.** 5%.

### T7. The ports question

- **Idea.** Decide whether characteristic 2 has ports. Either answer is useful: "no ports" makes §3.2 unconditional and
  gives σ → 1/2; "ports" gives expander-like port graphs for every spectral space.
- **Why now.** The companion proves ports only from a hypothesis it then refutes. Our flat-floor and CAT(0) work
  (b2 §3, "CAT(0) curvature alone forbids…") is adjacent.
- **Main risk.** This is nonlinear spectral gap theory for an unknown class of Hadamard spaces (Mendel–Naor territory).
- **First experiment.** Determine which Hadamard spaces are known to be spectral over F₂ (Euclidean flats, trees/star
  metrics by b2 §2, products), and check whether the entropy inequality of [43, Cor. 5.2] already fails for them. Pass: a
  written reduction of "ports" to a statement about that list.
- **Odds.** 10% for a decision; 50% for a useful partial statement.

### Negative targets (impossibility statements within reach of OpenAI's network bound)

The executor "anti" (`research/mm/anti/`) is writing the derivation of §3.2 in full. Here: my best statement, the
pitfalls, and the list. All are conditional on (H1) Lemma 4.1 as printed and (H2) some characteristic has no ports,
unless marked. "New" means: I know no earlier unconditional or conditional result of that form; before the release
every such statement was conditional on the network coding conjecture or absent.

**Best statement.** Let R be any semiring with 0 ≠ 1. Every trivalent tensor network over a finite field without ports
that represents the 0/1 tensor [C = A·B] for n×n matrices over R, with entries encoded in bits and 0, 1 encoded by fixed
strings, has size Ω(n²·β·√log n), where β is the number of bits per entry of B that can vary. In particular every
bounded fan-in Boolean circuit for the product has Ω(n²√log n) gates.

**Pitfalls.**
1. *Routing must depend on the input.* A fixed permutation is free wiring. The lemma needs one topology that realises
   every permutation in the support by changing only vertex tables. Pinning A does that: a pinned exterior bit is a
   constant vector contracted into a neighbouring table.
2. *Leave the outputs exterior.* The network must represent the graph tensor [C = AB], not a pinned scalar. A
   deterministic circuit gives it with coefficient exactly 1 over every k (unique consistent assignment).
3. *After pinning the tensor must be exactly a product of wires.* True for A = P_π. Not true for other A.
4. *Only the marginal law of each destination matters* (uniform on q outputs); the n² destinations are fully correlated
   through π and the lemma as printed allows that. Check this reading against the lemma's proof (the measure μ there is
   "a uniform input and its random destination").
5. *The field is ours to choose*, because the circuit is Boolean. Ports depend only on the characteristic.
6. *Size versus gates.* Size counts vertices and exterior bits; 3n² exterior bits are within the bound. Fan-out costs
   at most two equality vertices per gate.
7. *Sanity bounds.* The sub-problem (P, B) ↦ PB has circuits of size O(n² log n), so the method cannot exceed that.
   No O(n²) circuit is known even with P given by Beneš control bits. A guess-and-verify network does not obviously
   help: verifying a guessed source row still needs a selection.
8. *Do not claim the ports case.* Shared permutations across payload chunks are a restriction of the independent-list
   tensor of Theorem 2.2; that is the wrong direction (§3.2).
9. *The exponent.* √log n comes from Lemma 4.1 directly, not from Theorem 2.2's σ. Do not write (log n)^γ with γ from the
   ports case.

| # | Statement (Boolean circuits / trivalent networks) | Route | Within reach? | New? |
|---|---|---|---|---|
| N1 | n×n product over F₂ (any ring): Ω(n²√log n) | A = P_π, rows of B are n-bit records | yes, §3.2 | yes |
| N2 | Boolean (OR–AND) product: Ω(n²√log n) | same; P_π B is the same over the Boolean semiring | yes | yes for general circuits; monotone n³ is classical |
| N3 | (min,+) product with b-bit entries: Ω(n²·b·√log n) | A has 0 on π and +∞ elsewhere | yes | yes |
| N4 | Transitive closure on N vertices: Ω(N²√log N) | three-layer graph computes a Boolean product (Fischer–Meyer, Munro) | yes | yes |
| N5 | Inverse of a unitriangular matrix over F₂: Ω(n²√log n) | block matrix (I A 0; 0 I B; 0 0 I) | yes | yes |
| N6 | Polynomial multiplication over F₂, degree n: Ω(n√log n) | pin b = x^s; a·x^s is an input-dependent shift, r = n, q = n | yes | yes; and **tight** up to o(1) in the log exponent against the release's formal upper bound n(log n)^{1/2+ε} |
| N7 | Integer multiplication circuits: Ω(n√log n) | multiply by 2^s | yes | unconditional-in-(H2) version of Afshani et al. 2019; the release has only a Weak-ETH bound for tapes |
| N8 | Sorting n records of w ≥ log n bits: Ω(n·w·√log n) | direct | yes | cf. Farhadi et al. 2019 (conditional, log n) |
| N9 | Matrix–vector product, A as input: nothing | routes only n bits against n² input bits | no | — |
| N10 | Matrix–vector with preprocessing (circuit depends on A) | fixed A is fixed wiring; needs rigidity-type bounds for explicit F₂-linear maps | no | — |
| N11 | Online matrix–vector (OMv) | a data-structure model with adaptivity, not a circuit; the offline batch is N1 | no | — |
| N12 | Unrestricted AND-count of the 2×2 product over F₂ is 7 | SAT certificate (E1) | yes, by computation | probably; check Morse and Boyar–Find |
| N13 | Quadratic circuits are optimal for the product over F₂ within AND-depth 2 | structural, à la Morse | maybe (25%) | yes |
| N14 | Any n^{2+ε} bound for Boolean circuits or AND-count | none; §3.3 | no | — |

Remarks.
- N6 is the cleanest. With (H2) it pins the Boolean complexity of binary polynomial multiplication to
  n(log n)^{1/2±o(1)}: the only tight item in the table. For matrices the gap stays n²√log n versus n^{9/4}.
- N1–N5 are one theorem with five corollaries. N4 and N5 use only linear-size reductions.
- AND-count with free XOR is *not* reachable by the network bound: prices are monotone under linear maps at one
  site, not under XOR gates between distant bits, and network size counts XORs.
- Single-output problems (determinant, rank, triangle detection as a decision) get nothing from routing. Theorem 2.2
  itself is single-output (distinctness); a linear-size reduction from distinctness to triangle detection or rank would
  give Ω(N(log N)^σ) there, unconditionally. I do not know one. Worth an hour.

### Negative direction not to pursue

Extending the n^{9/4} bound to Boolean circuits is not a target. It asks for polynomially superlinear circuit size for
an explicit function, the central wall of Boolean complexity; the release's methods stop at polylog factors (§3.3).

## 6. If someone asks "so is n² possible or not?" — the one-paragraph answer

Counting arithmetic operations: no, over every field; the exponent is exactly 9/4. Counting bit operations over F₂: no
theorem forbids n² polylog; exactly O(n²) is forbidden if some characteristic has no ports; no known idea gets below
n^{9/4}; a size-2 or size-3 miracle would not change the exponent. In n²: products through inner dimension √n, fully
sparse products in m^{4/3}, randomised checking, and approximate products.

## 7. Consequences for our own notes if the flat hypothesis is a theorem

### 7.1 Is the companion's theorem really our FH? Yes [P]

- Our FH (`vpvnp/b2/notebook.md` §1, from Anthropic's Def. D.1): every finite subset of Euclidean space is a *price*, a
  pointwise limit of c·d_φ for spectral points φ on that finite party set.
- Companion Theorem 1.1 [P, intro.tex]: for any field k and real Hilbert space K there is an assignment H(T; x) such that
  (1) a binary wire u–v costs ‖u−v‖; (2) for each finite S ⊂ K of positive diameter there is **a spectral point F_S** with
  H(T; x) = W(S)·log₂F_S(T) for every tensor placed in S; (3) H depends on x only through distances and is homogeneous.
- So d_{F_S}(u,v) = ‖u−v‖/W(S) for all u, v ∈ S: the Euclidean metric on S is exactly W(S)·d_φ with φ = F_S. One invariant
  serves the whole configuration. No limit is needed. Over every field.
- Direction of the definitions: OpenAI's spectral point is Strassen's (additive on ⊕, multiplicative, monotone,
  normalised). That implies Anthropic's "subadditive on covers", since a sum is a restriction of the direct sum.
  d_φ ≤ 1 holds because W(S) ≥ diam(S).
- Lean scope [P, docs/379.md]: prices for sites in Euclidean space of any finite dimension are constructed in Lean; only
  the infinite-dimensional Hilbert extension is not. FH needs finite sets only.
- Extra, beyond FH: the shared-label law H(Δ_S(q)) = W(S)·log₂q (mean width), forced on any flat.
- Caveat: we have read statements, not proofs, and built nothing.

### 7.2 Statements of ours that become theorems (given the companion)

| Our statement | Where | Was | Becomes |
|---|---|---|---|
| Flat floor: E edges each crossing all of p merges, T = 2^{o(λ)} pieces ⇒ some piece has c_k ≥ Eλ/√p − o(λ) for all k | `vpvnp/b2/notebook.md` §3 Thm 3; reviewed `next/review-link.md` 1b | [R\|FH] | theorem over every field |
| Δ₃, three merges: ρ ≥ 1/√3, one piece ≥ 3√3λ under all three merges | b2 §3 Cor. (a); review-link 1b | [R\|PH] | theorem |
| Δ₃, two merges: min-floor ≥ (9/√2)λ ≈ 6.36λ (was 4λ) | b2 §3 Cor. (b) | [R\|FH] | theorem |
| p-merge levels with every edge crossing every merge: ρ ≥ 1/√p; α′ > 1 needs p ≥ 5 | b2 §3 Cor. (c); `LOGBOOK.md` Finding 3 (z1) | [R\|FH] | theorem |
| Rectangular crossing: cost function exactly 2‖(λ₁,λ₂)‖₂; App. B / Fock pieces optimal on the whole curve | b2 §3 "Rectangular crossing (sharp)"; `pieces.md` §2.3 | [R\|PH] | theorem |
| ρ_× = 1/√2 for the crossing: the engine's two-merge pieces are optimal | `LOGBOOK.md` H1; Finding 2 | [C] | theorem (lower bound b2, upper bound App. B) |
| sup_t (t + σ(t)) ≥ 2√2 for every two-term splitting curve | `next/x6/notebook.md` Consequence 1 | under PH | theorem |
| No splitting SWAP_Q = R + L with rank(R) and opSR(L) both ≤ Q^{√2−δ} | x6 Consequence 2 | "under FH it cannot exist" | theorem |
| K₄ with three perfect matchings: floor √2/3 | `LOGBOOK.md` 24 Nov, "K₄ under the real accounting" | flat floor | theorem (as a floor) |

- **The swap-splitting problem.** Yes: the circle is the limit, in the sense of x6. In units λ = E = 1, every family of
  splittings has t + σ(t) ≥ 2√2 somewhere, and the paper's curve σ = √(4 − t²) attains it. Precisely: the *balanced point*
  of the circle is optimal (τ = √2), and b2's sharp rectangular statement gives the whole curve for unequal widths:
  with |a+b|² + |a−b|² = 4, the bound λ₁|a+b| + λ₂|a−b| is tight. Keep the review's wording: these are liminf statements
  with T = 2^{o(λ)} pieces.
- **H6 is dead.** The cheaper trigger "every piece has min_k c_k ≤ (E/√p − η)λ" (review-link, Moderate 1) would refute
  FH. So unbalanced families such as (1.3λ, 2λ), (2λ, 1.3λ) do not exist, over any field.
- **The win-win collapses to one side.** "A family beating the flat floor ⇒ contracting ⇒ stronger permanent bound" has
  a false premise now. The dichotomy (Anthropic Thm D.2) is settled on the flat side. Whether the contracting hypothesis
  *also* holds is not decided by FH unless the two are exclusive; check D.2's wording before writing "contracting is
  false". The stronger permanent bound is moot anyway: OpenAI claims exp(c(log N)²/(log log N)²).
- **`two-proofs.md` Cor. 1′** ("a √D-shortening gives ¬FH"): now reads "no √D-shortening exists".
- **Finding 3 (why 1/√2 is rigid)**: the five structural no-gos (ladder theorem, grids, Weyl-diagonal, K₄ two-piece,
  characteristic 2) are now explained by one theorem. They remain valid as independent proofs.
- **Engine rate.** For levels built from two-merge crossings the exponent (log)^{-1/2} is optimal *for the piece method*.
  This is not a lower bound for #3-SAT algorithms.

### 7.3 What remains open

- **Three merges at 1/√3.** The floor is now a theorem; attainment is open. b2's Δ₃ construction side is unchanged
  (`LOGBOOK.md`: "Δ₃ ≥ 1/2 theorem and three-wire no-gos unreviewed"; H2: a three-merge object from multivariate
  orthogonal polynomials). If 1/√3 is attained: #3-SAT in 2^{O(n/(log n)^{0.79})}.
- **The floor itself may rise.** FH gives lower bounds from Euclidean prices only. The 9/4 paper says in terms that
  "prices coming from Euclidean flats give ratio two" for the matrix multiplication triangle and that "a different
  geometry is needed to reach 9/4" (a tripod with unit arms and shared-label rate 8/3) [P, §1.3]. So non-flat prices
  exist and can beat flat ones. For p ≥ 3 merges the true floor may be above 1/√p. For p = 2 it cannot, since the upper
  bound matches. **New question for b2:** redo the Δ₃ and K₄ floors over tripod and product-of-tripod prices
  (`vpvnp/b2/spider.py` already handles tree-like prices; star metrics are prices over every field by b2 §2).
- **K₄.** Floor √2/3 is a theorem; the known constructions reach only 1/3 (`LOGBOOK.md`). Open on both sides for the same
  reason.
- **p ≥ 5 merges, and configurations with edges internal to some merges.** Untouched (b2 "What this means").
- **Flat-case hub method capped at k^{3/2}** (`LOGBOOK.md` dead ends, b1): "proved in the paper's regime, conjectured in
  general" is unchanged, but its hypothesis (the flat case) now holds.
- **Mean width as a new tool.** The shared-label law prices copy tensors, which our accounting never used. Any piece
  family that shares a label among ≥ 3 groups can now be bounded exactly on flats. Worth one session on Δ₃.

### 7.4 Suggested edits (for the lead; I changed no file but this one)

- `next/LOGBOOK.md` H1: tag "[theorem given OpenAI 379, unverified by us]"; H6: [X, given 379].
- `vpvnp/b2/notebook.md`: replace [R|FH] and [R|PH] by [R, given OpenAI Thm 1.1]; keep the conditional tags in brackets.
- `research/README.md`, engine paragraph: add "W of bounded arity; ring-operation engines cannot beat n^{9/4} on the
  triangle (Baur–Strassen)".

## 8. If the release is wrong

- **If the 9/4 lower bound falls but the companion stands.** ω = 2 is open again and the user's algebraic target is alive;
  the best upper bound is still 9/4 (OpenAI, Oct 2026, with independent expositions by Amanov–van den Berg–Zuiddam,
  Doğan–Lysikov–Sakabe–Walter, Shpilka, Pass [S]), and Amanov–van den Berg–Zuiddam's barrier says the current
  degeneration method cannot go below 9/4. §7 is unaffected. §2 and §3.2 fall if the error is in Theorem 2.2 or Lemma 4.1.
- **If Theorem 2.2 falls.** Then so does the lower bound (its only route), the corollary of §2 and T1(a,b), T2. T3, T4's
  upper-bound entries, T5, T6 are unaffected: the Boyar–Find question, the rectangular *upper* bounds and α ≥ 1/2 do not
  depend on it. But α ≤ 1/2 and the exact formula do, so E5's "equal to the ω = 2 value" column would become "at most".
- **If the companion falls.** §7 reverts to the 24 Nov state: FH and PH are hypotheses, the win-win is live, H6 is a
  target again. The 9/4 lower bound cites the companion for prices on nonpositively curved spaces and for the routing
  results, so it would probably fall too.
- **Signals to watch.** An expert reaction to the Boolean corollary; whether Li–Yang-style circuit complexity people
  accept Lemma 4.1; any erratum on "ports".

## 9. Recommendation

**T1**, with T2 as its first deliverable and E1 running on the side.

- The single most promising and coolest target: *"No Boolean circuit multiplies matrices over F₂ in O(n²) gates, and no
  arithmetic circuit does it below n^{9/4}; and here is an explicit multilinear polynomial that bits compute easily and
  arithmetic cannot."* It is the complete, honest answer to "find an n² algorithm": a theorem about why not, with the
  exact residual gap (n² polylog) stated.
- Honest odds, given the release: the conditional theorem and the multilinear separation, written and referee-proof,
  85%. Unconditional (ports case), 15%. That the release itself survives expert reading of Theorem 2.2: I cannot
  estimate it, and it dominates everything.
- An actual n²·polylog algorithm over F₂ (T5): under 1%. I would not staff it beyond one exploratory session.
- If the user wants a *positive* n² result this week: T4. "Fully sparse products in m^{4/3+o(1)} and n×√n products in
  n^{2+o(1)} are theorems" is true (given the release), quotable, and takes an afternoon.

## Sources

Read in the scratchpad clone of github.com/openai/math: "The matrix multiplication exponent is nine fourths" (paper.txt,
§1–2, §4); "Euclidean geometry in the asymptotic spectrum of tensors" (build/intro.tex, port-graphs.tex);
lean/docs/379.md, 107.md; CONTENTS.md.

Search results and abstracts (not read in full):
- Morse, unrestricted multiplicative complexity of four-term binary polynomial multiplication: https://arxiv.org/abs/2608.30238
- Find / Boyar–Find, multiplicative complexity of vector-valued Boolean functions: https://arxiv.org/abs/1407.6169
- Mirwald–Schnorr, TCS 102 (1992) 307–328: https://ftp.math.utah.edu/pub/tex/bib/idx/tcs1990/102/2/307_328.html
- Abboud–Fischer–Kelley–Lovett–Meka: https://arxiv.org/abs/2311.09095
- Cui–Liu–Woodruff, combinatorial BMM in n³/2^{Ω(√log n)}: https://arxiv.org/abs/2611.06717
- Saha–Ye, (min,+) in Õ(n^{2.9964}): https://arxiv.org/abs/2610.20297
- News summary of Alman–Vassilevska Williams: https://aiweekly.co/alerts/alman-and-williams-crack-textbook-3sum-and-apsp-bounds
- Amanov–van den Berg–Zuiddam, exposition and barriers: https://arxiv.org/abs/2610.30054
- Doğan–Lysikov–Sakabe–Walter, tensor value and the 9/4 bound: https://arxiv.org/abs/2611.09716
- Raz–Shpilka, lower bounds for matrix product: https://arxiv.org/abs/cs/0201001
- Jukna, entropy of operators: https://eccc.weizmann.ac.il/report/2008/019/download
- Lower bound 21 for 3×3 over F₂: https://arxiv.org/abs/2609.06725 and https://arxiv.org/abs/2609.18722
- Kornerup et al., quantum time–space tradeoffs: https://arxiv.org/abs/2401.05321
- Jeffery–Kothari–Magniez: https://arxiv.org/abs/1112.5855
- Gola–Shinkar–Singh, matrix multiplication reductions: https://arxiv.org/abs/2404.08085
- Hirahara–Shimizu, ICALP 2025: https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/LIPIcs.ICALP.2025.97/LIPIcs.ICALP.2025.97.pdf
- Abboud–Bringmann–Fischer–Künnemann, fully sparse: https://arxiv.org/abs/2309.06317
- Bennett–Gajulapalli–Golovnev–Warton: https://drops.dagstuhl.de/storage/00lipics/lipics-vol392-approx-random2026/LIPIcs.APPROX-RANDOM.2026.40/LIPIcs.APPROX-RANDOM.2026.40.pdf
- Low-bandwidth sparse exponent 1.5: https://arxiv.org/abs/2611.15201

Cited from memory, to be checked before any external use: Li–Yang 2022; Find–Golovnev–Hirsch–Kulikov 2016;
Iwama–Morizumi 2002; Golovnev–Hirsch–Knop–Kulikov 2018; Afshani–Freksen–Kamma–Larsen 2019;
Farhadi–Hajiaghayi–Larsen–Shi 2019; Miles–Viola; Morgenstern 1973; Valiant 1977; Abrahamson 1991; Shpilka 2001;
Pratt / Paterson / Mehlhorn–Galil; Harvey–van der Hoeven 2018; Korec–Wiedermann 2014; Künnemann 2018;
Buhrman–Špalek 2006; Drineas–Kannan–Mahoney 2006; Pagh 2012; Bostan–Jeannerod–Mouilleron–Schost 2017; Zwick 2002;
Winograd 1968; Baur–Strassen 1983.
