# A consequence of Theorem 2.2 of "The matrix multiplication exponent is nine fourths": a superlinear Boolean circuit lower bound

*Note, 26 November 2026. We have not checked the proof of the theorem this note relies on, and we have not built its Lean formalisation.*

**Summary.** OpenAI's 24 November 2026 release (github.com/openai/math, family 379) includes the paper "The matrix
multiplication exponent is nine fourths" [MM]. Its Theorem 2.2 is a lower bound for tensor networks over finite
fields that compute "list distinctness". A short argument, given in full below, turns it into the following
statement. *Every bounded fan-in Boolean circuit deciding whether 2^w words of 2w bits are pairwise distinct has
Ω(N·(log N)^σ) gates, where N = 2w·2^w is the input length and σ > 0 is some constant.* The function is in AC⁰.
The best lower bounds published so far for explicit functions are linear (about 3.1n). We did not find this
consequence stated in the release. In the release's Lean library, the network bound appears as a theorem in the
dependency cone of the square-exponent theorem.

## 1. What the paper states

Quotations are from [MM], §2.1 (p. 7).

- **Networks.** "A *bit tensor* of arity u is a function {0,1}^u → k. In a tensor network each vertex carries such a
  table. A wire pairs two argument positions, and each unpaired position is a named exterior bit. For a fixed
  setting of the exterior bits, multiply the vertex entries and sum over all settings of the internal wires. [...]
  A network is *trivalent* if each vertex has arity at most three. Its *size* counts the vertices and exterior
  bits. Its *volume* counts the vertices and all wires, including the exterior wires."
- **The function.** "For w ≥ 1, let D_w be the zero-one tensor for a list of 2^w words of 2w bits each. Its value
  is one exactly when the words are pairwise distinct. It has n_w = 2w·2^w exterior bits. The tensor D_w^{⊗t} tests
  distinctness separately within each of t independently specified lists. The network may connect vertices across
  lists."
- **Theorem 2.2 (Volume of list distinctness).** "There is a constant σ > 0, depending only on k, such that for all
  sufficiently large w and every integer 1 ≤ t ≤ 2^w, vol_k(D_w^{⊗t}) > t·n_w·w^σ." Here k is a finite field.
  The theorem has no hypothesis on the matrix multiplication exponent.
- **The constant σ** is not given explicitly. §4 proves Theorem 2.2 in two cases that depend on the
  characteristic, and the release does not say which case holds:
  - "no ports": any σ < 1/2, via the routing Lemma 4.1;
  - "ports": σ < min{a/4, bδ/4, 1/4}, with a, δ taken from companion papers and not computed.
- **Circuits.** The paper converts a circuit into a network once, for a sorting circuit, inside the proof of
  Proposition 2.3 (ω_k ≥ 9/4): "use the zero-one table of each gate, copy bits at fan-outs with equality tables, and
  pin the output to one. For each accepted input there is exactly one consistent assignment of the internal wires."
  The paper does not state a general circuit-to-network lemma, and it does not mention lower bounds for Boolean
  circuits.

**The Lean version.** We read the import graph and the statements, without building anything. The proof of
`square_exponent` (ω = 9/4 over every field) uses the following theorem, from
`OAI/LinearAlgebra/MatrixExponent/BatchDescent/Hard.lean`:

```lean
theorem manyList_full (F : Type) [Field F] [Finite F] :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
      1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) → Realizes F w t m →
      (t : ℝ) * listBits w * (w : ℝ) ^ η < m
```

- `Realizes F w t m` says that D_w^{⊗t} is represented exactly by a network whose size (vertices plus exterior
  bits) is m. Every vertex table of the network has at most three bits.
- `listBits w = 2·w·2^w`.
- The chain is `square_exponent → omega_eq → contact_of_installations → contact_of_network_estimates`. The last
  step applies `Tagged.manyList_of_tag (BatchDescent.hard p)` for every prime p.
- The 592 modules in this cone contain no `sorry` or `axiom`.
- The catalogue lean/docs/379.md does not mention the theorem, and the Lean library states no Boolean-circuit
  consequence of it.

## 2. From networks to circuits

**Model.** A Boolean circuit has N inputs and gates of fan-in at most 2: any of the 16 binary functions, NOT, and
the constants. Fan-out is unbounded and there is one output. Its size s is the number of gates.

**Lemma (elementary; ours).** Let k be any field. A circuit of size s computing f: {0,1}^N → {0,1} gives a
trivalent k-network that represents f exactly. The network has at most 3s + N + 2 vertices, so its size is at most
3s + 2N + 2.

*Construction.*
1. Each gate g = op(u, v) becomes a vertex with table [c = op(a, b)] of arity 3. NOT gates get arity 2, constants
   arity 1.
2. A node of fan-out f ≥ 2 feeds a chain of f − 1 copy vertices [a = b = c]. Fan-out counts the use as output.
3. An unused input gets an arity-1 vertex whose table is 1.
4. The output wire ends at a vertex with table [c = 1].
5. The inputs are the exterior bits.

*Count and correctness.* The fan-outs sum to at most 2s + 1, so there are at most 2s + 1 copy vertices. Fix an input
x. A nonzero term of the sum must assign every wire the value the circuit computes on it, by induction along the
circuit. Hence at most one term is nonzero, and the sum equals [f(x) = 1] in any characteristic. All wires carry
bits, so no field values occur on wires. The Lean library uses the same steps (`DNet.table/comp/par/dup`, `pin`) to
build its sorting network.

**Corollary (given Theorem 2.2 as stated).** Take f = D_w, N = n_w and t = 1, and use `manyList_full` with k = F₂.
Then N·w^η < 3s + 2N + 2, so

  s > N·(w^η − 2)/3 − 1,  with w = log₂N − log₂log₂N − O(1).

Thus **s ≥ (1/3 − o(1))·N·(log₂ N)^η** for all large N of the form n_w, for some η > 0. To cover every N, apply D_w
to the first n_w input bits. The constant η is not explicit. If F₂ has "no ports", the paper's Lemma 4.1 gives any
exponent below 1/2.

**Further consequences, by the same lemma.** We have checked these less carefully.
- *Direct sum.* A circuit computing D_w on t independent lists, or only the AND of the t answers, needs
  (1/3 − o(1))·t·N·(log N)^η gates for t ≤ 2^{w^{1+η}}.
- *Counting circuits.* The bound holds for nondeterministic circuits where the number of accepting witnesses is
  ≡ D_w(x) mod p, for any prime p. This includes parity (⊕) circuits and unambiguous circuits. It does not include
  ordinary nondeterministic circuits. "Some word repeats" has nondeterministic circuits of size O(N): guess two
  indices and compare.
- *Formulas and branching programs* add nothing new. Nechiporuk's method already gives near-quadratic bounds for
  element distinctness in those models.
- *Upper bound.* Sorting networks give O(N log N) gates (AKS) and O(N log² N) (Batcher). D_w is also in uniform AC⁰.

## 3. How this compares with the literature

- **Explicit circuit lower bounds.** Over the full binary basis the record is 3.1n − o(n) (Li–Yang, STOC 2022).
  Earlier bounds are (3 + 1/86)n (Find–Golovnev–Hirsch–Kulikov, FOCS 2016) and 3n (Blum, 1984). Over the De Morgan
  basis U₂ the record is 5n − o(n) (Iwama–Morizumi, MFCS 2002, after Lachish–Raz's 4.5n). Gate-elimination proofs
  are known to stall near these constants. To our knowledge, no superlinear bound for any explicit function was
  known before this release. The release's own family 378 claims superlinear bounds for a language in E^NP on
  infinitely many lengths.
- **Barriers.** Natural proofs do not obviously exclude bounds of the form N·polylog N. They do apply to the extent
  that pseudorandom functions of quasi-linear size exist (Miles–Viola's candidates, CRYPTO 2012). Whether the
  argument in [MM] is "natural" is not clear to us. The Lean route is a descent/diagonal argument.
- **Conditional bounds via network coding.** If the undirected multiple-unicast conjecture held, constant-degree
  circuits for multiplication would need Ω(n log n) gates (Afshani–Freksen–Kamma–Larsen, ICALP 2019). The same
  conjecture gives external-memory sorting bounds (Farhadi–Hajiaghayi–Larsen–Shi, STOC 2019). In October 2026 the
  conjecture was refuted in preprints, with polylogarithmic coding gaps of small exponent:
  - Braverman–He, arXiv:2610.10108;
  - Zhang–Li–Li, arXiv:2610.09367;
  - see also arXiv:2610.20079.

  [MM]'s bound is of the weaker form (log N)^σ with σ < 1/2. A comparison with these coding gaps would be a useful
  check.
- **Element distinctness in other models.** Ben-Or proved Ω(n log n) for algebraic decision trees. Ajtai proved
  superlinear time for linear-space branching programs. Beame–Saks–Sun–Vee proved T = Ω(n·√(log(n/S)/log log(n/S)))
  for randomized branching programs. None of these models is general Boolean circuits.
- **Other lower bounds in the release**, with their Lean status from lean/docs/379.md:
  - Fourier transforms of order n: a lower bound Ω(n√log n) and an upper bound O(n(log n)^{1/2+ε}) for binary
    linear gates with arbitrary coefficients, also in batches. Both bounds are in Lean.
  - Formal polynomial multiplication: Ω(J·n√log n) is proved only in the paper; the upper bound is in Lean.
  - Integer multiplication on tapes: Ω(n√log n) under Weak ETH, in Lean.
  - VF ⊊ VBP ⊊ VP ⊊ VNP: in Lean.
  - Hamiltonian cycle and the permanent: superpolynomial arithmetic bounds, in Lean.

## 4. What we checked, and what we did not

**Checked:**
- We read the paper's definitions and Theorem 2.2 in the LaTeX.
- We checked the input length n_w, trivalency, and that "represents" means exact equality.
- We read the Lean definitions (`Network.lean`, `ListBounds.lean`) and the statement of `manyList_full`.
- We confirmed from the imports that `manyList_full` is in the dependency cone of `square_exponent`.
- We searched the release for an existing statement of the circuit consequence and found none.

**Not checked:**
- the proof of Theorem 2.2, or that of its companion inputs;
- the Lean build, or the Comparator check;
- whether any other text already states this consequence.

Logically, the corollary needs only Theorem 2.2 and the lemma in §2. So if Theorem 2.2 is true, the corollary
holds. If the corollary is false, Theorem 2.2 is false, and so is a Lean theorem that the proof of ω = 9/4 uses.

## 5. Three questions

1. **For the authors.** Is the Boolean-circuit consequence intended, and is there an explicit value, or an explicit
   lower bound, for σ (or η) over F₂?
2. **For experts in circuit complexity.** Does a mod-2 counting circuit (⊕-circuit) of size O(N) exist for
   distinctness, or one of size o(N·(log N)^ε) for every ε > 0? Either would contradict Theorem 2.2, and it is the
   most direct way to test it.
3. **On the proof structure.** The paper proves Theorem 2.2 in two cases, "ports" and "no ports". The Lean theorem
   `BatchDescent.hard` carries neither hypothesis and uses a descent/diagonal argument. Does the Lean proof avoid the
   case split? Does the no-ports Lemma 4.1 fit the 2026 refutations of the multiple-unicast conjecture?

---

**Three-post summary.**

1/ OpenAI's "matrix multiplication exponent is 9/4" paper (24 Nov 2026) has a lower bound, Thm 2.2, for tensor
networks over finite fields that test whether 2^w words of 2w bits are all distinct. With a standard
circuit-to-network embedding (each gate a table, fan-out by equality tables), it gives a Boolean circuit bound.

2/ Consequence: every bounded fan-in circuit for this AC⁰ function on N bits needs Ω(N·(log N)^σ) gates, for some
σ > 0. Published explicit bounds are linear (3.1n, Li–Yang 2022). We did not find this stated in the release. In
its Lean library, the network bound is a theorem the 9/4 proof uses.

3/ We have not checked the proof or built the Lean. The derivation is elementary, so the corollary stands or falls
with Thm 2.2. Questions: is it intended? What is σ? Is there a linear-size ⊕-circuit for distinctness, which would
refute it? Note with quotes: [link]
