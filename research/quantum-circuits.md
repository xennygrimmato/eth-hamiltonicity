# Exact quantum circuit amplitudes in 2^{O(G/√log G)}: a corollary of the 2026 ETH refutations

29 Oct 2026. Tags: **[Paper-A]** Anthropic's manuscript, **[Paper-O]** OpenAI's preprint (LaTeX in the
scout clone, read only, nothing run from it), **[Lit]** published literature, **[Computed]** checked in exact
arithmetic by `research/scripts/qc_*.py`, **[Mine]** a derivation not machine-checked.
**Everything algorithmic below is conditional on the refutations being correct.** For the Anthropic route
that means [A] Lemma 8(i), Theorem A(b) and Theorem B, in the forms quoted in `exact-hc-theorem.md` §1. For
the OpenAI route it means [O] Theorem `thm:tensor-contraction` (`quantitative-reduction.tex`
l.24–49). None of these is Lean-checked in the sharp form we use: in Anthropic's development the counted
route is formalised, while OpenAI's sharp appendix is not formalised.

---------------------------------------------------------------------------------------------------

## 0. Verdict

* **Novelty.** Neither lab states the corollary. Nor do the press coverage, the blogs or the discussion
  threads we could find (§1). As a mathematical step it is a near-immediate corollary of OpenAI's
  appendix theorem, which literally contracts Boolean tensor networks with one-bit wires: anyone who
  reads that theorem will see it. Its content lies in getting the hypotheses right (ring, precision,
  degree, denominators), which is what §2–3 do.
* **Theorem Q1 [Mine, conditional].** ⟨y|C|x⟩ can be computed *exactly*, as (a₀+a₁ω+a₂ω²+a₃ω³)/√2^k with
  aⱼ, k ∈ ℤ, for every Clifford+T(+CS, CH, SWAP) circuit on n qubits with G two-qubit gates (any
  connectivity) and G₁ single-qubit gates. The time is **2^{O(G/√log G)}·poly(n+G₁)**, deterministically.
  The same holds for exact output probabilities and marginals (G ↦ 2G), and therefore for exact sampling
  (§2). For depth-d circuits this is **2^{O(dn/√log n)}**. Through OpenAI's engine the space is
  polynomial, provided the Hadamard count is O(G+n).
* **Verified [Computed].** On 300 random circuits (n ≤ 6, G ≤ 20, up to 25 single-qubit gates; seeds 1–2; 1,073
  Definition-2 networks evaluated by brute force over crossing bits, 850 of them also by the literal
  Definition-2 sum) the integer network of Definition 2 [A], decoded, equals the exact
  Z[ω] state vector, and so does the (ℤ/2^{P₀})[V]/(V^ℓ) contraction of [O]. Marginals agree via the
  doubled network, and four deliberately broken variants are all caught (§4).
* **Strongest honest implication.** Assuming the refutations, the √log G rate is the right one for this
  route: #3-SAT with O(n) clauses reduces to amplitudes of constant-depth O(n)-gate circuits, so this class
  is exactly as hard as the refuted problem, and nothing better than the engine's rate can come from it.
  So every fine-grained supremacy statement whose hard family has **O(n) gates**, or whose hypothesis is
  ETH, SETH or a "2^{Ω(m)} for 3-CNF" variant, loses its foundation or is refuted (§5.2, table). Concretely:
  Morimae–Tamaki's Conjecture 7 is refuted outright, and the depth-scaling SETH variant is refuted via
  Calabro–Impagliazzo–Paturi.
  Statements about **dense** instances survive: Dalzell–Harrow–Koh–La Placa's poly3-NSETH(a) with up to
  Θ(n³) terms, per-int-NSETH (permanents), Morimae–Tamaki's average-case dense-cubic and quadratic+CNF
  conjectures, and Aaronson–Chen's QUATH/HOG. We confirm the team's belief that [A]'s clause-count-free
  mechanism does **not** carry over to ±1 cubic phases (§6). It fails because assignments with many
  "violated" factors contribute ±1, not 0 [Computed]. What does carry over is a weaker 2-adic truncation,
  costing O(n·log(m/n)) wires. That is subexponential only for m ≤ n·2^{o(√log n)} terms.
* **Practical meaning: none.** The constants are galactic. With [A]'s constants the bound beats
  Schrödinger's 2^n for depth d only once log₂ n ≳ 5·10⁴·d² (§7). Sampling-based supremacy experiments
  (n ≈ 50–100) are untouched.

---------------------------------------------------------------------------------------------------

## 1. Novelty search (what was found, exactly)

**OpenAI's LaTeX** (`main_full_version.tex`, 4,829 lines; `quantitative-reduction.tex`;
`quantitative-contraction.tex`; `quantitative-circuits.tex`). We searched case-insensitively for quantum,
qubit, amplitude, tensor network and circuit:

* *quantum, qubit, amplitude*: **0 hits** in all four files.
* *circuit*: only Boolean circuits. These are the circuit-to-3-CNF reduction (l.135–172), the
  E^NP circuit lower bound (Cor. `cor:quantitative-circuits`, l.183–193 and l.4230–4269) and
  `quantitative-circuits.tex` (Williams's witness-circuit argument).
* *tensor*: only the appendix engine ("Boolean tensor network", `quantitative-reduction.tex` l.15–49),
  used for #SAT and for sparse F₂-polynomial systems (Lemma `lem:tensor-sparse-query`). Related work
  mentions fermionants and permanents (Björklund–Kaski–Williams, l.398–405) but not quantum circuits.
* The repo catalogue (`CONTENTS.md`, `overview.tex`) mentions "quantum" only for geometric Langlands
  (family 069) and Liouville quantum gravity (family 211).

**Anthropic's paper** (`.../anth/fm/paper.txt`, 3,013 lines):

* "tensor networks" appears as a keyword (l.49). It also appears in related work: the evaluated sums
  are "contractions of closed tensor networks [MS08, Oru14, RS19]" (l.149–153), where **[MS08] is
  Markov–Shi, *Simulating quantum computation by contracting tensor networks*** (reference l.1419).
  Austrin–Kaski–Kubjas also appears (l.153–163, l.2775–2790).
* There is **no** statement about quantum circuits, amplitudes or supremacy. §7 lists only SAT/graph
  consequences, NSETH, and E^NP circuit lower bounds (l.1160–1215).

**Web (29 Oct 2026)**:

* The Quantum Insider ("OpenAI Computing Claim Faces Review, Raising Questions About Quantum Advantage",
  27 Oct) is generic. It says "some arguments about the difficulty of simulating quantum computers rely on
  related assumptions". It mentions an unnamed study whose SETH-based limits "would need another basis".
  It has no theorem or bound.
* The Quantum Zeitgeist substack ("The OpenAI Exponential Time Hypothesis Claim and What It Means for
  Quantum Computing") says SETH-based exact-output-probability hardness "will need new foundations". It
  says Dalzell et al.'s degree-3 assumption is not obviously affected because OpenAI's method "only
  handles sparse polynomial systems". It says random circuit sampling rests on non-collapse of PH, and
  that the bounded-width QSETH falls. It does **not** state a subexponential simulation theorem.
* The Hacker News thread (item 50251661) has no quantum discussion. A Medium explainer, mindstudio,
  Washington Times and forklog have none either.
* Closest prior work: Wahl–Strelchuk (PRL 131, 180601, 2023; arXiv 2208.01498), who give subexponential
  contraction for **geometrically local** (finite-range, D ≥ 2) circuits via planar separators. That is a
  locality result, unrelated to the refutations.

**Status:** not stated anywhere we could find. We claim the careful statement and proof (hypotheses,
encodings and the marginal/sampling corollary), together with the cubic-phase analysis of §6, and not the
idea, which is obvious to experts.

---------------------------------------------------------------------------------------------------

## 2. Statements

Notation: ω = e^{iπ/4}, Z[ω] = Z[x]/(x⁴+1), √2 = ω − ω³ ∈ Z[ω]. The gate set 𝒢 is
{H, T, T†, S, S†, X, Z} ∪ {CNOT, CZ, CS, SWAP, CH}. Each gate is stored as (N, κ) with N having entries
in Z[ω] and true matrix N/√2^κ (κ = 1 for H and CH, 0 otherwise). A circuit C on n qubits has G
two-qubit and G₁ single-qubit gates. k(C) = Σκ ≤ G + G₁ is its √2-denominator exponent. Input length
is poly(n+G+G₁).

**Theorem Q1 (exact amplitudes; [A] route).** Assume [A] Lemma 8(i), Theorem A(b) and Theorem B. There
are an absolute constant c and one deterministic algorithm with the following behaviour. Given C as above
with G ≥ 2 and log(G₁+2) ≤ G^{0.9}, and given x, y ∈ {0,1}ⁿ, it outputs integers a₀,…,a₃, k with

  ⟨y|C|x⟩ = (a₀ + a₁ω + a₂ω² + a₃ω³)/√2^k,  k = k(C),

within 2^{c·G/√log G}·poly(n + G₁) operations. The connectivity is arbitrary.

**Theorem Q1′ (OpenAI route, polynomial space).** Assume [O] Theorem `thm:tensor-contraction`. Put
s := max{2·#internal wires, G, k(C), 2}. Then the same output is computed in
poly(n+G+G₁)·2^{O(s/√log s)} time and poly(n+G+G₁) space. In particular, if k(C) = O(G), for example
when the number of H gates is O(G), the time is 2^{O(G/√log G)} with polynomial space.

**Corollary Q2 (probabilities, marginals, sampling).** Under either assumption, the following can be
done for every S ⊆ [n] and y_S. The marginal p(y_S) = Σ_{y_{S̄}} |⟨y|C|x⟩|² can be computed exactly as
(r₀ + r₁√2)/2^{k} with r₀, r₁ ∈ ℤ in 2^{O(G/√log G)}·poly time (in Q1′, 2G and 2k replace G and k). One
sample from the *exact* output distribution of C|x⟩ can be drawn in expected n·2^{O(G/√log G)}·poly
time (Las Vegas, exact arithmetic in Z[√2]).

**Corollary Q3 (constant depth).** A depth-d circuit has G ≤ dn/2. Its amplitudes, marginals and
exact samples cost 2^{O(dn/√log n)}·poly(n), and the exponent is o(n) whenever d = o(√log n).

**Remark (other gate sets).** Any fixed finite gate set with entries in (1/D)·Z[θ], with θ an algebraic
integer of degree δ, works. Kronecker substitution uses f_θ, the monic minimal polynomial of θ, with
digits decoded from Q(2^b), deg Q ≤ (δ−1)g. Then reduce mod f_θ (Lemma 2(b) below; the coefficient bound
comes from ℓ¹ norms instead of unitarity). In Q1′, x ↦ V with ℓ = (δ−1)G + 1 and the coefficient bound
determining P₀. P₀ must still be O(s). For cyclotomic fields Lemma 3 (the Galois bound) still holds.

---------------------------------------------------------------------------------------------------

## 3. Proofs

### 3.1 Path sum on segments (Markov–Shi form)

Merge single-qubit gates: on every qubit line, multiply the run of one-qubit gates in front of a
two-qubit gate into that gate, Ĝ_i := U_i·(R_{q₁} ⊗ R_{q₂}). The trailing run after the last two-qubit
gate on a line is multiplied into that gate from the left. A line without two-qubit gates contributes the
scalar ⟨y_q|R_q|x_q⟩. Each Ĝ_i = N_i/√2^{κ_i} with N_i ∈ M₄(Z[ω]), and κ_i is the sum of the κ's
merged. The cost is poly(G₁) arithmetic on O(k)-bit coordinates.

A *segment* is a piece of a qubit line between two consecutive two-qubit gates. It carries one bit
σ_e. The first and last legs of every touched line are fixed to x_q and y_q. On the touched lines there
are s₀ ≤ 2G − n_t ≤ 2G segments (n_t = number of touched qubits). Inserting resolutions of the identity
gives

**Lemma 1.** ⟨y|C|x⟩ = (Π_{untouched q} ⟨y_q|R_q|x_q⟩) · √2^{−Σκ_i} · A, where
A := Σ_{σ∈{0,1}^{s₀}} Π_i N_i[σ_out(i), σ_in(i)] ∈ Z[ω]. [Computed: Q1.]

### 3.2 From Z[ω] to integers

[A]'s engine evaluates sums of products of **integers**. [O]'s engine works in (ℤ/2^{P₀})[V]/(V^ℓ).
Z[ω] embeds in neither as a ring (x⁴ = −1 has no solution mod 4, nor modulo V), so we do not look for a
ring embedding. We use a homomorphism to a quotient that is injective on a box.

**Lemma 2 (Kronecker).** Let b ≥ 2 and M_b := 2^{4b} + 1.
(a) x ↦ 2^b defines a ring homomorphism κ_b: Z[ω] → ℤ/M_b, because 2^{4b} ≡ −1. It is injective on
{a : |a_j| ≤ 2^{b−1} − 1}. Indeed |Σa_j2^{bj}| < 2^{4b−1} < M_b/2, and balanced base-2^b digits are
unique.
(b) Alternatively, let Q ∈ ℤ[x] have deg Q ≤ D and ‖Q‖_∞ ≤ 2^{b−1} − 1. Then Q is recovered from the
integer Q(2^b), and A = Q mod (x⁴+1).
(c) (Non-ring for [O].) x ↦ V defines a ring homomorphism ℤ[x] → (ℤ/2^{P₀})[V]/(V^ℓ). It is injective on
polynomials of degree < ℓ, modulo 2^{P₀} coefficientwise.

**Lemma 3 (Galois bound).** Let C be a Clifford+T(+CS, CH) circuit, and write ⟨y|C|x⟩ = A/√2^k with
A = Σa_jω^j. Then |a_j| ≤ 2^{k/2}.
*Proof.* Gal(Q(ω)/Q) = {σ_t : ω ↦ ω^t, t odd} is abelian and contains complex conjugation. So σ_t(U)
is unitary whenever U is: σ_t(U)σ_t(U)* = σ_t(UU*) = I. Applying σ_t entrywise to all gates gives a
unitary circuit σ_t(C). σ_t(√2) = ±√2, so |σ_t(A)| = 2^{k/2}|⟨y|σ_t(C)|x⟩| ≤ 2^{k/2}. Finally
a_j = ¼Σ_t σ_t(A)σ_t(ω)^{−j}. ∎ [Computed: Q6. All four embeddings are checked to satisfy |σ_t(A)|² ≤ 2^k
exactly in Z[√2].]

So **b := ⌈k/2⌉ + 2** suffices for Lemma 2(a), and **P₀ := ⌈k/2⌉ + 3** suffices for (c): the signed
range is |a_j| < 2^{P₀−1}. The same argument gives |r_j| ≤ 2^k for marginals, so b := k + 2 there.

### 3.3 The network of Definition 2 [A] and its parameters

Fix g and a balanced partition of the G merged gates into groups V₁,…,V_g with |V_a| ≤ ⌈G/g⌉. A
segment is *internal* to a if both its end gates lie in V_a. It is *crossing* between a ≠ b otherwise.

* Settings: S_a = {0,1}^{P_a}, the bits of the crossing segments at a. P_a ≤ 4|V_a| ≤ 4⌈G/g⌉, because
  every merged gate has 4 legs. *This bound is where bounded gate arity enters; it holds for every
  connectivity.*
* W_a(z_a) := Kron_b(Σ_{internal bits of a} Π_{i∈V_a} N_i[·] reduced mod x⁴+1) ∈ ℤ, with
  Kron_b(a) = Σ_j a_j 2^{bj}.
* Ψ_{ab}(z_a, z_b) := Π_{e crossing a–b} [z_a(e) = z_b(e)]. By Observation (b) of [A] it factors through
  c_{ab} := #(segments between a and b) bits.

**Proposition 4 (Definition 2 holds).** With P := 4⌈G/g⌉ + 1:

1. Condition (i) holds: Σ_b c_{ab} = P_a ≤ P.
2. U := Σ_{a≠b} c_{ab} = 2·#crossing ≤ 2s₀ ≤ 4G.
3. Condition (ii) holds with B := 3b + 2 + log₂‖ã_a‖₁. Here ‖ã_a‖₁ ≤ 2^{#internal(a)}·Π_{i∈V_a} 4·2^{κ_i/2}
   (Lemma 3 applied entrywise to each merged gate), so B = O(k + G).
4. Condition (iii) holds with τ = 2^{#internal(a)}·poly ≤ 2^{2⌈G/g⌉}·poly(G, k). The values f_{ab} are
   0/1. The tables are computable from the prepared data (merged gates, partition) in time 2^{O(G/g)} with
   poly(G, k) memory, which meets the polynomial state bound that `anthropic-api.md` §4.1 requires.
5. The value is Z = Σ_z Π_a W_a Π Ψ_{ab} ≡ Kron_b(A) (mod M_b) by Lemma 2(a), since κ_b is a ring
   homomorphism and reduction mod x⁴+1 inside a table commutes with it. Hence A = decode(Z mod M_b).

[Computed: Q2 checks the literal Definition-2 sum, the brute-force sum over crossing bits and variable
elimination against each other. Q3 checks the unreduced decode of Lemma 2(b). Q4 checks (i), U and B.]

### 3.4 Running time (Q1)

Take the pieces of Theorem B (ρ = 1/√2, α′ = ½) and the levels of Theorem A. As in
`exact-hc-theorem.md` §6.4, let ℓ be the largest level with K_ℓ³⁰ ≤ G. Then K := K_ℓ ∈
(G^{1/300}, G^{1/30}], g = 3K⁸ ≤ 3G^{8/30}, and e := e_ℓ ≤ c_e/√log G with c_e = 0.85·√(300(3x₀+6)).
Lemma 8(i) with Theorem A(b) costs 2^X, where (bound (6.2) there)

X ≤ 1 + max{g log K, e(U + gP/K + K²) + C₀K² log(K(L+B′)) + 2gP/K + log τ} + C₁ log(g(P+B)),
L = ⌈(U+gP/K)/K²⌉ = O(G), B′ = ⌈2gP/K⌉ + g²B = O(g²(G+k)).

Term by term, with gP ≤ 4G + 5g:

| term | bound |
|---|---|
| e·U | ≤ 4c_e·G/√log G |
| (e+2)·gP/K | ≤ 3(4G+5g)/G^{1/300} = O(G^{1−1/300}) |
| e·K² + C₀K² log(K(L+B′)) | O(G^{1/15}·log(G+k)) = O(G^{0.97}) when log(G₁+2) ≤ G^{0.9} |
| log τ | O(G/g + log(G+k)) = O(G^{1−8/300} + G^{0.9}) |
| g log K, C₁ log(g(P+B)) | O(G^{8/30} log G), O(log(G+k)) |

Every term except the first is o(G/√log G). The preparation (merging, partition, decoding Z mod M_b)
costs poly(n, G₁, k). For G < K₀³⁰, an absolute constant, Feynman's sum over ≤ 2G segment bits costs
O(1)·poly. Hence 2^{c·G/√log G}·poly(n+G₁). The engine needs no balancing beyond the partition, because
Lemma 8 searches the K^g groupings itself (`exact-hc-theorem.md` §6.2). ∎

*Why the condition log(G₁+2) ≤ G^{0.9}:* B grows with k ≤ G+G₁ and enters through K²·log B. If it
fails, the input is already of size ≥ 2^{G^{0.9}}, and brute force over 2G bits is quasi-polynomial in
the input.

### 3.5 OpenAI route (Q1′): hypothesis by hypothesis

[O] Theorem `thm:tensor-contraction` (`quantitative-reduction.tex` l.29–49) has the following hypotheses.

* **Bipartite, one-bit edges, ≤ Cs edges.** Gate vertices form one side. Every segment is subdivided by
  a binary equality tensor, as [O] does in its own CNF encoding (l.79–83), which puts those vertices on
  the other side. That gives 2s₀ ≤ 4G ≤ 4s edges. Fixed legs are absorbed into the gate tensor, and a
  gate with no free leg is an isolated vertex ("contributes its scalar entry", l.23).
* **Maximum degree ≤ ⌈s^{9/10}⌉.** The degree is ≤ 4.
* **Number of vertices ≤ poly(s).** It is ≤ G + 2G.
* **Entries in 𝓑_{P₀,ℓ} = (ℤ/2^{P₀})[V]/(V^ℓ), 1 ≤ P₀, ℓ ≤ Cs.** The entries are N_i[·] with x ↦ V,
  polynomials of degree ≤ 3, and 0/1 for the equality tensors. The contraction is P(V) := Σ_σ Π N_i(V),
  of degree ≤ 3G, so ℓ := 3G + 1 ≤ 4s causes no truncation. Reducing P mod V⁴+1 over ℤ/2^{P₀} gives
  A mod 2^{P₀} (Lemma 2(c)), and P₀ := ⌈k/2⌉ + 3 recovers A by Lemma 3. **This is the only place where
  k enters: P₀ ≤ Cs forces s ≥ k/(2C).** This is why Q1′ uses s = max{…, k}.
* **Entries computable in (s+𝓛)^b·2^{As^{0.9}} time and (s+𝓛)^b space.** Each entry is a table lookup
  in the merged gate, which is precomputed in poly time.

The conclusion is (s+𝓛)^{O(1)}2^{O(s/√log s)} time and (s+𝓛)^{O(1)} space, with 𝓛 = poly(G+G₁+k). ∎
[Computed: Q5. Brute force and variable elimination in the truncated ring agree, and the lift equals A.
The ablations ℓ = 4 and P₀ one bit short are both caught.]

*Comment.* [O] works modulo a power of 2, so its engine cannot produce the exact *integer* coordinates
when the denominator exponent k is much larger than the number of wires. [A]'s engine returns exact
integers and has no such restriction (B only enters polynomially). This is one concrete asymmetry
between the two engines.

### 3.6 Probabilities and marginals (Q2)

Take C and C̄, the copy with every entry conjugated: (a₀,a₁,a₂,a₃) ↦ (a₀,−a₃,−a₂,−a₁). Both copies get
input x. For q ∈ S the outputs of both copies are fixed to y_q. For q ∉ S the two output legs are one
shared *trace* bit. Then Σ_{y_{S̄}} A(y)·Ā(y) is the value of a gate network with 2G merged gates and at
most 2(2G − n_t) + n_t ≤ 4G segments, so U ≤ 8G and P = 4⌈2G/g⌉ + 1. Its denominator is 2^k. The
numerator lies in Z[√2], and Lemma 3 gives |r_j| ≤ 2^k, so b := k+2. Everything in §3.3–3.5 applies
with G ↦ 2G. [Computed: Q7. VE and the integer network both match the state vector, the result lies in
Z[√2], and for S = ∅ the value is exactly 1. Dropping the conjugation is caught.]

*Sampling.* Draw y₁, y₂, … sequentially from the conditional marginals p(y₁…y_j)/p(y₁…y_{j−1}). These
are 2n marginal computations. Compare the cumulative values (in Z[√2]/2^k) with a uniform u ∈ [0,1)
generated lazily bit by bit. Sign tests in Z[√2] are exact (compare r₀² with 2r₁²), and the expected
number of random bits is O(n). The result is an exact sample in expected n·2^{O(G/√log G)} time. ∎

---------------------------------------------------------------------------------------------------

## 4. Verification [Computed]

Scripts are in `research/scripts/`. They use exact integer and Z[ω] arithmetic only, are run with
`python3 -I`, and each prints PASS/FAIL.

| script | what | result |
|---|---|---|
| `qc_lib.py` | Z[ω] (ω⁴ = −1, √2 = ω−ω³, Galois σ_t), gate set, exact state vector, circuit→segment network with single-qubit merging, doubled network, Definition-2 integer network (Kronecker, VE tables), (ℤ/2^{P₀})[V]/(V^ℓ) ring | library |
| `qc_check.py [seed] [count]` | Q1–Q7 of §3 on random circuits n ∈ [2,6], G ∈ [1,20], G₁ ∈ [0,25], random gates from 𝒢, random x, y, random balanced or contiguous partitions g = 1..4; plus 20 IQP instances (H^n·Z/CZ/CCZ·H^n, CCZ compiled to 6 CNOT + 7 T/T† + H) checking ⟨0|C|0⟩ = gap(f)/2ⁿ; plus 4 ablations (b too small, ℓ = 4, P₀ one bit short, no conjugation) that must be caught | seed 1, 150 circuits: **PASS**; seed 2, 150: **PASS**; all 4 ablations caught |
| `qc_cubic_gap.py [seed] [count]` | §6: exact expansion, 2-adic truncation at n+1 marks, valuation bound, failure of shorter truncation, failure of the CNF "kill heavy assignments" mechanism | seeds 1 (120), 3 (400): **PASS** |

Run statistics for seed 1 (150 circuits):

* 529 networks were evaluated by brute force over crossing bits, and 418 by the literal Definition-2
  sum.
* The largest instance had 23 crossing segments (variable elimination only); 48 partitions with a node
  over 14 boundary bits were skipped.
* 65 truncated-ring brute forces were run, and 91 marginals checked.

The brute-force/VE/state-vector agreement is exact (equality of integers), not numerical.

---------------------------------------------------------------------------------------------------

## 5. Implications

### 5.1 Against the classical state of the art (exact strong simulation, arbitrary connectivity)

| method | time for G two-qubit gates on n qubits, depth d | space | source |
|---|---|---|---|
| Schrödinger (state vector) | 2ⁿ·poly | 2ⁿ | folklore |
| Feynman path sum | 2^{O(G)} (≤ 4^G) | poly | folklore |
| Aaronson–Chen recursive | d^{O(n)} (m^{O(n)}) | poly | [Lit] arXiv 1612.05903 |
| tensor contraction | 2^{O(tw)}, tw of the line graph; Θ(n) for constant depth on expanders | 2^{O(tw)} | [Lit] Markov–Shi |
| geometrically local, D ≥ 2 | subexponential in G | | [Lit] Wahl–Strelchuk 2023 |
| **Q1 ([A] route)** | **2^{O(G/√log G)}**, i.e. 2^{O(dn/√log n)} | 2^{O(G/√log G)} as stated | here, conditional |
| **Q1′ ([O] route)** | **2^{O(G/√log G)}** when k = O(G) | **poly** | here, conditional |

For constant d on arbitrary connectivity no subexponential exact method was known (to our knowledge),
and tw = Θ(n) defeats tensor contraction. Q1/Q1′ is the first 2^{o(n)} bound for this class, and
conditionally the first polynomial-space bound below Aaronson–Chen's d^{O(n)} for d < 2^{c√log n}.

**Tightness (the reverse reduction) [Mine, standard; not scripted].** Take a 3-CNF with m = O(n) clauses
and bounded occurrences (Tovey copying). Add one ancilla y_j per clause and let c_j(x) ∈ {0,1} say that
clause j is satisfied. Then Σ_{x,y}(−1)^{Σ_j y_j(1+c_j(x))} = Σ_xΠ_j 2[c_j(x) = 1] = 2^m·#SAT. This is
⟨0|H^{⊗(n+m)} D H^{⊗(n+m)}|0⟩·2^{n+m}, with D = Π_j(−1)^{y_j(1+c_j(x))}. Each factor is a 4-qubit diagonal
gate, exactly synthesisable from O(1) Clifford+T one- and two-qubit gates with one ancilla. Bounded
occurrence lets the factors be coloured into O(1) layers. So C has constant depth and O(n) gates, and
⟨0|C|0⟩ determines #SAT exactly. (`qc_check.py` checks the analogous identity ⟨0|C|0⟩ = gap(f)/2ⁿ for
IQP circuits with a compiled CCZ.) So the
amplitude problem for constant-depth, O(n)-gate Clifford+T circuits is #3-SAT-hard at linear size, and
any 2^{o(n/√log n)} algorithm for it would improve the refutations' own rate. Before 2026, ETH gave a
2^{Ω(n)} lower bound for this class (the premise of Morimae–Tamaki Thm 6 and Dalzell et al. Thm 2).
Assuming the refutations, the truth is 2^{n/(log n)^{1/2±o(1)}}-ish, at least for these methods.

### 5.2 Which fine-grained supremacy conjectures fall

"Refuted" means refuted assuming the ETH refutations are correct.

| statement (source) | hypothesis / object | status |
|---|---|---|
| Morimae–Tamaki, *Fine-grained quantum computational supremacy* (arXiv 1901.01637), **Conjecture 7**: deciding gap(f) ≠ 0 for a 3-CNF with m clauses needs 2^{Ω(m)} nondeterministic time | 3-CNF, parameter m | **Refuted directly**: gap = 2ⁿ − 2·#SAT, and #SAT with m clauses takes deterministic 2^{O(m/√log m)} [A, Thm 1]. Their **Thm 7** (Clifford+T sampling with multiplicative error is not in 2^{o(t)}) loses its only premise. The hard family in its proof has G = O(t) gates and is sampled exactly in 2^{O(t/√log t)} by Q2. The theorem as stated ("there exist circuits with t T-gates", any Clifford count) is not refuted (see the T-count row). |
| same paper, **Thm 6** (ETH ⇒ no 2^{o(t)} strong simulation of Clifford+T); also Huang–Newman–Szegedy's ETH/SETH-type amplitude bounds (arXiv 1804.10368: SETH ⇒ 2^{n−o(n)} for poly-size circuits) | ETH, SETH | **Premise refuted.** The conclusion is refuted for every hard family with G = O(n) gates (Q1). For the poly-size families of HNS it is not touched (G/√log G ≥ n). HNS's *unconditional* bound for monotone simulators is unaffected. |
| same paper, Conjectures 4–6 (2^{(1−a)n} for gap of poly-size / log-depth / reversible circuits) | general circuits, parameter n | **Survive.** Size s = poly(n) gives 2^{O(s/√log s)} ≫ 2ⁿ. |
| Morimae–Tamaki, *Depth-scaling fine-grained supremacy based on SETH* (arXiv 1902.08382v1), Conjectures 1–2: CNF with ≤ cn clauses (any width) needs 2^{(1−a)n} | sparse CNF of unbounded width | **Refuted via Calabro–Impagliazzo–Paturi (CCC 2006).** The width and density exponents converge to the same limit (their Thms 13–14), and ETH false ⇒ s_k = 0 for all k. So the density exponents vanish. This is the *decision* version. For Conj. 2 (gap, nondeterministic) we did not check whether the duality holds for counting. The depth-scaling theorems lose their premise. Their hard circuits have O(nm) gates, so Q1 does not refute the conclusions. |
| Dalzell–Harrow–Koh–La Placa, *How many qubits are needed for quantum computational supremacy?* (Quantum 4, 264, 2020), **poly3-NSETH(a)** | general degree-3 F₂ polynomials, up to (n³+5n)/6 terms | **Survives.** Neither engine is clause-count-free for ±1 phases (§6). The best we can do is 2^{O(n log(m/n)/√log n)}, useless for m = Θ(n³). **Their Thm 2** (ETH ⇒ 2^{an} for poly3-NONBALANCED) loses its premise. Their numbers (208 IQP qubits *with 500 gates*, linear-in-gates runtime) extrapolate a sparse family. Asymptotically, families with O(n) gates are 2^{O(n/√log n)} (Q1), and with m ≤ n·2^{o(√log n)} terms 2^{o(n)} (§6). Quantitatively irrelevant at n = 208. |
| DHKL **per-int-NSETH(b)** (BosonSampling, 98 photons) | permanents | **Survives** (§5.3). |
| Morimae–Tamaki, *Additive-error fine-grained quantum supremacy* (Quantum 4, 329, 2020): Conj. 1 (average-case dense cubic, with NTIME[n²] oracle); Conj. 2 (dense quadratic + log-depth circuit); Conj. 3 (dense quadratic + 3-CNF with m clauses, 2^{am}) | dense quadratic/cubic phases | **Survive as far as we can tell.** A dense quadratic phase alone is Clifford and easy, but combined with a CNF the circuit has Θ(n²) gates. Our 2-adic route costs O(n log n) wires. Not refuted, not shown safe. |
| Aaronson–Chen (arXiv 1612.05903) QUATH / HOG | average-case, *approximate*, poly-time | **Unaffected.** These are not exact amplitudes or 2^{o(n)} statements. Their d^{O(n)} poly-space simulator is improved asymptotically (Q1′). |
| Buhrman–Patro–Speelman QSETH (arXiv 1911.05686) | quantum k-SAT / CNF-SAT | k-CNF form: refuted, because a classical 2^{o(n)} k-SAT algorithm is a quantum one. Forms for general formulas/circuits: not checked. |
| T-count-parameterised strong simulation (2^{o(t)} for t T-gates and arbitrarily many Cliffords) | dense cubic Z₈-phase sums on t variables (magic-state injection) | **Open.** The 2^{o(t)} lower bound is unsupported (its premise was ETH), but our tools give nothing below 2^{O(t log t/√log t)}. The stabilizer-rank state of the art, about 2^{0.4t} [Lit, recalled], stands. |

**Sampling vs exact amplitudes, precisely.**

1. Q2 *does* give classical **exact sampling** (zero error) in n·2^{O(G/√log G)}. So any hardness claim
   for sampling, even with multiplicative or additive error, stated as 2^{Ω(n)} for circuit families with
   O(n) gates, or O(n·(log n)^{1/2−ε}) gates, is refuted conditionally.
2. Q2 says **nothing** about families with G ≥ n√log n gates, which includes every random-circuit
   sampling experiment at depth d ≫ √log n. Constants aside, those claims rest on PH non-collapse plus
   average-case approximate-amplitude conjectures (QUATH, XEB-type), which the refutations do not touch.
3. For d = O(1) on arbitrary connectivity, the refutations imply a classical *exact* sampler in
   2^{O(n/√log n)}. Every quantum-advantage argument for constant-depth circuits must therefore be at most
   "quasi-exponential" in n. Approximate-sampling arguments that are already polynomial (for example
   2D constant-depth, Bravyi–Gosset–König-type relation problems, or unconditional shallow-circuit
   separations) are not affected.

### 5.3 BosonSampling: why it is not covered

BosonSampling amplitudes are permanents of n×n submatrices of an m×n Haar-random unitary: **dense**
complex permanents. The team's permanent work (`permanent/permanent-attack.md` §9, `permanent/barrier.md`)
found three things:

* no network for the dense permanent with U = o(n log n);
* a proof that row-local networks need U ≥ n·log(n/s), so the engine's guarantee is
  ≥ 2^{(½−o(1))n√log n} > 2ⁿ (Thm 6.1/Cor. 6.3 there);
* only bounded-degree (sparse) matrices go through, in 2^{O(n log Δ/√log n)}.

Viewed as a circuit, the interferometer has Θ(m²) beam splitters on wires with n+1 occupation values,
so U = Θ(m² log n) (DHKL use 2n²+n elements). Both views put BosonSampling, and hence per-int-NSETH,
outside the corollary. Ryser's 2ⁿ remains the classical state of the art for exact BosonSampling
amplitudes. The contrast is structural. Qubit circuits are sums over *binary* variables with bounded-arity
local constraints, about O(G) bits. Permanents of dense matrices are sums over *permutations*, which need
log n bits per row in any local encoding.

---------------------------------------------------------------------------------------------------

## 6. Cubic phases: does [A]'s clause-count-free bound apply? (the team's belief, tested)

Let f = Σ_{t∈T} m_t over F₂ (deg ≤ 3, |T| = m terms, n variables) and gap(f) = Σ_x (−1)^{f(x)}. This is
DHKL's poly3 object; ⟨0|H^n D_f H^n|0⟩ = gap/2ⁿ.

**[A]'s mechanism (App. D, paper.txt l.2114–2131).** For a CNF, [V(ξ)=∅] = Σ_{Π⊆V(ξ)} (−1)^{|Π|}, and
inclusion–exclusion is truncated at n̄ ≈ n/log Δ marks. Assignments with |V(ξ)| > n̄ contribute **0** to
#SAT, so O(n) sparse parity checks can kill them. That leaves n̄ marks at log Δ bits each, O(n) bits in
all, independent of m.

**For phases this breaks.** (−1)^{f(x)} = Π_t (1 − 2m_t(x)) = Σ_{Π⊆V(x)} (−2)^{|Π|} = (−1)^{|V(x)|}. Every
assignment contributes ±1, so there is no set of "bad" assignments with zero contribution to kill. The x
with |V(x)| > n̄ carry a nonzero total in general [Computed: C4]. So **the belief is correct**: the
m-independent bound does not transfer.

**What does transfer (Proposition C) [Mine; identity Computed, engine application a sketch].**
(a) gap(f) = Σ_{S⊆T} (−2)^{|S|}·2^{n−|V(S)|} exactly, where V(S) is the set of variables covered by S.
(b) Every term with |S| ≥ n+2 is divisible by 2^{n+2}, and |gap| ≤ 2ⁿ. So
gap(f) ≡ Σ_{|S|≤n+1} (−2)^{|S|}2^{n−|V(S)|} (mod 2^{n+2}) determines gap(f). The truncation at n+1 marks
is sharp up to constants, since truncating at ⌊n/2⌋ fails [Computed: C1–C3].
(c) Plug (b) into [O]'s incidence encoding (`lem:tensor-sparse-query`). Each monomial is a "test" with
factor 1 − 2∏_{v∈t} z_{t,v}. Use precision 2^{n+2} and ℓ = 1, an incidence degree bound K = 3(n+1)
instead of [O]'s idempotent lift, and branching on variables in > (3m/n)√log n monomials. Then the wire
count is M = O(n·log(em/n) + √n·log n). This gives

  gap(f) in 2^{O(n·log(em/n)/√log n)}·poly(m) time (conditional on [O]).

This is **2^{o(n)} iff log(m/n) = o(√log n)**, i.e. m ≤ n·2^{o(√log n)} terms. That is strictly more than
Q1 gives (Q1 needs m = o(n√log n), since G = Θ(m)). For dense f (m = Θ(n³)) it gives 2^{O(n√log n)}, worse
than brute force. The 2-adic truncation costs n+1 marks at log(m/n) bits each, where [A] pays n/log Δ
marks; that is the whole difference. We know of no way to make cubic phases m-independent. Doing so would
give dense poly3-NONBALANCED in 2^{o(n)} and refute poly3-NSETH(a), so we flag it as a target, not a
result. The application in (c) was not checked line by line against [O]'s degree and entry hypotheses
(the max degree is n^{3/4}·2^{o(√log n)} ≤ s^{9/10}, and the entries are products of 1 and −2, so we expect
no obstacle).

---------------------------------------------------------------------------------------------------

## 7. Limitations (honest list)

1. **Conditional.** Everything rests on [A] Lemma 8(i) + Theorems A(b), B, or on [O]'s appendix theorem
   (not formalised). If those fail, Q1/Q1′ fall with them. No independent route is offered.
2. **Galactic constants.** With [A]'s constants (c_e = 0.85·√(300·60) ≈ 114, `exact-hc-theorem.md`
   §6.4), the leading term e·U ≤ 4c_eG/√log G with G = dn/2 beats Schrödinger only when
   2c_e·d < √log₂ n, i.e. **log₂ n > 5.2·10⁴·d²**. This ignores all lower-order terms and G ≥ K₀³⁰ =
   2^{540}. [O] gives no explicit constants. The theorem says nothing about 50–1000-qubit experiments.
3. **Exact amplitudes vs sampling.** The theorem is about exact strong simulation. Its sampling
   consequence (Q2) is real but only for G = o(n√log n). Approximate/average-case hardness (RCS, XEB,
   QUATH) is untouched.
4. **Gate-count, not qubit-count.** The parameter is G. Circuits with G ≥ n√log n, which includes
   polynomial depth, gain nothing over 2ⁿ. The SETH-based 2^{n−o(n)} lower bound for poly-size circuits
   loses its premise, but its conclusion is not contradicted.
5. **Denominators in [O]'s route.** [O]'s 2-adic precision cap P₀ ≤ Cs forces k = O(s). Circuits with
   very many Hadamards per two-qubit gate need [A]'s route (exact integers) or s ≥ k.
6. **Verification scale.** The checks cover n ≤ 6 and G ≤ 20 and test the reductions (encodings,
   decodings, Definition-2 parameters, ring emulation), not the engines. The engines were treated as black
   boxes and replaced by brute force and variable elimination.
7. **Literature status.** The statuses of Morimae–Tamaki 1902 Conj. 2 (counting/gap version of the
   duality), the QSETH variants, and the stabilizer-rank constant 0.396 are from memory or abstracts, not
   re-derived; they are marked as such in §5.2.

Sources (web, accessed 29 Oct 2026): The Quantum Insider (27 Oct 2026); Quantum Zeitgeist substack
"The OpenAI Exponential Time Hypothesis Claim and What It Means for Quantum Computing"; Hacker News item
50251661; arXiv 1805.05224 (DHKL), 1901.01637, 1902.08382v1, 1912.06336 (Morimae–Tamaki), 1804.10368
(Huang–Newman–Szegedy), 1612.05903 (Aaronson–Chen), 2208.01498 (Wahl–Strelchuk), 1911.05686 (QSETH);
Calabro–Impagliazzo–Paturi CCC 2006 (duality). PDFs of the Morimae–Tamaki, Aaronson–Chen and CIP papers
were read as text in `scratchpad/qc_lit/` (not run).
