# The iterated product on the counting engine: constructions tried, lower bounds proved, the open question

Status: working notes, 4 Nov 2026. §0 is the verdict (written last); §§1–6 are the analysis, appended as
they were obtained. Lean: lean/EthFollowup/Scratch/IterProd/*.lean.


## 0. Verdict

**Neither a construction nor a general lower bound; the question is pinned down and shown to be hard in
both directions, with the natural special case proved.**

1. **No construction.** Every "flatten the tree" idea (Kronecker packing, one-shot DFT/pointwise products,
   CRT, discrete logs, exponent-vector witnesses, direct primality certificates) is quantified in §4 and
   costs ≥ Θ(nk) = Θ(n²/log n) or Θ(n log n) cut; none reaches o(n √log n). The best verifier remains the
   product tree at (1/5 + o(1)) n log₂ n (levels above the node size), i.e. prime finding stays at
   2^{Θ(n √log n)} by the counting route; the barrier of prime-finding.md §4 stands unchanged.
2. **Lower bound, proved (Lean, sorry-free):** in the tree model (any binary tree of pairwise
   multiplications, any shape, any factor sizes) U ≥ cost(T) ≥ Σ_i ℓ_i log₂(n/ℓ_i), and = n log₂ k for
   equal sizes (`cost_ge_entropy`, `cost_ge_equal`, IterProd/TreeBound.lean). So unbalanced trees cannot
   help. Also proved: the cut rank of the product indicator is exactly 2^{bits(S)} across a factor/label
   cut (`rank_prodMat_pow`) and ≤ τ(m) when m is hard-wired (`rank_prodMatFixed_le`, IterProd/CutRank.lean).
3. **Lower bound, general: provably out of reach.** The engine simulates any Boolean circuit of size
   ≤ Kn with U = O(size) (§5), so U = ω(n) for all parsimonious verifiers of "m = Π d_i" would be a
   superlinear circuit lower bound for an explicit TC⁰ function — open since the 1970s. The cut-rank
   method is additionally capped at 2n for clusters without auxiliary labels (§2.3).
4. **Sharpest open question (§6):** the unambiguous g-party number-in-hand communication complexity of
   verifying m = Π d_i with n^{4/5}-bit parties: between Ω(n) and (1/5) n log n; U = o(n √log n) would give
   exact π(x) and prime finding in x^{o(1)}.
5. **Side result (idea 5, modular weights):** μ ≡ Σ_{j=1}^{a} (−1)^{j+1} C(a,j) τ_{jq−1} (mod q^a) on
   squarefree d (finite differences; Lean-checked on instances, ModCheck.lean): fold aq − 1 instead of
   q^a − 1 for the squarefree chain mod q^a. For isolating ω = 1 the learnable exponent is at most a − 1
   and grows only with log_q(fold) (§4.5(b), brute force). Constant-factor gains in the fold only; the
   cut Θ(n log fold) at M ≥ x^{0.525} is unchanged.

## 1. The exact object

Engine model (factoring-note §2): g = 3K⁸ nodes, each holding ≤ P ≤ n/K⁷ bits of labels (P ≈ n^{4/5} at
K = n^{1/40}), each label shared by two nodes, node tables poly-time (even 2^{O(P)}-time is harmless),
U = Σ shared bits, cost 2^{Θ(U/√log n)}. A *parsimonious verifier of the k-fold product* is a label
system whose labels contain the witness (d_1,…,d_k, m) (Σ bits(d_i) = bits(m) = n, m is a *label*, not a
constant: the engine sums over m ∈ I) plus auxiliary labels, with exactly one accepted labelling per
witness with Π d_i = m and none otherwise. Then Z = Σ_{m∈I} τ_k(m) (or any cheap-weight variant, e.g.
Theorem B′ of prime-finding.md with τ_k, k ≈ n/log n, or the chain weights W_k). Target: U = o(n√log n).

Known: the product tree. Level ℓ has k/2^ℓ partial products of 2^ℓ·(n/k) bits; each multiplication of
sizes (a,b) costs cut Θ(a+b) with the 2D Schönhage–Strassen network (Factoring/MulNet*, ModP/ArithNet*);
total U = Σ_ℓ Θ(n) = Θ(n log k). Levels below the node size P can be absorbed into single nodes
(a node reads P/log n factors and emits their product): this removes log(P/log n) levels and leaves
log(n/P) = (1/5)log n levels, so U = Θ(n log n) still (prime-finding.md §4).

The two questions: (1) a network with U = o(n√log n); (2) a theorem U = Ω(n log k) (or Ω(n√log n)) for
every parsimonious verifier.

## 2. What the cut-rank method can and cannot certify

Cut lemma (Barriers/RankBounds.lean, `rank_le_two_pow_of_eq_sum_mul`): for any set L of nodes with w(L)
crossing bits, the matrix M_L[inside labels of L, labels outside L] := #accepted completions has rank
≤ 2^{w(L)}. Model R (`modelR_bound`, `sum_crossing_le_total`): for a *partition* of the nodes into
clusters V_j, U ≥ Σ_j w(V_j) ≥ Σ_j log₂ rank M_{V_j}.

2.1 Rank of the product indicator across one cut (Lean: IterProd/CutRank.lean, see §2.4).
 (a) m a label, factors split S | S^c, m on the S^c side: M[u, (v, m)] = [u·v = m], rows indexed by the
     products u of the S-side factors. Distinct rows have disjoint supports (v, m determine u), so
     rank = #{u ≠ 0 realised} = 2^{bits(S)} up to the multiplicity of representations: w ≥ bits(S).
 (b) m hard-wired (fixed): M[u, v] = [uv = m] has rank = #{u | m realised on both sides} ≤ τ(m) ≤
     2^{(1+o(1)) n/log₂ n}. So with m fixed, *no* single cut can be forced above n/log n, and a
     non-uniform network that knows the divisors of m can realise this (send the index of u among the
     divisors). The lower-bound question is therefore only meaningful with m as a label (the counting
     application has m as a label anyway).
 (c) A cut separating the bits m_{[a,b)} of m from everything else has rank 2^{b−a}: w ≥ b − a.

2.2 What Model R certifies for the product tree. Take the clusters to be the multiplication networks at
the internal tree nodes (inside: the FFT/transform labels; crossing: the two inputs and the output).
The inside labels of the node v are a function of its inputs (u, u′), and distinct (u,u′) have disjoint
supports (the outside labels include the factors, which determine u, u′), so rank M_v = #{(u,u′)
realised} ≈ 2^{size(u)+size(u′)}, i.e. log rank M_v ≈ 2·size(v). Summing, Σ_v log rank M_v = 2·Σ_v
size(v) = 2·Σ_i bits(d_i)·depth(i) = Θ(n log k). So the cut-rank bound is tight for the tree: the log k
is genuinely in the rank structure of the tree, not an artefact of the FFT.

2.3 The cap. In Model R the rows of M_{V_j} are indexed by the labels inside V_j. For clusters that
contain *no auxiliary labels* (only witness bits), rank M_{V_j} ≤ 2^{witness bits inside V_j}, so
Σ_j log rank M_{V_j} ≤ total witness bits = 2n. Hence any Ω(n log k) proof must exploit auxiliary
labels: it must show that every parsimonious verifier has a node partition whose clusters carry
auxiliary labels that are "determined by" Θ(n log k) witness bits in total. That is a statement about
all possible intermediate representations of the computation, i.e. a genuine local-proof-length lower
bound for iterated multiplication (see §5). The clean, provable special case is the tree model (§3).

## 3. Theorem (tree verifiers): unbalanced product trees cannot beat n log k  — Lean-proved (general)

Tree model. A *tree verifier* multiplies the factors along a binary tree T with leaf sizes ℓ_i (bits),
L = Σ ℓ_i = n, each internal node v running any multiplication network for its two children. By §2.1(a)
(Lean: `rank_prodMat_pow`) the cut separating the subtree of v from the rest has rank 2^{wt(v)} (wt(v) =
Σ of the leaf sizes below v), so it carries ≥ wt(v) bits; the subtrees of the internal nodes at one depth
are disjoint, and the cuts at different depths are nested, so U ≥ Σ_v wt(v) =: cost(T) = Σ_i ℓ_i depth(i)
(each level's partial products are the labels between the level's networks; the SS network achieves
cost(T)·O(1)).

Theorem (IterProd/TreeBound.lean, `cost_ge_entropy`, no sorry, axioms propext/Classical.choice/Quot.sound):
  for every binary tree with positive leaf weights, cost(T) ≥ Σ_i ℓ_i log₂(L/ℓ_i) = L·H(ℓ/L).
Proof: induction; at the root with child weights A + B = L, the increment is L − A log₂(L/A) − B log₂(L/B)
= L(1 − h(A/L)) ≥ 0 by `Real.binEntropy_le_log_two`.
Corollary (`cost_ge_equal`): k factors of w bits each: cost(T) ≥ k·w·log₂ k = n log₂ k, for *every* shape.
Consequences:
* Idea 1 of the brief (unbalanced trees, varying factor sizes) is dead: the bound is the entropy of the
  size distribution, which is n log k whenever the factors have comparable sizes. For the k-fold divisor
  count τ_k on n-bit m the factors are *all* sizes (the engine sums over all tuples), but the heavy
  tuples (those with many factors of ≈ n/k bits) must be verified too, and the tree is fixed before the
  tuple is read, so cost(T) ≥ n log₂ k − O(n) is forced for the tuples with equal sizes.
* The bound is tight for trees (balanced tree, SS networks: Θ(n log k)), so any improvement must come
  from a verifier that is not a tree of pairwise multiplications: no level of the computation may hold
  the n bits of partial products as labels.

## 4. Constructions tested (each with its quantified cut)

Notation: k factors of w = n/k bits (w ≈ log n for τ_k, k ≈ n/log n), node load P ≈ n^{4/5}.

4.1 Unbalanced trees. Dead by §3: U ≥ Σ_i ℓ_i log₂(n/ℓ_i), which is n log₂ k for comparable sizes. A
   tree whose shape adapts to the sizes (Huffman) only helps when the size distribution has low entropy,
   which the heavy tuples of τ_k do not.

4.2 Kronecker packing (many small multiplications in one FFT). Level ℓ of the tree is k/2^ℓ products of
   2^ℓ w-bit numbers; packing them as coefficients of two polynomials and doing one convolution computes
   all cross products, including the k/2^{ℓ+1} wanted ones, at cut Θ(total size) = Θ(n). But the level
   already costs Θ(n) with k/2^ℓ separate SS networks: the per-level cost is linear in the data and cannot
   be improved; the log k is the *number of levels*, not per-level inefficiency. Packing several levels
   into one node removes only the levels below P (prime-finding.md §4): the remaining log(n/P) = (1/5)log n
   levels have ≤ n^{1/5} numbers of ≥ P bits, and merging two of them is the 4-fold product of P-bit
   numbers with cut o(8P) — the same problem one scale down. Cut Θ(n log(n/P)) = Θ(n log n). No gain.

4.3 Rings where k-fold products are cheap (DFT / pointwise / CRT / discrete logs).
   (a) Evaluation–pointwise–interpolation: choose N ≈ n/b points in a ring R of b′ ≈ 2b + log N bits;
   the pointwise k-fold product at one point is a chain of k multiplications of b′-bit elements (sizes do
   not grow in R), cut Θ(k b′) per point, Θ(N k b′) = Θ(n k) in all; and each factor must be evaluated at
   all N points (N b′ ≈ n bits of evaluations per factor, Θ(nk) in all). Cut Θ(nk) = Θ(n²/log n) ≫ n log k.
   The one-shot DFT trades log k levels for a factor k of redundancy: each small factor becomes an
   n-bit evaluation vector.
   (b) CRT: Π d_i ≡ m (mod q_j) for n/log n primes q_j of log n bits needs d_i mod q_j for all (i,j):
   k · n/log n residues of log n bits = n²/log n label bits. Same redundancy, same cut.
   (c) Discrete logs turn the product into a k-fold *sum*, and sum trees are cheap (partial sums of k
   numbers of b bits have b + log k bits: total Σ_ℓ (k/2^ℓ)(b + ℓ) = O(kb) = O(n) — sizes do not add up
   for sums). But the logs are per modulus q_j and all n/log n moduli are needed: again n²/log n.
   (d) Integer polynomial product then carries (the SS idea applied once to all k factors): the
   coefficients of D(x) = Π d_i(x) are not small: D(1) = Π d_i(1) can be ≈ 2^{n+k}, so the coefficient
   ring must have ≈ n bits per coefficient — n/b coefficients of n bits = n²/b. The product tree's
   interleaving of carries with multiplications is what keeps every level at n bits.
   Verdict: every "flatten the tree" method replaces log k levels by a redundancy factor ≥ k/log k.

4.4 Exponent-vector witness. m = Π p_j^{e_j}: verifying it is the iterated product again (tree:
   n log ω(m); divisibility chain m_{j} = m_{j−1}/p_j^{e_j}: ω(m) multiplications of size ≤ n, up to
   n²/log n). The witness representation is irrelevant; only the verification matters. Certifying
   primality directly instead of counting (Pratt/AKS/Fermat-type certificates) needs modular
   exponentiations, i.e. chains of n squarings of n-bit numbers at fixed size: cut Θ(n²) per
   exponentiation — the geometric-width saving of ArithL (sizes halving along the chain) is unavailable
   because everything is reduced mod the n-bit modulus. So τ_k-counting at Θ(n log n) is the cheapest
   known prime isolator by a factor n/log n.

## 5. Why a general lower bound is out of reach: the engine simulates circuits

Observation (simulation). Let C be a Boolean circuit of size s (fan-in 2) computing the predicate
[Π d_i = m] on the 2n witness bits. Make every wire a 1-bit label and every gate a node checking its
gate equation (fan-out handled by copy nodes); given (d, m) the gate values are determined, so the label
system is parsimonious with U = O(s) and load O(1). Group the gates into g groups of ≤ P/3 gates: group
nodes have load ≤ P (the boundary wires), internal wires are no longer labels, and U ≤ O(s) still. The
engine needs g ≤ 3K⁸ ≈ n^{1/5} groups, i.e. s ≤ 3K⁸·P/3 = O(Kn) = O(n^{1+1/40}). Hence

   U_engine(Π_k) ≤ O(min{ size(C) : C computes [Π d_i = m] }) whenever that size is ≤ Kn.

Consequence. Any lower bound U = ω(n) for all parsimonious verifiers of the k-fold product (k ≈ n/log n)
implies a superlinear lower bound on the Boolean circuit size of the explicit, polynomial-time (indeed
TC⁰, Hesse–Allender–Barrington) predicate "m = Π d_i". No superlinear circuit lower bound is known for
any explicit function (the record for general circuits is ≈ 3n). So question (2) in its general form is
at least as hard as the oldest open problem in circuit complexity; Ω(n log k) or Ω(n√log n) for *all*
parsimonious networks is not provable with current tools, and the cut-rank method is capped as in §2.3.
Restricted models are the only place for theorems; the tree model (§3) is the natural one and is tight.

The converse direction fails: an engine construction need not be a small circuit (nodes compute
arbitrary functions of P bits; the SS network has U = O(n) while the best circuits for one n-bit
multiplication have size Θ(n log n)). So question (1) is genuinely different from circuit size: it asks
for the unambiguous g-party number-in-hand communication complexity of verifying m = Π d_i with the 2n
witness bits split among g ≈ n^{1/5} parties of n^{4/5} bits (any split chosen by the designer). Upper
bound n·log(n/P) = (1/5) n log₂ n (tree over parties, §1); lower bound Ω(n) (any single cut, §2.1(a));
nothing in between is known. For the additive analogue Σ d_i = m the answer is Θ(n) (sum tree: partial
sums of b-bit numbers have b + log k bits, sizes do not add). The gap is exactly the question of
whether products can be verified without an intermediate representation of full entropy at every scale.

4.5 The parity trick at higher moduli (idea 5). Available weights on squarefree d are exactly the pure
   exponentials t^{ω(d)} (τ_t, products of τ's, ordered/coprime/divisibility-constrained factorisations
   all give t^ω for some slot count t), so the question is which sequences ω ↦ b_ω (mod N) lie in the
   Z-span of {t^ω : 1 ≤ t ≤ T} ("fold T"), for ω ∈ [0, Ω] with Ω ≈ n/log n ≫ N.
   (a) The squarefree chain needs (−1)^ω mod q^a (Möbius inversion mod q^a forces g ≡ μ exactly).
   Lemma A′ used t = q^a − 1. Finite differences do better: (jq − 1)^ω ≡ p_ω(j) (mod q^a) with p_ω a
   polynomial of degree < a in j and p_ω(0) = (−1)^ω, so
       (−1)^ω ≡ Σ_{j=1}^{a} (−1)^{j+1} C(a,j) (jq − 1)^ω  (mod q^a):  fold aq − 1 instead of q^a − 1.
   Lean: IterProd/ModCheck.lean, #eval all true for (q,a) ∈ {(3,2),(3,3),(3,4),(5,2),(5,3),(2,3),(7,2)},
   ω < 24. Brute force (Smith normal form over Z, scratchpad iterprod/span2.py) gives the *minimal*
   fold with (−1)^ω in the span: N = 9:5, 27:8, 81:8(!), 25:9, 49:13 (= aq − 1 for odd q, a ≤ 3; 81 does
   better), and for q = 2: N = 4:3, 8:3, 16:5, 32:7, 64:7. So μ mod q^a costs fold O(aq), i.e. the chain
   W for [sqf] mod q^a has cut O(n log(aq)).
   (b) Isolating ω = 1 mod q^a. Every f(ω) = Σ_t a_t t^ω vanishing mod q^a on 2 ≤ ω ≤ Ω has f(1) ≡ 0
   (mod q): the terms with q ∤ t are periodic in ω with period | φ(q^a) and vanish on a full period
   inside [a, Ω], hence identically; the terms with q | t have q | f(1). So one never learns π mod q^a
   from a mod-q^a identity, only π mod q^{a−v}, v = v_q(f(1)) ≥ 1 (Theorem B′ is the case v = a − 1,
   fold q). The learned exponent e = a − v as a function of the fold T (brute force):
     q = 3: N = 27: fold 3 → e = 1, fold 6 → 2 (= a − 1); N = 81: folds 6..18 → e = 2 only;
     q = 5: N = 125: fold 5 → 1, fold 10 → 2;   q = 2: N = 32: fold 2 → 1, fold 4 → 3.
   The obstruction to e = a − 1 with fold < q² is Fermat periodicity: with only t = q·s, f(ω) = q^ω c(ω)
   and c(ω) ≡ c(ω + (q−1)) (mod q), so ω = 1 and ω = q cannot be separated once a > q.

## 6. The sharpest open question, and what would settle it

Q (g-party unambiguous verification of a product). The witness (d_1,…,d_k, m), Σ bits(d_i) = bits(m) = n,
k ≈ n/log n, is distributed (as the designer likes) among g ≈ n^{1/5} parties holding ≤ n^{4/5} bits each;
auxiliary labels are allowed; every label is seen by two parties; each party accepts or rejects its own
labels; exactly one accepting labelling per witness with Π d_i = m. Minimise U = total label bits.
   Known: Ω(n) ≤ U ≤ (1/5 + o(1)) n log₂ n.      Needed for 2^{o(n)} prime finding: U = o(n √log n).
* U = O(n) would follow from an O(n)-bit "locally checkable certificate" of iterated multiplication with
  n^{4/5}-bit checks; nothing of the kind is known for any multiplication-like problem beyond one product
  (where the SS transform is the certificate). A positive answer gives π(I) exactly, hence deterministic
  prime finding in 2^{O(n/√log n)} = x^{o(1)} (Polymath4 target 2^{o(n)} exceeded), via prime-finding.md
  §4; it would also give the exact π(x) in x^{o(1)} — far beyond Lagarias–Odlyzko. This is why one should
  expect the question to be hard: it would be a wholly new algorithmic phenomenon for the product.
* Any ω(n) lower bound implies a superlinear Boolean circuit lower bound for an explicit TC⁰ predicate
  (§5), so a negative answer is not provable today either. The only theorems available are in restricted
  models: trees (§3, tight at n log k), single cuts (§2.1), and the cap on the cut-rank method (§2.3).
* Intermediate target that is neither: a lower bound for *forward* networks (every auxiliary label a
  function of a set of factors only, never of m) that are additionally *exact at every label* (no label is
  a residue/hash of a partial product). This is the tree model in disguise; the first genuinely new case
  would allow residues, where the counting of states (§5: 2U ≥ Σ_a log₂ #states(a)) no longer gives size
  growth. I see no technique for it.
* Modular refinement (independent of Q): π(I) mod M is available for log M ≈ Σ_{q ≤ T} e_q(T) log q with
  fold T, where e_q(T) is the exponent table of §4.5(b); fold T costs cut Θ(n log T). Since the fold enters
  the cut only through log T, no polynomial saving in T changes the exponent Θ(n log n) at M ≥ x^{0.525}:
  the barrier of prime-finding.md §4 stands with the constant improved, not the shape.
   Additional data (span4.py, Smith normal form): N = 81 (q = 3, a = 4): folds 9, 18, 27 all give e = 2
   only, so the learnable exponent grows slower than log_q(fold) here; the exponent table is in the
   scratchpad file iterprod/span4.out (run still extending to N = 64, 125, 243 when this was written).

## 7. Lean status (lean/EthFollowup/Scratch/IterProd/)

* TreeBound.lean — `cost_ge_entropy`, `cost_ge_equal`: Lean-proved (general), sorry-free, axioms
  [propext, Classical.choice, Quot.sound] (printed in-file). 130 lines. Imports BinaryEntropy, Log.Base.
* CutRank.lean — `rank_eq_card_of_disjoint_rows` (rank = #nonzero rows for disjoint supports),
  `rank_prodMat`, `rank_prodMat_full`, `rank_prodMat_pow` (rank 2^a across the factor/label cut),
  `rank_prodMatFixed_le` (≤ τ(m) with m hard-wired): Lean-proved (general), sorry-free, same axioms.
  Imports EthFollowup.Barriers.RankBounds (reuses `rank_eq_card_of_linearIndependent`,
  `rank_le_card_of_eq_sum_mul'`).
* ModCheck.lean — finite-difference identity for μ mod q^a: Lean-checked on instances (#eval, all true),
  core Lean only.
* Not formalised: §2.2 (Model R certificate for the tree), §4 cut counts (back-of-envelope, each a
  one-line size count), §4.5(b) periodicity argument (three lines on paper, brute-force confirmed for
  N ≤ 125), §5 circuit simulation (standard, prose).
* Checked with `lake env lean` under the semaphore wrapper; no `lake build` of the modules was completed
  (the exclusive lock was held by another executor's leanchecker for > 1 h), so the #print axioms
  statements are at the end of each file instead of in a separate importing file.

## 8. Second pass (5 Nov 2026): checkers, residue targets, totient counts

Three directions not covered by §4: (a) non-tree verification by a (de)randomised checker, (b) verifying
only Π d_i ≡ m modulo Q ≈ x^{0.525}, (c) witness structures built on φ(m) (one multiplication). Each is
quantified below; none gets below the tree, and (a), (c) each have a clean reason. Notation as in §4;
"top problem" = the K := n/P ≈ n^{1/5} partial products of P bits each that survive node absorption (§4.2).

### 8.1 (a) Derandomised checkers: exactness forces a modulus of ≥ n/2 bits

Setting. A checker accepts (d, m) iff some predicate of the residue N mod Q_s holds, N := Π d_i − m, with
the seed s a label and an integer weight χ_s(r) on the residue r (the engine sums over s for free; the
weights are arbitrary since (s, r) fit in a node). The engine value is Σ_{(d,m)} F(N), F(N) :=
Σ_s χ_s(N mod Q_s). For the count to be c·#{true witnesses} we need F(N) = c·[N = 0] for every N that a
false witness can produce; for fixed d the label m ranges over an interval of length ≥ 2^{n−1}, so F must
vanish on 1 ≤ N < X with X ≥ 2^{n−1}.
 (i) Pure divisibility (χ_s = [r = 0], any sign/weight per s): Σ_{Q_s | N} χ_s = c[N = 0] for 0 < N < X
     is a triangular system in N (N = 1 kills the modulus 1, N = Q_s kills χ_s inductively), so χ_s = 0
     for all Q_s < X: some modulus must be ≥ X = 2^{n−1}. The check "Π d_i ≡ m mod Q" with Q ≥ 2^n is the
     full product again (K multiplications mod Q: cut ≥ (K−1)n).
 (ii) Arbitrary residue weights. F is a combination of the exponentials e(aN/Q_s); the number T of
     distinct frequencies is ≤ #Farey(Q_max) ≈ (3/π²) Q_max². F satisfies a linear recurrence of order T,
     so X − 1 ≥ T consecutive zeros force F ≡ 0, contradicting F(0) = c ≠ 0. Hence T ≥ X and
       Q_max ≥ (π/√3)·√X ≈ 1.81·2^{(n−1)/2}:  some modulus has ≥ n/2 − 0.1 bits.
     (Checked by exact rank computation for X ≤ 48, scratchpad iterprod/freq.py: the minimal Q_max with
     δ_0 ∈ span{N ↦ [N ≡ r (mod b)] : b ≤ Q_max} on [0, X) matches the Farey count bound; see below.)
     Cost of an (n/2)-bit modular check of the top problem: a chain of K−1 residue multiplications of
     ≥ n/2 bits each (each output residue is a label), cut ≥ (K−1)n/2 ≥ n log₂ K for K ≥ 4; computing the
     product exactly first and reducing is the tree. Mixing (exact tree up to level ℓ₀, residues above):
     n ℓ₀ + (K/2^{ℓ₀}) n/2 ≥ n log₂ K at 2^{ℓ₀} = K/2 — exactly the tree bound, no gain.
 (iii) Inclusion–exclusion over the number A(w) of accepting seeds (Σ_w C(A(w), j) = #{(w, j-subsets S):
     Π d_i ≡ m mod Π_{q∈S} q}) is the special case of (i) with moduli Π_S q: [A = S] = C(A, |S|) needs the
     full conjunction; truncating at A_max = max #{q ∈ Q : q | N} ≈ n/log q_min still needs the degree-
     A_max term, a modulus of ≈ n bits: cut Θ(Kn) again.
 Verdict: every residue-based checker that is exact after summing over seeds needs a modulus of ≥ n/2 bits
 and therefore costs ≥ the tree on the top problem. Non-residue checkers (hashes h_s(d, m) of b bits) have
 no such theorem, but the only exact one known is the verifier itself; real-logarithm checks (Σ log₂ d_i =
 log₂ m to n + log k bits) are the discrete-log redundancy of §4.3(c) again: k logs of n bits = kn.
 Rank check (freq.py, exact arithmetic, X = 2..48): the minimal Q_max with δ_0 ∈ span is exactly the least
 Q with #Farey(Q) ≥ X (necessary by the recurrence argument, and sufficient on every instance tested), e.g.
 X = 43..46 → Q_max = 12 (#Farey = 46), X = 47, 48 → 13 (58). So the bound Q_max ≈ 1.81√X is sharp.

### 8.2 (b) Residue targets: Π d_i ≡ m (mod Q) changes neither the fold nor the cost

* Information. #{(d, m) : m ∈ I, Σ bits(d_i) ≤ n, Π d_i ≡ m (mod Q)} = Σ over m′ ∈ (I + QZ) ∩ [1, 2^n) of a
  fold-k weight (τ_k with the size constraint): the exact count of the same weight over another cheap set.
  Nothing is gained by the modular target: the fold k ≈ n/log n needed to isolate ω = 1 modulo M is forced
  by §4.5(b)/prime-finding §4 (Vandermonde + Fermat periodicity) regardless of whether the final answer is
  wanted exactly or mod M, and the fold is what costs n log k. "Only residues are needed" was already the
  situation in Theorem B′: the count is exact, the identity is modular.
* Cost. The k-fold product reduced mod Q, Q ≈ x^{0.525}: residues r_j = r_{j−1} d_j mod Q are labels of
  0.525n bits, each step a multiplication of sizes (0.525n, w) plus a division by Q: cut ≥ 0.525n per step,
  total ≥ 0.525·n·k = Θ(n²/log n) ≫ n log k. Reducing mod Q only after the exact product is the tree plus
  O(n). Reduction at an intermediate level ℓ₀ gives n ℓ₀ + 0.525 n k/2^{ℓ₀} ≥ n log k − O(n) (8.1(ii)).
  On the top problem the same: K residues of 0.525n bits = 0.525 nK = Θ(n^{6/5}).
* The one thing residues do buy is in-node reduction: a P-bit factor held by one node can emit its residue
  mod any small Q for free (this is why 8.1 is phrased on the top problem). It does not help because 8.1(ii)
  forces log Q ≥ n/2.
 Verdict: (b) is (a)(i) with Q fixed in advance; dead for the same reason, with the extra observation that
 the modular target is equivalent to an exact count over a cheap set.

### 8.3 (c) Totient-type witnesses: one multiplication gives φ(m), but the engine sees a count only through its moments

Cheap counts (O(1) multiplications of n-bit numbers, parsimonious witnesses) and their values on squarefree m:
  φ(m) = #{(a,b,q) : ab = 1 + qm, a,b < m} = Π(p−1);  m, (m−1)^j, σ(m);  J_λ(m) = Π(p^λ − 1) (λ-tuples coprime
  to m, certified by a chain of λ gcd/inverse pairs, cut Θ(λn));  s(m) = #{a : a² ≡ 1} = #{a : a² ≡ a} = 2^ω;
  #{a : a³ ≡ a} = 3^ω for odd m (1 + gcd(2, p−1) = 3);  #{a : a² ≡ D} = Σ_{e|m}(D/e) (character twists);
  N₀(m) = #{(a,b) ∈ [1,m−1]² : m | ab} = Σ_{d|m} dφ(m/d) − (m−1), which is 0 iff m is prime.
  (Lean: TotientCheck.lean, #eval true: 2^ω and 3^ω counts for m ≤ 400.) A solution count mod m that is a
  constant T for every prime p is the point count of a finite scheme with T rational points (Chebotarev), i.e.
  m | a(a−1)⋯(a−T+1): verifying it is the ordered T-factorisation m = Π gcd(m, a−i), the tree again (n log T),
  or T divisibilities of n bits (Tn). So beyond t ∈ {2, 3} and their products, exponential weights t^ω are
  not cheaper this way. What is new is the polynomial-in-p family (φ, J_λ, m, σ).

(i) Isolating φ(m) = m − 1 (equivalently N₀(m) = 0). This is a ∀ over a < m; the engine cannot test a count,
  only sum functions of witnesses. The engine-accessible functionals of c(m) := m−1−φ(m) are the moments
  Σ_{m∈I} c(m)^j W(m) = #{(m, a_1..a_j) : a_i non-units} (W any weight on ≤ P bits of m): witness ≥ jn bits,
  so cut ≥ jn, achieved. Hence what is computable at cut Θ(Dn) is Σ_m G(φ(m), m) for polynomials G of degree D.
  * Exact. Need G(φ(m), m) = [m prime] on I. For I = [1, x] (or any I with ≫ x^{1/2+ε}·q points per class):
    G((q−1)(r−1), qr) must vanish for all primes q ≤ x^{1/2−ε} and all residues r = p (mod M) (p prime in
    I/q), i.e. G vanishes on the > D distinct lines y = (1 − 1/q)(x − q); restricted to a vertical line it has
    > D roots, so G ≡ 0, contradicting G(r−1, r) = 1. Thus D ≥ π(x^{1/2−ε}) over Z or mod any prime M: cut
    ≥ x^{1/2−ε}·n, exponential. For a short I (|I| = H ≥ 2^P, below which brute force is x^{o(1)} anyway)
    generic interpolation needs D ≈ √(2H): cut √(2H)·n ≫ n log n. No lower bound for short I, but no basis
    found that beats brute force: the moment method is brute force in disguise.
  * Mod M. G = 1 + c·H with H ≡ −c(m)^{−1} on the composite points, which (a) requires M ∤ c(m) for every
    composite m ∈ I (false on long I: m = Mp′, p′ ≡ 2 (mod M), c(m) ≡ p′ − 2) and (b) along a fixed class
    x ≡ r forces H(·, r) to interpolate −1/(r−1−y) at M − 1 points: degree M − 2. Cut Θ(Mn) for π mod M.
    The fold route gives π mod M with log M ≈ T at cut n log T = n log log M. Exponentially worse in M.
  * The Fermat polynomial 1 − c(m)^{M−1} (degree M − 1) counts #{m ∈ I : M | c(m)}, polluted by composites.
  * Count-of-counts: "φ(m) = c" has a short certificate only through the factorisation of m (φ = Π p^{e−1}(p−1)),
    two iterated products: circular.
(ii) What polynomial weights can do: L-adic vanishing (new identity family). For L ≥ 2 let λ = λ(L)
  (Carmichael) and F_a(p) := (p^λ − 1)^a ≡ 0 (mod L^a) for p ∤ L. Then Π_{p|m} F_a(p) = J_λ(m)^a ≡ 0 (mod L^{2a})
  for squarefree m coprime to L with ω(m) ≥ 2, so with the chain weight for [sqf] mod L^{2a}:
     Σ_{1<m∈I, sqf, (m,L)=1} J_λ(m)^a ≡ L^a · Σ_{p∈I, p∤L} ((p^λ − 1)/L)^a   (mod L^{2a}).
  L = 2, λ = 1, J_1 = φ:  Σ_{1<m∈I odd sqf} φ(m)^a ≡ 2^a Σ_{p∈I, p≡3 (4)} ((p−1)/2)^a (mod 2^{2a})
  (Lean-checked, I = [2, 600], a = 1..6, all true; the m = 1 term must be excluded). The inner weight
  ((p−1)/2)^a ≡ 1 (mod 2^a) for all p ≡ 3 (4) iff a ∈ {1, 2, 4} (Lean: a = 1..8), so a = 4 gives
  #{p ∈ I : p ≡ 3 (4)} mod 16 from four inverse pairs and the sqf chain mod 256; other a need a correcting
  weight on p mod 2^a (free only for a ≤ P). Cost for M = L^a: a inverse-pair tuples (cut ≥ λ a n) plus
  [sqf] mod L^{2a} (fold ≈ L^a, cut ≈ a n log L): Θ(λ(L)·a·n) = Θ(λ(L) n log M), one prime power at a time.
  The fold route gets every q ≤ T simultaneously, log M ≈ T, at cut n log T = n log log M. The totient route
  is exponentially worse in M and matches the fold only at M = O(1). Mechanism: a degree-δ polynomial weight
  costs δn (its witness) and vanishes to L-adic order ≈ δ; the exponential weight T^ω costs n log T and
  vanishes to order ≈ log_q T for all q ≤ T at once. The log k of the product tree is the price of that
  exponential, and nothing polynomial in (p, φ(p), …) reproduces it.
(iii) Divisor-sum identities with small divisors cannot isolate primes either: Σ_{d|m, 1<d≤√m} h(d) ≡ 0 (mod M)
  for all composite m ∈ I forces h ≡ 0 (take m = dp, p > d prime). The chain trick of Theorem B works for
  [sqf] because μ² is the parity of a count, not because the divisors are small.
 Verdict: (c) fails sharply. φ is one multiplication, but "φ(m) = m − 1" is a ∀; the engine reaches a count
 only through moments; moments isolate the maximum at degree ≥ M − 2 (mod M) or ≥ x^{1/2−ε} (exactly on [1,x]),
 cut Θ(Mn) against the fold's Θ(n log log M). The L-adic identity (ii) is the only positive by-product.

### 8.4 Verdict of the second pass, and what it adds to §6

* No construction. (a) exact residue checkers need a modulus of ≥ n/2 bits (recurrence/Farey argument, sharp
  on instances), so they cost ≥ the tree on the top problem; (b) a modular target is an exact count over a
  cheap set and costs ≥ 0.525 nk; (c) totient moments cost Θ(Mn) for π mod M against Θ(n log log M) by the
  fold. U = (1/5 + o(1)) n log₂ n remains the best; the barrier of prime-finding.md §4 is unchanged.
* The pattern across §4, §4.5 and §8: every route to π mod M costs cut ≥ n·log(fold) with fold ≈ log M for
  the exponential weights t^ω (tree, root-of-unity tuples s(m)^j, exponentiation a^T) and ≥ n·log M for
  polynomial weights. The question Q of §6 is untouched: a verifier of the ordered T-factorisation (or of
  m | a(a−1)⋯(a−T+1), the same witness set) with cut o(n √log n) for T ≈ n. The new no-go results narrow the
  design space: it cannot be a residue/fingerprint checker (8.1), and no polynomial weight substitutes for
  the exponential one (8.3(ii)).
* Lean (lean/EthFollowup/Scratch/IterProd/TotientCheck.lean, core Lean, `lake env lean`, 2 runs — the first
  exposed the missing m = 1 exclusion in 8.3(ii)): 2^ω / 3^ω point counts for m ≤ 400; the 2-adic φ-moment
  congruence on [2, 600] for a = 1..6; ((p−1)/2)^a ≡ 1 (mod 2^a) exactly for a ∈ {1, 2, 4}. All #eval true.
  Not formalised: 8.1 (recurrence argument; rank-checked in Python for X ≤ 48), 8.3(i) lines argument (prose).
