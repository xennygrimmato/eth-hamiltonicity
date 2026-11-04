# The iterated product on the counting engine: constructions tried, lower bounds proved, the open question

Status: working notes, 4 Nov 2026. §0 is the verdict (written last); §§1–6 are the analysis, appended as
they were obtained. Lean: lean/EthFollowup/Scratch/IterProd/*.lean.

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
