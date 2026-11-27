# loglog: can the factor log log n in the bound in n be removed?

27 Nov 2026. Machine-generated, not refereed; nothing here has been checked by a person. Tags: **[K]** quoted,
with location; **[R]** proved here (argument given in full); **[D]** derived here, unreviewed, resting on the cited
inputs; **[N]** numerical (script named); **[C]** conjecture; **[X]** dead, with the reason.

Sources (S = the directory `pb` of the session scratchpad, as in the brief). AN-ETH =
`S/aneth/paper.txt` (line numbers of that file); OA-ETH = `S/oaeth/main.tex` and `S/oaeth/quantitative-reduction.tex`
(line numbers of those files); both are unrefereed, machine-generated papers with Lean developments. Repo notes used: `research/sat-width.md` (density form of (68), Theorem K, Theorem S),
`research/sat3/ideas-round2.md` §3, `research/hc-degree-theorem.md` (same device for #HC).
Scripts: `research/sat3/loglog/` (§11). Notation: n variables, m clauses, D = max(2, m/n) the clause density,
e = Θ(1/√log n) the engine's rate (a network with total U is evaluated in 2^{O(eU)}), log = log₂.

## 0. Verdict

**No route gives 2^{O(n/√log n)} in n alone, and none improves the factor log log n** (not to log log log n, not to
√log log n). What was found:

1. **The diagnosis of the previous round is confirmed, with two corrections** (§1).
   The factor is `O(n) marks × log(clause density) address bits` in both papers, and the density is that of a
   sparsifier output at ε ≈ 1/√log n. Correction (a), already in `sat-width.md`: it is the average density m/n, not
   the maximum occurrence. Correction (b), new: the "entropy count" of round 2 is not an obstruction. At most 2^n
   monomials are ever forced, and every formula has an exact mark polynomial with at most 2^n monomials (§4.4). The
   loss is that a pairwise wire pays for the *trace* of the marked set on its own clauses, and the traces of one
   marked set on many wires add up (§6).
2. **Route 1 (better sparsification) is closed for fixed k = 3** [R] (§2). Two new lower bounds for sparsification
   on the same variables: pieces that are restrictions need density Ω(ε^{−2}) at 2^{εn} pieces (Calabro's
   O(ε^{−2} log²(1/ε)) is tight up to the log²); pieces that are arbitrary 3-CNFs need density Ω(ε^{−1/3}). So
   log(density) = Θ(log log n) at ε = 1/√log n for every sparsifier of this kind. `sat-width.md` Theorem S says
   nothing for fixed k; this fills that case.
3. **A new exact expansion without parity checks and without modular arithmetic** [R] (§5, "level identity"): a
   chain of subformulas, truncated inclusion–exclusion on each level, certified level by level. It gives U = O(n)
   on planted random formulas of any density [D], but U = Θ(n log² D) on Example H ([D]; small exact check [N]),
   so it does not improve the worst case.
4. **The obstruction, as an explicit family** (§6, Example H): n/2 guards, each guarding a bundle of Δ random
   2-clauses on the other n/2 variables, with 1 ≪ Δ ≪ √log n · log log n. No sparsification is involved: these are
   formulas with m = nΔ/2 clauses. The best of the schemes examined costs Θ(e·n·log Δ): plain clause network
   e·n·Δ; marks with any kill e·n·log Δ; publishing the false guards (n/Δ)·log Δ, which is O(e n) only for
   Δ ≳ √log n·log log n. The
   joint entropy of what has to be shared is O(n) bits; the Θ(n log Δ) is the sum of its marginals over the wires.
5. **Lower-bound side (Route 5)** [R] (§8): rank arguments cannot show that the factor is necessary. Every cut rank
   and the tensor rank of the solution tensor are at most 2^{n(1−1/K)}, so these methods stop at U ≥ 2n. Inside the
   clause-mark model the bound Θ(n log Δ) for H holds for every pointwise-exact polynomial, whatever the kill (§6.3,
   [R] for the lemma, [D] for its application to random H). This removes the caveat of `sat-width.md` Theorem K
   for this family.
6. **What would fix it** (§10): a contraction theorem that charges per shared bit and not per reader of the bit
   (wires read by d ≤ polylog nodes at the cost of one wire). For bounded-arity constraint networks this statement is
   equivalent to the target. Its far end (d = K, arbitrary tables) would give k-clique in N^{o(k)}, which I do not
   see how to get from the published theorems. Both engines are built on pairwise identifications; I found no cheap
   extension.

Odds that the target follows from the two engines used as black boxes: below 2%. With a new engine-level identity
for multi-reader bits: 3–5%. Odds for an intermediate factor (o(log log n)) by the black-box routes: below 2%.

## 1. Where the factor comes from (verification)

**[K] AN-ETH.** l.745–748: "This gives O(kn log ∆) bits on the edges. For k ≤ (log n)^{1/4} we have
log ∆ = O(k log log n), which gives the factors k² and log log n in the bound in n […] we do not know whether the
factor log log n can be removed." l.2441–2443 (Remarks after Theorem D): "The factor log ∆ = O(k log(k/e)) is paid
in (68): up to 14n marks are placed among up to r̄s̄ = O(n∆ log ∆) incidences, and the shared strings say which."
The bound (68), l.2334: U ≤ 6k(n + log 2Δ) + 28kn·log(96Δ log 2Δ) + 2g². The first term is the kind-0 marks
(n̄ ≈ n/log 2Δ truncated inclusion–exclusion marks at ≤ 3 log 2Δ bits), the second the kind-1 marks (M ≤ 14n marked
incidences of the r̄ ≤ 10n parity checks, each check of size s̄ < 32Δ log 2Δ, so log 3s̄ bits per mark and test).
Sparsification enters only through Δ ≤ 2(8k/ε)^{3k} + 2 at ε ∈ [e, 2e] (Step 5, l.2373–2400). l.2438–2441: "Only
log ∆ enters, so any form of the Sparsification Lemma with 2^{O(εn)} outputs […] in which the number of occurrences
is polynomial in 1/ε […] gives the same bound for fixed k."

**[K] OA-ETH.** Same source. `quantitative-reduction.tex` l.7–9: "The degree bound of Lemma [total-order] lets us
index a monomial retained in the product of their polynomial lifts with O_k(n log log n) wires." There: ≤ 6n parity
equations P_i = Σ_{e ∈ row i} v_e over F₂ (rows of length P = 20000B²μ², D₀ = 320000B²μ³, μ = ⌊log m⌋+1, `main.tex`
l.3265), 2-adic lift truncated at total order n+1, retained monomials of degree ≤ K = k(a + 2(ℓ−1)) = O(n) in
N ≤ n·λ^{O(1)} test–variable incidences (eq. sharp-incidence-degree, l.175), wires M ≤ J² + K log(e(N+K)/K) = O(nν),
ν = ⌈log log n⌉ (eq. sharp-wire-budget, l.229–236). So again O(n) marks, each an address among polylog(n) candidates.
Their rows are polylogarithmic even at constant density (the factor μ²), which is why they switch to the clause network
for m ≤ nν (l.360–369). `main.tex` l.1510–1517: "If sparsification gave B = O_k(1) at σ = Θ(ρ(n)/n), we would already
have a 2^{O_k(ρ(n))}-time algorithm […] At this choice of σ, however, the guarantee is only B = (log n)^{O_k(1)}."
§2 shows that no sparsifier on the same variables can give B = O(1) there.

**[D] Density, not occurrence** (`sat-width.md` Prop. 1.1 and Cor. 5.1; rechecked here against (60)–(69)). In
Steps 1–3, Δ is used through m ≤ Δn everywhere except in the node size (69). With D in its place,
U ≤ 6k(n + log 2D) + 28kn log(96D log 2D) + 2g², and after branching on the ≤ n/√log n variables that occur more
than kD√log n times: **#k-SAT in 2^{O(k·n·log(2D)/√log n)} for D = m/n ≤ n^{c}.** So the published pair of bounds
is the two ends of one bound in (n, m): `n·log(2 + m/n)/√log n`. The factor log log n is log D for D = (log n)^{Θ(1)}.

**Consequence: the target has nothing to do with sparsification as such.** It is the statement

> (T) #3-SAT on formulas with n variables and m = n·D clauses in time 2^{O(n/√log n)}, uniformly in D ≤ (log n)^{O(1)}.

Formulas with D = (log n)^{1/4} already have no bound better than 2^{O(n log log n/√log n)} (Example H, §6).

*Remark (#HC).* The factor log d̄ of R2d (`hc-degree-theorem.md`) has the same form, n marked edges among m, but
there it is honest entropy: a graph of degree d can have d^{Ω(n)} 2-factors, and the marks are the terms. For SAT
the terms carry n bits (an assignment) and the n log D is an artefact of how they are shared (§4.4, §6.3).

**Check of round 2, §3.** (i) "the factor comes entirely from the O(n) marks of the parity checks at log Δ address
bits each": confirmed, with D for Δ. (ii) "an entropy count shows the marks themselves must drop to O(n/log Δ)":
this holds for the particular expansion (all M-subsets of incidences occur in it), but it is not a property of the
problem; see §4.4. (iii) CRT with ℓ-adic checks, Fermat checks: confirmed dead (`sat-width.md` Lemma D(iii) has the
same valuations). (iv) "mod-2 isolation fails": confirmed, and for a second reason: even with a unique solution and
precision 1 the number of checks does not drop (§4.2, §9).

## 2. Route 1: sparsification with ε = 1/√log n

**The trade-off.** With 2^{εn} outputs of density D(ε), the time is 2^{εn + C·e·n·log D(ε)}. For D(ε) = ε^{−a} the
minimum over ε is at ε ≈ aCe and equals ≈ a·C·e·log(1/e) = (a/2)·C·e·log log n (`cost_tables.py` (2): the ratio to
e·log(1/e) is 1.97–2.00 for a = 2 and tends to 1/3 for a = 1/3) [N]. So any polynomial density, with any exponent
a > 0, gives Θ(log log n); only D(ε) = (1/ε)^{o(1)} would help.

**[K] Upper bounds.** AN-ETH l.2053–2055: for k = 3, "a bound in Calabro's proof [Cal09, (5.4)] gives
M(ε) = O(ε^{−2} log²(1/ε))" clauses per variable. OA-ETH `lem:sparsify` (`main.tex` l.3543–3560): occurrence bound
B = O_k([σ^{−1} log(2/σ)]^{k−1}), the same for k = 3.

**The test formula.** T(b, J): J blocks of b variables, and all clauses (¬x ∨ ¬y ∨ ¬z) on three variables of one
block ("at most two ones per block"). n = bJ, density C(b,3)/b ≈ b²/6, and |SAT| = |B|^J with |B| = 1 + b + C(b,2)
≥ b²/2.

**Proposition S1 (restrictions) [R].** Let SAT(T(b,J)) ⊆ ⋃_{i ≤ N} Q_i for subcubes Q_i (partial assignments ρ_i)
such that each restricted formula T|ρ_i (satisfied clauses removed, false literals deleted) has at most c·n clauses.
If b = ⌈15√(c+1)⌉ then N ≥ 2^{n/b}. So N ≤ 2^{εn} forces **c + 1 ≥ (1/ε − 1)²/225**.

*Proof.* Fix ρ. In block j let r_j variables be free and f_j ∈ {0,1,2} be fixed to 1 (three ones give no solution).
The block contributes cl_j clauses and sol_j solutions: (C(r,3), 1 + r + C(r,2)) for f = 0; (C(r,2), 1 + r) for
f = 1; (r, 1) for f = 2. In all cases sol_j ≤ 9·max(1, cl_j)^{2/3}: for f = 0 and r ≥ 3, sol ≤ r² and
r³ ≤ 27·C(r,3); the other cases are smaller. By the arithmetic–geometric mean inequality and Σ cl_j ≤ cn = cbJ,
∏ sol_j ≤ 9^J (1 + cb)^{2J/3}. Hence N ≥ (b²/(18(1+cb)^{2/3}))^J ≥ (b^{4/3}/(18(c+1)^{2/3}))^J ≥ 2^J for
b ≥ 15√(c+1), since 15^{4/3}/18 > 2. ∎

**Lemma F (fibre) [R].** Let χ be a CNF of width ≤ 3 on a set V of b variables all of whose satisfying assignments
have weight ≤ 2, and let M be the number of clauses of χ with at least two negative literals. Then
|SAT(χ)| ≤ 3b + 2 + 3M.

*Proof.* If χ has a clause without negative literals, every solution has a 1 among its ≤ 3 variables, and at most
3b sets of size ≤ 2 do. Otherwise let G be the graph of the pairs {x,y} with 1_{xy} ∈ SAT(χ), Low the vertices of
degree ≤ 2 and L the rest; at most 2b edges touch Low. (a) Let x, y ∈ L be non-adjacent. A clause false at 1_{xy}
has its negative literals among ¬x, ¬y and its positive literals outside {x,y}. If only ¬x occurs, with positive
literals u₁, (u₂), then every solution containing x contains u₁ or u₂, so x has degree ≤ 2: contradiction. So the
clause contains ¬x and ¬y, and no other negative literal: distinct non-edges inside L use distinct clauses with
exactly two negative literals; there are at most M₂ of them. (b) Let {x,y,z} be a triangle of G. A clause false at
1_{xyz} has negative literals inside {x,y,z} and positive literals outside. If its negative literals lie in a pair,
say {x,y}, it is false at 1_{xy} as well, which is a solution: contradiction. So it is (¬x ∨ ¬y ∨ ¬z): G has at
most M₃ triangles. (c) G[L] has ℓ = |L| vertices, at least C(ℓ,2) − M₂ edges, hence at least C(ℓ,3) − (ℓ−2)M₂
triangles. For ℓ ≥ 3 this gives ℓ(ℓ−1)/6 ≤ M₂ + M₃/(ℓ−2) ≤ M, so C(ℓ,2) ≤ 3M. Then
|SAT(χ)| ≤ 1 + b + 2b + max(1, 3M). ∎ (`sparsify_lb.py` (1), (1′): no violation in 4000 random and 600 targeted
instances with b ≤ 10 [N]; the lemma is far from tight.)

**Proposition S2 (arbitrary pieces) [R].** Let c ≥ 1, b = 48c + 28, n = bJ. If SAT(T(b,J)) = ⋃_{i ≤ N} SAT(ψ_i)
with CNFs ψ_i of width ≤ 3 on the same n variables, each with at most c·n clauses, then **N ≥ 2^{n/(69400 c³)}**.
So 2^{εn} pieces force c ≥ (69400 ε)^{−1/3}. Disjointness is not needed.

*Proof.* Fix ψ = ψ_i and write M_j for the number of its clauses with at least two negative literals on variables of
block j; Σ_j M_j ≤ cn, so more than J/2 blocks are *poor*: M_j ≤ 2cb. Call two blocks adjacent if a clause of ψ
contains variables of both; there are at most 3cn adjacent pairs, so by Turán's bound the poor blocks contain a set
I of at least (J/2)²/(6cn + J/2) = J/(24cb + 2) pairwise non-adjacent blocks. Fix an assignment α of the blocks
outside I. No clause meets two blocks of I, so the solutions of ψ that extend α form a product ∏_{j∈I} F_j(α), and
each nonempty factor is the solution set of a CNF as in Lemma F (the restriction of ψ by α to the clauses that meet
block j; restriction does not create negative literals), with M ≤ M_j. So
|F_j(α)| ≤ 3b + 2 + 6cb ≤ |B|/4, by the choice of b. Summing over α,
|SAT(ψ)| ≤ |B|^J·4^{−|I|} ≤ |SAT(T)|·2^{−J/(12cb+1)}, and b(12cb+1) ≤ 69400c³. ∎

**Conclusion [R].** For k = 3, every sparsification on the same variables has log D(ε) ≥ (1/3) log(1/ε) − O(1), and
every sparsification by restrictions has log D(ε) ≥ 2 log(1/ε) − O(1). At ε = 1/√log n that is (1/6) log log n and
log log n respectively (`sparsify_lb.py` (3)). Route 1 cannot change the order of the factor. [X]

*Limits.* The formula T is trivial for other reasons (its dense parts are local, and "at most two of b" has a
linear-size encoding with counter variables). The propositions close the route, not the problem. Pieces with new
variables are not covered (§7).

## 3. Route 2: branch on high-degree variables, engine on the rest

[D] In a formula with m = Dn clauses fewer than km/d variables occur more than d times. Branching on all of them
costs 2^{kDn/d}, which is 2^{O(en)} only for d ≥ kD/e: the maximum occurrence falls to D/e, the density does not
fall at all. The mark network pays log D with D the *average* density (§1), so nothing is gained: this step is
already inside the bound (it is the first step of the proof of the density form). Branching that lowers the density
itself is sparsification, and §2 applies. A direct comparison for one variable of degree d: wiring it costs e·d,
marks cost ≈ e·log d per variable on average, branching costs 1. Branching wins only for d > 1/e, and only if such
variables are few. Example H (§6) has n/2 variables of degree Δ < 1/e. [X]

## 4. Route 3: the marks

Throughout, a *mark polynomial* is a multilinear P ∈ Q[v_E : E ∈ Φ] (integer coefficients in both papers); v(ξ)
is the 0/1 vector of the clauses violated by ξ, and 𝒱 = {V(ξ)} is the family of violation sets. P is *pointwise exact* if P(v(ξ)) = [V(ξ) = ∅] for all ξ. Both
papers use P = η·K with η the truncated inclusion–exclusion and K = ∏_j [|V ∩ Λ_j| even], truncated 2-adically.

### 4.1 At least n/k marks in some term

**Lemma N [R].** If #SAT ≡ Σ_Π c_Π·2^{n−|vars(Π)|} (mod 2^{n+1}) with integers c_Π (Π ranges over jointly falsifiable
sets of clauses), then some Π with c_Π ≠ 0 has |vars(Π)| ≥ n − v₂(#SAT), hence at least (n − v₂(#SAT))/k clauses.

*Proof.* Otherwise every term is divisible by 2^{v₂(#SAT)+1}. ∎ So a formula with an odd number of solutions needs a
term with n/k marks, whatever the expansion; the number of marks cannot fall to n/log D.

### 4.2 At least (n − log #SAT)/k checks

**Lemma W [R].** Let Λ₁,…,Λ_r be parity checks such that the assignments with all parities even are the
satisfying assignments and at most N others. Then r ≥ (n − log(#SAT + N))/k.

*Proof.* [|V(ξ) ∩ Λ_j| even] is the condition p_j(ξ) = 0 for a polynomial p_j = Σ_{E∈Λ_j} v_E of degree ≤ k over
F₂. By Warning's second theorem ([K]) the common zeros of r such polynomials number 0 or at least 2^{n−kr}; here the
set is not empty unless #SAT + N = 0. ∎

The zero set depends only on the row space of the checks, so the bound holds for the rank of the incidence matrix.
Each check has a term with exactly one mark and 2-adic weight 0; Lemma 12 of AN-ETH therefore keeps every tuple with
one mark per check, r ≥ n/k − o(n) marks for formulas with few solutions and few light assignments. The same count
holds modulo 2 (after isolation), so precision 1 does not lower the number of checks.

### 4.3 Merged monomials: valuation = nullity

**Lemma M [R].** Let A be the r × m incidence matrix of the checks. In K(v) = ∏_j [⟨A_j, v⟩ even], the coefficient
of v^Π is (−2)^{|Π|}·2^{−rank(A_Π)} if the all-ones vector on Π lies in the row space of the column submatrix A_Π,
and 0 otherwise. In particular it has 2-adic valuation |Π| − rank(A_Π), and **every Π whose columns are independent
has coefficient (−1)^{|Π|}**.

*Proof.* K = 2^{−r} Σ_{J ⊆ [r]} ∏_E (1 − 2v_E)^{(JᵀA)_E}, and the exponent matters only modulo 2. So
K = 2^{−r} Σ_J Σ_{Π ⊆ supp(JᵀA)} (−2)^{|Π|} v^Π, and the fraction of J with (JᵀA)_E = 1 for all E ∈ Π is
2^{−rank(A_Π)} or 0. ∎ (`verify_identities.py` (B): 200 random matrices [N].)

So merging the marks of one clause in several checks does not help: the terms kept modulo 2^ν are the sets of
nullity < ν, the kept sets include all independent sets, and they have at most rank + ν − 1 elements.

### 4.4 What is forced, and what is not

**Lemma P [R].** (i) If every subset of Π₀ is a violation set (2^{Π₀} ⊆ 𝒱), then every pointwise-exact P has
coefficient (−1)^{|Π′|} at v^{Π′} for all Π′ ⊆ Π₀. (ii) The sets Π₀ of (i) are themselves in 𝒱, so at most
|𝒱| ≤ 2^n monomials are forced in this way. (iii) Every formula has a pointwise-exact P with rational
coefficients and at most |𝒱| ≤ 2^n monomials.

*Proof.* (i) The coefficient is Σ_{Π″ ⊆ Π′} (−1)^{|Π′∖Π″|} P(1_{Π″}), and P(1_{Π″}) = [Π″ = ∅] because 1_{Π″} is
v(ξ) for some ξ. (iii) Restriction to 𝒱 maps the monomials onto a spanning set of the functions on 𝒱, a space of
dimension |𝒱|; choose a basis among them and expand [V = ∅]. ∎

So neither the number of monomials (≤ 2^n suffices) nor their entropy obstructs. What obstructs is that the
coefficients of a sparse P are not local, and that the forced monomials, although at most 2^n jointly, have traces on
the wires whose logarithms add up to n log D (§6.3).

### 4.5 Check functions other than parity

`sat-width.md` Lemma D(iv): among f: {0..14} → {0,1} with f(0) = 1, f(1) = 0, parity is the unique function whose
Newton coefficients c_i have v₂(c_i) ≥ i − 1. For integer-valued f:

**Lemma V [R].** Let f(q) = Σ_i c_i C(q,i) be integer valued with f(0) = 1. (i) If f(1) = f(3) = 0 then
min(v₂(c₂), v₂(c₃)) ≤ 1. (ii) If v₂(c_i) ≥ τ for all i ≥ 2, then the zeros of f lie in one residue class modulo
2^{⌈τ⌉}.

*Proof.* c₁ = −1 and 0 = f(3) = −2 + 3c₂ + c₃, so 3c₂ + c₃ = 2 is not divisible by 4. For (ii),
f(q) ≡ 1 + c₁q modulo 2^{⌈τ⌉}. ∎ (`verify_identities.py` (C) [N].)

The extreme case of (ii) is the *isolation check* f(q) = 1 − q (zero only at q = 1): one mark per check, no 2-adic
truncation at all, exact over Z. With rate 1/|V| it kills an assignment with probability ≈ 1/e. This removes the
ν − 1 ≈ n extra marks of Lemma 12, but not the one mark per check; and as a random check kills a given assignment
with probability at most a constant, Θ(n) checks are still needed for 2^{Θ(n)} assignments [D]. It also loses
the monotone certificate X(Λ) (the factors are unbounded), so the checks would have to be found scale by scale with weights C(|V|, v_t) that are too expensive at coarse scales. [X] for the
factor; at best a constant.

### 4.6 Structure-aware checks: a scale formula

[D] Checks of size 2^t·O(1) kill, with constant probability each, every ξ with |V(ξ)| ≥ m/2^t, and a mark in such a
check costs ≈ t bits. If checks are added scale by scale, the number needed at scale t is ≈ n·h_t with
h_t = (1/n)·log #{ξ : m/2^{t+1} < |V(ξ)| ≤ m/2^t, not yet killed}, and the cost is

  U/n ≈ O(1) + Σ_{t ≤ log(D log D)} h_t · t + (extra precision marks) · (largest t in use).

For a planted random formula h_t ≈ t/2^t and the sum converges; for Example H, h_t ≈ 1/2 for every t (§6.1)
(`cost_tables.py` (3) evaluates the sums for these two model spectra). Both papers use the finest scale only, which costs (r + n)·log(D log D) on every
formula. So a structure-aware kill helps on formulas whose near-solutions are few, and not on H. This answers open
item 2 of `sat-width.md` §5.3 in the negative for the worst case, and positively for planted-type formulas (§5 gives
a cleaner way to the same end).

## 5. A kill-free exact expansion (level identity)

**Lemma L [R].** Let Φ₀ ⊂ Φ₁ ⊂ … ⊂ Φ_T = Φ, V_{t+1}(ξ) the clauses of Φ_{t+1} ∖ Φ_t violated by ξ, and
N_t ≥ max{|V_{t+1}(ξ)| : ξ ⊨ Φ_t}. Then, over the integers,

  #SAT(Φ) = Σ_{ξ ⊨ Φ₀} ∏_{t=0}^{T−1} τ_t(ξ),  τ_t(ξ) = Σ_{Π ⊆ V_{t+1}(ξ), |Π| ≤ N_t} (−1)^{|Π|}.

Moreover X_t(N) := Σ_{ξ ⊨ Φ₀} ∏_{t′<t} τ_{t′}(ξ)·C(|V_{t+1}(ξ)|, N+1) equals Σ_{ξ ⊨ Φ_t} C(|V_{t+1}(ξ)|, N+1), which
is 0 exactly when N ≥ max{|V_{t+1}(ξ)| : ξ ⊨ Φ_t}.

*Proof.* Let ξ ⊨ Φ₀. If ξ ⊨ Φ all factors are 1. Otherwise let t be the first level with V_{t+1}(ξ) ≠ ∅. Then
ξ ⊨ Φ_t, so |V_{t+1}(ξ)| ≤ N_t, the truncation of τ_t is void, and τ_t(ξ) = 0. The later factors are uncontrolled
integers multiplied by 0. The same argument applied to Φ_t gives the statement on X_t. ∎
(`verify_identities.py` (A): 300 random formulas, n ≤ 11, T ≤ 4, identity and certificates exact; lowering one N_t
by one breaks the identity in 251 of 290 instances [N].)

**Algorithm [D].** Nodes hold variables as in AN-ETH App. D, Step 3, with objects of kind 0 only, one family per
level. Φ₀ is enforced with untruncated marks (one bit per test). The bounds N_t are found and certified in the order
t = 0, 1, …: X_t(N) is a network of the same kind with N + 1 marks at level t, and X_t(N) = 0 certifies N. No parity
checks, no reduction modulo 2^β, no search for checks; tables are bounded by 1 in absolute value. The total is

  U ≤ 2(k−1)·[ |Φ₀| + Σ_t (N_t + 1)·max{1, log(3|Φ_{t+1} ∖ Φ_t|/N_t)} ] + O(T g²).

**Worst case [R for existence].** If Φ_t is a uniformly random half of Φ_{t+1}, an assignment that violates v
clauses of Φ_{t+1} satisfies Φ_t with probability ≤ 2^{−v}; by the union bound over 2^n assignments some half has
N_t ≤ n. With density doubling per level this gives U = O(k n log² D): worse than (68) by a factor log D.

**Planted formulas [D].** For a planted random 3-CNF of density C, all solutions lie within distance n·e^{−Ω(C)} of
the planted one ([K], recalled from the literature on planted 3-SAT, not re-read). Take densities C₁ < C₂ < … with
C_{j+1} = e^{cC_j/2}: the solutions of Φ_j violate at most C_{j+1}·n·e^{−cC_j} clauses of Φ_{j+1}, at ≈ cC_j bits
each, so level j costs n·cC_j·e^{−cC_j/2}; the sum over the log* D levels is O(n) (`cost_tables.py` (4)). So
**U = O(n) for planted random formulas of every density**, against O(n log D) for (68).

**Example H.** [N] `example_h.py` (20 guards, 20 other variables, Δ up to 16, three seeds): the maximum number
of false guards falls with Δ_t (20, 19, 15, 12, 4), while N_t does not fall (11, 15, 22, 33 for n = 40). [D] The
reason: the solutions of Φ_t have up to n/(2Δ_t) false guards, each with ≈ Δ_t/4 violated clauses at the next
level. So N_t = Θ(n) at every level and U = Θ(n log² Δ). [X] for the worst case.

## 6. Example H: the obstruction as a family

### 6.1 Definition and counts

H(n, Δ): guards x₁,…,x_{n/2}; variables y₁,…,y_{n/2}; for each guard i a bundle B_i of Δ clauses
(x_i ∨ u ∨ w), with u, w random literals of two y-variables. m = nΔ/2. Summing over the guards,

  #SAT = Σ_y ∏_i (1 + G_i(y)) = Σ_{S} #2SAT(Φ_S),  G_i = [y satisfies the 2-clauses of B_i],  Φ_S = ⋃_{i∈S} B_i.

[D] By the random 2-SAT threshold ([K]: clauses/variables = 1) only sets S of false guards with |S| ≲ n/(2Δ)
contribute, and for such S there are ≈ n/2 *active* clauses (clauses whose guard is false).

### 6.2 Three costs

(`example_h.py`, second table.) Per variable, in engine bits (to be multiplied by e) or in bits of enumeration:

| scheme | cost | when it is O(e·n) |
|---|---|---|
| clause network (one bit per clause and test) | e·n·Δ | Δ = O(1) |
| marks: guard's node tells the two other nodes of a clause that it is active; ≈ n/2 active clauses among nΔ/2 | e·(n/2)·log(2eΔ)·O(1) | Δ = O(1) |
| publish S (enumerate the false guards as part of the profile), then a clause network for Φ_S | (n/2Δ)·log(2eΔ) + e·O(n) | Δ ≳ (1/e)·log(1/e) = √log n·log log n |

The third line is what sparsification does when Δ exceeds its sunflower threshold: the branch "guard false" adds Δ
two-clauses and is rare. For 1 ≪ Δ ≪ √log n·log log n none of the three is O(e·n), and the best is the second:
**2^{Θ(n log Δ/√log n)}**, which for Δ = (log n)^{1/4} is 2^{Θ(n log log n/√log n)}. Other orders of the three
literals are worse [D]: a protocol for a clause (x ∨ u ∨ w) starts from one of its literals, and only "x false"
is rare (density 1/(2Δ)); starting from u costs one full bit per clause.

### 6.3 Why no kill helps, and where the log Δ is

**[D] Forced monomials.** Take ≈ cn/(2Δ) bundles and in each the clauses whose y-variables occur in no other chosen
clause (a (1 − O(c)) fraction, for small c). For most such choices every subset Π′ of the resulting set Π₀ is a
violation set: make false exactly the guards of the bundles that meet Π′, make both y-literals false in the clauses
of Π′, and satisfy the other clauses of those bundles by the remaining y-variables (a sparse 2-CNF with ≈ c²n
constrained clauses). |Π₀| ≈ cn/2. By Lemma P(i) every pointwise-exact mark polynomial for H contains all these
monomials with coefficient ±1, whatever its checks.

**[R] In the clause-mark model** of `sat-width.md` §2.1 (a marked object is shared by equality of mark strings on
its tests; Lemma A there: a pair pays the logarithm of the number of strings that occur), a pair {a,b} pays, in a
profile, at least log(number of traces, on the clauses with a test at {a,b}, of the forced monomials that have a
retained term in this profile). Indeed the terms whose marked clauses are exactly Π′ sum to the coefficient of
v^{Π′}; if that is nonzero one of them is retained, and its strings determine the traces of Π′. This applies to the
truncated polynomials of both papers as well: truncation changes a coefficient by a multiple of 2^ν, so a
coefficient ±1 stays nonzero.

**[D] For H** the clauses on one pair of nodes come from different bundles (random placement on g = n^{Ω(1)}
nodes), and almost every choice of μ_ab of them extends to a forced set with prescribed trace sizes on the other
pairs (the constraints of the previous paragraph are met by most choices). So the pair pays
log C(t_ab, μ_ab) − o(·), and in total

  U ≥ (k−1)·Σ_{a<b} log C(t_ab, μ_ab) ≈ (cn/2)·log(Δ/c) = Ω(n log Δ),

for every pointwise-exact polynomial: plain inclusion–exclusion, parity checks of any shape, isolation checks, the
level identity. The joint description of a forced monomial costs only (n/2Δ)·log Δ + n/2 bits (which bundles, then
which of their clauses). The n log Δ arises because the Δ clause-holders of a bundle are Δ different nodes, each of
which must learn, on its own wire, that this bundle is active: **one bit of the guard's node, read by Δ nodes, is
paid Δ times at log Δ/Δ each instead of once.**

## 7. Route 4: a reduction that keeps m + n = O(n); multi-reader wires

**Counting [R].** The 3-CNFs with n variables and Dn clauses (D ≤ n), all literals negative, have
2^{Θ(Dn log n)} different solution sets (the clauses are the minimal forbidden triples). There are 2^{O(Cn log n)}
pairs (formula with n′ + m′ ≤ Cn, choice of n of its variables). So no reduction to a single instance with
m′ + n′ = O(n) whose solutions project onto the solutions of the input exists for D → ∞, with or without new
variables; a reduction must branch, and §2 covers branching without new variables. With new variables I found
no construction beyond special cases (T(b,J) has a linear-size encoding with counters; H has none that I can see:
its information content is nΔ·log n bits).

**Reformulation [R].** Call a *hyperwire* a bit read by up to d nodes. A k-CNF with n variables is a network of
clause nodes joined by n hyperwires with d = max occurrence. Conversely a network of bounded-arity integer tables on
n hyperwires is a #CSP with n variables. So (T) is the statement

> (HW) networks of bounded-arity tables on n hyperwires, each read by at most (log n)^{O(1)} nodes, are evaluated
> in 2^{O(n/√log n)}

restricted to clause tables. A hyperwire read by d nodes is a tree of d − 1 ordinary wires, which is where
e·n·D comes from; marks use that a clause table is 1 − (rank one) and reach e·n·log D.

**Calibration [D].** For arbitrary tables and d of the order of the number K of nodes, (HW) contains: a 2-CSP on V
variables with domain N and a constraint on every pair, in N^{O(V/√log V)}, i.e. V-clique in N^{o(V)}. The two
engines give this only for constraint graphs with O(V) edges (cost e·log N per variable and constraint). Marks do
not help there: the density of forbidden pairs is N^{Θ(1)}, so the address costs Θ(log N) per mark and the saving is
lost unless log N ≪ √log n. So the gap between "bits × readers" and "bits" is the gap between sparse and dense
2-CSPs; Boolean CNFs sit at its mild end only because sparsification brings the number of readers down to
(log n)^{O(1)}.

**In the deformation engine (OA-ETH App. on contraction) [C, speculative].** If its top-level expansion held with
hyperwires as the units, a hyperwire with readers in all 8 groups would survive in every child (as 8 independent
hyperwires of degree d/8), so the number of units would not fall for log₈ d levels while the valuation budget u
halves: exponent ≈ n·d^{1/6}/√log n. That beats e·n·d but not e·n·log d. I did not verify that the expansion
generalises.

## 8. Route 5: is the factor necessary?

**Rank arguments cannot show it [R].** Put the variables on K nodes, n/K each. For every bipartition of the nodes
the solution tensor has rank ≤ 2^{min(|A|,|B|)·n/K}, and its tensor rank is ≤ 2^{n(1−1/K)}. A network with total U
has capacity ≈ U·|A||B|/K² across a balanced-degree cut and tensor rank ≤ 2^{U/2}. So cut-rank and tensor-rank
bounds are satisfied by U = 2n for every formula, and by every placement. A lower bound of the form
U = ω(n) for networks of the variable-partition form would need a method that sees the incidence structure (which
node reads which wire), and none is known for tensor networks in general.

**In the clause-mark model** the bound Θ(k n log D) is tight: `sat-width.md` Theorem K for family-based kills, and
§6.3 here for all pointwise-exact polynomials on H.

**Dense formulas, m = Θ(n³).** These are not the hard case. The factor is log of the density *after*
sparsification; the hard densities are 1 ≪ D ≲ √log n·log log n, where sparsification does nothing (§6.2). For
D above the sunflower thresholds the branching of the sparsifier is cheaper than the marks.

## 9. Decision instead of counting

[X] (i) Positive expansions [D]: ∏_E (number of true literals of E) is positive exactly on satisfying
assignments, and truncating a positive expansion is harmless, so no kill and no precision are needed. A term is a
selector (one literal per clause) that deviates from a default selector in ≤ n/log D clauses; the truncated sum is
positive iff some satisfying assignment falsifies ≤ n/log D of the default's selected literals. When a variable is
selected in ≈ D clauses this means that the default already agrees with a solution on all but O(n/(D log D)) of the
selected variables; a family of defaults chosen without knowing a solution needs 2^{n(1−O(log D/D))} members to
cover a unique solution, and producing a good default is the search problem itself. (ii) Isolation: a linear-size
pairwise-independent hash ([K], recalled, not re-read) keeps m + n within a constant factor and reduces the
precision to one bit, but by Lemma W the number of checks, hence of marks, stays ≥ n/k − o(n). (iii) Nothing else
in the framework distinguishes decision from counting.

## 10. What would fix it

Ranked; "odds" = my probability that the item yields (T).

1. **Multi-reader wires in an engine** (odds 3–5%). Needed: a level identity for the equality tensor of d parties
   under the merges of the clique engine (AN-ETH Lemma 2 / Theorem B are for d = 2), with cost per bit independent
   of d for d ≤ polylog, or the analogue for the Cauchy deformation of OA-ETH. A 3-party bit is a restriction of
   two wires (round 2, item 8), so the first test is growth in d: compute, with the price method of the barrier
   paper (round 2's "Paper"), the price of a d-party equality on a g × g grid under the row and column merges, and
   see whether it is bounded in d. Example H is the test instance: with guards as hyperwires its total is
   n/2 + n/2.
2. **A notification scheme with cheap marginals for clause tables** (odds < 2%). By §6.3 it must leave the
   clause-mark model: the object shared on a wire cannot be the set of marked clauses of that wire.
3. **Sparsification with new variables to density (1/ε)^{o(1)}** (odds < 1%): no mechanism; H has none.
4. **Constants.** The level identity removes the checks on planted-type formulas; isolation checks remove the n
   precision marks; using #SAT(Φ₀) for a sparse Φ₀ ⊂ Φ as the bound on the answer lowers the precision to
   log #SAT(Φ₀) + 1. None changes the order.

## 11. Scripts (`research/sat3/loglog/`, all exact or deterministic with fixed seeds)

| script / output | content |
|---|---|
| `verify_identities.py` / `.out` | (A) Lemma L and its certificates, with a mutation test; (B) Lemma M; (C) Lemma V(i). All PASS. |
| `sparsify_lb.py` / `.out` | Lemma F: random and targeted search for counterexamples (none); the constants of S1, S2 against Calabro's bound. |
| `example_h.py` / `.out` | Example H: f_t, #SAT(Φ_t), N_t on small instances; the three costs of §6.2. |
| `cost_tables.py` / `.out` | (68) with the density; the ε-balance; the scale formula of §4.6; the planted tower of §5. |

## 12. What is used from the two papers

Nothing new is claimed as a theorem about running time. The statements [D] that mention a running time use, as
black boxes: AN-ETH Theorem D(a) with its Steps 1–4 (Lemma 12 cut-off, Lemma 13 family of checks, the network of
Step 3 and (68), (69)), Lemma 8 case (i), Theorem A(a),(b) and Theorem B (the pairs (K_ℓ, e_ℓ) with
e_ℓ = Θ((log K_ℓ)^{−1/2})); Lean statement `MainTheorem`. The level identity of §5 needs only Step 3's network with
kind-0 objects and Step 4. From OA-ETH only the statements quoted in §1 and Theorem `thm:tensor-contraction` (in the
speculative paragraph of §7). Propositions S1, S2 and Lemmas F, L, M, N, P, V, W are self-contained; Lemma W uses
Warning's second theorem.
