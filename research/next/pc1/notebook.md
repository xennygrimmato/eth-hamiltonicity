# pc1 notebook: restricted BSS models in which the cofactor is controlled

24 Nov 2026. Researcher pc1. Inputs: y2 (L1–L3), y1 (root tracking, §4.3), review-pc.md (referee), [T26].
Tags: **[R]** proved here, full proof given / **[K]** known, cited / **[N]** computed (`checks.py`, output `checks.out`) /
**[C]** conjecture or open. Nothing here proves P_ℂ ≠ NP_ℂ.

## 0. Results in one screen

| # | Statement | Tag |
|---|---|---|
| A | **Fewnomial-in-y tests.** A nonzero f = Σ_{j≤τ} A_j(x)·y^{β_j} (A_j ∈ ℂ[x] arbitrary, exponents arbitrary) vanishes on at most τ−1 of the nonzero Ryser branches y = g_E. Hence a tree deciding A_g whose generic-path tests are products of ≤ m polynomials with ≤ τ powers of y each satisfies T·m·(τ−1) ≥ 2^n−1. No [T26]; every characteristic. Generalises the idea agent's ΠΣ-sparse theorem. | [R] §2 |
| B | **Trace cofactor lemma.** If Q ≠ 0 has the Ryser branches as y-roots with multiplicities μ_E ≥ 0 and at most h other distinct y-roots (over the algebraic closure of ℂ(x); any multiplicity, any degree, any complexity), then L̄(Σ_E μ_E g_E) ≤ C(h+1)n³(L(Q)+n²). With μ ≡ const off h′ branches and [T26]: L(Q) ≥ n^{c(log n)^{1/3}}/(C′(h+h′+1)n³) − n². | [R] §3 |
| B′ | **Tight machines.** No tree of depth T decides A_g if for generic x at most h values of y leave the generic path without being accepted ("false alarms"), all but h′ branches are hit with one common multiplicity, and (h+h′+1)·T < n^{c(log n)^{1/3}}/poly(n). | [R] §3.4 |
| AB | **Mixed machines.** Tests may be of two kinds, y-sparse (≤ τ powers of y) or tight as a group; the bound holds with h replaced by h+h′+T·m(τ−1). | [R] §3.5 |
| σ | **Unified form.** For every multiple Q = N_g·H: the degree-n Taylor germ of the y-trace σ(H) = −H_{k−1}/H_k of the cofactor is border-hard unless L(Q) is. Contains y2's L3 (H easy) and B (H has few roots), and products of the two kinds. | [R] §3.6 |
| P | **Partial norms.** Subcube partial Ryser sums with f free coordinates project onto per_f, so the partial norm over every subcube of dimension ≥ n^ε is border-hard, as is every multiple of it with few extra roots. Arbitrary large E: open; the weighted form is the same obstacle as the multiplicity caveat of B. | [R]/[C] §4 |
| Φ | **Referee's test case** Φ = ∏(x_i + T^{2^{i−1}}): all power sums and elementary symmetric functions of order ≤ poly of its 2^n roots are easy, and N(x,0) is easy, so [T26] is blind to it. Its weighted sibling (subset-sum weights) is a border-hard cyclic norm. Easiness of the test-case norm: undecided. | [R]/[C] §5 |

What each theorem does **not** give: A and B′ are lower bounds against *restricted* machines only. An unrestricted
polynomial-time machine may test y-dense polynomials with exponentially many false alarms; nothing here touches it.

## 1. Model and conventions

- g is the Ryser family of y2 §1: for E ⊆ [n], g_E = (−1)^{n+|E|} ∏_{i=1}^n ℓ_{i,E}, ℓ_{i,E} = Σ_{j∈E} x_ij, g_∅ = 0.
  The 2^n polynomials g_E are pairwise distinct, homogeneous of degree n (E ≠ ∅), real, and Σ_E g_E = per_n.
  N_g = ∏_E (y − g_E), A_g = Z(N_g) ⊂ ℂ^{n²+1}, A_g ∈ NP_ℂ (uniform, constant-free, Boolean witness).
- **Machine.** An algebraic computation tree over ℂ of depth T: operations +, −, ×, ÷, arbitrary complex constants, tests
  "v = 0?", every divisor tested first. A time-T BSS machine on inputs of size n²+1 unrolls into such a tree.
- **Generic path** (L1, refereed): the path followed by a generic input. Tested values v_1, …, v_r (r ≤ T) on it that are
  not identically zero are rational functions of (x,y); in L1's representation v_i = a_i/b_i with b_i a product of
  earlier a's. P := ∏ a_i, L(P) ≤ 5T.
  - Z(P) is exactly the set of inputs that leave the generic path (at the first i with a_i(z) = 0 one has b_i(z) ≠ 0, so
    v_i(z) = 0).
  - The generic leaf rejects, so A_g ⊆ Z(P): every y − g_E divides some a_i. For the least such i, y − g_E does not divide
    b_i, so **y − g_E divides the reduced numerator of the tested value v_i**.
- **False alarm**: an input that leaves the generic path and is rejected. For generic x the number of y with
  P(x,y) = 0 is 2^n + FA(x); FA := its generic value = number of distinct y-roots of P over the closure of ℂ(x)
  that are not Ryser roots.
- [T26] in the form used (y1 §1.1): L̄(per_n) ≥ (n^{c(log n)^{1/3}} − n²)/3 in operation count over ℂ((ε)).

## 2. Theorem A: tests that are products of polynomials with few powers of y

Two proofs of the key lemma are given. A.2 (valuations) is stronger and works in every characteristic; it grew out of the
**idea agent's Newton-polygon theorem** (relayed by the lead; file `research/next/ideas-span.md`), which I checked and
then generalised: sparsity in x is not needed, only the number of powers of y. A.1 (Descartes) was my first proof.

**Lemma A.1 [R] (Descartes; real root families).** Let ρ_1, …, ρ_N ∈ ℝ[x] be pairwise distinct nonzero polynomials. Let
f = Σ_{j=1}^τ A_j(x) y^{β_j} ≠ 0 with A_j ∈ ℂ[x] and distinct β_j ∈ ℕ. Then f(x, ρ_k(x)) = 0 for at most 2τ − 2 indices k.

*Proof.* Suppose f(x, ρ_k) = 0 for k ∈ K with |K| ≥ 2τ − 1. Let G := A_{j0} · ∏_{k∈K} ρ_k · ∏_{k<k′∈K}(ρ_k − ρ_{k′}) for some
A_{j0} ≠ 0. G is a nonzero polynomial over ℂ, so it does not vanish identically on ℝ^m. Fix X⁰ ∈ ℝ^m with G(X⁰) ≠ 0. Then
φ(y) := f(X⁰, y) is a nonzero complex polynomial with at most τ terms that vanishes at the 2τ − 1 distinct nonzero real
numbers ρ_k(X⁰). Write φ = φ_1 + iφ_2 with φ_1, φ_2 ∈ ℝ[y]; both vanish at these points, both have at most τ terms, one is
nonzero. By Descartes' rule a nonzero real polynomial with τ terms has at most τ − 1 positive and at most τ − 1
negative roots. Contradiction. ∎

**Lemma A.2 [R] (valuations; Ryser roots; any field k).** Let f = Σ_{j=1}^τ A_j(x) y^{β_j} ≠ 0 with A_j ∈ k[x], distinct β_j.
Then y − g_E divides f for at most τ − 1 nonempty E.

*Proof.* Let K := k(u)((t)) with u = (u_ij) indeterminates and t-adic valuation v. Substitute x_ij ↦ u_ij·t^{w_ij} with
w_ij := 2^i if j ≠ i and w_ii := 0. This is an injective ring map ι: k[x] → K (it sends distinct monomials to distinct
monomials in u times a power of t), so f̃ := Σ_j ι(A_j) y^{β_j} ∈ K[y] is nonzero with at most τ terms.
- *Valuation of the roots.* ι(ℓ_{i,E}) = Σ_{j∈E} u_ij t^{w_ij}. Its lowest power of t has coefficient a nonempty sum of
  distinct indeterminates, which is nonzero, so v(ι ℓ_{i,E}) = min_{j∈E} w_ij = 0 if i ∈ E and 2^i if i ∉ E. Hence
  v(ι g_E) = Σ_{i∉E} 2^i for E ≠ ∅. These 2^n − 1 integers are pairwise distinct (binary expansion).
- *Newton polygon.* A nonzero polynomial over a valued field with at most τ terms has a lower Newton polygon with at
  most τ − 1 edges of finite slope, and the valuation of every nonzero root in K̄ is minus one of these slopes. So the
  nonzero roots of f̃ take at most τ − 1 distinct valuations.
- If y − g_E | f then ι(g_E) is a nonzero root of f̃. Distinct E give distinct valuations. ∎

(Check of the relayed sketch. Step (1) "the root valuations of N_g·H contain those of N_g" is trivially right, and it
is all that is needed: each branch must be a root of some factor of some test, and a factor catches at most as many
branches as it has distinct root valuations. There is no cancellation in v(g_E) because the u_ij are independent. For
step (2) the weights above make distinctness a one-line proof; I did not check the idea agent's weights
(n+1)^i((j−i) mod n). Multiplicities are irrelevant throughout.)

**Definition.** A polynomial has *y-sparsity* ≤ τ if it has at most τ distinct powers of y (coefficients in ℂ[x]
arbitrary). It is at most deg_y + 1 and at most the number of monomials. A rational function has *ΠΣ_y-width* ≤ (m, τ)
if its reduced numerator is a product of at most m polynomials (with arbitrary multiplicities), each of y-sparsity ≤ τ.

**Theorem A [R].** Let a tree decide A_g (Ryser g) and let every tested value on the generic path have ΠΣ_y-width
≤ (m, τ), τ ≥ 2. Then the generic path contains at least (2^n − 1)/(m(τ − 1)) tests; in particular
**T·m·(τ − 1) ≥ 2^n − 1.** The same holds over every algebraically closed field.

*Proof.* By §1 each of the 2^n − 1 nonzero branches divides the reduced numerator of some tested value, hence (y − g_E is
irreducible) one of its ≤ m factors; by Lemma A.2 each factor takes at most τ − 1 branches. ∎

This contains: tests of y-degree ≤ Δ (m = 1, τ = Δ+1; the lead's candidate (c)); sparse tests of any degree; the idea
agent's ΠΣ-sparse model (products of m powers of t-sparse polynomials: T·m·(t−1) ≥ 2^n − 1, same constant), without
needing sparsity in x; and y-lacunary tests Σ_j A_j(x)y^{β_j} with A_j of arbitrary degree and complexity.

**Exact comparison with the idea agent's Theorem S** (`ideas-span.md`: ≤ R factors with ≤ t monomials each ⇒
R(t−1) ≥ 2^n − 1). One proof gives both: Lemma A.2 is the Newton-polygon argument of Theorem S with the observation
that only the number of powers of *y* enters, because the polygon is taken in y over the valued field k(u)((t)) and the
x-coefficients may be anything nonzero. So Theorem A ⊇ Theorem S: same constant, products and multiplicities handled,
cofactor-blind, every characteristic, and no sparsity in x. With "t-sparse" read as "≤ t powers of y" (as the idea
agent's note allows) the two statements coincide. The Descartes proof A.1 is weaker for Ryser roots (constant 2τ−2,
characteristic 0, real root family) and is kept only because it also covers root families that no valuation separates
(Knapsack). The idea agent's Theorems 2T, S′ and G (two-term cancellation, cancellation-free depth hierarchy, gadget)
go beyond Theorem A; I have not refereed them.

**Slope count as a complexity measure [R + idea agent].** Define sl(f) := number of distinct valuations of nonzero roots
of ι(f). Then sl(fg) ≤ sl(f) + sl(g), sl(f^a) = sl(f), sl(f) ≤ (y-sparsity) − 1, and any tree deciding A_g has
Σ_{tests} sl ≥ 2^n − 1. Sums are the only operation that can create slopes. The idea agent's gadget (G_0 = y, H_0 = 1,
G_{k+1} = t^{ε_k}(G_k + H_k)², H_{k+1} = G_kH_k, Q_n = G_n + H_n; not re-verified by me) has size O(n) and 2^n slopes, so no
slope bound holds for general circuits. **Consequence for Theorem B:** a tropical re-proof is not possible. Valuations
are multiplicity-blind, which is why Theorem A has no multiplicity caveat, but the slope set of Q only records *that*
2^n − 1 branches are present, never their sum; hardness of per enters Theorem B through the trace, which has no
tropical shadow. If the gadget's slope set can be made to contain {Σ_{i∉E}2^i} = all even numbers in [0, 2^{n+1}) (this is
the Newton polygon of a q-Pochhammer ∏_k(y − t^{2k})), then **no valuation-only argument can prove Gap G** [C; question
passed to the idea agent].

Remarks.
- (i) No hardness input. Lemma A.1 works for every family g with real coefficients and pairwise distinct g_e, e.g.
  Knapsack g_e = Σ x_i e_i over ℂ (bound 2τ − 2). Lemma A.2 needs a valuation separating the roots; for Knapsack take
  x_i ↦ u_i t^{2^i}: v(g_e) = 2^{min supp e} takes only n values, so A.2 gives nothing there and A.1 is the right tool.
- (ii) It contains the lead's candidate (c): deg_y ≤ Δ gives τ ≤ Δ + 1 and T ≥ (2^n−1)/Δ. It is strictly more general:
  the y-degree is unrestricted. Tests such as y^D − u(x)^D, or any polynomial with ≤ τ monomials of arbitrary degree,
  or Σ_j A_j(x)y^{β_j} with A_j of any degree and complexity, catch at most τ − 1 branches.
- (iii) Consequence for the full problem: **a polynomial-time machine for A_g must test, on its generic path, a value
  whose numerator is not a product of polynomially many polynomials with fewer than 2^n/poly(n) powers of y each.**
- (iv) Edge cases. Divisions: handled by passing to reduced numerators (§1). Tests not involving y: τ = 1, they catch
  no nonzero branch. Multiplicities play no role. τ = 1 in general: A(x)y^β vanishes on no nonzero branch.
  The branch g_∅ = 0 is not counted.
- (v) What the proof cannot do. Replacing "number of y-powers" by "number of additions involving y" fails for the
  counting method over ℂ: (y + iu)^D − (y − iu)^D uses three additions and has the D − 1 real-on-real roots
  u·cot(kπ/D). Those roots span a line, so this is not a counterexample to a statement about Ryser roots; it only shows
  that Descartes-type counting needs real structure. With *real* base polynomials the Wronskian bounds of
  Koiran–Portier–Tavenas (J. Symb. Comput. 2015, "A Wronskian approach to the real τ-conjecture") bound the real roots
  of Σ_{j≤τ} c_j ∏_{i≤k} q_i^{β_ij} polynomially in τ, k, deg q_i **[K, statement from memory, not re-read]**; the proof of
  Lemma A.1 would then extend to tests Σ_j A_j(x) ∏_i q_i(x,y)^{β_ij} with q_i ∈ ℝ[x,y] of bounded y-degree. I did not
  pursue this because real bases are not a natural restriction for a machine over ℂ.
- (vi) Dead variant (recorded): an algebraic Wronskian/valuation argument on a generic line (in the style of
  Chattopadhyay–Grenet–Koiran–Portier–Strozecki) reproves Lemma A.1 for sparse f without real numbers, and extends to bases
  q_i(x) not involving y. For bases involving y it needs each q_i(x, g_E(x)) to have a "private" zero, and the count is
  false without it: (y − u)^D − w^D has the D roots u + ζw. Lemmas A.1/A.2 already cover everything that argument reached.

## 3. Theorem B: few extra roots (uses [T26])

### 3.1 Statement

For a nonzero Q ∈ ℂ[x,y] with k := deg_y Q ≥ 1 write Q = Σ_j Q_j(x) y^j and, over the algebraic closure of ℂ(x),
Q = Q_k ∏_{ρ}(y − ρ)^{μ_ρ} (ρ distinct). The *trace* is Σ(Q) := Σ_ρ μ_ρ ρ = −Q_{k−1}/Q_k ∈ ℂ(x).

**Theorem B [R].** Let Q ≠ 0, s := L(Q). Let μ_E ≥ 0 be the multiplicity of y − g_E in Q, and let h be the number of
distinct y-roots of Q that are not Ryser roots. Then

  L̄(Σ_E μ_E g_E) ≤ C·(h + 1)·n³·(s + n²)  for an absolute constant C.

No assumption on deg Q, on the multiplicities or the degrees of the other roots, or on the complexity of the cofactor.

**Corollary B1 [R + T26].** If moreover μ_E = μ ≥ 1 for all but h′ of the E, then
(h + h′ + 1)(s + n²) ≥ n^{c(log n)^{1/3}}/(C′n³) for large n. In particular every multiple Q = c(x)·N_g^μ·H in which H has
at most n^{O(1)} distinct y-roots has superpolynomial L(Q). This answers candidate (a): **deg_y Q ≤ 2^n + h forces
L(Q)·(h+1) ≥ n^{c(log n)^{1/3}}/poly(n)**; the cofactor of an easy multiple must have superpolynomially many *distinct*
roots in y. (y2's Cor. 3.2 needed polynomially many factors of polynomial *total* degree; here the x-degree and the
complexity of the extra factors are arbitrary, and a factor c(x) is free.)

### 3.2 Step 1: the trace of an easy polynomial is border-easy

**Lemma B.1 [R].** For Q ≠ 0 with L(Q) = s and generic a ∈ ℂ^m, the degree-≤ d Taylor polynomial of Σ(Q) at a is
approximable (in the sense of [T26]) with O(d²(s + m)) operations.

*Proof.* Over 𝕂 = ℂ((δ)) put R(x) := (−δ)^k Q(x, −1/δ) = Σ_j Q_j(x)(−δ)^{k−j} ∈ ℂ[δ][x], computed with s + 1 operations
(the constants −1/δ and (−δ)^k are free). R = Q_k·∏_ρ(1 + δρ)^{μ_ρ} = Q_k·(1 + δΣ(Q) + δ²c_2 + …) with c_i ∈ ℂ[x][1/Q_k].
Let R₂ be the same with δ replaced by δ². Then

  R/R₂ = (1 + δΣ(Q) + δ²c_2 + …)/(1 + δ²Σ(Q) + …) = 1 + δ·Σ(Q) + δ²·(element of ℂ[x][1/Q_k][[δ]]).

Choose a with Q_k(a) ≠ 0. Then R₂(a) = Q_k(a) + O(δ²) ≠ 0 in 𝕂, so Strassen's division elimination at a applies to the
single division R/R₂: carry every gate as its Taylor expansion in z = x − a truncated at degree d, at O(d²) operations
per gate. Every element of ℂ[x][1/Q_k] has a Taylor expansion at a with complex coefficients, so the result is
1 + δ·trunc_d Σ(Q)(a+z) + δ²·w with w ∈ ℂ[[δ]][z]. Subtract 1, multiply by δ^{−1}. ∎

(For Q = N_g this is y2's L2(b); for Q = N_g·H with H given it is L3; here nothing about the cofactor is used, and what
comes out is the trace of *all* roots.)

### 3.3 Step 2: one root of an easy polynomial is border-easy, at any multiplicity

**Lemma B.2 [R; this is y1 §4.3 (Bürgisser's perturbation) with no witness variables].** Let ρ be a y-root of Q of
multiplicity μ ≥ 1 and a ∈ ℂ^m generic. The degree-≤ d Taylor polynomial of ρ at a is approximable with O(d³(s + m))
operations.

*Proof.* Genericity of a: Q_k(a) ≠ 0 and the discriminant of the squarefree part of Q (in y) does not vanish at a. Then
the distinct roots of Q are analytic near a with distinct values, and near (a, y_0), y_0 := ρ(a),
Q = U(x,y)·(y − ρ(x))^μ with U analytic, U(a,y_0) ≠ 0. Let c_ε := Q(a, y_0 + ε) = U(a,y_0+ε)ε^μ and

  F(z, Y) := Q(a + z, Y + ε) − c_ε  over 𝕂 = ℂ((ε)).

- F(0, y_0) = 0 and J := ∂_Y F(0, y_0) = ∂_yQ(a, y_0+ε) = μU(a,y_0)ε^{μ−1} + O(ε^μ) ≠ 0 in 𝕂 (characteristic 0).
- Hensel: there is a unique Y*(z) ∈ 𝕂[[z]] with Y*(0) = y_0, F(z, Y*) = 0. The chord iteration Y ← Y − J^{−1}F(z,Y) from
  Y = y_0 satisfies Y_ν ≡ Y* mod (z)^{ν+1}: the error e obeys e ← e·(1 − J^{−1}∂_YF(z,Y*)) + O(e²) and the bracket lies
  in (z). J^{−1} is a constant of 𝕂, so there is no division gate. d + 1 iterations, each one evaluation of Q on
  series truncated at degree d: O(d²(s+m)) each.
- The coefficients of Y* lie in ℂ[[ε]] and reduce to those of ρ(a+z). Let V := U^{1/μ} near (a,y_0) and
  Θ(x, ε, Y) := V(x, Y+ε)(Y + ε − ρ(x)) − V(a, y_0+ε)·ε. Then Θ(a, ε, y_0) ≡ 0 and ∂_YΘ(a,0,y_0) = V(a,y_0) ≠ 0. By the
  implicit function theorem there is an analytic S(x, ε) with Θ(x,ε,S) = 0, S(a,ε) = y_0. Raising to the μ-th power,
  Q(x, S+ε) = c_ε, so S(a+z, ε), expanded in z with coefficients in ℂ{ε}, is a solution of F = 0 with constant term y_0;
  by uniqueness it is Y*. At ε = 0: V(x,S)(S − ρ(x)) = 0, so S(x,0) = ρ(x). ∎

### 3.4 Proof of Theorem B, and the machine form

*Proof of Theorem B.* Take d = n and a generic. Σ(Q) = Σ_E μ_E g_E + Σ_{l≤h} e_l ρ_l near a, where ρ_l are the non-Ryser
roots and e_l their multiplicities. Σ_E μ_E g_E is a polynomial of degree ≤ n, so it equals its own Taylor polynomial.
Hence Σ_E μ_E g_E(a+z) = trunc_n Σ(Q)(a+z) − Σ_l e_l·trunc_n ρ_l(a+z). Approximate the first term by B.1 and each of
the h others by B.2 (same border parameter δ = ε; integers e_l are constants), then substitute z = x − a. ∎

*Proof of B1.* Σ_E μ_E g_E = μ·per_n + Σ_{E exceptional}(μ_E − μ)g_E; each g_E costs O(n²). Divide by μ and use [T26]. ∎

**Definition (tight machine).** A tree deciding A_g is *(h, h′)-tight* if (i) FA ≤ h: for generic x at most h values of
y leave the generic path without being accepted; (ii) there is μ ≥ 1 such that all but h′ of the factors y − g_E divide
P exactly μ times. Condition (i) is semantic. Condition (ii) is syntactic; it holds with μ = 1, h′ = 0 when every
branch is caught by exactly one test and transversally (the test numerator is squarefree along the branch) —
"unambiguous" machines.

**Theorem B′ [R + T26].** An (h, h′)-tight tree deciding A_g has depth T with
(h + h′ + 1)(5T + n²) ≥ n^{c(log n)^{1/3}}/(C′n³). So no polynomial-time BSS machine decides A_g with polynomially many
false alarms and polynomially many non-uniformly-hit branches.

*Proof.* Apply B1 to Q = P, L(P) ≤ 5T; the non-Ryser distinct roots of P number FA ≤ h (§1). ∎

Why the restriction is natural: a decision procedure of the form "compute a certificate polynomial that vanishes
exactly on A_g, up to few spurious zeros" is tight. Every algorithm that decides A_g by evaluating N_g, N_g times a
polynomial in x, or N_g times a few correction factors, is covered. What is not covered: procedures whose first
non-generic test has exponentially many spurious zeros per x (as y^D − 1 has for a hard half of its roots).

**The multiplicity caveat (open, O1).** Without (ii) the proof yields a border-easy *weighted* sum Σ_E μ_E g_E with
unknown positive integers μ_E, and I cannot show that every such sum is hard.
- The lead's Glynn-form computation (checked): with branches δ ∈ {±1}^n, g_δ = (∏δ_k)∏_iΣ_jδ_jx_ij,
  Σ_δ μ_δ g_δ = Σ_{f:[n]→[n]} μ̂(a(f)) ∏_i x_{if(i)}, a(f)_j = parity of 1 + |f^{−1}(j)|. So per_n appears with coefficient
  μ̂(0) = Σμ_δ > 0 and never cancels; the contamination is supported on non-bijective f.
- Removing the contamination means extracting the part that is multilinear in the columns. Every way I know costs 2^n:
  inclusion–exclusion over columns (Ryser itself), nilpotent column variables θ_j² = 0 (algebra of dimension 2^n),
  averaging over the 2^n column sign flips. A product over a subgroup Γ of flips makes μ Γ-invariant at cost |Γ|, which
  leaves μ̂ supported on Γ^⊥, still of size 2^n/|Γ|.
- Multiplicity-blind functionals: the denominator of ∂_yQ/Q is rad(Q), but any finite number of coefficients at y = ∞
  only sees μ-weighted power sums; recovering rad(Q) is a Padé problem of exponential order. gcd(Q, ∂_yQ) needs gcds at
  exponential degree. Both dead as far as I can see.

### 3.5 Mixed machines

**Theorem AB [R + T26].** Let a tree of depth T decide A_g. Split the generic-path tests into two groups: group S, each
of ΠΣ_y-width ≤ (m, τ); group R, with product P_R. Suppose P_R has at most h distinct non-Ryser y-roots, and all Ryser
branches dividing P_R do so with one multiplicity μ except h′ of them. Then
(h + h′ + T·m(τ−1) + 1)(5T + n²) ≥ n^{c(log n)^{1/3}}/(C′n³).

*Proof.* Group S catches at most T·m(τ−1) nonzero branches (Lemma A.2). Every other branch divides P_R. Apply Theorem B to
P_R (L(P_R) ≤ 5T) and add the at most T·m(τ−1) missing g_E and h′ corrections explicitly, O(n²) each. ∎

### 3.6 Unified form: the trace germ of the cofactor

**Proposition σ [R].** Let Q = N_g·H ≠ 0 and let t_H := trunc_n at a generic point of σ(H) := Σ(H), the trace of the
cofactor. Then per_n(a+z) = trunc_nΣ(Q) − t_H, hence L̄(t_H) ≥ L̄(per_n) − O(n²(L(Q) + n²)).
So **for every easy multiple, the degree-n germ of the trace of the cofactor is border-hard.**

It implies: L3 (if H is easy, B.1 applied to H makes t_H easy); Theorem B (if H has h distinct roots, B.2 makes t_H
cost O(hn³L(Q))); and mixtures H = H_1·H_2 with H_1 easy and H_2 having few roots (the trace is additive). This is the
sharpest form of "the cofactor is the whole problem" I have: the obstruction is one explicit germ of degree n, the
sum of the spurious roots.

### 3.7 Candidates (b) and (d)

- **(b) products of low-degree factors.** If a test is given as an explicit product of polynomially many factors of
  y-degree ≤ Δ it has y-degree ≤ poly and Theorem A applies. If only its irreducible factors are assumed to have degree
  ≤ Δ (exponentially many of them, computed implicitly), then by Bürgisser's Thm 1.3 each factor is border-easy, but
  σ(H) = Σ_j a_jσ(h_j) is again a sum over exponentially many easy terms, i.e. an instance of the same problem.
  Theorem B closes exactly the sub-case where the non-Ryser factors have polynomially many roots in total. **Not closed
  in general; no theorem.**
- **(d) constant-free machines.** Nothing new. Constants are irrelevant (Koiran; B4 of the ideas file); after
  specialising x to integers a constant-free Q gives an integer polynomial with 2^n integer roots, which is the
  τ-conjecture situation. Lemma A.1 is the y-fewnomial case of that statement, proved by Descartes.

## 4. Partial norms (secondary target)

For 𝓔 ⊆ 2^{[n]} let N_𝓔 := ∏_{E∈𝓔}(y − g_E), S_𝓔 := Σ_{E∈𝓔} g_E. By y2 L2(b), L̄(S_𝓔) ≤ L̄(N_𝓔) + 3; by Theorem B the same
holds up to the factor C(h+1)n³ for every multiple of N_𝓔 with h extra roots and simple Ryser hits.

**Proposition P1 (subcubes) [R, N for n = 3].** Let 𝓔 be a subcube: e_j = 1 for j ∈ J_1, e_j = 0 for j ∈ J_0, free on F,
|F| = f ≥ 1. Then per_f is obtained from S_𝓔 by a substitution (J_1 ≠ ∅) or as a difference of two substitutions
(J_1 = ∅). Hence L̄(N_𝓔) ≥ ½·L̄(per_f) − O(1): **the partial norm of every subcube of dimension f ≥ n^ε is border-hard**
given [T26].

*Proof.* With c_i := ℓ_{i,J_1}: S_𝓔 = ±Σ_{E′⊆F}(−1)^{f−|E′|}∏_i(c_i + ℓ_{i,E′}) = ±Σ_σ ∏_i x′_{iσ(i)}, the sum over maps
σ: [n] → F ∪ {*} whose image contains F, with x′_{i*} = c_i (inclusion–exclusion over F).
- J_1 ≠ ∅: put, for i ≤ f, x_ij = Y_ij on F and 0 elsewhere; for i > f, x_ij = 0 on F and c_i = 1. Rows i > f must go to *,
  rows i ≤ f must go to F bijectively: S_𝓔 ↦ ±per_f(Y).
- J_1 = ∅ (so n > f): fix j_0 ∈ F; rows i > f are the unit vector at j_0; rows i ≤ f carry Y with column j_0 multiplied
  by z. Maps of the first f rows whose image contains F∖{j_0} send at most one row to j_0, so S_𝓔 ↦ ±(z·per_f(Y) + R_0(Y))
  and per_f = ±(S|_{z=1} − S|_{z=0}). ∎

A subcube has |𝓔| ≥ 2^n/poly(n) iff its codimension is O(log n), so all "large" subcubes are covered, and much smaller
ones too. So a structured sub-product over a subcube is **not** an easy partial norm.

**P2 (what the machine gives) [R].** By pigeonhole some generic-path test numerator is a nonzero multiple of N_𝓔 for a
set 𝓔 with |𝓔| ≥ 2^n/T. Nothing controls the shape of 𝓔 or the cofactor.

**P3 (arbitrary large 𝓔) [C].** I can neither prove nor refute "S_𝓔 is border-hard for every 𝓔 with |𝓔| ≥ 2^n/poly".
- In the basis of monomials x^σ (σ: [n] → [n]), S_𝓔 = Σ_σ ŵ(im σ)x^σ with ŵ(J) = Σ_{E⊇J, E∈𝓔}(−1)^{n−|E|}.
- For 𝓔 symmetric (depending on |E| only) S_𝓔 = Σ_j c_j P_j, P_j := Σ_{|im σ|=j} x^σ. The mechanisms I know that make such
  a combination easy (c_j a polynomial in j of bounded degree; c supported on bounded j) force 𝓔 to consist of sets of
  size ≥ n − O(1), i.e. |𝓔| = poly. So no easy large symmetric partial sum arises this way.
- Undecided concrete case: 𝓔 = sets of even size. S_even = (R ± per_n)/2 with R = Σ_σ 2^{n−|im σ|}x^σ; hard unless R is
  ∓per + easy, which is implausible but not excluded by anything proved here.
- The weighted version (integer weights μ_E ≥ 1) is exactly the multiplicity caveat O1 of §3.4.

## 5. The referee's test case and a hard cyclic norm

Φ(x,T) = ∏_{i=1}^n (x_i + T^{2^{i−1}}), M = 2^n, roots r_ω = Φ(x, ω) for ω^M = 1, N_Φ := ∏_ω (y − r_ω). The 2^n roots span the
2^n multilinear monomials (referee).

**Fact Φ1 [R, N].** For every k, p_k := Σ_ω r_ω^k has a circuit of size O(nk²): p_k = M·Σ_l [T^{lM}]Φ^k, and
[T^{lM}]∏_i(x_i + T^{2^{i−1}})^k = Σ over digits a_i ∈ {0..k} with Σa_i2^{i−1} = lM of ∏_i C(k,a_i)x_i^{k−a_i} is a product of n
transfer matrices on carries c ∈ {0..k} (digit a_i ≡ c mod 2, new carry (c + a_i)/2, any final carry). Hence by
Newton's identities all elementary symmetric functions e_k of the roots, k ≤ poly, are easy. Also
N_Φ(x,0) = ±∏_ω∏_i(x_i + ω^{2^{i−1}}) = ±∏_i(x_i^{M/2^{i−1}} − (−1)^{M/2^{i−1}})^{2^{i−1}} is easy.

**Consequence.** Every hardness proof in this line (L2, L3, Theorem B, Prop. σ) reads a bounded-order coefficient at
y = ∞. For the test case these are all easy. **[T26] is blind to this family**: if its norm is hard, the reason is of
τ-conjecture type, not of permanent type. That is the precise sense in which it is a different animal from N_g.

**Fact Φ2 [R].** If only x_1, …, x_k are nonzero, r_ω = ω^{M−2^k}·ψ(ω) with deg ψ < 2^k and the norm costs poly(2^k)·n
(companion matrix, y2 §6(c)). So the family is easy for k = O(log n) active variables.

**Fact Φ3 [R, N for n = 2] (a hard cyclic norm).** Let B = n + 1, w_ij = B^{i−1} + B^{n+j−1}, W = Σ_{t<2n}B^t, M a power of 2
with M > nW, and Φ′(x,T) := T^{M−W}∏_{i,j≤n}(1 + x_ijT^{w_ij}). A set of pairs has weight W iff it is a perfect matching (no
carries in base B), and no other exponent of Φ′ is ≡ 0 mod M. So Σ_{ω^M=1}Φ′(x,ω) = M·per_n(x), and by y2 L2(b)
L̄(N_Φ′) ≥ L̄(per_n) − O(1): **a border-hard norm whose roots are indexed by the cyclic group μ_M**, with Φ′ of circuit
size O(n³). The set {(x,y): ∃ω, ω^M = 1, y = Φ′(x,ω)} is in NP_ℂ; L1, L3, Theorem B and Prop. σ apply to it verbatim
(d = n²). This shows that "cyclic norm of an easy Φ of exponential T-degree" is hard in general; the powers-of-two
weights of the test case are exactly the weights for which the coefficient extraction degenerates to a carry automaton.

**Verdict on the test case [C].** Undecided. I found no easy multiple: the recursion over the squaring tower
(t_{i+1} = t_i²) is G_{k+1}(u; t) = ∏_{s²=t}(x_{k+1}+s)^{2^k}G_k(u/(x_{k+1}+s); s), which needs G_k at two *different* arguments
and unfolds to all 2^n roots; enlarging the root set to independent t_i does not produce a binomial. And no hardness
proof can come from [T26] by Φ1. It is a clean candidate for "explicit family, all low symmetric functions easy,
exponential span, multiples conjecturally hard", but that is a conjecture.

## 6. What failed, and why

1. **Counting roots in models with y inside the bases** (tests Σ_j c_j∏_i q_i(x,y)^{β_ij}): false in general
   ((y−u)^D − w^D), and for Ryser roots it needs a private-zero property I could not establish. §2(vi).
2. **Additive complexity in y over ℂ**: counting fails with complex constants. §2(v).
3. **Removing multiplicities from the trace**: every route costs 2^n. §3.4.
4. **Implicit products of low-degree factors (b)**: same exponential-sum obstacle. §3.7.
5. **All large partial norms hard**: only subcubes (and complements of small sets) proved. §4.
6. **Test case**: neither easy nor hard established; [T26] cannot see it. §5.

## 7. Sharpest open statements

- **O1 (weighted Ryser).** For every μ: 2^{[n]} → ℤ_{≥1}, is Σ_E μ_E g_E border-hard given [T26]? A yes removes condition (ii)
  from B′ and leaves "few false alarms" as the only restriction. In Glynn form: is μ̂(0)·per + Σ_{a≠0}μ̂(a)F_a hard for
  every positive μ?
- **O2 (the gap, in trace form).** Gap G ⇔ for no easy Q with N_g | Q is trunc_n σ(Q/N_g) border-easy... more exactly:
  P_ℂ(nu) = NP_ℂ(nu) implies an easy Q whose cofactor has (a) some test that is not a short product of y-sparse polynomials (Thm A),
  (b) superpolynomially many distinct spurious roots (Thm B), (c) a border-hard trace germ (Prop. σ). Any argument
  showing that the spurious-root trace of an easy polynomial is border-easy *relative to the polynomial* proves
  P_ℂ ≠ NP_ℂ.
- **O3.** Is every multiple of the test-case norm N_Φ hard? (No VNP input can help.)

## 8. Files

- `checks.py` / `checks.out`: (1) trace identity for Q = c·N_g·H, n = 2, exact; (2) perturbed chord iteration recovers a
  triple root's Taylor coefficients as ε → 0, exact; (3) rank of generalized Vandermonde on 2τ−1 Ryser roots, numeric;
  (4) carry-DP power sums for the test case, n = 3, k ≤ 5, exact + numeric; (5) subcube projections onto per_2, n = 3,
  exact; (6) weighted cyclic family has trace M·per_2, exact.
