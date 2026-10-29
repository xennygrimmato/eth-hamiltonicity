# Sparse Fock spaces: can sub-partition growth (β < 1/2) carry two-order pieces?

Date 29 Oct 2026. Follows `rho-lower-bound.md` (Definition 3.1, Theorem 3.3, Lemma 4.1, Props 5.1–5.2, the
open statement (O-G) and the "minimal counterexample structure" of §7) and `rate.md` (the law ρ = 2^{β−1}).
Lean: `PiecesCounted.IsPieces ρ c D Alg` in `/home/user/anth-build/proof/statements/PiecesCountedStatement.lean`
(clauses `sum`, `row`, `col`, `caps`, `card`, `size_*`, `computes`). Scripts `research/permanent/scripts/fock_*.py`,
outputs `fock_*.out`. Tags as before: **[R]** proved here, **[K]** known, **[N]** numerical, **[C]** heuristic.

## 0. Verdict first

* **The "sparse Fock space" is not a separate, cheaper target: it is the general pieces problem in
  disguise [R, Theorem 2.1].** On V_S = ℚ[t_k : k ∈ S] every linear map between weight spaces is realised by
  the sparse Heisenberg operators (t^τ ∂^σ/σ! = |τ⟩⟨σ| on V_{|σ|}), and Definition 3.1 of `rho-lower-bound.md`
  asks for nothing but linear maps between weight spaces. Consequently *every* family of pieces
  (`Pieces.Family`, any ρ) is a graded two-order decomposition on *every* V_S with 1 ∈ S, at the price of
  2 bits per piece, and conversely. The hypothesis (O-G) of `rho-lower-bound.md` §7 is therefore equivalent
  to `PiecesCounted.Exist ρ c` itself (c ↦ c + O(1)). Nothing about squares, cubes or powers of 2 enters.
* **Where the law ρ = 2^{β−1} really comes from.** The law is Theorem 3.3 *plus* hypothesis (H): spread = 2h.
  The spread is a property of the *mechanism* that produces the pieces (locality, Lemma 4.1), not of the
  space. On V_S the law would hold *if* a locality-type identity existed; Theorem 3.1 below shows that none
  does, for any Laurent-polynomial annihilator (ordinary, twisted (z^a − w^a)^H, or any other), and that the
  obstruction is exactly arithmetic: the nonzero modes of a field that is "P-local" with a non-commuting
  partner form a set with **bounded gaps**, hence of positive lower density; squares, k-th powers, powers of
  2 have unbounded gaps. With Prop. 5.2 of `rho-lower-bound.md`, every free field obeying generalized
  locality spans a Fock subspace of partition growth: **β = 1/2 is forced for every locality mechanism** [R].
* **The other mechanism available on V_S, Wick/Leibniz slicing by contraction weight, is computed exactly
  [R]+[N]**: its certified cost is ≥ (2 + 2^β)λ for every grouping of the slices (Proposition 4.2), i.e.
  ρ ≥ 3/4 in the limit, and the true ranks at small sizes give ρ_true = 0.89–0.96 for S = ℕ, squares, powers
  of 2 (`fock_wick_pieces_*.out`), never below 0.886. The mechanism has no two-order character: every slice
  stands in one order only, and the only two-order combination (B_vA_x itself) has column rank N².
* **Multi-gradings, other pairings (Task 4) [R]**: a ℤ^d-grading used for costs must be collapsed to ℤ by a
  linear functional; the collapsed field is a one-variable field to which Theorem 3.1 applies whenever the
  annihilator survives the collapse; multi-variable locality (higher-dimensional vertex algebras) only
  *adds* modes per weight (β = (d−1)/d or worse). A non-top pairing changes the spread (the zero-mode
  loophole (O-H)), not β, and on V_S there is no locality to begin with. None of this circumvents anything.
* **Consequence statements, corrected** (per `clique-evaluation.md` §4.3, a claim not yet refereed): a
  construction with ρ = 2^{−2/3} would give α' = 2/3 and the rate 2^{O(U/(log U)^{2/3})} for #SAT and every
  *sparse* application of Theorem A; it would **not** give the dense permanent, which needs e_K·log K → 0,
  i.e. α' > 1, beyond the ceiling α' ≤ 1 of any min-over-two-groupings recursion. The earlier line
  "2^{O(n²/(log n)^{2/3})} for the dense permanent" is withdrawn.
* **Status of the question "is ρ < 1/√2 achievable at all":** unchanged and sharpened. It is exactly the
  general problem `Exist ρ c`, ρ < 1/√2 (a Hurwitz/HWY-type tensor problem, §6); every *mechanism* known
  to produce two-order identities is now proved to force β = 1/2 and hence ρ ≥ 1/√2 (locality in all its
  polynomial-annihilator forms) or to give ρ ≥ 3/4 (Wick slicing). There is no "sparse" shortcut.

## 1. Sparse Fock spaces and their growth (Task 1)

### 1.1 Definition [R]

For S ⊂ ℕ_{≥1} let V_S := ℚ[t_k : k ∈ S], graded by wt t_k = k, so V_{S,E} has the basis {t^μ : μ an
S-partition of E} (parts in S) and dim V_{S,E} = p_S(E) with Hilbert series Π_{k∈S}(1 − q^k)^{−1}. The
sparse Heisenberg algebra acts by ∇_{−k} = t_k·, ∇_k = k∂/∂t_k (k ∈ S), [∇_k, ∇_{−l}] = k[k = l]; the top
pairing of Lemma 10 restricts: for S-partitions μ, ν of h, (Π_i ∇_{μ_i}) t^ν = z_μ[μ = ν]. So the labels
(N = p_S(h) ≥ 2^λ), the nondegenerate pairing and the raising/lowering operators are all there; the
anticommutative version (parts distinct) is the same with the exterior algebra. f_S(E) := log₂ p_S(E),
β_S := lim log f_S(E)/log E.

### 1.2 Growth exponents [K]+[N] (`fock_growth.py`, `fock_growth.out`)

| S | asymptotic of ln p_S(E) | β | 2^{β−1} | f(2E)/(2f(E)) at E = 10³ / 10⁴ / 2·10⁴ |
|---|---|---|---|---|
| ℕ | π√(2E/3) (Hardy–Ramanujan) | 1/2 | 0.7071 | 0.728 / 0.715 / 0.713 |
| squares | 3(π/4)^{1/3}ζ(3/2)^{2/3}E^{1/3} (HR 1917) | 1/3 | 0.6300 | 0.676 / 0.654 / 0.650 |
| cubes | (a+1)[Γ(1+1/a)ζ(1+1/a)/a]^{a/(a+1)}E^{1/(a+1)}, a = 3 | 1/4 | 0.5946 | 0.662 / 0.633 / 0.627 |
| k⁴ | same, a = 4 | 1/5 | 0.5743 | 0.659 / 0.625 / 0.618 |
| primes | 2π√(E/(3 ln E)) (Roth–Szekeres) | 1/2 | 0.7071 | 0.709 / 0.694 / **0.692** |
| powers of 2 | (ln E)²/(2 ln 2) (de Bruijn; polylog growth) | 0 | 0.5000 | 0.614 / 0.586 / 0.580 |

Exact integers to E = 4·10⁴; the finite-size ratios to the leading terms are 0.97 (ℕ), 0.84 (squares),
0.68 (cubes), 0.53 (k⁴), 1.01 (primes), 0.66 (powers of 2) at E = 2·10⁴ — the usual slow convergence of
Meinardus-type asymptotics. Two remarks. (i) For primes the finite-size law is *below* 1/√2 (0.692 at
E = 2·10⁴) because f(2E)/(2f(E)) ≈ (1/√2)√(ln E/ln 2E); it converges to 1/√2 from below. So even β = 1/2
"with a log" would show a finite-size ρ < 1/√2 — if a two-order structure existed on the prime Fock space;
Theorem 3.1 excludes locality there too (primes have unbounded gaps). (ii) These numbers are what ρ *would* be
under hypothesis (H); §2 shows that on V_S nothing forces (H), and §3 that nothing realises it.

## 2. The reduction: on V_S the two-order structure is vacuous (Tasks 1–3, structural part)

### 2.1 Every linear map is in the algebra [R]

**Lemma 2.0.** For every S and all E, E' ≥ 0 the sparse Weyl algebra generated by ∇_{±k}, k ∈ S, surjects
onto Hom(V_{S,E}, V_{S,E'}). *Proof.* For S-partitions σ of E and τ of E', the operator
t^τ·Π_i ∂/∂t_{σ_i}/(Π_k mult_k(σ)!) maps t^{σ'} (|σ'| = E) to [σ' = σ]t^τ, i.e. it is |τ⟩⟨σ|; these span. ∎

So "a family of operators in U(sparse Heisenberg)" is no restriction; Definition 3.1 of `rho-lower-bound.md`
(two-order piece: operators X_x^{(j)} ∈ Hom(V_h, V_{h+r_j}), Y_v^{(j)} ∈ Hom(V_{h+r_j}, V_h), X', Y' in the
other order, with Σ_j Y^{(j)}_v X^{(j)}_x = Σ_j X'^{(j)}_x Y'^{(j)}_v) already asks only for linear maps.

### 2.2 Pieces ⟺ graded two-order decompositions on V_S [R]

**Theorem 2.1.** Let S ∋ 1 (so p_S is nondecreasing and p_S(E+1) ≤ 2p_S(E)), λ ≥ 1, N = 2^λ, and let h be
least with p_S(h) ≥ N.
(a) A graded two-order decomposition on V_S with certified costs c^row_i, c^col_i (Lemma 3.2 of
`rho-lower-bound.md`) is a family of pieces (`Pieces.Family lam`) with those costs, with integer data when
the operators have integer matrices, and `IsPieces ρ c` follows from `caps`, `card`, `size_*`, `computes`
for the operator data.
(b) Conversely, let (d, I, A_i, c^row_i, c^col_i, fn) be a family satisfying clauses (a), (b) of
Definition 7 at λ. Then there is a graded two-order decomposition on V_S (labels e_y = t^{μ(y)}, μ(y) the
y-th S-partition of h) whose certified costs are ≤ c^row_i + 2 and c^col_i + 2, with the same d and the same
integer factor functions. Its degree set is T_i = {ρ_i, −ρ'_i} with ρ_i, ρ'_i ≥ 0 minimal such that
p_S(h + ρ_i) ≥ 2^{c^row_i}, p_S(h + ρ'_i) ≥ 2^{c^col_i} (if c^row_i < λ take ρ_i = 0, cost λ + 2 instead).
(c) Hence `PiecesCounted.Exist ρ c` ⟹ a graded two-order decomposition on V_S with parameters (ρ, c + 2)
(the +2 bits per piece are absorbed into c·log₂(2λ) for λ ≥ 2), and conversely with c unchanged; the
statement (O-G) of `rho-lower-bound.md` §7 for V_S is equivalent to `Exist ρ c` for some c.

*Proof.* (a) is Lemma 3.2 of `rho-lower-bound.md`: A_i(x,y,u,v) = Σ_j Σ_τ e_τ^*(X^{(j)}_x e_y)·e_u^*(Y^{(j)}_v e_τ)
is a row factorization through R^row = Σ_j p_S(h + r_j) terms, likewise for the columns; the remaining
clauses concern the numbers only.
(b) Write W := V_{S,h+ρ} ⊕ V_{S,h−ρ'} and W' := V_{S,h−ρ} ⊕ V_{S,h+ρ'}. Then dim W ≥ p_S(h+ρ) ≥ 2^{c^row}
and dim W ≤ 2^{c^row+1} + p_S(h) ≤ 3·2^{c^row} by minimality of ρ and p_S(E+1) ≤ 2p_S(E), which holds for
every S ∋ 1: p_S(E+1) − p_S(E) counts the S-partitions of E+1 without part 1, and replacing the smallest part
k ≥ 2 of such a partition by k ones is an injection into the S-partitions of E+1 with at least two ones,
of which there are p_S(E−1) ≤ p_S(E); likewise 2^{c^col} ≤ dim W' ≤ 3·2^{c^col}. Fix an injection θ ↦ w_θ of
{0,1}^{c^row} into a basis of W and θ' ↦ w'_{θ'} of {0,1}^{c^col} into a basis of W'. Define
X_x e_{y} := Σ_θ fn(row,1,i,(x,y),θ) w_θ, Y_v w_θ := Σ_u fn(row,2,i,(u,v),θ) e_u (zero on the other basis
vectors of W and on the non-label basis vectors of V_{S,h}), and Y'_v e_y := Σ_{θ'} fn(col,2,i,(y,v),θ')w'_{θ'},
X'_x w'_{θ'} := Σ_u fn(col,1,i,(x,u),θ') e_u. Clause `row` gives e_u^*(Y_vX_x e_y) = A_i(x,y,u,v) and clause
`col` gives e_u^*(X'_xY'_v e_y) = A_i(x,y,u,v) for labels y, u; on non-label basis vectors both sides vanish.
So Y_vX_x = X'_xY'_v on V_{S,h}: a two-order piece with T = {ρ, −ρ'}, in which the term of degree −ρ' is
zero in the first order and the term of degree ρ is zero in the second (Definition 3.1 allows zero
summands). Its certified costs are ⌈log₂ dim W⌉ ≤ c^row + 2, ⌈log₂ dim W'⌉ ≤ c^col + 2. Clause `sum`
is unchanged. (c) follows. ∎

**What Theorem 2.1 says.** (i) The "cheapest hypothetical" of `rho-lower-bound.md` §7 — a two-order
identity on ℚ[t_{k²}] with poly(λ) terms — is *not* a smaller or more structured problem than the general one:
any pieces at all, including Theorem B's own, live on ℚ[t_{k²}] with the same costs; and a hypothetical
family with ρ < 1/√2 on ℚ[t_{k²}] *is* a general family with ρ < 1/√2. (ii) The realisation in (b) has
spread ρ_i + ρ'_i, which is whatever the ranks dictate — Theorem 3.3 applied to it reproduces exactly
log r_i + log o_i and nothing more. The law ρ ≥ f(2h)/(2f(h)) of Corollary 3.4 therefore never follows from
the space; it follows from a *mechanism* with spread 2h (Lemma 4.1: locality with top-pole pairing).
(iii) The rank inequalities (R1)–(R3) of `rho-lower-bound.md` §2 cannot exclude anything on V_S either:
the ρ = 1/2 profile {(N²,1), (1,N²), (N,N)} is realised with graded bookkeeping by T = {R, h}, {−R, −h},
{0}, where p_S(h+R) ≥ N² (the term of degree h is zero in one order since V_{S,0} is one-dimensional and
V_{S,<0} = 0). So any lower bound beyond 1/2 on V_S must use the actual tensors — the general problem.

## 3. Mechanism I: locality, in every polynomial form, needs dense modes (Task 3)

### 3.1 Generalized locality forces bounded gaps [R]

**Theorem 3.1.** Let V = ⊕_{E∈ℤ} V_E be graded over a field 𝔽, let a(z) = Σ_{n∈ℤ} a_n z^{−n−1} and
b(w) = Σ_m b_m w^{−m−1} be formal distributions with End(V) coefficients that are homogeneous (a_n of degree
δ_a − n, b_m of degree δ_b − m), and suppose C(z,w) := [a(z), b(w)] ≠ 0. Let P(z,w) ∈ 𝔽[z^{±1}, w^{±1}] be
nonzero with P(z,w)·C(z,w) = 0. Let P_t = Σ_i p_i z^i w^{t−i} be any nonzero homogeneous component of P and
L := max{i : p_i ≠ 0} − min{i : p_i ≠ 0} + 1 its width. Then the set {n : a_n ≠ 0} contains no L − 1
consecutive integers in its complement: every gap in the set of nonzero modes has length ≤ L − 2. The same
holds for the modes of b.

*Proof.* The coefficient of z^{−n−1}w^{−m−1} in P·C is Σ_{(i,j)} p_{ij} C_{n+i, m+j}, with C_{n,m} = [a_n, b_m]
of degree δ_a + δ_b − n − m. Terms with different i + j have different degrees, so each homogeneous component
P_t of P kills C separately: Σ_i p_i C_{n+i, m+t−i} = 0 for all n, m. Fix s ∈ ℤ and put x_k := C_{k, s−k}
(k ∈ ℤ); then with m = s − n − t: Σ_i p_i x_{n+i} = 0 for every n — a linear recurrence with constant
coefficients whose extreme coefficients p_{i_min}, p_{i_max} are nonzero. Hence if x_k = 0 for k in L − 1
consecutive integers, solving forward (dividing by p_{i_max}) and backward (by p_{i_min}) gives x ≡ 0. If
a_n = 0 then C_{n,m} = 0 for all m, so x_n = 0 for every s. Thus if the complement of {n : a_n ≠ 0} contained
L − 1 consecutive integers, every anti-diagonal x would vanish, i.e. C = 0. For b, exchange the roles. ∎

**Corollary 3.2.** (i) Ordinary locality P = (z−w)^H: gaps ≤ H − 1 (Prop. 5.1 of `rho-lower-bound.md`, which
gives the sharper "at most H − 1 missing modes"). (ii) Twisted locality P = (z^a − w^a)^H = Π_ζ(z − ζw)^H:
gaps ≤ aH − 1. (iii) Any P: the set of nonzero modes has lower density ≥ 1/(L−1) > 0. (iv) **The sparse
current φ_S(z) := Σ_{k∈S∪(−S)} ∇_k z^{−k−1} on V_S admits no polynomial annihilator of its self-commutator
unless S ∪ (−S) has bounded gaps**; squares, k-th powers (a ≥ 2), powers of 2, and primes (gaps unbounded,
Westzynthius) are excluded. Concretely [φ_S(z), φ_S(w)] = z^{−1}w^{−1}F_S(w/z) with F_S(q) = Σ_{k∈S∪−S} k q^k,
and a homogeneous P kills it iff the two-sided sequence c_k = k·[|k| ∈ S] satisfies a constant-coefficient
linear recurrence on ℤ, iff its Hankel matrices have bounded rank (`fock_locality_gap.py`: rank 2 for
S = ℕ, recurrence (z−w)²; rank 6 for S = {|k| ≡ ±1 mod 3}; unbounded for squares, cubes, powers of 2 — and
also for S = {k ≡ 1 mod 3} alone, because S ∪ (−S) = {1 mod 3 on k > 0} ∪ {2 mod 3 on k < 0} is not a
recurrence set: the annihilator must be symmetric under k ↦ −k, as the Heisenberg relation
[∇_{−k}, ∇_k] = −k demands).

**Corollary 3.3 (free fields).** Let a(z) satisfy generalized locality with some non-commuting partner, and let
its modes be of Heisenberg type: [a_m, a_n] = κ_m δ_{m+n,0}·Id with κ_m ≠ 0 whenever a_m ≠ 0 (m ≥ m_0), a_n 1 = 0
for n ≥ 0. Then by Theorem 3.1 the set K = {m ≥ m_0 : a_m ≠ 0} has gaps ≤ g := L − 2, and by Prop. 5.2 of
`rho-lower-bound.md` (whose proof uses only [a_m, a_{−n}] = κ_mδ_{mn} for m, n ∈ K) the vectors
a_{−λ_1}⋯a_{−λ_k}1, λ_i ∈ K, are independent, so dim V_E ≥ p_K(E). A set K with gaps ≤ g has lower density
δ ≥ 1/(g+1), and then log₂ p_K(E) ≥ (δ/2)√E − log₂(E+1) − O(1): the multisets of m = ⌊δ√E/2⌋ elements of
K ∩ [1, √E] (at least 2m of them) number ≥ C(2m, m) ≥ 2^m and have sums ≤ E, so some E' ≤ E has
p_K(E') ≥ 2^m/(E+1), and p_K(E'+ k_0 j) ≥ p_K(E') for the least k_0 ∈ K and all j ≥ 0 lifts this to all large
E up to the factor k_0 in the argument of √. Hence log dim V_E ≥ c√E − O(log E): **β = 1/2**, and by Corollary 3.4 of `rho-lower-bound.md`
(with spread 2h from Lemma 4.1 when the pairing is the top pole) ρ ≥ 1/√2 − o(1) for every decomposition by
slices of a generalized-locality identity between free fields.

For non-free fields, generalized locality in the one-variable sense is ordinary locality up to the twist, and
the twisted/orbifold vertex algebras obtained this way are again C₂-cofinite or free-field-like in every
known case (β = 1/2, [K] Dong–Mason, Gaberdiel–Neitzke, as in `rho-lower-bound.md` §5.2); a general theorem
"non-commutative ⟹ exp(c√E) growth" for abstract vertex algebras is not available, as before.

### 3.2 Multi-gradings and multi-variable fields (Task 4) [R]

Costs in Definition 3.1 need an additive ℤ-grading (passing spaces V_{h+r}); a ℤ^d-grading V = ⊕_{E∈ℤ^d} V_E
enters only through a linear functional ℓ: ℤ^d → ℤ, V_n := ⊕_{ℓ(E) = n} V_E, which only *merges* weight spaces
(dim V_n ≥ dim V_E for each E with ℓ(E) = n). For fields in d formal variables a(z_1,…,z_d) with modes a_k,
k ∈ ℤ^d, homogeneous for the ℤ^d-grading, the ℓ-graded one-variable field ã(ζ) := a(ζ^{ℓ_1},…,ζ^{ℓ_d}) has
modes ã_n = Σ_{ℓ(k) = n} a_k, which are exactly the homogeneous components for the ℤ-grading; if
P(z,w)[a(z),b(w)] = 0 and P̃(ζ,ξ) := P(ζ^ℓ, ξ^ℓ) ≠ 0 then P̃[ã(ζ), b̃(ξ)] = 0 and Theorem 3.1 applies to ã: the
ℤ-degrees carrying nonzero modes have bounded gaps, and Corollary 3.3 applies verbatim to free fields. The
only escape is P̃ = 0 (P vanishes on the curve (ζ^ℓ, ξ^ℓ), e.g. P = z_1w_2 − z_2w_1 with ℓ = (1,1), or the
degenerate δ(z_1)-type fields which are not ℤ^d-homogeneous); in the known multi-variable theories
(higher-dimensional vertex algebras, Nikolov) the annihilator is a power of the quadratic form (z−w)², which
survives every collapse, and the oscillator multiplicity per weight is n^{d−2}, β = (d−1)/d ≥ 1/2 — worse.
Ungraded structures (Clifford, group algebras, codes) were already treated in `rho-lower-bound.md` §6: without
a grading the terms pay log(#terms) in both directions, β = 1 effectively.

**Non-top pairings.** If the pairing is a lower pole a_{(H−1)}b ∈ V_w (w > 0), the spread is H = 2h − w and
the zero-mode loophole (O-H) is at stake — a question about *spread*, not about β; its dimension count
(`rho-lower-bound.md` §4.2) makes it a loser and it is unaffected by S. On V_S there is no locality identity
of any order (Corollary 3.2), so the pairing never enters: by Theorem 2.1 the pairing of a general piece
family is the arbitrary tensor Σ_i A_i = d[x=v][y=u], and Theorem 3.3 gives for the realization of §2.2
exactly the true ranks, whatever the pairing.

## 4. Mechanism II: Wick/Leibniz slicing, exactly (Tasks 1–3, numerical part)

### 4.1 The identity [R]

The only identity available on every V_S is Wick's theorem (normal ordering). With labels μ, ν S-partitions
of h, A_x := t^{μ}· (raises by h) and B_v := (h!/z_ν)Π_i ∇_{ν_i} (lowers by h; B_v t^μ = h![μ = ν] on V_h):

    B_v A_x = Σ_{ρ ⊆ μ ∩ ν} c_1(μ,ρ) c_2(ν,ρ) · t^{μ∖ρ} ∇_{ν∖ρ}        on V_h,                          (4.1)

one term for each common sub-multiset ρ, c_1 = Π_k C(mult_k μ, mult_k ρ), c_2 = (h!/z_ν)Π_k C(mult_k ν, mult_k ρ)
(mult_k ρ)! k^{mult_k ρ}. On V_h the term ρ passes through V_{|ρ|} as written (∇_{ν∖ρ} lowers by h − |ρ|) and
through V_{2h−|ρ|} with the factors exchanged; ρ = μ = ν gives h![x = v]·Id. Slicing by contraction weight,
T_w(x,y,u,v) := e_u^*(Σ_{|ρ|=w} … e_y), gives Σ_{w≤h} T_w = e_u^*(B_vA_x e_y) and T_h = h![x=v][y=u]. Every
family of signed sums {Σ_{w∈J_0}T_w} ∪ {−Σ_{w∈J}T_w : J ∈ 𝒫} with h ∈ J_0 and 𝒫 a partition of J_0∖{h} adds up
to the crossing with d = h!, |I| ≤ h + 1 ≤ poly(λ) (h ≤ λ^{1/β+o(1)}), integer entries, computable — all
clauses of `IsPieces` except `caps`, which is the question. Verified exactly for all S and h below
(`fock_wick_pieces.py`: (4.1) summed over ρ equals B_vA_x computed directly; T_h = h!·crossing: PASS).

### 4.2 Certified costs: no grouping beats 3/4 [R]

**Proposition 4.2.** In the Wick family, the piece whose coefficient at w = h is nonzero (there is one) has
certified cost ≥ 2λ + f_S(2h − w_1), where w_1 is the least weight in its support; hence ≥ (2 + 2^β)λ when
w_1 = 0 (the piece B_vA_x) and ≥ 3λ when w_1 ≥ 1. So the certified ρ of every grouping is ≥ 3/4, and the
grouping {B_vA_x, −Σ_{w<h}T_w} has certified ρ = (2 + 2^β)/4 (0.854 for β = 1/2, 0.815 for β = 1/3, → 3/4).

*Proof.* Column side: the slice T_h is Σ_{|ρ|=h} with p_S(h) choices of ρ, each passing through V_h: the
structure certifies Σ_{w∈J} p_S(w)p_S(w) ≥ p_S(h)² = N² terms, 2λ bits. Row side: exchanging the factors in
each term of Σ_{w∈J} g(w)T_w and re-expanding by (4.1) in the other order gives Σ_{ρ'} β(ρ')·(term through
V_{2h−|ρ'|}) with β(ρ') = Σ_{ν⊆ρ', |ν|∈J} ± g(|ν|)·(coefficients); for |ρ'| = w_1 the only ν is ρ' itself, so
β(ρ') = ±g(w_1)·c ≠ 0 and V_{2h−w_1} is among the passing spaces: ≥ f_S(2h − w_1) bits. If 0 ∈ J the sum
telescopes to the single term B_vA_x through V_{2h}: f_S(2h) = 2^βλ(1+o(1)). Since f_S(2h−w_1) ≥ f_S(h) = λ
for w_1 ≤ h, the bound is ≥ 3λ when w_1 ≥ 1. ∎

Contrast with locality: there every term of the slice Q_s stands in *both* orders through spaces of
dimension ≤ p(2h ± s) (Lemma 9(a)), whereas every Wick term stands in one order only; the crossing T_h itself
costs 4λ, and the only two-order combination, B_vA_x, has column rank N². This is the precise sense in which
"the naive Leibniz identity gives ρ ≈ 1" (`rho-lower-bound.md` §6).

### 4.3 True ranks [N] (`fock_wick_pieces_{N,sq,pow2,cubes}.out`)

All interval sums Σ_{a≤w≤b}T_w, both flattenings, ranks mod 2^61−1; dynamic programme over all interval
groupings for the min-max cost. ρ_true := min over groupings of max_i(log r_i + log o_i)/(4λ).

| S | h | N | λ | B_vA_x (r, o) | T_0 (r, o) | fine family ρ | coarse ρ | best grouping ρ | law f(2h)/(2f(h)) |
|---|---|---|---|---|---|---|---|---|---|
| ℕ | 5 | 7 | 2.81 | (25, 49) | (49, 1) | 0.914 | 0.949 | 0.914 | 0.960 |
| ℕ | 6 | 11 | 3.46 | (53, 121) | (121, 1) | 0.914 | 0.947 | 0.914 | 0.906 |
| ℕ | 7 | 15 | 3.91 | (89, 225) | (225, 1) | 0.914 | 0.971 | 0.914 | 0.906 |
| squares | 16 | 8 | 3.00 | (26, 64) | (64,1) | 0.892 | 0.960 | 0.892 | 0.826 |
| squares | 20 | 12 | 3.58 | (45, 144) | (144,1) | 0.927 | 0.990 | 0.925 | 0.806 |
| squares | 24 | 16 | 4.00 | (63, 256) | (256,1) | 0.952 | 0.995 | 0.938 | 0.812 |
| powers of 2 | 8 | 10 | 3.32 | (35, 100) | (100,1) | 0.886 | 0.955 | 0.886 | 0.778 |
| powers of 2 | 12 | 20 | 4.32 | (83, 400) | (400,1) | 0.920 | 0.987 | 0.920 | 0.758 |
| powers of 2 | 16 | 36 | 5.17 | (201, 1296) | (1296,1) | 0.937 | 0.988 | 0.936 | 0.741 |
| cubes | 40 | 8 | 3.00 | (21, 64) | (64,1) | 0.936 | 0.992 | 0.923 | 0.774 |

(Full tables with every interval in the `.out` files.) In every case B_vA_x has column rank exactly N² and T_0
= h![u=x][y=v] has row rank N²; the best grouping is always {B_vA_x, T_0, …, T_{h−1}} or a coarsening of the
T_w with w ≥ 1, with ρ_true between 0.886 and 0.96, *increasing* with h within each S. At these sizes
Theorem B's own pieces have ρ_true = 1.00 for h ≤ 7 (`rho_fock_pieces_3_7.out`: the cap Σ_i p(i) > p(h)²
bites until h ≈ 15), so finite-size comparisons between mechanisms mean nothing; the certified asymptotics
(Prop. 4.2 versus Cor. 3.5 of `rho-lower-bound.md`) are what count, and they say 3/4 < 1/√2 is never
approached by Wick slicing. No sparse S changes the picture: the exponent β only enters through f_S(2h) in the
one piece B_vA_x, and the floor 3/4 comes from the N² column rank of that piece, which has nothing to do with
the growth of V_S.

## 5. Consequences, stated honestly

If pieces with ρ = 2^{−2/3} existed (by Theorem 2.1 this is the general statement `Exist (2^{−2/3}) c`, not a
statement about ℚ[t_{k²}]), Theorem A as proved (`ExplicitCost.recursionSolves`, general in ρ) gives
α' = log₂(1/ρ) = 2/3 and the rate 2^{O(U/(log U)^{2/3})} for #SAT, k-SAT and every *sparse* application
(`rate.md` §1). It does **not** give the dense permanent or dense Hamiltonian cycle: by `clique-evaluation.md`
§4.3 (claim, not yet refereed) every recursion of Theorem A's shape has ρ ≥ 1/2 − o(1), hence α' ≤ 1 and
e_K ≥ c/log K, while the dense problems via the Laplace network need e_K·log K → 0, i.e. α' > 1. The line
"dense permanent in 2^{O(n²/(log n)^{2/3})}" in `rho-lower-bound.md` §7 is withdrawn; the correct consequence
of any ρ < 1/√2 is a faster rate for the sparse applications only.

## 6. Verdict and the exact open statement

**Proved here.**
(i) Theorem 2.1: graded two-order decompositions on V_S (any S ∋ 1) *are* pieces families and conversely
(costs +2 bits); hypothesis (O-G) for sparse Fock spaces is equivalent to `PiecesCounted.Exist ρ c`, and the
"cheapest counterexample structure" of `rho-lower-bound.md` §7 is the general problem itself. The law
ρ = 2^{β−1} is a consequence of spread 2h, never of the space.
(ii) Theorem 3.1: a field with a polynomial-annihilated nonzero commutator (ordinary, twisted, or arbitrary
generalized locality) has nonzero modes with bounded gaps; Cor. 3.2: no such identity exists for the sparse
currents on ℚ[t_k : k ∈ S] for S = squares, k-th powers, powers of 2, primes, or S = {1 mod 3} alone;
Cor. 3.3: free fields under generalized locality have β = 1/2 and ρ ≥ 1/√2 − o(1); §3.2: ℤ^d-gradings and
multi-variable locality reduce to this or make β larger.
(iii) Prop. 4.2 + §4.3: Wick slicing on any V_S has certified ρ ≥ 3/4 for every grouping, true ρ ≥ 0.886 at
all computed sizes.

**Not constructed, not excluded.** Pieces with ρ < 1/√2. The exact remaining statement is unchanged from
`rho-lower-bound.md` §7 but can now be put without any reference to algebras or gradings:

> Do there exist, for every λ, integer tensors A_i (i ∈ I, |I| ≤ poly λ) on ({0,1}^λ)^4 with
> Σ_i A_i = d[x=v][y=u], d ≥ 1, and rank_{(xy|uv)}A_i · rank_{(xu|yv)}A_i ≤ 2^{(2√2−ε)λ}·poly(λ) for all i?

Every graded, sparse, multi-graded or vertex-algebraic reformulation is this statement (Theorem 2.1), and every
mechanism that has ever produced such tensors with a sub-4λ cost is a locality identity, which forces
β = 1/2 and ρ ≥ 1/√2 (Theorem 3.1, Cor. 3.3, and `rho-lower-bound.md` Cor. 3.5/[K]). The honest estimate is
therefore stronger than before: **there is no "sparse Fock" route; a ρ < 1/√2 construction would have to be a
new tensor identity of Hurwitz type, with no algebraic template available**, and the lower-bound side is the
general HWY-hard problem of `rho-lower-bound.md` §2.2 (nothing beyond ρ ≥ 1/2 is provable by ranks).

## 7. Scripts

| script | what it does | output | status |
|---|---|---|---|
| `fock_growth.py` | p_S(E) exactly to 4·10⁴ for S = ℕ, squares, cubes, k⁴, primes, powers of 2; local exponent, ratio to the Hardy–Ramanujan/Meinardus/Roth–Szekeres/de Bruijn leading terms, the law f(2E)/(2f(E)) | `fock_growth.out` | PASS |
| `fock_locality_gap.py` | Hankel ranks of the two-sided mode sequence k[|k| ∈ S]: a polynomial annihilator of [φ_S(z), φ_S(w)] exists iff the rank is bounded (Thm 3.1 / Cor. 3.2(iv)); ℕ and {±1 mod 3} yes, squares/cubes/powers of 2/{1 mod 3} no | `fock_locality_gap.out` | PASS |
| `fock_wick_pieces.py S h…` | the Wick slices T_w on V_S exactly, identity checks, true ranks of all interval sums, DP over groupings, ρ_true vs the law | `fock_wick_pieces_{N,sq,pow2,cubes}.out` | IDENTITIES PASS |

Ranks are computed mod 2^61−1 (lower bounds for ranks over ℚ, generically exact; where a rank equals its
trivial upper bound N² or a certified count it is exact).
