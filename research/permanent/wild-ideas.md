# Wild ideas for the dense 0/1 permanent: accounting, obstructions, two new positive classes

29 Oct 2026. Read after `permanent-attack.md`, `barrier.md`, `rate.md`, `rho-lower-bound.md`; nothing there is
redone. Conventions as there (lg = log₂; the engine = Lemma 8 + Theorem A(b) + Theorem B of [A], exponent
≥ e_K·U + 2gP/K with e_K ≤ 0.85((3x₀+6)/lg K)^{α'}, α' = lg(1/ρ), x₀ ≥ 18; the Lean #k-SAT bounds are
2^{O(k² N (lg lg N)²/√lg N)} (OpenAI, N variables) and 2^{C·min(km/√lg m, k² N lg lg N/√lg N)} (Anthropic)).
Scripts: `scripts/wild_*.py`, outputs `scripts/wild_*.out`; every identity below is checked exactly for
n ≤ 8 on random instances.

## 0. Summary and ranking

Three facts that cut across all directions (all new here, proofs in §1):

* **(F1) Entropy.** Any per(A) = Σ_{t≤T} w_t·#SAT(F_t) with |w_t| ≤ 2^W has some F_t with ≥ lg n! − lg T − W
  = n lg n − 1.45n − lg T − W variables. So plain #SAT encodings (direction D) are dead for every arity,
  independently of how clever the encoding is: at N = n lg n variables the Lean bounds are 2^{Θ(n√lg n lg lg n)}.
  The only escapes are exponential weights (= the network engine's W tables) or modular counting (per mod p).
* **(F2) Algebra rank.** Any algebra R (commutative or not) with a functional φ and elements r_{ij} such that
  φ(Π_i r_{i f(i)}) = [f bijective] has dim R ≥ C(n, n/2) = 2^{n−O(lg n)}; sums of poly many such algebras too.
  Kills direction C (Clifford/group algebras, tensor substitution, Kronecker) and the "f_j of a linear form" part
  of direction B.
* **(F3) Engine ceiling, sharpened.** Every assignment-class network (U ≥ 2n lg K, forced by h ≥ g/2 ≥ K lg K/2
  nodes per side in Lemma 8 case (ii), g = 3K⁸ in case (i)) has engine exponent ≥ (3x₀+6)·n/2 ≥ 30n for
  **every** ρ ∈ [1/2,1), i.e. for every conceivable set of pieces. `permanent-attack.md` §3 said "2^{o(n)} iff
  e_K = o(1/lg K)"; since α' ≤ 1 is the framework's ceiling (`rate.md`), this is "never".

What survives is structured density, and two classes are new:

| # | idea | status | accounting | verdict |
|---|---|---|---|---|
| E2 | #HC of K_n − D, D sparse (dense HC counting) | **identity verified** (`wild_hc_complement.py`) | (m+1)(n+1) evaluations of a local Grassmann network on D, U = 2⌈lg 5⌉m_cross: **2^{O(m/√lg m)}·poly**, m = \|E(D)\| | **best; complete modulo plugging into the team's HC network** |
| E1 | per(C + D), rank(C) ≤ r, nnz(D) = m | **identity verified** (`wild_lowrank_sparse.py`) | (n+1)^{2r} evaluations of a vertex-weighted matching sum on supp(D): **n^{O(r)}·2^{O(m/√lg m)}**; includes per(J − B) | second; new dense class |
| A(i) | per mod p for all primes p ≤ 2n lg n, then CRT | identity verified; no mechanism | needs per mod p in 2^{o(n)} for ≈ n primes; F_p-sum has p^n terms | only non-barred *target* for generic dense; open |
| A(ii) | interpolation per(A + tJ), rank variable | no cheaper instances found | rook numbers r_k(A) all k ⇔ per(A + tJ) | dead as stated |
| A(iii) | self-reducibility / decision oracle | decision is poly but gives O(1) bits per query | n lg n bits needed ⇒ ≈ n lg n queries each 2^{o(n)} ⇒ back to A(i) | reduces to A(i) |
| B | Glynn / Fourier of products of linear forms | spectrum full on levels ≡ n (mod 2); q-th-root family; half-split rank full | 2^n or q^n terms, every f_j except linear fails | dead (F2) |
| C | algebras, Kronecker, tensor powers | F2; per(A⊗J_2) not a function of per(A) | dim ≥ C(n,n/2) | dead |
| D | non-injective encodings, hashing, Beneš | F1; bucket hashing N ≈ nk + n + n²/2^k ≥ n lg n | mod-p variants need Θ(n) aux bits per dense row ⇒ N = Θ(n²) | dead for plain #SAT; modular version = A(i) |

**Ranking for a full attack:** 1. E2 (write it against the team's HC network: it is dense #HC in 2^{o(n)}
whenever the complement has o(n√lg n) edges, and 2^{δn} for \|E(D)\| = O(n)). 2. E1 (same machinery, bosonic
PM network with an "unmatched" option). 3. A(i) as the long-term target for generic dense matrices, with the
explicit obstruction that every dense row costs Θ(n) bits of arity; §8 records why generic dense per in
2^{o(n)} is an independent open problem (determinantal complexity) that the refutations do not touch.

---------------------------------------------------------------------------------------------------

## 1. Three cross-cutting facts

**F1 (entropy of #SAT encodings).** Suppose per(A) = Σ_{t≤T} w_t·#SAT(F_t) for all A, with integer |w_t| ≤ 2^W
and F_t on N_t variables. Then Σ_t |w_t| 2^{N_t} ≥ max_A per(A) = n!, so max_t N_t ≥ lg n! − W − lg T.
With n! ≥ (n/e)^n: max N_t ≥ n lg n − 1.443n − W − lg T. For poly many instances and poly weights this is
n lg n − O(n). Under the Lean bounds, N = n lg n variables cost 2^{Ω(n√lg n)} even at k = O(1). (Ryser in this
language: T = 2^n instances with w_t = ±1, each with n lg n variables — consistent.)
Consequences: (a) direction D with 0/1 weights is dead regardless of arity or encoding; (b) exponential weights
are the engine's W tables (B bits, polynomial cost), so "D" collapses to "find a network", i.e. the barrier
analysis already done; (c) modular counting per(A) mod p has no entropy obstruction (per mod 2 ∈ P), which makes
A(i) the only #SAT-type target left.

**F2 (algebra rank).** Let R be any ring (not necessarily commutative) with a linear functional φ and elements
r_{ij} (i, j ∈ [n]) such that φ(r_{1f(1)} r_{2f(2)} ⋯ r_{nf(n)}) = [f is a bijection] for all f: [n] → [n]. Then
dim R ≥ C(n, n/2). Proof: for f₁: [n/2] → [n] and f₂: [n/2]+1..n → [n] put u(f₁) = r_{1f₁(1)}⋯r_{n/2, f₁(n/2)} and
v(f₂) likewise; M[f₁,f₂] := φ(u(f₁)v(f₂)) = [im f₁ ⊔ im f₂ = [n], both injective]. Restricted to injective
f₁, f₂ with im f₁ = S, im f₂ = S^c and a fixed order, M contains a C(n,n/2) permutation matrix, and M = ⟨φ, u ⊗ v⟩
has rank ≤ dim R. ∎ (`wild_glynn_fourier.py` prints rank C(n,n/2) for the [L + L′ = 1] matrix, n = 4, 6.) The
same holds if r_{ij} = A_{ij} r_j (Glynn/Ryser type) and for Σ_{t ≤ T} φ_t over T algebras (rank adds: Σ dim R_t ≥
C(n,n/2)). This is Nisan's argument read as a statement about substitution algebras; it says that **every
"evaluate Π_i L_i in a small algebra and read a coefficient" method needs dimension 2^{n−O(lg n)}**, over every
field (permutation matrices have full rank everywhere). Note the contrast with per mod 2 = det mod 2 ∈ P: the
rank bound applies to sum-of-products with a fixed row split, not to adaptive elimination (§8).

**F3 (engine ceiling for assignment networks, any ρ).** Lemma 8 case (i) has g = 3K⁸; case (ii) needs
K lg(2gK) ≤ 2ζ²g with ζ = a/b ≤ 1, so g ≥ K lg K. An assignment-class network has h ≥ g/2 blocks per side
and U ≥ 2n lg(e·h) ≥ 2n lg K (`permanent-attack.md` §8). Theorem A(a): e_ℓ ≥ ½ρ^ℓ and lg K_ℓ = (3x₀+6)2^ℓ −
6ℓ − 2x₀ − 6 ≤ (3x₀+6)2^ℓ, so 2^ℓ ≥ lg K_ℓ/(3x₀+6) and e_K ≥ ½((3x₀+6)/lg K)^{α'} ≥ ½(3x₀+6)/lg K for every
α' ≤ 1 once lg K ≥ 3x₀+6. Hence e_K U ≥ (3x₀+6)·n ≥ 60n (and ≥ 30n even with the cruder 2^ℓ ≤ 2 lg K/(3x₀+6)
bookkeeping of `barrier.md` Lemma 2.0). Since α' = lg(1/ρ) ≤ 1 for all admissible pieces (ρ ≥ ½, `rate.md`
§0), **no choice of pieces makes any assignment-class network for the dense permanent beat 2^{30n}**.

---------------------------------------------------------------------------------------------------

## 2. Direction A: the SAT counters as a non-local oracle

### A(i) Modular counting and CRT  (`wild_modp_sum.py`)

Verified identities:

* For a prime p ≥ n+2: per(A) ≡ (−1)^n Σ_{x∈F_p^n} Π_j x_j^{p−2} Π_i (Ax)_i (mod p). Proof: Σ_{x∈F_p} x^k = −1 if
  (p−1) | k > 0 and 0 otherwise; expanding Π_i (Ax)_i = Σ_f Π A_{if(i)} x^{L(f)} with loads L_j, the x-sum is
  (−1)^n [L_j + p − 2 ≡ 0 (mod p−1) ∀ j], and Σ_j L_j = n < p − 1 forces L = 1. Checked n = 3, 4, 5, p = 5, 7.
* For every q ≥ 2: #{f : Π A_{if(i)} = 1, L_j(f) ≡ 1 (mod q) ∀j} = per(A) (loads ≡ 1 with sum n are all 1).
  So Glynn (q = 2) is the first of a family of q^n-term root-of-unity formulas; none has fewer than 2^n terms.
* CRT budget: lg n! bits are needed; Σ_{p ≤ 2n lg n} lg p exceeds lg n! for n ≥ 8 (n = 256: 5810 vs 1684 bits,
  564 primes). So **per(A) exactly ⇐ per(A) mod p in 2^{o(n)} for each prime p ≤ 2n lg n** (≈ n primes).

Accounting of the obvious encodings of per mod p: the F_p-sum is p^n terms, each a product of n dense linear
forms (broadcast class). A #SAT-mod-p instance must compute Π_i (c_i(S) mod p) from Ryser's S: each dense row
needs a mod-p counter over ≈ n bits, Θ(n lg p) Tseitin variables per row ⇒ N = Θ(n² lg p). Fermat-type
identities on loads only reproduce the root-of-unity family. Group actions (Z_p acting on columns, or by
conjugation) need A invariant. **Obstruction identified:** the dense row. Every row factor reads n bits, and
no modular identity we know compresses "|row_i ∩ S| mod p" below arity n. **No entropy obstruction** (F1 does
not apply mod p; per mod 2 ∈ P), so this is the one place a genuinely new mechanism could live. Verdict: the
right target, no mechanism.

Side remarks. JSV approximation to relative error 2^{−t} costs 2^{2t}·poly, so in 2^{o(n)} we learn the top
o(n) bits of the ≈ n lg n-bit number per(A); Valiant's per mod 2^k (n^{O(k)}) gives the bottom o(n/lg n) bits;
the middle n lg n − o(n) bits are the hard core and are exactly what A(i) asks for.

### A(ii) Interpolation

per(A + tJ) = Σ_k r_k(A)(n−k)! t^{n−k} (rook numbers r_k), so n+1 evaluations ⇔ all rook numbers, each as hard
as per. per((1−t)A) is trivial. Björklund's rank variable (ranked walks through X ⊆ V∖K, interpolation in the
rank) gains 2^{Ω(√(n/lg n))} by collisions among p^{k²} small matrices, not by locality (`permanent-attack.md` §7);
the outer sum over 2^{n−k} sets X is a broadcast sum and the engine cannot speed it up. Verdict: dead as stated;
the only interpolation that pays is the one in E1/E2 (sparse part interpolated, dense part closed-form).

### A(iii) Self-reducibility

per ≠ 0 is a bipartite matching test (poly), and "per ≠ 0 mod p" for p = 2 is det mod 2 (poly). A decision
oracle delivers O(1) bits per call and per(A) has n lg n bits; so ≈ n lg n calls of 2^{o(n)} each would do —
but the calls must be to functions whose answers *determine* per, i.e. to per mod p or to bits of per; the
former is A(i), the latter is #P-hard per bit with no short certificates. Verdict: reduces to A(i).

---------------------------------------------------------------------------------------------------

## 3. Direction B: Glynn and the Fourier structure  (`wild_glynn_fourier.py`)

Glynn: per(A) = 2^{1−n} Σ_{δ: δ₁=1} (Π δ_i) Π_j ⟨δ, A_j⟩; equivalently 2·Ĝ([n]) for G(δ) = Π_j ⟨δ, A_j⟩.
Numerics (random dense 0/1 A, n = 4..8): the Walsh spectrum of G is nonzero on *every* slot of the levels
|S| ≡ n (mod 2) (e.g. n = 8: 128/128; n = 7: 64/64) — no sparsity beyond parity. The half-split matrix
M[δ₁,δ₂] = G(δ₁,δ₂) has rank 2^{n/2} (full) for generic A (16/16 at n = 8 over 12 samples), so the sign sum
has no low-rank shortcut.

Σ_δ (Πδ_i) Π_j f_j(⟨δ,A_j⟩) for other f_j: the Walsh coefficient Ĝ([n]) of Π_j f_j(ℓ_j) is Σ over choices of one
odd-level monomial per column, i.e. a "generalized permanent" with odd multiplicities; it equals per only for
f_j linear (the q-th-root version of §2 shows the same for periodic f_j). The exploitable case is A with r
distinct row types: ⟨δ, A_j⟩ depends on δ only through r partial sums, giving n^{O(r)} — which is Barvinok's
low-rank algorithm again (and E1 subsumes it). In the engine, Glynn is Ryser's broadcast network (F2 applies to
Z[δ]/(δ_i²−1) just as to Z[z]/(z_i²)). Verdict: dead.

---------------------------------------------------------------------------------------------------

## 4. Direction C: free matrix structure, algebras, tensors

* Row/column scaling and permutation: invariances only; they cannot reduce n² bits of a random matrix.
* Group/Clifford algebra substitution: F2, dim ≥ C(n,n/2); the Grassmann/exterior algebra (det(A_{ij}e_j) =
  per(A)e₁⋯e_n) and the bosonic z_j² = 0 algebra are both of dimension 2^n and sharp.
* Tensor powers: per(A ⊗ I_k) = per(A)^k (trivial); per(A ⊗ J_k) = (k!)^{2n} Σ_N Π_{ij} 1/N_{ij}! over k-regular
  contingency tables supported on A, which is **not** a function of per(A): among 3×3 0/1 matrices with
  per(A) = 2, per(A ⊗ J_2) ∈ {48, 80} (computed). No reduction in either direction.
* Decomposition A = Σ_k (rank-1 0/1 pieces): a biclique partition of a random dense 0/1 matrix has total weight
  Θ(n²/lg n) (Chung–Erdős–Spencer), so any gadget-per-piece construction has Ω(n²/lg n) local bits.
Verdict: dead, except that low rank *plus* a sparse correction is exactly E1.

---------------------------------------------------------------------------------------------------

## 5. Direction D: non-injective encodings with computable multiplicity

* F1 kills every 0/1-weighted #SAT encoding: N ≥ n lg n − O(n) variables. Concretely, bucket hashing h: cols →
  [2^k] costs nk bits for the bucket choices, n bits for the within-bucket Ryser sets S_b, and n·2^{−k}·n Tseitin
  bits for the arity-(k + n/2^k) row factors; N ≈ nk + n + n²/2^k ≥ n lg n at the optimum 2^k ≈ n/lg n.
  Beneš/Waksman switch encodings use n lg n switch bits with non-uniform multiplicities. Both are ≥ the
  entropy bound, as they must be.
* The Ryser encoding (S, n bits) *is* a non-injective encoding with o(n√lg n) bits; its multiplicity
  Π_i |row_i ∩ S| has n lg n bits, so it can only be realized through exponential weights (engine tables) —
  and then it is the broadcast network. Hashing the *columns* into blocks and sieving per block gives the
  Laplace network (addressing, n lg h bits) — F3.
* "Deterministic Valiant–Vazirani via the engine": isolation turns counting into decision only approximately
  (Stockmeyer), and exact counting from decision needs n lg n bits of answers (§2 A(iii)).
Verdict: the two classes of `permanent-attack.md` §8 (broadcast / assignment) are the only two, and D adds
nothing to them; the modular version is A(i).

---------------------------------------------------------------------------------------------------

## 6. E1 (new positive): per(C + D), C of rank r, D sparse  (`wild_lowrank_sparse.py`, ALL PASS)

Identity (multilinearity in the entries of D, then Barvinok):

```
per(C + D) = Σ_{M partial matching of supp(D)} Π_{(i,j)∈M} D_{ij} · per(C[rows∖M, cols∖M])
per(C[I,J]) = Σ_{α∈N^r, |α|=|I|} α! · [x^α] Π_{i∈I}(u_i·x) · [y^α] Π_{j∈J}(v_j·y)       (C = UVᵀ)
per(C + D) = Σ_α α! [x^α y^α] P_D(x,y),   P_D(x,y) = Σ_M Π_M D_{ij} Π_{i∉rows(M)}(u_i·x) Π_{j∉cols(M)}(v_j·y).
```

P_D is the **vertex-weighted matching generating polynomial of the sparse bipartite graph supp(D)**: a sum
over matchings M with edge weights D_{ij} and unmatched-vertex weights (u_i·x), (v_j·y). Checked for
n ≤ 7, r ≤ 3, m ≤ 9, integer U, V ∈ [−2,2].

Accounting. P_D has degree ≤ n in each of 2r variables; evaluate at (n+1)^{2r} integer points (weights
≤ (2rn)^n, B = O(n lg n) bits) and interpolate. One evaluation is the team's bosonic PM network
(`perm_bosonic_pm.py`) on supp(D) with an "unmatched" option per vertex (a local weight): U = 2 m_cross ≤ 2m,
node tables 2^{O(n/g)}. Time **(n+1)^{2r} · 2^{O(m/√lg m)} · poly**, which is 2^{o(n)} whenever
r = o(n/lg n) and m = o(n√lg n); with the Lean m-bound of the #k-SAT theorem (D of bounded degree) 2^{δn} for
every δ when m = O(n). Special cases: per(J − B) = Σ_k (−1)^k r_k(B)(n−k)! (r = 1; the complement of a sparse
graph, verified separately in `wild_hc_complement.py`); C any 0/1 low-rank pattern and D ∈ {−1,0,1} the sparse
correction, i.e. "low rank + sparse" 0/1 matrices. Obstruction for generic dense A: a random 0/1 matrix is at
Hamming distance ≥ n²/2 − O(rn^{3/2}) from every rank-r matrix, so m = Θ(n²). Verdict: a new 2^{o(n)} class
of dense matrices (all entries may be nonzero, degrees up to n), not the generic case.

---------------------------------------------------------------------------------------------------

## 7. E2 (new positive, best): dense Hamiltonian-cycle counting on complements of sparse graphs  (`wild_hc_complement.py`, ALL PASS)

Inclusion–exclusion over the forbidden edges D ⊆ E(K_n):

```
#HC(K_n − D) = Σ_{F ⊆ E(D)} (−1)^{|F|} H(F),
H(F) = (n−|F|−1)!/2 · 2^{p(F)}  if F is a linear forest with p nontrivial paths (n−|F| ≥ 1),
     = 1 if F is a Hamiltonian cycle of D,  0 otherwise.
```

The linear-forest statistic is made **local** by the all-minors matrix-tree theorem: for a subgraph F with
max degree ≤ 2 and |F| = k,

```
[ε^{n−k}] det( L_F + ε·diag([deg_F(v) ≤ 1]) ) = 2^{p(F)} · [F acyclic],
```

because det(L_F + diag(d)) = Σ_{spanning forests R ⊆ F} Π_{trees T∈R} (Σ_{v∈T} d_v); the ε-degree is the number of
trees, which equals n − k iff F is acyclic (then R = F and each path contributes its two endpoints), and
exceeds n − k otherwise. Hence

```
#HC(K_n − D) = Σ_{k ≤ n−2} (−1)^k (n−k−1)!/2 · [ε^{n−k}] S_k(ε) + (−1)^{n−1} #HamPath(D) + (−1)^n #HC(D),
S_k(ε) = Σ_{F ⊆ E(D): deg_F ≤ 2, |F| = k} det( L_F + ε·diag([deg_F(v) ≤ 1]) ).
```

Verified by brute force for n ≤ 8 and random D with up to 8 edges (both the raw inclusion–exclusion and the
determinant form equal the true count in all 9 instances; the rook formula per(J − B) in 7 instances).

Accounting. Σ_k y^k S_k(ε) = Σ_{x ⊆ E(D)} Π_v [deg_x v ≤ 2] y^{|x|} det(L_x + ε·diag([deg_x v ≤ 1])) is exactly
the shape of the team's fermionic network (`exact-count-lowrank.md`: det = Berezin integral, local vertex
weights that depend on the local degree, Grassmann edge factor (ψ̄_i − ψ̄_j)(ψ_i − ψ_j), 5 terms per crossing edge,
sign bookkeeping), with the vertex factor exp(ε[deg ≤ 1]ψ̄_vψ_v) added. It is a polynomial in (y, ε) of degree
≤ (m, n): **(m+1)(n+1) evaluations**, each a network on the sparse graph D with U = 2⌈lg 5⌉m_cross + O(g²) bits
and 2^{O(n/g)} tables; #HamPath(D) and #HC(D) are the team's sparse results. Total **2^{O(m/√lg m)}·poly** with
the m-bound, i.e. 2^{δn} for every δ when |E(D)| = O(n), and 2^{o(n)} whenever the complement has o(n√lg n)
edges. This is dense (degree n − O(1)) Hamiltonian-cycle counting, listed as "not covered" in
`sharp-eth-catalogue.md` §2. The directed version is simpler: H(F) = (n−k−1)! for a set of k arcs forming
vertex-disjoint directed paths (no 2^p), with the same determinant indicator on the underlying graph plus a
local in/out-degree check. Obstruction for generic dense graphs: the complement is dense too.
Verdict: the one idea here that is ready for a full write-up.

---------------------------------------------------------------------------------------------------

## 8. What generic dense per(A) in 2^{o(n)} would need

* Through the engine: a network with g ≥ K lg K nodes, each seeing o(n/lg K) bits, total U = o(n√lg K), node
  tables in 2^{o(n)}. F3 excludes assignment networks for all pieces; broadcast networks violate P; F2 excludes
  every substitution algebra; `barrier.md` Thm 6.1 excludes row-local networks. What is not excluded: nodes
  whose tables depend on the whole matrix (Model V and beyond), where no lower bound is possible (Prop. 4.1
  there). No such table with a useful 2^{o(n)} computation was found: the 2^{o(n)}-computable functions of a
  dense A we know are permanents of o(n)-size submatrices, determinants, matchings, JSV approximations and
  per mod 2^{o(n/lg n)} — none of which combines into per with few shared bits.
* Algebraically: per(A) in 2^{o(n)} would follow from determinantal complexity dc(per_n) = 2^{o(n)} over Z
  (Grenet's 2^n − 1 construction is Ryser as an ABP; the best lower bound is Mignon–Ressayre's n²/2;
  commutative ABP lower bounds for per are polynomial). The refutations say nothing about this.
* Lesson from per mod 2: all the rank/entropy barriers above are about sum-of-products representations with
  fixed splits; Gaussian elimination is adaptive and escapes them. A 2^{o(n)} algorithm for the dense permanent
  would have to be elimination-like (Valiant's mod 2^k is the only such mechanism and costs n^{O(k)}). This is a
  different problem from anything the two refutations solved; the honest frontier is the structured classes
  (bounded degree, E1, E2) and the modular target A(i).
