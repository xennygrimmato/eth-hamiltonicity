# x7 notebook: a cyclic (three-merge) version of App. B, or why it cannot exist

24 Nov 2026. Tags: [R] proved here, [K] known/cited, [N] computed (script in `code/`), [C] conjecture.
Inputs: x4, x5, b2 notebooks; VP paper App. B (paper.txt l.1251–1433); open-door §1.6–1.7; z1 §1–2, §4; x3 §4.

## 0. Status (written early, updated at the end)

- **(c) Weyl/Heisenberg pieces are closed by an uncertainty principle [R + N].** See §1. Every Weyl-diagonal piece
  A_f = Σ_s f(s) W_s⊗W_s† satisfies col·third = |supp f|·|supp f̂| ≥ N² (Donoho–Stark), i.e. c_col + c_third ≥ 2λ.
  So on K₄ no Weyl-diagonal piece can have third cost < 0.17λ with col cost < 1.83λ. This explains z1 §4's numbers
  (cosets sit exactly on c_col + c_third = 2λ) and rules out every function f, not only cosets and balls.
- **x4's "step 4" is not an obstruction for determinants [R].** §2. The Schur-complement expansion of App. B, done
  with three groups, gives a *triangle* network directly (Cauchy–Binet over the six directed bond blocks). The
  determinantal route therefore needs no "trace version". The real constraint is elsewhere (§3, §4).
- **Δ₃ has a structural property that B3 lacks: any two merges pin a node.** Consequence (conditional on a rank lemma
  that I verified numerically, [N]/[C]): every single tensor on Δ₃ satisfies c_k ≤ 4(c_{k'} + c_{k''}). With
  Theorem 1, every identity then has a piece *outside* the sphere |c| = 9λ: the literal A₂ sphere law is refuted on Δ₃
  as well. This does not exclude ρ = 1/√3, but it kills the "fused-accounting" Θ = 27e family. See §3.

## 1. Brainstorm item (c): Weyl partial sums on K₄. Closed by Donoho–Stark [R + N]

The crossing on K₄ is SWAP (z1 §4). Each split corresponds to one operation on it:
- row = rank of A as an operator;
- col = operator-Schmidt rank, i.e. realignment;
- third = rank of the partial transpose A^Γ (the split under which both edges are internal).

Weyl operators W_s, s ∈ Z_N², satisfy SWAP = (1/N)Σ_s W_s⊗W_s†. Take any piece A_f = Σ_s f(s) W_s⊗W_s†.
- **col(A_f) = |supp f|.** The W_s are linearly independent.
- **third(A_f) = |supp f̂|**, where f̂ is the (symplectic) Fourier transform. Reason: A_f^Γ = Σ_s f(s) W_s⊗W̄_s, the operators
  W_s⊗W̄_s commute, and they are diagonal in the Bell basis with characters as eigenvalues.
- Hence **col·third ≥ |Z_N²| = N²** for every f ≠ 0, by the uncertainty principle on finite abelian groups (Donoho–Stark).
  In log form, c_col + c_third ≥ 2λ.
- Check (`code/weyl_uncertainty.py`, N = 2…5, 240 random sparse and indicator f): both identities hold in every trial,
  and the minimum of col·third is exactly N².
- Row ranks are unconstrained by this bound, but z1 needs third < 0.17λ, which forces col > 1.83λ. Any family built from
  Weyl-diagonal pieces is at best trivial on the (col, third) pair. **Item (c) is dead for all f.** A useful K₄ piece
  must be non-diagonal in the Weyl basis, i.e. must mix W_s⊗W_t with s ≠ t.


## 2. Task 1: what is needed, precisely, and the triangle Cauchy–Binet lemma

### 2.1 The target [definitions from open-door §1.6–1.7]
Δ₃: nodes n ∈ {α+β+γ = 0} ⊂ Z₃³, edges n → n+(1,1,1) (three directed triangles), merges k = 1,2,3 = the coordinate
projections, groups G^k_g = {n : n_k = g}. Wire n sits on bond (n_k, n_k+1) of merge k, so **the 9 wires ↔ the 9 points
of AG(2,3), the 3 bonds of merge k ↔ the 3 lines of one parallel class, the triangles ↔ the 4th class.** Two distinct
wires share a bond in at most one merge (two points span one line). Each bond carries 3 wires.

A *three-merge piece family with saving ρ* is, for every λ, a set I with |I| = 2^{o(λ)} and tensors A_i on the 18
strings with Σ_i A_i = d·f_C, d ≠ 0, such that the D1 costs (min over exact triangle networks of Σ_bonds log₂ dim)
satisfy V = min_q max_i ⟨q, c(A_i)⟩ ≤ 9ρλ + o(λ) (uniform q suffices by the S₃ symmetry of Δ₃). Target ρ = 1/√3
(b2's floor, [R|PH] optimal), anything < 1/√2 counts. **What must be bounded is the triangle-network cost under each
merge.** The three bipartition ranks rk(G^k_g | rest) give only the lower bound ½Σ_g log rk ≤ c_k and the path upper
bound c_k ≤ log rk(G_i|rest) + log rk(G_j|rest) (MPS); the path bound is ≥ 2√6λ ≈ 4.90λ per merge even with fused
energies and is useless near the floor (x4 §8).

**The graded form.** Give every bond (k,b) its own grading variable X_{k,b} (9 variables). A family is the set of
coefficients Ψ_m, m ∈ Z^9, of a Laurent polynomial Ψ(X) with Ψ(1,…,1) = d·f_C, such that for every merge k the
coefficient of X_{k,0}^{a}X_{k,1}^{b}X_{k,2}^{c} (others as spectators of bounded support) is a triangle network on the
merge-k groups with bond dimensions poly·P(a), poly·P(b), poly·P(c), P(E) = e^{κ√E}. Piece cost
c_k(m) ≤ κ Σ_b √m_{k,b} + o(λ). With one variable per merge only (the "A₂" form X₁X₂X₃ = 1 of the brief), the three
bonds of a merge are graded together and the certified bound is 3κ√N_k, which at the balanced point N_k = Θ/3 is
no better than raw (§2.3). **Bond-level grading is necessary for a certified gain.**

### 2.2 Lemma T (three-group Cauchy–Binet) [R]
Let M = A + Σ_{p≠q} E_p F_{pq} D_{pq} G_{pq} E_qᵀ (mod high powers), A = diag(M_0, M_1, M_2) block-diagonal over the
groups of one merge, F_{pq} with rows in group p, G_{pq} with columns in group q, D_{pq} = diag(X_{\{pq\}}^{2r+1}).
Then
  det M[rows, cols] = Σ_{T} ± Π_{(pq)} X^{E(T_{pq})} · Π_p det [[M_p, F_{p·}|_{T_{p·}}], [G_{·p}|_{T_{·p}}, 0]],
the sum over subsets T_{pq} of the levels of each of the six directed bond blocks. The p-th factor depends only on
group p's symbols and on (T_{pq}, T_{qp})_{q≠p}. *Proof.* det(A + UDV) = Σ_T det D_T · ±det[[A, U_{·T}],[V_{T·}, 0]],
the multilinear expansion the paper uses (B.3, "the coefficients"). The column (pq, r) of U lives in the rows of p and
the row (pq, r) of V in the columns of q, so after reordering the bordered matrix is block-diagonal over groups. ∎

So the coefficient of Π X_{\{pq\}}^{N_{pq}} is a **triangle network** with bond {p,q} carrying the pair
(T_{pq}, T_{qp}), of energy ≤ N_{pq}. Squareness of the p-block is a charge law:
|I_p| − |J_p| = Σ_q (|T_{pq}| − |T_{qp}|). For two groups this is exactly B.3. **x4 §8 step 4 ("the determinant only
gives bipartitions; a trace version is needed") is therefore wrong.** Free-fermion (determinantal) states give
K_r networks for any r. This also answers candidates (b) and (c) of the brief in part: the "torus/trace" structure
is already present in Lemma T, and Gaussian fermionic states are exactly the determinantal case.

### 2.3 Accounting forced by the wires [R]
A wire w at level i has an entry between its two strings that must equal [i=j] at X = 1. In frame k it must be
≡ [i=j]X_{k,b_k(w)}^{2i+1} after gauge, because the wire crosses merge k on bond b_k(w). Summing the frame
energies of the term of det M that realises f_C:
- **Θ = Σ_{k,b} N_{k,b} = 3 · (Σ_w e_w) = 27e.** Each of the 9 wires contributes its energy e to each of its 3 bonds.
  The analogue in App. B is 2 cuts × 2 wires × e = 4e = Θ (x5's β = 4).
- The f_C term sits at the balanced point N_{k,b} = 3e, the analogue of App. B's middle coefficient.
- If the support of Ψ were the whole simplex {Σ N = 27e}, the costs c_k = κ Σ_b √N_{k,b} would fill exactly the ball
  Σ_k c_k² ≤ 3κ²·27e = (9λ)². That is x4's sphere, and its balanced point is the floor 3√3λ.
- With merge-level grading only, the balanced piece has N_k = 9e. The certified cost is then 3κ√(9e) = 9λ, no gain;
  the bipartition lower bound is 1.5κ√(2·9e) = 9λ/√2.

## 3. Task 3: why Δ₃ and not B3; and the sphere law is refuted on Δ₃ too

### 3.1 The property: any two merges pin a node
In Δ₃, G^{k'}_a ∩ G^{k''}_b is exactly one node for k' ≠ k'' (two lines of different classes meet in one point), and
both strings of a node lie in the same group under every merge. On B3 this fails: under two coordinate cuts the
quadrants (x=1,y=0) = {100, 101} and (0,1) = {011, 010} contain two strings on opposite sides of the third cut. On the
rectangle the property holds but there are only two merges, so it constrains nothing.

**Rank lemma (L1).** For disjoint parties A, B, C, D: rk(A | BCD) ≤ rk(AB | CD) · rk(AC | BD).
- [R] when D is trivial (the three-party bound rk(A|BC) ≤ rk(B|AC)·rk(C|AB)).
- [R] for graph tensors and GHZ hyperedges: every wire or hyperedge at A crosses at least one of the two cuts.
- [N] `code/rank_lemma.py`: in 32 alternating-projection instances (dims up to 9×3×3×3, ranks 2–4) no violation, and
  the bound is attained. The same holds for (L2) rk(AD|BC) ≤ rk(AB|CD)·rk(AC|BD).
- [C] in general.

**Proposition 3.1 [R given L1].** On Δ₃ every tensor A satisfies c_k(A) ≤ 4(c_{k'}(A) + c_{k''}(A)).
*Proof.* c_k ≤ log rk(G^k_i|rest) + log rk(G^k_j|rest) (path network). Then:
- log rk(G^k_i|rest) ≤ Σ_{n∈G^k_i} log rk(n|rest);
- by L1 with A = n, B = G^{k'}_{n_{k'}}∖n, C = G^{k''}_{n_{k''}}∖n, we get log rk(n|rest) ≤ ℓ^{k'}_{n_{k'}} + ℓ^{k''}_{n_{k''}},
  where ℓ^k_g = log rk(G^k_g|rest);
- over the 3 nodes of G^k_i, n_{k'} and n_{k''} each run over all three groups;
- for a triangle network, Σ_g ℓ^k_g ≤ 2c_k.
Hence c_k ≤ 2·2(c_{k'} + c_{k''}). ∎

**Corollary 3.2 (sphere law refuted on Δ₃) [R given L1].** By Theorem 1, every identity has a piece with
c_1 ≥ 9λ − o(λ). By 3.1 that piece has c_2 + c_3 ≥ (9/4)λ − o(λ), hence |c|² ≥ (81 + 2.53)λ². **No family has all
its pieces in the ball |c| ≤ 9λ.**
- This complements x4: price lower bounds (star, segment, Euclidean) stay on or inside the sphere (x4 §5), but tensor
  geometry pushes the corners out.
- The B3 refutation (x4 Prop. 4.1) came from a price. This one comes from the structure of single tensors. B3 does not
  have the pinning property, so 3.1 does not hold there. B3 instead fails through the segment price (1,1,3).
- In particular the "fused-accounting" determinantal family of §2.3 cannot exist with Θ = 27e. Its corner piece
  (27e, 0, 0) is a product across merges 2 and 3, hence a product over nodes, hence free in merge 1.
- The repair costs little. Θ must exceed 27e by the energy needed for c_2 + c_3 ≥ 2.25λ at that corner, which is
  ≥ 0.84e when spread over 6 bonds. The balanced piece then costs κ√Θ ≥ √27.84·λ ≈ 5.28λ. That is still far below 9λ/√2,
  so **ρ = 1/√3 + O(0.01) is not excluded by this**; only the literal sphere is.

## 4. Task 2/4: the bond-fusion requirement, and a no-go in the Meixner ansatz

**What a bond must do.** In frame k, the cross block K_{pq} (rows: modes of group p; columns: modes of group q) must
be ≡ F D G with one single-flavour propagator D = diag(X^{2r+1}). A bond with m flavours costs κ√(mE) and gives no
fusion. K_{pq} contains the three wire blocks of the wires on that bond. Write Φ_u for the bond-space vectors of the
out-string of wire u and Γ_u for those of its in-string. Then
- Φ_uᵀ D Γ_u ≡ ±diag(X^{2i+1}): the wire, which generalises (B.1);
- Φ_uᵀ D Γ_v for u ≠ v is junk;
- the actual entries of M must be polynomials whose truncations agree with these sums mod X^{2R};
- at X = 1 the junk must not change det M, which in App. B is achieved by block-triangularity.

In App. B (2 wires per bond) the solution is Φ_a = Γ_c = e (standard basis) and Φ_d = B, Γ_b = (y−1)B (Meixner). The
junk (y−1)DB vanishes at y = 1 and BᵀD is below the diagonal.

**Proposition 4.1 (no three-wire bond in the generalised-Meixner ansatz) [R].** Let each family have generating
vectors (α + a t)^r/(1 + b t)^{r+1}, the class containing both e and B. Then Σ_r y^r Φ_u(r,·)Γ_v(r,·) has generating
function
  1/((1 + b_u t)(1 + b'_v s) − y(α_u + a_u t)(α'_v + a'_v s)).
- Its coefficients are polynomial in y only if α_u α'_v ∈ {0} for u ≠ v. Otherwise they carry the denominators
  (1 − yα_uα'_v)^{i+j+1}.
- Diagonality for u = v forces b_u = yα'_u a_u and b'_u = yα_u a'_u.
- The rank-one matrix (α_u α'_v) with zero off-diagonal has at most one nonzero entry. So at least two of three families
  are standard (Φ, Γ supported on the diagonal).
- Two standard families have junk diag(X(y a_u a'_v)^i) ≠ 0 at X = 1 in *both* directions (u,v) and (v,u). No ordering
  makes the cross block triangular.
- With two wires this leaves exactly App. B's solution. With three it is impossible. ∎

So the obstruction to a third merge, at the level of one bond, is **fusing three wires into one fermion**. Meixner
orthogonality fuses two. A third needs a family with non-polynomial cross terms, or a different evaluation mechanism
than triangularity. Whether some non-Meixner family (e.g. bivariate Meixner/SU(2,1) matrix elements, which brief
item (d) suggests) does it is open [C].

## 5. K₄ (z1's smallest instance), from this angle
- K₄'s three merges are the three pairings of 4 nodes, so (L2) reads c_k ≤ c_{k'} + c_{k''} for every piece
  [N/C as L2]. This is consistent with the target (√2, √2, 0+)λ: pieces with t ≈ 0 have c_row ≈ c_col.
- Weyl-diagonal pieces: c_col + c_third ≥ 2λ (§1), so they are excluded.
- App. B pieces: t = 2λ (x5's third-cut ranks), so they are excluded.
- No finite-size numerics can certify t = o(λ): at fixed N, T pieces give N²/T trivially.

## 6. Honest table

| item | result | tag |
|---|---|---|
| (c) Weyl partial sums, any f | col·third = \|supp f\|·\|supp f̂\| ≥ N²: dead | [R], [N] N ≤ 5 |
| x4 step 4 ("needs trace version") | false for determinants: Lemma T gives triangle networks | [R] |
| A₂ (one variable per merge) | certified balanced cost 9λ: useless; bond-level grading needed | [R] |
| fused accounting | Θ = 27e, costs fill the (9λ)-ball | [R] |
| pinning property (Δ₃ yes, B3 no) | c_k ≤ 4(c_{k'} + c_{k''}); sphere law refuted on Δ₃ | [R given L1], L1 [N/C] |
| one bond carrying 3 wires | impossible in the generalised-Meixner ansatz; 2 wires = App. B | [R] |
| (a)/(b)/(d) explicit constructions | none found | — |
| end-to-end exponent | no improvement over 2^{O(n/√log n)} | — |

**Not done (time box).** Item 5 (independent checker, end-to-end) does not apply, because nothing works. The following
were not attempted:
- an exact symbolic test of Lemma T (it is a two-line Cauchy–Binet);
- the 6j/recoupling idea (coordinator item (a));
- bivariate Meixner families for §4.

x4's coverage caveat stands unchanged: Δ₃ covers one parallel class, only for q = 3^k.

**Next steps, in order:**
1. Prove or refute L1. Its general form is the inequality H₀(A) ≤ H₀(AB) + H₀(AC) for Rényi-0 entropies of pure
   four-party states.
2. Look for a single-flavour bond carrying three wires (the three-family analogue of (B.1)) outside the Meixner class.
   This is the precise local missing step. Without it no determinantal three-merge family can fuse, whatever the
   global design.
