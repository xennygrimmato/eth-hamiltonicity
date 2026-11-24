# z1 notebook: Route 2 (p parallel classes of AG(2,g)) and Route 4 (engine over F₂)

24 Nov 2026. Executor z1. Tags: [R] proved, [N] computed (script named), [C] conjecture,
[R|FH] proved under the flat hypothesis, [R|PH] under the planar hypothesis.

Sources: `next/ideas-3sat.md` (Routes 2, 4), `engine3-STATUS.md`, `engine3-open-door.md` §1.4–1.7, §2.3–2.7,
`vpvnp/b2/notebook.md` and scripts (`far_opt.py`, `verify_flat.py`, `metric_lp.py`).

## Log
- 0:00 read sources; set up folder.
- 0:20 wrote `ag_floor.py` (table), `check_orth.py` (independent finite-M checker). 0:45 table g = 2..5 (g = 5 still running).
- 1:00–2:00 Route 4 (eight-square, Fock mod q, N₀ = 2 exhaustive). 2:00–2:50 K₄ test, Weyl brainstorm, notebook.

## 1. Route 2, step 1: the floor table [first version, 0:50]

**Setting.** Level on AG(2,g): K = g² nodes, all C(K,2) edges as ONE configuration (so edges of merge classes are
included: an edge of class c is internal to merge c, Δ^c_e = 0, and costs 0 there). Merges = p of the g+1 parallel
classes. ρ is normalised by ALL edges, C(K,2)λ, because that is the recursion's denominator (e_{ℓ+1}S_{ℓ+1} = e_ℓ·cost).
PΓL(2,g) is transitive on every p-set of classes for g ≤ 5, so one price gives V ≥ (Σ_k b_k)/p [R].

**Closed forms [R].**
- Orthogonal price (hubs of merge k on a regular simplex in its own orthogonal block, u_e ∥ Σ_kΔ^k_e):
  **ρ_orth(p,g) = (√(p−1) + (g+1−p)/√p)/(g+1)** — a lower bound on ρ [R|FH]. Checked per merge with exact distances
  at M = 10⁷ (`check_orth.out`, all 14 (g,p) agree to 5 digits).
- **Cap of the far-leg Euclidean method [R]:** Σ_e|Σ_kΔ^k_e| ≤ √E·(Σ_e|Σ_kΔ^k_e|²)^{1/2}, and the cross terms
  Σ_e⟨Δ^k_e,Δ^{k′}_e⟩ vanish for k ≠ k′ over all pairs (two lines of different classes meet in exactly one point;
  checked numerically, `check_orth.out`), so the method can never certify more than **√(g/(p(g+1)))**. At p = g+1
  this equals ρ_orth: the orthogonal price is optimal there.
- Pigeonhole/star (Theorem 1 generalised, every field): ρ ≥ g/((g+1)p).
- "sep" = the floor if merge-class edges are kept as separate raw configurations (Route 2 as first written):
  ((p−1) + (g+1−p)/√p)/(g+1). At p = g+1 this is g/(g+1): no gain at all. **Internal edges only help if they are
  bundled into the same configuration as everything else.**

| g | p | ρ_orth [R/FH] | method cap | Euclid opt [N] | line price [R, uncond.] | star [R] | sep | 1/√p | reading |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 2 | 0.569 | 0.577 | 0.569 | 0.500 | 0.333 | 0.569 | 0.707 | = Anthropic level at g=2 (App. B + straight edges): floor attained |
| 2 | 3 | 0.471 | 0.471 | 0.471 | 0.333 | 0.222 | 0.667 | 0.577 | K₄ with 3 matchings; smallest instance below the p=2 value |
| 3 | 2 | 0.604 | 0.612 | 0.604 | 0.389 | 0.375 | 0.604 | 0.707 | = Anthropic level at g=3, attained |
| 3 | 3 | 0.498 | 0.500 | 0.498 | 0.333 | 0.250 | 0.644 | 0.577 | first ≤ 1/2 under FH |
| 3 | 4 | 0.433 | 0.433 | 0.433 | 0.292 | 0.188 | 0.750 | 0.500 | all classes; orth optimal |
| 4 | 2 | 0.624 | 0.632 | 0.624 | 0.400 | 0.400 | 0.624 | 0.707 | Anthropic, attained |
| 4 | 3 | 0.514 | 0.516 | 0.512* | 0.333 | 0.267 | 0.631 | 0.577 | |
| 4 | 4 | 0.446 | 0.447 | 0.445* | 0.292 | 0.200 | 0.700 | 0.500 | |
| 4 | 5 | 0.400 | 0.400 | (running) | | 0.160 | 0.800 | 0.447 | all classes |
| 5 | 2..6 | 0.638, 0.524, 0.455, 0.408, 0.373 | | (running) | | | | | |
(* SLSQP found slightly less than the closed form: local optimum; the closed form is the valid bound.)

**One-paragraph reading.**
1. For p = 2 the flat floor *with* internal edges equals exactly what Anthropic's level achieves at every g
   ((g−1)/(g+1) rectangles at 1/√2, 2/(g+1) straight edges at 1/2) [R|PH]: the accounting is calibrated.
2. **The floor does not stay ≥ 1/√2: it drops like 1/√p**, and internal edges lower it slightly further
   (ρ_orth·√p = (√(p(p−1)) + g+1−p)/(g+1) < 1). So the "door is open in the flat case" for every p ≥ 3, and
   below 1/2 from p = 4 (and p = 3 at g ≤ 3). There is no new barrier.
3. But internal edges are a **lower-order effect**: for fixed p and g → ∞ (which the squaring recursion needs),
   ρ_orth → 1/√p and the cap → 1/√p, i.e. exactly b2's fully-crossing floor; α′_flat = ½ log₂ p. Route 2 therefore
   reduces to Route 1's question (is 1/√p attainable for p ≥ 3?), not to a new one.
4. **Unconditional line prices also decay like 1/√p** (≈ E|S−S′|/p with S a sum of p pairwise independent bits,
   ≈ 1/√(πp) ≈ 0.56/√p) [R for each table entry, asymptotic form C]. So neither floor closes the door for growing
   p; equally, no unconditional floor stops α′ → ∞ as p → ∞.
5. p = g+1 (all classes): ρ ≥ √g/(g+1) ≈ K^{−1/4} per level; iterated with K_{ℓ+1} ≈ K_ℓ² this gives
   e(K) ≳ K^{−1/2}·(log K)^{O(1)} — the same order as b1's oblivious floor 1/(16√K). So the AG(2,g)-all-classes tower
   is *flat-optimal up to constants*: if its flat floor were attained, 3-SAT would run in 2^{n^{1−1/18+o(1)}}
   (K ≈ n^{1/9}) [D, modulo the term-count caveat of the ideas file].

### 1.1 Table completed for g = 4, 5 [N, `ag_floor_45.out`]
g = 4, p = 5: orth 0.400 = cap 0.400, Euclid 0.398, line 0.267, star 0.160.
g = 5, p = 2…6: orth 0.638, 0.524, 0.455, 0.408, 0.373; caps 0.646, 0.527, 0.456, 0.408(p=5), 0.373(p=6);
line 0.380, 0.320, 0.282, … (see file). Same pattern as g = 3, 4: line ≈ (0.62–0.67)·orth, both ∝ 1/√p.

**ρ and α′ (if the flat floor were attained).**

| regime | ρ_flat | α′ = log₂(1/ρ) | end-to-end |
|---|---|---|---|
| p = 2, any g (Anthropic; attained) | → 1/√2 | 1/2 | 2^{O(n/√log n)} (current) |
| p = 3, g → ∞ | → 1/√3 | 0.79 | 2^{O(n/(log n)^{0.79})} |
| p = 4, g → ∞ | → 1/2 | 1 | 2^{O(n/log n)} |
| p fixed, g → ∞ | → 1/√p | ½log₂p | 2^{O(n/(log n)^{½log₂p})} |
| p = g+1 (all classes) | √g/(g+1) ≈ K^{−1/4} per level | — (polynomial) | e(K) ≈ K^{−1/2}: 2^{n^{1−1/18+o(1)}} |
| unconditional (line prices), p fixed | ≳ 0.56/√p | ≤ ½log₂(πp) | no door closed |

Fixed-g α′ values in the table (`alpha_orth` column of the .out files, e.g. 1.21 at (3,4), 1.32 at (4,5)) are not
end-to-end exponents: the recursion needs g → ∞, where only the 1/√p part survives.

## 2. Route 2, step 2: a construction at the smallest instance

**Instance.** The smallest (g,p) whose flat floor lies below the p = 2 value at the same g is g = 2, p = 3:
K₄ with its three perfect matchings as merges (S1 = ab|cd, S2 = ac|bd, S3 = ad|bc), ρ_flat = √2/3 = 0.471
(= method cap, so the far-leg method is exact here), versus 0.569 for p = 2, trivial 4/6, unconditional 1/3.
Not an asymptotic level (K = 4 → 2), but the cleanest test of "internal edges + a third merge".

**Class-by-class generalisation of App. B [R].** K₄ = X₁ ⊗ X₂ ⊗ X₃, X_k = the crossing formed by the two edges of
class k; X_k crosses the two merges ≠ k and both its edges are internal to merge k. Product pieces
P¹⊗P²⊗P³ have Σ_k c_k = Σ_j (r_j + c_j + t_j), where (r_j, c_j) are the costs of P^j on its two crossing merges and
t_j its cost on its own merge (the split separating its two edges). So the product family reaches the flat floor
2√2λ per merge iff crossing pieces exist with r + c ≤ 2√2λ AND t = o(λ). Facts:
- the price method cannot see t: for a merge under which both edges are internal, L − H ≤ 0 by the triangle
  inequality, so b_t ≤ 0 for every price [R]. The flat floor therefore *allows* (√2, √2, 0)λ.
- **t = 0 exactly is impossible [R]:** if every piece is a product α(x,v)⊗β(y,u) across that split, its row and
  column flattenings are α⊗β and α⊗βᵀ (partial transpose), both of rank rk α·rk β, and Σ rk α·rk β ≥ N², so some
  piece costs ≥ 2λ − log T in both crossing merges: no trade at all.
- App. B pieces are generically full rank (N²) across the third split (span of Q_s(a_x,b_v) over x,v), t = 2λ:
  the product family costs Σ = 2√2 + 2 = 4.83 > 4 per crossing, *worse than trivial* [C, by the span argument;
  not computed].
- Beating 1/2 on K₄ (normalised by all 6 edges) needs t < (3 − 2√2)λ ≈ 0.17λ; beating trivial needs t < 1.17λ.
So the class-by-class route needs a new object: crossing pieces with the sphere law in two directions and
2^{o(λ)} operator-Schmidt rank in the third (i.e. a decomposition of I⊗I into 2^{o(λ)} pieces of small rank,
small partial-transpose rank and small realignment rank). Open; I found no inequality excluding it, and none
constructing it.

**Exact small test (N₀ = 2) [N, `k4_als.py`].** Two-type identity f = A + B with A a product across S3 and B a
product across S1 (the two-type shape that would give value + naming ≈ 2.95 < 3 at N₀ = 2: A = (log 15, ·, 0), B = (0, ·, log 15),
mixture ½–½); result in §2.1.

## 3. Route 4: the engine in positive characteristic

**Which floors survive [R, from b2 §2 and the definitions].** Theorem 1 (two merges, ρ ≥ 1/2), the star prices,
segment (line) prices and hence the whole "unconditional" column of §1 hold over every field (Strassen support
functionals). The core floor as written uses CVZ (ℂ); its proof only needs a subadditive, restriction-monotone
functional with value N^{2E_cross/g_H} on graph tensors and ≤ 2^{2c/g_H} on networks, which Strassen's upper support
functional provides on oblique (graph) tensors, so it holds over every field as well [R, same lift as b2's Q1].
The flat floors are [R|FH] *per field*; whether FH/PH hold over F̄₂ is the open dichotomy. The HWY sum-of-squares
obstruction is characteristic-0 only.

**Level tensors [R].** f_C is a 0/1 tensor that is a tensor product of identity matrices; every flattening is a
permutation matrix times an all-ones-free product, so its ranks are the same over every field (checked: f at N₀ = 8
has (64,64) over ℚ, GF(3), GF(2), `f2_pieces.out`). All field dependence is in the pieces.

**The existing crossing pieces, reduced mod q [N].**
1. **Eight-square pieces (Lemma 2, N₀ = 8), `f2_pieces.out`, `cd_ranks.out`, independent check `check_gf3.out`.**
   Identity R + C = 2f.
   - ℚ, GF(5), GF(7), GF(11), GF(13): ranks R (row 8, col 64), C (64, 8): ρ = (3+6+2)/12 = 11/12.
   - **GF(3): R has column rank 56, C row rank 56** (det of the 64×64 flattening = 2⁶⁴·3⁸, rank mod 3 = 56,
     confirmed with sympy on an independently built Fano-plane octonion table). Ranks are multiplicative under
     Kronecker products, so Lemma 2's tensored family over GF(3) has **ρ = (3 + log₂56 + 2)/12 = 0.9006 < 11/12**
     exactly, α′ = 0.151 instead of 0.126 [N, exact]. This is a genuine field dependence of a certified exponent
     (answering x5's question in the affirmative for these pieces), usable for decision by counting mod 3 with
     isolation. It is far from 1/√2 and is **not** an improvement over App. B.
   - GF(2): d = 2 = 0, and R ≡ C mod 2 with ranks (8, 8): the identity becomes 0 = 0. No pieces.
   - Quaternion version (N₀ = 4): no rank drop in any characteristic tested; ρ = 1.
2. **App. B / Fock pieces, h = 2…5 (`fock_modp.out`, using `scripts/pieces_fock_ranks.py` unchanged).**
   Σ_s A_s = h!·f, so **for every prime q ≤ h the identity vanishes mod q; in particular over F₂ for all h ≥ 2.**
   Dividing out q^{v_q(h!)} does not rescue it: some pieces have smaller q-adic content (`fock_padic.out`,
   q = 2, 3, h = 2…5: "all pieces divisible: False"). So **App. B does not exist in characteristic 2**, and in
   characteristic q it exists only for h < q (fine for an algorithm: choose a prime q > h = poly(λ)).
   For the smallest valid prime q just above h the worst piece's (c_r + c_c)/(4λ) drops below its ℚ value
   (h=2/GF(3): 0.75 vs 1.00; h=3/GF(5): 0.946; h=4/GF(5): 0.981; h=5/GF(7): 0.997), but the drop shrinks with h
   and is absent for larger q. No evidence of an asymptotic (2^{Ω(λ)}) rank gain [N, small h only].
3. **Exhaustive N₀ = 2 search (one bit per leg), all T [N, `f2_pieces.out`].** For ρ < 1 every piece must have
   rank 1 in one flattening (else its pure strategy costs ≥ 1 bit and naming adds ≥ 1); T ≥ 4 is excluded by naming
   alone. Over GF(2): best T = 2 family ρ = 1 (App. H profile (1,4)/(4,1)), best T = 3 family ρ = 1.12. GF(3):
   identical optima (T = 2: ρ = 1; T = 3: ρ = 1.12). **F₂ and GF(3) are equal at N₀ = 2: the Route-4 first
   experiment fails.**

**Reading.** Over F₂ the engine loses *both* known crossing constructions (d = 2 and d = h! vanish), so the
characteristic-2 engine currently has no trade at all (ρ = 1 at every computed size); Theorem 1's 1/2 still bounds
it below. The only measured field effect is a constant-factor rank drop in characteristic 3 for the eight-square
pieces. Route 4's "first experiment" fails at N₀ = 2 (equal optima); its premise (F₂ makes things easier) is
contradicted by the observation that the known identities need d invertible and d is even.

## 4. Brainstorm item: Weyl/Heisenberg partial sums as crossing pieces [N, `weyl_pieces.out`]

In operator language the crossing f = [x=v][y=u] is SWAP as a map (u,v) → (x,y) (row split, rank N²); the column
split is its realignment (operator-Schmidt rank N²); the third split (both edges internal) is its partial transpose
(rank 1). SWAP = (1/N)Σ_{(a,b)∈Z_N²} W_ab ⊗ W_ab†. Pieces A_S = (1/N)Σ_{S} W⊗W† for S = cosets of every subgroup
H ≤ Z_N², and for Weyl balls, N = 2…5, ranks (row, col, third) by SVD:
- **Cosets of H: (row, col, third) = (N²/|H|, |H|, t(H))** for every subgroup and every coset (all N ≤ 5), with
  t = |H| for |H| ≤ N (e.g. Lagrangian/cyclic |H| = N: (N, N, N), costs (1,1,1)λ) and t = N²/|H| for |H| ≥ N
  (N = 4, |H| = 8: (8, 8, 2)). So **row·col = N² exactly**: each coset is cheap (c_row + c_col = 2λ, i.e. "ρ = 1/2" on
  the two crossing merges, plus third cost ≤ λ), but there are N²/|H| cosets, and grouping cosets adds ranks. With
  |H| = N^α the naming is (2−α)λ per merge, which puts the family back at ρ = 1 — the Strassen/rank-one trap of
  open-door §1.7, with a third split attached. Weyl balls are worse: row rank stays N² (ball r ≥ 1), and only N = 5,
  r = 1 shows a third-split drop (25 → 17).
- Conclusion [N, small N]: subgroup/ball partial sums give no 2^{o(λ)}-piece family; any useful family must group
  exponentially many cosets into one piece *with rank cancellation*, which is what App. B's Fock grading does in two
  directions. The three-rank object of §2 is not produced by Weyl partial sums.

### 2.1 Result of the two-type K₄ test [R + N]
- ALS (`k4_als.out`, one restart, 20 sweeps): residual 0.92 — nowhere near an identity.
- **Exact impossibility, every N [R].** Suppose f = α_{ad}⊗β_{bc} + γ_{ab}⊗δ_{cd}. Fix all legs of d (and the
  legs of a, b, c toward d to the matching values): f becomes the triangle tensor ⟨N,N,N⟩ on a, b, c, the first term
  becomes (vector on a)⊗(matrix on b,c), the second (matrix on a,b)⊗(vector δ on c). Contract the c-party with any w
  in the hyperplane w ⊥ δ: the second term dies, so the slice T(w) (an a|b matrix) has rank ≤ 1. But every non-zero
  slice of ⟨N,N,N⟩ has rank N·rank(W) ≥ N ≥ 2. Contradiction. So no two-type family of this shape exists at any
  block size; at N₀ = 2 with T = 2 nothing below the trivial value is possible on K₄ with three merges.
- Asymptotic K₄ question (2^{o(λ)} pieces, value < 2√2λ·… ) remains open; it is the three-rank object of §2.

## 5. Final summary (2:55)
- Route 2 table complete (g = 5, p = 6 last row in `ag_floor_45.out`). Floors with internal edges drop like 1/√p;
  internal edges are a lower-order effect; door open in the flat case; unconditional line prices also ∝ 1/√p.
  Reduction: Route 2 = "is 1/√p attainable for p ≥ 3" (Route 1's question). p = g+1 tower would be flat-optimal
  (e(K) ≈ K^{−1/2}, b1's order).
- Smallest test instance: K₄ with three matchings, ρ_flat = √2/3; needed object: crossing pieces with sphere-law
  costs in two directions and 2^{o(λ)} cost in the third. Exact negatives: t = 0 impossible; two-type shape impossible.
- Route 4: F₂ kills both known identities (d = 2, d = h!); no F₂ trade at N₀ = 2 (equal to GF(3)); a genuine
  characteristic-3 gain for eight-square pieces (11/12 → 0.9006), not an end-to-end improvement.
- No claimed improvement over 2^{O(n/√log n)}.
- g=5,p=6 final row [N]: 5 6 300  0.3727      0.3727          0.3693     0.2333(ls400)  0.1389  0.8333  0.4082  1.424
