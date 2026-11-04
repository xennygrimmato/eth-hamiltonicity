> **Status of these notes.** Informal research notes, **not claimed** (no [Lean] tag). Tags used below:
> **[Lit]** = stated in a primary source (cited); **[Folklore]** = standard, no single source located;
> **[Mine]** = my own derivation, with a full short proof here; **[Mine-sketch]** = my own, proof only sketched;
> **[Open]** = no result found either way. Literature search: web, 2026-11-04.

# Circuit complexity of cycle parity on a fixed sparse graph: status

Context: `linear-encoding.md` reduces a linear-size signed #SAT encoding of `n·#HC(G)` to computing
`c(π) mod 2` (the number of cycles) for a partial permutation `π` whose arcs lie in `G`.

## 0. Verdict

| question | status |
|---|---|
| `O(m log m)` upper bound | **known** (D&C 2D-dominance parity, Lemma C of `linear-encoding.md`). Best constant I can derive: `2(m−n+1)·⌈log₂ m⌉ + O(Δ·m)` [Mine-sketch, §3.3]. For cubic graphs that is `≈ (2/3)·m log₂ m`. |
| `O(m log log m)` or `O(m)` for general bounded-degree `G` | **[Open].** Nothing found. `O(m)` holds for graphs with small genus, crossing number or separators [Mine-sketch], but #HC is already `2^{o(n)}` on those graphs, so it does not help. The hard case is bounded-degree expanders, which have genus `Θ(m)`, crossing number `Θ(m²)` and separators of size `Θ(m)`. |
| superlinear lower bound | **not known and currently out of reach.** The best lower bound for *any* explicit function in the full binary basis is `3.1n − o(n)` [Lit: Li–Yang, STOC 2022]. A size-`O(m)` circuit would contradict **no** known result. |
| "cycle parity is ⊕L-complete" | **False** for this presentation. The function is a GF(2) quadratic form, so it lies in `AC⁰[⊕]` (depth 2, size `O(m²)`). It is **provably not** ⊕L-hard (or L-hard) under AC⁰ reductions (§2). ⊕L-complete problems are, e.g., det over GF(2) [Lit: Damm 1990]. |
| linear-size signed (GapP-type) witness | **[Open].** It is no harder to get than a circuit. A sufficient condition is a sparse *implicit* (Schur-complement) representation of the quadratic form (§5). It would imply neither linear circuits nor anything about ⊕L, and it contradicts no known bound. |
| `Cross(x)` / inversion parity of a selected subsequence | Same status as above: an explicit GF(2) quadratic form with `O(N log N)` circuits and no superlinear lower bound. It runs in **`O(N)` word-RAM time** (§6), so the `Ω(N log N)` comparison bound is irrelevant. |

## 1. The function, and why it is a quadratic form

**Definition.** Fix `G = (V,E)` with `|V| = n`, `|E| = m` and max degree `Δ`, and let `A(G)` be its `2m` arcs.
`CP_G : {0,1}^{A(G)} → {0,1}` is defined on the promise that the 1-arcs form vertex-disjoint directed cycles (a partial
permutation `π`; uncovered vertices are fixed points). Its value is `c(x) mod 2`, the number of cycles.
`sgn(π) = (−1)^{n − c(x) − #fix(x)}` and `#fix` is a linear form, so CP_G and the sign are interchangeable at `O(m)` extra cost.

**Fact 1.1 [Folklore; e.g. in R. J. Lipton's blog post "Graphs, permutations, characters and logspace", 2009].**
`c(π) ≡ n + inv(π) (mod 2)`, where `inv(π) = #{i<j : π(i) > π(j)}`.

**Corollary 1.2 [Mine, immediate].** Number `V` and add the diagonal points `(i,i)` for fixed points, with the indicator
`f_i = 1 ⊕ ⊕_{a out of i} x_a` (affine). Then
`CP_G(x) = n ⊕ ⊕_{p,q ∈ P, p dominates-inversely q} y_p y_q`, where `P = A(G) ∪ diag` (`|P| = 2m+n`) and `y = (x, f)`.
So on the promise, CP_G is a **GF(2) polynomial of degree 2** in `x`: it is an offline *2D-dominance parity*. Lemma W of
`linear-encoding.md` gives a second quadratic form, `Cross ⊕ Σρ_v`, over the `m` undirected chords in convex position.

(I also tested an orientation-free "peak" variant, `c ≡ Cross + #{v : both neighbours below v}`, for *undirected*
2-regular graphs. It is **false**: about 40% failures in random tests, script in the scratchpad. The orientation is needed.)

## 2. Where it sits among complexity classes

* **Upper bound [Mine, from 1.2].** A depth-2 `⊕∘∧` circuit of size `O(m²)` computes it, so it is in `AC⁰[⊕]`. For
  permutations in list form it is also in `AC⁰[⊕]`, since each comparison is AC⁰. That is what lies behind Lipton's remark that
  the parity is "quite simple for a constant depth polynomial circuit that has mod 2 gates".
* **Not ⊕L-hard [Mine, short proof].** Suppose it were ⊕L-hard under AC⁰ (or even AC⁰[⊕]) reductions. Then
  `L ⊆ ⊕L ⊆ AC⁰[⊕]`. But MAJORITY ∈ L and MAJORITY ∉ AC⁰[⊕] [Lit: Razborov 1987; Smolensky, STOC 1987].
  So the premise "permutation cycle parity is complete for ⊕L" is **wrong**.
  * What *is* ⊕L-complete: det/rank over GF(2) [Lit: Damm, IPL 36(5) 1990; Buntrock–Damm–Hertrampf–Meinel, Math. Syst. Theory 25 (1992)].
  * What is L-complete (under NC¹ reductions, so weak reductions): the cycle structure itself, e.g. "same cycle?" and
    one-cycle vs two-cycles [Lit: Cook–McKenzie, J. Algorithms 8 (1987)].
  * The parity forgets exactly the global information that makes those problems L-complete.
* **Bounded depth without ⊕ [Mine].** PARITY of `k` bits reduces by projection to CP_G for a disjoint union of `k`
  6-vertex gadgets: each bit chooses between two triangles and one hexagon. So AC⁰ needs size `exp(Ω(m^{1/(d−1)}))`
  [Lit: Håstad 1986], and de Morgan formulas need size `Ω(m²)` [Lit: Khrapchenko 1971]. These gadget graphs are
  planar and have `O(m)` circuits, so **these bounds say nothing about circuit size**.
* **Monotone.** This is irrelevant in practice. For slice functions, monotone size ≤ `2C(f) + O(m log² m)` [Lit: Berkowitz 1982,
  as stated in lecture notes]. A monotone lower bound would therefore be a general lower bound, and none is known.
* **Width-bounded branching programs.** By Barrington, the function has polynomial-size width-5 BPs, since `AC⁰[⊕] ⊆ NC¹`.
  Nothing linear is known. I tried a rank/communication argument across a cut. The naive identity
  "`(−1)^{c(M∪N)} = ±sgn(M)sgn(N)`" for matchings is **false**: I checked it numerically, and the Pfaffian signs live in the skew entries.
  I make no OBDD claim.

## 3. Upper bounds on circuit size

3.1 **[Folklore/Mine] `O(m²)`, and `O(m + cr(D))` for any drawing `D` of `G`.**
Whitney's formula (Lemma W, in general form) gives `c ≡ Σ_cycles(rot + #self-crossings + 1)`. In any fixed drawing, the
rotation number is a sum of local turning terms. Use polygonal edges with all angles in `(2π/K)ℤ`, `K = O(Δ)`, and a
mod-`2K` counter, which costs `O(Δm)` gates. The crossing parity is `⊕_{crossing pairs (e,f) of D} x_e x_f`.

3.2 **[Lit-derived, in-repo] `2m'⌈log₂ n⌉ + O(m)`** via Lemma C (D&C dominance parity, convex drawing, `m' = m − d_r`).
Measured: `≈ 1.55·m log₂ n` crossing variables.

3.3 **[Mine-sketch] `2(m−n+1)⌈log₂ m⌉ + O(Δm)`: the spanning-tree drawing.**
1. Draw a spanning tree `T` in a small disk `U` on the sphere. Then `∂U` is the Euler tour of `T`.
2. Draw each of the `m−n+1` non-tree edges as a geodesic chord of the complementary disk, ending at its own slot of `∂U`
   (at its rotation position).
3. Tree edges cross nothing. Two chords cross at most once, and they cross iff their slots interleave.
4. By 3.1, CP_G = (interleaving parity of the active chords) ⊕ (local terms). Apply Lemma C to `m−n+1` chords with
   `2(m−n+1)` distinct circle points. No ties occur, so the `DT` correction is a single prefix pass.

For cubic `G`, this is about 3× fewer chords than 3.2.

3.4 **[Mine-sketch] `O(m + g log g)` with `g` = genus of some embedding of `G`.**
* On a surface with a spin structure, Johnson's quadratic form `q` on `H₁(S;ℤ/2)` satisfies `q(γ) = wind_ξ(γ) + 1` for simple
  closed curves. It is additive on disjoint curves. [Lit: D. Johnson, J. London Math. Soc. 1980; discrete version:
  Cimasoni–Reshetikhin, CMP 2007.]
* So `c ≡ q([π]) + Σ local winding terms`.
* `[π] ∈ (ℤ/2)^{2g}` costs `O(m)` gates, using cotree prefix-XORs in a tree–cotree decomposition.
* `q` in the tree–cotree basis is again a chord-interleaving form on `2g` chords (the Euler tour of `T`), so Lemma C gives
  `O(g log g)`.
* This interpolates between planar (`O(m)`) and 3.3. It is useless for expanders.

3.5 **[Mine-sketch] `O(m)` for hereditary classes with `O(n^{1−ε})` separators.**
* Recurse on an `r`-division. Each piece returns, in list form, the pairing its internal paths induce on its boundary,
  plus the parity of its closed cycles.
* Composing two pairings on `b` boundary points costs `b·polylog b` (pointer jumping and routing).
* So `f(n) = 2f(n/2) + O(n^{1−ε} polylog n) = O(n)`.
* Again, #HC on these classes is already `2^{o(n)}`.

3.6 **General bounded-degree `G`: nothing better than `Θ(m log m)` is known [Open].** Related results, none of which transfers:
* Chan–Pătraşcu (SODA 2010), *Counting inversions, offline orthogonal range counting, and related problems*: `O(n√log n)` word-RAM.
  It uses word packing, so it does not carry over to circuits.
* Asharov–Lin–Shi, *Sorting short keys in circuits of size o(n log n)* (SODA 2021 / SICOMP 2022): their bound beats AKS only for
  keys of `o(log n)` bits. Our "keys" are vertex names with `log n` bits.
* Network-coding-conditional `Ω(n log n)` bounds [Lit: Afshani–Freksen–Kamma–Larsen, ICALP 2019 (multiplication); ALS21 (sorting)]
  need many output bits, so they **do not apply to a 1-bit function** [Mine, remark].

## 4. Lower bounds (what exists)

* **General B2 circuits:** `3.1n − o(n)`, for affine dispersers [Lit: Li–Yang STOC 2022; previously
  `(3+1/86)n` by Find–Golovnev–Hirsch–Kulikov FOCS 2016]. There is no superlinear lower bound for any function in NP, so an
  `Ω(m log m)` (or even `ω(m)`) lower bound for CP_G would be a breakthrough. Equally, **an `O(m)` upper bound would violate nothing.**
* **Multiplicative complexity [Lit: Mirwald–Schnorr, TCS 102 (1992)].** A quadratic form `x^T A x` needs exactly
  `rank_{GF2}(A+A^T)/2` AND gates. So CP_G needs at most `m+O(n)` AND gates in total. **The whole question is the XOR (linear)
  part**, that is, a linear-circuit question in disguise.
* **Linear circuits.** No superlinear lower bound is known for any explicit matrix in unbounded depth [Lit: Valiant, MFCS 1977
  (rigidity program); Jukna–Sergeev, *Complexity of linear boolean operators*, FnT-TCS 2013]. For dominance/range
  matrices, polylog lower bounds exist only in data-structure models:
  * semigroup (no cancellation): Chazelle, J. ACM 1990, `Q = Ω((log_{2S/n} n)^{d−1})`; Afshani 2019 for low space;
  * group model: Larsen, FOCS 2011 / SICOMP; the best static bound against linear space is `Ω̃(log n)` for 2D.

  None of these bounds unrestricted-cancellation GF(2) circuits. Chazelle's off-line paper (DCG 1997) is from memory, not verified.
* **Baur–Strassen does not transfer [Mine, remark].** For arithmetic circuits, size `s` for `x^T A y` gives a linear circuit of size
  `O(s)` for `A` (derivatives). Boolean circuits compute the form only as a function on the cube, where formal and discrete
  derivatives differ, so this does not carry over.

## 5. The signed / GapP variant

**Definition.** A *gap witness of size s* for CP_G is a width-3 CNF `φ(x,y)` with `s` variables plus clauses and a variable `z`
such that `Σ_{y : φ(x,y)} (−1)^{z} = C·(−1)^{c(x)}` on the promise, with `C ≠ 0` independent of `x`.
Let `s_gap(G)` be the least such `s`. The labs' engines take signed counts natively (`#(Φ∧¬z) − #(Φ∧z)`, or integer node weights).

* **(a) [Folklore]** `s_gap ≤ 4·s_circ + O(m)`, by Tseitin (parsimonious, unique extension).
* **(b) [Mine, proof] Gauss-sum criterion.** Suppose that on the promise
  `CP_G(x) = x^T C x ⊕ x^T B w`, where `w` is the unique solution of `M w = B' x` and `M` is invertible over GF(2).
  Then `Σ_{w,u ∈ GF(2)^k} (−1)^{u^T(Mw ⊕ B'x) ⊕ x^T C x ⊕ x^T B w} = 2^k (−1)^{CP_G(x)}`, because `Σ_u (−1)^{u·v} = 2^k[v=0]`.
  So `s_gap = O(nnz(M)+nnz(B)+nnz(B')+nnz(C))`.
  * A linear circuit is the case where `M` is unit lower-triangular (forward substitution).
  * General sparse `M` (sparse linear *systems*, with possibly dense inverses) is a priori stronger.
  * Whether the dominance form has such an `O(m)` representation is **[Open]**.
* **(c) [Mine; also in `linear-encoding.md` §4.3] Positivity barrier.** Any witness of the form "colour each cycle consistently,
  homogeneous local weights" contributes `tr(M^L)` per cycle. If `tr(M^L)` is the same constant for all `L ≥ 3`, then only
  eigenvalue 1 survives and the constant is ≥ 0. So `−1` per cycle needs the geometry: crossings, or spin/winding as in 3.4.
* **(d) [Mine] Residues are cheap.** With `q` colours, constant along mixed arcs, `Σ_η q^{c(η)}` is a #SAT count of size
  `O(m log q)`. Reducing mod `q+1` gives `n·#HC(G) mod (q+1)`. That is cheap for `q = 2^{o(√log m)}`, but CRT up to `n·n!` needs
  `log q ≈ log n`, which is back to `Θ(m log n)`.
* **(e) Determinant / GapL.** `sgn(π) = det(P_π)`. DET is GapL-complete [Lit: Toda 1991; Vinay 1991; Damm 1991;
  direct combinatorial proof via clow sequences, Mahajan–Vinay, Chicago J. TCS 1997]. Clow-sequence ABPs give a gap
  witness of polynomial size, `Θ(n²m)`-ish, nowhere near linear. Since CP_G ∈ AC⁰[⊕] (§2), the GapL machinery is overkill.
  The issue is linear vs `m log m`, not the class.
* **(f) Consequences of a linear gap witness.** It gives **no** circuit: evaluating `Σ_y` is exponential. It does not bear on
  ⊕L, because CP_G is not ⊕L-hard. It contradicts **no** known lower bound, since none beyond `3.1n` exists even for
  deterministic circuits, and nondeterministic/gap circuits are only stronger.

## 6. `Cross(x)` / inversion parity of a selected subsequence

`Inv_σ(x) = ⊕_{i<j, σ_i>σ_j} x_i x_j` for a fixed `σ ∈ S_N` is offline 2D-dominance parity on the points `(i,σ_i)`.
* **Known:** `O(N log N)` circuits (Lemma C); multiplicative complexity `≤ N/2` (Mirwald–Schnorr).
* **No** superlinear lower bound is known, by §4.
* **[Mine]** Word-RAM time `O(N)`: mark the selected values, rank them by prefix sums, then count the cycles of the induced
  permutation in list form. The `Ω(N log N)` comparison/sorting bound therefore does not even apply to RAMs computing
  the *parity*, let alone to circuits. RAM-to-circuit simulation costs `polylog` factors, because of pointer chasing.
* For CP_G restricted to expanders I found no reduction in either direction to general `Inv_σ` [Open].

## 7. Conditional statements for the paper

**Theorem (conditional; relative to Anthropic's MainTheorem [Lean] and OpenAI's `exact_count_and_sat` [Lean]).**
Let `Δ` be fixed. Suppose that for every graph `G` with `m` edges and maximum degree `≤ Δ`, a B2-circuit for CP_G of size
`≤ s(m)`, or more generally a gap witness of size `≤ s(m)`, can be constructed in time `T(m)`. Then:
1. there is a width-3 CNF `Φ_G` with a designated variable `z`, with `N_v ≤ s(m) + 26m + O(n)` variables and `O(s(m) + m)` clauses,
   such that `n·C·#HC(G) = #(Φ_G ∧ ¬z) − #(Φ_G ∧ z)`;
2. hence `#HC(G)` can be computed in time `T(m) + 2^{O((s(m)+m)/√log(s(m)+m))}` (via Anthropic), and in time
   `2^{O(N_v (log log N_v)²/√log N_v)}` (via OpenAI).

In particular:
* `s(m) = O(m)` gives `2^{O(m/√log m)}`;
* `s(m) = o(m√log m)` gives `2^{o(m)}`;
* `s(m) = O(m log m)` (the known bound) gives nothing.

*Proof.* Take the CNF of `linear-encoding.md` §5 and replace its Crossing block and `ρ_v` block by
`z := CP_G(a)`, where `a_{i→j} = [edge ij in state A_ij]`, computed with `O(m)` gates. The circuit is Tseitin-encoded
(parsimonious); a gap witness is conjoined, and the constant `C` is the witness's. Lemma S2 gives `κ = (−1)^{c}`.
The rest is unchanged. ∎

**Contrapositive (a uniform lower bound from counting hardness).** If #HC on max-degree-`Δ` graphs is not solvable in time
`2^{o(m)}`, then CP_G (a function in `AC⁰[⊕]`) has no `2^{o(m)}`-time-constructible circuits, nor gap witnesses, of size
`o(m√log m)` for infinitely many `m`. That would be a superlinear, uniform-construction lower bound for an explicit natural function.

**Caveats.**
* (i) Uniformity matters. The non-uniform smallest circuit is not known to be findable in `2^{o(m)}` time.
* (ii) The hypothesis "sparse #HC needs `2^{Ω(m)}`" is *not* refuted by the labs' theorems. The known encoding has size
  `Θ(m log n)`, which is exactly the barrier. But the labs' theorems, combined with sparsification (Impagliazzo–Paturi–Zane), already refute
  standard ETH. So the contrapositive is a statement *inside* that world, and it must not be phrased as following from ETH.
* (iii) The cut-off is sharp on the scale of these theorems: any `s(m) = m·(log m)^{1/2−ε}` suffices, and `m log m` does not.

## 8. Sources

* Li, Yang, *3.1n − o(n) circuit lower bounds for explicit functions*, STOC 2022 (ECCC TR21-023).
  Find, Golovnev, Hirsch, Kulikov, FOCS 2016.
* Mirwald, Schnorr, *The multiplicative complexity of quadratic Boolean forms*, TCS 102(2):307–328, 1992 (FOCS 1987).
* Cook, McKenzie, *Problems complete for deterministic logarithmic space*, J. Algorithms 8(3):385–394, 1987.
* Damm, *Problems complete for ⊕L*, IPL 36(5):247–250, 1990.
  Buntrock, Damm, Hertrampf, Meinel, *Structure and importance of logspace-MOD class*, Math. Syst. Theory 25 (1992) (from memory).
* Toda 1991; Vinay, Structures 1991; Mahajan, Vinay, *Determinant: combinatorics, algorithms, and complexity*, Chicago J. TCS 1997.
* Razborov 1987; Smolensky STOC 1987; Håstad STOC 1986; Khrapchenko 1971; Berkowitz 1982 (slice functions; constant as
  quoted in Toronto CS2401 notes).
* Valiant, MFCS 1977; Jukna, Sergeev, FnT-TCS 9(1), 2013.
* Chazelle, J. ACM 37 (1990), arithmetic model; Afshani, arXiv 1903.07967; Larsen, FOCS 2011 (group model and discrepancy).
* Chan, Pătraşcu, SODA 2010. Asharov, Lin, Shi, SODA 2021, arXiv 2010.09884.
  Afshani, Freksen, Kamma, Larsen, ICALP 2019.
* Johnson, *Spin structures and quadratic forms on surfaces*, J. LMS 1980. Cimasoni, Reshetikhin, *Dimers on surface
  graphs and spin structures I*, CMP 2007 (arXiv math-ph/0608070).
* Lipton, blog, 2009-07-18 (cycle parity ≡ n + inv; ACC⁰[2]).
