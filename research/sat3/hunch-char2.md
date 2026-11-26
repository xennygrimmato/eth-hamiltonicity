# Hunch: is characteristic 2 special for the contracting hypothesis?

Working notes, 26 November 2026. Machine-generated, not refereed. Nothing here is committed.

Tags: **[K]** quoted, with location; **[R]** proved here; **[D]** derived here, not reviewed; **[N]** numerical
(exact arithmetic unless said otherwise); **[C]** conjecture; **[X]** dead, with the reason.

Sources: [AN] = Anthropic, "VP ≠ VNP over every field" (line numbers of our text copy `fm/paper.txt`);
[EG] = OpenAI, "Euclidean geometry in the asymptotic spectrum of tensors" (line numbers of our text copy in
`dl_oai/`). Both are machine-generated and not refereed. Scripts: `hunch2/`.

**Hunch.** The contracting hypothesis might hold over fields of characteristic 2 although it fails in
characteristic 0, because tensors over such a field can use F₂-linear structure that is unavailable elsewhere.

**Verdict.** Not refuted, not supported. Odds that contracting holds in characteristic 2 and fails in
characteristic 0: about 1 %. The one concrete mechanism that could be tested (rank drops of the crossing-identity
terms modulo 2) exists at every computed size but costs only a constant factor in rank, which is nothing in the
exponent: outcome (i) of §2.4. Details in §6.

---

## 1. Where the field enters

### 1.1 The F₂ of Mat_μ(F₂) is a label set, chosen for the geometry

- [K] [AN] l. 270–272: "The field enters only through the tensors, which have entries in k, and the restrictions,
  which use k-linear maps. The set Mat_μ(F₂) only supplies the parties and their addition; its F₂ is not the
  field k."
- [K] [AN] l. 280–285 and D.2 Step 1 (l. 1716–1721): the quadrilateral a, a+W, a+W+W′, a+W′ has "since 2 = 0,
  both diagonals W + W′". This is the only reason for the prime 2 in Step 1.
- [K] [AN] l. 291: "We do not know which of the two hypotheses holds, even over R"; l. 564: "Which of the two
  hypotheses holds may depend on the field."
- [K] [EG] l. 3850–3854 (§11.1.1): "The binary field here indexes the subspaces. Their images lie in a spectral
  space over the coefficient field F, of arbitrary characteristic." OpenAI makes the same separation.
- [D] The question "is the finite metric space (Mat_μ(F₂), √rk) a price over k" does not see the labels: any
  bijective relabelling of the 2^{μ²} parties gives the same question. Index sets of tensors are sets; every group
  law on them (XOR included) is available over every field as a 0/1 tensor. So "char k = 2 matches the F₂ of the
  matrices" is a coincidence of notation, not a structural link.
- [D] Could the dichotomy be run with Mat_μ(F_ℓ), ℓ odd? Step 1 survives: for a transversal pair the diagonals
  W + W′ and W − W′ both have rank i + j and both are uniform among such matrices, so the mean of Lemma C.4(b)
  still gives D(i+j)² ≤ D(i)² + D(j)². Steps 3–7 use 2 = 0 repeatedly (coinciding diagonals in (D.2); the
  exchange u₁x₁ᵀ + u₂x₂ᵀ = u₁(x₁+x₂)ᵀ + (u₁+u₂)x₂ᵀ in Step 5; "a matrix of rank two is reached by two steps of
  rank one" in Step 6). The paper does not run it per prime, and says nothing about other ℓ. Whether an ℓ-version
  holds is open [C]; nothing ties ℓ to char k.
- [K] The groups of the contracting branch, U_h(F₂) ([AN] l. 488, App. F) and SL_h(F₂[s]/(s^{n+1})) ([AN]
  l. 2540–2572), are 2-groups receiving homomorphisms from Mat_μ(F₂) ([AN] l. 2166–2185). Their F₂ is again the
  label field. The laws have coefficients in a finitely generated ring A ⊆ k and "hold over every commutative
  A-algebra" ([AN] l. 496–498).

### 1.2 What actually depends on k

Only the set P(k) of prices on a finite set V. Facts:

- **(M1) [R]** k ⊆ K ⇒ P(K) ⊆ P(k). A spectral point over K restricts to one over k: tensors, products and
  restrictions over k are such over K. Hence contracting over k ⇒ contracting over K. (Also `review-theoremAB.md`
  l. 66.)
- **(M2) [K]** [EG] Lemma 2.3 (l. 1066): "For k ⊆ K, the possible joint values of spectral points on any family of
  tensors defined over k are the same over the two fields." [EG] l. 3800: ports "depends only on the
  characteristic". For Strassen points this gives P(k) = P(K). [AN] states no analogue for its own, weaker,
  axioms; our referee read the proof of 2.3 (`review-theoremAB.md` l. 64). [D] So, modulo that bookkeeping, the
  truth of contracting depends on char k only. Write C(χ) for "contracting holds in characteristic χ".
- **(M3) [D]** (the argument of [EG] Lemma 7.1, l. 2366–2376, turned around). If a finite pseudometric is a price
  in characteristic p for infinitely many p, it is a price in characteristic 0: reduce rational tensors at large
  primes, pass to a subsequence on which all values converge; "every rational restriction and every
  tensor-product or direct-sum identity survives reduction at all sufficiently large primes" [K, l. 2374].
  Consequence: **C(0) with (μ, s) ⇒ C(p) with (μ, s″) for every s″ ∈ (s, √μ) and all p ≥ p₀(μ, s″).** The finite
  exceptional set may contain 2.
- **(M4)** Not known, in either direction: C(2) ⇒ C(0); C(0) ⇒ C(2); (C(p) for all p) ⇒ C(0). The last fails for
  lack of uniformity in p of the tensor powers.
- **(M5) [R]** "Reduction mod 2 can only help" is true for one kind of object and false in general.
  - True: an identity between *integer* tensors whose terms are priced by flattening ranks (the crossing
    identity) reduces mod p, and matrix ranks can only drop.
  - Not available: identities over ℚ in general. The laws of [AN] come from a duality argument and live over a
    ring A that may contain 1/2; A has residue fields of all but finitely many characteristics only.
  - False as a blanket statement: the 0/1 tensor XOR = δ(x+y+z = 0) on F₂ is, over char ≠ 2, isomorphic to the
    unit tensor ⟨2⟩ (Fourier transform), and over char 2 it is the structure tensor of k[t]/(t²), i.e. the W
    tensor. Asymptotic subrank: 2 in char ≠ 2, 2^{h(1/3)} = 1.8899 in char 2 (Strassen 1991, tight tensors; the
    upper bound is a support functional, which exists over every field) [K, classical, from memory]. So
    ⟨2⟩ ≲ XOR holds in char ≠ 2 and fails in char 2: characteristic 2 has *fewer* asymptotic restrictions here,
    equivalently *more* spectral values. Conversely the 0/1 matrix J₃ − I₃ has rank 3 over ℚ and 2 over F₂.
    Neither characteristic dominates the other.

### 1.3 Field dependence of the asymptotic spectrum: what is classical [K, from memory, not re-checked]

- Depends on the characteristic only: asymptotic rank and the exponent ω (Schönhage 1981; Strassen 1988).
  Whether ω depends on the characteristic is open. By the constructibility argument of (M3), for each fixed
  tensor rank and border rank over F̄_p agree with those over ℚ̄ for all but finitely many p, so
  limsup_p ω_p ≤ ω₀.
- Spectral points: flattening ranks and Strassen's support functionals exist over every field; the quantum
  functionals (Christandl–Vrana–Zuiddam) need ℂ. No spectral point is known that exists only in characteristic p.
- Asymptotic quantities that do depend on the characteristic: the asymptotic subrank of the structure tensor of
  k[ℤ/p]. In char ≠ p (roots of unity adjoined, free asymptotically) it is ⟨p⟩, value p. In char p it is
  k[x]/(x^p): asymptotic rank p (border rank p), asymptotic subrank strictly smaller (p = 2: 1.8899; p = 3:
  2.7551, the cap-set constant; Strassen 1991, Ellenberg–Gijswijt 2017, Kleinberg–Sawin–Speyer 2018).
- Not asymptotic: R(k[x]/(x^n)) = 2n − 1 against n in the split semisimple case; R(W) = 3 against border rank 2;
  rank of the 2×2 determinant/permanent tensors. These disappear under regularisation.
- Reading for the hunch [D]: the local, non-semisimple group algebra of an elementary abelian 2-group in
  characteristic 2 is a *degeneration* of the semisimple one. It is cheaper to make and weaker to use. Every known
  characteristic-p phenomenon of this kind (slice rank, cap sets) is an *upper bound on what a tensor can do* that
  holds only in characteristic p, i.e. an extra obstruction there, not an extra construction.

---

## 2. The crossing identity by characteristic

### 2.1 The computation [N, exact]

`hunch2/crossing_ranks_by_char.py`, `dump_psi.py`: the tensors Ψ_N of [AN] Prop. B.2 are computed modulo four
31-bit primes with `ports/protocol/crossing_identity_modp.py`, lifted to ℤ by CRT, and the lift is checked against
a fifth prime. Then flattening ranks are taken mod 2, 3, 5, 7 and mod two large primes (= rank over ℚ).

**Sanity anchor.** Over ℤ, Σ_N Ψ_N = +1 · (permutation tensor ⟨|Σ₁|⟩_{ac}⟨|Σ₂|⟩_{bd}) in all seven cases below
(`dump_psi.py`). The right-hand side is a 0/1 tensor with d₁d₂ ones, so the identity does not degenerate to 0 = 0
mod 2. At dims 2 × 2 the term Ψ₈ has content 2 and vanishes mod 2; the other eight terms still sum to the wire
product.

**Ranks drop in small characteristic, at every size.** Pairs are (rank across ab|cd, rank across ad|bc).

Classes (2,12,2,12), dims 5 × 5, full rank 25, N = 0, 2, 4, …, 24 (then mirror):

| char | profile |
|---|---|
| 0 | (25,1) (25,3) (25,7) (25,11) (25,16) (25,21) (25,23) (25,24) (25,25) ×5 |
| 2 | (25,1) (12,3) (12,5) (12,3) (25,5) (8,4) (8,7) (8,4) (25,11) (12,8) (8,8) (12,8) (12,12) |
| 3 | (25,1) (14,3) (14,7) (24,10) (7,7) (8,8) (19,10) (13,11) (14,12) (19,18) (12,14) (11,13) (20,20) |
| 5 | (16,1) (16,3) (22,7) (24,11) (25,14) (25,18) (20,18) (23,22) (21,22) (23,24) (25,25) (23,23) (24,24) |
| 7 | drops of at most 2 |

Size-1 classes of dimension d = 2^m, characteristic 2, by y-degree k = N/2 (m = 1, 2, 3; classes (1,4), (1,8),
(1,16)):

| k | 0 | 1 ≤ k ≤ d−1 | d ≤ k ≤ 2d−1 | 2d | then mirror |
|---|---|---|---|---|---|
| char 2 | (d², 1) | (d²/2, k+1) | (d²/2, 2d−k) | (d(d−1)/2, d(d−1)/2) | |
| char 0 (d = 8) | (64,1) | (64, 3), (64,7), (64,13), (64,22), (64,33), (64,46), (64,59) | (64,64) | (64,64) | |

(At d = 2 the middle term is 0, which fits d(d−1)/2 only up to the vanishing; the formula row is the pattern of
d = 4, 8.) Dimension 3^m in characteristic 3: the balanced middle term has rank (6,6) of 9 and (54,54) of 81,
i.e. (2/3)d². Classes (2,14,2,14), dims 8 × 8, char 2: all 29 terms nonzero, ranks between (16,3) and (62,48),
balanced middle term (54,54) of 64. Classes (1,8,2,14), dims 4 × 8, char 2: balanced term (26,26) of 32.

**No digit (Lucas) factorisation.** [N] For d = 2^m the second rank grows like k + 1 in the y-degree k, not like a
product over the binary digits of k, and the number of nonzero terms is 4d + 1 at d = 4, 8 (all of them). So the
profile is not a tensor power of the m = 1 profile, and there is no single-letter optimisation to run.

### 2.2 The arc lemma: what a persistent drop would mean [R, given [AN] Lemmas A.2, A.3 and thm_alt]

Let x, v be the ends of the first wire (size p), y, u those of the second (size q), in a Euclidean parallelogram
with centre c, unit vectors e_x, e_y from c to x, y, and angle θ between them. Put

    r*(θ)² = p² + q² + 2pq cos θ,      r′*(θ)² = p² + q² − 2pq cos θ,      r*² + r′*² = 2(p² + q²).

*Claim.* cost_o(r) := min_{o,o′} p|xo| + q|yo| + p|vo′| + q|uo′| + r|oo′| equals p|xv| + q|yu| if r ≥ r*(θ) and is
strictly smaller if r < r*(θ); likewise for the hubs w, w′ of the other partition with r′*(θ).
*Proof.* The function is convex in (o, o′). At o = o′ = c its value is p|xv| + q|yu|. The gradients of the smooth
part are −(p e_x + q e_y) in o and +(p e_x + q e_y) in o′; the subgradients of r|oo′| at o = o′ are (g, −g),
|g| ≤ r. So (c, c) is a minimiser iff |p e_x + q e_y| ≤ r. For the other partition replace e_y by −e_y. ∎

So the circle law of [AN] Prop. B.3 is exactly tight on Euclidean parallelograms, point by point on the arc
|p − q| ≤ r ≤ p + q.

> **Lemma (arc).** Let k be a field over which the flat hypothesis holds. Fix p, q > 0, θ and ε > 0. Then there is
> no family of covers ⟨d₁⟩_{ac}⟨d₂⟩_{bd} = Σ_{j ≤ T} Ψ_j over k with ln d₁ = (p + o(1))n₀, ln d₂ = (q + o(1))n₀,
> ln T = o(n₀), in which every term has ln rk_{ab|cd}(Ψ_j) ≤ (r*(θ) − ε)n₀ or ln rk_{ad|bc}(Ψ_j) ≤ (r′*(θ) − ε)n₀.

*Proof.* Take the parallelogram together with the two optimal hub pairs for the deficient ranks; under the flat
hypothesis this finite Euclidean set is a price over k. Apply a spectral point approximating it to the cover:
subadditivity and Lemma A.3 bound p|xv| + q|yu| by ln T/n₀ plus the smaller of the two hub costs of some term,
which is strictly below p|xv| + q|yu| by the claim. ∎

Contrapositive: **a subexponential cover over F₂ that misses a point of the arc refutes the flat hypothesis over
F₂, hence (thm_alt) proves contracting in characteristic 2, and contradicts [EG] Thm 1.2 at p = 2** ([K] l. 156:
"Over every field there is a spectral flat of every dimension"; its proof works over finite prime fields first,
Lemma 7.1). The balanced point of the arc, (√2, √2) against the full (2, 2) for p = q = 1, is the value 1/√2 of
the two-merge crossing; so "1/√2 is optimal in characteristic 2" is equivalent, at that point, to this lemma's
hypothesis there.

### 2.3 Reading the tables against the arc [N]

`hunch2/arc_test.py` (first argument: slack in nats per coordinate). With slack ln 2 (a factor 2 in rank, which
is o(1) in the exponent and less than ln T) every point of the arc is covered by a single term, in every case
and every characteristic computed. With slack 0 parts of the arc near its ends are uncovered in characteristic 2
(for d = 8, size 1: 82 %), but only by this factor 2: the terms sit at (d²/2, ·) instead of (d², ·).

For size-1 classes of dimension 2^m the pattern of §2.1, if it continues [C], gives in units of ln d the points
(2, 0), (2 − o(1), ≤ 1), (2 − o(1), 2 − o(1)), (≤ 1, 2 − o(1)), (0, 2). The single middle term at
(2 − o(1), 2 − o(1)) lies above the whole arc. For the multi-element classes (dims 5, 8, 4 × 8) the balanced term
has 48 %, 84 %, 81 % of full rank on both cuts.

### 2.4 Outcome

Of the three outcomes — (i) on or above the arc; (ii) strictly below with subexponentially many terms; (iii)
below only with exponentially many terms — the data show **(i)**: the drop is a bounded factor (about 1 − 1/p at
the balanced term for dimension p^m; 1/2 at most terms for p = 2), and the number of terms does not shrink (one
term vanishes at d = 2, two at d = 3; none at larger sizes). [N] for the sizes listed; [C] beyond.

Caveat that cuts both ways: at these sizes the characteristic-0 bound (N+1)P(N) is vacuous too (all middle terms
have full rank over ℚ), so no computation of this size can see the exponent in any characteristic. The regime
where the circle law bites has dimensions near 2^128 (`ports/protocol/notes.md`).

Mechanism of the drop [D]: Ψ₀ is a product of two matrices of minors of the Pascal matrix (C(r,n) at y = 0 is
(−1)^n binom(r+n, n)); such minors, restricted to an energy class, lose rank modulo small primes; and y − 1 =
(X+1)² mod 2 makes the (a,b), (c,b) blocks of M degenerate together at X = 1.

---

## 3. K_{2,3} and the two-merge value in characteristic 2

- [K] `ports/note-k23-rate.md` Theorem K: f*(k) ≥ 3/√10 over every field; equality if contracting fails over k.
  So "a protocol over F₂ with rate above 3/√10" is *equivalent in content* to the hunch, not a separate test.
- [R] Classical (deterministic) network codes are tensor restrictions over every field: put at each node the 0/1
  tensor of its encoding function and contract; the sum over wire labels runs over consistent labellings only, so
  the result is the demand tensor. So XOR coding is available in every characteristic, and it gives 3/4 here in
  every characteristic (Okamura–Seymour; Harvey–Kleinberg–Lehman 2006, as cited in the note).
- [R] Node tensors are free: a restriction applies an arbitrary linear map at each party. The rank, border rank or
  asymptotic rank of the XOR node (W in characteristic 2, ⟨2⟩ otherwise) is not charged anywhere. Only wires are
  charged. So the special structure of k[t₁..t_n]/(t_i²) cannot lower a cost; what it changes is which *global*
  identities hold, and there it removes one (§1.2 (M5): ⟨2⟩ ≲ XOR fails in characteristic 2).
- Structure tensor of F₂[t]/(t²) [K, classical, from memory]: it is the W tensor; rank 3, border rank 2,
  asymptotic rank 2, asymptotic subrank 2^{h(1/3)} ≈ 1.8899; it is tight, and its known spectral values are the
  support functionals ζ^θ(W) ∈ [1.8899, 2]. Of F₂[t₁..t_n]/(t_i²): W^{⊗n}, asymptotic rank 2^n.
- Linearity of Frobenius x ↦ x² [D]: over a perfect field of characteristic 2 it is a semilinear bijection of k,
  not a k-linear map on tensor factors; applied entrywise to an identity it gives the same identity with
  conjugated coefficients. It produces no new restriction between 0/1 tensors.
- Two-merge value [D]: by §2.2 the balanced arc point 1/√2 is forced from below in any characteristic in which
  flats exist; [EG] claims this for every characteristic. The mod-2 data (§2.3) do not go below it.
- [X] A characteristic-2 protocol idea that beats 3/√10 on K_{2,3}: none found. Reason: every candidate reduces
  either to a classical code (rate 3/4), or to the crossing identity mod 2 (constant-factor rank drop, §2), or to
  using XOR/W as a resource (weaker than ⟨2⟩ in characteristic 2).

---

## 4. Is the answer the same in every characteristic?

Precise state of knowledge:

1. C depends on the characteristic only ((M1), (M2); [D] modulo the [AN]-versus-Strassen axioms).
2. C(0) ⇒ C(p) for all sufficiently large p, with slightly worse s ((M3)) [D].
3. Flats: [EG] Thm 1.2 claims them in every characteristic [K]. Flat and contracting are not known to exclude each
   other ([K] [AN] D.3), and Euclidean pull-backs to Mat_μ(F₂) have D(μ)²/D(1)² < 2 (`ports/ideas-ports.md`
   l. 331), so flats say nothing about C(χ) directly. They do pin the crossing identity (§2.2).
4. Under randomised Weak ETH, C(χ) fails for every χ ([K] `ports/note-contracting-eth.md` Cor. 1′).
5. No transfer between characteristic 2 and any other characteristic is known in either direction ((M4)). The
   hunch is therefore logically open, and reduces to: **is there an identity between wire products over F̄₂,
   not liftable to characteristic 0, that is violated by √rk on Mat_μ(F₂) for some μ?** The crossing identity
   mod 2 is the only non-liftable family examined here, and by §2.2 it can never serve (unless flats fail in
   characteristic 2), because it is already saturated by Euclidean parallelograms.

---

## 5. Cheapest experiments

- **Done.** Rank profiles mod 2, 3, 5, 7 for seven classes up to dims 9 × 9 (§2). Minutes of CPU.
- **Next cheapest, informative, not decisive.** A vectorised version of the same computation at dims 16–64 for
  multi-element classes, to see whether the balanced term keeps a constant fraction of full rank mod 2. A proof of
  the size-1 pattern (d²/2, k+1), d(d−1)/2 for all m would settle that family; it is a statement about a 4 × 4
  determinant over F₂[X].
- **Decisive, out of reach.** Any finite certificate for the hunch on K_{2,3} must have rate above 0.9487. With
  uniform binary wires that needs n ≥ 20 copies (local dimensions 2^40 and 2^60). Single-shot with unequal
  dimensions needs supply dimension q ≥ 10 and demand 9 (ln 9/ln 10 = 0.954): 10⁶ bond assignments and 9⁸ output
  equations for the F₂ SAT encoder (`tools/tensorlab/python/f2sat.py`), which already times out on 2 → (2,2,2,1)
  (`ports/e3/notebook.md` l. 168). Not feasible.
- **Decisive, theoretical.** Check [EG]'s proof of Thm 1.2 at the prime field F₂ (Lemma 7.1 onwards; Lemma 11.3
  with coefficient field F₂). If it stands, §2 is closed for good and the hunch needs a different identity.

---

## 6. Verdict

| Statement | Odds | Basis |
|---|---|---|
| Contracting holds in some characteristic | ≈ 5 % | contradicts randomised Weak ETH; no identity in sight |
| Contracting holds in char 2 but fails in char 0 (the hunch) | ≈ 1 % | no structural link between the label field and k (§1.1); known char-p phenomena are extra obstructions, not extra constructions (§1.3); the one testable mechanism gives a constant factor only (§2) |
| The mod-2 rank drop of Ψ_N improves the circle law | < 1 % | would refute [EG] Thm 1.2 at p = 2 (§2.2); data show outcome (i) |

Where the hunch fails, precisely: not at a theorem. It fails to find a foothold. (a) The F₂ of the configuration
is not the field. (b) Local structure (W against ⟨2⟩) is free in the restriction model. (c) Integer identities do
drop rank mod 2, but by a bounded factor in every computed case, and an exponent-level drop is excluded wherever
flats exist. What remains open is §4 item 5.
