# Referee report: research/sat3/notes.md (26 Nov 2026)

Scope: §§2–7 of `notes.md`, its scripts, and the cited inputs: AN text `scratchpad/fm/paper.txt` (Def. A.4, Thm A.6,
Prop. A.5, Prop. C.3, Lemma C.4, Thm D.2 Steps 1–8, Remark D.3), `ports/note-k23-rate.md` §§1.2–2.3,
`ports/c1d1/notes.md` D1, `vpvnp/b2/notebook.md` §1. All numbers below come from my own code in
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/refsat3/`. I did not run the author's
evaluators to get them.

Missing input: `research/sat3/s3-experiments.md` does not exist (searched the whole filesystem). So the "executor's
independent numerics" could not be read. `check_ninetripods.py` exists and imports `verify_pf.py`, which is in the
folder. The notes cite "32/32 chains", "Rust unit test" and similar results that have no file behind them.

## Verdicts, weakest first

| # | claim | verdict |
|---|---|---|
| 5 | Theorem S (gap thresholds 0.7075 / 0.79) | **gap** (the class is not D1's class; no uniformity in g) |
| 6 | Duality remark §7.2 ("the gap can be total") | **gap** (the example shows slack for one functional, not a floor/attainment gap) |
| 4(iii) | Large-net limit, Φ = 3(1−θ)(1+2θ), transfer | **correct in the limit model; transfer correct with fix** (holds for F₂^M, F₃^M, F₄^M, not for "groups with index-4 subgroups") |
| 4(ii) | One-tree reduction | correct |
| 4(i) | Δ₃: nine tripods give 6 per merge | correct |
| 3 | Product-hull Theorem 4.3 (Lemmas 4.1, 4.2) | correct (can be upgraded from [D] to [R]) |
| 2 | Euclidean cap Prop. 2.2 | correct |
| 1 | Bimedian inequality Prop. 3.1, Thm 3.2, Cor. 3.3, 3.4 | correct |

---

## 5. Theorem S: gap

**What D1 proves and why.** D1.1 fixes a *finite list* 𝒞 of configurations. Every level is a partition of its edges
into copies of members of 𝒞, each copy *all-crossing*, plus a remainder ξ → 0. The proof of Theorem D uses this at
one point that matters: "𝒞 is finite, so one C occurs for infinitely many n, with λ → ∞" (c1d1, l. 361). Only then
is the floor, which is a liminf in λ at a *fixed* configuration with no rate (D1.4 item 3; b2 (★): "the scale c
depends only on the finite configuration and on ε"), applied at the level that dips.

**What Theorem S assumes.** Its levels are "p-net levels over k (class of D1.1 with one configuration per level)". A
p-net level of order g is one configuration whose size grows with g. It contains edges internal to merges, so it is
not all-crossing. Along a tower g_ℓ = K_ℓ grows doubly exponentially. The averaging step gives a level ℓ(n) with
ρ < (pod floor) − η, but the configuration at that level is a net of order g_{ℓ(n)}, and that order can differ for
every n. The pod floor for the order-g net holds for λ ≥ λ₀(g, η), and λ₀ comes from the approximation scale
c(P_g, ε) of the finite point set P_g (orbit product plus far legs) by c·d_φ. Nothing bounds that scale in g:
Theorem 4.3 only says each finite subset is a price, and prices are limits. So "some level is below the floor by a
constant" does not imply "some finite set is not a price". The sentence "the floor statement is 'liminf as λ → ∞ at
fixed configuration', with the same absence of a rate as in D1.4" names the problem without resolving it. In D1 the
missing rate only blocks the *sharp* form. Here it blocks the constant-gap form too, because the configuration is not
fixed.

There is a second, smaller mismatch. The 2^{o(λ·E)} term budget with E ~ g⁴/2 is a different normalisation from
D1's 2^{τ(λ)} per copy. With a growing configuration the selection loss c(P_g, ε)·log T/δ has to be compared with
λ·E·b, which again needs a bound on c(P_g, ε).

**Fixes, any one of which would close the gap:**
1. **Uniform floor.** Prove the pod floor for order-g nets with an error ε(λ) independent of g, for example by showing
   that all the P_g are uniformly approximable inside one price space at one scale. Nothing in hand gives this.
2. **Fixed configurations.** Decompose net levels into copies of finitely many fixed balanced configurations, each
   with a pod floor of at least the stated value. §7.5 itself says the smallest balanced sub-configurations (the
   translation classes E_v) grow with g, so this is open.
3. **Per-level statement.** Restate the result as: "a single level of order g with ρ < value_g − η, at
   λ ≥ λ₀(g, η), proves contracting". This is true by the argument given, but it says nothing about towers.

Item 1 of Theorem S (balanced two-merge levels) is also not literally D1. D1's flat floor E/√p is b2 Theorem 3, which
assumes all-crossing configurations. For balanced but not all-crossing configurations the attainment of the cap is
not established. The part "no price argument can give less than 1/2" is correct (it is Theorem 3.2).

The numbers themselves are right: log₂(3/√(27/8)) = 0.70752 and log₂√3 = 0.79248.

## 6. Duality remark (§7): gap in the illustration

- **A.6 as quoted.** AN A.6 (l. 1164) is the one-sided statement for a finite list A₁…A_r with max_β. The "iff" is
  fine because the converse is trivial: φ(C)^N ≤ 2^{εN}·sup φ(A)^N. The extension to an arbitrary family also works,
  and needs no compactness. Prop. A.5 (l. 1138) handles arbitrary sets of triples, η φ(C) < φ(C) gives the
  contradiction against a sup, and each certificate uses finitely many members. Correct.
- **The example.** Take 𝒫 to be the common restrictions of ⟨N⟩₁₂ and ⟨N⟩₂₃. Then 𝒫 consists of product states, and
  the flattening rank at {2}|{1,3} is N on both networks. Both facts are right: a common restriction has flattening
  rank 1 at party 3 and at party 1, so it is u⊗w⊗v. This shows that the bound sup_𝒫 φ ≤ min_k φ(N_k) is strict for
  one φ.
- **What it does not show.** It does not show that "price floor ⇒ pieces" fails, because in this example no target
  separates the two conditions. If ∀φ: φ(f) ≤ min_k φ(N_k), then the flattenings at {3} and at {1} (where one of the
  two networks has value 1) force f to have flattening rank 1 at parties 1 and 3. So f = u⊗f₂⊗v, which lies in 𝒫.
  The family of all φ closes the per-functional slack here. The claims "So 'price floor ⇒ pieces' is false as a
  general principle" and §0 item 6 ("the gap can be total") are therefore unsupported.
- **Fix.** Either exhibit an f with ∀φ φ(f) ≤ min_k φ(N_k) that is not covered, or weaken the remark to "the price
  method uses only the per-φ bound min_k φ(N_k), which can be strict".
- The K₄ and Δ₃ remarks after the example are pointers to other notes and not checked here.
- §7.4 depends on Theorem S's transfer. At finite g the pod value is *below* flat for g ≤ 8 (table below), so "no
  sphere-law family on a net" holds only for large g, and only for the groups of 4(iii).

## 4(iii). Large-net limit: correct in the model; transfer needs a scope fix

**Recomputation** (`limit.py`, exact rational arithmetic, my own c(n,n′) and D̄ from the definitions in the limitnet
docstring):

| Q, A | θ | Φ exact | 3(1−θ)(1+2θ) | level √Φ/3 |
|---|---|---|---|---|
| Z₄, {0} | 1/4 | 27/8 (S = 81/64, D̄ = 3/8) | 27/8 | 0.612372 |
| Z₂², {0} | 1/4 | 27/8 | 27/8 | 0.612372 |
| Z₄, {0,2} / Z₂², {0,1} | 1/2 | 3 | 3 | 0.577350 |
| Z₃, {0} | 1/3 | 10/3 | 10/3 | 0.608581 |
| Z₅, {0} | 1/5 | 84/25 | 84/25 | 0.611010 |
| p = 4: Z₃, slopes 0, ∞, 1, −1, {0} | 1/3 | 16/3 | p(1−θ)(1+(p−1)θ) = 16/3 | √Φ/4 = 0.577350 = 1/√3 |

- **Proof of Thm 5.4, line by line.** The node probabilities, the gain table (2 for two singly-active nodes of
  different classes, 1 for active with inactive, ≤ 0 otherwise) and E[c₊²] = 6θ(1−θ)²(1+2θ) with D̄ = 2θ(1−θ) all
  check. The maximum is at θ = 1/4.
- **General p.** Φ_p = p(1−θ)(1+(p−1)θ) checks; I re-derived it from P(x=p) = θ², P(x=1) = pθ(1−θ). The optimum
  θ* = (p−2)/(2(p−1)) gives ½√(p/(p−1)) **only for p ≤ 4**. For p ≥ 5 the constraint P(x=0) = (1−θ)(1−(p−1)θ) ≥ 0
  binds at θ = 1/(p−1), and the notes handle this correctly (the "transversality" wording is really this
  nonnegativity). The table values 0.5477, 0.516 and 0.4768 (F₇, θ = 1/7) are confirmed. The task's phrase "general p:
  ½√(p/(p−1))" holds only for p ≤ 4.
- **Closure property.** The closure is verified by enumeration. For p = 3, r, c ∈ A ⇒ r − c ∈ A and both permuted
  versions hold, so x ∈ {0,1,3}. For p = 4, two A-lines force all four iff 2 is invertible mod A (odd index):
  0 violations for Z₃, Z₉ and Z₆ with index 3, and 9 violations for Z₁₂ with index 4. The p = 4 net also needs
  |G| odd so that slopes 1 and −1 are transversal; F₃^M satisfies both.
- **Author's own outputs.** `lim_5.txt` and `lim_6.txt` (random searches) report only 3.0. The values 3.36 and 10/3
  quoted for Z₅ and Z₆ are evaluations of the subgroup tripod, which my code confirms. They are not search results.

**The transfer: what it assumes.** The level value is (1/(pE))·Σ_e √(m_e/D_pairs). Here m_e is the mean of c₊² over
the orbit of e, in the product over the automorphism orbit (Thm 5.1). This equals √Φ/3 in the limit only if
(a) almost all edges lie in orbits along which (πn, πn′) is asymptotically uniform on Q² × Q², and (b) the
same-merge hub pairs form one orbit.
- For G = F₂^M, GL_M(F₂) acts transitively on generic pairs (a, b) (independent vectors), and (a) and (b) hold. My
  exact finite-g computation (`transfer.py`, internal edges included) gives:

  | g | 4 | 8 | 16 | 32 | 64 | 256 | 1024 | 4096 | ∞ |
  |---|---|---|---|---|---|---|---|---|---|
  | value | 0.5410 | 0.5729 | 0.5915 | 0.6016 | 0.6069 | 0.6110 | 0.6120 | 0.6123 | 0.6124 |

  The values increase to the limit, and they are **below the flat 0.5774 for g ≤ 8**.
- The same argument works for F₃^M (p = 4) and F₄^M (p = 5): generic means independent, and GL is transitive.
- **Not** for "groups with index-4 subgroups" in general. For cyclic Z_g (4 | g), the symmetries that act
  compatibly with π are translations, units and S₃. The norm then depends on v mod 4, and Jensen loses. The same
  construction gives **0.5857**, not 0.6124 (`transfer.py`, last line).
- **Fix.** In §5.4 and Theorem S item 2, replace "nets of groups with index-4 subgroups" by "nets of F₂^M (or groups
  whose automorphisms act transitively on generic pairs modulo A)".
- The remaining step of the transfer (internal edges O(1/g), D over distinct pairs versus independent pairs) is fine.
  It is the uniformity in g, item 5, that is missing.

## 4(ii). One-tree reduction (Thm 5.1): correct

- The per-factor bound s^k_e ≤ Σ_j w_{e,j} σ^k_{e,j} is valid for arbitrary legs (Cauchy–Schwarz on |x o|, with
  equality for |xy|).
- Then Σ_e ‖c_e₊‖ ≤ √(E Σ_j S_λ(T_j)) ≤ √(E Γ* Σ_j D_λ(T_j)), and Σ_j D_λ ≤ (1/p)Σ λ_k²δ_k² = 1 with λ_k = 1/δ_k.
  Γ* is homogeneous of degree 0 in λ, so the sup over λ is just a sup over directions. A factor with D_λ = 0 has
  S = 0 (triangle inequality), which I checked.
- **Attainment.** It needs transitivity on edges and on *all* same-merge hub pairs. The latter implies merge
  transitivity and equal δ_k, hence λ ≡ 1. Verified for Δ₃ (`autd3.py`): the group has order 108 and is transitive on
  the 9 edges and on the 9 same-merge pairs.
- **Search.** A free-λ pod search (`gamma.py`, 400 restarts, independent code) finds Γ = 36.000 and nothing larger.
  This agrees with the [N] claim and Conjecture 5.3. The sup over λ is not proved to equal the λ ≡ 1 value; the
  notes say so.

## 4(i). Δ₃ nine-tripod product: correct

My own evaluator (`ninetripods.py`) uses explicit points in the l₂ product of nine tripods.
- δ_k² = 6 for all 9 same-merge pairs.
- With explicit legs at distance M: b = (5.913567)³ at M = 10², (5.99142)³ at 10³, (5.999143)³ at 10⁴ and
  (5.999991)³ at 10⁶.
- The exact far-leg optimum over all arm choices (fresh arms included) is Σ_k b_k = 18.000, so b_k = 6 and
  ρ = 6/9 = 2/3.
- Single-tripod ratio: S = 24, D̄ = 2/3, Γ = 36.
- The proof of Thm 5.2 checks: 6 factors with c = 2 per edge, c = −1 at the factors n₀ ∈ e, 0 at n″.

The conditional ρ_Δ₃ ≥ 2/3 is legitimate, because Δ₃ is a fixed configuration and the λ → ∞ liminf applies. It uses
Theorem 4.3 with m_j = 3 and σ = 0.

## 3. Product-hull Theorem 4.3: correct

- **(a) Block-diagonal embedding.** Rank is additive on block-diagonal matrices, so √rk is the l₂ product of the
  per-block √rk. Corollary P (refereed) gives √r·√(graph metric of K_{2,m}) per block for m ≤ 2^r + 1. μ = 2rJ ≥ 3
  can be arranged (pad by diag(a,0) if 2rJ = 2). `thm_alt_rank_price` then gives a price over the same k for every
  μ ≥ 3 (AN l. 1714: "fix μ ≥ 3"). ✓
- **(b) Lemma 4.1.** C.4(f) (l. 1658–1660) needs exactly |xy| = |uv| = δ, |xu| = |yv| = h and both diagonals of
  squared length δ² + h². These hold for x = F(z,0), u = F(z,1), y = F(z′,0), v = F(z′,1). The conclusion
  |ab|² = d_Z² + h²(s−t)² covers *all* pairs (z,s), (z′,s′) with z ≠ z′ and s ≠ s′; for z = z′ the claim is trivial
  on one segment.
  - Z need not be geodesic.
  - Completeness of Y is used only through C.4(a) (existence and uniqueness of the point at t), which is part of the
    CAT(0) definition (l. 1599).
  - This is AN Step 8 (l. 1779–1784) with Z arbitrary.
- **(c) Lemma 4.2 and the induction.**
  - The four points n, t_i, t_j, s are the square {0,a}² with the correct distances.
  - Two applications of 4.1 (Z₁ = {0,a} × Z, then Z₂ = [0,a] × Z) fill Q_ij × Z.
  - On the triangle Δ_i the two parametrisations agree: they agree at the vertices, on the side [n,s] (unique
    geodesic), and then on the segments from t_i.
  - Isometry is a pairwise condition, and any two points of D_m × Z lie in some Q_ij × Z. ✓ (same as the refereed
    H_m, now with a Z factor).
  - The induction over factors (Z = the diamonds already built × the S's still to do) is sound.
  - "Infinite arms": a finite subset of ∏(𝕋_{m_j} × ℝ) has |ξ_j| + |σ_j| ≤ R in every factor. The uniform scaling
    by a/(√2R) maps 𝕋_m × ℝ to itself and puts the set inside ∏ D_{m_j}. Prices are closed under multiples and
    pull-backs. ✓
- **(d)** Every step stays over the field k on which contracting fails. ✓

The proof uses only C.3, C.4(a),(f), thm_alt_rank_price and Lemma P, so the [D] tag can become [R]. The "not
covered" list in the notes (two branch points, other links) is accurate.

## 2. Euclidean cap (Prop. 2.2): correct

- s^k_e ≤ ⟨u_e, h^k(e⁻) − h^k(e⁺)⟩ holds.
- The cross terms Σ_e⟨Δ̃^k_e, Δ̃^l_e⟩ expand to Σ_{G,G′}⟨h_G, h_{G′}⟩·[Σ_{n∈G∩G′}deg n − #{(y,z)}] and vanish by
  balance (ordered pairs; edges internal to both groups are counted twice on both sides).
- Numerically (`euclid.py`, far-leg Hilbert value), with |cross terms| ≤ 4·10⁻¹⁵ on 300 random hub sets in R^1–R^11
  each:

  | configuration | best found | cap |
  |---|---|---|
  | crossing | 2.82843 | 2.82843 |
  | Δ₃ (3 merges) | 15.418 | 15.588 |
  | K₄ | 8.48528 | 8.48528 |
  | 3-net Z₄, order 4, all 120 edges | 179.25 | 185.90 |
  | 3-net Z₂², order 4, all 120 edges | 181.53 | 185.90 |

- On Δ₃ the orthogonal simplex attains 15.5885 = 9√3 exactly. With finite legs it gives b = 5.15854, 5.19578 and
  5.19615 at M = 10², 10⁴ and 10⁶.
- Balance verified by enumeration (`configs.py`) for the crossing, Δ₃, K₄, both 3-nets of order 4, and the three K₄
  sub-crossings X_j.

## 1. Bimedian inequality and consequences: correct

- **Prop. 3.1.** I re-derived it: two applications of C.4(a) give (1−t)²|oo′|² + t²|ww′|² + t(1−t)[|wo′|² + |ow′|² −
  |ow|² − |o′w′|²] for one bimedian, the swapped bracket for the other, and the brackets cancel.
  - In Euclidean space the sum is the exact parallelogram identity: 2(1−t)²|o−o′|² + 2t²|w−w′|². Checked
    (error 2·10⁻¹⁴).
  - Random tests (`bimedian.py`, 3000 quadruples each, with t either ½ or random; my own metric-tree code with
    points on edges, exact geodesics, l₂ products) on one tree (n = 2–12 vertices), tree², tree³ × R², and R⁴ give
    max(lhs − rhs) ≤ 1.1·10⁻¹³. Equality occurs in trees, so the inequality is tight.
- **Thm 3.2.** Each step checks:
  - convexity of the distance gives λ₁|xo¹| + λ₂|xo²| ≥ Λ|xβ|;
  - the triangle inequality gives |xy| − |xβ| − |yβ′| ≤ |ββ′|;
  - one C.4(a) chain gives |ββ′|² ≤ Σ_{k,l}μ_kμ_l|o^k o^l|² − t(1−t)(…);
  - balance cancels the k ≠ l and the subtracted terms;
  - |o^k(e⁺)o^k(e⁻)| ≤ δ_k on crossing edges and 0 on internal ones;
  - Cauchy–Schwarz finishes.
  A version with unequal edge bits also holds, with Cauchy–Schwarz weighted by w_e and balance unweighted. That is
  what "the crossing bound 2√(λ₁²+λ₂²) from CAT(0) alone" needs.
- **Numerics.** My own pod-product far-leg optimiser (`podopt.py`) finds:

  | configuration | best b₁ + b₂ or Σ_k b_k | cap |
  |---|---|---|
  | crossing | 2.82843 | 2√2 (attained) |
  | Δ₃ rows + columns | 12.240 | 9√2 = 12.728 |
  | Δ₃ with 3 merges | 16.25 | 27/√2 = 19.09 (the nine-tripod product gives 18) |
  | K₄ | 8.48528 | 6√2 (attained) |

  The hill-climb over general tree products (`bvals.py`) also shows no violation.
- **Normalisation.** The notes' b_k is b2 (★)'s quantity (L − H_k)/δ_k, with δ_k the largest hub–hub distance of
  merge k, in units of λ. b2 states that one price gives one piece and the adversary mixes, so
  V/λ ≥ max_{x ∈ conv{b}} min_k x_k. A bound on Σ_k b_k valid for every price therefore bounds everything the method
  gives: several spectral points combine into a product, whose d is a sum, which is again a price. ρ is V/(λ·#edges),
  as in D1.1.
- **(i) Balanced fully-crossing two-merge configurations: ≤ E/√2.** ✓ The definition of balance uses ordered pairs,
  which is consistent with both proofs.
- **(ii) K₄: ≤ 2√2 per merge.** ✓ K₄ = X₁ ⊔ X₂ ⊔ X₃; each X_j is balanced for the other two merges, and the saving
  under its own merge is ≤ 0. Together with the flat value 2√2 the K₄ price floor is exactly 2√2λ (ρ = √2/3) under
  FH.
- **(iii) p-nets: ≤ E/√2 per merge.** ✓ Lines of different classes meet once, so both sides equal g² − 1 and every
  pair of merges is balanced. Summing b_k + b_l ≤ √(2E·E_×) over pairs gives (1/p)Σb_k ≤ √(E E_×/2).
- **Minor.** "The true price floor of a 3-net lies in [1/√3, 1/√2]": at finite g the full level has internal edges,
  and the flat value is √(E_×/(pE)) < 1/√p. The lower end is 1/√3 only as g → ∞.

## Summary for the author

- **Unconditional and correct:** Prop. 3.1, Thm 3.2, Cor. 3.3, Cor. 3.4, Prop. 2.2.
- **Correct under ¬contracting:** Thm 4.3 (upgrade to [R]), Thm 5.1, Thm 5.2.
- **Correct as a computation:** Thm 5.4, Prop. 5.5 (the closed form only for p ≤ 4).
- **To fix:**
  1. Theorem S does not follow from D1's averaging, because its levels are growing configurations with no uniform
     floor. Restrict or restate it (fixes in §5 above), and correct §0 item 4, the table in §5.4 and §7.4
     accordingly.
  2. Restrict the group class to F₂^M, F₃^M, F₄^M (or groups whose automorphisms act transitively on generic pairs
     modulo A). Cyclic groups give only 0.586 with this construction.
  3. Note that the finite-g pod value is below flat for g ≤ 8.
  4. §7.2 needs a separating target f, or a weaker wording.
  5. Supply `s3-experiments.md`, or remove the references to it.

Scripts (all in `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/refsat3/`):
- `trees.py`: metric trees and their products
- `bimedian.py`: Prop. 3.1
- `configs.py`: configurations and the balance check
- `bvals.py`: b-vectors and Thm 3.2 random tests
- `euclid.py`: Prop. 2.2
- `podopt.py`: CAT(0) caps in pod products
- `ninetripods.py`: Thm 5.2
- `gamma.py`: Γ search
- `autd3.py`: Δ₃ symmetry group
- `limit.py`: Φ exact
- `transfer.py`: finite g, and cyclic groups
