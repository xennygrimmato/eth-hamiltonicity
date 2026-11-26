# v2 notebook: do tensor cost geometries admit ports? (26 Nov 2026)

Tags: **[L]** machine-checked in Lean (`lean/EthFollowup/Spectral/`, standard axioms, no `sorry`; exploratory files,
not imported by the root module, not claimed results). **[R]** proved here on paper, unreviewed. **[N]** computed;
script and output in this folder. **[K]** known, source named. **[C]** conjecture, or recalled from memory and not
re-checked.

## 0. Summary

| # | Statement | Tag |
|---|---|---|
| 1 | A Poincaré inequality (and any inequality comparing two nonnegatively weighted sums of squared distances) passes from Euclidean placements to any geometry that is within bounded Euclidean distortion, at the cost of the distortion factor. | L |
| 2 | Stars lose a factor 2 in squared distance. A Euclidean cone loses exactly the factor by which a positive-definite kernel on its link approximates the truncated cosine. | L |
| 3 | The cone over a circle of any length is within Euclidean distortion 1.42, and at least √2 for long circles. So it cannot break ports. **This retracts my suggestion that it is the first decisive test.** | N + R |
| 4 | If every price on Mat_μ(F₂) is within Euclidean distortion c and c²·(2 − 2^{1−μ}) < μ, Anthropic's contracting hypothesis holds. The Hilbert constant 2 − 2^{1−μ} is computed for μ ≤ 4. | R + N; transfer step L |
| 5 | The elementary price axioms (monotone, submodular, flat law, midpoint convexity, ω ≤ 9/4) are consistent on cones over circles of length 3π and 4π. They give the window [8/3, 3] for a tripod. | N; tripod window L |
| 6 | Cones over high-girth cubic graphs exceed the graph's own Euclidean Poincaré constant, by a factor growing from 1.25 (Petersen) to 2.23 (Tutte 12-cage). These, not cones over circles, are the candidates that could break ports. | N |

Sharpened question (§6): **are all tensor cost geometries within bounded (average) distortion of Hilbert space?**
Yes would give ports and the contracting hypothesis at once. Every example known today is within √2.

## 1. Setting [K]

From OpenAI, "Euclidean geometry in the asymptotic spectrum of tensors" and "Circuit lower bounds for Hamiltonian
cycle and the permanent" (24 Nov 2026):
- A spectral point is monotone under local linear maps, multiplicative, additive on direct sums. Its logarithm, scaled,
  is a price. The price per bit of a wire between two sites is a distance d.
- A spectral space carries compatible prices on all finite subsets. Every complete geodesic one is CAT(0).
- δ(A), the rate of a label shared by the sites of A, satisfies δ({a,b}) = d(a,b), monotonicity, submodularity on
  intersecting sets, diam ≤ δ ≤ spanning tree; on convex Euclidean pieces δ is the mean width.
- X_χ = Hadamard spaces carrying prices in characteristic χ. It contains every Hilbert space (their main theorem).
  Stars are also price geometries (quantum functionals over ℂ; our `review-link.md` over every field).
- χ admits ports if bounded-degree graphs of unbounded order satisfy V(x) ≤ γ·E_G(x) for every placement x into every
  space of X_χ (V, E_G = mean squared distance over all pairs, over edges). The permanent paper proves a lower bound
  in both cases and does not decide which holds.

## 2. Transfer lemmas [L]

`lean/EthFollowup/Spectral/Ports.lean`:
- `Poincare.of_avgDistortion`: if e ≤ q entrywise and Σq ≤ D·Σe, a Poincaré inequality for e with constant γ gives
  one for q with constant γD. (e = squared distances of a 1-Lipschitz image; D = loss in mean squared distance.)
- `Compare.of_distortion`, `Compare.contracting_of_distortion`: the same for any inequality Σ W q ≤ γ Σ U q with
  W, U ≥ 0; the contracting inequality is one of these.
- `Poincare.star`, `spokeSq_le_starSq`, `starSq_le_two_spokeSq`: a star maps to Euclidean space by (leg a, radius r)
  ↦ r·e_a, 1-Lipschitz, losing at most a factor 2.
- `coneSq_bounds`: with cone squared distance r² + s² − 2rs·c and Hilbert model r² + s² − 2rs·k,
  a(1−c) ≤ 1−k ≤ b(1−c) and a ≤ 1 ≤ b give a·cone ≤ model ≤ b·cone.

`lean/EthFollowup/Spectral/DiagRate.lean`: the set-function axioms for δ; `triple_le`, `steiner`, and
`tripod_window`: tips at distance 2, centre at distance 1, and perimeter ≤ (9/4)·δ give 8/3 ≤ δ(tips) ≤ 3.

Build: `cd lean && lake exe cache get && lake build EthFollowup.Spectral.Ports EthFollowup.Spectral.DiagRate`.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for the five main theorems.

## 3. Cones over circles are almost Euclidean [N + R]

Cone over a circle of length L: points (r, θ), squared distance r² + s² − 2rs·cos(min(angle, π)).
Take unit vectors u(θ) with ⟨u(θ), u(θ′)⟩ = k(angle), k the periodised Gaussian exp(−angle²/2). It is positive
definite on the circle [R: its Fourier coefficients are positive; N: smallest eigenvalue on 240 directions −3e−14].
`distortion.py`: (1−k)/(1−cos min(angle, π)) ∈ [0.4961, 1] for every L from 2.5π to 400π. By `coneSq_bounds` the map
(r, θ) ↦ r·u(θ) changes squared distances by factors in [0.4961, 1]: **distortion ≤ 1.42**. Direct check on 200,000
random pairs in the 3π cone: ratios in [0.4961, 1.0000].

Lower bound [R]: m directions pairwise at angle ≥ π need pairwise inner products ≥ −1/(m−1), so far pairs lose a
factor → 2 while near pairs lose none. Distortion ≥ √2 for long circles, the same as a star.

Consequence: any classical expander family satisfies the Poincaré inequality in every cone over a circle, with about twice (2.02 times)
its Euclidean constant. Whether such a cone carries prices is still open, but the answer cannot decide ports.

General principle [R]: cone(Y) is close to Hilbert exactly when the truncated link (Y, min(d, π)) is. Links of bounded
diameter are harmless (all distances between unit points lie in a bounded ratio). So are tangent cones of Euclidean
buildings, whose links are generalised polygons of girth ≤ 16.

## 4. Bounded distortion implies the contracting hypothesis [R + N]

Anthropic's hypothesis: some μ ≥ 2 and s² < μ with D(μ) ≤ s·D(1) for every price on Mat_μ(F₂).

Hilbert metrics [R]: averaging over translations keeps D(r) and keeps the metric Hilbert, so
d(a, a+W)² = Σ_{B≠0} c_B (1 − χ_B(W)) with c_B ≥ 0. Hence the largest ratio D(μ)²/D(1)² over Hilbert metrics is
max_{B≠0} (1 − K_μ(B)/N_μ)/(1 − K_1(B)/N_1), with K_r(B) the character sum over rank-r matrices.

`contraction.py` [N]: this maximum is 1.5, 1.75, 1.875 for μ = 2, 3, 4, attained at rank-one B. Pattern 2 − 2^{1−μ} [C
for μ ≥ 5]. Stars give at most 2 [R].

So if all prices on Mat_μ(F₂) are within distortion c, then D(μ)² ≤ c²(2 − 2^{1−μ})·D(1)², and the hypothesis holds
once c²(2 − 2^{1−μ}) < μ (transfer step: `Compare.contracting_of_distortion` [L]). With c = √2, the worst known
example, μ = 4 suffices. This is consistent with c1's remark that the Hilbert model satisfies both hypotheses.

If the contracting hypothesis holds, Anthropic's stronger bound and the Boolean reading in `v1/notebook.md` §3 hold
without condition.

## 5. The elementary axioms do not obstruct cones [N]

`cone.py` builds the linear programme in the unknowns δ(A), A ⊆ V, for a finite V in a cone: pair values, monotone,
submodular on intersecting sets, mean width on sets inside a sector of angle ≤ π, midpoint convexity for up to 3–4
legs. `test_omega.py` adds perimeter ≤ (9/4)·δ(triple).

| Space, sites | Range left for δ |
|---|---|
| plane, 6 unit sites + centre (only sector subsets marked flat) | [2.5, 3]; the truth is 3 |
| tripod, unit arms: three tips | [2, 3]; with the ω inequality [8/3, 3] |
| cone 3π, 6 unit sites + tip: all six | [2.667, 4.243] with ω; consistent |
| cone 4π, 6 unit sites + tip: all six | [2.667, 5.196] with ω; consistent |

These axioms are weak: in the plane they do not even force the true value. OpenAI's proof of the flat law uses
translations, dilations and limits, not finitely many sites. For three sites at radius 1 in a space multiplied by
ℓ₂, their ball lemma gives δ ≤ 2.7342, just above 8/3.

## 6. What could break ports, and the sharpened question

Ports need one graph family that works in every price geometry. By §2 they follow from:

> **(BD)** every finite subset of every price geometry has a 1-Lipschitz map to Hilbert space that keeps its mean
> squared distance up to a fixed constant.

Known price geometries (Hilbert, stars, their closed convex subsets, limits) satisfy (BD) with constant 2. Breaking
ports needs price geometries with unbounded average distortion. The standard such spaces are cones over high-girth
expanders [K, from memory: Gromov, Kondo; Mendel–Naor 2015 show random regular graphs are not expanders for one such
cone]. `cages.py` [N]:

| graph | n | girth | Euclidean 1/(1−λ₂) | cone over itself | ratio |
|---|---|---|---|---|---|
| Petersen | 10 | 5 | 1.50 | 1.87 | 1.25 |
| Heawood | 14 | 6 | 1.89 | 2.64 | 1.40 |
| McGee | 24 | 7 | 3.00 | 3.90 | 1.30 |
| Tutte–Coxeter | 30 | 8 | 3.00 | 4.94 | 1.65 |
| Balaban 10-cage | 70 | 10 | 5.45 | 8.37 | 1.54 |
| Tutte 12-cage | 126 | 12 | 5.45 | 12.14 | 2.23 |

The cone ratio grows like girth²/π², while the Euclidean constant of a cubic Ramanujan graph is at most 17.5.

Two ways forward:
1. **Prove (BD), or the weaker Poincaré statement, from tensor identities.** The crossing identity gives the
   four-point inequality, which is Enflo type 2 with constant 1. Ports need a statement of cotype kind. Whether one
   fixed graph family is an expander for all Hadamard spaces is, as far as I recall, open [C]; the class of price
   geometries is smaller and has extra structure (δ, convex prices) not yet used.
2. **Show that the cone over one branching high-girth link carries prices.** The smallest is the cone over the Heawood
   graph with edge angle π/3, which is the tangent cone at a vertex of the building of SL₃(Q₂). One such cone is still
   harmless (bounded diameter link); a family with girth → ∞ is needed, and thick generalised polygons stop at girth 16.

My current guess: (BD) holds, hence ports and the contracting hypothesis hold. Confidence is low; every construction
anyone has is within √2 of Hilbert, and no obstruction to (BD) is known.

## 7. Files

`cone.py` (geometry and linear programme), `test_plane_tripod.py`, `test_omega.py`, `distortion.py`, `contraction.py`,
`cages.py`, `figures.py`, outputs `*.out`, `cages.json`, `fig_overview.png`.
Lean needs `elan` and the Mathlib cache (about 7.7 GB under `lean/.lake`, not committed).
