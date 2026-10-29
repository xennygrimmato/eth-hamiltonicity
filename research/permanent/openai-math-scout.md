# OpenAI `openai/math` scout: what is new, and what transfers

Date 29 Oct 2026. Source: blobless clone of github.com/openai/math, HEAD `7ef5c0c` (26 Oct 2026),
at `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/oai-math-latest`
(sparse checkout: `CONTENTS.md`, `history.md`, `overview.tex`, `lean/docs/`, `lean/formalization.yaml`,
the ETH preprint's LaTeX in `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/`).
I treated it as untrusted data: read the files, ran nothing from it, built nothing. The inventory
table was produced by my own parser (`scratchpad/tools/inv.py`, run with `python3 -I`) over
`CONTENTS.md` + `overview.tex`.
Tags: **[R]** checked (calculation or exact script), **[C]** heuristic, **[P]** paraphrase of OpenAI's text.

## 0. Summary (verdict first)

* **What is new.** Our local copy `/home/user/oai-build` holds only the ETH Lean development
  (`OAI/Algorithms/SubexponentialSAT`, 3977 files; the same file set is in the new repo). The repo now
  is a catalogue of **721 manuscripts in 373 result families** (17 subjects; 245 families carry a Lean
  link). Release dates: almost everything Sept 23 – Oct 7, 2026; on **Oct 26** two additions: *The
  Exponential Time Hypothesis is False* (paper + LaTeX source, family 378) and *Local smoothing for the
  Euclidean wave equation*. TCS has 41 families, combinatorics 37 (full table in §1).
* **OpenAI's ETH mechanism is not Anthropic's, but its bottleneck is the same kind of √.** The paper has
  two engines (§2). (i) Main text: a *deformation* H(T) of the counting polynomial in which, at Q
  interpolation points, every factor reads only one of r groups plus a few shared integer
  "measurements"; H(0) is recovered by Hermite interpolation. The √log comes from the **binomial
  CLT width**: the replacement forms need degree R ≈ √(Q log(1/ε)) (exact agreement of a degree-R
  polynomial with the parity on all but ε of the biased cube — the real probabilistic degree of parity, optimal within their swap algebra), and
  Q ≈ log n / log r because the auxiliary label space ([r]²)^Q must be poly(n). Exponent ≈ n·R/Q.
  (ii) Appendix (sharp bound): a recursive **Boolean tensor-contraction theorem**, s wires in
  2^{O(s/√log s)}, whose cost per call is the number of "mode monomials" of weight < precision —
  a **K-coloured partition count exp(√(K·p)) = exp(M/√u)**, i.e. the *same Hardy–Ramanujan Fock-space
  growth* that fixes ρ = 1/√2 in Anthropic's pieces. Both refutations land on α = 1/2 for
  structurally the same reason (bosonic √E growth), so OpenAI offers no ready-made α' > 1/2.
* **The one genuinely transferable asymmetry:** OpenAI's main-text engine charges for *Boolean
  variables* N and only for the *logarithm* of the incidence density M/N (it enters as
  log(1/ε) ≈ log(M/N) under the square root), whereas Anthropic's engine charges for shared bits
  (≈ incidences). Feeding it **Ryser's formula** (N = n variables, n linear row factors with m
  incidences, total degree 2n) gives, by my parameter analysis (not a written proof), the permanent /
  #PM of an n×n matrix with ≤ Δ nonzeros per row and column in
  **2^{O(n·√(log Δ·loglog n / log n)·loglog n + n(loglog n)²/√log n)}**: sub-exponential whenever
  log Δ = o(log n/(loglog n)³), versus our 2^{O(n log Δ/√log n)} (needs log Δ = o(√log n)); the same
  holds for general-graph #PM via a product formula (§4(d)). Quadratically better dependence on log Δ, still nothing for dense
  matrices (log(m/n) ≈ log n kills it: the degree R would exceed Q). End-to-end exact toy check of the
  whole pipeline on Ryser's formula: §5, script `scripts/oai_ryser_replacement.py`.
* **Ranked ideas (§6):** (1) Ryser + replacement-form engine for sparse permanents/#PM (promising,
  near-mechanical, verified on toys); (2) "beat the parity/CLT barrier": structured label sets or a
  non-commutative M₀ with R = o(√Q) would give α' > 1/2 for *OpenAI's* engine, an independent target
  from ρ < 1/√2 (speculative; I sketch why the swap algebra is optimal); (3) the 2-adic
  Cauchy-deformation + mode-weight bookkeeping as an alternative Fock space for pieces (low odds:
  locality of the delta kernel seems to force linear mode weights, hence partition growth).

## 1. Inventory (all 373 families)

Columns: family number, subject (from `overview.tex`), title, Lean link in the catalogue (Y = a Lean
formalization of at least part is linked), preprint date range, number of manuscripts. TCS/combinatorics
rows relevant to us are discussed in §3.

| # | subject | title | Lean | dates (2026) | mss |
|---|---|---|---|---|---|
| 001 | Number theory | Milne’s rationality conjecture and algebraic specialization | - | Oct 7 | 1 |
| 002 | Number theory | The full BSD formula from low Selmer corank | - | Oct 6–Oct 7 | 3 |
| 003 | Number theory | The quasi-Riemann hypothesis | Y | Sep 30–Oct 5 | 3 |
| 004 | Number theory | Hilbert’s tenth problem over ℚ | - | Oct 6–Oct 7 | 2 |
| 005 | Number theory | Irrationality of Catalan’s constant | Y | Sep 24 | 1 |
| 006 | Number theory | Goldfeld’s conjecture: densities and mean analytic rank | - | Oct 6–Oct 7 | 2 |
| 007 | Number theory | Ordinary two-point correlations and the corrected Elliott conjecture | Y | Sep 24 | 1 |
| 008 | Number theory | The Deligne–Drinfeld conjecture | Y | Sep 23 | 1 |
| 009 | Number theory | Function-field reconstruction from Milnor K-theory and Galois data | Y | Sep 23–Oct 5 | 3 |
| 010 | Number theory | Unrestricted pro-modularity at the prime two | - | Oct 5–Oct 6 | 3 |
| 011 | Number theory | Prime-factor statistics of $`p-1`$ | - | Sep 17–Sep 24 | 3 |
| 012 | Number theory | Independent largest prime factors of consecutive integers | Y | Sep 24 | 1 |
| 013 | Number theory | Ostmann’s inverse Goldbach conjecture | Y | Sep 24 | 1 |
| 014 | Number theory | Restricted geometric Langlands, global Arthur enhancements, and generic Ramanujan | - | Sep 24–Oct 5 | 8 |
| 015 | Number theory | Torus-packet equidistribution in prime, quartic, and sextic degrees | Y | Sep 24–Oct 5 | 3 |
| 016 | Number theory | Zilber–Pink in abelian varieties and the Siegel threefold | - | Sep 24 | 4 |
| 017 | Number theory | The irrationality exponent of π is 2 | Y | Sep 24 | 1 |
| 018 | Number theory | The Margulis–Platonov conjecture over global fields | - | Sep 23–Oct 5 | 2 |
| 019 | Number theory | The local p-adic section conjecture and global consequences | - | Sep 24–Oct 6 | 2 |
| 020 | Number theory | Squarefree quartics and power-free polynomial values | Y | Sep 24 | 1 |
| 021 | Number theory | A quadratic bound for Jacobsthal’s function | Y | Sep 25 | 1 |
| 022 | Number theory | The weak inhomogeneous Duffin–Schaeffer conjecture | - | Sep 25 | 1 |
| 023 | Number theory | Patterson's first moment for cubic Gauss sums | Y | Sep 25 | 1 |
| 024 | Number theory | An asymptotic formula for the number of totients | Y | Sep 25 | 1 |
| 025 | Number theory | Short Egyptian fractions | Y | Sep 25 | 1 |
| 026 | Number theory | Positive lower density of large prime gaps | Y | Sep 25 | 1 |
| 027 | Number theory | Potential integral density on curve character varieties | Y | Sep 25 | 1 |
| 028 | Number theory | Uniformly bounded components of Gaussian-prime graphs | Y | Sep 26 | 1 |
| 029 | Number theory | Primitive roots for every admissible integer base | - | Oct 4 | 2 |
| 030 | Number theory | Modularity of elliptic curves over imaginary quadratic fields | - | Oct 4 | 1 |
| 031 | Number theory | Uchida’s conjecture for open homomorphisms of Galois groups | - | Oct 5 | 1 |
| 032 | Algebraic and complex geometry | The rational Hodge conjecture for CM abelian varieties | Y | Sep 10–Oct 6 | 5 |
| 033 | Algebraic and complex geometry | Iitaka subadditivity, variation, and logarithmic additivity | Y | Sep 10–Sep 27 | 5 |
| 034 | Algebraic and complex geometry | Log abundance for compact Kähler spaces under logarithmic Iitaka subadditivity | - | Sep 24–Oct 6 | 14 |
| 035 | Algebraic and complex geometry | Log-canonical threefold abundance in numerical dimension one | - | Sep 24–Oct 5 | 2 |
| 036 | Algebraic and complex geometry | Numerical semiampleness and generalized minimal models | - | Sep 24–Oct 6 | 4 |
| 037 | Algebraic and complex geometry | The ordinary-double-point volume gap | - | Sep 24 | 2 |
| 038 | Algebraic and complex geometry | Fujita’s freeness conjecture | - | Sep 23 | 1 |
| 039 | Algebraic and complex geometry | Nagata’s conjecture and maximal Seshadri constants | Y | Sep 23–Oct 5 | 4 |
| 040 | Algebraic and complex geometry | Bloch’s conjecture for complex surfaces | - | Sep 24 | 1 |
| 041 | Algebraic and complex geometry | Hyperkähler SYZ and projective-space bases | - | Sep 23 | 2 |
| 042 | Algebraic and complex geometry | Oka classification for minimal compact complex surfaces: Kodaira dimension zero and class VII | - | Sep 23 | 1 |
| 043 | Algebraic and complex geometry | P = W for fixed-determinant SLn moduli spaces | - | Sep 24 | 1 |
| 044 | Algebraic and complex geometry | The equivariant cohomological Hikita conjecture | - | Sep 24 | 1 |
| 046 | Algebraic and complex geometry | Shafarevich counterexamples in dimension two and with large fundamental group | - | Sep 23–Oct 5 | 2 |
| 047 | Algebraic and complex geometry | Zariski cancellation and affine fibrations over the complex numbers | Y | Sep 23 | 1 |
| 048 | Algebraic and complex geometry | A characteristic-zero counterexample to Lipman–Zariski | - | Sep 23 | 1 |
| 049 | Algebraic and complex geometry | A stable-coordinate counterexample in four variables | Y | Sep 24–Oct 5 | 2 |
| 050 | Algebraic and complex geometry | A counterexample to Griffiths’ positivity conjecture | Y | Sep 24 | 1 |
| 051 | Algebraic and complex geometry | Kobayashi’s canonical-ampleness conjecture | - | Sep 23 | 1 |
| 052 | Algebraic and complex geometry | Tangent splittings and product decompositions | Y | Sep 23 | 2 |
| 053 | Algebraic and complex geometry | A counterexample to Pixton completeness in Chow | - | Sep 24 | 1 |
| 054 | Algebraic and complex geometry | Irrational cubic fourfolds with Hodge-theoretic and categorical K3 associations | - | Sep 24 | 1 |
| 055 | Algebraic and complex geometry | Gepner symmetry and large-volume stability on threefolds | - | Sep 24 | 2 |
| 056 | Algebraic and complex geometry | Termination of projective and Kähler fourfold minimal model programs | - | Sep 24–Oct 7 | 5 |
| 057 | Algebraic and complex geometry | Fundamental groups of special complex varieties and root orbifolds | - | Sep 23–Oct 5 | 3 |
| 058 | Algebraic and complex geometry | Semialgebraic universal covers and bounded domains | Y | Sep 24 | 2 |
| 059 | Algebraic and complex geometry | Counterexamples to Zariski’s multiplicity conjecture | - | Sep 24–Sep 27 | 2 |
| 060 | Algebraic and complex geometry | The Global Spherical Shell conjecture | - | Sep 24 | 1 |
| 062 | Algebraic and complex geometry | Projective contact classification and the LeBrun–Salamon conjecture | - | Sep 23 | 1 |
| 063 | Algebraic and complex geometry | The generalized Mukai conjecture | - | Sep 24 | 1 |
| 064 | Algebraic and complex geometry | Topological triviality of μ-constant surface singularities | - | Sep 24 | 1 |
| 065 | Algebraic and complex geometry | Virasoro constraints for complete intersections and projective-bundle towers | - | Sep 24–Oct 5 | 2 |
| 066 | Algebraic and complex geometry | Bounded klt complements for Fano contractions | Y | Sep 25 | 2 |
| 067 | Algebraic and complex geometry | The Campana–Peternell conjecture in dimension six | - | Sep 25 | 1 |
| 068 | Algebraic and complex geometry | Anticanonical nonvanishing in every dimension | - | Sep 26 | 7 |
| 069 | Algebraic and complex geometry | Global quantum geometric Langlands at irrational level | - | Oct 4 | 1 |
| 071 | Real and complex analysis | Koebe’s circle-domain conjecture | Y | Sep 23 | 2 |
| 072 | Real and complex analysis | Brennan's conjecture and the integral-means spectrum | Y | Sep 24 | 2 |
| 073 | Real and complex analysis | The Falconer distance conjecture | Y | Sep 23 | 1 |
| 074 | Real and complex analysis | Kakeya in three and four dimensions | - | Sep 23–Sep 24 | 2 |
| 075 | Real and complex analysis | The $`L\log L`$ Fourier-convergence conjecture | Y | Sep 23 | 1 |
| 076 | Real and complex analysis | Real ultraflat Littlewood polynomials and unbounded binary merit factors | Y | Sep 23–Oct 5 | 3 |
| 077 | Real and complex analysis | Fourier restriction for positively curved surfaces | - | Sep 24 | 2 |
| 078 | Real and complex analysis | The three-dimensional Bochner–Riesz conjecture | - | Sep 24 | 1 |
| 079 | Real and complex analysis | Local smoothing for the Euclidean wave equation | Y | Sep 24–Oct 25 | 2 |
| 080 | Real and complex analysis | The exact Sobolev endpoint for Schrödinger convergence | - | Sep 24 | 2 |
| 081 | Real and complex analysis | Riesz transforms and rectifiability in higher codimension | Y | Sep 24 | 1 |
| 082 | Real and complex analysis | Annular variation and dyadic absolute bounds for the triangular Hilbert transform | Y | Sep 24–Oct 5 | 3 |
| 083 | Real and complex analysis | Hilbert transforms along Lipschitz directions | Y | Sep 25 | 1 |
| 084 | Real and complex analysis | The geometric case of the Erdős similarity conjecture | Y | Sep 25–Oct 5 | 2 |
| 085 | Real and complex analysis | Endpoint Sobolev regularity of centered disk averages | Y | Sep 26 | 1 |
| 086 | Real and complex analysis | An L3 bound for the trilinear Hilbert transform | - | Oct 5 | 1 |
| 087 | Convex and metric geometry | The Mahler conjectures, functional inequalities and polar-product symplectic width | Y | Sep 22 | 3 |
| 088 | Convex and metric geometry | Sharp projection-body inequalities and a counterexample to simplex maximization | Y | Sep 24 | 2 |
| 089 | Convex and metric geometry | Bounded-distortion L1 embeddings of planar and bounded-treewidth graphs | Y | Sep 23 | 2 |
| 090 | Convex and metric geometry | Triangular-lattice optimality, long-range Riesz and Coulomb energies, and spherical logarithmic energy | Y | Sep 23–Sep 26 | 4 |
| 091 | Convex and metric geometry | Logarithmic and Lp Brunn–Minkowski inequalities and the B-conjecture | Y | Sep 23 | 1 |
| 092 | Convex and metric geometry | The optimal order of convex-body covering density | Y | Sep 23 | 2 |
| 093 | Convex and metric geometry | Dimension-free logarithmic Sobolev inequality for subgaussian log-concave measures | - | Sep 23 | 1 |
| 094 | Convex and metric geometry | Subpolynomial dimension reduction in Lp | Y | Sep 23 | 1 |
| 095 | Convex and metric geometry | Hyperbolicity cones without semidefinite lifts | Y | Sep 24–Oct 5 | 3 |
| 096 | Convex and metric geometry | The Gaussian propeller conjecture in every dimension | Y | Sep 24 | 1 |
| 097 | Convex and metric geometry | The Euclidean Steinitz–Bergström bound | Y | Sep 24 | 1 |
| 098 | Convex and metric geometry | Compact counterexamples to bi-Lipschitz dimension reduction | Y | Sep 25 | 1 |
| 099 | Convex and metric geometry | The sharp exponential scale of edit-distance distortion | Y | Sep 27 | 3 |
| 100 | Convex and metric geometry | Cylinder coverings below the half-area bound | Y | Sep 27 | 4 |
| 101 | Convex and metric geometry | The sharp simplex conjecture for isotropic constants | - | Oct 5 | 1 |
| 102 | Theoretical computer science | The Unique Games Conjecture and optimal approximation thresholds | Y | Sep 23 | 5 |
| 103 | Theoretical computer science | Exact derandomization of logarithmic space: $`\mathsf L=\mathsf{RL}=\mathsf{BPL}`$ | Y | Sep 23 | 1 |
| 104 | Theoretical computer science | Quasipolynomial algorithms for mean-payoff, stochastic and parity games | Y | Sep 25–Oct 5 | 4 |
| 105 | Theoretical computer science | Perfect completeness for 2-to-1 games | Y | Sep 23 | 1 |
| 106 | Theoretical computer science | Hardness of coloring three-colorable graphs | Y | Sep 24 | 1 |
| 107 | Theoretical computer science | Matrix multiplication with exponent at most 9/4 | Y | Sep 24–Oct 2 | 3 |
| 108 | Theoretical computer science | A cubic permanent–determinant lower bound | Y | Sep 24 | 1 |
| 109 | Theoretical computer science | Integer multiplication below $`n\log n`$ | - | Sep 23 | 1 |
| 110 | Theoretical computer science | Optimal-order randomized k-server on arbitrary metrics | Y | Sep 24 | 2 |
| 111 | Theoretical computer science | One-sample matroid prophet inequalities against an almighty adversary | Y | Sep 23 | 1 |
| 112 | Theoretical computer science | Beyond the square-root exponent for depth-three circuits | Y | Sep 23 | 1 |
| 113 | Theoretical computer science | Approximate counting and entropy of perfect matchings | Y | Sep 23 | 2 |
| 114 | Theoretical computer science | Approximate counting of common integer polymatroid bases | Y | Sep 23–Oct 5 | 2 |
| 115 | Theoretical computer science | Sampling and counting contingency tables with arbitrary margins | Y | Sep 24 | 2 |
| 116 | Theoretical computer science | Uniform black-box noncommutative identity testing across characteristics | Y | Sep 24–Oct 4 | 3 |
| 117 | Theoretical computer science | Uniform sparsest cut: hardness and semidefinite gaps | Y | Sep 24 | 2 |
| 118 | Theoretical computer science | Bin packing and unbounded configuration-LP gaps | Y | Sep 24 | 1 |
| 119 | Theoretical computer science | The Courtade–Kumar and Hellinger conjectures | Y | Sep 24 | 2 |
| 120 | Theoretical computer science | Almost-linear-time exact matching and prescribed-degree factors in general graphs | - | Sep 24 | 1 |
| 121 | Theoretical computer science | Almost-linear approximation of edit distance | Y | Sep 24 | 1 |
| 122 | Theoretical computer science | Quantitative trace-reconstruction bounds with a uniform decoder | Y | Sep 24–Oct 5 | 3 |
| 124 | Theoretical computer science | Polynomial-time scheduling on three identical machines | Y | Sep 24 | 1 |
| 125 | Theoretical computer science | The metric k-median approximation threshold and recovery | Y | Sep 24 | 2 |
| 126 | Theoretical computer science | Exponential semidefinite complexity of perfect matching | Y | Oct 5 | 1 |
| 127 | Theoretical computer science | Average sensitivity of polynomial threshold functions | Y | Sep 25 | 1 |
| 128 | Theoretical computer science | A factor-two approximation for shortest common superstring | Y | Sep 24 | 1 |
| 129 | Theoretical computer science | Exponential state costs for two-way automata | Y | Sep 25 | 2 |
| 130 | Theoretical computer science | Exact Fourier transforms below $`n\log n`$ | Y | Sep 25 | 2 |
| 131 | Theoretical computer science | Rapid mixing of graph switches for every degree sequence | Y | Sep 25 | 1 |
| 132 | Theoretical computer science | A superquadratic separation of sensitivity and block sensitivity | Y | Sep 25 | 1 |
| 133 | Theoretical computer science | The computational complexity of Weisfeiler–Leman refinement | Y | Sep 25 | 4 |
| 134 | Theoretical computer science | Generalized star height at most three | Y | Sep 25 | 3 |
| 135 | Theoretical computer science | Homogeneous depth-five lower bounds for iterated matrix multiplication | Y | Sep 25 | 1 |
| 136 | Theoretical computer science | A quasilinear PCP theorem for PPAD | - | Sep 25 | 1 |
| 137 | Theoretical computer science | One-tape time simulation in two-fifths-power space | Y | Sep 25 | 1 |
| 138 | Theoretical computer science | Subset Sum in $`O(2^{0.49n})`$ time | - | Sep 26–Oct 4 | 2 |
| 139 | Theoretical computer science | Subpolynomial query complexity for log-concave sampling | Y | Sep 26 | 1 |
| 140 | Theoretical computer science | Memory–sample lower bounds for noiseless Gaussian regression | Y | Sep 27 | 6 |
| 141 | Theoretical computer science | Existential–universal real sentences in the counting hierarchy | - | Oct 4 | 1 |
| 142 | Theoretical computer science | Deterministic polynomial factorization over prime fields | - | Oct 4 | 1 |
| 143 | Dynamical systems and ergodic theory | Hilbert's sixteenth problem: uniform bounds for limit cycles | Y | Sep 24 | 2 |
| 144 | Dynamical systems and ergodic theory | Banach’s simple Lebesgue-spectrum problem | Y | Sep 23 | 1 |
| 145 | Dynamical systems and ergodic theory | Rokhlin’s multiple-mixing problem | Y | Sep 23 | 1 |
| 146 | Dynamical systems and ergodic theory | Positive metric entropy for the standard map | Y | Sep 23 | 1 |
| 147 | Dynamical systems and ergodic theory | The near-boundary Birkhoff conjecture | - | Sep 24 | 2 |
| 148 | Dynamical systems and ergodic theory | The entropy-rate dimension formula for self-similar measures | Y | Sep 24 | 1 |
| 149 | Dynamical systems and ergodic theory | Classwise permanence for weakly reversible mass-action systems | Y | Sep 25–Oct 5 | 2 |
| 150 | Dynamical systems and ergodic theory | Weak mixing of triangular billiards with an irrational angle | Y | Sep 25–Oct 5 | 2 |
| 151 | Dynamical systems and ergodic theory | A C1 counterexample to the entropy conjecture | Y | Sep 25 | 1 |
| 152 | Dynamical systems and ergodic theory | Zero entropy does not guarantee a smooth positive-volume model | Y | Sep 25 | 1 |
| 153 | Dynamical systems and ergodic theory | Arithmetic classification and non-Pisot singularity for Bernoulli convolutions | - | Oct 3 | 1 |
| 154 | Dynamical systems and ergodic theory | Pointwise multiple ergodic averages for mixing transformations | - | Oct 4 | 4 |
| 155 | Combinatorics | A counterexample to periodic tiling in dimension three | Y | Sep 23 | 1 |
| 156 | Combinatorics | Borsuk's conjecture fails in dimension nine | Y | Sep 23 | 1 |
| 157 | Combinatorics | Graph coloring, clique minors, and Colin de Verdière invariants | Y | Sep 23 | 3 |
| 158 | Combinatorics | The Euclidean plane cannot be colored with five colors | Y | Sep 23 | 1 |
| 159 | Combinatorics | Erdős’s reciprocal-sum conjecture and quasipolynomial Szemerédi bounds | Y | Sep 23 | 1 |
| 160 | Combinatorics | Superexponential van der Waerden numbers | Y | Sep 23 | 1 |
| 161 | Combinatorics | Counterexamples to Sidorenko’s conjecture and the forcing conjecture | Y | Sep 23 | 1 |
| 162 | Combinatorics | Counterexamples to Ryser’s covering conjecture | Y | Sep 23–Sep 27 | 2 |
| 164 | Combinatorics | Hindman’s finite sums and products conjecture | - | Sep 23 | 1 |
| 165 | Combinatorics | The Harary–Hill and Zarankiewicz crossing-number formulas | Y | Sep 23 | 2 |
| 166 | Combinatorics | The higher-dimensional Erdős distinct-distances conjecture | - | Sep 23 | 1 |
| 167 | Combinatorics | Planar distinct distances and unit-distance bounds | Y | Sep 23 | 2 |
| 168 | Combinatorics | Combinatorial invariance of Kazhdan–Lusztig polynomials | Y | Sep 24 | 1 |
| 169 | Combinatorics | Shareshian–Wachs elementary positivity | Y | Sep 24 | 1 |
| 170 | Combinatorics | Sharp logarithmic exponents for off-diagonal Ramsey numbers | Y | Sep 24 | 2 |
| 171 | Combinatorics | The hypercube Ramsey conjecture | - | Sep 23 | 1 |
| 172 | Combinatorics | Classification of finite Euclidean Ramsey configurations | Y | Sep 23 | 1 |
| 173 | Combinatorics | Seymour’s second-neighborhood conjecture | Y | Sep 23 | 1 |
| 174 | Combinatorics | Deterministic construction of strong thin spanning trees | Y | Sep 23 | 2 |
| 175 | Combinatorics | Talagrand’s expectation thresholds, discrete convexity, and graph decompositions | Y | Sep 23–Oct 5 | 3 |
| 176 | Combinatorics | The second Kahn–Kalai conjecture with an edge-count bound | Y | Sep 24 | 1 |
| 177 | Combinatorics | Bounded-degree coboundary expanders | Y | Sep 24 | 1 |
| 178 | Combinatorics | Deterministic nonbipartite Ramanujan graphs in every fixed degree | - | Sep 23 | 1 |
| 179 | Combinatorics | The circulant Hadamard and Barker-sequence conjectures | Y | Sep 23 | 1 |
| 180 | Combinatorics | Barnette’s Hamiltonian-cycle conjecture | Y | Sep 24 | 1 |
| 181 | Combinatorics | The Erdős–Gallai cycle-decomposition conjecture | Y | Sep 24 | 1 |
| 182 | Combinatorics | Power savings for intersective polynomial differences and prime arguments | Y | Sep 24–Oct 5 | 3 |
| 183 | Combinatorics | Power savings for planar halving lines and k-sets | Y | Sep 25 | 1 |
| 184 | Combinatorics | Correspondence coloring with a fixed forbidden subgraph | Y | Sep 25–Oct 5 | 2 |
| 185 | Combinatorics | Counterexamples to infinite matroid intersection and packing/covering | Y | Sep 24 | 1 |
| 186 | Combinatorics | Uniform influence and sharp thresholds for graph and hypergraph properties | Y | Sep 25–Oct 5 | 2 |
| 187 | Combinatorics | Snaky in 21 Maker moves | Y | Sep 25 | 1 |
| 188 | Combinatorics | The sharp terminal leave in random triangle removal | Y | Sep 25 | 1 |
| 189 | Combinatorics | Cycle–clique Ramsey numbers | Y | Sep 25 | 1 |
| 190 | Combinatorics | Polynomial removal fails for ordered binary matrices | Y | Sep 25 | 1 |
| 191 | Combinatorics | A power improvement in the Heilbronn triangle lower bound | Y | Sep 25 | 1 |
| 192 | Combinatorics | Boolean functions violate the square-root degree bound by arbitrary factors | Y | Sep 26 | 1 |
| 193 | Algebra | Serre’s intersection-multiplicity conjecture | - | Sep 23 | 1 |
| 194 | Algebra | Lech’s multiplicity conjecture | Y | Sep 23 | 1 |
| 195 | Algebra | A counterexample to the small Cohen–Macaulay module conjecture | Y | Sep 23 | 1 |
| 196 | Algebra | A counterexample to Kaplansky’s zero-divisor conjecture | Y | Sep 23 | 1 |
| 197 | Algebra | A torsion-free group algebra that is not directly finite | Y | Sep 23–Oct 4 | 4 |
| 198 | Algebra | A counterexample to finitistic-dimension finiteness | Y | Sep 23 | 1 |
| 199 | Algebra | Counterexamples to Auslander–Reiten, Tachikawa and related homological conjectures | Y | Sep 23 | 2 |
| 200 | Algebra | Eisenbud–Green–Harris and lex-plus-powers | - | Sep 23 | 2 |
| 201 | Algebra | A counterexample to Kurosh’s division-ring problem | - | Sep 23 | 1 |
| 202 | Algebra | The blockwise Alperin weight conjecture | - | Sep 23 | 1 |
| 203 | Algebra | Donovan's conjecture over fields and complete mixed-characteristic DVRs | - | Sep 24–Sep 25 | 2 |
| 204 | Algebra | Tensor saturation for even spin groups | - | Sep 24 | 1 |
| 205 | Algebra | Saxl’s conjecture and universal tensor squares | Y | Sep 24 | 2 |
| 206 | Algebra | Finite lattice representation and undecidability | Y | Sep 24 | 2 |
| 207 | Algebra | The ℓ¹-Bass conjecture for all discrete groups | Y | Sep 24–Oct 5 | 2 |
| 208 | Algebra | Finite symmetric tensor categories and the Verlinde tower | - | Sep 24 | 1 |
| 209 | Algebra | Integral counterexamples to Gersten’s conjecture | - | Sep 25–Sep 26 | 2 |
| 210 | Algebra | Foulkes' conjecture for sixth powers and quadratic stabilization | Y | Sep 25 | 2 |
| 211 | Probability and statistical mechanics | The geometric phase diagram, diffusion, and spectra of random planar maps | Y | Sep 24–Oct 5 | 7 |
| 212 | Probability and statistical mechanics | Planar first-passage geometry and the absence of bigeodesics | Y | Sep 24 | 2 |
| 213 | Probability and statistical mechanics | Critical percolation on every quasi-transitive graph | Y | Sep 24 | 2 |
| 214 | Probability and statistical mechanics | The Benjamini–Schramm nonuniqueness conjecture | Y | Sep 24 | 1 |
| 215 | Probability and statistical mechanics | Canonical $`O(3)`$ continuum limit and exact $`O(4)`$ mass asymptotics | Y | Sep 23–Oct 5 | 5 |
| 216 | Probability and statistical mechanics | Critical and near-critical XY scaling and BKT universality | - | Sep 24–Oct 5 | 6 |
| 217 | Probability and statistical mechanics | The low-temperature Sherrington–Kirkpatrick fluctuation law | - | Sep 24 | 2 |
| 218 | Probability and statistical mechanics | Conformal universality for weakly interacting and random-bond Ising models | Y | Sep 23–Oct 5 | 6 |
| 219 | Probability and statistical mechanics | GOE bulk universality for regular graphs with weak Anderson disorder | - | Sep 23–Oct 5 | 2 |
| 220 | Probability and statistical mechanics | Directional zero–one laws beyond iid environments and iid ballisticity | Y | Sep 23–Oct 5 | 3 |
| 221 | Probability and statistical mechanics | The Mézard–Parisi formula for diluted spin glasses | Y | Sep 23 | 1 |
| 222 | Probability and statistical mechanics | Perceptron free energies and microscopic jamming exponents | Y | Sep 24 | 4 |
| 223 | Probability and statistical mechanics | Random-cluster interfaces: critical, disordered, thermal, and natural-time scaling | - | Sep 23–Oct 5 | 6 |
| 224 | Probability and statistical mechanics | Critical and quenched near-critical universality for Poisson–Voronoi percolation | - | Sep 23–Oct 5 | 3 |
| 225 | Probability and statistical mechanics | Gaussian free field limits throughout the balanced six-vertex regime | - | Sep 23 | 1 |
| 226 | Probability and statistical mechanics | The double-dimer loop ensemble converges to CLE4 | - | Sep 23 | 1 |
| 227 | Probability and statistical mechanics | Critical SK autocorrelation processes and dynamics across the temperature transition | Y | Sep 24–Oct 5 | 8 |
| 228 | Probability and statistical mechanics | Continuum phase transitions for radial pair potentials | Y | Sep 24 | 2 |
| 229 | Probability and statistical mechanics | Exact three- and four-state reconstruction thresholds and four-state tree capacity | Y | Sep 25–Oct 5 | 3 |
| 230 | Probability and statistical mechanics | Exact Hausdorff gauges for SLE | Y | Sep 25–Sep 26 | 2 |
| 231 | Probability and statistical mechanics | The free uniform spanning forest is a factor of IID | Y | Sep 25 | 1 |
| 232 | Probability and statistical mechanics | Gaussian fields and interfaces for triangular-lattice Lipschitz heights | - | Oct 6 | 3 |
| 233 | Probability and statistical mechanics | The joint critical Ashkin–Teller current limit | - | Oct 6 | 1 |
| 234 | Probability and statistical mechanics | All-temperature pressure of orthogonally invariant Ising spin glasses | Y | Sep 25 | 1 |
| 235 | Probability and statistical mechanics | Limiting random SAT thresholds, sharp variance and computability | Y | Sep 25–Oct 5 | 4 |
| 236 | Probability and statistical mechanics | The exact factor-of-IID threshold for free Ising spins on trees | Y | Sep 26 | 1 |
| 237 | Probability and statistical mechanics | The three-quarter exponent for honeycomb self-avoiding walk | Y | Sep 26 | 13 |
| 238 | Probability and statistical mechanics | Optimal logarithmic mixing of the Thorp shuffle | Y | Sep 26 | 12 |
| 239 | Probability and statistical mechanics | Sharp singularity rates for symmetric random sign matrices | - | Oct 3–Oct 4 | 2 |
| 240 | Mathematical logic | Shelah's eventual categoricity and the prescribed-threshold obstruction | Y | Sep 24 | 2 |
| 241 | Mathematical logic | Rigidity of the Turing degrees | Y | Sep 24 | 1 |
| 242 | Mathematical logic | Single-fold Diophantine representations and undecidability under an at-most-one-solution promise | Y | Sep 24 | 1 |
| 243 | Mathematical logic | Separating choiceless counting from polynomial time and witnessed choice | Y | Sep 23–Sep 24 | 2 |
| 244 | Mathematical logic | The Partition Principle does not imply Choice | Y | Sep 24 | 1 |
| 245 | Mathematical logic | Weak normalization implies strong normalization in pure type systems | Y | Sep 25 | 1 |
| 246 | Group theory | Cannon's conjecture | Y | Sep 23 | 1 |
| 247 | Group theory | An infinite finitely presented residually finite 2-group and a finitely presented nil algebra | Y | Sep 23–Oct 5 | 2 |
| 248 | Group theory | Thompson's group F is nonamenable | Y | Sep 23 | 1 |
| 249 | Group theory | A finitely generated Eilenberg–Ganea counterexample | Y | Sep 23 | 1 |
| 250 | Group theory | Boone–Higman embeddings with higher finiteness | Y | Sep 23 | 3 |
| 251 | Group theory | Amenability, unitarizability, and strong Ulam stability | Y | Sep 23–Oct 5 | 2 |
| 252 | Group theory | A torsion-free hyperbolic group that is neither residually finite nor linear over any field | Y | Sep 23 | 1 |
| 253 | Group theory | An infinite finitely presented simple amenable group | Y | Sep 23 | 1 |
| 254 | Group theory | Classifying spaces and geometric obstructions for Artin groups | Y | Sep 23 | 3 |
| 255 | Group theory | Quasi-isometric recognition of virtually polycyclic groups | Y | Sep 24 | 1 |
| 256 | Group theory | Nonsingular systems of equations over arbitrary groups | Y | Sep 24–Oct 5 | 2 |
| 257 | Group theory | A hyperbolic group without a geometric CAT(0) action | Y | Sep 25 | 1 |
| 258 | Group theory | Gersten’s conjecture and virtual compact specialness of one-relator groups | - | Sep 25 | 2 |
| 259 | Group theory | A group without fixed price | - | Oct 5 | 1 |
| 260 | Mathematical physics | Spacetime Penrose inequalities: enclosing area, charge, rotation, and anti-de Sitter extensions | Y | Sep 27–Oct 5 | 13 |
| 261 | Mathematical physics | Localization and delocalization in the Anderson model | Y | Sep 23 | 2 |
| 262 | Mathematical physics | Sharp finite-matrix Lieb–Thirring inequalities and all equality cases | Y | Sep 23–Oct 5 | 3 |
| 263 | Mathematical physics | The ionization and generalized ionization conjectures | Y | Sep 24 | 3 |
| 264 | Mathematical physics | Strong cosmic censorship near two-ended Kerr data | - | Sep 23 | 3 |
| 265 | Mathematical physics | Area laws and tensor networks for two-dimensional gapped systems | - | Sep 24 | 2 |
| 266 | Mathematical physics | Exactly three mutually unbiased bases in dimension six | Y | Sep 24 | 2 |
| 267 | Mathematical physics | Positive-temperature Bose–Einstein condensation and exact quantum depletion | Y | Sep 24–Oct 5 | 5 |
| 268 | Mathematical physics | The spin-one Haldane gap | - | Sep 24 | 2 |
| 269 | Mathematical physics | Uniform Laughlin gap and stability under bounded scalar disorder | Y | Sep 24–Oct 5 | 2 |
| 270 | Mathematical physics | Threshold and positive-energy bound states of the BFSS matrix model | - | Sep 24–Oct 5 | 2 |
| 271 | Mathematical physics | Bloch's law, its lattice correction, and the spherical magnetization law | Y | Sep 24–Oct 5 | 4 |
| 272 | Mathematical physics | Entanglement without distillable secret key | Y | Sep 27 | 1 |
| 273 | Mathematical physics | The entropy photon-number inequality | Y | Sep 24 | 1 |
| 274 | Mathematical physics | Parity is not in QAC0 | Y | Sep 24 | 2 |
| 275 | Mathematical physics | QMA-hardness of continuum Coulomb energy | Y | Sep 24 | 2 |
| 276 | Mathematical physics | Classical capacity of generalized amplitude damping | Y | Sep 24 | 1 |
| 277 | Mathematical physics | Threshold repetition for entangled games | Y | Sep 25 | 1 |
| 278 | Mathematical physics | Failure of Kohn–Sham ensemble representation | - | Sep 25 | 1 |
| 279 | Mathematical physics | Exact quantum factoring over a fixed finite gate set | Y | Sep 25 | 1 |
| 280 | Mathematical physics | Unitary vertex operator algebras and conformal nets | Y | Sep 25 | 1 |
| 281 | Mathematical physics | QAOA attains the SK optimum in the thermodynamic-first limit | Y | Sep 25–Sep 27 | 2 |
| 282 | Mathematical physics | From scale symmetry to local conformal symmetry in four-dimensional QFT | - | Sep 26 | 1 |
| 283 | Mathematical physics | Polynomial-time unitary synthesis from a Boolean oracle | - | Oct 5 | 1 |
| 284 | Mathematical physics | The optimal quartic separation between randomized and quantum queries | - | Oct 5 | 1 |
| 285 | Operator algebras | Counterexamples to Baum–Connes and Kadison–Kaplansky | - | Sep 23 | 3 |
| 286 | Operator algebras | Rigidity and arithmetic of lattice von Neumann algebras | - | Sep 23 | 2 |
| 287 | Operator algebras | Isomorphism of the free group factors | Y | Sep 23 | 1 |
| 288 | Operator algebras | Kadison's similarity conjecture | Y | Sep 23 | 1 |
| 289 | Operator algebras | Strong Kadison–Kastler stability and its spatial boundaries | Y | Sep 23–Oct 5 | 3 |
| 290 | Operator algebras | Relative bicentralizers and modular spectral recovery | Y | Sep 23 | 2 |
| 291 | Operator algebras | Cuntz comparison, nuclear dimension, and equivariant Jiang–Su stability | Y | Sep 23–Oct 5 | 4 |
| 292 | Operator algebras | Kirchberg's $`\mathcal O_2`$ norm-ultrapower embedding problem | Y | Sep 23 | 1 |
| 293 | Operator algebras | Invariant projections, hyperinvariant subspaces, and transitive algebras | Y | Sep 27 | 2 |
| 294 | Operator algebras | Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness | Y | Sep 23 | 1 |
| 295 | Operator algebras | The Kadison–Ringrose cohomology conjecture | Y | Sep 23 | 1 |
| 296 | Operator algebras | The generator problem for finite factors | Y | Sep 23 | 1 |
| 297 | Operator algebras | A ZFC counterexample to Naimark's problem | Y | Sep 24 | 1 |
| 298 | Operator algebras | Two notions of free entropy differ even when both are finite | Y | Sep 25 | 1 |
| 299 | Operator algebras | The Kirchberg–Rørdam character criterion and infinite tensor-power Jiang–Su stability | Y | Sep 25 | 1 |
| 300 | Operator algebras | Approximation and quadratic strong-operator paving | - | Sep 25 | 2 |
| 301 | Operator algebras | Trace cones and Razak–Jacelon stabilization | Y | Sep 25 | 1 |
| 302 | Operator algebras | Radius of comparison equals half the mean dimension | - | Sep 25 | 2 |
| 303 | Operator algebras | Weak pure infiniteness and Cuntz-algebra absorption | Y | Sep 25 | 1 |
| 304 | Topology | The Hilbert–Smith conjecture in every dimension | - | Sep 23 | 1 |
| 305 | Topology | Four-dimensional disk embedding and Wall's conjecture | - | Sep 24 | 3 |
| 306 | Topology | The purely cosmetic surgery conjecture | - | Sep 23 | 1 |
| 307 | Topology | Failure of rational injectivity for maximal coarse assembly | Y | Sep 23–Oct 5 | 2 |
| 308 | Topology | Finite Smith–Toda complexes at every height | - | Sep 23 | 2 |
| 309 | Topology | The Kervaire invariant problem at the prime three | - | Sep 24 | 1 |
| 310 | Topology | Quillen's conjecture in rational homology | - | Sep 24 | 1 |
| 311 | Topology | The Hovey–Strickland and Chai conjectures | - | Sep 24 | 1 |
| 312 | Topology | The Grothendieck homotopy hypothesis | Y | Sep 24 | 1 |
| 313 | Topology | Finite generation for the $`K(n)`$-local sphere | - | Sep 24 | 1 |
| 314 | Topology | Cyclic length and chromatic fixed-point loss | - | Sep 24 | 1 |
| 315 | Topology | The four-dimensional Singer conjecture | - | Sep 25 | 1 |
| 316 | Topology | Curtis’s conjecture | - | Sep 25 | 1 |
| 317 | Topology | Thomason model structures in all strict higher dimensions | Y | Sep 25 | 1 |
| 318 | Topology | Chromatic splitting: filtrations and counterexamples | - | Sep 25–Sep 27 | 5 |
| 319 | Topology | Counterexamples to finite generation at chromatic height two | - | Sep 26 | 1 |
| 320 | Topology | Nonhomeomorphic closed aspherical four-manifolds | - | Oct 4 | 1 |
| 321 | Topology | A counterexample to Wall's finite D(2) problem | - | Oct 6 | 1 |
| 322 | Functional analysis | Tingley’s sphere-isometry problem | Y | Sep 23 | 1 |
| 323 | Functional analysis | Independence of the separable quotient problem | Y | Sep 23 | 1 |
| 324 | Functional analysis | Lipschitz equivalent Banach spaces need not be linearly isomorphic | Y | Sep 24–Sep 26 | 2 |
| 325 | Functional analysis | The complete Crouzeix conjecture | Y | Sep 23–Sep 26 | 2 |
| 326 | Functional analysis | The cotype–cotype conjecture under the approximation property | Y | Sep 23 | 1 |
| 327 | Functional analysis | Markov type characterizes superreflexivity | Y | Sep 23 | 1 |
| 328 | Functional analysis | Nonexpansive fixed points in reflexive Banach spaces | Y | Sep 24 | 1 |
| 329 | Functional analysis | A counterexample to metric-entropy duality | Y | Sep 24 | 1 |
| 330 | Functional analysis | A uniformly discrete counterexample to bounded approximation in Lipschitz-free spaces | Y | Sep 26 | 1 |
| 331 | Functional analysis | Reflexive midpoint convexity and diamond distortion | Y | Sep 27 | 7 |
| 332 | Functional analysis | Metric Markov cotype of ℓ1 and Hilbert-space Lipschitz extension | - | Oct 5 | 1 |
| 333 | Differential geometry | Smooth isometric immersions of surfaces into ℝ4 | Y | Sep 23 | 1 |
| 334 | Differential geometry | A smooth surface metric with no local isometric immersion in ℝ3 | Y | Sep 24 | 1 |
| 335 | Differential geometry | Gromov’s integral scalar-curvature bound for simplicial volume | - | Sep 23–Oct 5 | 2 |
| 336 | Differential geometry | Spectral scalar curvature, Urysohn width, and macroscopic dimension | - | Sep 23–Oct 5 | 3 |
| 337 | Differential geometry | Sharp Cartan–Hadamard isoperimetry and rigidity | Y | Sep 23 | 1 |
| 338 | Differential geometry | Yau's uniformization conjecture | - | Sep 23 | 1 |
| 339 | Differential geometry | Katok's entropy rigidity conjecture | - | Sep 23 | 1 |
| 340 | Differential geometry | A counterexample to the nearby Lagrangian conjecture | - | Sep 23 | 1 |
| 341 | Differential geometry | Donaldson's hypersymplectic deformation conjecture | - | Oct 7 | 1 |
| 342 | Differential geometry | Donaldson's tamed-to-compatible conjecture | Y | Oct 6 | 1 |
| 343 | Differential geometry | Symplectic ball packing in higher dimensions | Y | Sep 23 | 1 |
| 344 | Differential geometry | The metric Blaschke conjecture | - | Sep 23 | 1 |
| 345 | Differential geometry | Infinitely many closed geodesics on Riemannian spheres and closed three-manifolds | - | Sep 24 | 1 |
| 346 | Differential geometry | Sharp singular-set bounds for stationary integral varifolds | - | Sep 23–Oct 5 | 2 |
| 347 | Differential geometry | Counterexamples to stable-Morse and strong Arnold fixed-point bounds | Y | Sep 23–Oct 5 | 5 |
| 348 | Differential geometry | Nonnegative-curvature Einstein classification and an L2 topological gap | Y | Sep 23–Oct 5 | 3 |
| 349 | Differential geometry | The Solomon–Yau least-volume conjecture | - | Sep 23 | 1 |
| 350 | Differential geometry | Yau’s nodal bounds: surfaces and higher dimensions | Y | Sep 23 | 3 |
| 351 | Differential geometry | Scalar curvature and finite-time Ricci-flow singularities | - | Sep 24 | 3 |
| 352 | Differential geometry | A finite-time singularity of Calabi flow | - | Sep 24 | 1 |
| 353 | Differential geometry | Affine Bernstein rigidity through dimension nine and a smooth dimension-ten counterexample | Y | Sep 24–Oct 5 | 2 |
| 354 | Differential geometry | The isoperimetric profile of the cubic three-torus | Y | Sep 24 | 1 |
| 355 | Differential geometry | Unique tangent flows at the first surface singularity | - | ? | 1 |
| 356 | Differential geometry | Gigli’s characterization of Alexandrov curvature | Y | Sep 24 | 2 |
| 357 | Differential geometry | Bi-Lipschitz coordinates at every regular RCD point | - | Sep 25 | 1 |
| 358 | Differential geometry | A three-manifold without conjugate points or nonpositive curvature | Y | Sep 24 | 1 |
| 359 | Differential geometry | Negative Kähler curvature without bounded holomorphic coordinates | Y | Sep 25 | 2 |
| 360 | Differential geometry | Weak MTW curvature gives convexity and regular optimal transport | Y | Sep 25 | 2 |
| 361 | Differential geometry | Failure of integer-degree harmonic dimension comparison | Y | Sep 25–Sep 26 | 2 |
| 362 | Partial differential equations | Global smoothness for relativistic Vlasov–Maxwell | Y | Sep 23 | 1 |
| 363 | Partial differential equations | Nonuniqueness with local conservation for the hard-sphere Boltzmann equation | Y | Sep 23–Oct 5 | 2 |
| 364 | Partial differential equations | Kinetic limits and fluctuations over the Boltzmann lifespan | - | Sep 23 | 2 |
| 365 | Partial differential equations | Joint metric and connection recovery from one boundary patch | Y | Sep 23–Oct 5 | 3 |
| 366 | Partial differential equations | The planar Mumford–Shah regularity conjecture and local weak-L4 gradient bounds | - | Sep 24 | 1 |
| 367 | Partial differential equations | The critical dimension for the one-phase Bernoulli problem | Y | Sep 24 | 1 |
| 368 | Partial differential equations | The three-dimensional Ball–Evans approximation problem | - | Sep 24 | 2 |
| 369 | Partial differential equations | The hot spots conjecture for simply connected planar domains | Y | Sep 24 | 1 |
| 370 | Partial differential equations | The Lane–Emden and Hénon–Lane–Emden conjectures | Y | Sep 24 | 1 |
| 371 | Partial differential equations | Stable blowup for the defocusing Schrödinger equation | Y | Sep 24 | 1 |
| 372 | Partial differential equations | Global uniqueness in smooth isotropic elasticity | Y | Sep 24 | 1 |
| 373 | Partial differential equations | Nonattainment of the three-marginal Coulomb Monge problem | Y | Sep 25 | 1 |
| 374 | Partial differential equations | Sharp one-third stability of Brenier maps | Y | Sep 25 | 1 |
| 375 | Partial differential equations | De Giorgi's conjecture in dimension eight | - | Sep 26 | 1 |
| 376 | Partial differential equations | Universal computation in forced Navier–Stokes flows | Y | Sep 27–Oct 6 | 9 |
| 377 | Partial differential equations | Interior $`C^{1,\alpha}`$ regularity for infinity-harmonic functions | - | Oct 4 | 1 |
| 378 | Theoretical computer science | Disproof of the Exponential Time Hypothesis | Y | Oct 25 | 1 |

## 2. OpenAI's ETH proof: the two engines, and how they compare with Anthropic's

Paper: `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex`
(technique overview l.540–1663, construction §4 l.2073–2845, sparse-polynomial systems §5, hashing §6),
`quantitative-reduction.tex` and `quantitative-contraction.tex` (Appendix: the sharp bound). Lean
(`lean/docs/378.md`) covers the weaker main-text bound 2^{O_k(n (log log n)²/√log n)}; the sharp
2^{O(n log log n/√log n)} (and 2^{O(n/√log n)} for m ≤ Dn) is the appendix, not formalized.

### 2.1 Engine I (main text): deformation, shared measurements, Hermite recovery [P, checked in §5]

* **Object.** #F = Σ_{x∈{0,1}^n} Π_f Φ_f(x) with factors of small scope and **total X-degree O(n)**
  (3-occurrence 3-CNF: deg ≤ M ≤ 3n). Replace every *occurrence* X_v in factor f by a linear form
  ⟨P_{f,v}(T), X⟩ with P_{f,v}(0) = δ_v and deg_T ≤ R. Then H(T) = Σ_x Π_f Φ_f(⟨P(T),x⟩) has
  H(0) = #F and deg H ≤ (deg)·R.
* **Design at t = 1..Q.** Variables are split into r groups S_{t,g}, each factor is assigned to one group
  σ_f(t), and the forms of f depend on other groups only through a few shared *integer measurements*
  y_h = C_h x_h (≤ 2τn rows in total, row coefficient sum ≤ D). Fixing y, the sum factorises over groups:
  H(t) = Σ_y Π_g Σ_{u∈{0,1}^{S_g}, C_g u = y_g} A_{t,g}(u; y). Cost (2D+1)^{2τn}·2^{2n/r}.
* **Taylor data.** H(0) is recovered by Hermite interpolation from the jets H(t+z) mod z^J at t ∈ [Q],
  J ≈ deg H/Q; the jets come from 2^j C(n,j) (j ≤ q) "restricted sums" with the formal shift input
  fixed to Boolean 1_U (inclusion–exclusion), each again computed by group separation.
* **The construction (the new mechanism).** Auxiliary labels B = ([r]×[r])^Q (pairs "group of the
  variable, group of the factor" at each point), swaps Π_s, W₀ = ½Σ(I − Π_s), V₀ = ΠΠ_s,
  **M₀ = V₀ f(W₀)** with f the degree-(R−1) interpolant of **(−1)^j on a window of R integers**
  around the mean of j ~ Bin(Q, (r−1)/2r). Then (i) M₀ only connects u, w whose group sequences
  disagree in < R positions (so each term can be killed at its bad points by Π(1 − T/s) of degree < R),
  and (ii) I − M₀ is supported on the product eigenvectors with j outside the window: those are the
  measurement rows, a fraction ε = Pr[Bin ∉ window] ≤ 2e^{−R²/8Q}. Occurrences are placed in h ≈ M/D
  copies of B (labels balanced by conditional expectations).
* **Where the √ comes from.** Exponent/n ≈ (R/Q)log(Q/R) + τ log D + 1/r with
  R ≈ √(8Q·ln(1/ε)), ε ≈ τ/(r·b), and **Q ≈ log n/log r** because D = r^{2Q} must be ≤ poly(n)
  (balancing needs 2(b+w)D² ≤ M; a larger label space only multiplies the measurement rows). Hence
  R/Q ≈ √(log(1/ε)·log r/log n): the binomial standard deviation √Q over Q ≈ log n points.
  Lower bound inside OpenAI's template: in the product eigenbasis M₀ = V₀·g(Π₁..Π_Q) acts by
  χ(σ)g(σ) (σ ∈ {±1}^Q the swap signs, χ the parity), so rank(I − M₀) = D·μ_p{g ≠ χ}: **g must agree
  exactly with the parity on all but ε of the p-biased cube.** For symmetric g (OpenAI's f(W₀)) an
  alternation argument gives deg ≥ (number of consecutive layer pairs kept) − 1, hence
  R = Ω(√(Q log(1/ε))) [R, sketch: Δg alternates in sign on kept pairs]; for general g this is the
  real probabilistic degree of parity, Θ(√(Q log 1/ε)) on the uniform cube [K], and I expect the same
  for biased p [C]. So **R ≈ √Q is optimal for every M₀ in the commutative swap algebra**; beating it
  needs non-commuting structure (§6, idea 2).
* For general k-CNF: sparsification + Tovey copying gives 2^{o(n)} directly; the sharp bound replaces
  clauses by O(n) parity tests of polylog sparsity (expander/Tanner code + greedy conditional
  expectations with exact counts), lifted by a Beigel–Tarui-type idempotent mod 2^{n+1}, with the
  product truncated *globally* to keep total degree O(n) (Lemma `lem:total-order`).

### 2.2 Engine II (appendix): Boolean tensor contraction in 2^{O(s/√log s)} [P]

Theorem `thm:tensor-contraction`: a bipartite Boolean tensor network with ≤ Cs one-bit wires, max
degree ≤ s^{9/10}, entries in (ℤ/2^{P₀})[V]/(V^ℓ) computable in 2^{O(s^{0.9})}, is contracted in
(s+𝓛)^{O(1)}·2^{O(s/√log s)} time and polynomial space. This is **the same kind of object as
Anthropic's network engine** (s wires ↔ total U; one-bit wires instead of c_{ab}-bit edges). Mechanism per
call (M wires): pack edges into packets of L = 2^a slots with labels in [r]^a (r = 64); deform the
identity wiring by a **2-adic Cauchy kernel** W_xy(T) = C(T)/(C'(0)(T − (y−x))), C(T) = Π_{t∈S}(T−t),
S = {−L..L−1}, so W(0) = I; at a node t of 2-adic valuation i, W(t) is *local* for the grouping by the
i-th label symbol; near t, cross-group entries expand geometrically into **modes**
L_Z = Σ_{y in tile} j^b X_y of **weight b+1** (coefficient divisible by 2^{b+1}); only mode monomials
of total weight < working precision p_t matter (`tensor-mode-budget`); each monomial splits the call
into r children with ≤ M/8 wires. "Tapered Hermite recovery" (multiplicity h(u − i) at valuation i)
keeps p_t = O(M D_t/u), and the number of monomials is
**exp(O(√(K p_t))) with K = 6M/D modes per weight — a K-coloured partition count — = exp(O(M/√u))**,
u ≈ λ/2^d retained valuation levels. At depth d, M ≤ s 8^{−d}, u ≈ λ 2^{−d}, so the exponents decay
like (√2/8)^d and **the root alone sets the rate s/√log s**.

### 2.3 Comparison with Anthropic's engine (the high-priority question)

| | Anthropic (pieces + clique recursion) | OpenAI I (replacement forms) | OpenAI II (tensor contraction) |
|---|---|---|---|
| resource charged | shared bits U (+ node load P ≤ n/K⁷) | Boolean variables N; incidences only via log(M/N) | wires s (one bit each); degree ≤ s^{0.9} |
| saving mechanism | per level: square K, multiply e by ρ; e_ℓ ≈ ρ^ℓ, log K_ℓ ≈ 2^ℓ | one deformation level; Taylor cost R/Q | one deformation level (recursion only for children) |
| source of the √ | ρ = f(2h)/(2f(h)) = 1/√2 with f = log p(E) ≈ c√E (Fock space, Hardy–Ramanujan) | R ≈ √Q: binomial CLT width = parity-agreement degree (Smolensky) | #mode monomials = K-coloured partitions of p: exp(√(Kp)) (Hardy–Ramanujan) |
| why log n inside | depth ≈ log log K levels, each squaring K | Q ≤ log D/log r, label space D ≤ poly(n) | u ≤ log L, packet/label space ≤ s^{1/1000} |
| rate | U/(log U)^{α'}, α' = log₂(1/ρ) = 1/2 | n(log log n)²/√log n | s/√log s |
| what α' > 1/2 needs | pieces with ρ < 1/√2 (sub-√ graded two-order structure) | M₀ beating the parity bound, or Q ≫ log D | mode weights growing superlinearly (sub-√ mode growth) |

**Verdict [R/C].** OpenAI does *not* avoid the √ by a different route; it reaches α = 1/2 by a different
architecture (single level, no per-level ρ) whose bottleneck is again a bosonic √E growth:

* In engine II the modes are exactly an oscillator spectrum (one oscillator per (packet, tile, b), energy
  b+1), so the count is a partition function, the same exp(c√E) that gives Anthropic's ρ = 1/√2. There is
  no √2 "doubling" loss in OpenAI II, but there is also no compounding: the whole saving is one factor
  √u ≈ √log s. The analogue of "β = 1/2 for every local field" (rho-lower-bound.md Prop. 5.1/5.2) is
  2-adic: the mode weights are linear in b because the delta function [y − x = t] restricted to a tile is
  only *locally* analytic in j (Mahler/Amice: locally analytic of a fixed order ⇔ Mahler coefficients with
  valuation growing linearly), so linear weights, hence partition growth, look forced by locality [C].
* In engine I the √ is the CLT/Smolensky √Q, a genuinely different-looking source, but with the same
  √(log n) ceiling because Q ≤ log(poly n). Its constants: rate ≈ 0.5·√(lg Δ·lg λ/λ)·lg λ per variable for
  Ryser (shape-fit in `oai_ryser_rate.out`).
* So the per-level constant question has no answer on OpenAI's side (there is no per-level ρ); the
  "effective" exponent is 1/2 in both of their engines, and OpenAI's own parameters cannot reach
  α' > 1/2 without beating either the parity-agreement bound (engine I) or linear mode weights (engine II).

## 3. Other results: technique triage

The catalogue is overwhelmingly pure mathematics (number theory, geometry, operator algebras, PDE,
…: ~290 of 373 families) with no algorithmic content that touches exact counting; I list them in §1
only. For the TCS/combinatorics families that could plausibly matter I read the catalogue abstracts
(and, where marked, the LaTeX). Summaries are [P] (OpenAI's claims, unverified by me).

| # | result | core technique (as stated) | relevance to us |
|---|---|---|---|
| 378 | ETH false: #k-SAT in 2^{O(n log log n/√log n)}, poly space | §2 (read in full: overview, §4 construction, appendix) | **high** — §2, §4–§6 |
| 107 | ω ≤ 9/4 over ℂ; ω < 2.258 (char 0, most char p); α > 0.465 | new tensor constructions/"staggered extraction" (abstract only) | none: the clique base case e_K ≤ max(ω/9, 5/18) (rate.md §1.4) is already pinned at 5/18 by forming the matrices (ω/9 drops from 0.264 to 0.25); constants only, rate unchanged |
| 130 | exact DFT in O(n (log n)^{1−10⁻¹³}); linear circuits o(n log n) | a **finite tensor saving** (a tensor power A^{⊗b} of one invertible non-monomial matrix with fewer calls than the axis algorithm, monomial maps free) amplified by tensor powers (LaTeX intro read) | conceptual twin of "pieces at fixed λ amplified by the recursion"; for pieces, tensoring multiplies the piece count |I| so the additive loss log|I|/(4λ) stalls the recursion (rate.md §3.1) — low |
| 108 | border determinantal complexity of per_m is Ω(m³) | algebraic-geometry lower bound (abstract) | lower bounds in the det model; does not constrain our network model — none |
| 113 | FPRAS for #PM in general graphs; AOV entropy conjecture | approximate counting (abstract) | approximate, not exact; no transfer to exact 2^{o(n)} — none |
| 114/115 | FPRAS for common polymatroid bases; contingency tables, exact sampling | approximate counting/MCMC | none |
| 120 | max-cardinality matching in (n+m)^{1+o(1)} | (abstract) | none (decision/optimisation) |
| 126 | exponential PSD rank of the PM polytope | lower bound | none |
| 135 | homogeneous ΣΠΣΠΣ lower bound n^{Θ(√n)} for IMM | lower bound; √n from depth-5 homogeneous structure | none for algorithms; style of argument (rank of partial derivatives) is the same family as our barrier.md rank cuts |
| 112 | depth-3 circuits 2^{ω(√n)} for a P language | lower bound | none |
| 138 | Subset Sum in 2^{0.49n} (word RAM) | representation method + filtering/aliases beyond meet-in-the-middle (intro read) | the 2^{n/2} barrier it breaks is a meet-in-the-middle barrier; Ryser's 2^n is not of that type — low |
| 116 | uniform black-box non-commutative PIT | matrix hitting points | the HWY sum-of-squares link (rate.md §2) is about *lower* bounds; this is PIT — none |
| 104 | quasipolynomial mean-payoff/stochastic/parity games | (abstract) | none |
| 103, 105, 106, 102 | L = RL = BPL; 2-to-1 games; 3-colouring hardness; UGC | (abstracts) | none |
| 180 | Barnette's conjecture (cubic bipartite planar 3-connected ⇒ Hamiltonian) | "paired states" structural argument | existence, not counting — none |
| 161/162/170/… | combinatorics (Sidorenko counterexample, Ryser *covering* conjecture, Ramsey) | constructions | none ("BalancedRyser" in `lean/ComparatorChallenges` is the covering conjecture, not the permanent) |

## 4. Transfer analysis

Ratings: **promising** (concrete, checked), **plausible** (worth a look), **low**, **negative** (with reason).

**(a) Engine rate α' > 1/2.** *Low.* Both OpenAI engines sit at α = 1/2 for the same structural reason as
ours (§2.3). Two non-trivial leads remain, both speculative and both *new targets* rather than
reformulations of ρ < 1/√2: (a1) in engine I, an M₀ outside the commutative swap algebra (or a structured
label set) with R = o(√Q), i.e. "identity = (sparse-support, low-swap-distance) + (low rank)" with better
parameters than the parity polynomial; (a2) in engine II, a deformation kernel whose cross-group expansion
has superlinear mode weights. (a2) looks blocked by the Mahler/Amice locality argument of §2.3 [C]; (a1)
is open to me (idea 2 in §6).

**(b) Dense permanent with o(n√log n) shared bits.** *Negative, but the obstruction moves.* Engine I does
not count bits at all: Ryser's formula has only N = n Boolean variables, n linear row factors and total
degree 2n — exactly its input format, and the full pipeline works on it (§5, exact). The cost is in the
measurements: rows ≈ 2rεM with M = nnz(A) + n, so ε ≈ τ n/(r M) and R² ≈ 8Q ln(1/ε) ≈ 8Q ln(M/n).
For a dense matrix ln(M/n) ≈ ln n while Q ≤ log₂n/(4 log₂ r), so R/Q ≈ √(22 log₂ r) > 1: the degree
would exceed the number of points [R, arithmetic]. Inside OpenAI's per-occurrence template this is a real
barrier: for one dense factor f at one point t, the off-group parts of the forms P_{f,v}(t) contain an
identity block on {v : a_v(t) ≠ d_f(t), dist(d_f, a_v) ≥ R}, so ≥ n(1 − 2/r) − deg_G(f) independent
measurements are needed, while group balance forces Σ_v dist(d_f, a_v) ≥ Q n(1 − 2/r); together this
forces r ≤ ~6, i.e. no saving [R, sketch]. A template with *one* replacement form per linear factor
escapes the per-occurrence count, but then A = Σ_{t=1}^{R} λ_t(B_t + K_t) with B_t block-diagonal for
the t-th grouping and rank K_t ≤ τn (Lagrange extrapolation from R of the points), and a dimension count
gives R ≥ r/(1 + 4τr) for generic dense A [R]; the heuristic constraint count (Q·n²(1−1/r) equations
against Rn² unknowns) suggests R ≈ Q [C]. So the dense permanent hits a **matrix-rigidity-type
obstruction** in engine I, the analogue of our "assignment class" bound. Engine II (tensor contraction)
sees Ryser as m wires: 2^{O(m/√log m)}, useless for dense.

**(c) Dense HC counting.** *Negative.* Engine I needs Σ_x Π_f Φ_f with O(n) Boolean variables and total
degree O(n). Ryser has this shape; the HC analogue (Bax/Karp: Σ_X (−1)^{n−|X|}·#closed n-walks in G[X])
is a matrix power, not a product of local factors, and every encoding of the walk uses Θ(n log n) bits
(our assignment-class barrier). I found no product formula for #HC with o(n log n) variables. OpenAI's
own corollary only gives #PM in 2^{o(v+e)}; it says nothing on HC.

**(d) Sparse results.** *Promising for #PM/permanents, nothing for HC/TSP.*
* **Sparse permanents / bipartite #PM.** Ryser through engine I, with b = w = Δ+1 (max degree) and the
  paper's constraints (2(b+w)D² ≤ M, tail ≤ τ/(rb)), gives exponent/n ≈
  (2R/Q)log₂(eQ/R) + 2rε(Δ+1)log₂(2D+1) + 2/r, optimised in `oai_ryser_rate.py`:
  **#PM (or per of an integer matrix with ≤ Δ nonzeros per row and column, poly-bit entries) in
  2^{O(n·√(log Δ·log log n/log n)·log log n)}**, subexponential for log Δ = o(log n/(log log n)³).
  Ours (permanent-attack.md §4) is 2^{O(n log Δ/√log n)}, subexponential only for log Δ = o(√log n);
  OpenAI's corollary (one Boolean variable per edge) is 2^{o(nΔ)}. The new range is
  √log n ≲ log Δ ≲ log n/(log log n)³. Caveats: (i) asymptotic only — with the paper's constants the
  rate is still > 1 (worse than Ryser) at every n in the table up to n = 2^{262144} (for Δ = O(1) it is
  0.69 there, versus 0.23 for our engine's guarantee); (ii) needs max degree, not average (the
  balancing variance is Σ deg² — skewed degrees need branching on heavy columns, as OpenAI do for
  heavy variables); (iii) I verified the identity chain exactly on toys, not the complexity proof.
* **General-graph #PM / hafnian** in the same bound: #PM(G) = [y^{n/2}] Σ_x Π_v(2x_v−1)
  Π_u(1 + y x_u Σ_{w>u, w∼u} x_w) — n variables, total degree 3n, incidences m + 2n
  (`oai_hafnian_product.py`, exact, PASS for 40 random graphs, n ≤ 10).
* **#HC, TSP with exponential weights, the degree-based HC bound:** no transfer (no product formula; the
  HC network already has U ≈ n log Δ bits and engine I on a network costs U/√log U, the same as ours).

## 5. Numerical checks (exact integers/rationals)

* `scripts/oai_ryser_replacement.py` → `oai_ryser_replacement.out`: **the whole engine-I pipeline on
  Ryser's formula**, five configurations (n ≤ 5; (r,Q,R) ∈ {(2,4,2), (3,3,2), (2,5,3)}; densities
  0.5–1.0 including the all-ones 5×5 matrix, per = 120; D = 256…1024 auxiliary labels, 67–189
  measurement eigenvectors). Checks, all PASS: (1) I − M₀ = Σ_exc κ_ψ ψψᵀ (measurement rows span
  I − M₀); (2) H(0) = per(A); (3) deg H ≤ 2n(R−1); (4) separation H(t) = Σ_y Π_g B_{t,g}(y) at every
  t ∈ [Q], computing the forms from measurements + local data only; (5) the Taylor jets H(t+z) mod z^J
  from the restricted sums Z_{t,E,U} (each by separation); (6) Hermite recovery of per(A) from the jets;
  plus a non-triviality check (23–60 non-zero cross-group coefficients; H(1) ∉ {per}, e.g. −426 for the
  all-ones case) and a control (with J−1 jets the system is underdetermined). This confirms that dense,
  many-variable linear factors fit the engine *as an identity*; the obstruction of §4(b) is purely in the
  cost parameters.
* `scripts/oai_ryser_rate.py` → `oai_ryser_rate.out`: optimised exponent/n for Ryser through engine I
  (exact binomial tails in log space, paper's constraints) against our engine's guarantee for the
  bounded-degree profile network. At log₂Δ = √(log₂ n) the OpenAI route decreases
  (2.99, 2.81, 2.42, 2.03, 1.68 for log₂ n = 2¹⁰…2¹⁸) while ours stays ≈ 40; the shape fit
  rate/(√(lg Δ·lg lg n/lg n)·lg lg n) is stable at 0.53 → 0.49 up to log₂ n = 2²⁰. For Δ = O(1) ours is
  better at all listed sizes. All values > 1 at practical n: this is an asymptotic statement.
* `scripts/oai_hafnian_product.py` → `.out`: the general-graph product formula for #PM, 40 random graphs,
  PASS.

## 6. Ranked ideas worth a full attack

1. **Ryser (and the hafnian product) through OpenAI's engine I: sparse #PM/permanent in
   2^{O(n√(log Δ·log log n/log n)·log log n)}.** *Promising, near-mechanical.* What is needed: restate
   OpenAI's Proposition `prop:general-count` + Lemma `lem:layout` + Lemma `lem:incidence-parameters` for
   factors of X-degree 1 or 2 with scope ≤ Δ+1 and occurrence ≤ Δ+1 (their §4 already allows arbitrary
   scope w and occurrence b; only the parameter lemma assumes b, w ≤ polylog n — redo it with
   ε = τ/(r(Δ+1)), R = Θ(√(Q log(rΔ/τ)))), and bit-complexity for integer entries. Lean: their
   `SubexponentialSAT` development is general in the factor polynomials (to be confirmed in
   `OAI/Algorithms/SubexponentialSAT`). This strictly improves our degree-based #PM bound for
   √log n ≲ log Δ ≲ log n/(log log n)³ and extends to non-bipartite graphs. It does **not** touch HC.
2. **Beat the parity barrier in engine I (non-commutative M₀ / structured labels).** *Speculative,
   high payoff.* The rate of engine I is R/Q with R the least degree such that some
   M₀ ∈ ℚ^{B×B}, supported on pairs whose group sequences differ in < R places, has rank(I − M₀) ≤ εD.
   Within the commutative swap algebra this is the real probabilistic degree of parity, Θ(√(Q log 1/ε)),
   hence α = 1/2. Nothing I know forbids a non-commuting M₀ (or a label set that is a code rather than all
   of ([r]²)^Q, so that exceptional directions restricted to occupied labels have low rank) with
   R = Q^{1/2−δ}; that would give engine-I rate n/(log n)^{1/2+δ}, i.e. α' > 1/2 for #k-SAT by a route
   independent of ρ. First step: the clean partial-matrix-completion question "min rank of L agreeing with
   I_D outside the allowed support", small Q exhaustive LP/rank search. Note the warning sign: the same
   √ appears in three different guises (Fock growth twice, CLT once).
3. **Mode-weight engineering in engine II as an alternative "Fock space" for pieces.** *Low.* The
   tensor-contraction count exp(√(K p)) would become exp(K^{k/(k+1)} p^{1/(k+1)}) if mode weights grew
   like b^k; the delta-kernel locality seems to force linear weights (Mahler/Amice), the 2-adic mirror of
   rho-lower-bound.md Prop. 5.1. Worth one afternoon to make that argument rigorous: if it holds, it is a
   second, independent proof that "local deformations ⇒ partition growth ⇒ α = 1/2", which would
   strengthen the barrier write-up rather than the algorithm.
