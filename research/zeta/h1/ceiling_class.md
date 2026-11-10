# What the 0.68185 ceiling covers, and a class of certificates outside it   [h1]

Scripts: `h1/ceiling_npoint.py` (outputs `h1/np_N_level.out`). Builds on h3/T1_extremal.md §5–6 (periodic model, column generation)
and h4/T2 (Prop 2). Tags as in TEAM.md.

## 1. The class covered by the PairCeiling theorem — precise statement [K, from the Lean source]
`Zeta23/PairCeiling/Ceiling.lean`, `ceiling_of_valid_at` (and `Stability.lean`, `CeilingLaw256.lean`):
let `r ∈ C¹[0,1]`, `r'` continuous, differentiable off a countable set with integrable `r''`; let a configuration (law) have
form-factor atoms `s_j` at `j/N`, `1 ≤ j ≤ N`, and simple fraction `p₁`. **If** `c₀ + Σ_{j=1}^{N} s_j r(j/N) ≤ p₁` **then**
`c₀ + ∫₀¹ r(x) x dx ≤ p₁ + |r(1)||D(1)| + |r'(1)||E(1)| + sup|E|·∫₀¹|r''|`, `D = C − x²/2`, `E = ∫D`.
For the explicit N = 256 law: `p₁ = 0.6818287`, `|D(1)| ≤ 0.824`, `sup|E| ≤ 2.55·10⁻⁶` (given `EnclOK`).
So the theorem bounds the *value* `c₀ + ∫₀¹ r(x)x dx` of every certificate that
 (a) is **linear in the two-point form factor** restricted to frequencies `0 < α ≤ 1` (the δ-mass at 0 is inside `c₀`),
 (b) has a `C¹` (piecewise `C²`) multiplier `r`, with `r(1) = 0` or the edge penalty `0.824|r(1)|`,
 (c) is valid — as an inequality between numbers — on the on-line marked configurations (marks 1, 2) that make up the law
     (averaging over the law is the one step done outside Lean).
Nothing about Gram structure, positivity of `r` or of `r̂`, windows, or rank–trace is assumed: **non-PD kernels, signed `r`, and
certificates proved by any method are covered**, provided they are of type (a)–(c).

## 2. What reduces to this class [R]
1. *Nonlinear functions of the two-point data.* Let `p = Φ(F|_{(0,1]})` be any functional, valid configuration-wise
   (`Φ(F_conf) ≤ s₁(conf)/N(conf)`) and continuous for the topology in which the stability inequality holds (testing against
   `C²` multipliers). Realise the law as a single configuration by concatenating long blocks, block type `c` occupying a fraction
   `w_c` of the height: the two-point form factor of the concatenation is `Σ w_c F_c + o(1)` at every fixed resolution (cross-block
   pairs have relative weight O(1/block length)), and its simple fraction is `Σ w_c p₁(c)`. Hence `Φ(F_law) ≤ 0.68183`: the
   ceiling holds for **all** continuous functionals of bandwidth-one two-point data, not only linear ones (Cauchy–Schwarz-type
   or Christoffel-type certificates built from `tr G̃`, `tr G̃²` included).
2. *Several compressions at once.* Let `G_a = Σ_ρ m_ρ v^a_ρ (v^a_ρ)^T` be compressions with windows `φ_a` (any supports whose
   pairwise products have length ≤ L, same grid). All are pull-backs of the *same* form `M = ⊕_on m ⊕_pairs [[0,m],[m,0]]` on
   "zero space" under maps `V_a`, and by Poisson–Gabor `v^a_ρ·v^b_{ρ'} = (aL²)·κ_{ab}(γ_ρ−γ_{ρ'})` with `κ_{ab} ∝ \widehat{φ_aφ_b}`.
   Therefore `tr(G_aG_b) = Σ_{ρ,ρ'} m m' κ_{ab}(γ−γ')²`: every mixed quadratic trace is the Hilbert–Schmidt norm of the single
   compression with window `φ_aφ_b`. Stacking (`V = (c_aV_a)_a`, block matrix `[G_{ab}]`) has kernel `Σ c_a²κ_{aa}` (h3 §1). So
   "Sylvester inertia in more than one compression simultaneously" produces, at the quadratic level, exactly the data
   `{Σ κ²: κ = ψ̂, ψ ≥ 0, |supp ψ| ≤ 1}` ⊂ linear two-point data ⇒ ceiling 0.68185 applies. (By polarisation these span all
   of `F|_{[−1,1]}`, so the *information* is the full unconditional form factor, as the lead suggested; the ceiling is the ceiling
   for that information.)
3. *`F ≥ 0` beyond `|α| = 1`* (CGdL class). Not literally in the class (multiplier nonzero beyond 1), but `F ≥ 0` holds for
   every conjugation-symmetric configuration (method.md Prop 2.1(a), h4 Prop 2), so it is not extra information about ζ, and such
   certificates are invalid for deep off-line pairs. Under RH their ceiling is a different LP (not addressed by the Lean theorem).
4. *Off-line sensitive two-point data* (bilinear vs sesquilinear sums, Aryan's odd companion). The ceiling law consists of
   on-line configurations (simple + double), on which all such statistics coincide with the RH ones; they cannot lower the ceiling
   unless they are of a different correlation order.

## 3. What is outside the class
(i) **n-point data, n ≥ 3, in the Rudnick–Sarnak range** `Σ|ξ_j| < 2` — unconditional for complex zeros (RS Thm 1.1; they state
    explicitly that RH is not needed for the smoothed sums). The ceiling law is only constrained through its two-point function.
(ii) fine-resolution / long-range two-point data (`r` rough on the scale of the law's period): these exist unconditionally
    (the whole matrix `G̃+Ẽ` is determined by the primes ≤ T/2π, [AF] (2.9)), but [C] they only add O(1/log²T) arithmetic
    corrections at macroscopic distances and no evaluable higher moment.
(iii) data about other functions (ξ′, families) — different problem.
So the only candidate for breaking 0.68185 with unconditional "bandwidth-one-type" data about ζ itself is (i).

## 4. Experiment: the ceiling with 3- and 4-point data added [N]
Periodic model of h3/§6 and of `LawN256.lean`: N-periodic configurations, total multiplicity N, marks 1 (simple) and 2 (double),
`S(l) = Σ_j m_j e(l t_j/N)`. Rows imposed on the law (mirror-symmetrised, so real parts only), the right sides being the
Diaconis–Shahshahani moments of CUE(N), i.e. the model form of Montgomery (2-pt) and Rudnick–Sarnak (3-, 4-pt):

    2pt:  E|S(l)|² = l,                         1 ≤ l ≤ N−1
    3pt:  E Re[S(a)S(b)conj S(a+b)] = 0,        1 ≤ a ≤ b, a+b ≤ N−1
    4pt:  E|S(a)|²|S(b)|² = ab(1+δ_{ab}),       a+b ≤ N−1;   E Re[S(a)S(b)conj(S(c)S(d))] = 0, a+b=c+d ≤ N−1, {a,b}≠{c,d}

Objective: minimise E[#simple]/N. Master LP over columns (4000 CUE(N) samples + random marked configurations + priced columns),
pricing by multistart L-BFGS. Every reported value is the value of an exactly feasible law (slack 0), hence a rigorous-up-to-LP-
tolerance **upper bound** for every certificate using those rows; that the true minimum is not lower rests on the heuristic pricing.

| N | 2-pt only | + 3-pt | + 3-pt + 4-pt |
|---|---|---|---|
| 8  | 0.6860 (h3: 0.685996) | **0.7088** (converged; second seed with 3× more pricing tries: 0.708803) | **0.7119** (converged) |
| 12 | 0.6839 (h3: 0.683689) | ≤ 0.7051 (last line: `it 284 obj 0.705103 slack 0.00e+00 ncols`; drift < 1e-4 per 30 iterations) | not converged (last line: `it  61 obj 0.749792 slack 0.00e+00 ncols`) |
| 16 | 0.6830 (h3) | not converged, upper bound only (last line: `it 119 obj 0.708773 slack 0.00e+00 ncols`) | — |
| 256 | 0.68183 (A–F) | — | — |

Reading [N/C]: adding the unconditional three-point data **raises the model ceiling by about 0.02** (0.686 → 0.709 at N = 8,
0.684 → ≈0.705 at N = 12; N = 16 unconverged, so the large-N limit of the gain is NOT established — it could shrink); the four-point data add only ≈0.003 at N = 8. So
* the 0.68185 ceiling is a ceiling for two-point bandwidth-one data only, not for all unconditional correlation data;
* a certificate using the RS three-point function could in principle certify ≈ 0.70 (if the trend persists in N — to be confirmed
  at N = 16, 24 with a faster pricer, and the finite-N offset is the same ≈ +0.002–0.004 as for the two-point ceiling);
* even with 4-point data the model ceiling stays far below 1: the Rudnick–Sarnak range is still very restrictive.
Optimal laws put weight on all compositions (k₁,k₂) from (8,0) to (0,4) (N = 8), unlike the two-point law (almost only (8,2)
at N = 12): the bispectrum rows force a compensation of the self-term `Σ m_j³`.

## 5. What a proof would need [C]
A *cubic configuration inequality*: for conjugation-symmetric configurations,
`s₁ ≥ c₀N − Σ_{ρ,ρ'} m m' K₂(γ−γ') − Σ_{ρ,ρ',ρ''} m m' m'' K₃(γ−γ', γ'−γ'')`, `K̂₂` supported in [−1,1], `K̂₃` in the hexagon
`|ξ₁|+|ξ₂|+|ξ₁+ξ₂| < 2`, with value `> 0.68185` against the GUE data. Matrix candidates: `tr(G_aG_bG_c) = Σ κ_{ab}κ_{bc}κ_{ca}`
(cyclic product of PD kernels with windows `φ_aφ_b`, total support < 2) — unconditional by RS; a lemma of the type
"`rank P₁ ≥ α tr − β‖·‖² + γ tr(G_aG_bG_c) − (charges)`" would be the cubic analogue of Lemma 3.2. Two warnings:
(1) [R] a single matrix at bandwidth λ has rank ≤ λN, so the cubic term must be used *together with* the bandwidth-one quadratic
term (mixed windows), never as `tr G_{2/3}³` alone; (2) h2 reports negative evidence for one half-bandwidth cubic attempt
(Tyagi). The dual solution of the LP above (the multipliers of the 3-pt rows) is the natural guide for `K₃`; extracting it at
N = 12–16 and testing its validity on off-line pairs (as h3 did for the two-point dual) is the next experiment.
