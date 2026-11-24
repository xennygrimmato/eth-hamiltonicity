# Next big theorems: ten candidates (24 Nov 2026)

Idea generation only. Nothing here is proved or computed; every "why now" is a heuristic argument. Tags:
**[K]** known from a source, **[W]** seen in a web search today (unrefereed unless stated), **[C]** my conjecture or
sketch. Scores are 1–5: A = ambition, T = tractability for us.

## 0. What is already claimed (checked today, so we do not redo it)

| Topic | Status found today | Consequence for this list |
|---|---|---|
| RH + GRH for Dirichlet L-functions | Alpöge + Claude, 20 Nov, Lean, checked by Rubinstein, Sutherland, Lean FRO [W]. Dedekind, Hecke and automorphic L-functions are **not** covered (Sutherland's page, Wikipedia) [W]. Method per Wikipedia: Stepanov-style, theta correspondence as "multiplicity", Arakelov sizes. Rubinstein's page gives a guide reducing RH to a main inequality (M) and 13 hypotheses. | Anything needing GRH for non-abelian fields is still open (idea 3). |
| Quasi-RH (Re s > 11/12) and no Landau–Siegel zeros | OpenAI, Oct; Banks and Kerr rewrites with explicit constants [W]. | Superseded by GRH, but gives a second, analytic route. |
| Artin's primitive root conjecture | Existence and positive lower density claimed unconditionally: OpenAI paper 029 (≫ x/log² x), Bhargava 14 Oct (≫ x/log x), Vojdanovski Nov (simultaneous bases, Lean) [W]. **The asymptotic with Artin's constant is not claimed.** Hooley needs GRH for Kummer fields Q(ζ_q, a^{1/q}), which are non-abelian, so Dirichlet GRH does not give it [K]. | Not "now a theorem via Hooley". Folded into idea 3. |
| ω | OpenAI: ω_ℂ ≤ 9/4 through spectral points ("tensor characters"), Lean; extended to all fields and to ℤ by others (2611.09716, 2610.28627, 2611.04175) [W]. Our `engine3-literature.md` notes SDP relaxations stall at 9/4 on the triangle. | The open targets are ω < 9/4 and ω = 2 (idea 4). |
| VP ≠ VNP | Anthropic 24 Nov (exponent 4/3, ineffective m₀, dichotomy undecided); OpenAI competing proof with 5/4 [W via c2]. No follow-up on the dichotomy, on exponential bounds, or on ω found. | Ideas 1, 4, 7. |
| Exact π(N), prime finding in N^{o(1)} | Ni, 15 Nov. No follow-up found on twin-prime or Goldbach counts, M(x), or ζ(½+it) [W]. | Ideas 2, 5. |
| Factorials | Zhang 2610.28338: some multiple m·k! has τ ≤ exp(O((log k)^{2/3}(loglog k)^{1/3})) [W]. Bürgisser 2009 goes "permanent easy ⇒ n! easy", so VP ≠ VNP does **not** give hardness of n! [K, checked]. | Idea 9 stays hard. |
| Idoneal numbers | Still listed as open (65, 66 or 67) [W]. Weinberger: complete under GRH for real Dirichlet characters [K]. | Idea 6. |

## 1. Decide the flat/contracting dichotomy: effective VP ≠ VNP with exponent 2

- **Statement.** Over ℂ (then every field), prove that the contracting hypothesis holds, or that it fails. Equivalent
  form from c1: decide whether the rank metric ρ_μ(a,b) = √rk(a−b) on Mat_μ(F₂) is a price. If contracting:
  PERM_m needs 2^{c(log m)²/loglog m} gates (Thm K.7) and, with explicit μ and s, an effective m₀. If flat for all μ:
  the engine's levels are capped (b2 flat floor ρ ≥ 1/√p), which closes most of engine-3's "open door".
- **Why now.** We already have the reduction to one explicit finite object (c1 §1), the proof that curvature alone
  cannot decide it (c1 §2–4), and the win–win (b2 Prop. 4: an engine trade below the flat floor proves contracting).
  Nobody else has these. OpenAI's 5/4 proof may avoid the dichotomy; reading it could give the missing identity.
- **First step.** μ = 2: 16 parties. Use c1's cover characterisation (ρ_μ is a price iff no ρ-cheaper family of graph
  tensors asymptotically covers the complete network). Search for a covering identity at bond dimension 2 and 4 on the
  quadrilateral a, a+W, a+W+W′, a+W′ with W, W′ of rank 1 (the smallest non-Euclidean-rectangle test). In parallel,
  test the three-merge Δ₃ trade (b2: ρ < 1/√3 there proves contracting).
- **Main risk.** Both directions need new tensor identities or new spectral points; all explicit points are
  partition-stars (c1 §3). The answer may differ by field.
- **Scores.** A 4, T 3.

## 2. Exact twin-prime and Goldbach counts in N^{o(1)}

- **Statement.** π₂(N) = #{p ≤ N : p+2 prime}, the Goldbach count r(N) = #{p+q = N}, and the count of any fixed
  admissible prime constellation below N, are computable deterministically in 2^{O(b/√log b)}, b = log N. Corollaries:
  a deterministic N^{o(1)} test of Goldbach for a given N, with the decomposition found by binary search on prefix
  counts; exact π(N; q, a).
- **Why now.** No algorithm faster than sieving (N^{1−o(1)}) is known for π₂(N): the Meissel–Lehmer and
  Lagarias–Odlyzko methods do not handle a product of two prime indicators [K]. Ni's indicator
  1_P(n) = −μ(n)Λ(n)/log n is a multiplicity in one network with O(b) shared bits. A product 1_P(n)·1_P(n+2) is two
  copies sharing only n, so the shared bits stay O(b) [C]. Our library is the one Ni built on.
- **First step.** Write the doubled network (about 150 variables) and redo Ni's error budget: each indicator is a
  bounded approximate value for every n, composite n included, so the product error per n stays below 2^{−b−2} with
  M = O(b) quadrature nodes. Check on N ≤ 10⁶ numerically, then state it in Lean on top of Ni's v0.1.
- **Main risk.** Ni's result is unreproduced by us. The approximations for composite n might not be uniformly bounded,
  in which case cross terms need care. It is an algorithm, not a proof of the twin prime conjecture; some will call
  it a corollary.
- **Scores.** A 3, T 4.

## 3. ERH: RH for Dedekind zeta functions (GRH for Hecke L-functions)

- **Statement.** Extend the Alpöge–Claude theorem from Dirichlet characters over ℚ to Hecke characters of number
  fields. A decisive first case: class-group and ray-class characters of quadratic fields and of Q(ζ_q), i.e.
  dihedral and monomial L-functions.
- **Why now.** The method (per Wikipedia) runs through the theta correspondence, and Hecke characters of quadratic
  fields are exactly the L-functions of theta series, so they sit one step along the same chain [C]. Alpöge says the
  proof can be "massively simplified"; the 17 M-line archive is machine-readable and an AI teardown is under way.
  By Aramata–Brauer, RH for ζ_L with L Galois gives it for all subfields [K].
- **What it unlocks [K].** Hooley's asymptotic for Artin's conjecture (only lower bounds are claimed today);
  Koiran's "Hilbert's Nullstellensatz ∈ AM" and Bürgisser's VP_ℂ = VNP_ℂ ⇒ NC/poly = PH/poly without hypothesis;
  Bach's bound for class-group generators, hence unconditional subexponential class groups and regulators;
  effective Chebotarev (Lagarias–Odlyzko, Serre); Weinberger's Euclidean rings; Ono–Soundararajan needs GL₂ too.
- **First step.** In Rubinstein's guide, locate which of the 13 hypotheses use that the base field is ℚ, and which
  use that the character is of GL₁. Restate (M) for an imaginary quadratic K and list what fails.
- **Main risk.** The Arakelov "size" comparison may use special features of ℚ. Nobody understands the proof yet, and
  Anthropic's own team is the obvious competitor.
- **Scores.** A 5, T 2.

## 4. ω below 9/4, aiming at ω = 2, by the geometry of prices

- **Statement.** ω = sup over spectral points φ of the perimeter d_φ(1,2) + d_φ(2,3) + d_φ(1,3) of the three-party
  wire metric, since ⟨n,n,n⟩ is the product of three wires and φ ≤ asymptotic rank with equality at the maximum
  (Strassen duality) [K + C]. Spectral metrics form a convex set (φ^a ψ^{1−a} is again a spectral point by Hölder)
  [C]. So ω/3 is the side of the largest equilateral triangle among *normalised* spectral metrics. Target: a
  universal inequality on normalised prices that forces perimeter ≤ 2 + ε.
- **Why now.** The VP ≠ VNP paper is the first to prove inequalities valid for **all** spectral points (crossing
  identity ⇒ CAT(0)). An upper bound on ω proved this way is dual and needs no algorithm, so the
  Coppersmith–Winograd-type barriers for degeneration methods do not apply [C]. OpenAI's 9/4 proof also uses
  spectral points, so the two releases can be combined.
- **First step.** Re-derive 9/4 as a price inequality on three parties plus hubs (compare the SDP that gives 9/4 on
  the triangle in `engine3-literature.md`). Then add the crossing inequality on four parties with one shared hub and
  see whether the optimum of the enlarged programme drops below 9/4. Also test a win–win: does "contracting at μ"
  bound the perimeter, or does a normalised flat hypothesis give ω > 2?
- **Main risk.** The curvature inequalities are scale-free, and ω lives in the normalisation d ≤ 1, which the paper
  never uses. Any three-point metric is a tree metric, so all information must come from auxiliary parties.
- **Scores.** A 5, T 2.

## 5. ζ(½+it) and L(½+it, χ) in t^{o(1)}; the n-th zero, N(T) and M(x) exactly

- **Statement.** ζ(½+it) to poly(log t) bits in time 2^{O(b/√log b)}, b = log t; hence N(T) exactly, the n-th zero to
  any fixed precision, and (RH now being a theorem) certified zero data at any height. Also the Mertens function
  M(x) and L(1, χ_d) to rounding precision in x^{o(1)}, d^{o(1)}.
- **Why now.** The best rigorous bound is Hiary's t^{4/13+o(1)} [K]. The Riemann–Siegel main sum
  Σ_{n ≤ √(t/2π)} n^{−½−it} has O(b) shared bits (n), and Ni's method already handles analytic weights by Cauchy-kernel
  quadrature plus integer quotients. M(x) is Ni's own Ramanujan-sum primitive without the Λ factor [C].
- **First step.** Do M(x) first (one afternoon if Ni's network is as described). Then build the phase
  e(t·log n / 2π): approximate log n to 2b bits as a quotient, multiply by t inside the constraint system, reduce
  mod 1 by a unique-witness floor, and apply the rational-phase kernel. Budget the error for a non-integer answer
  (no final rounding rescue: aim at absolute error 2^{−b}).
- **Main risk.** Composition of approximations (log, then a b-bit multiplication, then e(·)) may need t-dependent
  node counts and push shared bits above O(b). The Riemann–Siegel remainder must be handled to the same precision.
- **Scores.** A 3, T 4.

## 6. Euler's idoneal numbers and the deterministic harvest from Dirichlet GRH

- **Statement.** (a) Euler's list of 65 idoneal numbers is complete (open since 1778; Gauss's one-class-per-genus
  problem). (b) Unconditional deterministic polynomial-time square roots mod p (least non-residue < 2 ln² p, Bach).
  (c) Deterministic primitive root mod p in p^{o(1)}: factor p−1 with the engine, then test g ≤ (log p)^{O(1)}
  (Shoup). The best unconditional bound is p^{1/4+ε} [K]. (d) Miller's test with our constant 0.29 ln² n.
- **Why now.** Each needs GRH only for Dirichlet characters, which is the part that is Lean-checked [K]. (c) is the
  one place where toolkit items 1 and 2 are both needed. We already have the Miller–Rabin constant (`mr2/`).
- **First step.** For (a): take Weinberger's explicit GRH bound, close the finite range by a certified computation,
  and state it in Lean against the released GRH theorem. Check the statement name in Alpöge's archive first.
- **Main risk.** Low mathematical risk, high risk of being scooped within days. (a) needs a Lean-checkable finite
  search up to about 10¹¹ unless the explicit bound can be sharpened.
- **Scores.** A 3, T 4.

## 7. An exponential lower bound for the permanent (VNP ⊄ VQP as the first step)

- **Statement.** PERM_m needs 2^{m^ε} gates. First step: more than 2^{(log m)^C} for every C.
- **Why now.** The price method is the first technique that works for general circuits. Its cap is structural: the
  networks f_{k,ℓ} have only k ≈ (log m)^{2/3} parties, and a k-party tensor of block size n has rank ≤ n^{k/2}, so
  log L ≤ (log m)² at best; b1 shows the Euclidean hub method stops at ℓk^{3/2} [R in b1].
- **First step.** Replace the complete wire network by a bounded-degree expander on k = m^ε parties with wires of
  constant size ℓ, so block sizes are 2^{3ℓ} and the cut ranks are 2^{Ω(kℓ)}. Redo (2.4): the 2^k balanced sets cost k
  bits, the same order as the length, so the question is a constant. Work out which price is needed: b1's discrepancy
  argument says Euclidean prices fail; tree and median (ℓ₁-type CAT(0) cube complex) metrics are the candidates, and
  trees appear in the contracting case (thm_tree).
- **Main risk.** lem_balanced with 2^k pieces may eat the whole gain for sparse networks. Needed prices may not
  exist. Very likely needs an idea beyond the paper.
- **Scores.** A 5, T 1–2.

## 8. Break the 1/√log rate: 3-SAT in 2^{O(n/log n)}, then the Satisfiability Hypothesis

- **Statement.** #3-SAT in 2^{O(n/log n)} (ρ = 1/2 pieces), giving E^NP ⊄ SIZE(εn log n) by our quantitative Williams
  argument; ultimately 2^{n^{1−ε}}, giving E^NP ⊄ SIZE(n^{1+ε}) and beating Ryser and Held–Karp.
- **Why now.** engine3-STATUS reduces the question to three or more merges; b2 shows that in the flat case levels
  with p ≤ 4 fully crossing merges cannot do it, so the search space is now: p ≥ 5, edges internal to merges, or
  the contracting case. That is a much smaller target than three weeks ago.
- **First step.** A five-merge configuration with every edge crossing all merges, checked against the 1/√p floor;
  ALS search at N₀ = 8 where finite certificates stop refuting (STATUS item 2).
- **Main risk.** The dichotomy (idea 1) may close the door entirely. Searches so far found nothing.
- **Scores.** A 4 (n log n) to 5, T 2.

## 9. P_ℂ ≠ NP_ℂ through factorials: "no accelerator for products"

- **Statement.** No nonzero multiple of k! has straight-line programs of length (log k)^{O(1)} (Shub–Smale: this
  gives P_ℂ ≠ NP_ℂ in the Blum–Shub–Smale model) [K].
- **Why now.** The contracting-case argument refutes "accelerators" (programs that sum v^H steps in v^{H−16} steps)
  by diagonalisation. A short program for m·k! is an accelerator for a product over k steps. Also the RH method is
  "divisibility ≤ size", which is the natural shape of a lower bound for integers divisible by every prime ≤ k.
  Zhang's subexponential upper bound shows the problem is alive.
- **First step.** Formulate a product accelerator in the paper's Section 2.4 language and see where thm_noacc uses
  additivity. Check whether Bürgisser's counting-hierarchy argument can be reversed in the contracting case.
- **Main risk.** The known implication goes the wrong way (permanent easy ⇒ factorials easy). Integers of size
  2^{2^ℓ} defeat naive size arguments. Speculative.
- **Scores.** A 5, T 1.

## 10. All zeros of ζ are simple (or a proportion above the 19/27 line)

- **Statement.** Every nontrivial zero of ζ is simple; first step, more than 19/27 of them (Bui–Heath-Brown under RH,
  now unconditional) and above the bandwidth-one ceiling 0.6819 of our `zeta/` notes.
- **Why now.** The new proof is Stepanov-like: it controls vanishing multiplicity of an auxiliary object. A method
  whose currency is multiplicity may bound the multiplicity of zeros directly [C]. With RH as a theorem, all
  RH-conditional pair-correlation results (support 1) become unconditional, and our `zeta/` framework can use them.
- **First step.** Port the RH-conditional inputs into the `zeta/h5` Lean map and recompute the certified proportion.
  Ask of Rubinstein's guide: does inequality (M) change if a zero is double?
- **Main risk.** The multiplicity in Stepanov's method is not the multiplicity of zeros of ζ; the analogy may be
  empty. The proportion game is crowded.
- **Scores.** A 4, T 2 (proportion: A 2, T 4).

## Ranking

| Rank | Idea | A | T | Why this place |
|---|---|---|---|---|
| 1 | 1. Decide the dichotomy | 4 | 3 | Our unique position; settles effectivity, the exponent, and the engine's fate |
| 2 | 2. Twin-prime / Goldbach counts in N^{o(1)} | 3 | 4 | Fast, Lean-ready, a headline people understand |
| 3 | 3. ERH for Dedekind / Hecke | 5 | 2 | Largest downstream list; first case is one theta lift away |
| 4 | 4. ω < 9/4 by prices | 5 | 2 | Highest variance; dual method avoids known barriers |
| 5 | 5. ζ(½+it) in t^{o(1)}, M(x) | 3 | 4 | Sibling of 2; M(x) is nearly free |
| 6 | 6. Idoneal numbers + deterministic harvest | 3 | 4 | Easy but will be scooped fast |
| 7 | 8. Rate 1/log, Satisfiability Hypothesis | 4–5 | 2 | Depends on 1 |
| 8 | 7. Exponential permanent bound | 5 | 1–2 | Needs a new network and new prices |
| 9 | 10. Simple zeros | 4 | 2 | Analogy unproven |
| 10 | 9. P_ℂ ≠ NP_ℂ | 5 | 1 | Speculative |

**Top three: 1, 2, 3.** Do 2 this week (with M(x) from 5 as a warm-up), keep 1 as the main line, and open 3 by
reading Rubinstein's guide for the dihedral case. Idea 4 is the one to pick if we want a single high-risk bet.

## Sources consulted today

- Rubinstein, verification page: https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/
- Wikipedia, "Alpöge's proof of the Riemann hypothesis"; "Artin's conjecture on primitive roots"; "Idoneal number"
- Tracker records: kingy.ai quasi-RH / Landau–Siegel; matrix multiplication 9/4
- arXiv 2611.09716, 2610.28627, 2611.04175 (9/4 expositions); 2610.28338 (factorial multiples); 2610.17090 (survey of
  OpenAI's release); Bürgisser, ECCC TR06-113
- Local: `vpvnp/{b1,b2,c1,c2}/notebook.md`, `engine3-STATUS.md`, `primes-rh/NI-2611.md`, `circuit-lower-bounds.md`,
  `zeta/novelty.md`, the VP ≠ VNP paper text
