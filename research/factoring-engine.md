# Factoring on the counting engines: RR 2610.00600, Shunia 2610.00711, and our route

Sources (untrusted, read only): `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/factoring-lit/`
(`rr/rr.tex`, `sh/sh.tex`, both `*.abs.json`). Akshima et al., *A Subexponential Time Algorithm for
Elliptic Curve Discrete Logarithm*, v0.2, 29 Oct 2026 (github.com/bochum-crypto/subexponential-ecdl,
PDF read through a text extractor; cited below as [AK]). Line numbers refer to the `.tex` files.

## 0. Verdict in five lines

1. **RR** proves `∃ M, ∀ k ≥ 1, ∃ C, time ≤ C·2^{n/k}` for `Nat.minFac` in Lean, on **Anthropic's network engine**
   (re-proved: Defs 1–3 and 5, Lemma 1, Lemma 2, Prop 3, "e* = 0"). It uses the ε-route with no counted rate, so `C_k`
   is not controlled. Full factorisation is "not in Lean".
2. **Shunia** gives a correct one-page composition, *conditional* on two unrefereed preprints: OpenAI Thm D.1
   (the Boolean tensor-contraction bound) and [AK] Thm 3 (the multiplication BTN). It has no Lean proof.
3. **The "linear-size encoding" is real, but it is not a CNF.** It is a Boolean tensor network with
   **< 1100(d+1) edges and vertices of degree < 136(d+1)^{3/4}**, each vertex checking an arbitrary
   polynomial-time predicate. It is one level of Schönhage–Strassen over Z/(2^J+1), with J ≈ 16√d, and a
   four-step (√·√) DFT. Twiddles are powers of 2, so they are free shifts. Canonical residues make it
   parsimonious. I re-derived the parameters (below) and they check out. For bounded-width CNFs / circuits,
   no O(n) encoding is known; the best is O(n log n). **Via our Tseitin/#3-SAT clause route the rate would be
   2^{O(n log n/√log n)} = 2^{O(n√log n)}: useless, worse than N^{1/5}.**
4. **The honest best rate is 2^{O(n/√log n)} = exp(O(log N/√log log N)).** It can be machine-checked **on our bridge**,
   because Anthropic's `Net g` already allows big nodes: node settings of length P with poly-time W, and cost
   2^{e(U+gP/K)+2gP/K}. Put the SS vertices into g ≤ n^{1/5} clusters of n^{4/5} bits. Then U, gP = O(n), and the
   counted route (`CountedRoute.onTheCountedRecursion` + `groupingExplicit`, the `Theorem2.lean` template)
   gives 2^{C n/√log n}. This would prove RR's own Lean proposition `SqrtLogLogConjecture` unconditionally.
5. **Beyond factoring:** the pattern "O(n) unknown bits + O(1) multiplications/comparisons" gives new
   deterministic x^{o(1)} results (§4). Three of them look new and cheap: deterministic square roots / least
   non-residue / fixed-degree root finding mod p; exact Dirichlet-divisor, Σσ and Gauss-circle sums in x^{o(1)};
   and the class number h(D) in |D|^{o(1)}. Discrete log, knapsack, SVP and the permanent are useless (§4).

## 1. Rudich–Rousseau, hexagon:2610.00600 (29 Oct 2026)

**Statement (Lean, verbatim from rr.tex l.155–177; `Challenge.lean`, Lean v4.35.0, Mathlib only):**
```lean
def factor : ℕ → ℕ := Nat.minFac
abbrev FactoringMachine := TM2ComputableInTime encodeNat encodeNat factor
def FactoringMachine.FiniteAlphabets (M : FactoringMachine) : Prop := ∀ k, Finite (M.tm.Γ k)
def FactorsWithin (M : FactoringMachine) (T : ℕ → ℕ) : Prop := M.FiniteAlphabets ∧ ∀ n, M.time n ≤ T n
def FactoringInTime (T : ℕ → ℕ) : Prop := ∃ M : FactoringMachine, FactorsWithin M T
theorem subexponentialRate :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, FactorsWithin M (fun n => C * 2 ^ (n / k))
def SqrtLogLogConjecture : Prop :=
  ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (C * n / (Nat.sqrt (Nat.log 2 n) + 1)))
```
* The statement is sound and minimal. It uses one machine (∃M before ∀k), finite alphabets on all stacks,
  binary input (`encodeNat`), and output `minFac` (so `minFac 0 = 2`, `minFac 1 = 1`). `#print axioms` gives the
  standard three (l.181).
* **What `C_k 2^{n/k}` hides.** ∀k∃C_k means exactly time 2^{n·ε(n)} for *some* ε → 0, with no rate. In the
  proof, ℓ (the number of recursion levels) "is computed from n while it runs, and grows without bound"
  (l.238–240). Anthropic's levels grow doubly exponentially (K_{l+1} = (2^{3l+x₀}K_l)²) and the ε-route
  shrinks e by a constant factor per level, so the implied ε(n) can be a very slowly vanishing function.
  The C_k are galactic. The "trying all groupings" step (l.234) adds a K^g factor. Whether the proof would give
  1/√log n is not visible from the paper. It does not claim it: √log is stated only as the *conjecture*
  `SqrtLogLogConjecture`, "made by the AI … We did not ask it to follow through" (l.196–201).
* **Method** (l.210–256). (1) Prefix search on n-bit divisor words, using the count of divisors with prefix x
  (`search_eq_minFac`). (2) `mulNet_value`: an SS network with "a Fourier transform on numbers modulo 2^m+1,
  split into two layers of smaller transforms [CT65, Bai90], and then the carries"; "each check only stores
  the values it is given, so once d and e are chosen every other bit is determined" (parsimony); clusters
  "share at most a constant times n bits in total (`clusterNet`)" (l.222–231). (3) Anthropic's engine §§3–5
  re-proved, with "all arithmetic modulo small numbers". (4) A zero test by residues mod 1..2M and C(2M, M)
  (Erdős). (5) Compilation through two intermediate languages to Mathlib TM2.
* **Gaps.** The rate is unquantified (above). Full factorisation (their Theorem 2) is not in Lean, but it is a trivial
  loop. The proof was not read by the authors ("we did not read the proof", provenance). That is irrelevant for the
  Lean claim, but the paper's description of the proof is AI-written. We did not obtain the Palomar sources (the
  registry page did not render). **The independent check that matters is that the SS-as-network idea is the same
  as [AK] §2.3**, and it is mathematically sound (§3).

## 2. Shunia, hexagon:2610.00711 (2 Nov 2026)

**Claim** (sh.tex l.68–76): the least prime factor and the full factorisation in time 2^{O(n/√log n)} and space n^{O(1)}.
Corollary 3 (l.260–271) is exactly RR's `SqrtLogLogConjecture` form.

**Proof** (1 page). Thm 2 = OpenAI Thm D.1 as restated in [AK, Thm 2] (l.120–132): BTN, s edges, degree
O(s^{9/10}), poly-time predicates, gives 2^{O(s/√log s)} time, poly space. Thm 3 = [AK, Thm 3] (l.155–163):
ab = z, d-bit a and b, parsimonious, < 1100(d+1) edges, degree < 136(d+1)^{3/4}. Lemma 4 (l.183–221): fix z = N and the
prefix of a in the predicates at the interface endpoints. The graph is unchanged and parsimony is kept, so
C_N(u) = contraction − [u ⊑ word(1)]. Then s = Θ(n) and degree O(s^{3/4}). Main proof (l.223–258): n prefix rounds,
≤ n² counts for the full factorisation.

**Check.** The composition is correct *given* Thms 2 and 3. Points checked:
* Degree O(n^{3/4}) ≤ s^{9/10}: yes. Fixing bits inside a predicate keeps the edge count and degree: yes. The
  divisor ↔ assignment bijection (both a, b < 2^n, z has 2n bits, N > 0 forces a, b ≥ 1): yes. The off-by-one for the
  divisor 1: handled (l.204–206). Lexicographic = numeric for fixed-length words, so the least divisor > 1 is prime: yes.
* TM vs bit operations: poly overhead → constant in the exponent. Fine at this rate.
* The O(n log n) remark (l.283–291) is right: an O(n log n)-size network gives 2^{O(n√log n)}, "which does not give
  subexponential time".

**Gaps.** (i) It is entirely conditional on OpenAI Thm D.1. That theorem is unrefereed, and [AK] say "the authors
did not attempt to independently verify that theorem" (AK, AI disclosure). Remark 1's reduction (bipartite subdivision,
ring Z_{2^{s+1}}[X]/X) is plausible, but Shunia takes it from [AK] (l.134–147). (ii) It is conditional on [AK] Thm 3,
a v0.2 preprint 5 days old with "minor bug fixes" in v0.2. (iii) There is no Lean proof, and nothing is new beyond
the composition. Its abstract's "the linear-size multiplication encoding of Akshima et al." is accurate, but the reader
should know that it is a high-arity-vertex network, not a CNF. (iv) [AK] note that D.1's recursion only kicks in for
size ≥ 2^{2^{17}} (footnote 4). So the result is galactic, as RR's is.

## 3. The encoding question (decisive)

**What [AK] Thm 3 is** (§2.3, Fig. 1). Limbs of k = J/4 bits, with J the least power of 2 such that d < J²/64 (so J ≈ 8–16√d).
There are ≈ d/k ≈ √d limbs. The ring is A = Z/(2^J+1), the length L is the least power of 2 ≥ 2·(#limbs), and ω = 2^{2J/L}. The pipeline:
forward DFT of a and of b in two stages (L₂ vertices, then L₁ vertices, with L₁, L₂ ≤ √J ≈ d^{1/4}), then L pointwise
products, an inverse DFT in two stages, and 2n carry vertices. A transform vertex sees ≤ 2√J words of J+1 bits, i.e.
O(d^{1/4}·d^{1/2}) = **O(d^{3/4})** bits. There are O(d^{1/4}) of them per stage, so each stage has O(d) edges. Products and
carries have degree O(√d). Coefficients satisfy L·2^{2k} ≪ 2^J, so there is no wrap-around. Canonical residues in
[0, 2^J] and unique carries give parsimony. This matches my own reconstruction, and RR describe the same network
(l.226–231). **So: yes, a parsimonious O(n)-edge encoding of "pq = N, p ⊒ π" exists in the BTN / large-node
model.** Its whole trick is that a vertex may run any poly-time check on n^{3/4} bits, which collapses the log n
levels of FFT recursion into 2 stages.

**What does not exist (as far as known).** A bounded-width CNF (or fan-in-2 circuit) of O(n) size. The best are
O(n log n) for multitape TMs (Harvey–van der Hoeven 2021) and O(n log n·2^{O(log* n)}) or O(n log n log log n)
circuits (Fürer / Schönhage–Strassen). Turning the BTN into a CNF needs Tseitin on each vertex's poly-time
predicate, which brings the size back to ≥ n log n. [AK] say the same: "even the best known fast circuits have about
d log d wires … This costs a factor log d … more than the factor √log d that Theorem 2 saves" (§2.3).

**Rates:**

| engine / model | size of the "pq=N, prefix" instance | rate |
|---|---|---|
| our Tseitin → #3-SAT, Anthropic clause bound 2^{CkM/√log M} | M = Θ(n log n) clauses | 2^{O(n√log n)}: **useless** (> 2^{n/5}) |
| OpenAI D.1 (BTN, degree ≤ s^{0.9}) | s < 1100(n+1), degree 136 n^{3/4} | 2^{O(n/√log n)}, poly space (conditional, unverified) |
| **Anthropic `Net g` counted route (our bridge)** | g ≤ 3n^{1/5} clusters, P = O(n^{4/5}), U, gP = O(n) | **2^{O(n/√log n)}**, exponential space, Lean-verified engine |

Why the Net route works. Our `groupingExplicit` + Theorem A(b) give
T ≲ (K^g + 2^{e_ℓ(U+gP/K)+2gP/K}·τ)·poly with e_ℓ ≤ (3x₀+6)/√log K_ℓ and g = 3K⁸ (anthropic-api.md §2.1, §4.3).
Pack the SS vertices (total degree ≤ 2200(n+1), each ≤ 136 n^{3/4}) first-fit into g bins of capacity
P = 4400(n+1)/g + 136 n^{3/4}. Pick K = K_ℓ, the largest level ≤ n^{1/40}, so log K_ℓ = Θ(log n) and P ≥ n^{3/4}.
Then U ≤ 2s = O(n), gP = O(n), and K^g = 2^{O(n^{1/5} log n)}, which gives 2^{O(n/√log n)}. The node constraint is
gP = O(n) with P ≥ max vertex degree, which forces K ≤ ~n^{1/32}. That is why the `pickOf` exponent must be 1/40
here, not Theorem2.lean's 1/30. A three-stage DFT (degree n^{2/3}) would also allow 1/30. Nothing better than
n/√log n is available from either engine.

## 4. Lean plan on our bridge (target: RR's `SqrtLogLogConjecture`, plus the full factorisation)

Template: `ExactHC/Theorem2.lean` (1765 lines: uniform machine, `pickOf`, `branch_bound`) and `UPackage.lean`
(640 lines: one context type, one set of procedures, uniform in g). The label-sharing form (`ULabelPackage`) fits
directly: shared bits are BTN edges between clusters, Ψ = equality, f = [z|shared = θ], and W_a = conjunction of the
cluster's vertex predicates.

| module | content | est. lines |
|---|---|---|
| F1 `SSArith` | words mod 2^J+1 (canonical, J+1 bits); ω = 2^{2J/L} with ω^{L/2} = −1; DFT/inverse-DFT identity; four-step factorisation; negacyclic convolution = limb product (no overflow: L·2^{2k} < 2^J); carry chain | 3–5k |
| F2 `MulNet` | the BTN (vertices, ports, predicates) for (n, N, u); `mulNet_value`: count = #{a : a ∣ N, word_n(a) ⊒ u} (parsimony: every auxiliary bit is a function of a, b); clusters → `Net g` with `Is P B`, U, gP ≤ c₀n + q g³ | 2–3k |
| F3 `MulProcs` | `Procs`/`PolyTimeProcs` for mem/W/Ψ/f (PolyT of the stage-wise DFT on bit lists, via `fun_prop`), with S = poly(n) | 1.5–3k |
| F4 `UMulPackage` | reader `prep : (unary g, N, u) ↦ context`; one q for all g (as in UPackage) | 0.6–1k |
| F5 `FactorM` | a stepped machine: n prefix rounds, each runs Lemma 8 case (i) + `cliqueMachine` with queries plugged (`stPlug`), keeps u, appends 0/1 on count > [u ⊑ 1]; the `round_bound` analysis (as `branch_bound` minus the Lemma 6.1 branching, times n); `CountKSat.exists_tmW` → TM2 | 1.5–2k |
| F6 `FactorStatement` | `search_eq_minFac` (prefix search = minFac); an adaptor from `Outputs M (bits N) (bits (minFac N))` to Mathlib `TM2ComputableInTime encodeNat encodeNat Nat.minFac` with `time n ≤ C·2^{Cn/(√⌊log₂ n⌋+1)}` (re-state RR's 13 lines verbatim in our v4.33 environment); full factorisation by iteration (`Nat.primeFactorsList`); `d(N)` as one count | 0.6–1k |

The total is **≈ 10–15k lines**. That is less than RR's 36k, because we import the engine and the TM bridges
instead of re-proving them. The risk is concentrated in F1 and F3 (PolyT certificates for the DFT stages).
Shortcut: if RR's Palomar sources are licensed for reuse, port their `mulNet_value`/`clusterNet` (v4.35 → v4.33) for F1–F2.
Do *not* go through `Circuits/Engine.lean` (the CNF clause route): it would give only 2^{O(n√log n)}.
The (b) route, OpenAI D.1, gives the same rate in poly space but has no Lean bridge, so it is not machine-checkable for us.

## 5. Beyond factoring: "O(n) unknown bits + O(1) cheap arithmetic"

The criterion: a parsimonious large-node network with O(n) cut. In [AK]'s toolbox these are available at O(n) each:
+, <, = 0, gated equality, copying, ×, and mod-q × / + (AK Lemmas 2 and 8, Cor 1). Anything with O(1) such operations on
O(n) unknown bits costs 2^{O(n/√log n)}, and prefix search turns counting into search.
Ranked by novelty × feasibility (feasibility = reuse of F1–F5):

| # | problem | certificate size | rate | status |
|---|---|---|---|---|
| 1 | minFac / full factorisation of N | O(n) (one ×) | 2^{O(n/√log n)} | Shunia (conditional), **new as verified**; F1–F6 |
| 2 | **sqrt mod p, least quadratic non-residue, roots of fixed-degree f mod p** (deterministic) | y² ≡ a (one mod-×); for the non-residue: count pairs (x < B, y) with y² ≡ x and binary-search the first B where #residues < B; Horner: d mod-× | 2^{O(dn/√log n)} | **new**: unconditional deterministic bounds were Burgess-type p^{1/(4√e)+o(1)} for the non-residue and ~p^{1/2} (Shoup) for root finding; GRH gives poly. F1 + mod reduction |
| 3 | **Σ_{m≤x} d(m) (Dirichlet divisor sum), Σ_{m≤x} σ(m), Gauss circle #{u²+v² ≤ x}**; generally, lattice points in any region cut out by O(1) multiplications | one × + one < (σ: an extra counter c < a) | x^{o(1)} = 2^{O(n/√log n)} | **new**: known exact algorithms are ~x^{1/3} (Hiary et al.); feasible (one ×) |
| 4 | d(N) (one count), φ, λ, μ, σ, rad, squarefreeness of N, ord_N(a) (via factoring N and the p−1), sqrt mod composite N | via #1 | 2^{O(n/√log n)} | immediate corollaries; deterministic best was N^{1/5} for all of them |
| 5 | **class number h(D) of an imaginary quadratic field** = #reduced forms (a, b, c), b² − 4ac = D, \|b\| ≤ a ≤ c | 2 ×, comparators, O(n) bits | \|D\|^{o(1)} | **new** deterministic unconditional (previous: \|D\|^{1/2}-ish unconditional, \|D\|^{1/4..1/5} under GRH / Shanks). The TM statement is cheap; linking to Mathlib's class group is costly |
| 6 | #solutions in a box of a fixed Diophantine equation with O(1) operations (small roots of f(x,y) ≡ 0 mod N beyond Coppersmith's bound, partial-key RSA, …) | O(#ops·n) | 2^{O(n/√log n)} | general meta-theorem, a corollary of the F1 toolbox |
| 7 | ECDL ([AK]): index calculus with hashed factor bases | O(mb), point addition O(b) | 2^{O(b/(log b)^{1/4})}, **randomised**, conditional on D.1 | could port to the Anthropic Net (same encodings), but the randomised TM statement and the factor-base probability analysis are heavy; low feasibility |
| ✗ | DL in (Z/p)*, order finding (direct) | g^x needs n modular × → s = Θ(n²) | 2^{O(n²/√log n)} | **useless** directly (DL stays at p^{1/2} deterministic; order via #4 is fine) |
| ✗ | subset sum / knapsack, n items of n bits | the partial sums carry n·(n/b) bits for blocks of b ≤ s^{0.9} ⇒ s ≥ n^{2/1.9} ≈ n^{1.05} (n² with an adder tree) | worse than 2^{n/2} | **useless**; for w-bit numbers, w ≪ n, the DP 2^w already wins |
| ✗ | SVP, dimension n, poly-bit lattice | the witness alone has n log n bits | 2^{O(n√log n)} | **useless** vs deterministic 2^{O(n)} (Micciancio–Voulgaris) |
| ✗ | polynomial factorisation over F₂ (or small q), degree n | O(n) (SS/Cantor-type FFT network) | 2^{O(n/√log n)} | **pointless**: Berlekamp is deterministic poly for small q. Only large p matters → #2 |

**Reverse direction (permanent-like dense problems).** No. Factoring works because the *witness* is tiny (n bits)
and all the "work" (Θ(n log n) bits of FFT transcript) can be hidden inside big nodes with linear cut. For the
permanent / #PM the witness is a permutation (≥ n log n bits). The global constraint (bijectivity) forces a
cut U ≈ n lg h (`permanent/permanent-attack.md` §2), and the n² input entries are touched by every row factor.
Large nodes do not shrink a cut that the witness itself must carry. A hard cap applies: any engine route
costs ≥ 2^{(witness bits)/√log}. So only problems whose natural NP witness is O(n) bits *and* whose verifier has
O(n) cut in the large-node model can gain. Arithmetic verifiers (×, mod ×) qualify; permutation and matching
verifiers do not.

## 6. Recommended next step

F1–F6 (factoring at 2^{O(n/√log n)}, proving RR's `SqrtLogLogConjecture` unconditionally on Anthropic's verified
engine), then #2 and #3 as cheap follow-ups on the same `MulNet` (≈ +1–2k lines each), with #4 as corollaries.
