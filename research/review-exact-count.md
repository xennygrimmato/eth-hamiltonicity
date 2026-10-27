# Referee report: exact deterministic #HC in 2^{delta n} for sparse graphs

Referee, 2026-10-27. Status: COMPLETE. Verdict: **SOUND, conditional on Anthropic's [A]** (Theorem A(b) /
Lemma 8(i), equivalently Lemma 1 with e* = 0). No errors found in steps (1)-(4). Two points that looked
like gaps in the one-paragraph claim are already handled correctly in research/exact-hc-theorem.md
(details below).

## Method
My own derivation and code came first; I read research/exact-hc-theorem.md only after that.
Scripts (exact integers, all written from scratch):
- scripts/review_exact_count.py: brute-force #HC, 2-factor enumeration, Bareiss det, a global
  Grassmann/Berezin integrator, a blob evaluator built from my own sign derivation, and a literal
  network (Definition 2 of [A]) with copy bits summed over {0,1} with their Psi indicators (g <= 5).
  Two crossing-edge alphabets: 6 states, and a 5-state product trick (1+loc_i)(1+loc_j) - loc_i loc_j.
  Half the blob tests carry random integer weights w_e on "edge used" and u_e in {-3..3}\{0} on the
  bilinear terms. Target: sum_X prod w_e det L_r(X;u).
- scripts/review_exact_count_ablate.py: drops the global interleaving sign (unweighted and weighted).
- scripts/review_exact_count_interleave.py: graphs built so that crossing edges pile up on
  interleaving bundles.

## (a) Berezin = det
About 500 (graph, arbitrary subgraph X, every root) checks, plus about 115 checks of the sum over all
2-factors. All equal. Integral = coefficient of prod_{v != r} psibar_v psi_v.

## (b) Sign rule (own derivation) and blob evaluation
Each bilinear term is a pair of generators. Pairs are even, so they commute. Put each pair in blob order
(the generator in the lower blob first). The sign is then (-1)^{number of interleaving pairs of pairs}.
- Pairs that meet in exactly one blob are decided by that blob alone.
- Two pairs in the same bundle ab interleave iff 1 + [x_p<x_q] + [y_p<y_q] is odd. This splits into
  C(N_ab,2) + (a-local) + (b-local), so it is local too.
- Pairs on disjoint chords give exactly sum_{a<c<b<d} N_ab N_cd.

This matches claim (3). Observation: every blob has an even number of odd generators, so (P_ab) is a
cycle-space vector of K_g. Because of that the global sign is nontrivial only on a few % of random
instances.

Tests: n = 3..10, including Petersen, prisms, K4, K5, K33, K34 and rings of triangles, plus random and
cubic-like graphs. g = 2..6, with random, very unequal and empty blobs, a random root and a random
local order. About 790 blob evaluations (638 in the main suite, both alphabets) and 297 literal-network
evaluations. **0 failures.** Without the global sign, 8 instances give the wrong answer, so the tests do
exercise that term.

One failure appeared during development. It came from misplaced weights in my own harness, not from the
claim, and was fixed.

The claim's "5 choices (unused, or one of 4 bilinear terms)" is literally one state short: "used with
term 1" is missing. The write-up's labels {N,0,1,2,3}, with label 0 = 1*(1+psibar_t psi_t), merge two
terms correctly. I did not test those exact labels. My 5-state alphabet is a different merge and passes,
and the difference only changes a constant.

## (c) Fit to [A]
- Settings are the base-5 codes of the incident crossing labels plus copy bits (subsets of
  {0,1}^{P_a} are allowed). The node table W_a is a signed integer table that includes the
  (-1)^{P_ab * copy} factors.
- Psi is a genuine equality test (Def 1(b)).
- Totals: U <= 2 log5 m + g^3 and B = O(n/g). log tau <= 1.5 mu, with mu <= (2m+n)/g + 2.
- Lemma 8(i) with Theorem A(b) gives an exponent of about e*4.65m + 3*gP/K + log tau + O(g^3) +
  O(K^2 log n). This is <= delta n for e <= delta/40D, K >= 60D/delta and g = 3K^8.
- Nothing hidden blows up. The C(g,4) interleavings cost only O(g^3) copy bits, a constant for fixed
  delta. The factors K^g and (K(L+B'))^{C0 K^2} are polynomial.
- Unbounded degree is the one real trap: a blob holding a degree-Theta(n) vertex makes P = Theta(n) and
  2gP/K = Theta(K^7 n). The write-up fixes this (Lemma 6.1) by branching on the two cycle edges at each
  vertex of degree > n/g (at most n^{4Dg} branches, polynomial for fixed g), followed by a
  degree-balanced partition. Correct.

## (d) Plausibility / literature
- Identity (1) is elementary folklore: a 2-factor has n spanning trees if it is a Hamiltonian cycle and
  0 if it is disconnected. Pairing cycle covers or subgraphs with Kirchhoff counts to enforce
  connectivity is standard (e.g. Bjorklund's determinant sums).
- The fermionic matrix-tree form is Caracciolo-Jacobsen-Saleur-Sokal-Sportiello (2004).
- The result contradicts (#)ETH for sparse #HC, and hence SETH-type assumptions, all of which [A]
  already claims to refute. I know of no other robust conditional or unconditional bound that it breaks.
  Pathwidth lower bounds of the (6-eps)^pw kind concern graphs where N >> pw.

## What remains conditional
Everything algorithmic rests on [A]: Theorem A(b), Lemma 8 and the existence of pieces. Steps (1)-(4) and
the bookkeeping are sound. I did not build or re-verify the Lean files.
