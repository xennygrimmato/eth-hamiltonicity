# Referee report on x1 (twins, Goldbach, k-tuples, Mertens via Ni)

**Verdict: CORRECT WITH FIXES.** I did not break the core claims. Four statements in the notebook need correcting; two of them (Mertens prior art, k-scaling) are substantive.

## Checks

1. **Identity.** The edge cases hold:
   - c_1(1) = 1, so n = 1 is exact.
   - d = 1 contributes the single term x = 0.
   - The m = 1 term vanishes because log 1 = 0.
   - n = 2 uses j = 1 and y = 1. Re(j ln 2 + log z) ≥ 0.223 on the disc, so 1/log is analytic there.
   - At a prime power p^k with k ≥ 2, μ = 0, so the term is 0.

   The sum Σ_{2≤n≤N} P(n)P(n+2) counts the primes p ≤ N with p+2 prime, and p+2 may be N+1 or N+2. So (3,5) is counted and (2,4) is not. This differs from the convention "p+2 ≤ N" by at most 1, so **state the convention in Thm A.**

2. **Error budget.** I recomputed it independently.
   - The error is bounded tuple by tuple, by telescoping. Large Ramanujan sums therefore never enter the bound; only the tuple count T does.
   - The count is right: T ≤ (N+2)^5, with two copies of (n, d, m, x, x′).
   - The product bound Π(B+1) per copy is 2·2·(β+1)·2.44.
   - D = 5β′ + log₂(1536(β′+1)²) gives a total error < 1/2. ✓
   - Ni's table already suffices for twins once β ≥ 19. x1's threshold β ≥ 22 is conservative and harmless.

3. **Engine.**
   - (a) **Fix the text: "Ni has not released his network" is false.** Ni's local repo has it in `formal/bridge/EthFollowup/Primes/FourKernel*.lean`.
     - The equation list is generic: `compile (es : Fin m → Equation)`.
     - It runs through `WeightedNetworkBounds.arithSys_U_le`, which gives U ≤ 2·Wa(n)·A(n,L), where A is the total limb mass.
     - In the doubled system A doubles, so U and P change only by a constant factor and c₀′ = O(1).
     - What remains is mechanical: the 8-kernel descriptor, a fibre-product count bijection over the shared n, and the bit bounds. It is still unwritten, so A–C stay conditional on it.
   - **Fix the k-scaling.** Each copy's bit count grows with the precision D ≈ (2k+1)β, so U = Θ(k²β). N^{o(1)} then needs k = o((log b)^{1/4}), not k = o(√log b), and the exponent is O(k²b/√log b). Uniformity of the package in k is also unproven. **State the theorems for fixed k only.**
   - (b) **The variable counts reconcile.**
     - Ni: 72 variables = 12 + 4·15.
     - Ni: 33 equations = 5 + 4·7.
     - Ni: 132 slots = 33·4 fixed slots, counting zero and linear slots.
     - Ni has 41 var×var products, because he stores U, V and Q as variables. x1 has 19, because it treats them as query constants.
     - Long×long products are allowed; each costs 60·(its limb count) in A.
   - (c) **Multiplicities are expanded correctly.** Each factor contributes a (node, re/im) choice. The sign branch partitions the data; it is not summed. That gives at most (2M)^8 × scales classes, which is β^{O(1)}.

4. **Mertens.** It really is simpler: one phase kernel and no logarithms. **But "best known x^{3/5}" is wrong.** Hirsch–Kessler–Mendlovic (arXiv 2212.09857) give Õ(√x) for M(x). Ni's Remark 7 explicitly expects the Mertens case, so Thm C is his anticipated corollary, not a new idea.

5. **Validation.** `pipeline.py` faithfully reproduces Ni's eq. (2):
   - integer quotients ⌊2^{t+p}q|X|/D⌋;
   - p-bit Gaussian coefficients;
   - exact arithmetic throughout;
   - sieve truth for comparison.

   A wrong method would fail it. It does not exercise the engine system, though: the class expansion is checked for π with one copy only. Semiprimes, a²+1, π(N;q,a), Liouville and Chowla are untested. My re-runs:
   - Twins, N = 300: 0 of 299 rounding failures, max error 2^−62.8.
   - Cousin primes (n, n+4), N = 500, a case x1 did not run: 0 of 499 rounding failures, max error 2^−61.5, final count 27, which is correct.

6. **Novelty** (searched 24 Nov 2026): I found no N^{o(1)} exact π₂, G(2n), k-tuple or M(x) result. Hexagon is not indexed, so that check is weak.

## Corrected statements

Assume three things:
- (i) Ni's Prop. 4 (`NatBatchQuery.machine_TM_linear_input`), with the 3-SAT engine under it;
- (ii) the doubled-descriptor count and bit lemma, as an instance of Ni's compiler;
- (iii) the coefficient certification at precision O(β).

Then for **fixed** k and h, each of the following is computable in T_C(N):
- π₂(N) = #{p ≤ N : p+2 prime};
- G(2n);
- the Sophie Germain count #{p ≤ N : 2p+1 prime};
- #{n ≤ N : n+h_i all prime}.

M(x) is computable in T_C(x) under (i) and a one-copy lemma. It is a Ni-anticipated corollary, and the prior best bound is Õ(√x).
