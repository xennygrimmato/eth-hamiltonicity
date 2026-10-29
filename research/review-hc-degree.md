# Referee report: "Exact counting of Hamiltonian cycles in time 2^{O(n log Δ/√log n)}" (research/hc-degree-theorem.md)

29 Oct 2026. I redid the key steps (encoding, value identity, profile sum, Prop. 3.2, the exponent
arithmetic) before reading the note's proofs. Then I re-ran the script with new seeds and
mutation tests. Scratch tests are in
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/{mut.py,inter.py}`.

## Summary

The note swaps the per-crossing-edge base-5 labels of [HC] Def. 5.1 for a per-pair block. For a
fixed profile s, the block holds the colex rank of the set of used crossing edges in E(a,b), plus
2 bits per used edge. The note then sums over the profiles. This cuts the total shared bits U from
2 log5·m to 2n·log(2e·d̄) + g³. The per-node bits fall from about log5·μ to
2ν·log(2eΔ) + g + g². High-degree vertices then cost only logarithmically, so Theorem A (maximum
degree) needs no degree-reduction branching.

I checked every step of the core argument and found it correct. The network is a valid network in
the sense of Definition 2 of [A], and the value identity is right. The parameter bounds hold with
the stated constants. The exponent arithmetic for Theorem A and Corollary C(a) is right. The
comparison with [HC] (2.32·Δn against 2n(log Δ + 2.44), with the new term smaller for Δ ≥ 4) is
right.

The issues I found are of three kinds:

* **Simpler proof missed.** Theorem B already follows from Algorithm A unchanged. The case split,
  the branching at Θ = n^{0.6} and the 2^n DP are not needed. The note's §5 states the opposite.
* **The script does not test the interleaving sign.** None of its instances exercises it, although
  the write-up says some do. I checked this property separately and it holds.
* **Small inaccuracies** in the hypotheses of Corollary C(b) and in the literature comparison.

## Verdict

**Sound.** The issues below are fixable and change neither the theorems nor their conditional
status. The main text needs no mathematical change. §4.2, §5 ("For Theorem B: yes"), the Lean plan
in §7 and the description of the script in §6 need editing.

## What I checked independently (all confirmed)

1. **Definition 2 of [A].** For each node a, the setting is the concatenation of per-pair blocks
   and the copy bits y^{(a)} on Q_a.
   * W_a = σ_a·χ_a·I_a is a function of ℓ^{(a)} and y^{(a)}. Each of these can be decoded from
     z_a, block by block.
   * Ψ_ab depends only on (z_a, z_b). Ψ_ab = [π_ab(z_a) = π_ba(z_b)], and π_ab has length
     c_ab = c′_ab + (g − b).
   * The factorisation through c_ab bits is Observation (b) of [A].
   * c is symmetric, and len_a = P_a ≤ P.
   * (i): Σ_b c_ab = Σ_b c′_ab + C(g−a,2) + (a−1)(g−a) ≤ Λ + g − 1 + g² ≤ P.
   * U = 2Σ_{a<b} c′_ab + 2C(g,3), using Σ_b (b−1)(g−b) = C(g,3).
   * P and B do not depend on the profile. Only U, and with it L, varies from profile to profile,
     and Lemma 8 accepts any U.
2. **Bijection for a fixed profile.** The colex rank is a bijection from the s-subsets onto
   [0, C(e,s)). Off S_ab every label is N, and on S_ab every label is one of {0,1,2,3}. Every
   string with valid rank fields therefore decodes to exactly one setting, so S_a is exactly the
   image of the encoding.
   Both ends list E(a,b) in the same crossing order and use the same s_ab. So the blocks are equal
   iff the labels agree on E(a,b), which is Lemma 2.3.
   Everything the node tables need is recomputed from the decoded labels: σ_a, the parities
   P_{ab} = Σ π_k mod 2 used by χ_a, the parities P_{bd} sent on the pair, and I_a. So the
   re-encoding changes nothing in [HC] §4.
3. **Profile sum.** The map ℓ ↦ s(ℓ) partitions L^{m_×}. For a fixed s, each ℓ in the fibre
   determines exactly one consistent z. So Σ_s Z_s = n·#HC, by [HC] Thm 4.6.
   Inadmissible profiles give 0: Σ_{v∈V_a} deg_ℓ(v) = s_a, because every crossing edge at a has
   exactly one end in V_a. If s_a > 2ν_a, some vertex v has deg_ℓ(v) ≥ 3, every degree indicator
   in I_a vanishes, and Z_s = 0.
   Profile count: at most (2ν+1)^{C(g,2)}. With g ≤ 3n^{8/30} this is 2^{O(n^{16/30} log n)}, which
   is o(n/√log n) in the exponent. For fixed K (Corollary C(a)) it is poly(n).
4. **Prop. 3.2.** I checked the following:
   * Vandermonde, and log C(N,M) ≤ M log(eN/M).
   * F_N is monotone: the derivative of M log(eN/M) in base 2 is log(N/M).
   * Route Δ: F_{N_a}(2ν_a) ≤ 2ν_a log(2eΔ) when 2ν_a ≤ N_a, using N_a ≤ Δν_a. In the other case,
     N_a(log e + 2) < 2ν_a log(4e).
   * Route μ: (log e + 2)·N_a ≤ 3.443·μ_a.
   * U: |s| ≤ n by admissibility, and log C(m_×,|s|) + 2|s| ≤ n log(4em/n) = n log(2e·d̄), in both
     cases n ≤ m_× and m_× < n.
   * (ii): the number of x is at most Π_v(1 + d + C(d,2)) ≤ Δ^{2ν_a}, using 1 + d + C(d,2) ≤ d²
     for d ≥ 2 and min-degree ≥ 2. The ℓ¹ norm is submultiplicative, ‖1 + q_e‖₁ = 5, every piece
     has norm ≤ 2, and |x| ≤ ν_a. Hence |I_a| ≤ Δ^{2ν_a}·20^{ν_a} = 2^{2ν_a(log Δ + 2.161)}.
     The μ-route gives ≤ 2^{2.661μ_a}, using ν_a ≤ μ_a/2.
   * (iii): the I_a loop (one monomial per factor, inversion-count sign) runs in poly(n) memory.
     τ ≤ 2^Λ·poly(n).
5. **Exponent for Theorem A.** This is (1.1)–(1.2) of [HC] with ζ = 1/(2K) and g = 3K⁸, giving
   K²L ≤ U + gP/K + K². The dominant term is e·U ≤ c_e(2nλ + g³)/√log n. The other terms are
   lower order:
   * (e+2)·gP/K = O(n^{1−1/300} log n);
   * log τ = O(n^{1−8/300} log n);
   * K²-terms O(n^{1/15} log n), g·log K = O(n^{8/30} log n), and the profile count above.

   All of these are o(n/√log n) uniformly in Δ ≤ n. **No degree reduction is needed for
   Theorem A.** This is correct.
6. **Corollary C(a).** With e ≤ δ/(8λ₀) and K ≥ 24λ₀/δ:
   * e·U ≤ δn/4 + g³;
   * (e+2)·gP/K ≤ 6nλ₀/K + O(1) ≤ δn/4 + O(1);
   * log τ ≤ δn/12 + O(log n).

   Total O(2^{δn}). Correct.
7. **Theorem B, as written.** Case 1 (2^n·poly ≤ 2^{2nλ̄/√log n} when λ̄ ≥ √log n) is correct.
   Case 2 is also correct:
   * Lemma 6.1 is valid for any Θ ≥ 2.
   * |H| < d̄n/Θ ≤ n^{0.401}.
   * Route μ with Lemma 6.2 gives gP/K = O(n^{1+1/1000−1/300}) + O(n^{0.87}).
8. **Script re-run.** `python3 hc_degree_network.py 4242 30` gives PASS (D1 135, D2 507 147,
   D3 122 342, D4 6 066, D5 3 552, D6 30, D7 194; 26 s). Seed 99 with 20 instances also passes.

## Issues

### 1. Theorem B needs no case split, no branching and no 2^n DP (moderate; the proof given is correct but redundant, and §5 claims the opposite)

Prop. 3.2 bounds the total by U ≤ 2n·log(2e·d̄) + g³. The only input to this bound is
admissibility (|s| ≤ n) together with m_× ≤ m. It holds for **any** partition and any Δ.

In Algorithm A (vertex-balanced β, route Δ), the per-node quantities enter only through
gP/K = O(n log n · n^{−1/300}) and log τ = O(n^{1−8/300} log n). Both use λ ≤ log(2en). Both are
o(n/√log n) for **every** Δ ≤ n, as §4.1 and §5 themselves note.

Hence Algorithm A, unchanged, already runs in 2^{c_e(2n log(2e d̄) + o(n))/√log n}. Since
log(2e·d̄) ≥ log(4e) > 3.4, this is 2^{O(n log(2e·d̄)/√log n)}, which is Theorem B. In §4.1,
replace λ by λ̄ in the e·U line and nothing else changes.

As a result:

* the Case 1/Case 2 split in §4.2 is unnecessary;
* the branching at Θ = n^{0.6}, route μ and Lemma 6.2 are unnecessary;
* the deterministic 2^n·poly algorithm is unnecessary.

§5 says "For Theorem B: yes … one needs the per-node bits to be controlled by the blob's degree
sum". It also says the split exists "because the gP/K term … exceeds the claimed bound". Both
statements are false for route Δ. They hold only for route μ, which the note did not need to use.

§7 lists a new 2^n·poly #HC machine (subset DP) as missing Lean work. That item can be deleted,
along with the Lemma 6.1/6.2 and route-μ table-procedure items for Theorem B.

*Fix:* in §0, state Theorem A directly with d̄ (Theorem A becomes a corollary). Replace §4.2 with
the remark above. Correct §5 and §7. Route μ can stay as a remark. For fixed K
(Corollary C(a)), however, the average-degree version does **not** follow this way: gP/K ≈ 2nλ/K
with λ up to log n is not ≤ δn. So keep C(a) as a maximum-degree statement, or prove its
average-degree form with branching.

### 2. The script never exercises the interleaving sign or the parity copies (moderate, verification)

§6 says the planted instances that visit four blobs in order (0,2,1,3) are "the case where the
interleaving sign matters, [HC] C12". They are not. I set sign_mode = "nointerleave" on
`DegNetwork`, which drops χ_a. **All checks still PASS** on seeds 2026 (24 instances), 4242 (30),
11 (30) and 99 (20) (`mut.py`).

So, as shipped, D7 does not test χ_a or the parity copies on the pairs. By [HC] §8, the sign
matters on disconnected 2-factors whose non-root cycle winds through the blobs in interleaving
order. A planted Hamiltonian cycle on 1–2 vertices per blob does not produce these.

*The property itself is true.* `inter.py` uses the generator of `review_exact_count_interleave.py`
(g = 4, n = 7–9, at most 9 crossing edges). It selected 4 instances on which the ablated **old**
network is wrong. On all 4, the full rank-encoded network passes every check, and the ablated
rank-encoded network fails D7 (MISMATCH).

*Fix:* add this instance family to the script. Add a built-in ablation self-test: assert that
"nointerleave" fails on at least one instance. Correct the sentence in §6.

### 3. Vacuous or weak checks in the script (minor)

* **D3 "Ψ symmetric" is a tautology.** `HCNetwork.Psi(b,a,…)` is defined as `Psi(a,b,…)` with the
  arguments swapped. The "c symmetric" check only compares values that are both built from the
  same symmetric dictionary.
* **D2 "z is not None and len(z) = P_a" is nearly vacuous.** `settings()` enumerates only labels in
  the correct fibre, so `encode` never returns None. The round trip is tested only on encodings.
  That every string with valid ranks is a setting (surjectivity) is never tested, although it is
  trivial.
* **D7 evaluates Ψ semantically,** by comparing decoded labels. It does not use π/f, so D7 alone
  does not test the rank code; D3 does. D3 is not toothless: a mutant whose π drops the 2-bit
  labels and keeps only the rank fails D3 6 741 times. A mutant with admissibility tightened to
  2ν_a − 1 fails D7 31 times.
* **Prop. 3.2(iii) is not implemented.** The degree-pruned enumeration of x and its cost
  Δ^{2ν}·20^ν are absent: I_a is computed by the existing `proof_lib` routine. Only the
  magnitude bound on |I_a| is checked.
* **B differs from the write-up.** The script uses B = ⌈min(2νλ, 2.7μ)⌉ + 1, tighter than
  B = ⌈Λ⌉ + 1, so its check is stronger. Say so in §6.

### 4. Hypotheses of Corollary C (minor)

"Assume (H_A), or only [A, Lemma 1 and Proposition 3]" applies only to part (a). Part (b) needs the
counted route, that is, the full (H_A) with K growing with n. With a fixed achievable (K, e),
e·U ≈ 2e·n·log(2eΔ) is not O(δn) once log Δ grows like c√log n. *Fix:* split the hypothesis
between (a) and (b).

### 5. Literature comparison (minor)

* **BHKK [TALG 2012].** The abstract claims O*((2−ε_Δ)^n) for TSP, and an analysis of Ryser's
  formula for the permanent of sparse matrices. It does not claim counting Hamiltonian cycles.
  `paper/main.tex` Table 1 (l.261) lists BHKK as "decision/TSP", which conflicts with this note's
  "count Hamiltonian cycles (and solve TSP)". Either drop "count", or justify it as the sum-product
  version of their trimmed Bellman–Held–Karp DP and say so.
* **"All of these are (2 − ε)^n with ε → 0 as the degree grows"** is wrong for Björklund's
  1.657^n, which does not depend on the degree. Rephrase.
* **Björklund–Williams [ICALP 2019]** is stated for directed graphs (average degree d,
  2^{n−Ω(n/d)}, deterministic). This also covers undirected graphs. The paper's table says
  "directed"; the note should too.
* **Small fixed Δ.** Optionally note that unconditional counting is much faster than (2−ε)^n for
  small fixed Δ, for example via pathwidth on cubic graphs. This does not affect any claim, since
  the new bounds are asymptotic and conditional.
* **"They beat 2^n exactly when C_A log(2eΔ) < √log n"** ignores the lower-order terms. Say
  "roughly".

### 6. Small editorial points (minor)

* **§1 and Lemma 3.3 give different profile counts.** §1 says (n+3)^{g²/2}; Lemma 3.3 says
  (2ν+1)^{C(g,2)}. They agree only when ν ≤ n/2 + 1, which holds for the Lemma 4.1 partition.
  State §1 for that partition. The bound s_ab ≤ min(2ν_a, 2ν_b, e_ab) is slightly sharper. (Every
  admissible nonzero profile also has s_a even, though this is not needed.)
* **Prop. 3.2(iii): name the enumeration.** The procedure for I_a should pick, per node, the
  cheaper of the two enumerations of x. This is implicit in "either … or"; make it explicit,
  because τ uses the minimum.
* **Theorem A's displayed bound.** "≤ 2^{3.5·C_A·n log Δ/√log n}" uses
  log(2eΔ) ≤ 3.443·log Δ for Δ ≥ 2. That is fine, but with issue 1 the natural headline is
  2^{O(n log(2e·d̄)/√log n)}.

## Recommendation

Accept after revision. The mathematics stands. Fix issues 1 and 2: simplify Theorem B, and add the
interleaving family and an ablation self-test to the script. The rest is editorial.
