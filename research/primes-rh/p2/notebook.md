# p2 notebook — which functionals of the prime indicator the engine computes (subtasks 2, 7)

Sources read: parity-note/main.tex (chain lemma, one-count identity, Rem. modk, Prop. adv),
lean/EthFollowup/Primes/{ChainParity,ArithLDesc,PrimeDesc}.lean, ModP/ArithDesc.lean (description language),
research/prime-finding.md (Thm B, B', §3).
Scripts: `checks.py` (all identities, brute force, x <= 10^6, output `checks_1e6.out`), `sopfr_table.py`,
`oddquery_stat.py`.

## 0. The one principle (everything below is a corollary)

`term_zmod` (Lean, ChainParity): for every m < 2^{2^L}, τ^<(m)·C_L(m) is odd **iff m is prime**. Hence for ANY
weight w: ℕ → ℕ,

    Σ_{m∈I} τ^<(m) C_L(m) w(m)  ≡  Σ_{p∈I prime} w(p)   (mod 2).                         (★)

So the engine gives Σ_{p∈I} w(p) mod 2 in x^{o(1)} for every w that is itself an engine count of witnesses
("cheap w"): conjoin the witness constraints of w with primeDescL (disjoint new variables; cuts add). In the
description language of the Lean library (ModP.ArithDesc + ArithLDesc) the cheap constraints on m are:
products var·var / var·const inside linear chains (coeff sum ≤ 32), comparisons with constants/variables, and
**bit patterns** on any variable (free: no extra cut). Cost = engine cost 2^{O(U/√log n)} with cut U; base
primeDescL has U ≤ 2^{22}(n+2); x^{o(1)} = 2^{o(n)} iff U = o(n√log n); the paper's *rate* 2^{O(n/√log n)} iff U = O(n).

Verified numerically: (★)'s base fact for all m ≤ 10^6 (`[base]` line in checks_1e6.out: True).
(Checking the per-m fact for all m ≤ X already implies every mod-2 identity below on [1,X] by linearity; the
script nevertheless computes both sides literally for each functional.)

## 1. The table

Cost column: extra cut on top of the interval count (base U = O(n)), and the resulting time.
Status: Lean = machine-checked; paper = proof below, trivial extension, not formalised; [C] = heuristic.

| functional | how | extra cut | time | status | numeric check (x ≤ 10^6) |
|---|---|---|---|---|---|
| π(I) mod 2, I any interval | primeDescL | — | 2^{O(n/√log n)} | Lean | base: True |
| #{p∈I : p≡r (q)} mod 2, **any q ≤ x** (small, x^{o(1)}, or ~x) | new level-0 var t, chain m·1 = t·q + r (q constant) | O(n) | 2^{O(n/√log n)} | paper | 720 random (q,r,I), q ∈ {2..300007} incl. 2^j: 0 mismatches |
| q = 2^j, any r; more generally any **subcube** {m : bits in J fixed} | bit pattern on m | 0 | same as π(I) | paper (patterns exist in ArithDesc) | (v) below |
| residues r in a range [r1,r2] mod q | t, r variables, m = qt + r, r1 ≤ r ≤ r2 | O(n) | same | paper | — (follows from (★)) |
| arbitrary union of R classes / k intervals / k cheap sets | k separate counts, XOR | k·(base) | k·2^{O(n/√log n)} | paper (linearity) | (iii): unions k=2,5,20, 90 tests: 0 |
| conjunction of s cheap constraints | conjoin | O(s·n) | 2^{O(sn/√log n)} — x^{o(1)} iff s = o(√log n) | paper | — |
| Σ_{p∈I} χ(p) mod 2, χ real (Legendre/Jacobi/Kronecker) | χ(p) ≡ 1 (mod 2) for p∤q | — | — | trivial | **gives nothing beyond π(I) mod 2 and [q-divisors in I]** |
| #{p∈I : (p/q)=+1} mod 2, q prime any size | witness y, 1 ≤ y ≤ (q−1)/2, y·y = q·s + r, m = q·t + r (unique witness) | O(n) | 2^{O(n/√log n)} | paper | (ii) q up to 10007, 240 tests: 0 |
| #{p∈I : (p/q)=+1} mod 2, q composite (factorisation known — factoring is x^{o(1)} anyway) | per prime q_i a canonical residue- or non-residue-certificate (y² ≡ m or y² ≡ m·g_i), keep branches with even # of non-residue bits | O(n + ω(q)) (or 2^{ω(q)-1} queries) | same | paper | (ii'') q=15,77,10403: 90 tests: 0 |
| complex χ of order r mod prime q: Σχ(p) in Z[ζ_r]/2 | = Σ_j ζ^j (N_j mod 2), N_j = #{p : p g^{-j} is an r-th power}; r odd: raw witness y^r ≡ p g^{-j} has r (odd) solutions, no canonical choice needed | O(n log r) | same for r = O(1) | paper | (ii') cubic, q=7,13,31,1009: 120 tests: 0 |
| same, r even (4 \| r) | raw count is 2^s·[..], s = v_2(r) ≥ 2: read N_j mod 2 from the count mod 2^{s+1} (needs §(iv)) | mod-2^{s+1} machinery | x^{o(1)} for s = O(1) | paper | — |
| Σ_{p∈I} f(p) mod 2, f(m) = # parsimonious witnesses (bits of p, p mod q, bits of polynomial expressions in p with O(1) mult., any Boolean circuit of size s via the circuit simulation remark of the paper) | (★) | U_f (bits: 0; O(1) mult.: O(n); circuit: O(s)) | x^{o(1)} iff U_f = o(n√log n) | paper | (v) XOR of all primes in I from 20 bit queries, 40 tests: 0 |
| π(I) mod k, fixed k | Thm B' (Rem. modk), with my cheaper weight (§3) | O(n·S(k)), S(k)=sopfr(c_k)+sopfr(k) | 2^{O(n/√log n)} for k = O(1) | paper | (iv) k=2,3,4,5,6,8: Σ_{m≤x} g W ≡ 1 + kπ(x) (mod k²) for ALL x ≤ 10^6: True |
| π(I) mod k, k growing | same | rigorous S(k) ≤ 3k | x^{o(1)} iff k = o(√log n) = o(√log log x) | paper | — |
| π(I) mod M (CRT over prime powers ≤ K) | as above per prime power | — | rigorous: M ≤ lcm(1..K), K = o(√log log x), i.e. **M up to exp(o(√log log x))** | paper | — |
| π(I) mod M, M up to exp exp(o(√log log x)) (board/prime-finding.md claim) | needs S(k) = O(log k) (or an O(n log k) ordered-k-factorisation verifier, not built) | — | — | **[C], not [R]** | sopfr(c_k)/ln k ∈ [4.3, 16.6] for k ≤ 256 (sopfr_table.py), slowly growing |
| Σ_{p∈I} f(p) mod k (cheap integer f) | Σ g·W·f ≡ [1∈I]f(1) + kΣ_p f(p) (mod k²) | U_f + O(nS(k)) | as above | paper | (v') Σ_p (p mod 5) mod 3, 40 tests: 0 |

## 2. Proof sketches

**(i) APs, any q.** S = {m ≡ r mod q} has the unique witness t = (m−r)/q. Add variable t (level 0, n bits) and the
level-0 chain [m·1] = [t·q] + [r] (q, r constants with ≤ lk 0 limbs; no `.lin` terms, as WFB requires). The count
is Σ_{m∈I, m≡r} τ^<(m)C_L(m) ≡ #{p ∈ I, p ≡ r} by (★). Well-formedness: one more level-0 variable/product/chain;
Spread constant rises from 8 to ~9. No restriction on q: q can be 3, x^{o(1)}, 2^j or ≈ x. For q = 2^j replace
the chain by the bit pattern "low j bits of m = r" (ArithDesc `pat`), which costs nothing.

**(ii) characters.** Real χ: χ(p) ∈ {±1} ≡ 1 mod 2, so Σ_{p∈I}χ(p) ≡ π(I) − #{p∈I : p | q}: no new GF(2)
information. The useful sets are the level sets {p : χ(p) = 1}: Legendre via canonical root y ≤ (q−1)/2 (for
r = m mod q a nonzero QR, exactly one such y; for non-residues none); Jacobi by multiplying Legendre conditions
over the known factorisation, encoding the sign as parity of branch bits. Over Z[ζ_r]/2 a complex character sum is
determined by the parities N_j mod 2 of the index classes, each computable (r odd: r solutions, odd multiplicity
is enough by (★)). The **mod-M** sums Σ_{p∈I} χ(p) mod M = N_+ − N_− mod M come from §(iv).

**(iii) unions.** Mod 2 the functional is linear: k disjoint pieces → XOR of k counts, cost linear in k. A single
count is possible when the union has a parsimonious description (e.g. residues in a range, subcubes).

**(iv) mod k.** Remark modk / Thm B': W(n) := Σ_{d²|n} f(d) W'(d) (depth L), with f(d) ≡ μ(d) (mod k²) on squarefree
d; then W ≡ [n sqf] (mod k²) by the chain-lemma induction (non-squarefree d are killed by W'(d) ≡ 0, so f only
matters on squarefree d). And g(m) := k^{ω(m)} on squarefree m gives Σ_{m∈I} g(m)W(m) ≡ [1∈I] + kπ(I) (mod k²).
**Cost correction.** The note's f = τ_{k²−1} and g = τ_k are ordered (k²−1)- and k-fold factorisations; with
fixed-width boxes each factor needs the full width of d, so the cut is Θ(k²·n), not n log k as prime-finding.md
says (the note itself only says "grows like n log k; we have not built it"). **Improvement:** on squarefree d,
c^{ω(d)} = Π_{p^e‖c} τ_p(d)^e, so any c ≡ −1 (mod k²) works with f = Π τ_p^e at cost sopfr(c) full-width
variables; similarly g = Π_{p^e‖k} τ_p^e. Levels shrink geometrically (Σ_i n/2^i ≤ n), so U = O(n·S(k)),
S(k) = sopfr(c_k) + sopfr(k). Rigorous: c = k²−1 = (k−1)(k+1) gives S(k) ≤ 3k → π mod k in x^{o(1)} for
k = o(√log n), and by CRT π mod M for M | lcm(1..K), K = o(√log log x): **M up to exp(o(√log log x))** [paper].
For the board's exp exp(o(√log log x)) one needs S(k) = (log k)^{1+o(1)}; numerically min_{c≡−1 (k²)} sopfr(c)
≈ 4–17 ln k for k ≤ 256 (sopfr_table.py) — plausible via smooth numbers in residue classes, **[C]**.
Checked: for k = 2,3,4,5,6,8 with the optimal c (3, 8, 15, 24, 35, 63) and L = 5, the congruence holds for every
prefix x ≤ 10^6 (hence every interval).

**(v) weighted.** (★) with w = f; for mod k replace by Σ g W f.

## 3. Consequence for prime finding (for p1 / T3 / P1)

* The family A of x^{o(1)} queries is rich: it contains all subcube indicators (bit patterns), whose GF(2) span is
  everything (point = primality test). Expressivity is not the obstruction.
* **Linear adversary (strengthens the note's Prop. adv to arbitrary GF(2)-linear queries).** Let the algorithm ask
  q_p parity queries ⟨1_S, Q_i⟩ for arbitrary sets Q_i (any family!) and q_m membership queries, under the sole
  promise that S meets every H-window. Answer "even"/"no". Let U = [N,2N] minus queried points and the output y.
  Need E ⊆ U with Σ_{x∈E} col(x) = s := Σ_{x∈U} col(x) ∈ GF(2)^{q_p}; s lies in the column span, so some E of size
  ≤ rank ≤ q_p works. S = U \ E misses ≤ q_p + q_m + 1 points, so meets every H-window if q_p + q_m + 1 < H.
  Hence ≥ H − 1 queries. Mod M: E exists with |E| < D((Z/M)^{q_p}) (Davenport constant; = q_p(M−1)+1 for prime-power
  M), giving ≳ H/M. **So no choice of cheap query family breaks the even-total barrier without a number-theoretic
  input about the actual primes beyond gap bounds.** [R, on paper]
* Empirically the barrier is not felt: [N,2N] (N = 5·10^5) has an even count, the classes mod 3 and mod 4 are all
  even, but p ≡ 3 and p ≡ 7 (mod 8) are odd. Over 2000 random windows N ≤ 5·10^5, the first odd query in the
  sequence (total, classes mod 2,4,8,16,32) occurred at query 1 in 986, ≤ 9 in 1709, ≤ 41 in all 2000
  (oddquery_stat.py) — geometric, as for random parities.

## 4. Idea log
1. AP extension — works, trivial, [paper]; 2. characters — real ones useless mod 2, level sets work; 3. mod-k cost —
found the k² vs log k discrepancy, fixed partially with sopfr trick; 4. linear adversary — barrier is family-independent.
Next: (a) prove S(k) = (log k)^{O(1)} unconditionally (needs y-smooth c ≡ −1 mod k² with y = polylog k — this is
a smooth-numbers-in-APs statement; under GRH(now RH for Dirichlet L? only ζ is claimed) it might follow); (b) a
Lean description `apDescL` reusing PrimeDesc proofs (~100 lines).

## 5. Follow-up from lead (after first hand-back)

### 5.1 Prime patterns: twin primes, k-tuples, Sophie Germain, Goldbach, a²+1  [R on paper, N]
Conjoin j disjoint copies of primeDescL, copy i on variable m_i with the level-0 chain m_i·1 = a_i·m + b_i
(m_i·1 = m·a_i + b_i). Solutions = tuples of witness tuples, so count = Σ_m Π_i τ^<(m_i)C_L(m_i), and
parity is multiplicative: ≡ #{m ∈ I : all a_i m + b_i prime} (mod 2). Cut j·U + O(jn): same rate for fixed j,
x^{o(1)} for j = o(√log n). Instances: twins (1,0),(1,2); any admissible k-tuple; Sophie Germain (1,0),(2,1);
Goldbach G(2n) = #{p ≤ n : 2n−p prime} mod 2 (chain m + m' = 2n, comparison m ≤ n; the ordered count is ≡ [n prime]
by symmetry, so only the unordered one is informative); #{a ∈ [a1,a2] : a²+1 prime} mod 2 (m = a·a + 1, unique
witness a). patterns.py, X = 10^6: 200 random intervals per pattern, all 2n ≤ 2·10^4 plus 300 random Goldbach
values, 300 a²+1 ranges: 0 mismatches (patterns_1e6.out).
Novelty: TCH (arXiv 1009.3956 §1.1) treat π and π(x;a,q) mod 2 for q = O(N^{c/10}) — so small-q AP parity is
prior art in spirit; nothing on twins/Goldbach/tuples. Web searches for parity algorithms for twin-prime or
Goldbach counts found nothing (weak negative). TCH's 2^ω identity does not extend to products, so the statement
"parity of the twin-prime count in any interval in x^{o(1)}" looks new — but it is a one-line corollary.

### 5.2 Escape (B): rigid identities localised to [N,2N]  — verdict: dead as stated, collapses into (C)
* **Binomial / Legendre with a character.** Unique factorisation gives, for χ = (·/q) and any multiset S of
  integers with computable Π_{m∈S} χ(m/q^{v_q}): Σ_{p≠q, χ(p)=−1} h_S(p) ≡ [χ(Π S') = −1] (mod 2),
  h_S(p) = Σ_{m∈S} v_p(m). C(2N,N) (S = [1,2N] − 2·[1,N]) has h = 1 on (N,2N], but also h odd on
  (N/2,2N/3], (N/3,2N/5], … and on small primes: h(p) = ⌊2N/p⌋ − 2⌊N/p⌋ is 1-periodic in t = N/p, so every factorial
  ratio Π (α_i N)!^{c_i} repeats the window pattern at all scales. rigid.py (q=3, N ≤ 4000): identity holds always,
  but window parity equals the rigid bit only 50.5% of the time; contamination is spread over all scales
  (N=4000: 44/27/30/7/6 contaminating primes in (N/2,N],(N/4,N/2],(N/16,N/4],(√2N,N/16],(0,√2N]).
* **Why this is general.** Any such identity is linear in the prime indicator with a KNOWN value (that is what
  beats the deletion adversary: deleting primes breaks factorisation). It forces an odd window only if the
  non-window coefficients h_S(p) are all even — i.e. S is a multiplicative relation whose product is a square
  outside the window and carries an odd χ-weighted exponent on window primes. Exhibiting such S means exhibiting
  integers whose factorisation contains a window prime. With deterministic x^{o(1)} factoring, a single explicit
  integer of size x^{O(1)} (or bit length o(n√log n)) with a prime factor in [N,2N] already finishes. So (B) adds
  nothing to Polymath4 Problem 1 (factoring oracle + RH) = escape (C).
  Cancelling contamination by XOR-ing factorial "square waves" ⌊α t⌋ mod 2 appears to need as many waves as there
  are scales of t = N/p (up to N/2) — heuristic, not proved.
* **Zagier involution** (x²+4yz = n): gives #{x²+4y² = n} ≡ #{d | n : d ≡ n/d (4), …} (mod 2) — an identity between
  two cheap counts whose prime contribution is the same on both sides; forces no oddness. Dead.
* **Wilson** [(m−1)! ≡ −1 mod m]: (m−1)! mod m is not a cheap count (m-fold product). Dead on cost.
* **Kalai's question** (a_n with π([a_n,2a_n]) provably odd): no candidate; equivalent to p3's Conjecture PR type
  statements.
