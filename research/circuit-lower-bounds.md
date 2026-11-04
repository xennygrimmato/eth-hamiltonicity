# Circuit lower bounds from the 2026 ETH refutations: what follows, what is formalised, what is new

Status: analysis. No new Lean code yet. Sources were checked against the primary PDFs where marked [verified].

## 0. Summary

* **Anthropic's claim (paper l.143–147, 1171–1175; Lean `ENP.CorCircuits`):** some L ∈ E^NP has no circuits of size O(n).
  The proof uses only the δ-form (ETH is false). It gives "not O(n)", which is ω(n) infinitely often, but with **no
  explicit rate**.
* **What the *rate* gives** (new, unless someone else has stated it): Anthropic's Corollary 11 bound,
  #k-SAT in `min(2^{C·k·m/√log m}, 2^{C·k²·n·loglog n/√log n})`, put into the same Williams argument gives
  **E^NP ⊄ SIZE(ε·n·√log n)** (i.o., full binary basis, non-uniform) for an absolute ε > 0 (roughly ε ≈ 1/(10³·C)).
  OpenAI's `ρ(N) = N(lnln N)²/√ln N` gives the weaker **E^NP ⊄ SIZE(ε·n·√log n/(loglog n)²)**.
* This is the first **explicit superlinear** rate for E^NP over the full basis. Before 2026 the best was 3.1n − o(n)
  [Li–Yang STOC'22], and near-maximum bounds were known only from S₂E upward [CHR24, Li24].
  The *qualitative* "not O(n)" is Anthropic's own claim. The improvement is the rate n√log n.
* **It cannot be pushed** to NEXP or NQP, to poly-size, or beyond Θ(n·√log n) with these algorithms. Reasons are in §3.
* **Lean:** the module is **not** parametric in the SAT time. `2^{δN}` and `c₀·(m+1)` are hard-wired. The changes needed
  are local (5 places, §4).

## 1. What Anthropic's Lean proves (exactly)

Statement file `proof/statements/CircuitLowerBoundStatement.lean` (namespace `ENP`):
* **Basis:** `Gate` = *any* of the 16 functions {0,1}²→{0,1} plus two wire indices (the full binary basis B₂).
  **Size** = number of gates (inputs not counted). Output = last wire. Non-uniform: one circuit per n.
* `HasCircuits L s := ∀ n, ∃ C, C.length ≤ s n ∧ ∀ x, |x| = n → (eval C x ↔ L x)` (already parametric in s).
* `HasLinearCircuits L := ∃ c, HasCircuits L (fun n => c*(n+1))`.
* **Class:** `InENP L`: a Mathlib `FinTM2` oracle machine with finite alphabets, a SAT oracle (CNF, unary
  encoding `encCnf`), and running time `2^{c(|x|+1)}`, where each query costs 1 step. `InENP'` is the restart-protocol form.
* **Theorem:** `CorCircuits : ∃ L, InENP L ∧ ¬HasLinearCircuits L`, and `CorCircuits'` (the InENP' form).
  `CircuitLowerBoundInfinitelyOftenStatement.lean`: `CorCircuitsInf` (for every c, infinitely many n with no
  c(n+1)-gate circuit).
* Proof assembly:
  * `consequences/CircuitLowerBound/Main.lean`: `no_linear_circuits` (l.76), `corCircuits_of` (l.142).
  * `Closed.lean`: `stTab`, `stForm`, `stENP'` (`stENP'_of stCertSched stCertTabF stFlip`), and `stENP := stRestart L0 stENP'`.
  * `StAlg` (Interfaces.lean) is proved in `networks/Eight/Cor/ENP.lean: Eight.stAlg_of` from `StEngine`
    (Corollary 6 for stepped machines, **δ-form**: `Serves E k δ c`, time `c·2^{δN}`).
  * The end theorems are in `consequences/FromPrinted/Circuits.lean` (`circuits`, `circuitsFrom`).
* `consequences/SizeCircuit/` is **not** about circuit lower bounds. It is Corollary 7 (graph problems): CNFs with
  O(n) variables, δ/(a+1).
* **Proof shape (Williams [Wil13, Thm 6.1], self-contained):**
  * The language is `L0` (greedy lexicographically-first satisfying assignment of `Phi m`, which is in E^NP).
  * `Phi m` is a succinct tableau CNF (`tabF`) whose variables have m bits and whose time is `2^{bt}` with
    bt ≈ m/2.
  * Lazy diagonalisation runs along chains m = 2^a(2s+1) up to `top a = 2^{2^{2^a}}`, so no PCP is used.
  * The SAT step: guess a witness circuit C (m inputs, ≤ c₀(m+1) gates), then build the 3-CNF "some clause is
    violated" (`StForm`: Tseitin of 3 copies of C plus the clause circuit of size a₀(m+1)+g(e)). It has
    `Nv ≤ 3|C| + a₀(m+1) + g e` variables and 4 clauses per gate + 1 (`Circ/Form.lean`, `tseitin`).
  * Run #3-SAT on it with δ = 1/(32(3c₀+a₀+1)). `Alg/Time.lean: exists_threshold` makes the total time ≤ 2^{m/8}.
  * **Slack is a constant factor in the exponent** (2^{m/8} vs tableau time 2^{bt}), not just 2^n/n^{ω(1)}.

## 2. Quantitative Williams theorem and the derivation

**Primary statements [verified]:**
* [Wil13] = Williams, *Improving exhaustive search implies superpolynomial lower bounds*, STOC'10 / SICOMP 2013
  (PDF people.csail.mit.edu/rrw/improved-algs-lbs2.pdf):
  * **Thm 1.1:** if CircuitSAT on n vars and n^k gates is in 2^n·poly(n^k)/s(n), with s superpolynomial, for all
    k, then NEXP ⊄ P/poly.
  * **Thm 1.2:** if CircuitSAT is in 2^{(1−δ)n}poly(m), then E^NP ⊄ SIZE(2^{εn}).
  * **Lemma 3.2 (folklore):** E^NP ⊆ SIZE(S) ⇒ NTIME[2^n] has universal witness circuits of size S. This is
    where E^NP, rather than NEXP, enters: no easy-witness lemma is needed.
  * **Thm 6.1:** "If ETH is false then E^NP does not have linear size circuits."
    * Sketch: the tableau has 2^{3n} cells. The witness circuit has cn gates. The check circuit D has O(cn)
      wires and 3n+O(1) inputs. 3SAT in 2^{εn} for all ε gives NTIME[2^n] ⊆ NTIME[2^{εn}].
    * The hypothesis is decision 3SAT in 2^{δ·#vars} for every δ, applied via Tseitin. The slack is exponential.
* [JMV15] Jahanjou–Miles–Viola, *Local reductions*, ICALP'15 (arXiv 1311.3171):
  * **Thm 1:** NTIME(T) reduces to a 3CNF of size T·polylog T whose clause map is NC0.
  * **Cor 2(1):** if SAT of *linear-size circuits* is in 2^n/n^{ω(1)}, then E^NP ⊄ linear size.
  * **Cor 3(1′):** ¬ETH suffices.
  * Proof (§6): guess C_x on ℓ = n+O(log n) inputs. The check circuit C_x'' has 3|C_x| + O(ℓ) gates in the same
    class. A SAT time of 2^ℓ/ℓ^{ω(1)} = o(2^n) contradicts the NTIME hierarchy [Žák83].
  * They note that "the proofs provide a close correspondence between the running time for satisfiability and the
    parameters of the circuit class".
* [BV14] Ben-Sasson–Viola, *Short PCPs with projection queries* (quoted in JMV §1): 3SAT in c^n with c < 2^{1/10}
  ⇒ E^NP ⊄ SIZE(3n), full basis. This is the constant-level quantitative instance.
* [Wil14b, Thm 5.8] (JACM 2014) is the same E^NP/universal-witness mechanism. I did not re-check the theorem number.

**General quantitative form (both routes):** let s(n) ≥ n with s(n)log s(n) = 2^{o(n)}. Then E^NP ⊄ SIZE(s) if
CircuitSAT for circuits with ℓ = O(n) inputs and size 3s(ℓ)+O(ℓ) runs in time
* 2^ℓ/ℓ^{ω(1)} (JMV route, quasi-linear PCP), or
* 2^{γℓ} for a suitable fixed γ<1 (Williams / Lean route, exponential slack).

Decision SAT is enough; counting is not needed. By Tseitin (B₂ gates: 1 variable and ≤ 4 width-3 clauses per gate),
it suffices that **3-SAT on M = 4·(3s+O(ℓ)) clauses** (N = 3s+O(ℓ) variables) runs in that time.

**Instantiation (Lean route, constants as in `exists_threshold`):** take s(m) = ε(m+1)√log₂(m+2). Then
* Nv ≤ 3s + a₀(m+1) + g(e) and M ≤ 4Nv+1, so M ≤ 12ε·m√log m·(1+o(1)) + O(m).
* Since x/√log x is increasing, the Anthropic m-branch with k = 3 gives
  `T ≤ C·2^{3C·M/√log M} ≤ 2^{36Cε·m + O(m/√log m)}`.
* The circuit encoding is poly(m, s) = 2^{o(m)}.
* We need T·poly ≤ 2^{m/8}. The Lean split is 2^{m/32} per factor, so it suffices that 36·C·ε < 1/32, i.e.
  **ε = 1/(1200·C)** works.
* Result: **E^NP ⊄ SIZE(ε·n√log n)** (i.o.).
* With the n-branch (`k²n·loglog n/√log n`, N = Nv) one gets only n√log n/loglog n. Use the m-branch.
* **OpenAI** (`exact_count_and_sat`, ρ(N) = N(lnlnN)²/√lnN, in variables): need C₂·ρ(3s+O(m)) ≤ m/40, so
  **s = ε·n√log n/(loglog n)²**.

**Strength:**
* The result implies Anthropic's "not O(n)" and is strictly more informative (an explicit rate, ≥ ε n√log n
  infinitely often).
* The constant ε is non-explicit, because C is existential in Lean (`MainTheoremAllOccur`: ∃ M C) and in the paper.
  So the result is "∃ε>0", not "for every c, c·n√log n". A rate of 2^{o(M/√log M)} would be needed for every c.

**Known landscape (full binary basis):**
* E^NP: 3.1n − o(n) [Li–Yang, STOC'22]. Earlier: 3.011n for affine dispersers [FGHK16], which are in P. A
  superlinear bound for E^NP was open; Williams writes "linear size circuit lower bounds are not known for this
  class".
* NEXP vs linear size: open, and still open after 2026 (no easy-witness lemma at linear size; JMV pose this).
* Σ₂E ⊄ i.o.-SIZE(2^n/n) [Chen–Hirahara–Ren STOC'24]; S₂E likewise [Li STOC'24]. E^NP ⊆ S₂E.
* Kannan: Σ₂P ∩ Π₂P ⊄ SIZE(n^k) for each k. Fixed-polynomial bounds are known for S₂P, ZPP^NP, MA/1 and PP.
  None of these classes is known to lie inside E^NP, and E^NP ⊄ SIZE(n^k) for fixed k > 1 is **open**.

So E^NP ⊄ SIZE(ε n√log n) is the first ω(n)-with-explicit-rate bound for a class below S₂E over B₂. It is
unconditional to the extent Theorem 1 / Corollary 11 are (they are machine-checked by Anthropic).

## 3. Can one go further?

* **Larger s for E^NP:** the method converts a 3SAT rate 2^{M/g(M)} into s = εn·g(n). Tseitin and the check
  circuit (3s + O(n)) are already linear, so the only lever is the rate.
  * n log n needs 3SAT in 2^{O(M/log M)}.
  * n^{1+ε} needs 2^{M^{1−ε'}}.
  * Neither algorithm does this.
* **NEXP / NQP (smaller classes):** these need an easy-witness lemma.
  * IKW and Murray–Williams work for poly size, and MW's NQP lemma loses a polynomial in size.
  * After the loss one needs SAT for poly(n)-size circuits in 2^n/n^{ω(1)}. 2^{O(s/√log s)} with s = n^k is
    useless. So there are **no NEXP/NQP consequences**. Linear-size easy witnesses are JMV's open problem.
* **Counting power:** #SAT does not help here. E^NP uses the NP oracle only to fix the lexicographically-first
  witness, and the check is a decision question.
  * Williams-type #SAT → NEXP results (ACC, THR∘THR, Chen–Ren average case) again need poly size.
  * Average-case and approximation versions for E^NP at size n√log n would follow if the CLW / Chen–Ren machinery
    had only O(1)·s overhead. It does not obviously (PCPs, XOR lemmas).
* **Almost-everywhere (Chen–Lyu–Williams FOCS'20, ECCC TR20-150):** E^NP ⊄ i.o.-C via a constructive NTIME
  hierarchy [Fortnow–Santhanam].
  * The SAT step for size n√log n would cost only 2^{O(εn)}, which is well within a "2^{(1−δ)n}" hypothesis.
  * The open point is whether their reduction keeps the check circuit at O(s) gates (they use PCPs with polylog
    overhead, which would eat the √log). **Unverified; plausible with JMV/BV14 local reductions; worth a careful
    check.**
* **Restricted classes:**
  * Formulas: Tseitin is linear, so formula size n√log n is implied and is weaker than the known n^{3−o(1)} for P.
  * Depth-2 threshold, series-parallel and log-depth linear size (Valiant): already implied by the general bound, or
    weaker than known results.
  * No restricted class gains, since the algorithm is a CNF algorithm.
* **P^NP:** Williams' P^NP variant needs SAT for circuits with 2^n gates, so it is out of reach.

## 4. Lean plan for `E^NP ⊄ SIZE(ε n√log n)`

The module is **not** parametric in the SAT time. The size function and the rate enter at exactly these places:
1. `CircuitLowerBound.StAlg` (Interfaces.lean): `C.length ≤ c₀ * (m + 1)` and the conclusion
   `Acc N m (2^(m/8))`. Generalise to `C.length ≤ s m` for `s : ℕ → ℕ`, quantified as ∃ε.
2. `no_linear_circuits` (Main.lean l.76): it only uses `hc (p s)` to get a circuit of size `≤ c₀*(p s+1)`. It goes
   through verbatim for `¬HasCircuits L0 s'`. This is the cheapest change.
3. `Alg.EngineOK` (Alg/Machine.lean l.247), `runs_algo`: time `c·2^{δN}` becomes `c·2^{t(N, |ψ|)}`.
4. `StForm` / `Alg.FormOK` (InterfacesPolyT.lean, Alg/Machine.lean l.118): add the clause bound
   `ψ.length ≤ 4·Nv + 1`. This is a counting lemma about `tseitin` (Circ/Form.lean, 4 clauses per gate, `gateCl`).
5. `Alg/Time.lean: exists_threshold` (l.69): the δ-arithmetic, where the size function meets the rate. It needs a
   new real-analysis lemma:
   * Hypotheses: n ≤ ε(m+1)√log(m+2), Nv ≤ 3n + a₀(m+1) + G, M ≤ 4Nv+1, T ≤ cE·2^{C·3M/√log₂ M}.
   * Conclusion: q(T+1)·base^q ≤ 2^{m/8}.
   * Uses monotonicity of x/√log x and ε := 1/(1200·C).
   * Finally `Eight.stAlg_of` (networks/Eight/Cor/ENP.lean l.81) chooses ε instead of δ.
6. **Engine:** the rate is available as `Tied.TopM` (rates/GeneralPieces/Tied/Defs.lean l.74).
   * It provides `AM` and `eM`, both PolyT, with `AM (enc k φ, pad) = count` once `|pad| ≥ 2^{eM}`, and the rate
     `eM ≤ G·k·m·r(m)` with r = rPow(1/2) (`ClauseBoundStatement.TargetSqrt`; `MainTheoremAllOccur` is proved via
     `maintheorem/NamesInOrder/Main.lean`).
   * The stepped engine for `algo` is "compute eM, build a pad of 2^{eM} units, call AM". It needs an adapter from
     `Prog.Fml` with N variables to `Sat3.CNF n` with AllOccur (rename occurring variables; decision only, so free
     variables are harmless).
7. New statement: `∃ L ε, 0 < ε ∧ InENP L ∧ ¬HasCircuits L (fun n => ⌊ε*(n+1)*√(logb 2 (n+2))⌋₊)`, with ε
   existential (C is existential).

Estimated effort: items 2–4 are small. Item 5 is moderate real analysis. Item 6 is the main work (stepped adapter
plus the PolyT pad builder). The rest of the module (tables, chains, L0, E^NP membership) is reused unchanged.

## Sources
* Williams, *Improving exhaustive search implies superpolynomial lower bounds*, SICOMP 42(3) 2013; PDF
  https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf. Thm 1.1, 1.2, Lemma 3.2, Thm 6.1 (§6). [verified]
* Jahanjou, Miles, Viola, *Local reductions*, ICALP 2015, https://arxiv.org/abs/1311.3171. Thm 1, Cor 2, Cor 3,
  §6 proof; BV14 quoted in §1. [verified]
* Ben-Sasson, Viola, *Short PCPs with projection queries*, ICALP 2014 (via JMV). [secondary]
* Chen, Lyu, Williams, *Almost-everywhere circuit lower bounds from non-trivial derandomization*, FOCS 2020,
  ECCC TR20-150. [abstract checked]
* Li, Yang, *3.1n − o(n) circuit lower bounds for explicit functions*, STOC 2022. Chen, Hirahara, Ren, STOC 2024. Li,
  STOC 2024. Murray, Williams, STOC 2018. [as cited in Anthropic paper l.146–147; not re-fetched]
* Anthropic paper (scratchpad paper.txt l.45–56, 143–147, 1171–1175, Cor 11 l.2098–2103); Lean files as named above.
