# The permanent modulo p and modulo p^k: mechanism, accounting, verdict on route A(i)

29 Oct 2026. Follows `wild-ideas.md` (F1, F2, F3, §A(i)) and `permanent-attack.md` (broadcast/assignment
classes, §8). Scripts: `scripts/modp_*.py`, outputs `scripts/modp_*.out`; every identity used below is
checked in exact integer arithmetic on random 0/1 matrices, n ≤ 8. lg = log₂.

## 0. Summary

* **Mechanism (§2).** Every known char-p saving comes from one of: (M1) vanishing of shifted-Ryser terms mod p
  (a term dies if one of its n row factors is ≡ 0; random shifts kill all but (1−1/p)ⁿ of them; BW list the
  survivors as dissimilar pairs: 2^{n−Ω(n/p)}); (M2) the same mod p^k (a term dies if ≥ k factors are ≡ 0 mod p;
  BHL: 2ⁿ/exp{Ω(γ²n/(p lg p))}, γ = 1 − kp/n, **only for kp < n**); (M3) Valiant's equal-row elimination, which
  closes only for p = 2 (n^{k+O(1)} for 2^k); (M4, new here, verified) per ≡ 0 mod p when rank_p(A)(p−1) < n.
  The controlling parameter is the density 1/p of zero residues: saving Θ(n/p), zero at p ≥ n and at kp ≥ n.
* **Budget (§3).** CRT needs primes up to ≈ 0.9 n ln n. The vanishing regimes of *all* primes < n carry
  lg n! − 1.09n bits (Legendre), so primes ≥ n with zero saving are unavoidable. **F1 extends to any modulus
  M with lg M ≥ lg n! + 2** (Lemma B4): small p with k ≈ n lg n/lg p needs ≥ n lg n − O(n) #SAT variables,
  like the integers.
* **Encodings (§4).** Ryser mod p via Tseitin counters: N = Θ(n² lg p). The Fourier form (4.1) has only
  N = n(1+⌈lg p⌉) variables and arity 2, but n² nonzero pair weights; unweighted, it is a sparse CNF plus **one
  dense quadratic congruence mod p** (4.2). For p = 2 it is a quadratic Gauss sum (per ≡ det); for odd p the
  only non-affine parts are 2n unary weights (a Clifford-plus-magic shape). As a network, c_ab = ⌈lg p⌉·rank_p
  of the off-diagonal blocks: U ≈ 2gn lg p, P ≈ 2n lg p, inadmissible for every p. F_p cut ranks of dense rows
  equal the rational ones (177/180 cases): **a dense row is exactly as wide mod p as over Z.**
* **Key question (§5): no.** per mod p^k with small p and k ≈ n lg n/lg p is the integer permanent; M1/M2 stop
  at kp = n, M3 costs n^{Θ(1)} per digit (2^{Θ(n lg² n)} in total), (B4) charges ≥ 1 variable per digit, and the
  engine is ring-agnostic, so the broadcast/assignment barriers apply unchanged.
* **Verdict (§6).** No algorithm; a precise obstruction plus three missing primitives that would break it.

Scripts: `modp_identities.py` (identities (2.1)–(2.3), (4.1)), `modp_affine.py` ((4.2), Gauss sum for p = 2,
non-affinity of ĥ), `modp_cutrank.py` (F_p vs Q cut ranks), `modp_budget.py` (CRT/p-adic budget, per values).
All print PASS or tables; outputs in `scripts/modp_*.out`.

---------------------------------------------------------------------------------------------------

## 1. What is known, with exact statements

| result | statement | mechanism |
|---|---|---|
| per ≡ det (mod 2) | poly | signs vanish in char 2 |
| Valiant 1979 (TCS 8) | per mod 2^k in O(n^{4k}) (often quoted 4k−3) | row elimination; pairs of equal rows give a factor 2 |
| Björklund–Husfeldt–Lyckberg, IPL 125 (2017) 20–25 | per mod 2^k in **n^{k+O(1)}**; for odd p with kp < n, per mod p^k in **2^n / exp{Ω(γ² n/(p lg p))}**, γ = 1 − kp/n (Las Vegas) | Ryser + Bax–Franklin random shift + tabulation |
| BHL corollary (CRT) | per in 2^n/exp{Ω(δ² n/(β^{1/(1−δ)} lg β))} **provided \|per A\| ≤ βⁿ and β ≤ (144δn)^{1−δ}** | CRT over primes ≲ β^{1/(1−δ)} |
| Björklund–Williams, ICALP 2019 | per over any finite ring with r ≤ n elements, deterministic 2^{n−Ω(n/r)}; so per mod p in 2^{n−Ω(n/p)} | Ryser + listing pairs of "dissimilar" vectors |
| Björklund 2012 (arXiv 1211.0391); Björklund–Kaski–Williams (Algorithmica 2019); B. Li, arXiv 2309.15422 = ICALP 2026 art. 138 | per over F_q in 2^{n−Ω(√(n/lg n))}, 2^{n−Ω(√(n/lglg n))}, **2^{n−Ω(√n)}·q^{O(1)}** (Li); same for integers by CRT, hafnian, directed #HC | self-reduction to 2^{n−k}poly(n) weighted k×k instances, k = Θ(√n), tabulation on Kakeya sets + Hasse derivatives |
| Valiant 1979 | per mod p is Mod_pP-hard for every odd p | — |

Two remarks that matter for us.

* The BHL CRT corollary is explicitly conditioned on |per A| ≤ βⁿ with β ≤ (144δn)^{1−δ}, i.e. on per having
  only n lg β ≪ n lg n bits. A dense 0/1 matrix has per up to n! ≈ (n/e)ⁿ, β ≈ n/e, outside the hypothesis.
  So BHL themselves record the obstruction we meet below: **the char-p saving pays only for ≈ n·lg P bits of
  information when primes up to P are used, and a dense permanent has n lg n bits.**
* Nothing in the list beats 2^{n−Ω(n/p)} for any fixed odd p. per mod 3 in 2^{(1−ε)n} for a fixed ε > 0 is
  known (BW: ε = Ω(1/3)), per mod 3 in 2^{o(n)} is not.

---------------------------------------------------------------------------------------------------

## 2. Why characteristic p (and p^k) saves: the mechanism in one page

Everything starts from the **shifted Ryser formula** (Nijenhuis–Wilf, Bax–Franklin): for every w ∈ Zⁿ,

```
per(A) = Σ_{S⊆[n]} (−1)^{n−|S|} Π_i ( w_i + r_i(S) ),    r_i(S) = Σ_{j∈S} A_ij.          (2.1)
```

(Expand Π_i(w_i + r_i) = Σ_T Π_{i∉T} w_i Π_{i∈T} r_i; the S-sum of Π_{i∈T} r_i(S) counts maps T → [n] onto [n],
which is 0 for |T| < n.)

**(M1) Vanishing of terms, mod p (Bax–Franklin / BW).** Mod p, a term of (2.1) is 0 as soon as one factor
w_i + r_i(S) ≡ 0. For w uniform in F_pⁿ and fixed S the n factors are independent uniform residues, so a
term survives with probability (1 − 1/p)ⁿ ≈ e^{−n/p}. In expectation only 2ⁿ(1−1/p)ⁿ ≈ 2ⁿe^{−n/p} terms are nonzero; the work is to
*enumerate only those* without touching the others. Split the columns in halves, S = S_L ⊔ S_R, so the
factor vector is u(S_L) + v(S_R) + w ∈ F_pⁿ, and a term survives iff u + v + w has no zero coordinate
("dissimilar pairs", BW). Listing the dissimilar pairs (by a branching/tabulation over the coordinates)
costs about the number of surviving pairs plus overhead; the exponent saving is **Ω(n/p)** (BW,
deterministic) or Ω(n/(p lg p)) (BHL).

**(M2) Vanishing of terms, mod p^k.** Mod p^k a term is 0 as soon as ≥ k of its factors are ≡ 0 mod p
(each such factor contributes a p to the valuation). With random w the number Z_w(S) of zero factors is
Bin(n, 1/p), mean n/p; for k = (1−γ)n/p Chernoff gives Pr[Z_w(S) < k] = exp(−Ω(γ²n/p)), whence BHL's
2ⁿ/exp{Ω(γ²n/(p lg p))}. **The saving disappears at kp = n**: beyond it a typical term has fewer than k
zero factors and nothing vanishes.

```
per(A) ≡ Σ_{S : Z_w(S) < k} (−1)^{n−|S|} Π_i (w_i + r_i(S))     (mod p^k),   Z_w(S) = #{i : p | w_i + r_i(S)}.   (2.2)
```

**(M3) Repeated rows (Valiant's mechanism, the only "elimination" one).** per is a symmetric multilinear
function of its rows, so per(…, r + c·r', …, r', …) = per(A) + c·per(…, r', …, r', …), and a matrix with a row
repeated m times has per divisible by m! (σ and σ∘τ for τ permuting the equal rows give equal products).
In char p, per(v^{(p)}, rest) ≡ 0: in the polynomial picture per = [z₁⋯z_n] Π_i ⟨r_i, z⟩, and
⟨v,z⟩^p = ⟨v, z^p⟩ (Frobenius) has no multilinear monomial. For **p = 2** two equal rows already give a factor
2, so each elimination step pushes the error one 2-adic digit up; depth-k recursion with poly branching
gives n^{O(k)}. For **odd p** a factor p needs p equal rows, the error term of a single row operation is a
*unit* multiple of a smaller-looking but equally hard permanent, and the recursion does not close — which
is the content of Mod_pP-hardness.

**(M4) Low rank over F_p (a fact we use as a test, new to our notes).** If A ≡ UVᵀ (mod p) with U, V ∈ F_p^{n×r},
then mod p only exponent vectors α ∈ [0, p−1]^r survive in Barvinok's formula (α! ≡ 0 otherwise):

```
per(A) ≡ Σ_{α ∈ [0,p−1]^r, |α|=n} α! · [x^α] Π_i (u_i·x) · [y^α] Π_j (v_j·y)   (mod p),                     (2.3)
```

so **per(A) ≡ 0 (mod p) whenever rank_p(A)·(p−1) < n**, and per mod p costs ≤ n²·p^{r}·poly in general. For a
random 0/1 matrix rank_p(A) = n − O(1), so this buys nothing generically; it does show that "char p" is
quantitatively a statement about *degree ≤ p−1 per coordinate*: the truncated algebra F_p[x]/(x_l^p) has
dimension p^r, and F2 applies to it unchanged.

**The parameter.** In (M1)/(M2) the saving is controlled by the density 1/p of zero residues: saving
Θ(n/p) (up to lg p), at most Θ(k)·lg-factors of "free" vanishing digits mod p^k, and it is **zero for p ≥ n**
and for kp ≥ n. In (M3) it is controlled by p through "how many equal rows make a factor p": 2 for p = 2,
p otherwise.

Verified (`modp_identities.py`, ALL PASS): (2.1) for random w ∈ [−5,5]ⁿ, n ≤ 7; (2.2) for (p,k) ∈ {(3,1..4),
(5,1), (7,1), (2,3), (2,5)} at n = 7, 8, with surviving fractions matching Pr[Bin(n,1/p) < k] (e.g. p = 3, k = 1:
0.027 vs (2/3)⁸ = 0.039; p = 3, k = 4 (kp/n = 1.5): 0.75 of all terms survive); m equal rows ⇒ m! | per, n ≤ 7;
(2.3) and the vanishing rank_p(A)(p−1) < n ⇒ per ≡ 0 for p ∈ {2,3,5}, n ≤ 8.

---------------------------------------------------------------------------------------------------

## 3. The information budget of every CRT / p-adic scheme

`modp_budget.py`. lg n! = n lg n − 1.443n + O(lg n) bits must be recovered.

**(B1) Plain CRT over primes.** Σ_{p≤P} lg p ≥ lg n! + 1 needs P ≈ 0.86–0.90·n ln n (n = 64 … 16384: P = 229,
1217, 6197, 30211, 142963; 50 … 13261 primes). As in `wild-ideas.md`, ≈ n primes up to ≈ n ln n.

**(B2) The vanishing regime carries slightly too little.** In (M1)/(M2) a prime p pays only while kp < n,
i.e. it yields at most (⌈n/p⌉ − 1)·lg p bits. Summed over **all** primes p < n this is, by Legendre's formula
lg n! = Σ_p Σ_e ⌊n/p^e⌋ lg p,

```
Σ_{p<n} ⌊(n−1)/p⌋ lg p  =  lg n! − (Σ_p lg p /(p(p−1)) + o(1))·n  ≈  lg n! − 1.09 n        (printed: deficit 0.85n, 0.96n, 1.01n, 1.05n, 1.07n)
```

So even if every prime below n were run in its vanishing regime, ≈ 1.09n bits would still be missing and
would have to come from primes p ≥ n, where (M1)/(M2) give nothing (γ ≤ 0, saving n/(p lg p) ≤ 1/lg n). And
the vanishing regime is not cheap anyway: the best cost there is 2^{n−Θ(n/p)} even for p = 3.

**(B3) Single prime power, small p.** per mod p^k with p^k > n! is the integer permanent; k = ⌈lg(n!+1)/lg p⌉.
For p = 2, k = 297, 1685, 8771, 43252, 205749 at n = 64 … 16384, and the best known cost n^{k+O(1)} (BHL) has
lg(cost)/n = 27.8, 52.7, 85.7, 126.7, 175.8 ≈ lg² n. Per mod 2^k is 2^{o(n)} exactly when k = o(n/lg n): this
is the "bottom o(n/lg n) bits" of `wild-ideas.md`, short of the needed n lg n bits by a factor lg² n.

**(B4) Lemma (F1 for a modulus M).** Suppose per(A) ≡ Σ_{t≤T} w_t·#SAT(F_t) (mod M) for all 0/1 A, |w_t| ≤ 2^W,
F_t on N_t variables, N = max N_t. Then

```
N ≥ min(lg M − 2, lg n!) − W − lg T.
```

*Proof.* If N < lg M − 2 − W − lg T, the right side lies in (−M/4, M/4) and so does per(A) ∈ [0, n!] once
lg M ≥ lg n! + 2; two integers in (−M/4, M/4) that are congruent mod M are equal, so the identity holds over Z
and F1 gives N ≥ lg n! − W − lg T. If lg M < lg n! + 2 the claim is the first case of the minimum. ∎
More generally N ≥ lg R_M − W − lg T − 1 where R_M is the number of residues per hits mod M (the right side
takes ≤ 2T2^{W+N} + 1 values); per hits every integer in [0, 2^{n−1}] (checked exhaustively n ≤ 4, sampled n = 5),
so R_M = M for lg M ≤ n − 1, and heuristically R_M ≈ M up to lg M ≈ lg n!.

Consequences. (a) **"Small p, k ≈ n lg n/lg p" is dead for every plain #SAT encoding**: it needs
N ≥ n lg n − 1.45n − W − lg T, exactly as for the integer permanent; under the Lean N-bound that is
2^{Ω(n√lg n)}. (b) A p-adic or CRT scheme that respects entropy must split the n lg n bits over many coprime
moduli, each carrying at most b(n) bits, where b(n) is the largest N the N-bound can afford in 2^{o(n)}:
b(n) = o(n√lg n/(k²(lg lg n)²)). Hence **≥ lg n!/b(n) = ω(√lg n (lg lg n)²) distinct primes**, and with
b = n√lg n/(lglg n)² (constant 1) at n = 2^{10} … 2^{40}: ≥ 30 … 173 moduli, primes up to 113 … 1031, and the
largest prime would need k_P·P/n = 4.7 … 23 — **far outside the vanishing regime kp < n**. (c) For networks
with exponential weights (the engine's B-bit tables) F1 does not apply, so the entropy budget is not the
obstruction there; §4 is.

---------------------------------------------------------------------------------------------------

## 4. Char-p encodings and their exact accounting (task 2)

Three encodings; all verified (`modp_identities.py` (e), `modp_affine.py`, `modp_cutrank.py`).

**(E-R) Ryser mod p as #k-SAT mod p (Tseitin counters).** Variables x = 1_S (n bits); per row a mod-p counter
along its support (≈ n/2 positions for density ½, ⌈lg p⌉ bits per state) and ⌈lg p⌉ bits to realise the
weight r_i mod p as a count (#{v < r_i} = r_i):

```
N ≈ n + n(n/2 + 1)⌈lg p⌉ = Θ(n² lg p),   k = 2⌈lg p⌉ + 1,   m ≈ (n²/2)·2^{2⌈lg p⌉+1}.
Lean N-bound exponent ≈ C·k²N(lglgN)²/√lgN ≈ 2C⌈lg p⌉³ n²(lg lg n)²/√lg n;   m-bound ≈ C k m/√lg m ≈ C' n² p² lg p/√lg n.
```

Both are ≫ n for every p ≥ 2. (The (M1)/(M2) restriction to {S : Z_w(S) < k} adds one more arity-n
threshold constraint and changes nothing.)

**(E-F) Fourier / 2-local form.** With h(r) = r mod p and ĥ(t) = p^{−1}Σ_y y ζ^{−ty} (ζ = e^{2πi/p}),

```
per(A) ≡ X := Σ_{s∈{0,1}ⁿ} Σ_{t∈Z_pⁿ} (−1)^{n−|s|} Π_i ĥ(t_i) · Π_{i,j} ζ^{t_i A_ij s_j}     (mod p),         (4.1)
```

an X ∈ Z computed by integer arithmetic in Z[ζ] or in F_q, q ≡ 1 (mod p). **N = n(1 + ⌈lg p⌉) variables, arity 2,
linear in n for fixed p** — the first char-p encoding with O(n lg p) variables. But the n² pair weights
ζ^{t_i A_ij s_j} are all nonzero, the interaction graph is K_{n,n}, and there is nothing to sparsify. Turned into
unweighted counting it is

```
p^n X = Σ_{c∈Z_p} ζ^c N_c,   N_c = #{ x ∈ {0,1}^{N'} : C_loc(x),  Q(x) ≡ c (mod p) }   (signed by |s| mod 2),     (4.2)
N' = n(1 + 3⌈lg p⌉),   C_loc = 2n constraints of arity O(lg p)  (t_i, y_i < p;  v_i < y_i),
Q(x) = Σ_{i,j} t_i A_ij s_j − Σ_i t_i y_i   with ≈ n²⌈lg p⌉ + n⌈lg p⌉² Boolean monomials,
```

i.e. **a sparse k-CNF plus ONE dense quadratic congruence mod p** (`modp_affine.py` (b) checks
Σ_c ζ^c N_c = pⁿX exactly, n ≤ 5, p ∈ {3,5}). For p = 2 the unary weight is ĥ(t) = ½(−1)^t and (4.1) is the
quadratic Gauss sum X = 2^{−n}Σ_{s,t∈F_2ⁿ}(−1)^{n−|s|+|t|+tᵀAs}, computable in poly time from the rank and Arf
invariant of a quadratic form (`modp_affine.py` (a), n ≤ 7): **this is per ≡ det (mod 2) seen as an affine
(Clifford-type) exponential sum.** For odd p the only non-affine ingredients are *unary*: ĥ (|ĥ| is not
constant on its support: p = 3: 1, 0.577, 0.577; `modp_affine.py` (c)) and the Boolean domain {0,1} ⊂ Z_p of s.
So per mod p = ⟨dense affine phase | non-affine unary weights^{⊗2n}⟩, the same shape as strong simulation of a
Clifford circuit fed with 2n magic qudits: its cost is the **affine (stabilizer) rank χ of ĥ^{⊗n} ⊗ 1_{\{0,1\}}^{⊗n}**
times poly. χ ≤ 2ⁿ trivially (= Ryser); 2^{o(n)} would give per mod p in 2^{o(n)}; the best known lower bounds
on stabilizer ranks of magic tensor powers are Ω(n) (Peleg–Shpilka–Volk, ITCS 2022), so nothing is excluded
and nothing is known.

**(E-N) As a network for the engine.** Put t_{R_a} and s_{C_a} at node a (g nodes, |R_a| = |C_a| = n/g). The pair
factor ζ^{t_{R_a}ᵀA[R_a,C_b]s_{C_b}} depends on t only through A[R_a,C_b]ᵀt ∈ F_p^{rank}, so

```
c_ab = ⌈lg p⌉·( rank_p A[R_a,C_b] + rank_p A[R_b,C_a] ),    U = 2⌈lg p⌉ Σ_{a≠b} rank_p A[R_a,C_b],    P_a = ⌈lg p⌉ Σ_{b≠a}(…),
tables 2^{(n/g)(1+⌈lg p⌉)}.
```

For a random 0/1 matrix rank_p A[R_a,C_b] = n/g − O(1), so P_a ≈ 2n⌈lg p⌉ and U ≈ 2gn⌈lg p⌉: **inadmissible
(P ≤ n/K⁷ fails) for every p**. The matching lower bound: the complex rank of [ζ^{tᵀMs}]_{t∈Z_p^{|R_a|}, s∈{0,1}^q}
for a random 0/1 block M is close to 2^{min(q, |R_a| lg p)} (p = 3, |R_a| = q = 4: 16, 16, 12, 12 of 16;
`modp_cutrank.py` (3)), so c_ab ≳ n/g is forced: this is the broadcast class of `permanent-attack.md` §8.

**The cut ranks do not drop in characteristic p.** `modp_cutrank.py` (1): for the Ryser row-group factor
Π_{i∈R_a}(w_i + r_i(x)) across (x_{C_b} ; x_rest), n = 8, p ∈ {3,5,7}, |R_a| ∈ 1..4, q ∈ 2..4, 5 samples each, the
F_p-rank equals the Q-rank in 177 of 180 cases (the 3 exceptions are lower by 1–2) and reaches the generic
2^{min(|R_a|,q)} in most samples; the shortfalls come from degenerate 0/1 blocks, identically over Q. A single row factor always has rank 2 (it is a linear form) in every characteristic,
so a dense row costs one shared bit per (row, column block) pair — U ≥ n·h, P ≥ n — over F_p exactly as over Z.
The engine is ring-agnostic (an F_p-valued network lifts to an integer network with the same value mod p,
same U and P), so the barriers of `permanent-attack.md` §8 and F3 apply verbatim mod p and mod p^k.
F2 also holds over every Z/M (its permutation submatrix is invertible mod M).

**Where char p *does* lower a rank.** `modp_cutrank.py` (2): the *global* half split M[x_L,x_R] =
Π_i(w_i + r_i) mod p at n = 8 has F_p-rank 4–10 of 16 for p = 3 and 8–16 for p ≥ 5. This is (M1): only
(2(1−1/p))ⁿ entries are nonzero, and for p = 3, (4/3)ⁿ = 2^{0.415n} < 2^{n/2} bounds the rank. So the char-p
saving lives in the global, Θ(n)-arity split (where BW/BHL exploit it by listing dissimilar pairs), and not in
the local cuts the engine charges. The engine cannot see it.

**For which p is any of this 2^{o(n)}?** (E-R): none. (E-F)/(E-N): none, since the network is inadmissible
for every p and the #SAT form needs a dense quadratic congruence. The only p with 2^{o(n)} cost is p = 2
(poly), and p^k = 2^k with k = o(n/lg n). This is exactly the regime where CRT fails (§3).

**Björklund/Li self-reduction mod p.** The 2^{n−Ω(√n)} algorithm over F_q reduces per to 2^{n−k}poly(n)
weighted k×k instances (k = Θ(√n)) and tabulates; the outer sum ranges over subsets X ⊆ V∖K and each weight
depends on all n−k bits of X (one node with P = n − k, `permanent-attack.md` §7). Its saving comes from
collisions among the ≤ q^{k²} small instances and from Kakeya-set interpolation, not from locality; nothing in
it is specific to small characteristic, and the engine has nothing to amplify.

---------------------------------------------------------------------------------------------------

## 5. The key question: per mod p^k with p small and k ≈ n lg n / lg p

Since p^k > n!, this *is* the integer permanent; the question is whether a char-p mechanism keeps working as
k grows. Each mechanism, followed to k ≈ n lg n/lg p:

| mechanism | regime where it saves | at k = lg n!/lg p | cost there |
|---|---|---|---|
| (M1)/(M2) Bax–Franklin vanishing (BHL) | kp < n (saving exp{−Ω(γ²n/(p lg p))}, γ = 1 − kp/n) | kp/n = p lg n/lg p ≫ 1: almost every term survives (p = 3, kp/n = 1.5 at n = 8: 75% survive) | 2ⁿ (no saving) |
| (M3) Valiant elimination, p = 2 | each digit costs a factor n^{O(1)}: n^{k+O(1)} (BHL), O(n^{4k}) (Valiant) | k = lg n! ≈ n lg n | 2^{Θ(n lg² n)} (lg cost/n = 28 … 176 for n = 64 … 16384) |
| (M3) odd p | needs p equal rows per factor p; the error term of a row operation is a unit multiple of an equally hard permanent | — | no algorithm (Mod_pP-hard) |
| (M4) low F_p-rank | rank_p(A) < n/(p−1) gives 0; p^{rank}·poly in general | random 0/1: rank_p = n − O(1) | ≥ pⁿ |
| (E-F) 2-local / Gauss-sum form | p = 2: affine ⇒ poly | p odd: non-affine unaries | χ(ĥ^{⊗n}⊗1^{⊗n}) ≤ 2ⁿ, nothing better known |

Three precise facts close the question.

1. **Entropy (B4).** Any plain #SAT encoding of per mod p^k with lg p^k ≥ lg n! + 2 has N ≥ n lg n − 1.45n −
   W − lg T variables: identical to the integer case, so the Lean N-bound costs 2^{Ω(n√lg n)}. Digit-by-digit
   methods must therefore pay less than one counted variable per p-adic digit; Valiant's pays lg n.
2. **Small primes only.** If every modulus is a power of a prime ≤ P with lg P = o(lg n), then (Mertens)
   the vanishing regimes carry Σ_{p≤P}(n/p)lg p = n lg P(1 + o(1)) = o(n lg n) bits, so some prime must be used
   with k_p p/n ≥ lg n!/(n lg P) → ∞, i.e. strictly outside the only regime where any odd-p mechanism saves
   anything. With all primes below n the vanishing regimes still miss ≈ 1.09n bits (B2).
3. **Engine.** Networks are ring-agnostic: a network for per mod p^k is a network with the same (U, P, g, B)
   and integer tables, and its cut ranks over Z/p^k are ≥ those over F_p, which equal the rational ones on the
   cuts the engine charges (§4). So for exponential-weight networks (where F1/B4 do not bind) per mod p^k has
   exactly the broadcast/assignment barrier of the integer permanent: U·P ≥ n² or U ≥ 2n lg(eh), e_K·U ≥ 30n (F3).

**Answer to the key question: no.** per mod p^k with p small and k ≈ n lg n/lg p is not easier than per in any
representation we can feed to the refutation engine: for #SAT encodings by (B4), for networks by the
unchanged cut ranks, and every char-p mechanism stops saving at kp ≈ n (odd p) or costs n^{Θ(1)} per digit (p = 2).

---------------------------------------------------------------------------------------------------

## 6. Verdict and the precise obstruction

**Obstruction (route A(i)).**
* *Many primes.* Recovering n lg n − 1.44n bits by CRT needs primes up to ≈ 0.9·n ln n (B1). Every known
  char-p mechanism (Bax–Franklin vanishing, dissimilar-pair listing, BHL's p^k extension) saves
  Θ(n/p)–Θ(n/(p lg p)) in the exponent, which is O(1/lg n) at p ≈ n ln n; the vanishing regimes of *all* primes
  < n carry ≈ lg n! − 1.09n bits (B2), so primes ≥ n with zero saving are unavoidable. No odd p has a known
  2^{o(n)} algorithm, not even p = 3.
* *Few prime powers.* Single-modulus p-adic recovery is the integer problem: F1 holds verbatim mod M once
  lg M ≥ lg n! + 2 (B4), and entropy-respecting schemes need ω(√lg n·(lglg n)²) coprime moduli with
  k_p p/n ≫ 1 (B4(b)); Valiant's p = 2 mechanism gives 2^{o(n)} only for k = o(n/lg n).
* *Engine.* The char-p encodings with few variables exist — (E-F) has N = n(1 + ⌈lg p⌉), arity 2 — but they
  are dense: n² nonzero pair weights (no CNF, nothing to sparsify), and as networks c_ab = ⌈lg p⌉·rank_p of the
  off-diagonal blocks, so U ≈ 2gn⌈lg p⌉, P ≈ 2n⌈lg p⌉: inadmissible for every p. The F_p cut ranks of dense
  rows equal the rational ones (one bit per (row, block) pair; a linear form has rank 2 in every characteristic).
  The char-p saving lives only in the global Θ(n)-arity split (fewer nonzero Ryser terms), which the engine
  does not charge and cannot exploit. **The dense row is exactly as wide mod p as over Z.**

**What would break it (the precise missing primitives).**
1. An m-independent 2^{o(N)} counting algorithm for *a k-CNF plus one dense quadratic congruence mod p*
   (4.2), N' = n(1 + 3⌈lg p⌉). This gives per mod p in 2^{o(n lg p)}: 2^{o(n)} for p = 2^{O(1)}, but it is
   still 2^{o(n lg n)} at the primes p ≈ n ln n that CRT needs, so it would also have to run in 2^{o(N/lg N)}
   there. The refutations' N-bound comes from sparsifying OR-clauses and has no analogue for a congruence
   with n² terms.
2. Subexponential affine (stabilizer) rank of ĥ^{⊗n} ⊗ 1_{\{0,1\}}^{⊗n} over Z_p (Clifford-plus-magic
   simulation with 2n magic qudits in 2^{o(n)}), for ≈ n primes up to n ln n. Known lower bounds are Ω(n); for p = 2
   the rank is 1 (Gauss sum, per ≡ det).
3. An elimination mechanism for odd p (or for 2^k at amortised cost 2^{o(1/lg n)} per digit) — the analogue
   of Valiant's equal-row trick that does not need p equal rows.

None of these is supplied by the refutations. Route A(i) stays open as a target but has no mechanism, and the
obstruction is now quantitative: **per mod p in 2^{o(n)} for ≈ n primes up to ≈ 0.9 n ln n, with every
known char-p saving equal to Θ(n/p) (zero at p ≥ n), and every low-variable char-p encoding dense (n² weights,
P ≈ 2n lg p).** The positive results remain E1/E2 of `wild-ideas.md` and the bounded-degree network.
