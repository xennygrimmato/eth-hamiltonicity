# x7 notebook: a cyclic (three-merge) version of App. B, or why it cannot exist

24 Nov 2026. Tags: [R] proved here, [K] known/cited, [N] computed (script in `code/`), [C] conjecture.
Inputs: x4, x5, b2 notebooks; VP paper App. B (paper.txt l.1251–1433); open-door §1.6–1.7; z1 §1–2, §4; x3 §4.

## 0. Status (written early, updated at the end)

- **(c) Weyl/Heisenberg pieces are closed by an uncertainty principle [R + N].** See §1. Every Weyl-diagonal piece
  A_f = Σ_s f(s) W_s⊗W_s† satisfies col·third = |supp f|·|supp f̂| ≥ N² (Donoho–Stark), i.e. c_col + c_third ≥ 2λ.
  So on K₄ no Weyl-diagonal piece can have third cost < 0.17λ with col cost < 1.83λ. This explains z1 §4's numbers
  (cosets sit exactly on c_col + c_third = 2λ) and rules out every function f, not only cosets and balls.
- **x4's "step 4" is not an obstruction for determinants [R].** §2. The Schur-complement expansion of App. B, done
  with three groups, gives a *triangle* network directly (Cauchy–Binet over the six directed bond blocks). The
  determinantal route therefore needs no "trace version". The real constraint is elsewhere (§3, §4).
- **Δ₃ has a structural property that B3 lacks: any two merges pin a node.** Consequence (conditional on a rank lemma
  that I verified numerically, [N]/[C]): every single tensor on Δ₃ satisfies c_k ≤ 4(c_{k'} + c_{k''}). With
  Theorem 1, every identity then has a piece *outside* the sphere |c| = 9λ: the literal A₂ sphere law is refuted on Δ₃
  as well. This does not exclude ρ = 1/√3, but it kills the "fused-accounting" Θ = 27e family. See §3.

## 1. Brainstorm item (c): Weyl partial sums on K₄. Closed by Donoho–Stark [R + N]

The crossing on K₄ is SWAP (z1 §4). Each split corresponds to one operation on it:
- row = rank of A as an operator;
- col = operator-Schmidt rank, i.e. realignment;
- third = rank of the partial transpose A^Γ (the split under which both edges are internal).

Weyl operators W_s, s ∈ Z_N², satisfy SWAP = (1/N)Σ_s W_s⊗W_s†. Take any piece A_f = Σ_s f(s) W_s⊗W_s†.
- **col(A_f) = |supp f|.** The W_s are linearly independent.
- **third(A_f) = |supp f̂|**, where f̂ is the (symplectic) Fourier transform. Reason: A_f^Γ = Σ_s f(s) W_s⊗W̄_s, the operators
  W_s⊗W̄_s commute, and they are diagonal in the Bell basis with characters as eigenvalues.
- Hence **col·third ≥ |Z_N²| = N²** for every f ≠ 0, by the uncertainty principle on finite abelian groups (Donoho–Stark).
  In log form, c_col + c_third ≥ 2λ.
- Check (`code/weyl_uncertainty.py`, N = 2…5, 240 random sparse and indicator f): both identities hold in every trial,
  and the minimum of col·third is exactly N².
- Row ranks are unconstrained by this bound, but z1 needs third < 0.17λ, which forces col > 1.83λ. Any family built from
  Weyl-diagonal pieces is at best trivial on the (col, third) pair. **Item (c) is dead for all f.** A useful K₄ piece
  must be non-diagonal in the Weyl basis, i.e. must mix W_s⊗W_t with s ≠ t.

(Further sections follow.)
