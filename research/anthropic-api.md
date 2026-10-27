# C0 scout: Anthropic's Lean API for Lemma 8, Theorem A(b), Theorem B (and what to use instead)

Workspace: `/home/user/anth-build` (Lean v4.33.1). All paths below are relative to it. Paper text:
`.../scratchpad/anth/fm/paper.txt` (Lemma 8 at l.1542, Theorem A at l.1587, Theorem B at l.1723,
Definitions 1–4 and Lemma 1 at l.755–889).

Summary up front:

* All three statements are **general**: they speak of an arbitrary `Net g` (Definition 2 as data
  plus `Net.Is P B`) or of arbitrary integer tables given by query access. Nothing in them is
  specific to CNFs.
* `groupingExplicit` (Lemma 8) is a **standalone theorem**. The proof of the Main Theorem does not use
  it (PaperIndex l.2019–2028: "The proof of the Main Theorem uses only the part of this proof up to
  the call"). It is still fully proved, and we can use it as it stands.
* The CNF chain to TM2 (`CountedRoute`) does **not** go through Lemma 8 in counted operations. It
  turns the counted clique machine into a padded `Solver` and then uses the **padding-model**
  grouping `rebalG` on the CNF network `satFk`. There is no ready-made "counted Lemma 8 output →
  TM2" theorem. There are, however, generic bridges (`CountKSat.exists_tmW`,
  `GraphProblems.tm_of_stepped`, `PaddedDescent.exists_tm_padded`).
* For **Theorem 1** (2^{δn}) the cleanest route is the main-text route:
  `Printed.groupingLemma` + `Given.stEveryEta` + `Given.stOnGiven` (Lemma 1 on any network given by
  procedures) + `GraphProblems.tm_of_stepped`. These need polynomially bounded memory, and that
  memory bound is a real constraint on how we write the procedure for W_a (see §4).

---------------------------------------------------------------------------------------------------

## 1. Definitions

### 1.1 Step machines and machines with query access (the cost model)

`proof/statements/StepMachineStatements.lean`

* l.29 `class HasSize (α) where size : α → ℕ`. Instances: ℕ ↦ `n.size+1`, ℤ ↦ `natAbs.size+1`,
  pairs add, lists `Σ(size x+1)+1` (l.36–45).
* l.57
  ```lean
  structure Stepped (α β : Type) : Type 1 where
    σ : Type
    [sz : HasSize σ]
    init : α → σ
    step : σ → σ
    out : σ → Option β
  ```
* l.77 `def Runs (M : Stepped α β) (a : α) (t S : ℕ) (b : β) : Prop := M.Reaches S b (M.init a) t`
  ("halts with b within t steps, all states of size ≤ S").
* Polynomial-time steps: `IsPolyT M` (class: `init`, `step`, `out` are `PolyT` on Mathlib TM2, plus
  `Carried σ`), file `proof/machines/ToTuring/PolyT.lean` l.54 (`PolyT f`). An operation is one
  application of `step`, which may be any polynomial-time function of the whole state. So a step
  count means something only together with the state bound S. This is stated in the header of
  `proof/machines/QueryMachines/Kernel.lean` l.32–72.

`proof/machines/QueryMachines/Kernel.lean`

* l.89
  ```lean
  structure QueryMachine (Q A α β : Type) : Type 1 extends Stepped α β where
    ask : σ → Option Q
    resume : σ → A → σ
  ```
* l.102 `inductive Reaches` (halt / own step / query: a query x needs `O x = some v`).
* l.111 `def Runs (M) (O : Q → Option A) (a : α) (own : ℕ) (L : List Q) (S : ℕ) (b : β) : Prop`
* l.115
  ```lean
  def Within (M : QueryMachine Q A α β) (O : Q → Option A) (w : Q → ℕ) (a : α) (T S : ℕ) (b : β) : Prop :=
    ∃ (own : ℕ) (L : List Q), M.Runs O a own L S b ∧ own + (L.map w).sum ≤ T
  ```
  "The result is b within T operations when query x costs w x, on states of size ≤ S."
* l.123 `def unitCost : Q → ℕ := fun _ => 1`
* l.130 `close M O : Stepped α β` (oracle built in, one step per query); l.142 `plug M R` (each
  query answered by running a step machine R on (context, query)); l.157 `subst M N` (answered by a
  machine with query access of its own).
* l.172 `class IsPolyQ` / l.183 `def PolyTimeSteps (M) : Prop := Nonempty (IsPolyQ M)`.
* Proved rules (`proof/machines/QueryMachines/Runs.lean`, `Poly.lean`): `stMono` (Runs l.276),
  `stClose` (l.288: `(M.close O).Runs a T S b ↔ M.Within O unitCost a T S b`), `stSlowDown`
  (l.296), `stSubst` (l.304), `stPlug` (l.307), `stSubstWithin` (l.313); `stPolyPlug` (Poly l.374),
  `stPolySubst` (l.378), `stPolyClose` (l.382). Their statements are in Kernel.lean l.190–257.
  `StPlug`:
  ```lean
  M.Runs O a own L S b → (∀ x ∈ L, ∀ v, O x = some v → R.Runs (c, x) (t x) S' v) →
    (M.plug R).Runs (c, a) (own + (L.map fun x => t x + 2).sum) (size c + S + S' + 1) b
  ```

So in these statements **an algorithm** is a `QueryMachine` (or `Stepped`) value. Its input is
data, mostly unary lists `List Unit`. Its cost is `Within … T S`. It carries a separate
`PolyTimeSteps` certificate.

### 1.2 Definition 1 (factors through c bits)

`proof/networks/Paper/SecNetworks_DefFactor.lean` l.40 `def FactorsThrough (F : X → X' → ℤ) (c : ℕ)`
(alias `PaperIndex.factorsThrough`). It is not used by `Net`. `Net.Is.fact` states the
factorization inline (below).

### 1.3 Definition 2 (network), its value and total

`proof/networks/Eight/SecNetworks_Defs.lean`

```lean
structure Net (g : ℕ) where                                   -- l.38
  len : Fin g → ℕ
  S : Fin g → Finset (List Bool)
  W : Fin g → List Bool → ℤ
  Ψ : Fin g → Fin g → List Bool → List Bool → ℤ
  c : Fin g → Fin g → ℕ
  f : Fin g → Fin g → List Bool → List Bool → ℤ

def value : ℤ := ∑ z ∈ Fintype.piFinset N.S, (∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)   -- l.52
def U : ℕ := ∑ a, ∑ b ∈ univ.erase a, N.c a b                                                                   -- l.55

structure Is (P B : ℕ) : Prop where                                                                             -- l.58
  P_pos : 1 ≤ P
  B_pos : 1 ≤ B
  len_S : ∀ a, ∀ z ∈ N.S a, z.length = N.len a
  len_le : ∀ a, N.len a ≤ P
  Ψ_symm : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, N.Ψ b a z' z = N.Ψ a b z z'
  c_symm : ∀ a b, N.c a b = N.c b a
  fact : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, N.Ψ a b z z' = ∑ θ ∈ words (N.c a b), N.f a b z θ * N.f b a z' θ
  i : ∀ a, ∑ b ∈ univ.erase a, N.c a b ≤ P
  ii_W : ∀ a, ∀ z ∈ N.S a, |N.W a z| < 2 ^ B
  ii_Ψ : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, |N.Ψ a b z z'| < 2 ^ B
  ii_f : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ θ ∈ words (N.c a b), |N.f a b z θ| < 2 ^ B
```
(`pairs` = ordered pairs a < b; `words c` = all bit lists of length c.)

Definition 2(iii), in two forms:

* **As an oracle** (used by Lemma 1 and Lemma 8): `proof/statements/PrintedStatement.lean` l.114
  `abbrev NetQuery := WQ ⊕ (WQ ⊕ (PsiQ ⊕ FQ))` (membership, W, Ψ, f). l.119 `def netOracle (N : Net g) :
  NetQuery → Option ℤ` answers membership only for strings of length `len a`, W on `S a`, Ψ on
  `S a × S b`, f on `S a × words (c a b)`, a ≠ b. l.129 `NetInput := (List Unit × List Unit) × (List
  (List Unit) × List (List (List Unit)))`. l.133 `netInput N P B` hands P, B, the P_a and c_{a,b} in
  unary. Each query is priced τ (`fun _ => τ`) in `Within`.
* **As procedures** (step machines): `SecNetworks_Defs.lean` l.83 `structure Procs (C)` (fields P, B,
  len, cap, and step machines mem/W/Ψ/f on `C × query`); l.96 `Procs.Give … (P B τ S)` (each
  answer within τ steps on states ≤ S); l.108 `structure IsNetwork Np c N P B τ S : Prop` (`is :
  N.Is P B`, `τ_pos`, `given`). The variant with query access is in
  `proof/threesat/Printed/Programs.lean` l.77 `structure ProcsQ (Q A C)`.
  `proof/statements/GivenStatement.lean` l.45 `PolyTimeProcs` and l.75 `def IsGivenNetwork Np O c N P B τ S := SecNetworks.IsNetwork (Np.close O) c N P B τ S ∧ PolyTimeProcs Np`.
  For plain step machines use `Given.ofProcs`, `Given.noTable` (l.79–84).

### 1.4 Definition 3 (the (K,λ)-clique) and table queries

* `SecNetworks_Defs.lean` l.139 `def clique (K lam : ℕ) (W : Fin K → List Bool → ℤ) : Net K`
  (len = (K−1)λ, c = λ, Ψ = [copies agree], f = [copy = θ]).
* `PrintedStatement.lean` l.53 `abbrev TableQuery := ℕ × List Bool`. l.57
  `def tables (K lam) (W : ℕ → List Bool → ℤ) : TableQuery → Option ℤ` answers (w, z) iff w < K and
  |z| = (K−1)λ. A query costs `unitCost`.
* Definition 4: l.77 `AchievedBy M Cc K e` (value within Cc·2^{eK²λ}(B+λ)^Cc **and states ≤
  Cc(B+λ)^Cc**), l.83 `Achievable K e`.

---------------------------------------------------------------------------------------------------

## 2. The three statements, verbatim

### 2.1 Lemma 8: `ExplicitCost.groupingExplicit`

Proof: `proof/rates/ExplicitCost/GroupingLemma.lean` l.212. Statement:
`proof/rates/ExplicitCost/GroupingDefs.lean` l.180.

```lean
def SolvesCliques {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (inp : α) (K L B' 𝒯 SE : ℕ) : Prop :=   -- l.169
  ∀ W : ℕ → List Bool → ℤ, (∀ w < K, ∀ z ∈ words ((K - 1) * L), |W w z| < 2 ^ B') →
    E.Within (tables K L W) QueryMachine.unitCost inp 𝒯 SE (clique K L fun w => W w.val).value

def GroupingExplicit : Prop := ∃ C₁ : ℕ, ∀ (α : Type) (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α) (a b K g : ℕ) (N : Net g) (P B τ 𝒯 SE : ℕ),
  2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → 1 ≤ τ → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  SolvesCliques E (arg (unary K, unary (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U), unary (AppRunningTime.B'of K g P B))) K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (AppRunningTime.B'of K g P B) 𝒯 SE →
    ∃ T : ℕ, (groupingData E arg).Within (netOracle N) (fun _ => τ) (groupingInput a b K N P B) T (SE + (g * (P + B) + size (a, b)) ^ C₁) N.value ∧
      (T : ℝ) ≤ ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (2 * (g : ℝ) * P / K) * τ) * ((g : ℝ) * (P + B)) ^ C₁

theorem groupingExplicit : GroupingExplicit
```
Auxiliary definitions (`GroupingDefs.lean`): l.63 `GroupingInput := (ℕ × ℕ) × DataInput`. l.92
`CliqueInput := List Unit × List Unit × List Unit` (K, λ, B in unary). l.116
`groupingData E arg : QueryMachine NetQuery ℤ GroupingInput ℤ`. l.120
`groupingInput a b K N P B := ((a, b), dataInput K N P B)`, where `dataInput K N P B = ((unary K,
unary g), netInput N P B)` (`EntryDefs.lean` l.89). l.188 `GroupingPoly` (poly-time steps if E is and
`PolyT arg`), proved as `ExplicitCost.groupingPoly`.

`proof/statements/AppRunningTimeStatement.lean`:
```lean
def Cases (K g : ℕ) (ζ : ℝ) (P : ℕ) (c : Fin g → Fin g → ℕ) : Prop :=                    -- l.102
  (g = 3 * K ^ 8 ∧ ζ = 1 / (2 * K)) ∨ (K ∣ g ∧ (∀ a b, a ≠ b → (c a b : ℝ) ≤ (P : ℝ) / g) ∧ (K : ℝ) * Real.log (2 * g * K) ≤ 2 * ζ ^ 2 * g)
noncomputable def Lof (K g : ℕ) (ζ : ℝ) (P U : ℕ) : ℕ := ⌈((U : ℝ) + 2 * ζ * g * P) / (K : ℝ) ^ 2⌉₊   -- l.106
def B'of (K g P B : ℕ) : ℕ := (2 * g * P + K - 1) / K + g ^ 2 * B                          -- l.109
```
ζ = a/b is part of the input. The paper's constant `K^g` is explicit. The state bound is SE (E's own
bound) plus a polynomial.

### 2.2 Theorem A(b): `ExplicitCost.recursionSolves`

Proof: `proof/rates/CountedRecursion/Main.lean` l.96. Statement:
`proof/rates/CountedRecursion/RecursionDefs.lean` l.553.

```lean
structure Setting (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data) : Prop where              -- l.80
  is : D.Is ρ c
  short : ∀ lam tr i, D.cap lam tr i ≤ 2 * lam
  x₀_ge : 18 ≤ x₀
  x₀_c : c + 5 ≤ 2 ^ x₀

def RecursionSolves : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped PieceQuery Ans), PiecesCounted.IsPieces ρ c D Alg → Setting ρ c x₀ D →
  (cliqueMachine c x₀ Alg).PolyTimeSteps ∧ CliqueLevels.Solves (cliqueMachine c x₀ Alg) (Levels.Gen.K x₀) (Levels.Gen.e ρ x₀) C₀
```
`proof/statements/CliqueLevelsStatement.lean`:
```lean
noncomputable def bound (e : ℝ) (K C₀ lam B : ℕ) : ℝ := (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((K : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * K ^ 2)   -- l.47
def Solves (M : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) : Prop :=           -- l.51
  ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B → (∀ w < K l, ∀ z ∈ words ((K l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, M.Within (tables (K l) lam W) QueryMachine.unitCost (unary l, unary lam, unary B) T S (clique (K l) lam fun w => W w.val).value ∧
      (T : ℝ) ≤ bound (e l) (K l) C₀ lam B ∧ (S : ℝ) ≤ bound (e l) (K l) C₀ lam B
```
Note that the **state bound S is the whole exponential bound**, not a polynomial. The sharper forms
are `RecursionCountedUpTo` (l.518: pieces as an oracle, S ≤ (K(λ+B))^{C₀K}) and `SolvesInFactor`;
neither is the form used downstream. Levels (`proof/statements/LevelsStatement.lean` l.23–36):
`K x₀ 0 = 2^x₀`, `K x₀ (l+1) = (2^(3l+x₀)·K x₀ l)^2`, `e ρ x₀ 0 = 1/2`,
`e (l+1) = (ρ + 3/2^(l+5))·e l + 3/K l`. `cliqueMachine` is defined in
`CountedRecursion/SolverDefs.lean` l.153, with input `Head = List Unit × List Unit × List Unit`
(ℓ, λ, B in unary).

### 2.3 Theorem B: `PiecesCounted.halfPieces`

Proof: `proof/rates/PiecesCounted/Half.lean` l.88. Statement:
`proof/statements/PiecesCountedStatement.lean` l.265.
```lean
def HalfPieces : Prop := ∃ (c : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer), IsPieces (1 / Real.sqrt 2) c D Alg ∧
  ∀ lam, 1 ≤ lam → ∃ mu : Pieces.Bits lam → AppHalfPieces.Ptn, AppHalfPieces.IsMu lam (AppHalfPieces.hOf lam) mu ∧
    (D.fam lam).I = Finset.Icc (-(2 * (AppHalfPieces.hOf lam : ℤ))) (2 * (AppHalfPieces.hOf lam : ℤ)) ∧ (D.fam lam).d = (AppHalfPieces.hOf lam).factorial ∧
    ∀ s ∈ (D.fam lam).I, (∀ x y u v, ((D.fam lam).A s x y u v : ℚ) = AppHalfPieces.piece (AppHalfPieces.hOf lam) mu s x y u v) ∧
      D.cap lam false s = Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) s) ∧ D.cap lam true s = Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) s)
```
`Data` (l.94), `Data.Is` (l.102), `IsPieces` (l.169: `is`, `polyTimeSteps`, `computes`), `room`
(l.161). `halfPieces` does **not** give `Setting.short` (c^row, c^col ≤ 2λ). That comes from
`PiecesCounted.mayAssume` (`proof/rates/PiecesCounted/Assume.lean` l.108, c ↦ c+2).

### 2.4 How they are chained for CNFs (`proof/maintheorem/CountedRoute/`)

`Defs.lean` l.118 / `Main.lean` l.89, **proved**:
```lean
def OnTheCountedRecursion : Prop :=
  ∃ (c x₀ C₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped ExplicitCost.PieceQuery ExplicitCost.Ans),
    PiecesCounted.IsPieces (1 / Real.sqrt 2) (c + 2) D Alg ∧ (∀ lam tr i, D.cap lam tr i ≤ 2 * lam) ∧ CountedInstance.AreThePiecesOfAppHalfPieces D ∧ 18 ≤ x₀ ∧ c + 7 ≤ 2 ^ x₀ ∧
    (∀ l : ℕ, _root_.Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (lg (_root_.Levels.Gen.K x₀ l))) ∧
    ThmVariables.Hypothesis (_root_.Levels.Gen.K x₀) (_root_.Levels.Gen.e (1 / Real.sqrt 2) x₀) C₀ (levelsUnder x₀) fractionHalf (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) ∧
    ∀ [QueryMachine.IsPolyQ (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)], ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ →
      ChainOn (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) (_root_.Levels.Gen.K x₀ 0) C₀ (levelsUnder x₀) fractionHalf n₁
```
`ThmVariables.Hypothesis` (`proof/variables/ThmVariables/Defs.lean` l.83) has the fields `levels`,
`computesK`, `number`, `steps : E.PolyTimeSteps`, `solves : Solves E K e C₀`.
**`CountedRoute.onTheCountedRecursion` is the single handle that packages Theorem B + MayAssume +
Theorem A(b)**, with e_ℓ ≤ (3x₀+6)/√log K_ℓ. Use it instead of combining `halfPieces` and
`recursionSolves` by hand.

The CNF path to TM2 after that:

1. `QueryMachines.Bridge.solverOfMachine` / `SolverOfMachineLevels`
   (`proof/rates/CountedToPadded/Defs.lean` l.157, l.227): the counted machine E becomes a padded
   `ClauseBound.Alg.Solver` (`proof/rates/ClauseBound/Alg/Interfaces.lean` l.126; tables written
   out, right once the pad has 2^need units).
2. The CNF top level `ClauseBound.Alg.countG`/`AM` (`proof/rates/ClauseBound/Alg/Top.lean` l.42, 77)
   applies the **padding-model grouping** `PaddedDescent.F.rebalG`
   (`proof/rates/PaddedDescent/F/Prog.lean` l.78) to the CNF network `satFk : FNet _`
   (Interfaces.lean l.186). Lemma 8 in counted form is not used.
3. Functions of (input, pad) become TM2 machines (`PairsToBound.Computes`,
   `proof/variables/PairsToBound/Defs.lean` l.192; `PaddedDescent.exists_tm_padded`,
   `proof/rates/PaddedDescent/Pad.lean` l.116).

---------------------------------------------------------------------------------------------------

## 3. General or CNF-specific?

**General.** `GroupingExplicit` quantifies over every `N : Net g` with `N.Is P B` and `Cases`, and
over every clique machine E. `Solves`/`RecursionSolves` quantify over all integer tables W. The
network enters Lemma 8 only through `netOracle N` (query price τ) and `netInput N P B`. Nothing has
to be generalised. CNF-specific pieces exist only downstream: `satFk`, `countG`, `AM`, the `Given`
`formulaProcs`.

Other general tools found:

* `Printed.groupingLemma` (Lemma 1, fixed K; `proof/threesat/Printed/End.lean` l.71; statement
  `PrintedStatement.lean` l.149–158):
  ```lean
  def ComputesNetworks (NM : QueryMachine NetQuery ℤ NetInput ℤ) (C₁ g K : ℕ) (e : ℝ) : Prop :=
    ∀ (N : Net g) (P B τ : ℕ), N.Is P B → 1 ≤ τ →
      ∃ T : ℕ, NM.Within (netOracle N) (fun _ => τ) (netInput N P B) T (C₁ * (P + B) ^ C₁) N.value ∧
        (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁ * τ
  def GroupingLemma : Prop := ∀ (K : ℕ) (e : ℝ), Achievable K e →
    ∃ (NM : QueryMachine NetQuery ℤ NetInput ℤ) (C₁ : ℕ), NM.PolyTimeSteps ∧ ComputesNetworks NM C₁ (3 * K ^ 8) K e
  ```
  The state bound C₁(P+B)^{C₁} is **polynomial**.
* `Given.stEveryEta : ∀ η > 0, ∀ K₀, ∃ K ≥ K₀, Achievable K η` (`proof/threesat/Given/End.lean` l.41;
  statement `PrintedStatement.lean` l.173).
* `Given.stOnGiven` (`proof/threesat/Given/Networks.lean` l.41; statement `GivenStatement.lean` l.93)
  is Lemma 1 applied to **any** network given by procedures:
  ```lean
  def StOnGiven : Prop := ∀ (NM : NetMachine) (C₁ g K : ℕ) (e : ℝ), ComputesNetworks NM C₁ g K e →
    ∀ (Q A C : Type) [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (Np : ProcsQ Q A C) (O : Q → Option A) (c : C) (N : Net g) (P B τ S : ℕ), IsGivenNetwork Np O c N P B τ S →
      (NM.PolyTimeSteps → (networkOn g NM Np).PolyTimeSteps) ∧
      ∃ T : ℕ, (networkOn g NM Np).Within O QueryMachine.unitCost c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
        (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ
  ```
  `Given.onFormula` (End.lean l.56) is the CNF instance, a template for ours.
* Padding model: `rebalG_spec'` (`proof/rates/GeneralPieces/Group/Lemma.lean` l.153) for any `FNet C`
  that `Presents` a `Groundwork.Network (Fin g) (List Bool) (List Bool)`.
* TM2 bridges:
  * `CountKSat.exists_tmW` (`proof/consequences/CountKSat/Host.lean` l.222): for
    `M : Stepped (List Bool) (List Bool)` with `[IsPolyT M]`, one TM2 machine N and q with
    `M.Runs x T S w → TM2OutputsInTime N.tm x w (q·(T+1)·(|x|+S+1)^q)`. This is **linear in T,
    polynomial in S**.
  * `GraphProblems.tm_of_stepped` (`proof/consequences/GraphProblems/Host.lean` l.27): from
    c·2^{(δ/2)·sz} steps on states ≤ c(sz+2)^c to ⌊C·2^{δ·sz}⌋ TM2 steps.
  * Graph input code `GraphProblems.code G = unary n ++ matrix G` (`proof/statements/GraphProblemsStatement.lean` l.89).

---------------------------------------------------------------------------------------------------

## 4. Recommendation

### 4.1 What we must prove about our network (C1)

Target the `Net g` structure directly; M7 should produce exactly this.

1. A definition `hcNet G r β order : Net g` (settings = `List Bool`, `S a : Finset (List Bool)`, `W`,
   `Ψ`, `c`, `f` as in Definition 5.1).
2. `(hcNet …).Is P B` with P := w(μ)+g+g², B := 2μ+1 (Prop. 5.4). The fields are: lengths, `len ≤
   P`, symmetry of Ψ and c, `fact` (Lemma 5.2), (i), (ii) with strict `< 2^B`.
3. `(hcNet …).value = n * numHC G` (Theorem 5.3).
4. Cost of table queries. In the Lemma 8 and Lemma 1 statements this is **only the price τ**: no
   proof obligation inside the lemma. The obligation appears when the queries are answered.
   Recommended form: `Given.IsGivenNetwork (Given.ofProcs Np) Given.noTable c N P B τ S`, that is,
   `Procs C` with context c = the prepared graph data (graph, β, crossing order, the lists
   E(a,b), w_ab, Q_a), `Procs.Give c N P B τ S` (mem/W/Ψ/f each `Runs` within τ steps on states ≤
   S), plus `PolyTimeProcs` (`Unary` for P, B, len, cap; `PolyTimeSteps` for the four machines).
   **S must be polynomial in n, uniformly in g.** `exists_tmW` costs (|x|+S+1)^q with q from the
   machine's certificate, which depends on K, and so on g. With S = 2^{Θ(μ)} the overhead
   2^{qΘ(μ)} with μ ≈ 3Dn/g cannot be pushed below 2^{δn}. So the procedure for I_a in
   Prop. 5.4(iii) must **not** hold Λ_a densely (2^{|Γ_a|} integers). It must be a loop with
   poly(n) state, for example a sum over the choices of one monomial per factor, 5^{μ}·poly
   steps. This gives τ = 2^{O(μ)}·poly(n) with S = poly(n). For Theorem 2 alone, S ≤ 2^{O(m/√log n)}
   would be tolerable, because one uniform machine has a single absolute q.

### 4.2 Theorem 1 (2^{δn}): main-text route (shortest, all pieces proved)

`Given.stEveryEta` → (K, e) achievable with e ≤ δ/(40D), K ≥ 60D/δ → `Printed.groupingLemma` →
NM with `ComputesNetworks NM C₁ (3K⁸) K e` → `Given.stOnGiven` on our `Procs` → `networkOn g NM
(ofProcs Np)` closed with `noTable` (`stClose`) is a `Stepped C ℤ` with
`Runs c T (size c + C₁(P+B)^{C₁} + S + 4)` and T ≤ 3C₁·2^{e(U+gP/K)+2gP/K}(P+B)^{C₁}·τ.

Then:

* precompose a poly-time reader `code G ↦ c` (`Stepped.mapIn`, `IsPolyT.mapIn`);
* add the branching of Lemma 6.1 and the sum over branches. These are step-machine combinators
  (`QueryMachine.sumRange`, `proof/machines/QueryMachines/CombDefs.lean` l.126, used with `prodRange` in
  `Printed.bruteMachine`, `Programs.lean` l.70);
* divide by n and output `SatK.binary`-style bits (`mapOut`);
* finish with `GraphProblems.tm_of_stepped` to get a `TM2ComputableAux Bool Bool` with
  ⌊C·2^{δn}⌋ steps on `code G`.

This needs neither Lemma 8 nor Theorem A/B. It matches the write-up's "alternative route" in §6.3.

### 4.3 Theorem 2 (2^{O(max(m,n)/√log n)}): counted route

Take `CountedRoute.onTheCountedRecursion` to get E := `cliqueMachine (c+2) x₀ Alg` with
`Solves E (K x₀) (e x₀) C₀`, `PolyTimeSteps`, and e_ℓ ≤ (3x₀+6)/√log K_ℓ. Then:

* Instantiate `groupingExplicit` with α := `Head` and arg (K, L, B') := (unary ℓ(K), L, B'), where
  ℓ(K) is the level with K x₀ ℓ = K (definable and poly-time in unary K). Take a = 1, b = 2K
  (case (i), g = 3K⁸). Take 𝒯 = SE := ⌊bound e_ℓ K C₀ L B'⌋₊. `SolvesCliques` asks for one 𝒯 and
  SE for all W, while `Solves` gives ∃ T S per W: use `QueryMachines.stMono` (Within is monotone).
  Side conditions: L ≥ 1 (true since ζgP > 0) and B' ≥ 1.
* Answer the `netOracle N` queries with our procedures: `QueryMachine.plug` with
  `answerOf Np` (`Programs.lean` l.108) and `stPlug`. The price τ per query covers t x + 2 when
  t x ≤ τ − 2; otherwise use `stSlowDown` with a factor of 3. Poly-time: `groupingPoly` +
  `stPolyPlug`.
* Wrap the result in one uniform `Stepped (List Bool) (List Bool)`: it reads `code G`, picks ℓ from n,
  branches, builds `groupingInput`, plugs the procedures and sums. Then apply `CountKSat.exists_tmW`.
  T and S are both ≤ 2^{O(m/√log n)}, and the machine is one fixed machine, so q is absolute and
  the bound stays 2^{C*·m/√log n}.

What is missing, and about how much work it is:

* (a) The `Net`, `Is`, value and `Procs`/`Give` facts for our network (M7 + C1). This is the bulk of
  the work.
* (b) The uniform outer machine (reader, level choice, branching, sum, division), built with the
  combinators in `proof/machines/StepMachines` and `QueryMachines/CombDefs`. Moderate work.
  `Printed.COUNT`/`SAT` (`Programs.lean` l.234–241) and `GraphProblems` are templates.
* (c) Arithmetic for the exponent (6.2). Routine.

No new theory about Anthropic's model is needed.

Alternative for Theorem 2 (closer to how Anthropic did CNFs): give the network as an `FNet` (plain
poly-time functions), use `solverOfMachine` + `rebalG_spec'` in the padding model, then
`exists_tm_padded`. This forgoes `groupingExplicit`, because padding replaces counting, and requires
a `Groundwork.Network` + `PNet.Presents` (`proof/machines/StepMachines/Prog/Spec.lean` l.77, 85)
rather than `Net`. Conversion: `ofNetwork`, used in `RecursionDefs.lean` l.113.

### 4.4 Distance to a `MainTheorem`-style statement

`MainTheorem` (`MainResults.lean`) is `∃ M : TM2ComputableAux Bool Bool, ∃ C, (∀ i, Finite (M.tm.Γ i)) ∧ …
TM2OutputsInTime …`. The reusable path from "counted operations with query access" to that form is:

query machine → (answer queries with step machines: `plug`/`subst`, or `close` with a poly-time
oracle) → `Stepped (List Bool) (List Bool)` with `IsPolyT` and a `Runs x T S w` bound →
`CountKSat.exists_tmW` (TM2, q(T+1)(|x|+S+1)^q) or `GraphProblems.tm_of_stepped` (2^{δn} form).

This path is generic and proved. The only thing that makes counted bounds honest is the state bound
S, so every procedure we write must come with an S (polynomial for Theorem 1).

---------------------------------------------------------------------------------------------------

## 5. Verified

`/home/user/anth-build/scout/C0.lean` (scratch file; `lake env lean`, about 15 min, mostly reading oleans
from disk) type-checks `#check` of `groupingExplicit`, `recursionSolves`, `halfPieces`,
`Printed.groupingLemma`, `Printed.stEveryEta`, `CountKSat.exists_tmW`, `groupingPoly`. All depend only
on `[propext, Classical.choice, Quot.sound]`. Imports needed: `ExplicitCost.GroupingLemma`,
`CountedRecursion.Main`, `PiecesCounted.Half`, `Printed.End`, `Given.End`, `CountKSat.Host`.
