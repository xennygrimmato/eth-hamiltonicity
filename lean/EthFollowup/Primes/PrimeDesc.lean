/-
# The leveled description of the prime-parity count (Executor P, step P1; primes-plan.md)

`primeDescL b l0 L A B : LDesc` (ArithL, `ArithLDesc`): variables, for `k = 0, …, L`,
`x_{3k} = d_k`, `x_{3k+1} = s_k`, `x_{3k+2} = e_k`, where `d_0 = m`, `s_0 = a`, `e_0 = b`;
levels `lev d_k = k`, `lev s_k = lev e_k = k − 1` (so `m, a, b` have level `0`).
Products `p = 4k − 2 + r`: `d_k·d_k`, `s_k·1`, `s_k·e_k`, `d_{k−1}·1`; chain `j` equates products
`2j` and `2j + 1`: chain `2k − 1` is `d_k·d_k = s_k` and chain `2k` is `s_k·e_k = d_{k−1}`
(chain `0`: `a·b = m`); chain `j` has level `(j − 1)/2`.
Comparisons: `m ≥ max A 1`, `m ≤ B`, `a < b`.

* `primeDescL_sat`: the satisfying assignments, explicitly;
* `primeDescL_count`: `countB b bx = Σ_{m ∈ [A,B]} τ^<(m)·C_L(m)` for any box function `bx` with
  `y^{2^k} < 2^n → y < bx k`, `B < 2^n`;
* `primeDesc_count_mod_two` (`L = primeL n = Nat.size n`): `countB % 2 = #{primes in [A,B]} % 2`;
* `primeDescL_WF`, `primeDescL_spread` (`Spread 8`), level bounds `≤ L`.

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import EthFollowup.Primes.ArithLDesc
import EthFollowup.Primes.ChainParity
import EthFollowup.ModP.ArithInstances
import Mathlib.Data.Nat.Size

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.ModP

/-! ## Chains as lists -/

/-- The chains `(d_1, …, d_L)` with `d_1² ∣ n`, `d_{k+1}² ∣ d_k` (`n ≠ 0`, all `d_k ∣ …`). -/
def chains : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | L + 1, n => (n.divisors.filter (fun d => d * d ∣ n)).biUnion fun d =>
      (chains L d).map ⟨List.cons d, List.cons_injective⟩

theorem card_chains (L n : ℕ) : (chains L n).card = chainCount L n := by
  induction L generalizing n with
  | zero => rfl
  | succ L ih =>
    rw [chains, chainCount, card_biUnion]
    · exact sum_congr rfl fun d _ => by rw [card_map, ih]
    · intro d _ d' _ hdd'
      exact disjoint_left.2 fun l hl hl' => by
        simp only [mem_map, Function.Embedding.coeFn_mk] at hl hl'
        obtain ⟨l1, -, rfl⟩ := hl
        obtain ⟨l2, -, h⟩ := hl'
        exact hdd' (List.cons.inj h).1.symm

theorem mem_chains {L n : ℕ} {l : List ℕ} : l ∈ chains L n ↔ l.length = L ∧
    ∀ k < L, (n :: l).getD (k + 1) 0 * (n :: l).getD (k + 1) 0 ∣ (n :: l).getD k 0 ∧
      (n :: l).getD k 0 ≠ 0 := by
  induction L generalizing n l with
  | zero => cases l <;> simp [chains]
  | succ L ih =>
    cases l with
    | nil => simp [chains]
    | cons d t =>
      simp only [chains, mem_biUnion, mem_filter, Nat.mem_divisors, mem_map,
        Function.Embedding.coeFn_mk, List.cons.injEq]
      constructor
      · rintro ⟨a, ⟨⟨-, hn⟩, ha⟩, l', hl', rfl, rfl⟩
        rw [ih] at hl'
        refine ⟨by simp [hl'.1], fun k hk => ?_⟩
        rcases k with _ | k
        · simpa using And.intro ha hn
        · have := hl'.2 k (by omega)
          simpa using this
      · rintro ⟨hlen, h⟩
        have h0 := h 0 (by omega)
        simp only [List.getD_cons_succ, List.getD_cons_zero] at h0
        refine ⟨d, ⟨⟨(Dvd.intro d rfl).trans h0.1, h0.2⟩, h0.1⟩, t, ?_, rfl, rfl⟩
        rw [ih]
        refine ⟨by simpa using hlen, fun k hk => ?_⟩
        have := h (k + 1) (by omega)
        simpa using this

/-- Along a chain from `m ≠ 0`: `d_k ≠ 0` and `d_k^{2^k} ≤ m`. -/
theorem chain_pow_le {L m : ℕ} {l : List ℕ} (hm : m ≠ 0) (hl : l ∈ chains L m) :
    ∀ k ≤ L, (m :: l).getD k 0 ≠ 0 ∧ (m :: l).getD k 0 ^ 2 ^ k ≤ m := by
  rw [mem_chains] at hl
  intro k hk
  induction k with
  | zero => simp [hm]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨hd, -⟩ := hl.2 k (by omega)
    have hD : (m :: l).getD (k + 1) 0 ≠ 0 := by
      intro hD; rw [hD] at hd; simp at hd; exact ih1 hd
    refine ⟨hD, ?_⟩
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero ih1) hd
    calc (m :: l).getD (k + 1) 0 ^ 2 ^ (k + 1)
        = ((m :: l).getD (k + 1) 0 * (m :: l).getD (k + 1) 0) ^ 2 ^ k := by
          rw [← sq, ← pow_mul, ← pow_succ']
      _ ≤ ((m :: l).getD k 0) ^ 2 ^ k := Nat.pow_le_pow_left h2 _
      _ ≤ m := ih2

/-! ## The description -/

/-- Level of variable `v`: `lev x_{3k} = k`, `lev x_{3k+1} = lev x_{3k+2} = k − 1`. -/
def levOf (v : ℕ) : ℕ := if v % 3 = 0 then v / 3 else v / 3 - 1

/-- Product `r` of block `k`: `d_k·d_k`, `s_k·1`, `s_k·e_k`, `d_{k−1}·1`. -/
def prodKR (k r : ℕ) : ProdD :=
  if r = 0 then ⟨3 * k, .var (3 * k)⟩
  else if r = 1 then ⟨3 * k + 1, .const [1]⟩
  else if r = 2 then ⟨3 * k + 1, .var (3 * k + 2)⟩
  else ⟨3 * (k - 1), .const [1]⟩

/-- Product `p` (`p + 2 = 4k + r`). -/
def prodOf (p : ℕ) : ProdD := prodKR ((p + 2) / 4) ((p + 2) % 4)

theorem prodKR_0 (k : ℕ) : prodKR k 0 = ⟨3 * k, .var (3 * k)⟩ := by simp [prodKR]
theorem prodKR_1 (k : ℕ) : prodKR k 1 = ⟨3 * k + 1, .const [1]⟩ := by simp [prodKR]
theorem prodKR_2 (k : ℕ) : prodKR k 2 = ⟨3 * k + 1, .var (3 * k + 2)⟩ := by simp [prodKR]
theorem prodKR_3 (k : ℕ) : prodKR k 3 = ⟨3 * (k - 1), .const [1]⟩ := by simp [prodKR]

/-- Chain `j`: product `2j` = product `2j + 1`. -/
def chainOfIdx (j : ℕ) : ChainD := ⟨[⟨1, .prod (2 * j)⟩], [⟨1, .prod (2 * j + 1)⟩]⟩

/-- **The leveled description** for depth `L` and interval `[A, B]` (constants: `l0` limbs of
`b` bits). -/
def primeDescL (b l0 L A B : ℕ) : LDesc where
  D := { nV := 3 * L + 3, pat := [], prods := (List.range (4 * L + 2)).map prodOf,
         chains := (List.range (2 * L + 1)).map chainOfIdx,
         cmps := [⟨0, .const (toLimbs b l0 (max A 1)), .ge⟩, ⟨0, .const (toLimbs b l0 B), .le⟩,
           ⟨1, .var 2, .lt⟩] }
  lev := (List.range (3 * L + 3)).map levOf
  levC := (List.range (2 * L + 1)).map fun j => (j - 1) / 2

/-- The depth used for inputs of `n` bits: `L = size n` (the bit length of `n`), so `n < 2^L`
and `2^{2^L} > 2^n`. (Written as `(Nat.bits n).length` for the polynomial-time reader.) -/
def primeL (n : ℕ) : ℕ := (Nat.bits n).length

/-- The description for `n`-bit inputs. -/
def primeDesc (b l0 n A B : ℕ) : LDesc := primeDescL b l0 (primeL n) A B

/-! ## Evaluation -/

theorem limbsVal_one (b : ℕ) : limbsVal b [1] = 1 := by simp [limbsVal]

theorem pe_0 (b k : ℕ) (x : ℕ → ℕ) :
    (prodOf (2 * (2 * k))).eval b x = x (3 * k + 1) * x (3 * k + 2) := by
  rw [prodOf, show (2 * (2 * k) + 2) / 4 = k by omega, show (2 * (2 * k) + 2) % 4 = 2 by omega]
  simp [prodKR, ProdD.eval, Operand.eval]

theorem pe_1 (b k : ℕ) (x : ℕ → ℕ) :
    (prodOf (2 * (2 * k) + 1)).eval b x = x (3 * (k - 1)) := by
  rw [prodOf, show (2 * (2 * k) + 1 + 2) / 4 = k by omega,
    show (2 * (2 * k) + 1 + 2) % 4 = 3 by omega]
  simp [prodKR, ProdD.eval, Operand.eval, limbsVal_one]

theorem pe_2 (b k : ℕ) (x : ℕ → ℕ) :
    (prodOf (2 * (2 * k + 1))).eval b x = x (3 * (k + 1)) * x (3 * (k + 1)) := by
  rw [prodOf, show (2 * (2 * k + 1) + 2) / 4 = k + 1 by omega,
    show (2 * (2 * k + 1) + 2) % 4 = 0 by omega]
  simp [prodKR, ProdD.eval, Operand.eval]

theorem pe_3 (b k : ℕ) (x : ℕ → ℕ) :
    (prodOf (2 * (2 * k + 1) + 1)).eval b x = x (3 * (k + 1) + 1) := by
  rw [prodOf, show (2 * (2 * k + 1) + 1 + 2) / 4 = k + 1 by omega,
    show (2 * (2 * k + 1) + 1 + 2) % 4 = 1 by omega]
  simp [prodKR, ProdD.eval, Operand.eval, limbsVal_one]

theorem getD_prods {L p : ℕ} (hp : p < 4 * L + 2) :
    ((List.range (4 * L + 2)).map prodOf).getD p default = prodOf p := by
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]; simp

/-- **The satisfying assignments**. -/
theorem primeDescL_sat {b l0 L A B : ℕ} (hA : max A 1 < 2 ^ (b * l0)) (hB : B < 2 ^ (b * l0))
    (x : ℕ → ℕ) :
    (primeDescL b l0 L A B).D.Sat b x ↔ max A 1 ≤ x 0 ∧ x 0 ≤ B ∧ x 1 < x 2 ∧
      (∀ k ≤ L, x (3 * k + 1) * x (3 * k + 2) = x (3 * (k - 1))) ∧
      (∀ k, 1 ≤ k → k ≤ L → x (3 * k) * x (3 * k) = x (3 * k + 1)) := by
  have hch : (∀ ch ∈ (primeDescL b l0 L A B).D.chains,
      sideVal b (primeDescL b l0 L A B).D.prods x ch.lhs =
        sideVal b (primeDescL b l0 L A B).D.prods x ch.rhs) ↔
      ∀ j < 2 * L + 1, (prodOf (2 * j)).eval b x = (prodOf (2 * j + 1)).eval b x := by
    simp only [primeDescL, List.forall_mem_map, List.mem_range, chainOfIdx, sideVal, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Src.eval, one_mul, add_zero]
    constructor
    · intro h j hj
      have := h j hj
      rwa [getD_prods (by omega), getD_prods (by omega)] at this
    · intro h j hj
      rw [getD_prods (by omega), getD_prods (by omega)]
      exact h j hj
  unfold Desc.Sat
  rw [hch]
  have hpat : ∀ v < (primeDescL b l0 L A B).D.nV,
      patMatch ((primeDescL b l0 L A B).D.pat.getD v []) (x v) := by
    intro v _; simp [primeDescL, patMatch]
  rw [and_iff_right hpat]
  have hcmp : (∀ q ∈ (primeDescL b l0 L A B).D.cmps, q.rel.Holds (x q.v) (q.rhs.eval b x)) ↔
      max A 1 ≤ x 0 ∧ x 0 ≤ B ∧ x 1 < x 2 := by
    simp [primeDescL, CmpRel.Holds, Operand.eval, limbsVal_toLimbs hA, limbsVal_toLimbs hB]
  rw [hcmp]
  simp only [and_assoc]
  apply and_congr_right; intro _; apply and_congr_right; intro _; apply and_congr_right; intro _
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk1 hk => ?_⟩
    · have := h (2 * k) (by omega)
      rwa [pe_0, pe_1] at this
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have := h (2 * k + 1) (by omega)
      rwa [pe_2, pe_3] at this
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
    · rw [pe_0, pe_1]; exact h1 k (by omega)
    · rw [pe_2, pe_3]; exact h2 (k + 1) (by omega) (by omega)

/-! ## The count -/

/-- The assignment built from `m, a, b` and a chain `l = (d_1, …, d_L)`. -/
def enc (m a b : ℕ) (l : List ℕ) (v : ℕ) : ℕ :=
  if v % 3 = 0 then (m :: l).getD (v / 3) 0
  else if v / 3 = 0 then (if v % 3 = 1 then a else b)
  else if v % 3 = 1 then (m :: l).getD (v / 3) 0 * (m :: l).getD (v / 3) 0
  else (m :: l).getD (v / 3 - 1) 0 / ((m :: l).getD (v / 3) 0 * (m :: l).getD (v / 3) 0)

theorem enc_3 (m a b : ℕ) (l : List ℕ) (k : ℕ) : enc m a b l (3 * k) = (m :: l).getD k 0 := by
  rw [enc, if_pos (by omega), show 3 * k / 3 = k by omega]

theorem enc_0 (m a b : ℕ) (l : List ℕ) : enc m a b l 0 = m := by simp [enc]
theorem enc_1 (m a b : ℕ) (l : List ℕ) : enc m a b l 1 = a := by simp [enc]
theorem enc_2 (m a b : ℕ) (l : List ℕ) : enc m a b l 2 = b := by simp [enc]

theorem enc_3k1 (m a b : ℕ) (l : List ℕ) {k : ℕ} (hk : 1 ≤ k) :
    enc m a b l (3 * k + 1) = (m :: l).getD k 0 * (m :: l).getD k 0 := by
  rw [enc, if_neg (by omega), if_neg (by omega), if_pos (by omega), show (3 * k + 1) / 3 = k by omega]

theorem enc_3k2 (m a b : ℕ) (l : List ℕ) {k : ℕ} (hk : 1 ≤ k) :
    enc m a b l (3 * k + 2) = (m :: l).getD (k - 1) 0 / ((m :: l).getD k 0 * (m :: l).getD k 0) := by
  rw [enc, if_neg (by omega), if_neg (by omega), if_neg (by omega), show (3 * k + 2) / 3 = k by omega]

theorem levOf_3 (k : ℕ) : levOf (3 * k) = k := by
  rw [levOf, if_pos (by omega)]; omega
theorem levOf_3k1 (k : ℕ) : levOf (3 * k + 1) = k - 1 := by
  rw [levOf, if_neg (by omega)]; omega
theorem levOf_3k2 (k : ℕ) : levOf (3 * k + 2) = k - 1 := by
  rw [levOf, if_neg (by omega)]; omega

theorem lv_primeDescL {b l0 L A B v : ℕ} (hv : v < 3 * L + 3) :
    (primeDescL b l0 L A B).lv v = levOf v := by
  unfold LDesc.lv
  simp only [primeDescL]
  rw [List.getD_eq_getElem _ _ (by simpa using hv)]; simp

theorem getD_xlist (X : ℕ → ℕ) {L j : ℕ} (hj : j ≤ L) :
    (X 0 :: (List.range L).map fun k => X (3 * (k + 1))).getD j 0 = X (3 * j) := by
  rcases j with _ | j
  · simp
  · rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega)]; simp

theorem extV_lt {N : ℕ} (x : Fin N → ℕ) {v : ℕ} (hv : v < N) : extV N x v = x ⟨v, hv⟩ := by
  simp [extV, hv]

/-- The target set: `m ∈ [A, B]`, `(a, b)` with `a·b = m`, `a < b`, and a chain from `m`. -/
def primeSet (L A B : ℕ) : Finset (Σ _ : ℕ, (ℕ × ℕ) × List ℕ) :=
  (Icc A B).sigma fun m => ((Nat.divisorsAntidiagonal m).filter fun p => p.1 < p.2) ×ˢ chains L m

theorem card_primeSet (L A B : ℕ) :
    (primeSet L A B).card = ∑ m ∈ Icc A B, tauLt m * chainCount L m := by
  rw [primeSet, card_sigma]
  exact sum_congr rfl fun m _ => by rw [card_product, card_chains]; rfl

/-- Nonvanishing along a satisfying assignment. -/
theorem sat_ne_zero {L : ℕ} {X : ℕ → ℕ} (h0 : 1 ≤ X 0)
    (h1 : ∀ k ≤ L, X (3 * k + 1) * X (3 * k + 2) = X (3 * (k - 1)))
    (h2 : ∀ k, 1 ≤ k → k ≤ L → X (3 * k) * X (3 * k) = X (3 * k + 1)) :
    ∀ k ≤ L, X (3 * k) ≠ 0 := by
  intro k hk
  induction k with
  | zero => simp; omega
  | succ k ih =>
    intro h
    have e1 := h1 (k + 1) hk
    have e2 := h2 (k + 1) (by omega) hk
    rw [show k + 1 - 1 = k by omega, ← e2, h, zero_mul, zero_mul] at e1
    exact ih (by omega) e1.symm

/-- **The count of the description.** -/
theorem primeDescL_count {b l0 L A B n : ℕ} (bx : ℕ → ℕ) (hA : max A 1 < 2 ^ (b * l0))
    (hB : B < 2 ^ (b * l0)) (hBn : B < 2 ^ n) (hbx : ∀ k y, y ^ (2 ^ k) < 2 ^ n → y < bx k) :
    (primeDescL b l0 L A B).countB b bx = ∑ m ∈ Icc A B, tauLt m * chainCount L m := by
  rw [← card_primeSet]
  unfold LDesc.countB
  show ((Fintype.piFinset fun v : Fin (3 * L + 3) => range (bx ((primeDescL b l0 L A B).lv v))).filter
    fun x => (primeDescL b l0 L A B).D.Sat b (extV (3 * L + 3) x)).card = _
  refine card_bij'
    (fun x _ => ⟨extV (3 * L + 3) x 0, ((extV (3 * L + 3) x 1, extV (3 * L + 3) x 2),
      (List.range L).map fun k => extV (3 * L + 3) x (3 * (k + 1)))⟩)
    (fun y _ => fun v : Fin (3 * L + 3) => enc y.1 y.2.1.1 y.2.1.2 y.2.2 v) ?_ ?_ ?_ ?_
  · -- maps into the target
    intro x hx
    rw [mem_filter, primeDescL_sat hA hB] at hx
    obtain ⟨-, hA1, hB1, hab, h1, h2⟩ := hx
    set X := extV (3 * L + 3) x
    have hne := sat_ne_zero (le_trans (le_max_right A 1) hA1) h1 h2
    simp only [primeSet, mem_sigma, mem_Icc, mem_product, mem_filter, Nat.mem_divisorsAntidiagonal]
    have hX0 := le_trans (le_max_right A 1) hA1
    refine ⟨⟨le_trans (le_max_left A 1) hA1, hB1⟩, ⟨⟨?_, by omega⟩, hab⟩, ?_⟩
    · simpa using h1 0 (by omega)
    · rw [mem_chains]
      refine ⟨by simp, fun k hk => ?_⟩
      rw [getD_xlist X (by omega), getD_xlist X (by omega)]
      refine ⟨?_, hne k (by omega)⟩
      rw [h2 (k + 1) (by omega) (by omega)]
      have e := h1 (k + 1) (by omega)
      rw [show k + 1 - 1 = k by omega] at e
      exact Dvd.intro _ e
  · -- the inverse maps into the filter
    rintro ⟨m, ⟨a, b'⟩, l⟩ hy
    simp only [primeSet, mem_sigma, mem_Icc, mem_product, mem_filter,
      Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨⟨hAm, hmB⟩, ⟨⟨hab, hm0⟩, hlt⟩, hl⟩ := hy
    have hcp := chain_pow_le hm0 hl
    have hl' := (mem_chains.1 hl)
    have hX : ∀ v < 3 * L + 3, extV (3 * L + 3) (fun v : Fin (3 * L + 3) => enc m a b' l v) v =
        enc m a b' l v := fun v hv => by rw [extV_lt _ hv]
    rw [mem_filter, Fintype.mem_piFinset]
    constructor
    · intro v
      rw [mem_range]
      show enc m a b' l v < bx ((primeDescL b l0 L A B).lv v)
      rw [lv_primeDescL v.isLt]
      have hv := v.isLt
      have hmn : m < 2 ^ n := by omega
      obtain ⟨k, r, hr, hvk⟩ : ∃ k r, r < 3 ∧ (v : ℕ) = 3 * k + r := ⟨v / 3, v % 3, by omega, by omega⟩
      rw [hvk]
      have hk : k ≤ L := by omega
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
      · rw [add_zero, enc_3, levOf_3]
        exact hbx _ _ (lt_of_le_of_lt (hcp k hk).2 hmn)
      · rw [levOf_3k1]
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · rw [show 3 * 0 + 1 = 1 from rfl, enc_1]; apply hbx; simp
          exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (Dvd.intro _ hab)) hmn
        · rw [enc_3k1 _ _ _ _ hk1]
          apply hbx
          have : ((m :: l).getD k 0 * (m :: l).getD k 0) ^ 2 ^ (k - 1) = (m :: l).getD k 0 ^ 2 ^ k := by
            obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            rw [show j + 1 - 1 = j by omega, ← sq, ← pow_mul, ← pow_succ']
          rw [this]; exact lt_of_le_of_lt (hcp k hk).2 hmn
      · rw [levOf_3k2]
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · rw [show 3 * 0 + 2 = 2 by rfl, enc_2]; apply hbx; simp
          exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (Dvd.intro_left _ hab)) hmn
        · rw [enc_3k2 _ _ _ _ hk1]
          apply hbx
          refine lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.div_le_self _ _) _) ?_
          exact lt_of_le_of_lt (hcp (k - 1) (by omega)).2 hmn
    · rw [primeDescL_sat hA hB]
      rw [hX 0 (by omega), hX 1 (by omega), hX 2 (by omega)]
      rw [enc_0, enc_1, enc_2]
      refine ⟨max_le hAm (Nat.pos_of_ne_zero hm0), hmB, hlt, fun k hk => ?_, fun k hk1 hk => ?_⟩
      · rw [hX _ (by omega), hX _ (by omega), hX _ (by omega)]
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · simpa [enc_0, enc_1, enc_2] using hab
        · rw [enc_3k1 _ _ _ _ hk1, enc_3k2 _ _ _ _ hk1, enc_3]
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          have := (hl'.2 j (by omega)).1
          rw [show j + 1 - 1 = j by omega]
          exact Nat.mul_div_cancel' this
      · rw [hX _ (by omega), hX _ (by omega), enc_3, enc_3k1 _ _ _ _ hk1]
  · -- left inverse
    intro x hx
    rw [mem_filter, primeDescL_sat hA hB] at hx
    obtain ⟨-, hA1, hB1, hab, h1, h2⟩ := hx
    set X := extV (3 * L + 3) x with hXdef
    have hne := sat_ne_zero (le_trans (le_max_right A 1) hA1) h1 h2
    funext v
    have hv := v.isLt
    have hxv : x v = X v := (extV_lt x hv).symm
    rw [hxv]
    obtain ⟨k, r, hr, hvk⟩ : ∃ k r, r < 3 ∧ (v : ℕ) = 3 * k + r := ⟨v / 3, v % 3, by omega, by omega⟩
    try simp only
    rw [hvk]
    have hk : k ≤ L := by omega
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
    · rw [add_zero, enc_3, getD_xlist X hk]
    · rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [show 3 * 0 + 1 = 1 from rfl, enc_1]
      · rw [enc_3k1 _ _ _ _ hk1, getD_xlist X hk, h2 k hk1 hk]
    · rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [show 3 * 0 + 2 = 2 by rfl, enc_2]
      · rw [enc_3k2 _ _ _ _ hk1, getD_xlist X hk, getD_xlist X (by omega), h2 k hk1 hk, ← h1 k hk]
        have : 0 < X (3 * k + 1) := by
          rw [← h2 k hk1 hk]; exact Nat.mul_pos (Nat.pos_of_ne_zero (hne k hk))
            (Nat.pos_of_ne_zero (hne k hk))
        exact Nat.mul_div_cancel_left _ this
  · -- right inverse
    rintro ⟨m, ⟨a, b'⟩, l⟩ hy
    simp only [primeSet, mem_sigma, mem_product] at hy
    have hlen := (mem_chains.1 hy.2.2).1
    have hX : ∀ v < 3 * L + 3, extV (3 * L + 3) (fun v : Fin (3 * L + 3) => enc m a b' l v) v =
        enc m a b' l v := fun v hv => by rw [extV_lt _ hv]
    try simp only
    rw [hX 0 (by omega), hX 1 (by omega), hX 2 (by omega), enc_0, enc_1, enc_2]
    have hlist : ((List.range L).map fun k =>
        extV (3 * L + 3) (fun v : Fin (3 * L + 3) => enc m a b' l v) (3 * (k + 1))) = l := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [hX _ (by simp at h1; omega), enc_3, List.getD_cons_succ, List.getD_eq_getElem _ _ h2]
    rw [hlist]
    try rfl

/-- **Parity of the count** = parity of the number of primes in `[A, B]` (depth `L`, `B < 2^{2^L}`). -/
theorem primeDescL_count_mod_two {b l0 L A B n : ℕ} (bx : ℕ → ℕ) (hA : max A 1 < 2 ^ (b * l0))
    (hB : B < 2 ^ (b * l0)) (hBn : B < 2 ^ n) (hbx : ∀ k y, y ^ (2 ^ k) < 2 ^ n → y < bx k)
    (hBL : B < 2 ^ 2 ^ L) :
    (primeDescL b l0 L A B).countB b bx % 2 = ((Icc A B).filter Nat.Prime).card % 2 := by
  rw [primeDescL_count bx hA hB hBn hbx, primeParity hBL]

theorem primeL_eq_size (n : ℕ) : primeL n = Nat.size n := Nat.size_eq_bits_len n

theorem primeL_spec (n : ℕ) : 2 ^ n < 2 ^ 2 ^ primeL n := by
  apply Nat.pow_lt_pow_right (by norm_num)
  rw [primeL_eq_size]; exact Nat.lt_size_self n

/-- **The count for `n`-bit inputs, mod 2.** -/
theorem primeDesc_count_mod_two {b l0 n A B : ℕ} (bx : ℕ → ℕ) (hA : max A 1 < 2 ^ (b * l0))
    (hB : B < 2 ^ (b * l0)) (hBn : B < 2 ^ n) (hbx : ∀ k y, y ^ (2 ^ k) < 2 ^ n → y < bx k) :
    (primeDesc b l0 n A B).countB b bx % 2 = ((Icc A B).filter Nat.Prime).card % 2 :=
  primeDescL_count_mod_two bx hA hB hBn hbx (lt_trans hBn (primeL_spec n))

/-! ## Well-formedness, spread, levels -/

theorem chain_hasProd {L c p : ℕ} (hc : c < 2 * L + 1) :
    (((List.range (2 * L + 1)).map chainOfIdx).getD c default).HasProd p ↔
      p = 2 * c ∨ p = 2 * c + 1 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc)]
  simp [chainOfIdx, ChainD.HasProd]
  constructor <;> rintro (h | h) <;> omega

theorem chainOf_primeDescL {b l0 L A B p : ℕ} (hp : p < 4 * L + 2) :
    (primeDescL b l0 L A B).D.chainOf p = p / 2 := by
  have hc : p / 2 < 2 * L + 1 := by omega
  obtain ⟨h1, h2⟩ := Desc.chainOf_spec (D := (primeDescL b l0 L A B).D) (p := p) (c := p / 2)
    (by simpa [primeDescL] using hc) ((chain_hasProd hc).2 (by omega))
  have hlt : (primeDescL b l0 L A B).D.chainOf p < 2 * L + 1 := by omega
  rw [show (primeDescL b l0 L A B).D.chains = (List.range (2 * L + 1)).map chainOfIdx from rfl,
    chain_hasProd hlt] at h2
  omega

theorem lc_primeDescL {b l0 L A B c : ℕ} (hc : c < 2 * L + 1) :
    (primeDescL b l0 L A B).lc c = (c - 1) / 2 := by
  unfold LDesc.lc
  simp only [primeDescL]
  rw [List.getD_eq_getElem _ _ (by simpa using hc)]; simp

theorem lp_primeDescL {b l0 L A B p : ℕ} (hp : p < 4 * L + 2) :
    (primeDescL b l0 L A B).lp p = (p / 2 - 1) / 2 := by
  unfold LDesc.lp
  rw [chainOf_primeDescL hp, lc_primeDescL (by omega)]

theorem lv_le {b l0 L A B : ℕ} (v : ℕ) : (primeDescL b l0 L A B).lv v ≤ L := by
  by_cases hv : v < 3 * L + 3
  · rw [lv_primeDescL hv, levOf]; split_ifs <;> omega
  · unfold LDesc.lv
    rw [List.getD_eq_default _ _ (by simp [primeDescL]; omega)]; exact Nat.zero_le _

theorem lc_le {b l0 L A B : ℕ} (c : ℕ) : (primeDescL b l0 L A B).lc c ≤ L := by
  by_cases hc : c < 2 * L + 1
  · rw [lc_primeDescL hc]; omega
  · unfold LDesc.lc
    rw [List.getD_eq_default _ _ (by simp [primeDescL]; omega)]; exact Nat.zero_le _

theorem foldr_max_le {l : List ℕ} {c : ℕ} (h : ∀ x ∈ l, x ≤ c) : l.foldr max 0 ≤ c := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- All levels are `≤ L`: `nL ≤ L + 1`. -/
theorem nL_le {b l0 L A B : ℕ} : (primeDescL b l0 L A B).nL ≤ L + 1 := by
  unfold LDesc.nL
  have h1 : (primeDescL b l0 L A B).lev.foldr max 0 ≤ L := foldr_max_le fun x hx => by
    simp only [primeDescL, List.mem_map, List.mem_range] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [levOf]; split_ifs <;> omega
  have h2 : (primeDescL b l0 L A B).levC.foldr max 0 ≤ L := foldr_max_le fun x hx => by
    simp only [primeDescL, List.mem_map, List.mem_range] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    omega
  exact Nat.add_le_add_right (sup_le h1 h2) 1

theorem primeL_le (n : ℕ) : primeL n ≤ Nat.log 2 (n + 2) + 1 := by
  rw [primeL_eq_size, Nat.size_le]
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n + 2)
  omega

/-- **Well-formedness** for any limb counts `lk` with `lk 0 = l0` and `lk k ≥ 1` (`b ≥ 1`). -/
theorem primeDescL_WF {b l0 L A B : ℕ} (lk : ℕ → ℕ) (hb : 1 ≤ b) (hl0 : lk 0 = l0)
    (hlk : ∀ k, 1 ≤ lk k) : (primeDescL b l0 L A B).WFB b lk where
  pat_len := by intro v _; simp [primeDescL]
  prod_ok := by
    intro p hp
    have hp' : p < 4 * L + 2 := by simpa [primeDescL] using hp
    have h1b : (1 : ℕ) < 2 ^ b :=
      lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hb)
    rw [show (primeDescL b l0 L A B).D.prods.getD p default = prodOf p from getD_prods hp',
      lp_primeDescL hp', chainOf_primeDescL hp']
    have hnC : (primeDescL b l0 L A B).D.chains.length = 2 * L + 1 := by simp [primeDescL]
    have hnV : (primeDescL b l0 L A B).D.nV = 3 * L + 3 := rfl
    obtain ⟨k, r, hr, hpk⟩ : ∃ k r, r < 4 ∧ p + 2 = 4 * k + r :=
      ⟨(p + 2) / 4, (p + 2) % 4, by omega, by omega⟩
    rw [prodOf, show (p + 2) / 4 = k by omega, show (p + 2) % 4 = r by omega, hnC]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · rw [prodKR_0]; simp only [LDesc.OpOK, hnV]
      rw [lv_primeDescL (by omega), levOf_3]
      refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
    · rw [prodKR_1]; simp only [LDesc.OpOK, hnV]
      rw [lv_primeDescL (by omega), levOf_3k1]
      refine ⟨by omega, by omega, ⟨by simp [hlk], by simpa using h1b⟩, by omega⟩
    · rw [prodKR_2]; simp only [LDesc.OpOK, hnV]
      rw [lv_primeDescL (by omega), lv_primeDescL (by omega), levOf_3k1, levOf_3k2]
      refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega⟩
    · rw [prodKR_3]; simp only [LDesc.OpOK, hnV]
      rw [lv_primeDescL (by omega), levOf_3]
      refine ⟨by omega, by omega, ⟨by simp [hlk], by simpa using h1b⟩, by omega⟩
  term_ok := by
    intro c hc t ht
    have hc' : c < 2 * L + 1 := by simpa [primeDescL] using hc
    have hg : (primeDescL b l0 L A B).D.chains.getD c default = chainOfIdx c := by
      simp only [primeDescL]
      rw [List.getD_eq_getElem _ _ (by simpa using hc')]; simp
    rw [hg] at ht
    simp [chainOfIdx] at ht
    rcases ht with rfl | rfl <;> simp only [LDesc.SrcOK] <;> simp [primeDescL] <;> omega
  coeff_le := by simp [primeDescL, chainOfIdx]
  prod_once := by
    intro c hc c' hc' p h h'
    have e : (primeDescL b l0 L A B).D.chains = (List.range (2 * L + 1)).map chainOfIdx := rfl
    have hc1 : c < 2 * L + 1 := by simpa [primeDescL] using hc
    have hc2 : c' < 2 * L + 1 := by simpa [primeDescL] using hc'
    rw [e, chain_hasProd hc1] at h
    rw [e, chain_hasProd hc2] at h'
    omega
  cmp_ok := by
    intro q hq
    have hq' : q < 3 := by simpa [primeDescL] using hq
    have hlv0 : (primeDescL b l0 L A B).lv 0 = 0 := by rw [lv_primeDescL (by omega)]; rfl
    have hlv1 : (primeDescL b l0 L A B).lv 1 = 0 := by rw [lv_primeDescL (by omega)]; rfl
    have hlv2 : (primeDescL b l0 L A B).lv 2 = 0 := by rw [lv_primeDescL (by omega)]; rfl
    have hnV : (primeDescL b l0 L A B).D.nV = 3 * L + 3 := rfl
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
    · have hg : (primeDescL b l0 L A B).D.cmps.getD 0 default =
          ⟨0, .const (toLimbs b l0 (max A 1)), .ge⟩ := rfl
      have hq0 : (primeDescL b l0 L A B).lq 0 = 0 := by unfold LDesc.lq; rw [hg]; exact hlv0
      rw [hq0, hg, hnV]
      simp only [LDesc.CmpOK]
      exact ⟨by omega, by rw [length_toLimbs, hl0], toLimbs_lt _ _ _⟩
    · have hg : (primeDescL b l0 L A B).D.cmps.getD 1 default =
          ⟨0, .const (toLimbs b l0 B), .le⟩ := rfl
      have hq0 : (primeDescL b l0 L A B).lq 1 = 0 := by unfold LDesc.lq; rw [hg]; exact hlv0
      rw [hq0, hg, hnV]
      simp only [LDesc.CmpOK]
      exact ⟨by omega, by rw [length_toLimbs, hl0], toLimbs_lt _ _ _⟩
    · have hg : (primeDescL b l0 L A B).D.cmps.getD 2 default = ⟨1, .var 2, .lt⟩ := rfl
      have hq0 : (primeDescL b l0 L A B).lq 2 = 0 := by unfold LDesc.lq; rw [hg]; exact hlv1
      rw [hq0, hg, hnV]
      simp only [LDesc.CmpOK]
      exact ⟨by omega, by omega, hlv2⟩

/-- **Spread 8**: object `i` of each kind has level `≥ i / 8`. -/
theorem primeDescL_spread {b l0 L A B : ℕ} : (primeDescL b l0 L A B).Spread 8 where
  var := by
    intro v hv
    rw [lv_primeDescL hv, levOf]; split_ifs <;> omega
  prod := by
    intro p hp
    have hp' : p < 4 * L + 2 := by simpa [primeDescL] using hp
    rw [lp_primeDescL hp']; omega
  chain := by
    intro j hj
    rw [lc_primeDescL (by simpa [primeDescL] using hj)]; omega
  cmp := by
    intro q hq
    have hq' : q < 3 := by simpa [primeDescL] using hq
    rw [show q / 8 = 0 by omega]; exact Nat.zero_le _

end EthFollowup.Primes
