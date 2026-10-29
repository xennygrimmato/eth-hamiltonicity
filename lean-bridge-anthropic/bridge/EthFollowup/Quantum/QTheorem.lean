/-
# Theorem Q1 at Turing-machine level (fixed-density form): `amplitude_TM`

`research/quantum-circuits.md`, Theorem Q1, with the route of `theorem1` (Lemma 1 of Anthropic's
paper for a fixed level, `Given.stEveryEta`, `Printed.groupingLemma`, `Given.onSteps`), and
`CountKSat.exists_tmW` for the passage to one of Mathlib's Turing machines.

**`amplitude_TM`**: for every `δ > 0` there are a Turing machine (finite alphabets) and a constant
`C` such that for every Clifford+T circuit `C` (gates H, T, T†, S, S†, X, Z, CNOT, CZ, CS, SWAP, CH;
any connectivity) on `n` qubits and all basis states `x, y`, the machine started on
`circCode C x y` halts within `⌊C · 2^{δ·G} · (|word| + 2)^C⌋` steps (`G` = number of two-qubit
gates) with `outWord a k`, where `k` is the number of `H` and `CH` gates and the integers
`a₀, …, a₃` satisfy `⟨y|C|x⟩ = (a₀ + a₁ω + a₂ω² + a₃ω³)/√2^k`. The polynomial factor in the length
of the word (which is `Θ(n·(#gates))`) is what Q1's `poly(n + G₁)` becomes here.
-/
import EthFollowup.Quantum.QMachine
import EthFollowup.ExactHC.Assembly
import CountKSat.Host

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset Printed

/-! ### The output in polynomial time -/

theorem offK_eq (b : ℕ) :
    offK b = 2 ^ (b - 1) * 2 ^ (b * 0) + 2 ^ (b - 1) * 2 ^ (b * 1) + 2 ^ (b - 1) * 2 ^ (b * 2) +
      2 ^ (b - 1) * 2 ^ (b * 3) := by
  simp only [offK, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- One decoded digit, in natural numbers. -/
def decN (b r j : ℕ) : ℕ := (r + offK b) % Mb b / 2 ^ (b * j) % 2 ^ b

theorem decodeK_eq' (b r j : ℕ) : decodeK b r j = (decN b r j : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ) := by
  simp [decodeK, decN]

namespace QP

variable {γ : Type} [Enc γ]

theorem offK_polyT {b : γ → ℕ} (hb : Unary b) : PolyT fun x => offK (b x) := by
  have h0 : Unary fun x => b x - 1 := Unary.of_le hb (PolyT.sub hb.poly (PolyT.const 1)) fun x => Nat.sub_le _ _
  have hp : PolyT fun x => 2 ^ (b x - 1) := PolyT.two_pow h0
  have hq : ∀ j : ℕ, PolyT fun x => 2 ^ (b x * j) := fun j => PolyT.two_pow (hb.mul (Unary.const j))
  exact (PolyT.add (PolyT.add (PolyT.add (PolyT.mul hp (hq 0)) (PolyT.mul hp (hq 1))) (PolyT.mul hp (hq 2)))
    (PolyT.mul hp (hq 3))).congr fun x => (offK_eq _).symm

theorem decodeK_polyT {b r : γ → ℕ} (hb : Unary b) (hr : PolyT r) (j : ℕ) :
    PolyT fun x => decodeK (b x) (r x) j := by
  have h0 : Unary fun x => b x - 1 := Unary.of_le hb (PolyT.sub hb.poly (PolyT.const 1)) fun x => Nat.sub_le _ _
  have hp : PolyT fun x => 2 ^ (b x - 1) := PolyT.two_pow h0
  have hM : PolyT fun x => Mb (b x) := by
    unfold Mb; exact PolyT.add (PolyT.two_pow ((Unary.const 4).mul hb)) (PolyT.const 1)
  have hq : PolyT fun x => 2 ^ (b x * j) := PolyT.two_pow (hb.mul (Unary.const j))
  have h2 : PolyT fun x => 2 ^ b x := PolyT.two_pow hb
  have ho := offK_polyT hb
  have hd : PolyT fun x => decN (b x) (r x) j := by
    unfold decN
    exact PolyT.mod (PolyT.div (PolyT.mod (PolyT.add hr ho) hM) hq) h2
  exact (PolyT.subZ (PolyT.natCast hd) (PolyT.natCast hp)).congr fun x => (decodeK_eq' _ _ _).symm

theorem natWord_polyT {k : γ → ℕ} (hk : PolyT k) : PolyT fun x => natWord (k x) := by
  unfold natWord; fun_prop

theorem intWord_polyT {z : γ → ℤ} (hz : PolyT z) : PolyT fun x => intWord (z x) := by
  have := natWord_polyT (PolyT.natAbs hz)
  have hd : PolyT fun x => decide (z x < 0) := PolyT.decide_ltZ hz (PolyT.const 0)
  unfold intWord; fun_prop

theorem bW_unary : Unary fun p : List Bool × ℤ => bW p.1 := bK_unary.comp PolyT.id'.fst

theorem finQ_polyT : PolyT finQ := by
  have hb := bW_unary
  have hM : PolyT fun p : List Bool × ℤ => Mb (bW p.1) := by
    unfold Mb; exact PolyT.add (PolyT.two_pow ((Unary.const 4).mul hb)) (PolyT.const 1)
  have hr : PolyT fun p : List Bool × ℤ => p.2.toNat % Mb (bW p.1) := PolyT.mod (PolyT.toNat PolyT.id'.snd) hM
  have hd : ∀ j, PolyT fun p : List Bool × ℤ => intWord (decodeK (bW p.1) (p.2.toNat % Mb (bW p.1)) j) :=
    fun j => intWord_polyT (decodeK_polyT hb hr j)
  have hk : PolyT fun p : List Bool × ℤ => natWord (((readQ p.1).2.2.2.map fun c => kapC c.1).sum) := by
    have h222 : PolyT fun p : List Bool × ℤ => (readQ p.1).2.2.2 := readQ_222.comp PolyT.id'.fst
    refine natWord_polyT ?_
    unfold kapC; fun_prop
  have := hd 0; have := hd 1; have := hd 2; have := hd 3
  unfold finQ outWord
  exact (by fun_prop : PolyT fun p : List Bool × ℤ =>
    intWord (decodeK (bW p.1) (p.2.toNat % Mb (bW p.1)) 0) ++ intWord (decodeK (bW p.1) (p.2.toNat % Mb (bW p.1)) 1) ++
      intWord (decodeK (bW p.1) (p.2.toNat % Mb (bW p.1)) 2) ++ intWord (decodeK (bW p.1) (p.2.toNat % Mb (bW p.1)) 3) ++
      natWord (((readQ p.1).2.2.2.map fun c => kapC c.1).sum))

end QP

theorem qM_poly (g : ℕ) (NM : NetMachine) (hN : NM.PolyTimeSteps) : Nonempty (IsPolyT (qM g NM)) := by
  obtain ⟨i1⟩ := networkOnSteps_poly g NM qNp hN qNp_keeps qNp_P qNp_B
  have : IsPolyT (mainQ g NM) := IsPolyT.mapIn (QP.prepQ_polyT g)
  have : IsPolyT (Stepped.ofFun finQ) := IsPolyT.ofFun QP.finQ_polyT
  exact ⟨IsPolyT.bind⟩

/-! ### Counting -/

theorem scan_len : ∀ (cs : List GC) (st : SS),
    (cs.foldl scanStep st).1.length = st.1.length + (cs.filter fun c => decide (7 ≤ c.1)).length
  | [], _ => by simp
  | c :: cs, st => by
    rw [List.foldl_cons, scan_len cs, scanStep_length, List.filter_cons]
    by_cases h : 7 ≤ c.1
    · simp [h]; omega
    · simp [h]

/-- The number of blocks is the number of two-qubit gates. -/
theorem twoCount_eq {n : ℕ} (C : List (Gate n)) : (stC C).1.length = twoCount C := by
  unfold stC scan
  rw [scan_len]
  simp only [scanInit, List.length_nil, zero_add, codes, twoCount, List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun g _ => ?_
  cases g with
  | one u q => cases u <;> rfl
  | two u q₁ q₂ h => cases u <;> rfl

theorem twoCount_le {n : ℕ} (C : List (Gate n)) : twoCount C ≤ C.length := List.length_filter_le _ _

theorem length_circCode {n : ℕ} (C : List (Gate n)) (x y : Basis n) :
    (circCode C x y).length = n + 1 + n + n + C.length * (4 + 2 * n) := by
  simp only [circCode, List.length_append, List.length_replicate, List.length_cons, List.length_nil,
    List.length_ofFn, List.length_flatMap, length_gateWord, List.map_const', List.sum_replicate, smul_eq_mul]
  try ring

theorem length_cl_le (st : SS) (g : ℕ) [NeZero g] : (cpart st g).cl.length ≤ 2 * st.1.length := by
  rw [length_cl]
  have h1 : (clN st g).length ≤ (allN st.1.length).length := List.length_filter_le _ _
  have h2 : (allN st.1.length).length = 2 * st.1.length := by
    rw [← allV_map, List.length_map]
    simp [allV, List.length_product]; ring
  omega

/-! ### Sizes of values are at most the lengths of their words -/

class SizeLe (α : Type) [Enc α] [HasSize α] : Prop where
  le : ∀ x : α, size x ≤ len x

instance : SizeLe ℕ := ⟨fun k => by rw [len_nat]; show k.size + 1 ≤ _; omega⟩
instance : SizeLe Bool := ⟨fun b => by rw [len_bool]; exact le_rfl⟩
instance : SizeLe Unit := ⟨fun u => by rw [len_unit]; show 1 ≤ 2; omega⟩
instance {α β : Type} [Enc α] [HasSize α] [Enc β] [HasSize β] [SizeLe α] [SizeLe β] : SizeLe (α × β) :=
  ⟨fun p => by
    rw [len_pair]; have := SizeLe.le p.1; have := SizeLe.le p.2
    show size p.1 + size p.2 ≤ _; omega⟩
instance {α : Type} [Enc α] [HasSize α] [SizeLe α] : SizeLe (List α) :=
  ⟨fun l => by
    induction l with
    | nil => rw [len_nil]; show 0 + 1 ≤ 2; omega
    | cons a l ih =>
      rw [len_cons]
      have := SizeLe.le a
      have e : size (a :: l) = size a + 1 + size l := by
        show ((a :: l).map fun x => size x + 1).sum + 1 = size a + 1 + ((l.map fun x => size x + 1).sum + 1)
        rw [List.map_cons, List.sum_cons]; omega
      omega⟩

/-! ### The exponent -/

theorem expo_le {e δ : ℝ} {g K G U P : ℕ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK1 : 1 ≤ K) (hKg : K ≤ g)
    (hU : U ≤ 4 * G) (hP : P = 4 * (G / g + 1)) (he : 4 * e ≤ δ / 4) (hKδ : 14 ≤ δ / 4 * K) :
    e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K + ((2 * (G / g + 1) + 1 : ℕ) : ℝ) ≤
      δ / 2 * G + ((12 * g + 3 : ℕ) : ℝ) := by
  have hg1 : 1 ≤ g := hK1.trans hKg
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg1
  have hKgr : (K : ℝ) ≤ g := by exact_mod_cast hKg
  have hq : ((G / g : ℕ) : ℝ) * g ≤ G := by exact_mod_cast Nat.div_mul_le_self G g
  have hq' : ((G / g : ℕ) : ℝ) ≤ G / K := by
    rw [le_div_iff₀ hK0]
    calc ((G / g : ℕ) : ℝ) * K ≤ ((G / g : ℕ) : ℝ) * g := by gcongr
      _ ≤ G := hq
  have hPr : (P : ℝ) = 4 * ((G / g : ℕ) : ℝ) + 4 := by rw [hP]; push_cast; ring
  have hgP : (g : ℝ) * P ≤ 4 * G + 4 * g := by rw [hPr]; nlinarith
  have hgP0 : 0 ≤ (g : ℝ) * P := by positivity
  have h1 : (g : ℝ) * P / K ≤ 4 * (G / K) + 4 * g := by
    rw [div_le_iff₀ hK0]
    have : 4 * ((G : ℝ) / K) * K = 4 * G := by field_simp
    nlinarith
  have hUr : (U : ℝ) ≤ 4 * G := by exact_mod_cast hU
  have hG0 : (0 : ℝ) ≤ G := by positivity
  have hGK : 14 * ((G : ℝ) / K) ≤ δ / 4 * G := by
    rw [mul_div_assoc', div_le_iff₀ hK0]; nlinarith
  have h2 : e * ((U : ℝ) + (g : ℝ) * P / K) ≤ 4 * e * G + (g : ℝ) * P / K := by
    have : 0 ≤ (g : ℝ) * P / K := by positivity
    nlinarith
  have h3 : 2 * ((g : ℝ) * P) / K = 2 * ((g : ℝ) * P / K) := by ring
  have h4 : 4 * e * (G : ℝ) ≤ δ / 4 * G := by nlinarith
  push_cast
  rw [h3]
  nlinarith

/-! ### The machine on one circuit -/

open Asm in
/-- **The stepped machine on every circuit**: the output word within `A (L+2)^A 2^{(δ/2) G}` steps on
states of size `A (L+2)^A` (`L` the length of the word, `G` the number of two-qubit gates). -/
theorem qM_bound {NM : NetMachine} {C₁ K g : ℕ} [NeZero g] {e δ : ℝ} (hNM : ComputesNetworks NM C₁ g K e)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK1 : 1 ≤ K) (hKg : K ≤ g) (he : 4 * e ≤ δ / 4) (hKδ : 14 ≤ δ / 4 * K) :
    ∃ A : ℕ, ∀ {n : ℕ} (C : List (Gate n)) (x y : Basis n), ∃ T : ℕ,
      (qM g NM).Runs (circCode C x y) T (A * ((circCode C x y).length + 2) ^ A)
        (outWord (fun j => decodeK (bC C) ((((XC g C x y).net boolCode).value).toNat % MC C) j.val) (hcount C)) ∧
      (T : ℝ) ≤ A * (((circCode C x y).length : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * twoCount C) := by
  obtain ⟨-, cP, -, hlenP⟩ := QP.prepQ_polyT g
  obtain ⟨-, cF, -, hlenF⟩ := QP.finQ_polyT
  -- explicit bounds in the length `L` of the word
  have pB : ∀ L, Pol 1 L L := fun L => Pol.id
  obtain ⟨Ab, hb⟩ : ∃ A, ∀ L, Pol A L ((L + 1) * L + 2) :=
    ⟨_, fun L => Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 1)) Pol.id) (Pol.const 2)⟩
  obtain ⟨AB, hB⟩ : ∃ A, ∀ L, Pol A L (2 * L + 4 * ((L + 1) * L + 2) + 2) :=
    ⟨_, fun L => Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.mul (Pol.const 4) (hb L))) (Pol.const 2)⟩
  obtain ⟨Ac, hc⟩ : ∃ A, ∀ L, Pol A L (cP * (3 * L + 3) ^ cP) :=
    ⟨_, fun L => Pol.mul (Pol.const cP) (Pol.pow (Pol.add (Pol.mul (Pol.const 3) Pol.id) (Pol.const 3)) cP)⟩
  set fB : ℕ → ℕ := fun L => 2 * L + 4 * ((L + 1) * L + 2) + 2
  set fc : ℕ → ℕ := fun L => cP * (3 * L + 3) ^ cP
  set fZ : ℕ → ℕ := fun L => 2 * L + g * fB L + 2
  obtain ⟨AZ, hZ⟩ : ∃ A, ∀ L, Pol A L (fZ L) :=
    ⟨_, fun L => Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.mul (Pol.const g) (hB L))) (Pol.const 2)⟩
  set fO : ℕ → ℕ := fun L => cF * ((3 * L + 2) + (3 * fZ L + 5) + 2 + 1) ^ cF
  obtain ⟨AO, hO⟩ : ∃ A, ∀ L, Pol A L (fO L) :=
    ⟨_, fun L => Pol.mul (Pol.const cF) (Pol.pow (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 3) Pol.id)
      (Pol.const 2)) (Pol.add (Pol.mul (Pol.const 3) (hZ L)) (Pol.const 5))) (Pol.const 2)) (Pol.const 1)) cF)⟩
  set fPB : ℕ → ℕ := fun L => (4 * L + 4) + fB L
  obtain ⟨APB, hPB⟩ : ∃ A, ∀ L, Pol A L (fPB L ^ C₁) :=
    ⟨_, fun L => Pol.pow (Pol.add (Pol.add (Pol.mul (Pol.const 4) Pol.id) (Pol.const 4)) (hB L)) C₁⟩
  set fS : ℕ → ℕ := fun L => (2 * L + 1) + (fc L + C₁ * fPB L ^ C₁ +
      ((5 * fc L + 4 * (4 * L + 4) + 6 * (L + 1) + 20) + fc L + 2 * g + 4 * (4 * L + 4) + 8) + 4) +
      (2 * L + 1 + fZ L) + fO L + 4
  obtain ⟨AS, hS⟩ : ∃ A, ∀ L, Pol A L (fS L) :=
    ⟨_, fun L => Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1))
      (Pol.add (Pol.add (Pol.add (hc L) (Pol.mul (Pol.const C₁) (hPB L)))
        (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 5) (hc L))
          (Pol.mul (Pol.const 4) (Pol.add (Pol.mul (Pol.const 4) Pol.id) (Pol.const 4))))
          (Pol.mul (Pol.const 6) (Pol.add Pol.id (Pol.const 1)))) (Pol.const 20)) (hc L)) (Pol.const (2 * g)))
          (Pol.mul (Pol.const 4) (Pol.add (Pol.mul (Pol.const 4) Pol.id) (Pol.const 4)))) (Pol.const 8)))
        (Pol.const 4)))
      (Pol.add (Pol.add (Pol.mul (Pol.const 2) Pol.id) (Pol.const 1)) (hZ L))) (hO L)) (Pol.const 4)⟩
  set fT : ℕ → ℕ := fun L => 3 * C₁ * 2 ^ (12 * g + 3) * fPB L ^ C₁ + 2
  obtain ⟨AT, hT⟩ : ∃ A, ∀ L, Pol A L (fT L) :=
    ⟨_, fun L => Pol.add (Pol.mul (Pol.const (3 * C₁ * 2 ^ (12 * g + 3))) (hPB L)) (Pol.const 2)⟩
  refine ⟨AS + AT, fun {n} C x y => ?_⟩
  -- the run
  set w := circCode C x y
  set L := w.length with hLdef
  set N := (XC g C x y).net boolCode
  set Z := N.value
  set P := PQ (stC C) g
  set B := BQ (stC C) (bC C)
  set G := (stC C).1.length with hGdef
  obtain ⟨T, hrun, hTle⟩ := (Given.onSteps hNM (qGiven g C x y)).2
  have hmain : (mainQ g NM).Runs w T (size (cC g C x y) + C₁ * (P + B) ^ C₁ +
      (SQ (stC C) g (cC g C x y) P + size (cC g C x y) + 2 * g + 4 * P + 8) + 4) Z :=
    Stepped.mapIn_runs (by rw [prep_cC]; exact hrun)
  have hout : finQ (w, Z) =
      outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C) := by
    unfold finQ bW
    simp only [w, readQ_code, List.length_replicate, length_codes, hcount_eq]
  have hfin := Stepped.ofFun_runs finQ (w, Z)
  rw [hout] at hfin
  have hrun2 := Stepped.bind_runs hmain hfin
  -- facts about the length
  have hlen : L = n + 1 + n + n + C.length * (4 + 2 * n) := length_circCode C x y
  have hn : n ≤ L := by omega
  have hm : C.length ≤ L := by nlinarith
  have hG : G ≤ L := by rw [hGdef, twoCount_eq]; exact (twoCount_le C).trans hm
  have hbb : bC C ≤ (L + 1) * L + 2 := by
    show (n + 1) * C.length + 2 ≤ _; have := Nat.mul_le_mul (Nat.add_le_add_right hn 1) hm; omega
  have hBB : B ≤ fB L := by show 2 * G + 4 * bC C + 2 ≤ _; simp only [fB]; omega
  have hgG : G / g ≤ L := (Nat.div_le_self _ _).trans hG
  have hPP : P ≤ 4 * L + 4 := by show 4 * (G / g + 1) ≤ _; omega
  have hlw : len w = 3 * L + 2 := len_bools w
  have hcc : size (cC g C x y) ≤ fc L := by
    have h1 : size (cC g C x y) ≤ len (cC g C x y) := SizeLe.le _
    have h2 := hlenP w
    rw [prep_cC, hlw] at h2
    exact h1.trans h2
  have hsw : size w = 2 * L + 1 := LabelSystem.size_word w
  -- the value
  have hK := length_cl_le (stC C) g
  have hZnat : Z.natAbs.size ≤ 2 * L + g * fB L + 1 := by
    have h1 := value_le g C x y
    have h2 : Z.natAbs < 2 ^ ((cpart (stC C) g).cl.length + g * B + 1) :=
      lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
    have h3 := Nat.size_le.2 h2
    have h4 : g * B ≤ g * fB L := Nat.mul_le_mul_left _ hBB
    omega
  have hZs : size Z ≤ fZ L := by show Z.natAbs.size + 1 ≤ _; simp only [fZ]; omega
  have hOs : size (outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C)) ≤ fO L := by
    have h1 := SizeLe.le (outWord (fun j => decodeK (bC C) (Z.toNat % MC C) j.val) (hcount C))
    have h2 := hlenF (w, Z)
    rw [hout, len_pair, hlw, len_int] at h2
    refine h1.trans (h2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)))
    simp only [fZ]; omega
  have hSQ : SQ (stC C) g (cC g C x y) P ≤ 5 * fc L + 4 * (4 * L + 4) + 6 * (L + 1) + 20 := by
    have e : SQ (stC C) g (cC g C x y) P = 5 * size (cC g C x y) + 4 * P + 6 * (G / g + 1) + 20 := rfl
    omega
  have hPBle : (P + B) ^ C₁ ≤ fPB L ^ C₁ := Nat.pow_le_pow_left (by simp only [fPB]; omega) _
  refine ⟨T + 1 + 1, hrun2.mono le_rfl ?_, ?_⟩
  · -- the states
    refine le_trans ?_ ((hS L).mono (Nat.le_add_right _ _))
    have h1 : size (w, Z) = size w + size Z := rfl
    have h2 := Nat.mul_le_mul_left C₁ hPBle
    simp only [fS]
    rw [h1]
    simp only [max_def]
    split_ifs <;> omega
  · -- the steps
    have hU : N.U ≤ 4 * G := by
      have := LabelSystem.U_eq (XC g C x y) boolCode
      simp only [Fintype.card_fin, Fintype.card_eq_zero, add_zero, mul_one] at this
      show N.U ≤ _; rw [this]; omega
    have hX := expo_le (g := g) (K := K) (G := G) (U := N.U) (P := P) he0 he1 hK1 hKg hU rfl he hKδ
    have hτ : (τQ (stC C) g : ℝ) = (2 : ℝ) ^ (((2 * (G / g + 1) + 1 : ℕ)) : ℝ) := by
      rw [Real.rpow_natCast]; unfold τQ; push_cast; ring
    set X : ℝ := e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K
    have h2X : (2 : ℝ) ^ X * (τQ (stC C) g : ℝ) ≤ (2 : ℝ) ^ (12 * g + 3) * (2 : ℝ) ^ (δ / 2 * G) := by
      rw [hτ, ← Real.rpow_add two_pos, show (2 : ℝ) ^ (12 * g + 3) = (2 : ℝ) ^ ((12 * g + 3 : ℕ) : ℝ) by
        rw [Real.rpow_natCast], ← Real.rpow_add two_pos]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    have hPBR : ((P : ℝ) + B) ^ C₁ ≤ (fPB L : ℝ) ^ C₁ := by exact_mod_cast hPBle
    have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * G) := by
      have : 0 ≤ δ := by nlinarith
      exact Real.one_le_rpow one_le_two (by positivity)
    have hTL : ((fT L : ℕ) : ℝ) ≤ ((AS + AT : ℕ) : ℝ) * ((L : ℝ) + 2) ^ (AS + AT) := by
      have := (hT L).mono (Nat.le_add_left AT AS)
      unfold Pol at this; exact_mod_cast this
    have htw : twoCount C = G := (twoCount_eq C).symm
    rw [htw]
    calc ((T + 1 + 1 : ℕ) : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ X * ((P : ℝ) + B) ^ C₁) * (τQ (stC C) g) + 2 := by
          push_cast; linarith
      _ = 3 * C₁ * ((P : ℝ) + B) ^ C₁ * ((2 : ℝ) ^ X * (τQ (stC C) g : ℝ)) + 2 := by ring
      _ ≤ 3 * C₁ * (fPB L : ℝ) ^ C₁ * ((2 : ℝ) ^ (12 * g + 3) * (2 : ℝ) ^ (δ / 2 * G)) +
            2 * (2 : ℝ) ^ (δ / 2 * G) := by
          have : (0 : ℝ) ≤ 3 * C₁ := by positivity
          gcongr
          linarith
      _ = ((fT L : ℕ) : ℝ) * (2 : ℝ) ^ (δ / 2 * G) := by simp only [fT]; push_cast; ring
      _ ≤ _ := by gcongr

/-! ## Theorem Q1, fixed-density form -/

/-- **Theorem Q1 (exact amplitudes, `δ` form), Turing-machine level.** For every `δ > 0` there are
a Turing machine of Mathlib with finite alphabets and a constant `C` such that, for every
Clifford+T circuit `Cir` (gates `H, T, T†, S, S†, X, Z, CNOT, CZ, CS, SWAP, CH`, arbitrary
connectivity) on `n` qubits and all basis states `x, y`, the machine, started on the word
`circCode Cir x y`, halts within `⌊C · 2^{δ G} · (|word| + 2)^C⌋` steps (`G = twoCount Cir`, the
number of two-qubit gates) with the word `outWord a k` of integers `a₀, a₁, a₂, a₃` and
`k = hcount Cir` (the number of `H` and `CH` gates) such that
`⟨y|Cir|x⟩ = (a₀ + a₁ω + a₂ω² + a₃ω³)/√2^k`, `ω = e^{iπ/4}`. -/
theorem amplitude_TM (δ : ℝ) (hδ : 0 < δ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (Cir : List (Gate n)) (x y : Basis n), ∃ a : Fin 4 → ℤ,
        amplitude Cir x y = (∑ j : Fin 4, (a j : ℂ) * ω ^ (j : ℕ)) / ((Real.sqrt 2 : ℝ) : ℂ) ^ hcount Cir ∧
        GraphProblems.Outputs M (circCode Cir x y) (outWord a (hcount Cir))
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * twoCount Cir) * (((circCode Cir x y).length : ℝ) + 2) ^ C⌋₊ := by
  set η : ℝ := min 1 (δ / 16) with hηd
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨K, hK0, hach⟩ := Given.stEveryEta η hη (⌈56 / δ⌉₊ + 2)
  obtain ⟨NM, C₁, hpoly, hNM⟩ := Printed.groupingLemma K η hach
  have hK1 : 1 ≤ K := by omega
  have hKg : K ≤ 3 * K ^ 8 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
      _ ≤ 3 * K ^ 8 := Nat.le_mul_of_pos_left _ (by norm_num)
  haveI : NeZero (3 * K ^ 8) := ⟨by positivity⟩
  have he : 4 * η ≤ δ / 4 := by
    have := min_le_right 1 (δ / 16); linarith
  have hKδ : 14 ≤ δ / 4 * K := by
    have h1 : 56 / δ ≤ K := by
      have := Nat.le_ceil (56 / δ)
      have h2 : ((⌈56 / δ⌉₊ : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : ⌈56 / δ⌉₊ ≤ K)
      linarith
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  obtain ⟨A, hA⟩ := qM_bound hNM hη.le (min_le_left _ _) hK1 hKg he hKδ
  obtain ⟨inst⟩ := qM_poly (3 * K ^ 8) NM hpoly
  obtain ⟨N, q, hfin, hN⟩ := CountKSat.exists_tmW (qM (3 * K ^ 8) NM)
  refine ⟨N, q * (A + 1) ^ (q + 1) + A + (A + 1) * q + 1, hfin, fun n Cir x y => ?_⟩
  obtain ⟨T, hrun, hT⟩ := hA Cir x y
  set Z := ((XC (3 * K ^ 8) Cir x y).net boolCode).value
  have hZ0 : 0 ≤ Z := value_nonneg (3 * K ^ 8) Cir x y
  refine ⟨fun j => decodeK (bC Cir) (Z.toNat % MC Cir) j.val, ?_, ?_⟩
  · -- the amplitude
    have h := amplitude_of_residue Cir x y Z (qValue (3 * K ^ 8) Cir x y)
    have e : (Z % (Mb (bK n Cir.length) : ℤ)).toNat = Z.toNat % MC Cir := by
      obtain ⟨z, hz⟩ := Int.eq_ofNat_of_zero_le hZ0
      rw [hz]; norm_cast
    rw [h, e]
  · -- the time
    obtain ⟨ev⟩ := hN (circCode Cir x y) T _ _ hrun
    refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.le_floor ?_)⟩⟩
    set L := (circCode Cir x y).length
    set G := twoCount Cir
    have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * G) := Real.one_le_rpow one_le_two (by positivity)
    have hE2 : (2 : ℝ) ^ (δ / 2 * G) ≤ (2 : ℝ) ^ (δ * G) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (by have : (0 : ℝ) ≤ G := (by positivity); nlinarith)
    have hL2 : (1 : ℝ) ≤ (L : ℝ) + 2 := by have : (0 : ℝ) ≤ L := (by positivity); linarith
    have hLA : (1 : ℝ) ≤ ((L : ℝ) + 2) ^ A := one_le_pow₀ hL2
    -- T + 1 and L + S + 1
    have h1 : ((T + 1 : ℕ) : ℝ) ≤ (A + 1) * ((L : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * G) := by
      push_cast; nlinarith
    have h2 : ((L + A * (L + 2) ^ A + 1 : ℕ) : ℝ) ≤ (A + 1) * ((L : ℝ) + 2) ^ (A + 1) := by
      push_cast
      have : (L : ℝ) + 1 ≤ ((L : ℝ) + 2) ^ (A + 1) := by
        calc (L : ℝ) + 1 ≤ (L : ℝ) + 2 := by linarith
          _ = ((L : ℝ) + 2) ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ hL2 (by omega)
      have h3 : (A : ℝ) * ((L : ℝ) + 2) ^ A ≤ A * ((L : ℝ) + 2) ^ (A + 1) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL2 (by omega)) (by positivity)
      nlinarith
    have h3 : ((L + A * (L + 2) ^ A + 1 : ℕ) : ℝ) ^ q ≤ ((A : ℝ) + 1) ^ q * ((L : ℝ) + 2) ^ ((A + 1) * q) := by
      rw [pow_mul, ← mul_pow]; gcongr
    set Cc : ℕ := q * (A + 1) ^ (q + 1) + A + (A + 1) * q + 1
    have hpow : ((L : ℝ) + 2) ^ A * ((L : ℝ) + 2) ^ ((A + 1) * q) ≤ ((L : ℝ) + 2) ^ Cc := by
      rw [← pow_add]; exact pow_le_pow_right₀ hL2 (by simp only [Cc]; omega)
    have hcoef : (q : ℝ) * ((A : ℝ) + 1) * ((A : ℝ) + 1) ^ q ≤ Cc := by
      simp only [Cc]; push_cast; rw [pow_succ]; nlinarith [Nat.zero_le A, Nat.zero_le q]
    calc ((q * (T + 1) * ((circCode Cir x y).length + A * ((circCode Cir x y).length + 2) ^ A + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * ((T + 1 : ℕ) : ℝ) * ((L + A * (L + 2) ^ A + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
      _ ≤ (q : ℝ) * ((A + 1) * ((L : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * G)) *
            (((A : ℝ) + 1) ^ q * ((L : ℝ) + 2) ^ ((A + 1) * q)) := by gcongr
      _ = ((q : ℝ) * ((A : ℝ) + 1) * ((A : ℝ) + 1) ^ q) * (((L : ℝ) + 2) ^ A * ((L : ℝ) + 2) ^ ((A + 1) * q)) *
            (2 : ℝ) ^ (δ / 2 * G) := by ring
      _ ≤ (Cc : ℝ) * ((L : ℝ) + 2) ^ Cc * (2 : ℝ) ^ (δ * G) := by gcongr
      _ = _ := by ring

end EthFollowup.Quantum
