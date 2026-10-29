/-
# Theorem Q1, bridge part 8: reading the input word, the context, the output

* `readQ`: the word `circCode C x y` ↦ (`n` in unary, the bits of `x`, of `y`, the gate codes);
  `readQ_code`;
* `prepQ g`: the context of the circuit network with `g` nodes (`prepQ_code`: on `circCode C x y` it is
  `qCtx (scan n (codes C)) …`), `prepQ_polyT`;
* `finQ`: the output word from the value of the network (`decodeK`, `outWord`), `finQ_polyT`.
-/
import EthFollowup.Quantum.QCtxPoly
import GraphProblems.Read
import GraphProblems.Cert

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Groundwork Groundwork.Prog

/-- The reader's result: `n` in unary, `x`, `y`, the gate codes. -/
abbrev QIn : Type := List Unit × (List Bool × (List Bool × List GC))

/-- `n` in unary and the rest of the word (`GraphProblems.read1`). -/
@[irreducible] def rd1 (w : List Bool) : List Unit × List Bool := GraphProblems.read1 w

/-- The code of one gate block. -/
def decG (n : ℕ) (blk : List Bool) : GC :=
  (ofWord (blk.take 4), ((blk.drop 4).take n).idxOf true, (blk.drop (4 + n)).idxOf true)

/-- **The reader.** -/
@[irreducible] def readQ (w : List Bool) : QIn :=
  ((rd1 w).1, ((rd1 w).2.take (rd1 w).1.length,
    (((rd1 w).2.drop (rd1 w).1.length).take (rd1 w).1.length,
      (List.range (((rd1 w).2.drop (2 * (rd1 w).1.length)).length / (4 + 2 * (rd1 w).1.length))).map fun j =>
        decG (rd1 w).1.length ((((rd1 w).2.drop (2 * (rd1 w).1.length)).drop
            (j * (4 + 2 * (rd1 w).1.length))).take (4 + 2 * (rd1 w).1.length)))))

/-! ### The reader is right on the words of circuits -/

theorem length_bits4 (k : ℕ) : (bits4 k).length = 4 := by simp [bits4]
theorem length_oneHot (n q : ℕ) : (oneHot n q).length = n := by simp [oneHot]

theorem idxOf_oneHot {n q : ℕ} (hq : q < n) : (oneHot n q).idxOf true = q := by
  unfold oneHot
  have h : ∀ (k : ℕ) (m : ℕ), q < k + m → m ≤ q →
      ((List.range' m k).map fun p => decide (p = q)).idxOf true = q - m := by
    intro k
    induction k with
    | zero => intro m h1 h2; omega
    | succ k ih =>
      intro m h1 h2
      rw [List.range'_succ, List.map_cons, List.idxOf_cons]
      by_cases hm : m = q
      · subst hm; simp
      · have : (decide (m = q) == true) = false := by simp [hm]
        rw [this, cond_false, ih (m + 1) (by omega) (by omega)]
        omega
  rw [List.range_eq_range', h n 0 (by omega) (by omega), Nat.sub_zero]

theorem length_gateWord {n : ℕ} (g : Gate n) : (gateWord g).length = 4 + 2 * n := by
  cases g <;> simp [gateWord, length_bits4, length_oneHot] <;> ring

theorem ofWord_bits4_one (u : G1) : ofWord (bits4 u.idx) = u.idx := by cases u <;> rfl
theorem ofWord_bits4_two (u : G2) : ofWord (bits4 u.idx) = u.idx := by cases u <;> rfl

theorem decG_eq (n k a b : ℕ) (ha : a < n) (hb : b < n) :
    decG n (bits4 k ++ oneHot n a ++ oneHot n b) = (ofWord (bits4 k), a, b) := by
  have e1 : (bits4 k ++ oneHot n a ++ oneHot n b).take 4 = bits4 k := by
    rw [List.append_assoc]; exact List.take_left' (length_bits4 _)
  have e2 : (bits4 k ++ oneHot n a ++ oneHot n b).drop 4 = oneHot n a ++ oneHot n b := by
    rw [List.append_assoc]; exact List.drop_left' (length_bits4 _)
  have e3 : (bits4 k ++ oneHot n a ++ oneHot n b).drop (4 + n) = oneHot n b :=
    List.drop_left' (by simp [length_bits4, length_oneHot])
  unfold decG
  rw [e1, e2, e3, List.take_left' (length_oneHot _ _), idxOf_oneHot ha, idxOf_oneHot hb]

theorem decG_gateWord {n : ℕ} (g : Gate n) : decG n (gateWord g) = g.code := by
  cases g with
  | one u q => simp only [gateWord, Gate.code]; rw [decG_eq _ _ _ _ q.2 q.2, ofWord_bits4_one]
  | two u q₁ q₂ h => simp only [gateWord, Gate.code]; rw [decG_eq _ _ _ _ q₁.2 q₂.2, ofWord_bits4_two]

theorem blocks_flatMap {α : Type} (f : α → List Bool) (W : ℕ) (hW : 0 < W) (hf : ∀ a, (f a).length = W) :
    ∀ l : List α, (List.range ((l.flatMap f).length / W)).map (fun j => ((l.flatMap f).drop (j * W)).take W) =
      l.map f
  | [] => by simp
  | a :: l => by
    have hlen : ((a :: l).flatMap f).length = W + (l.flatMap f).length := by
      simp [List.flatMap_cons, hf]
    have hl : (l.flatMap f).length = l.length * W := by
      rw [List.length_flatMap]; simp [hf]
    rw [hlen, hl, show W + l.length * W = (l.length + 1) * W by ring, Nat.mul_div_cancel _ hW,
      List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons]
    congr 1
    · simp [List.flatMap_cons, List.take_left' (hf a)]
    · have := blocks_flatMap f W hW hf l
      rw [hl, Nat.mul_div_cancel _ hW] at this
      rw [← this]
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, List.flatMap_cons, Nat.succ_mul]
      rw [show j * W + W = W + j * W by ring, ← List.drop_drop, List.drop_left' (hf a)]

theorem blocks_decG {n : ℕ} (C : List (Gate n)) :
    (List.range ((C.flatMap gateWord).length / (4 + 2 * n))).map (fun j =>
      decG n (((C.flatMap gateWord).drop (j * (4 + 2 * n))).take (4 + 2 * n))) = codes C := by
  have hb := blocks_flatMap (gateWord (n := n)) (4 + 2 * n) (by omega) length_gateWord C
  have e := congrArg (List.map (decG n)) hb
  rw [List.map_map, List.map_map] at e
  rw [codes, ← List.map_congr_left fun g _ => decG_gateWord g]
  exact e

/-- **The reader on the word of a circuit.** -/
theorem readQ_code {n : ℕ} (C : List (Gate n)) (x y : Basis n) :
    readQ (circCode C x y) = (List.replicate n (), (List.ofFn x, (List.ofFn y, codes C))) := by
  have hr : rd1 (circCode C x y) = (List.replicate n (), List.ofFn x ++ (List.ofFn y ++ C.flatMap gateWord)) := by
    have e : circCode C x y = GraphProblems.unary n ++ (List.ofFn x ++ (List.ofFn y ++ C.flatMap gateWord)) := by
      simp [circCode, GraphProblems.unary, List.append_assoc]
    rw [rd1, e]
    simp only [GraphProblems.read1, GraphProblems.Read.ones_unary_append, GraphProblems.Read.rest_unary_append]
  have hx : (List.ofFn x).length = n := List.length_ofFn
  have hy : (List.ofFn y).length = n := List.length_ofFn
  have hd : (List.ofFn x ++ (List.ofFn y ++ C.flatMap gateWord)).drop (2 * n) = C.flatMap gateWord := by
    rw [two_mul, ← List.drop_drop, List.drop_left' hx, List.drop_left' hy]
  unfold readQ
  rw [hr]
  simp only [List.length_replicate]
  rw [hd, List.take_left' hx, List.drop_left' hx, List.take_left' hy, blocks_decG]

/-! ### The context -/

/-- `κ` of a gate code. -/
def kapC (u : ℕ) : ℕ := if u = 0 ∨ u = 11 then 1 else 0

theorem hcount_eq {n : ℕ} (C : List (Gate n)) : hcount C = ((codes C).map fun c => kapC c.1).sum := by
  induction C with
  | nil => rfl
  | cons g C ih =>
    simp only [hcount, codes, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    cases g with
    | one u q => cases u <;> rfl
    | two u q₁ q₂ h => cases u <;> rfl

/-- **The context of the circuit network** read from the word, `g` nodes. -/
def prepQ (g : ℕ) (w : List Bool) : QCtx :=
  qCtx (scanA (readQ w).1.length (readQ w).2.2.2) g (readQ w).1.length (Mb (bK (readQ w).1.length (readQ w).2.2.2.length))
    (2 ^ bK (readQ w).1.length (readQ w).2.2.2.length % Mb (bK (readQ w).1.length (readQ w).2.2.2.length))
    (2 ^ (2 * bK (readQ w).1.length (readQ w).2.2.2.length) % Mb (bK (readQ w).1.length (readQ w).2.2.2.length))
    (2 ^ (3 * bK (readQ w).1.length (readQ w).2.2.2.length) % Mb (bK (readQ w).1.length (readQ w).2.2.2.length))
    (readQ w).2.1 (readQ w).2.2.1 (PQ (scanA (readQ w).1.length (readQ w).2.2.2) g)
    (BQ (scanA (readQ w).1.length (readQ w).2.2.2) (bK (readQ w).1.length (readQ w).2.2.2.length))

theorem validC_codes {n : ℕ} (C : List (Gate n)) : ∀ c ∈ codes C, ValidC n c := by
  intro c hc
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
  cases g with
  | one u q => exact ⟨q.2, q.2, fun h => absurd h (by cases u <;> simp [Gate.code, G1.idx])⟩
  | two u q₁ q₂ h => exact ⟨q₁.2, q₂.2, fun _ e => h (Fin.ext e)⟩

theorem prepQ_code (g : ℕ) {n : ℕ} (C : List (Gate n)) (x y : Basis n) :
    prepQ g (circCode C x y) = qCtx (scan n (codes C)) g n (Mb (bK n C.length))
      (2 ^ bK n C.length % Mb (bK n C.length)) (2 ^ (2 * bK n C.length) % Mb (bK n C.length))
      (2 ^ (3 * bK n C.length) % Mb (bK n C.length)) (List.ofFn x) (List.ofFn y)
      (PQ (scan n (codes C)) g) (BQ (scan n (codes C)) (bK n C.length)) := by
  unfold prepQ
  rw [readQ_code]
  simp only [List.length_replicate, length_codes]
  rw [scanA_eq _ (validC_codes C)]

theorem zp_of (b : ℕ) : ZP (Mb b) b (2 ^ b % Mb b) (2 ^ (2 * b) % Mb b) (2 ^ (3 * b) % Mb b) where
  h1 := by rw [ZMod.natCast_mod]; push_cast; rfl
  h2 := by rw [ZMod.natCast_mod]; push_cast; rw [← pow_mul, mul_comm]
  h3 := by rw [ZMod.natCast_mod]; push_cast; rw [← pow_mul, mul_comm]

/-! ### Polynomial time -/

namespace QP

theorem rd1_polyT : PolyT rd1 := by
  have := GraphProblems.stCertRead.1
  unfold rd1; exact this

@[fun_prop] theorem rd1_polyT' {γ : Type} [Enc γ] {w : γ → List Bool} (hw : PolyT w) : PolyT fun x => rd1 (w x) :=
  PolyT.comp rd1_polyT hw

@[fun_prop] theorem decG_polyT {γ : Type} [Enc γ] {n : γ → ℕ} {b : γ → List Bool} (hn : PolyT n) (hb : PolyT b) :
    PolyT fun x => decG (n x) (b x) := by
  unfold decG; fun_prop

theorem readQ_polyT : PolyT readQ := by
  have hR1 : PolyT fun w => (rd1 w).1 := PolyT.fst rd1_polyT
  have hR2 : PolyT fun w => (rd1 w).2 := PolyT.snd rd1_polyT
  have hn : Unary fun w => (rd1 w).1.length := Unary.of_length (by fun_prop)
  have hgw : PolyT fun w => ((rd1 w).2.drop (2 * (rd1 w).1.length)) := by fun_prop
  have hcnt : Unary fun w => ((rd1 w).2.drop (2 * (rd1 w).1.length)).length / (4 + 2 * (rd1 w).1.length) :=
    Unary.of_le (Unary.of_length hgw) (PolyT.div (PolyT.length hgw) (by fun_prop)) fun w => Nat.div_le_self _ _
  have hr := PolyT.range hcnt
  unfold readQ
  fun_prop

theorem readQ_1 : PolyT fun w => (readQ w).1 := PolyT.fst readQ_polyT
theorem readQ_21 : PolyT fun w => (readQ w).2.1 := PolyT.fst (PolyT.snd readQ_polyT)
theorem readQ_221 : PolyT fun w => (readQ w).2.2.1 := PolyT.fst (PolyT.snd (PolyT.snd readQ_polyT))
theorem readQ_222 : PolyT fun w => (readQ w).2.2.2 := PolyT.snd (PolyT.snd (PolyT.snd readQ_polyT))

theorem bK_unary : Unary fun w => bK (readQ w).1.length (readQ w).2.2.2.length := by
  have h1 : Unary fun w => (readQ w).1.length := Unary.of_length readQ_1
  have h2 : Unary fun w => (readQ w).2.2.2.length := Unary.of_length readQ_222
  unfold bK
  exact (((h1.add (Unary.const 1)).mul h2).add (Unary.const 2))

theorem prepQ_polyT (g : ℕ) : PolyT (prepQ g) := by
  have hR1 := readQ_1
  have hR21 := readQ_21
  have hR221 := readQ_221
  have hR222 := readQ_222
  have hn : Unary fun w => (readQ w).1.length := Unary.of_length hR1
  have hb := bK_unary
  have hst : PolyT fun w => scanA (readQ w).1.length (readQ w).2.2.2 := scanA_polyT hn (by fun_prop)
  have hM : PolyT fun w => Mb (bK (readQ w).1.length (readQ w).2.2.2.length) := by
    unfold Mb; exact PolyT.add (PolyT.two_pow ((Unary.const 4).mul hb)) (PolyT.const 1)
  have h1 : PolyT fun w => 2 ^ bK (readQ w).1.length (readQ w).2.2.2.length := PolyT.two_pow hb
  have h2 : PolyT fun w => 2 ^ (2 * bK (readQ w).1.length (readQ w).2.2.2.length) :=
    PolyT.two_pow ((Unary.const 2).mul hb)
  have h3 : PolyT fun w => 2 ^ (3 * bK (readQ w).1.length (readQ w).2.2.2.length) :=
    PolyT.two_pow ((Unary.const 3).mul hb)
  have hG : Unary fun w => (scanA (readQ w).1.length (readQ w).2.2.2).1.length := Unary.of_length (by fun_prop)
  have hP : Unary fun w => PQ (scanA (readQ w).1.length (readQ w).2.2.2) g := by
    unfold PQ
    exact (Unary.const 4).mul ((Unary.of_le hG (PolyT.div hG.poly (PolyT.const g)) fun w => Nat.div_le_self _ _).add
      (Unary.const 1))
  have hB : Unary fun w => BQ (scanA (readQ w).1.length (readQ w).2.2.2) (bK (readQ w).1.length (readQ w).2.2.2.length) := by
    unfold BQ
    exact (((Unary.const 2).mul hG).add ((Unary.const 4).mul hb)).add (Unary.const 2)
  unfold prepQ
  exact qCtx_polyT hst (Unary.const g) hn hM (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) hP hB fun w => by unfold Mb; positivity

end QP

end EthFollowup.Quantum
