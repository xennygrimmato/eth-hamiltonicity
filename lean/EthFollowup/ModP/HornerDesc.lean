/-
# The Horner-chain description (roots-plan.md §3, H3)

Variables (degree `d ≥ 1`, `nV = 2d`): `x = 0`; `k_i = 1 + i` (`0 ≤ i < d`); `h_i = d + i` (`1 ≤ i ≤ d − 1`);
`h_0 = a_d` is a constant and `h_d = 0` is forced. Products `2i = h_i·x` (`x·a_d` for `i = 0`), `2i + 1 = k_i·m`;
chain `i`: `h_i·x + a_{d-1-i} = h_{i+1} + k_i·m` (no `h_d` term); comparisons `x < m`, `x ≥ lo`, `h_i < m`;
prefix pattern `π` on `x`.

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import EthFollowup.ModP.ArithDesc
import EthFollowup.ModP.ArithInstances
import EthFollowup.ModP.HornerCount

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-! ## Definitions (FROZEN, roots-plan.md §3) -/

def hornerProd (b ℓ d m : ℕ) (a : List ℕ) (p : ℕ) : ProdD :=
  if p % 2 = 0 then (if p / 2 = 0 then ⟨0, .const (toLimbs b ℓ (a.getD d 0))⟩ else ⟨d + p / 2, .var 0⟩)
  else ⟨1 + p / 2, .const (toLimbs b ℓ m)⟩                      -- prod 2i = h_i·x (x·a_d for i = 0), prod 2i+1 = k_i·m
def hornerChain (b ℓ d : ℕ) (a : List ℕ) (i : ℕ) : ChainD :=   -- h_i·x + a_{d-1-i} = h_{i+1} + k_i·m  (no h_d)
  ⟨[⟨1, .prod (2 * i)⟩, ⟨1, .const (toLimbs b ℓ (a.getD (d - 1 - i) 0))⟩],
   if i + 1 < d then [⟨1, .lin (d + i + 1)⟩, ⟨1, .prod (2 * i + 1)⟩] else [⟨1, .prod (2 * i + 1)⟩]⟩
def hornerDesc (b ℓ n d m : ℕ) (a : List ℕ) (lo : ℕ) (π : List Bool) : Desc :=
  { nV := 2 * d, pat := [prePat n π],
    prods := (List.range (2 * d)).map (hornerProd b ℓ d m a),
    chains := (List.range d).map (hornerChain b ℓ d a),
    cmps := [⟨0, .const (toLimbs b ℓ m), .lt⟩, ⟨0, .const (toLimbs b ℓ lo), .ge⟩] ++
      (List.range (d - 1)).map fun j => ⟨d + 1 + j, .const (toLimbs b ℓ m), .lt⟩ }   -- x < m, x ≥ lo, h_i < m

/-! ## Shape -/

theorem hornerDesc_nV (b ℓ n d m : ℕ) (a : List ℕ) (lo : ℕ) (π : List Bool) :
    (hornerDesc b ℓ n d m a lo π).nV = 2 * d := rfl

theorem length_hornerDesc_prods (b ℓ n d m : ℕ) (a : List ℕ) (lo : ℕ) (π : List Bool) :
    (hornerDesc b ℓ n d m a lo π).prods.length = 2 * d := by simp [hornerDesc]

theorem length_hornerDesc_chains (b ℓ n d m : ℕ) (a : List ℕ) (lo : ℕ) (π : List Bool) :
    (hornerDesc b ℓ n d m a lo π).chains.length = d := by simp [hornerDesc]

theorem length_hornerDesc_cmps {b ℓ n d m : ℕ} {a : List ℕ} {lo : ℕ} {π : List Bool} (hd : 1 ≤ d) :
    (hornerDesc b ℓ n d m a lo π).cmps.length = d + 1 := by simp [hornerDesc]; omega

/-- The description constant `64 (nV + nP + nQ + 1)(nC + 1)` of ArithNet (`cA`, bridge) for the
Horner description: `64 (5d + 2)(d + 1)`. -/
theorem hornerDesc_cA_eq {b ℓ n d m : ℕ} {a : List ℕ} {lo : ℕ} {π : List Bool} (hd : 1 ≤ d) :
    64 * (((hornerDesc b ℓ n d m a lo π).nV + (hornerDesc b ℓ n d m a lo π).prods.length +
      (hornerDesc b ℓ n d m a lo π).cmps.length + 1) * ((hornerDesc b ℓ n d m a lo π).chains.length + 1)) =
      64 * (5 * d + 2) * (d + 1) := by
  rw [hornerDesc_nV, length_hornerDesc_prods, length_hornerDesc_chains, length_hornerDesc_cmps hd]
  ring

/-! ## Products and chains by index -/

theorem hornerProd_zero (b ℓ d m : ℕ) (a : List ℕ) :
    hornerProd b ℓ d m a 0 = ⟨0, .const (toLimbs b ℓ (a.getD d 0))⟩ := by simp [hornerProd]

theorem hornerProd_even (b ℓ d m : ℕ) (a : List ℕ) {i : ℕ} (hi : 1 ≤ i) :
    hornerProd b ℓ d m a (2 * i) = ⟨d + i, .var 0⟩ := by
  rw [hornerProd, if_pos (by omega), if_neg (by omega), show 2 * i / 2 = i by omega]

theorem hornerProd_odd (b ℓ d m : ℕ) (a : List ℕ) (i : ℕ) :
    hornerProd b ℓ d m a (2 * i + 1) = ⟨1 + i, .const (toLimbs b ℓ m)⟩ := by
  rw [hornerProd, if_neg (by omega), show (2 * i + 1) / 2 = i by omega]

theorem getD_hornerProds {b ℓ d m : ℕ} {a : List ℕ} {p : ℕ} (hp : p < 2 * d) :
    ((List.range (2 * d)).map (hornerProd b ℓ d m a)).getD p default = hornerProd b ℓ d m a p := by
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]; simp

theorem getD_lt_of_forall {a : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ c ∈ a, c < B) (j : ℕ) : a.getD j 0 < B := by
  by_cases hj : j < a.length
  · rw [List.getD_eq_getElem _ _ hj]; exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hB

theorem hornerProd_eval_even {b ℓ d m : ℕ} {a : List ℕ} (ha : ∀ c ∈ a, c < 2 ^ (b * ℓ)) (x : ℕ → ℕ) (i : ℕ) :
    (hornerProd b ℓ d m a (2 * i)).eval b x = (if i = 0 then a.getD d 0 else x (d + i)) * x 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [mul_zero, hornerProd_zero, if_pos rfl]
    simp only [ProdD.eval, Operand.eval]
    rw [limbsVal_toLimbs (getD_lt_of_forall (by positivity) ha d), mul_comm]
  · rw [hornerProd_even _ _ _ _ _ hi, if_neg (by omega)]
    rfl

theorem hornerProd_eval_odd {b ℓ d m : ℕ} {a : List ℕ} (hm : m < 2 ^ (b * ℓ)) (x : ℕ → ℕ) (i : ℕ) :
    (hornerProd b ℓ d m a (2 * i + 1)).eval b x = x (1 + i) * m := by
  rw [hornerProd_odd]
  simp only [ProdD.eval, Operand.eval]
  rw [limbsVal_toLimbs hm]

/-- Chain `i` evaluated. -/
theorem hornerChain_iff {b ℓ d m : ℕ} {a : List ℕ} (hm : m < 2 ^ (b * ℓ)) (ha : ∀ c ∈ a, c < 2 ^ (b * ℓ))
    (x : ℕ → ℕ) {i : ℕ} (hi : i < d) :
    sideVal b ((List.range (2 * d)).map (hornerProd b ℓ d m a)) x (hornerChain b ℓ d a i).lhs =
        sideVal b ((List.range (2 * d)).map (hornerProd b ℓ d m a)) x (hornerChain b ℓ d a i).rhs ↔
      (if i = 0 then a.getD d 0 else x (d + i)) * x 0 + a.getD (d - 1 - i) 0 =
        (if i + 1 < d then x (d + (i + 1)) else 0) + x (1 + i) * m := by
  have hc : a.getD (d - 1 - i) 0 < 2 ^ (b * ℓ) := getD_lt_of_forall (by positivity) ha _
  unfold hornerChain
  by_cases h1 : i + 1 < d
  · simp only [h1, if_true, sideVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Src.eval,
      one_mul, add_zero]
    rw [getD_hornerProds (by omega), getD_hornerProds (by omega), hornerProd_eval_even ha,
      hornerProd_eval_odd hm, limbsVal_toLimbs hc, ← add_assoc]
  · simp only [h1, if_false, sideVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Src.eval,
      one_mul, add_zero, zero_add]
    rw [getD_hornerProds (by omega), getD_hornerProds (by omega), hornerProd_eval_even ha,
      hornerProd_eval_odd hm, limbsVal_toLimbs hc]

/-! ## The satisfying assignments -/

/-- **The satisfying assignments of the Horner description**, explicitly. -/
theorem hornerDesc_sat {b ℓ n d m lo : ℕ} {a : List ℕ} {π : List Bool} (hd : 1 ≤ d)
    (hm : m < 2 ^ (b * ℓ)) (hlo : lo < 2 ^ (b * ℓ)) (ha : ∀ c ∈ a, c < 2 ^ (b * ℓ)) (x : ℕ → ℕ) :
    (hornerDesc b ℓ n d m a lo π).Sat b x ↔
      patMatch (prePat n π) (x 0) ∧ (x 0 < m ∧ lo ≤ x 0 ∧ ∀ i, 1 ≤ i → i < d → x (d + i) < m) ∧
        ∀ i < d, (if i = 0 then a.getD d 0 else x (d + i)) * x 0 + a.getD (d - 1 - i) 0 =
          (if i + 1 < d then x (d + (i + 1)) else 0) + x (1 + i) * m := by
  unfold Desc.Sat
  have hpat : (∀ v < (hornerDesc b ℓ n d m a lo π).nV,
      patMatch ((hornerDesc b ℓ n d m a lo π).pat.getD v []) (x v)) ↔ patMatch (prePat n π) (x 0) := by
    simp only [hornerDesc]
    constructor
    · intro h; simpa using h 0 (by omega)
    · intro h v _
      rcases v with _ | v
      · simpa using h
      · simp
  have hcmp : (∀ q ∈ (hornerDesc b ℓ n d m a lo π).cmps, q.rel.Holds (x q.v) (q.rhs.eval b x)) ↔
      (x 0 < m ∧ lo ≤ x 0 ∧ ∀ i, 1 ≤ i → i < d → x (d + i) < m) := by
    simp only [hornerDesc, List.cons_append, List.nil_append, List.forall_mem_cons, List.forall_mem_map,
      List.mem_range, CmpRel.Holds, Operand.eval, limbsVal_toLimbs hm, limbsVal_toLimbs hlo]
    apply and_congr_right; intro _; apply and_congr_right; intro _
    constructor
    · intro h i hi1 hi
      have := h (i - 1) (by omega)
      rwa [show d + 1 + (i - 1) = d + i by omega] at this
    · intro h j hj
      have := h (j + 1) (by omega) (by omega)
      rwa [show d + (j + 1) = d + 1 + j by omega] at this
  have hch : (∀ ch ∈ (hornerDesc b ℓ n d m a lo π).chains,
      sideVal b (hornerDesc b ℓ n d m a lo π).prods x ch.lhs =
        sideVal b (hornerDesc b ℓ n d m a lo π).prods x ch.rhs) ↔
      ∀ i < d, (if i = 0 then a.getD d 0 else x (d + i)) * x 0 + a.getD (d - 1 - i) 0 =
          (if i + 1 < d then x (d + (i + 1)) else 0) + x (1 + i) * m := by
    simp only [hornerDesc, List.forall_mem_map, List.mem_range]
    exact forall₂_congr fun i hi => hornerChain_iff hm ha x hi
  rw [hpat, hcmp, hch]

/-- The canonical assignment of a root `x`: `x`, the quotients `k_i`, the Horner values `h_i`. -/
def hornerCanon (m d : ℕ) (a : List ℕ) (x : ℕ) : ℕ → ℕ := fun v =>
  if v = 0 then x else if v ≤ d then hK m d a x (v - 1) else hH m a x (v - d)

/-- **Satisfying assignments = canonical assignments of the roots** (coefficients reduced). -/
theorem hornerDesc_sat_iff {b ℓ n d m lo : ℕ} {a : List ℕ} {π : List Bool} (hd : 1 ≤ d)
    (hlen : a.length = d + 1) (hm0 : 0 < m) (ha : ∀ c ∈ a, c < m) (hm : m < 2 ^ (b * ℓ))
    (hlo : lo < 2 ^ (b * ℓ)) (x : ℕ → ℕ) :
    (hornerDesc b ℓ n d m a lo π).Sat b x ↔
      patMatch (prePat n π) (x 0) ∧ x 0 < m ∧ lo ≤ x 0 ∧ polyEvalMod m a (x 0) = 0 ∧
        ∀ v, 1 ≤ v → v < 2 * d → x v = hornerCanon m d a (x 0) v := by
  have ha' : ∀ c ∈ a, c < 2 ^ (b * ℓ) := fun c hc => (ha c hc).trans hm
  have had : a.getD d 0 < m := getD_lt_of_forall hm0 ha d
  rw [hornerDesc_sat hd hm hlo ha']
  have hci := horner_chain_iff (x := x 0) (fun j => x (d + j)) (fun j => x (1 + j)) hm0 hd hlen had
  constructor
  · rintro ⟨hp, ⟨hx, hl, hb⟩, hc⟩
    obtain ⟨⟨hz, hh⟩, hk⟩ := hci.1 ⟨hc, hb⟩
    refine ⟨hp, hx, hl, hz, fun v hv1 hv => ?_⟩
    unfold hornerCanon
    rw [if_neg (by omega)]
    split_ifs with hvd
    · have := hk (v - 1) (by omega); rwa [show 1 + (v - 1) = v by omega] at this
    · have := hh (v - d) (by omega) (by omega); rwa [show d + (v - d) = v by omega] at this
  · rintro ⟨hp, hx, hl, hz, hv⟩
    have hh : ∀ i, 1 ≤ i → i < d → x (d + i) = hH m a (x 0) i := by
      intro i hi1 hi
      rw [hv _ (by omega) (by omega), hornerCanon, if_neg (by omega), if_neg (by omega),
        show d + i - d = i by omega]
    have hk : ∀ i < d, x (1 + i) = hK m d a (x 0) i := by
      intro i hi
      rw [hv _ (by omega) (by omega), hornerCanon, if_neg (by omega), if_pos (by omega),
        show 1 + i - 1 = i by omega]
    obtain ⟨hc, hb⟩ := hci.2 ⟨⟨hz, hh⟩, hk⟩
    exact ⟨hp, ⟨hx, hl, hb⟩, hc⟩

theorem extV_of_lt {N : ℕ} (x : Fin N → ℕ) {v : ℕ} (hv : v < N) : extV N x v = x ⟨v, hv⟩ := by
  simp [extV, hv]

theorem hornerCanon_lt {m d : ℕ} {a : List ℕ} (hm0 : 0 < m) (hlen : a.length = d + 1) (ha : ∀ c ∈ a, c < m)
    {x : ℕ} (hx : x < m) {v : ℕ} (hv : v < 2 * d) : hornerCanon m d a x v < m := by
  unfold hornerCanon
  split_ifs with h0 h1
  · exact hx
  · exact hK_lt hm0 hlen ha hx (by omega)
  · exact hH_lt hm0 hlen x _ (by omega)

/-- **The count of the Horner description**: the number of roots `x ∈ [lo, m)` of `a` modulo `m`
with prefix `π` (box `2^n'`; coefficients reduced, `0 < m`, `m ≤ 2^n ≤ 2^n'`, `|π| ≤ n`). -/
theorem hornerDesc_count {b ℓ n n' d m lo : ℕ} {a : List ℕ} {π : List Bool} (hd : 1 ≤ d)
    (hlen : a.length = d + 1) (hm0 : 0 < m) (ha : ∀ c ∈ a, c < m) (hm : m < 2 ^ (b * ℓ))
    (hlo : lo < 2 ^ (b * ℓ)) (hmn : m ≤ 2 ^ n) (hnn : n ≤ n') (hπ : π.length ≤ n) :
    (hornerDesc b ℓ n d m a lo π).countB b (2 ^ n') =
      ((range m).filter fun x => lo ≤ x ∧ polyEvalMod m a x = 0 ∧
        x / 2 ^ (n - π.length) = Factoring.Search.ofWord π).card := by
  have hmn' : m ≤ 2 ^ n' := hmn.trans (Nat.pow_le_pow_right (by norm_num) hnn)
  have h0 : 0 < 2 * d := by omega
  unfold Desc.countB
  rw [hornerDesc_nV]
  refine card_bij' (fun y _ => y ⟨0, h0⟩)
    (fun x _ => fun v : Fin (2 * d) => hornerCanon m d a x v) ?_ ?_ ?_ ?_
  · intro y hy
    rw [mem_filter, Fintype.mem_piFinset] at hy
    obtain ⟨hbox, hs⟩ := hy
    rw [hornerDesc_sat_iff hd hlen hm0 ha hm hlo] at hs
    obtain ⟨hp, hx, hl, hz, -⟩ := hs
    rw [extV_of_lt _ h0] at hp hx hl hz
    rw [mem_filter, mem_range]
    exact ⟨hx, hl, hz, (patMatch_prePat hπ (by omega)).1 hp⟩
  · intro x hx
    rw [mem_filter, mem_range] at hx
    obtain ⟨hx, hl, hz, hp⟩ := hx
    have hX : ∀ v < 2 * d, extV (2 * d)
        (fun v : Fin (2 * d) => hornerCanon m d a x v) v = hornerCanon m d a x v :=
      fun v hv => extV_of_lt (N := 2 * d) _ hv
    rw [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun v => mem_range.2 ((hornerCanon_lt hm0 hlen ha hx v.isLt).trans_le hmn'), ?_⟩
    rw [hornerDesc_sat_iff hd hlen hm0 ha hm hlo, hX 0 h0]
    have hc0 : hornerCanon m d a x 0 = x := by simp [hornerCanon]
    rw [hc0]
    exact ⟨(patMatch_prePat hπ (by omega)).2 hp, hx, hl, hz, fun v _ hv => hX v hv⟩
  · intro y hy
    rw [mem_filter] at hy
    have hs := hy.2
    rw [hornerDesc_sat_iff hd hlen hm0 ha hm hlo] at hs
    obtain ⟨-, -, -, -, hv⟩ := hs
    rw [extV_of_lt _ h0] at hv
    funext v
    rcases Nat.eq_zero_or_pos (v : ℕ) with hv0 | hv0
    · have : v = ⟨0, h0⟩ := Fin.ext hv0
      subst this; simp [hornerCanon]
    · have := hv v hv0 v.isLt
      rw [extV_of_lt _ v.isLt] at this
      exact this.symm
  · intro x _
    simp [hornerCanon]

/-! ## Well-formedness -/

theorem hornerChain_hasProd (b ℓ d : ℕ) (a : List ℕ) (i p : ℕ) :
    (hornerChain b ℓ d a i).HasProd p ↔ p = 2 * i ∨ p = 2 * i + 1 := by
  unfold ChainD.HasProd hornerChain
  split_ifs <;> simp <;> constructor <;> rintro (h | h) <;> omega

/-- **Well-formedness** (`d ≥ 1`, patterns of length `n ≤ nB`). -/
theorem hornerDesc_WF {b ℓ n nB d m lo : ℕ} {a : List ℕ} {π : List Bool} (hd : 1 ≤ d) (hn : n ≤ nB) :
    (hornerDesc b ℓ n d m a lo π).WFB b ℓ nB where
  pat_len := by simp [hornerDesc, length_prePat, hn]
  prod_ok := by
    intro pd hpd
    simp only [hornerDesc, List.mem_map, List.mem_range] at hpd
    obtain ⟨p, hp, rfl⟩ := hpd
    rw [hornerDesc_nV]
    unfold hornerProd
    split_ifs with h1 h2
    · exact ⟨by dsimp only; omega, toLimbs_OK b ℓ _⟩
    · exact ⟨by dsimp only; omega, by simp only [Operand.OK]; omega⟩
    · exact ⟨by dsimp only; omega, toLimbs_OK b ℓ _⟩
  term_ok := by
    intro ch hch t ht
    simp only [hornerDesc, List.mem_map, List.mem_range] at hch
    obtain ⟨i, hi, rfl⟩ := hch
    simp only [hornerDesc, List.length_map, List.length_range]
    unfold hornerChain at ht
    split_ifs at ht with h1 <;> simp at ht <;> rcases ht with rfl | rfl | rfl | rfl <;>
      first | exact toLimbs_OK b ℓ _ | (simp [Src.OK]; omega)
  coeff_le := by
    intro ch hch
    simp only [hornerDesc, List.mem_map, List.mem_range] at hch
    obtain ⟨i, hi, rfl⟩ := hch
    unfold hornerChain
    split_ifs <;> simp
  prod_once := by
    intro c hc c' hc' p h h'
    simp only [hornerDesc, List.length_map, List.length_range] at hc hc'
    simp only [hornerDesc] at h h'
    rw [List.getD_eq_getElem _ _ (by simpa using hc)] at h
    rw [List.getD_eq_getElem _ _ (by simpa using hc')] at h'
    simp only [List.getElem_map, List.getElem_range, hornerChain_hasProd] at h h'
    omega
  cmp_ok := by
    intro q hq
    simp only [hornerDesc, List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
      List.mem_range] at hq
    rcases hq with rfl | rfl | ⟨j, hj, rfl⟩
    · exact ⟨by simp [hornerDesc]; omega, toLimbs_OK b ℓ _⟩
    · exact ⟨by simp [hornerDesc]; omega, toLimbs_OK b ℓ _⟩
    · exact ⟨by simp [hornerDesc]; omega, toLimbs_OK b ℓ _⟩

/-! ## Sanity checks (roots-plan.md §4) -/

example : (hornerDesc 3 1 3 2 7 [1, 1, 1] 0 []).countB 3 (2 ^ 3) = 2 := by
  rw [hornerDesc_count (by norm_num) rfl (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)
    le_rfl (by norm_num)]
  decide

end EthFollowup.ModP
