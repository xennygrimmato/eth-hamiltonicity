/-
# The rank-encoded HC network `N_s` (module A1, file 3)

`research/hc-degree-theorem.md` Definition 2.2, Theorem 2.5, Proposition 3.2, Lemma 3.3.
For a graph `G` on `Fin n`, a partition `β`, a crossing order `X : Crossing G β m` and a root `r`,
and a profile `s : Fin g → Fin g → ℕ`:

* `X.netS r s = (X.hcSystem r).netP (rankPC (symProf s))`: the network of §2 with the rank code
  (`symProf s` symmetrizes `s`; for the symmetric profiles of `VB.symProfiles` it is `s`);
* `Adm X s` (admissible: `∑_{b≠a} s_ab ≤ 2|V_a|`) and `Bnd X s` (`s_ab ≤ e_ab`);
* `I_eq_zero_of_card`: `I_a(ℓ) = 0` when more than `2|V_a|` crossing edges at `a` are used;
* **Theorem 2.5** `sum_netS`: `∑_{s ∈ symProfiles Rd g, Adm β s ∧ Bnd s} value(N_s) = n·#HC(G)`
  for `m < Rd`;
* **Proposition 3.2** for admissible bounded symmetric profiles: per node
  `sum_c_netS_le : ∑_{b≠a} c_ab ≤ 10·|V_a|·lgN n + 2g²` (`lgN n = ⌊log₂(n+2)⌋`), total
  `U_netS_le : U ≤ 10(n·lgd + n) + 3g³` (`lgd = ⌊log₂(M/n + 2)⌋` for any `M ≥ m`), the bound
  `abs_T_lt : |T| < 2^{2n²+1}`, and `netS_is` (Definition 2 with `P = 10·ν·lgN n + 2g² + 1`,
  `B = 2n² + 1` for `ν ≥ max_a |V_a|`).
-/
import EthFollowup.ExactHC.HCNetwork
import EthFollowup.ExactHC.PairCode
import EthFollowup.ExactHC.VertexBalanced
import ClauseBound.Rec.Few
import ClauseBound.ParityChecks.Binom

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset Rank

/-! ### Binomial estimates -/

/-- `C(N, j) ≤ (3(⌊N/k⌋ + 1))^k` for `j ≤ k`. -/
theorem choose_le_pow_div (N j k : ℕ) (hj : j ≤ k) : N.choose j ≤ (3 * (N / k + 1)) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : j = 0 := by omega
    simp
  rcases lt_or_ge N k with hN | hN
  · calc N.choose j ≤ 2 ^ N := Nat.choose_le_two_pow N j
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hN.le
      _ ≤ (3 * (N / k + 1)) ^ k := Nat.pow_le_pow_left (by generalize N / k = t; omega) k
  · have h1 := ClauseBound.Rec.sum_choose_le (δ := N) (n := k) hk hN
    have h2 : (N.choose j : ℝ) ≤ ∑ ν ∈ range (k + 1), (N.choose ν : ℝ) :=
      single_le_sum (f := fun ν => (N.choose ν : ℝ)) (fun _ _ => by positivity) (mem_range.2 (by omega))
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h3 : (3 * N / k : ℝ) ≤ 3 * (((N / k : ℕ) : ℝ) + 1) := by
      have e : N < N / k * k + k := Nat.lt_div_mul_add hk
      have e' : (N : ℝ) < ((N / k : ℕ) : ℝ) * k + k := by exact_mod_cast e
      rw [div_le_iff₀ hk0]; nlinarith
    have h4 : (3 * N / k : ℝ) ^ k ≤ (3 * (((N / k : ℕ) : ℝ) + 1)) ^ k :=
      pow_le_pow_left₀ (by positivity) h3 k
    have : (N.choose j : ℝ) ≤ (((3 * (N / k + 1)) ^ k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- `2^{∑ cw} ≤ 2^{#T}·C(∑ e, ∑ s)` when `s_i ≤ e_i`. -/
theorem two_pow_sum_cw_le {ι : Type} (T : Finset ι) (e s : ι → ℕ) (h : ∀ i ∈ T, s i ≤ e i) :
    2 ^ (∑ i ∈ T, cw (e i) (s i)) ≤ 2 ^ #T * (∑ i ∈ T, e i).choose (∑ i ∈ T, s i) := by
  rw [← prod_pow_eq_pow_sum]
  calc ∏ i ∈ T, 2 ^ cw (e i) (s i) ≤ ∏ i ∈ T, (2 * (e i).choose (s i)) :=
        prod_le_prod' fun i hi => two_pow_cw_le _ _ (Nat.choose_pos (h i hi))
    _ = 2 ^ #T * ∏ i ∈ T, (e i).choose (s i) := by rw [prod_mul_distrib, prod_const]
    _ ≤ _ := Nat.mul_le_mul_left _ (ClauseBound.ParityChecks.prod_choose_le T e s)

/-- The same without `s_i ≤ e_i`: a pair with `s_i > e_i` has `cw = 0`. -/
theorem two_pow_sum_cw_le' {ι : Type} (T : Finset ι) (e s : ι → ℕ) (k : ℕ) (hk : ∑ i ∈ T, s i ≤ k) :
    2 ^ (∑ i ∈ T, cw (e i) (s i)) ≤ 2 ^ #T * (3 * ((∑ i ∈ T, e i) / k + 1)) ^ k := by
  classical
  set T' := T.filter fun i => s i ≤ e i with hT'
  have h0 : ∑ i ∈ T, cw (e i) (s i) = ∑ i ∈ T', cw (e i) (s i) := by
    rw [hT', sum_filter_of_ne]
    intro i _ hne
    by_contra h
    apply hne
    unfold cw
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    rfl
  have hsub : T' ⊆ T := filter_subset _ _
  have h1 := two_pow_sum_cw_le T' e s fun i hi => (mem_filter.1 hi).2
  have h2 := choose_le_pow_div (∑ i ∈ T', e i) (∑ i ∈ T', s i) k ((sum_le_sum_of_subset hsub).trans hk)
  have h3 : (3 * ((∑ i ∈ T', e i) / k + 1)) ^ k ≤ (3 * ((∑ i ∈ T, e i) / k + 1)) ^ k := by
    have := Nat.div_le_div_right (c := k) (sum_le_sum_of_subset (f := e) hsub)
    exact Nat.pow_le_pow_left (by omega) k
  have h4 : 2 ^ #T' ≤ 2 ^ #T := Nat.pow_le_pow_right (by norm_num) (card_le_card hsub)
  rw [h0]
  exact h1.trans (Nat.mul_le_mul h4 (h2.trans h3))

/-- `lgN n = ⌊log₂(n+2)⌋ ≥ 1`. -/
def lgN (n : ℕ) : ℕ := Nat.log 2 (n + 2)

theorem one_le_lgN (n : ℕ) : 1 ≤ lgN n := Nat.log_pos (by norm_num) (by omega)

theorem lt_two_pow_lgN (n : ℕ) : n + 2 < 2 ^ (lgN n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

/-! ### Generic counting in a label system -/

namespace LabelSystem

variable {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L] (X : LabelSystem g K R L)

theorem pairItems_self (a : Fin g) : X.pairItems a a = [] := by
  rw [pairItems, List.filter_eq_nil_iff]
  intro k _
  have := X.lo_ne_hi k
  simp only [OnPair, decide_eq_true_eq]
  rintro (h | h) <;> exact this (h.1.trans h.2.symm)

theorem cntP_self (a : Fin g) (ℓ : K → L) : X.cntP a a ℓ = 0 := by
  simp [cntP, pairLab, X.pairItems_self]

theorem cntP_le (a b : Fin g) (ℓ : K → L) : X.cntP a b ℓ ≤ (X.pairItems a b).length :=
  (List.length_filter_le _ _).trans (X.length_pairLab a b ℓ).le

theorem cntP_eq_card (a b : Fin g) (ℓ : K → L) :
    X.cntP a b ℓ = #(univ.filter fun k => X.OnPair a b k ∧ ℓ k ≠ X.dflt) := by
  unfold cntP pairLab pairItems
  rw [List.filter_map, List.length_map, List.filter_filter,
    ← length_filter_of_complete _ X.kord_nodup X.mem_kord (fun k => X.OnPair a b k ∧ ℓ k ≠ X.dflt)]
  congr 1
  apply List.filter_congr
  intro k _
  simp [and_comm]

theorem length_pairItems (a b : Fin g) : (X.pairItems a b).length = #(univ.filter (X.OnPair a b)) := by
  unfold pairItems; exact length_filter_of_complete _ X.kord_nodup X.mem_kord _

/-- The used items at `a`, counted over the pairs. -/
theorem sum_cntP (a : Fin g) (ℓ : K → L) :
    ∑ b ∈ univ.erase a, X.cntP a b ℓ = #(univ.filter fun k => X.Inc a k ∧ ℓ k ≠ X.dflt) := by
  simp only [cntP_eq_card]
  rw [card_eq_sum_card_fiberwise (f := fun k => X.other a k) (t := univ.erase a)]
  · refine sum_congr rfl fun b hb => ?_
    have hb' := (mem_erase.1 hb).1
    congr 1
    ext k
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨X.inc_of_onPair h1, h2⟩, X.other_eq (Ne.symm hb') h1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3 ▸ X.onPair_other h1, h2⟩
  · intro k hk
    replace hk := (mem_filter.1 hk).2
    rw [coe_erase, coe_univ]
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    exact X.other_ne hk.1

theorem sum_pairItems (a : Fin g) : ∑ b ∈ univ.erase a, (X.pairItems a b).length = #(univ.filter (X.Inc a)) := by
  simp only [length_pairItems]; exact X.sum_card_onPair a

end LabelSystem

/-! ### The network `N_s` -/

/-- The symmetrized profile `s(min a b, max a b)`. -/
def symProf {g : ℕ} (s : Fin g → Fin g → ℕ) (a b : Fin g) : ℕ := s (min a b) (max a b)

theorem symProf_symm {g : ℕ} (s : Fin g → Fin g → ℕ) (a b : Fin g) : symProf s a b = symProf s b a := by
  simp [symProf, min_comm, max_comm]

theorem symProf_eq {g : ℕ} {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a) : symProf s = s := by
  funext a b
  unfold symProf
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, hs]

namespace Crossing

variable {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
  (X : Crossing G β m) (r : Fin n)

/-- **The rank-encoded network `N_s`** (Definition 2.2). -/
noncomputable def netS (s : Fin g → Fin g → ℕ) : Eight.SecNetworks.Net g :=
  (X.hcSystem r).netP ((X.hcSystem r).rankPC (symProf s) (symProf_symm s) rfl)

/-- The number `e_ab` of crossing edges between the blobs `a` and `b`. -/
noncomputable def eP (a b : Fin g) : ℕ := ((X.hcSystem r).pairItems a b).length

/-- `s` is admissible: `∑_{b ≠ a} s_ab ≤ 2|V_a|` for every node. -/
abbrev Adm (β : Fin n → Fin g) (s : Fin g → Fin g → ℕ) : Prop := ∀ a, ∑ b ∈ univ.erase a, s a b ≤ 2 * #(blob β a)

/-- `s_ab ≤ e_ab` for all pairs. -/
abbrev Bnd (s : Fin g → Fin g → ℕ) : Prop := ∀ a b, s a b ≤ X.eP r a b

/-- The profile of a labelling. -/
noncomputable def profL (ℓ : Fin m → Label) (a b : Fin g) : ℕ := (X.hcSystem r).cntP a b ℓ

theorem filter_inc_eq (a : Fin g) (ℓ : Fin m → Label) :
    (univ.filter fun k => (X.hcSystem r).Inc a k ∧ ℓ k ≠ (X.hcSystem r).dflt) =
      (X.chords.delta a).filter fun k => ℓ k ≠ Label.N := by
  ext k
  simp only [mem_filter, mem_univ, true_and, X.mem_delta]
  rfl

/-- `#{k ∈ δ(a) : ℓ_k ≠ N} ≤ ∑_{v ∈ V_a} deg_ℓ(v)`: every crossing edge at `a` has an end in `V_a`. -/
theorem card_used_le (ℓ : Fin m → Label) (a : Fin g) :
    #((X.chords.delta a).filter fun k => ℓ k ≠ Label.N) ≤ ∑ v ∈ blob β a, X.degL ℓ a v := by
  unfold degL
  refine le_trans (card_le_card fun k hk => ?_) card_biUnion_le
  rw [mem_biUnion]
  have hk' := mem_filter.1 hk
  rcases X.mem_delta.1 hk'.1 with h | h
  · exact ⟨X.s k, mem_blob.2 h, mem_filter.2 ⟨hk'.1, hk'.2, Or.inl rfl⟩⟩
  · exact ⟨X.t k, mem_blob.2 h, mem_filter.2 ⟨hk'.1, hk'.2, Or.inr rfl⟩⟩

/-- **A vertex of `ℓ`-degree `≥ 3` kills the blob sum**: if more than `2|V_a|` crossing edges at `a`
carry a label `≠ N`, then `I_a(ℓ) = 0`. -/
theorem I_eq_zero_of_card (ℓ : Fin m → Label) (a : Fin g)
    (h : 2 * #(blob β a) < #((X.chords.delta a).filter fun k => ℓ k ≠ Label.N)) : X.I r ℓ a = 0 := by
  have hv : ∃ v ∈ blob β a, 3 ≤ X.degL ℓ a v := by
    by_contra hc
    push_neg at hc
    have : ∑ v ∈ blob β a, X.degL ℓ a v ≤ ∑ _v ∈ blob β a, 2 := sum_le_sum fun v hv => by
      have := hc v hv; omega
    rw [sum_const, smul_eq_mul] at this
    have := X.card_used_le ℓ a
    omega
  obtain ⟨v, hvb, hv3⟩ := hv
  unfold I
  refine sum_eq_zero fun x _ => ?_
  have : X.degInd ℓ a x = 0 := by
    unfold degInd
    rw [if_neg]
    intro hall
    have := hall v hvb
    omega
  rw [this, zero_mul]

theorem T_par_eq_zero_of_not_adm (ℓ : Fin m → Label) (h : ¬ Adm β (X.profL r ℓ)) :
    ∏ a, (X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ) = 0 := by
  unfold Adm at h
  push_neg at h
  obtain ⟨a, ha⟩ := h
  refine prod_eq_zero (mem_univ a) ?_
  have hc : 2 * #(blob β a) < #((X.chords.delta a).filter fun k => ℓ k ≠ Label.N) := by
    rw [← X.filter_inc_eq r a ℓ, ← LabelSystem.sum_cntP]; exact ha
  rw [Crossing.hcSystem_T, X.I_eq_zero_of_card r ℓ a hc, mul_zero]

theorem value_netS (s : Fin g → Fin g → ℕ) :
    (X.netS r s).value = ∑ ℓ : Fin m → Label,
      if (∀ a b, a ≠ b → X.profL r ℓ a b = symProf s a b) then
        ∏ a, (X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ) else 0 := by
  rw [netS, LabelSystem.PairCode.value_netP, LabelSystem.PairCode.profSet, sum_filter]
  rfl

theorem profL_mem {Rd : ℕ} (hRd : m < Rd) (ℓ : Fin m → Label) : X.profL r ℓ ∈ VB.symProfiles Rd g := by
  rw [VB.mem_symProfiles]
  refine ⟨fun a b => ?_, fun a b => (X.hcSystem r).cntP_comm a b ℓ, fun a => (X.hcSystem r).cntP_self a ℓ⟩
  have h1 := (X.hcSystem r).cntP_le a b ℓ
  have h2 : ((X.hcSystem r).pairItems a b).length ≤ m := by
    rw [LabelSystem.length_pairItems]
    exact (card_filter_le _ _).trans (by simp)
  simp only [profL]; omega

theorem bnd_profL (ℓ : Fin m → Label) : Bnd X r (X.profL r ℓ) := fun a b => (X.hcSystem r).cntP_le a b ℓ

/-- **Theorem 2.5**: summed over the admissible bounded symmetric profiles with entries `< Rd`, the
values of the networks `N_s` give `n · #HC(G)` (for `m < Rd`). -/
theorem sum_netS {Rd : ℕ} (hRd : m < Rd) :
    ∑ s ∈ VB.symProfiles Rd g, (if Adm β s ∧ Bnd X r s then (X.netS r s).value else 0) =
      n * (Hamiltonian.hamCycles G).card := by
  have key : ∀ s ∈ VB.symProfiles Rd g, (if Adm β s ∧ Bnd X r s then (X.netS r s).value else 0) =
      ∑ ℓ : Fin m → Label, if Adm β s ∧ Bnd X r s ∧ X.profL r ℓ = s then
        ∏ a, (X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ) else 0 := by
    intro s hs
    have hs' := VB.mem_symProfiles.1 hs
    rw [value_netS, symProf_eq hs'.2.1]
    split_ifs with h
    · refine sum_congr rfl fun ℓ _ => ?_
      have e : (∀ a b, a ≠ b → X.profL r ℓ a b = s a b) ↔ X.profL r ℓ = s := by
        constructor
        · intro h'
          funext a b
          by_cases hab : a = b
          · subst hab; rw [hs'.2.2]; exact (X.hcSystem r).cntP_self a ℓ
          · exact h' a b hab
        · rintro rfl _ _ _; rfl
      by_cases hp : X.profL r ℓ = s
      · rw [if_pos (e.2 hp), if_pos ⟨h.1, h.2, hp⟩]
      · rw [if_neg (fun h' => hp (e.1 h')), if_neg (fun h' => hp h'.2.2)]
    · exact (sum_eq_zero fun ℓ _ => if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)).symm
  rw [sum_congr rfl key, sum_comm]
  have inner : ∀ ℓ : Fin m → Label, (∑ s ∈ VB.symProfiles Rd g, if Adm β s ∧ Bnd X r s ∧ X.profL r ℓ = s then
      ∏ a, (X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ) else 0) =
      ∏ a, (X.hcSystem r).T a ℓ (fun j => (X.hcSystem r).par j ℓ) := by
    intro ℓ
    rw [sum_eq_single (X.profL r ℓ)]
    · by_cases ha : Adm β (X.profL r ℓ)
      · rw [if_pos ⟨ha, X.bnd_profL r ℓ, rfl⟩]
      · rw [if_neg (fun h => ha h.1), X.T_par_eq_zero_of_not_adm r ℓ ha]
    · intro s _ hne
      rw [if_neg (fun h => hne h.2.2.symm)]
    · intro h; exact absurd (X.profL_mem r hRd ℓ) h
  rw [sum_congr rfl fun ℓ _ => inner ℓ, ← blob_factorisation X r]
  exact sum_congr rfl fun ℓ _ => prod_congr rfl fun a _ => X.hcSystem_T_par r a ℓ

theorem value_netS_eq_zero {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a) (hd : ∀ a, s a a = 0)
    (hB : ¬ Bnd X r s) : (X.netS r s).value = 0 := by
  rw [value_netS, symProf_eq hs]
  refine sum_eq_zero fun ℓ _ => if_neg fun h => hB fun a b => ?_
  by_cases hab : a = b
  · subst hab; rw [hd]; exact Nat.zero_le _
  · rw [← h a b hab]; exact X.bnd_profL r ℓ a b

/-- **Theorem 2.5** with the admissible profiles only (the bound `s ≤ e` is automatic). -/
theorem sum_netS_adm {Rd : ℕ} (hRd : m < Rd) :
    ∑ s ∈ VB.symProfiles Rd g, (if Adm β s then (X.netS r s).value else 0) =
      n * (Hamiltonian.hamCycles G).card := by
  rw [← X.sum_netS r hRd]
  refine sum_congr rfl fun s hs => ?_
  have hs' := VB.mem_symProfiles.1 hs
  by_cases hA : Adm β s
  · by_cases hB : Bnd X r s
    · rw [if_pos hA, if_pos ⟨hA, hB⟩]
    · rw [if_pos hA, if_neg (fun h => hB h.2), X.value_netS_eq_zero r hs'.2.1 hs'.2.2 hB]
  · rw [if_neg hA, if_neg (fun h => hA h.1)]

/-! ### Proposition 3.2: the parameters -/

variable {X r}

theorem card_delta_le (a : Fin g) : (X.chords.delta a).card ≤ #(blob β a) * n := by
  refine (X.card_delta_le_mu a).trans ?_
  unfold mu
  calc ∑ v ∈ blob β a, G.degree v ≤ ∑ _v ∈ blob β a, n :=
        sum_le_sum fun v _ => (G.degree_lt_card_verts v).le.trans (by simp)
    _ = _ := by rw [sum_const, smul_eq_mul]

theorem rcap_eq {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a) (a b : Fin g) :
    ((X.hcSystem r).rankPC (symProf s) (symProf_symm s) rfl).cap a b = cw (X.eP r a b) (s a b) + 2 * s a b := by
  show cw _ (symProf s a b) + 2 * symProf s a b = _
  rw [symProf_eq hs]; rfl

theorem cap_netS {s : Fin g → Fin g → ℕ} (hs : ∀ a b, s a b = s b a) (a b : Fin g) :
    (X.netS r s).c a b = cw (X.eP r a b) (s a b) + 2 * s a b + ((X.hcSystem r).pairCopies a b).length := by
  show ((X.hcSystem r).rankPC (symProf s) (symProf_symm s) rfl).cap a b + _ = _
  rw [rcap_eq hs]

theorem sum_c_netS (s : Fin g → Fin g → ℕ) (hs : ∀ a b, s a b = s b a) (a : Fin g) :
    ∑ b ∈ univ.erase a, (X.netS r s).c a b =
      ∑ b ∈ univ.erase a, (cw (X.eP r a b) (s a b) + 2 * s a b) + #(univ.filter ((X.hcSystem r).Touch a)) := by
  rw [netS, LabelSystem.PairCode.sum_c_eqP]
  rw [sum_congr rfl fun b _ => rcap_eq hs a b]

/-- **Proposition 3.2, per node**: `∑_{b≠a} c_ab ≤ 10·|V_a|·lgN n + 2g²`. -/
theorem sum_c_netS_le (s : Fin g → Fin g → ℕ) (hs : ∀ a b, s a b = s b a) (hA : Adm β s)
    (a : Fin g) :
    ∑ b ∈ univ.erase a, (X.netS r s).c a b ≤ 10 * (#(blob β a) * lgN n) + 2 * g ^ 2 := by
  rw [sum_c_netS s hs, sum_add_distrib, ← mul_sum]
  set ν := #(blob β a)
  have hsa := hA a
  have htouch := X.hcSystem_card_touch_le r a
  have hcw : ∑ b ∈ univ.erase a, cw (X.eP r a b) (s a b) ≤ g + 2 * ν * (lgN n + 2) := by
    have h1 := two_pow_sum_cw_le' (univ.erase a) (fun b => X.eP r a b) (fun b => s a b) (2 * ν) hsa
    have hN : ∑ b ∈ univ.erase a, X.eP r a b = (X.chords.delta a).card := by
      simp only [eP]; rw [LabelSystem.sum_pairItems]; rfl
    rw [hN] at h1
    have h3 : 3 * ((X.chords.delta a).card / (2 * ν) + 1) ≤ 2 ^ (lgN n + 2) := by
      have hd := card_delta_le (X := X) a
      have e1 : (X.chords.delta a).card / (2 * ν) ≤ n / 2 := by
        rcases Nat.eq_zero_or_pos ν with h0 | hpos
        · simp [h0]
        · refine (Nat.div_le_div_right hd).trans (le_of_eq ?_)
          rw [show #(blob β a) * n = ν * n from rfl, mul_comm 2 ν, Nat.mul_div_mul_left _ _ hpos]
      have e2 := lt_two_pow_lgN n
      rw [pow_succ] at e2 ⊢
      omega
    have h4 : (3 * ((X.chords.delta a).card / (2 * ν) + 1)) ^ (2 * ν) ≤ 2 ^ ((lgN n + 2) * (2 * ν)) :=
      (Nat.pow_le_pow_left h3 _).trans_eq (pow_mul _ _ _).symm
    have hcard : #(univ.erase a) ≤ g := by rw [card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]; omega
    have h5 : 2 ^ (∑ b ∈ univ.erase a, cw (X.eP r a b) (s a b)) ≤ 2 ^ (g + 2 * ν * (lgN n + 2)) := by
      calc _ ≤ _ := h1
        _ ≤ 2 ^ g * 2 ^ ((lgN n + 2) * (2 * ν)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hcard) h4
        _ = _ := by rw [← pow_add]; congr 1; ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h5
  have hl := one_le_lgN n
  have hg : g ≤ g ^ 2 := by rw [sq]; exact Nat.le_mul_self g
  have : ν ≤ ν * lgN n := Nat.le_mul_of_pos_right _ hl
  nlinarith

theorem sum_card_blob : ∑ a : Fin g, #(blob β a) = n := by
  have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ) (f := β) (fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_fin] at this
  exact this.symm

/-- **Proposition 3.2, the total**: `U ≤ 10(n·lgd + n) + 3g³` with `lgd = ⌊log₂(M/n + 2)⌋`, `M ≥ m`. -/
theorem U_netS_le (s : Fin g → Fin g → ℕ) (hs : ∀ a b, s a b = s b a) (hA : Adm β s)
    {M : ℕ} (hM : m ≤ M) :
    (X.netS r s).U ≤ 10 * (n * Nat.log 2 (M / n + 2) + n) + 3 * g ^ 3 := by
  rw [netS, LabelSystem.PairCode.U_eqP]
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => rcap_eq hs a b]
  simp only [eP]
  set lgd := Nat.log 2 (M / n + 2)
  have hsum : ∑ a, ∑ b ∈ univ.erase a, s a b ≤ 2 * n := by
    calc ∑ a, ∑ b ∈ univ.erase a, s a b ≤ ∑ a : Fin g, 2 * #(blob β a) := sum_le_sum fun a _ => hA a
      _ = 2 * n := by rw [← mul_sum, sum_card_blob]
  have hcw : ∑ a, ∑ b ∈ univ.erase a, cw ((X.hcSystem r).pairItems a b).length (s a b) ≤
      g ^ 2 + 2 * n * (lgd + 3) := by
    set T := (univ : Finset (Fin g)).sigma fun a => univ.erase a
    have hT : #T ≤ g ^ 2 := by
      rw [card_sigma]
      calc ∑ a : Fin g, #(univ.erase a) ≤ ∑ _a : Fin g, g := sum_le_sum fun a _ => by
            rw [card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]; omega
        _ = g ^ 2 := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sq]
    have h1 := two_pow_sum_cw_le' T (fun p => ((X.hcSystem r).pairItems p.1 p.2).length) (fun p => s p.1 p.2)
      (2 * n) (by rw [sum_sigma]; exact hsum)
    rw [sum_sigma, sum_sigma] at h1
    have hE : ∑ a, ∑ b ∈ univ.erase a, ((X.hcSystem r).pairItems a b).length = 2 * m := by
      simp only [LabelSystem.sum_pairItems]
      rw [LabelSystem.sum_card_inc, Fintype.card_fin]
    rw [hE] at h1
    have h3 : 3 * (2 * m / (2 * n) + 1) < 2 ^ (lgd + 3) := by
      have e1 : 2 * m / (2 * n) ≤ M / n := by
        rw [Nat.mul_div_mul_left _ _ (by norm_num)]; exact Nat.div_le_div_right hM
      have e2 : M / n + 2 < 2 ^ (lgd + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      rw [pow_succ, pow_succ] at *
      omega
    have h4 : (3 * (2 * m / (2 * n) + 1)) ^ (2 * n) ≤ 2 ^ ((lgd + 3) * (2 * n)) :=
      (Nat.pow_le_pow_left h3.le _).trans_eq (pow_mul _ _ _).symm
    have h5 : 2 ^ (∑ a, ∑ b ∈ univ.erase a, cw ((X.hcSystem r).pairItems a b).length (s a b)) ≤
        2 ^ (g ^ 2 + 2 * n * (lgd + 3)) := by
      calc _ ≤ _ := h1
        _ ≤ 2 ^ (g ^ 2) * 2 ^ ((lgd + 3) * (2 * n)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hT) h4
        _ = _ := by rw [← pow_add]; congr 1; ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h5
  have hR := Crossing.card_copyIdx_le g
  have hsplit : ∑ a, ∑ b ∈ univ.erase a, (cw ((X.hcSystem r).pairItems a b).length (s a b) + 2 * s a b) =
      ∑ a, ∑ b ∈ univ.erase a, cw ((X.hcSystem r).pairItems a b).length (s a b) +
        2 * ∑ a, ∑ b ∈ univ.erase a, s a b := by
    simp only [sum_add_distrib, mul_sum]
  rw [hsplit]
  have hg : g ^ 2 ≤ g ^ 3 := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · simp [h0]
    · exact Nat.pow_le_pow_right h0 (by norm_num)
  nlinarith

/-- **The bound `B = 2n² + 1`**. -/
theorem abs_T_lt (a : Fin g) (ℓ : Fin m → Label) (y : CopyIdx g → Bool) :
    |(X.hcSystem r).T a ℓ y| < 2 ^ (2 * (n * n) + 1) := by
  refine (X.abs_hcT_lt r a ℓ y).trans_le (pow_le_pow_right₀ (by norm_num) ?_)
  have : mu G β a ≤ n * n := by
    unfold mu
    calc ∑ v ∈ blob β a, G.degree v ≤ ∑ _v ∈ blob β a, n :=
          sum_le_sum fun v _ => (G.degree_lt_card_verts v).le.trans (by simp)
      _ = #(blob β a) * n := by rw [sum_const, smul_eq_mul]
      _ ≤ n * n := Nat.mul_le_mul_right _ ((card_le_univ _).trans (by simp))
  omega

/-- **Definition 2 for `N_s`** (admissible, bounded, symmetric `s`), with `P = 10·ν·lgN n + 2g² + 1`
and `B = 2n² + 1` for any `ν ≥ max_a |V_a|`. -/
theorem netS_is (s : Fin g → Fin g → ℕ) (hs : ∀ a b, s a b = s b a) (hA : Adm β s)
    {ν : ℕ} (hν : ∀ a, #(blob β a) ≤ ν) :
    (X.netS r s).Is (10 * (ν * lgN n) + 2 * g ^ 2 + 1) (2 * (n * n) + 1) := by
  refine LabelSystem.PairCode.netP_is _ (by omega) (by omega) (fun a => ?_) fun a x _ => abs_T_lt a x.1 x.2
  have := sum_c_netS_le (X := X) (r := r) s hs hA a
  have : #(blob β a) * lgN n ≤ ν * lgN n := Nat.mul_le_mul_right _ (hν a)
  show ∑ b ∈ univ.erase a, (X.netS r s).c a b ≤ _
  omega

end Crossing

end EthFollowup.ExactHC
