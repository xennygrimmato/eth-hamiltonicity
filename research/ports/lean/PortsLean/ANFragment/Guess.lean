import PortsLean.ANFragment.Defs

/-!
# Guess counts on Anthropic's run semantics (overlay; no AN file is edited)

* `EvG θ F x l` mirrors `NS1.Ev` constructor by constructor; each accepting run carries a guess
  count, `guess` contributes 1, sequencing adds.
* `EvG.toEv` : projection to `Ev` (so `EvG` lists are the accepting runs of `Ev`, by `Ev.unique`).
* `GB θ F x g` : some guess-annotated run list has every accepting run with `≤ g` guesses.
* `DoesG θ F x Q c g := Does θ F x Q c ∧ GB θ F x g` would be the guess-aware `Does`
  (`Does` itself lives in `NS1/Comp.lean`, not copied; `GB` is the new clause).

Guess bounds cannot be read off `Does`/`Gives` (e.g. `ite guess id fail` gives one weight-1
output yet guesses once), so every bound below is syntax-directed.
-/

namespace NS1G

open NS1

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- `Ev` with a guess count on every accepting run. -/
inductive EvG (θ : List Bool → A) : Fm → Tree → List (Run A × ℕ) → Prop
  | quote (c x : Tree) : EvG θ (.quote c) x [(.det 1 c, 0)]
  | id (x : Tree) : EvG θ .id x [(.det 1 x, 0)]
  | hd {a : Fm} {x : Tree} {l : List (Run A × ℕ)} : EvG θ a x l →
      EvG θ (.hd a) x (l.map fun r => (r.1.tick r.1.out.hd, r.2))
  | tl {a : Fm} {x : Tree} {l : List (Run A × ℕ)} : EvG θ a x l →
      EvG θ (.tl a) x (l.map fun r => (r.1.tick r.1.out.tl, r.2))
  | cons {a b : Fm} {x : Tree} {la lb : List (Run A × ℕ)} : EvG θ a x la → EvG θ b x lb →
      EvG θ (.cons a b) x (la.flatMap fun r => lb.map fun s =>
        ((r.1.seq s.1).tick (.cons r.1.out s.1.out), r.2 + s.2))
  | ite {a b c : Fm} {x : Tree} {la : List (Run A × ℕ)} {L : Run A × ℕ → List (Run A × ℕ)} :
      EvG θ a x la → (∀ r ∈ la, r.1.out ≠ .nil → EvG θ b x (L r)) →
      (∀ r ∈ la, r.1.out = .nil → EvG θ c x (L r)) →
      EvG θ (.ite a b c) x (la.flatMap fun r => (L r).map fun s => ((r.1.seq s.1).tick s.1.out, r.2 + s.2))
  | run {a b : Fm} {x : Tree} {la lb : List (Run A × ℕ)} {L : Run A × ℕ → Run A × ℕ → List (Run A × ℕ)} :
      EvG θ a x la → EvG θ b x lb →
      (∀ r ∈ la, ∀ s ∈ lb, EvG θ (Fm.ofTree r.1.out) s.1.out (L r s)) →
      EvG θ (.run a b) x (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t =>
        (((r.1.seq s.1).seq t.1).tick t.1.out, r.2 + s.2 + t.2))
  | guess (x : Tree) : EvG θ .guess x [(.det 1 .nil, 1), (.det 1 Tree.one, 1)]
  | fail (x : Tree) : EvG θ .fail x []
  | theta {a : Fm} {x : Tree} {l : List (Run A × ℕ)} : EvG θ a x l →
      EvG θ (.theta a) x (l.map fun r => (⟨r.1.cost + 1, r.1.th * θ r.1.out.path, r.1.bill, .nil⟩, r.2))
  | mul {a : Fm} {x : Tree} {l : List (Run A × ℕ)} : EvG θ a x l →
      EvG θ (.mul a) x (l.map fun r => (⟨r.1.cost + 1, r.1.th, r.1.bill ++ [r.1.out.path], .nil⟩, r.2))

/-- **Projection.** Forgetting guess counts gives `Ev`. -/
theorem EvG.toEv {F : Fm} {x : Tree} {l : List (Run A × ℕ)} (h : EvG θ F x l) :
    Ev θ F x (l.map Prod.fst) := by
  induction h with
  | quote c x => exact Ev.quote c x
  | id x => exact Ev.id x
  | hd _ ih => simpa [List.map_map, Function.comp_def] using Ev.hd ih
  | tl _ ih => simpa [List.map_map, Function.comp_def] using Ev.tl ih
  | cons _ _ iha ihb =>
    have := Ev.cons iha ihb
    simpa [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def] using this
  | @ite a b c x la L _ _ _ iha ihb ihc =>
    classical
    let L' : Run A → List (Run A) := fun r => if r.out = .nil then evl θ c x else evl θ b x
    have hL : ∀ r ∈ la, (L r).map Prod.fst = L' r.1 := by
      intro r hr
      by_cases h : r.1.out = .nil
      · simp only [L', if_pos h]; exact ((ihc r hr h).evl).symm
      · simp only [L', if_neg h]; exact ((ihb r hr h).evl).symm
    have := Ev.ite (L := L') iha
      (fun r hr hne => by
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
        rw [← hL r' hr']; exact ihb r' hr' hne)
      (fun r hr he => by
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
        rw [← hL r' hr']; exact ihc r' hr' he)
    convert this using 1
    rw [List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun r hr => ?_
    rw [← hL r hr, List.map_map, List.map_map]
    rfl
  | @run a b x la lb L _ _ _ iha ihb ih =>
    classical
    let L' : Run A → Run A → List (Run A) := fun r s => evl θ (Fm.ofTree r.out) s.out
    have hL : ∀ r ∈ la, ∀ s ∈ lb, (L r s).map Prod.fst = L' r.1 s.1 := fun r hr s hs =>
      ((ih r hr s hs).evl).symm
    have := Ev.run (L := L') iha ihb (fun r hr s hs => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
      rw [← hL r' hr' s' hs']; exact ih r' hr' s' hs')
    convert this using 1
    rw [List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun r hr => ?_
    rw [List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun s hs => ?_
    rw [← hL r hr s hs, List.map_map, List.map_map]
    rfl
  | guess x => exact Ev.guess x
  | fail x => exact Ev.fail x
  | theta _ ih => simpa [List.map_map, Function.comp_def] using Ev.theta ih
  | mul _ ih => simpa [List.map_map, Function.comp_def] using Ev.mul ih

theorem EvG.evl {F : Fm} {x : Tree} {l : List (Run A × ℕ)} (h : EvG θ F x l) :
    NS1.evl θ F x = l.map Prod.fst := h.toEv.evl

theorem EvG.mem_evl {F : Fm} {x : Tree} {l : List (Run A × ℕ)} (h : EvG θ F x l) {r : Run A × ℕ}
    (hr : r ∈ l) : r.1 ∈ NS1.evl θ F x := by
  rw [h.evl]; exact List.mem_map_of_mem hr

variable (θ) in
/-- Every accepting run makes at most `g` guesses. -/
def GB (F : Fm) (x : Tree) (g : ℕ) : Prop := ∃ l : List (Run A × ℕ), EvG θ F x l ∧ ∀ r ∈ l, r.2 ≤ g

namespace GB

variable {F G : Fm} {x : Tree} {g g' g'' : ℕ}

theorem hl (h : GB θ F x g) : Hl θ F x := let ⟨_, h1, _⟩ := h; h1.toEv.hl

theorem mono (h : GB θ F x g) (hg : g ≤ g') : GB θ F x g' :=
  let ⟨l, h1, h2⟩ := h; ⟨l, h1, fun r hr => (h2 r hr).trans hg⟩

theorem quote (c x : Tree) : GB θ (.quote c) x 0 := ⟨_, EvG.quote c x, by simp⟩
theorem id (x : Tree) : GB θ .id x 0 := ⟨_, EvG.id x, by simp⟩
theorem fail (x : Tree) : GB θ .fail x 0 := ⟨_, EvG.fail x, by simp⟩
theorem guess (x : Tree) : GB θ .guess x 1 := ⟨_, EvG.guess x, by simp⟩

theorem hd (h : GB θ F x g) : GB θ (.hd F) x g :=
  let ⟨l, h1, h2⟩ := h; ⟨_, EvG.hd h1, by simpa using h2⟩
theorem tl (h : GB θ F x g) : GB θ (.tl F) x g :=
  let ⟨l, h1, h2⟩ := h; ⟨_, EvG.tl h1, by simpa using h2⟩
theorem theta (h : GB θ F x g) : GB θ (.theta F) x g :=
  let ⟨l, h1, h2⟩ := h; ⟨_, EvG.theta h1, by simpa using h2⟩
theorem mul (h : GB θ F x g) : GB θ (.mul F) x g :=
  let ⟨l, h1, h2⟩ := h; ⟨_, EvG.mul h1, by simpa using h2⟩

theorem cons (hF : GB θ F x g) (hG : GB θ G x g') : GB θ (.cons F G) x (g + g') := by
  obtain ⟨la, a1, a2⟩ := hF
  obtain ⟨lb, b1, b2⟩ := hG
  refine ⟨_, EvG.cons a1 b1, fun u hu => ?_⟩
  simp only [List.mem_flatMap, List.mem_map] at hu
  obtain ⟨r, hr, s, hs, rfl⟩ := hu
  exact Nat.add_le_add (a2 r hr) (b2 s hs)

theorem ite {a b c : Fm} (ha : GB θ a x g)
    (hb : ∀ r ∈ NS1.evl θ a x, r.out ≠ .nil → GB θ b x g')
    (hc : ∀ r ∈ NS1.evl θ a x, r.out = .nil → GB θ c x g'') :
    GB θ (.ite a b c) x (g + max g' g'') := by
  classical
  obtain ⟨la, a1, a2⟩ := ha
  let Lb : List (Run A × ℕ) := if h : ∃ r ∈ NS1.evl θ a x, r.out ≠ .nil then
    (hb h.choose h.choose_spec.1 h.choose_spec.2).choose else []
  let Lc : List (Run A × ℕ) := if h : ∃ r ∈ NS1.evl θ a x, r.out = .nil then
    (hc h.choose h.choose_spec.1 h.choose_spec.2).choose else []
  have hLb : ∀ r ∈ la, r.1.out ≠ .nil → EvG θ b x Lb ∧ ∀ s ∈ Lb, s.2 ≤ g' := by
    intro r hr hne
    have h : ∃ r ∈ NS1.evl θ a x, r.out ≠ .nil := ⟨r.1, a1.mem_evl hr, hne⟩
    simp only [Lb, dif_pos h]
    exact (hb h.choose h.choose_spec.1 h.choose_spec.2).choose_spec
  have hLc : ∀ r ∈ la, r.1.out = .nil → EvG θ c x Lc ∧ ∀ s ∈ Lc, s.2 ≤ g'' := by
    intro r hr he
    have h : ∃ r ∈ NS1.evl θ a x, r.out = .nil := ⟨r.1, a1.mem_evl hr, he⟩
    simp only [Lc, dif_pos h]
    exact (hc h.choose h.choose_spec.1 h.choose_spec.2).choose_spec
  let L : Run A × ℕ → List (Run A × ℕ) := fun r => if r.1.out = .nil then Lc else Lb
  refine ⟨_, EvG.ite (L := L) a1 (fun r hr hne => by simp only [L, if_neg hne]; exact (hLb r hr hne).1)
    (fun r hr he => by simp only [L, if_pos he]; exact (hLc r hr he).1), fun u hu => ?_⟩
  simp only [List.mem_flatMap, List.mem_map] at hu
  obtain ⟨r, hr, s, hs, rfl⟩ := hu
  have := a2 r hr
  by_cases he : r.1.out = .nil
  · simp only [L, if_pos he] at hs
    have := (hLc r hr he).2 s hs
    show r.2 + s.2 ≤ g + max g' g''
    omega
  · simp only [L, if_neg he] at hs
    have := (hLb r hr he).2 s hs
    show r.2 + s.2 ≤ g + max g' g''
    omega

theorem run {a b : Fm} (ha : GB θ a x g) (hb : GB θ b x g')
    (h : ∀ r ∈ NS1.evl θ a x, ∀ s ∈ NS1.evl θ b x, GB θ (Fm.ofTree r.out) s.out g'') :
    GB θ (.run a b) x (g + g' + g'') := by
  classical
  obtain ⟨la, a1, a2⟩ := ha
  obtain ⟨lb, b1, b2⟩ := hb
  let L : Run A × ℕ → Run A × ℕ → List (Run A × ℕ) := fun r s =>
    if hrs : r.1 ∈ NS1.evl θ a x ∧ s.1 ∈ NS1.evl θ b x then (h r.1 hrs.1 s.1 hrs.2).choose else []
  have hL : ∀ r ∈ la, ∀ s ∈ lb, EvG θ (Fm.ofTree r.1.out) s.1.out (L r s) ∧ ∀ t ∈ L r s, t.2 ≤ g'' := by
    intro r hr s hs
    have hrs : r.1 ∈ NS1.evl θ a x ∧ s.1 ∈ NS1.evl θ b x := ⟨a1.mem_evl hr, b1.mem_evl hs⟩
    simp only [L, dif_pos hrs]
    exact (h r.1 hrs.1 s.1 hrs.2).choose_spec
  refine ⟨_, EvG.run a1 b1 fun r hr s hs => (hL r hr s hs).1, fun u hu => ?_⟩
  simp only [List.mem_flatMap, List.mem_map] at hu
  obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
  have := a2 r hr; have := b2 s hs; have := (hL r hr s hs).2 t ht
  show r.2 + s.2 + t.2 ≤ g + g' + g''
  omega

/-- `app p F` runs the fixed code `p` on every value of `F`. -/
theorem app {p : Tree} (hF : GB θ F x g) (h : ∀ s ∈ NS1.evl θ F x, GB θ (Fm.ofTree p) s.out g') :
    GB θ (NS1.app p F) x (g + g') := by
  have := run (GB.quote (θ := θ) p x) hF (g'' := g') (fun r hr s hs => by
    rw [(Ev.quote (θ := θ) p x).evl, List.mem_singleton] at hr
    subst hr
    exact h s hs)
  simpa [NS1.app] using this

theorem lett {body : Fm} (hF : GB θ F x g) (h : ∀ s ∈ NS1.evl θ F x, GB θ body s.out g') :
    GB θ (NS1.lett F body) x (g + g') := by
  have := app (p := body.code) hF (by rw [Fm.ofTree_code]; exact h)
  simpa [NS1.app, NS1.lett] using this

end GB

/-! ## Values of deterministic sub-formulas -/

theorem evl_dt {F : Fm} {x o : Tree} {k : ℕ} (h : Dt θ F x o k) : NS1.evl θ F x = [.det k o] :=
  Ev.evl h

theorem evl_cons {a b : Fm} {x : Tree} (ha : Hl θ a x) (hb : Hl θ b x) :
    NS1.evl θ (.cons a b) x = (NS1.evl θ a x).flatMap fun r => (NS1.evl θ b x).map fun s =>
      (r.seq s).tick (.cons r.out s.out) :=
  (Ev.cons ha.ev hb.ev).evl

theorem evl_lett_out {e body : Fm} {x : Tree} (he : Hl θ e x) (h : ∀ s ∈ NS1.evl θ e x, Hl θ body s.out)
    {u : Run A} (hu : u ∈ NS1.evl θ (lett e body) x) :
    ∃ s ∈ NS1.evl θ e x, ∃ t ∈ NS1.evl θ body s.out, u.out = t.out := by
  rw [(Ev.lett he.ev h).evl] at hu
  simp only [List.mem_flatMap, List.mem_map] at hu
  obtain ⟨s, hs, t, ht, rfl⟩ := hu
  exact ⟨s, hs, t, ht, rfl⟩

/-! ## `pickB`: a unary walk; picking from a list of `n` costs `≤ n` guesses -/

theorem pickB_guesses (xs : List Tree) : GB θ pickB (.cons pickB.code (listT xs)) xs.length := by
  induction xs with
  | nil =>
    have := GB.ite (θ := θ) (b := .ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))
      (c := .fail) (g' := 0) (g'' := 0) (GB.tl (GB.id _))
      (fun r hr hne => by
        rw [evl_dt (Dt.tl (Dt.id _)), List.mem_singleton] at hr
        subst hr; exact absurd rfl hne)
      (fun _ _ _ => GB.fail _)
    simpa [pickB] using this
  | cons y ys ih =>
    set x := Tree.cons pickB.code (listT (y :: ys))
    have hinner : GB θ (.ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) x
        (1 + max 0 (0 + 0 + ys.length)) := by
      refine GB.ite (GB.guess x) (fun _ _ _ => GB.hd (GB.tl (GB.id x))) (fun r hr he => ?_)
      refine GB.run (GB.hd (GB.id x)) (GB.cons (GB.hd (GB.id x)) (GB.tl (GB.tl (GB.id x))))
        (fun r hr s hs => ?_)
      rw [evl_dt (Dt.hd (Dt.id x)), List.mem_singleton] at hr
      rw [evl_dt (Dt.cons (Dt.hd (Dt.id x)) (Dt.tl (Dt.tl (Dt.id x)))), List.mem_singleton] at hs
      subst hr hs
      simpa [Run.det, x, Fm.ofTree_code, listT, Tree.hd, Tree.tl] using ih
    have := GB.ite (θ := θ) (c := .fail) (g'' := 0) (GB.tl (GB.id x)) (fun _ _ _ => hinner)
      (fun r hr he => GB.fail _)
    refine (by simpa [pickB] using this : GB θ pickB x (0 + max (1 + max 0 (0 + 0 + ys.length)) 0)).mono ?_
    simp; omega

/-! ## Folds: guesses add over the list -/

theorem foldB_guesses {step : Fm} {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree}
    (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → GB θ step (.cons x σ) (d x) ∧
      ∀ r ∈ NS1.evl θ step (.cons x σ), Inv ys r.out)
    {σ : Tree} (hσ : Inv xs σ) :
    GB θ (foldB step) (.cons (foldB step).code (.cons σ (listT xs))) (xs.map d).sum := by
  induction xs generalizing σ with
  | nil =>
    have := GB.ite (θ := θ) (g' := 0) (g'' := 0) (b := .run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.tl (.tl (.tl .id)))))) (GB.tl (GB.tl (GB.id _)))
      (fun r hr hne => by
        rw [evl_dt (Dt.tl (Dt.tl (Dt.id _))), List.mem_singleton] at hr
        subst hr; exact absurd rfl hne)
      (fun _ _ _ => GB.hd (GB.tl (GB.id _)))
    simpa [foldB] using this
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := h y ys σ List.mem_cons_self hσ
    set x := Tree.cons (foldB step).code (.cons σ (listT (y :: ys)))
    have hE : GB θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step) x (0 + d y) := by
      refine GB.lett (GB.cons (GB.hd (GB.tl (GB.tl (GB.id x)))) (GB.hd (GB.tl (GB.id x))) |>.mono
        (by simp)) (fun s hs => ?_)
      rw [evl_dt (Dt.cons (Dt.hd (Dt.tl (Dt.tl (Dt.id x)))) (Dt.hd (Dt.tl (Dt.id x)))),
        List.mem_singleton] at hs
      subst hs
      simpa [Run.det, x, listT, Tree.hd, Tree.tl] using h1
    have hHl : ∀ s ∈ NS1.evl θ (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.tl (.tl (.tl .id))))) x, ∃ r ∈ NS1.evl θ step (.cons y σ),
          s.out = .cons (foldB step).code (.cons r.out (listT ys)) := by
      intro s hs
      rw [evl_cons (GB.hd (GB.id x)).hl ((GB.cons hE (GB.tl (GB.tl (GB.tl (GB.id x))))).hl)] at hs
      simp only [List.mem_flatMap, List.mem_map] at hs
      obtain ⟨r0, hr0, s1, hs1, rfl⟩ := hs
      rw [evl_dt (Dt.hd (Dt.id x)), List.mem_singleton] at hr0
      subst hr0
      rw [evl_cons hE.hl (GB.tl (GB.tl (GB.tl (GB.id x)))).hl] at hs1
      simp only [List.mem_flatMap, List.mem_map] at hs1
      obtain ⟨e, he, t, ht, rfl⟩ := hs1
      rw [evl_dt (Dt.tl (Dt.tl (Dt.tl (Dt.id x)))), List.mem_singleton] at ht
      subst ht
      have hEl : Hl θ (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) x :=
        (GB.cons (GB.hd (GB.tl (GB.tl (GB.id x)))) (GB.hd (GB.tl (GB.id x)))).hl
      obtain ⟨s0, hs0, t0, ht0, hout⟩ := evl_lett_out hEl (fun s hs => by
        rw [evl_dt (Dt.cons (Dt.hd (Dt.tl (Dt.tl (Dt.id x)))) (Dt.hd (Dt.tl (Dt.id x)))),
          List.mem_singleton] at hs
        subst hs
        simpa [Run.det, x, listT, Tree.hd, Tree.tl] using h1.hl) he
      rw [evl_dt (Dt.cons (Dt.hd (Dt.tl (Dt.tl (Dt.id x)))) (Dt.hd (Dt.tl (Dt.id x)))),
        List.mem_singleton] at hs0
      subst hs0
      refine ⟨t0, by simpa [Run.det, x, listT, Tree.hd, Tree.tl] using ht0, ?_⟩
      simp [Run.tick, Run.det, hout, x, listT, Tree.hd, Tree.tl]
    have hrun : GB θ (.run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.tl (.tl (.tl .id)))))) x (0 + (0 + (0 + d y + 0)) + (ys.map d).sum) := by
      refine GB.run (GB.hd (GB.id x)) (GB.cons (GB.hd (GB.id x)) (GB.cons hE (GB.tl (GB.tl (GB.tl (GB.id x))))))
        (fun r hr s hs => ?_)
      rw [evl_dt (Dt.hd (Dt.id x)), List.mem_singleton] at hr
      subst hr
      obtain ⟨r, hr, hs'⟩ := hHl s hs
      rw [hs']
      simpa [Run.det, x, Fm.ofTree_code, Tree.hd] using
        ih (fun z zs τ hz hinv => h z zs τ (List.mem_cons_of_mem _ hz) hinv) (h2 r hr)
    have := GB.ite (θ := θ) (c := .hd (.tl .id)) (g'' := 0) (GB.tl (GB.tl (GB.id x))) (fun _ _ _ => hrun)
      (fun r hr he => by
        rw [evl_dt (Dt.tl (Dt.tl (Dt.id x))), List.mem_singleton] at hr
        subst hr; simp [Run.det, x, listT, Tree.tl] at he)
    refine (by simpa [foldB] using this :
      GB θ (foldB step) x (0 + max (0 + (0 + (0 + d y + 0)) + (ys.map d).sum) 0)).mono ?_
    simp

theorem evl_run_out {a b : Fm} {x : Tree} (ha : Hl θ a x) (hb : Hl θ b x)
    (h : ∀ r ∈ NS1.evl θ a x, ∀ s ∈ NS1.evl θ b x, Hl θ (Fm.ofTree r.out) s.out)
    {u : Run A} (hu : u ∈ NS1.evl θ (.run a b) x) :
    ∃ r ∈ NS1.evl θ a x, ∃ s ∈ NS1.evl θ b x, ∃ t ∈ NS1.evl θ (Fm.ofTree r.out) s.out, u.out = t.out := by
  rw [(Ev.run' ha.ev hb.ev h).evl] at hu
  simp only [List.mem_flatMap, List.mem_map] at hu
  obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
  exact ⟨r, hr, s, hs, t, ht, rfl⟩

/-- `foldF`, for arbitrary values of the initial state and of the list. -/
theorem foldF_guesses {step s l : Fm} {x : Tree} {gs gl B : ℕ} (hs : GB θ s x gs) (hl : GB θ l x gl)
    (h : ∀ a ∈ NS1.evl θ s x, ∀ b ∈ NS1.evl θ l x,
      GB θ (foldB step) (.cons (foldB step).code (.cons a.out b.out)) B) :
    GB θ (foldF step s l) x (gs + gl + B) := by
  have h1 := GB.cons (GB.quote (θ := θ) (foldB step).code x) (GB.cons hs hl)
  refine (GB.app (p := (foldB step).code) h1 (g' := B) (fun u hu => ?_)).mono (by omega)
  rw [evl_cons (GB.quote _ _).hl (GB.cons hs hl).hl] at hu
  simp only [List.mem_flatMap, List.mem_map] at hu
  obtain ⟨q, hq, w, hw, rfl⟩ := hu
  rw [evl_dt (Dt.quote _ _), List.mem_singleton] at hq
  subst hq
  rw [evl_cons hs.hl hl.hl] at hw
  simp only [List.mem_flatMap, List.mem_map] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  simpa [Run.tick, Run.det, Fm.ofTree_code] using h a ha b hb

theorem listT_toList' (t : Tree) : listT t.toList = t := by
  induction t with
  | nil => rfl
  | cons p q _ ihq => simp only [Tree.toList, listT, ihq]

/-- A fold whose step is guess-free on every input is guess-free on every list. -/
theorem foldB_free {step : Fm} (hstep : ∀ y, GB θ step y 0) (σ t : Tree) :
    GB θ (foldB step) (.cons (foldB step).code (.cons σ t)) 0 := by
  have := foldB_guesses (θ := θ) (step := step) (Inv := fun _ _ => True) (d := fun _ => 0)
    (xs := t.toList) (fun z ys τ _ _ => ⟨hstep _, fun _ _ => trivial⟩) (σ := σ) trivial
  simpa [listT_toList'] using this

/-- `appF` is guess-free beyond its arguments. -/
theorem appF_guesses {a b : Fm} {x : Tree} {ga gb : ℕ} (ha : GB θ a x ga) (hb : GB θ b x gb) :
    GB θ (appF a b) x (gb + ga) := by
  have inner : GB θ (foldF .id (.quote .nil) a) x (0 + ga + 0) :=
    foldF_guesses (GB.quote _ _) ha fun _ _ _ _ => foldB_free (fun _ => GB.id _) _ _
  have := foldF_guesses (B := 0) hb inner fun _ _ _ _ => foldB_free (fun _ => GB.id _) _ _
  simpa [appF] using this

/-- One step of the composed lister: run `G'` on the head piece, append to the state. -/
theorem stepC_guesses {G' : Tree} {y σ : Tree} {g' : ℕ} (hG' : GB θ (Fm.ofTree G') y g') :
    GB θ (stepC G') (.cons y σ) g' := by
  have h1 : GB θ (.cons (NS1.app G' (.hd .id)) (.tl .id)) (.cons y σ) (0 + g' + 0) :=
    GB.cons (GB.app (GB.hd (GB.id _)) fun s hs => by
      rw [evl_dt (Dt.hd (Dt.id _)), List.mem_singleton] at hs
      subst hs; simpa [Run.det, Tree.hd] using hG') (GB.tl (GB.id _))
  have := GB.lett (body := appF (.hd .id) (.tl .id)) h1 (g' := 0 + 0) fun s _ =>
    appF_guesses (GB.hd (GB.id _)) (GB.tl (GB.id _))
  simpa [stepC] using this

/-- **Additivity under `compC`.** If every accepting run of `G` on `z` makes `≤ g` guesses and
outputs a list whose pieces `y` each have `≤ g'_y` guesses under `G'`, with `Σ_y g'_y ≤ B` for
every output, then every accepting run of `compC G G'` on `z` makes `≤ g + B` guesses.
`compC` itself adds no guess. -/
theorem compC_guesses {G G' : Tree} {z : Tree} {g B : ℕ} (d : Tree → ℕ)
    (hG : GB θ (Fm.ofTree G) z g)
    (hpieces : ∀ r ∈ NS1.evl θ (Fm.ofTree G) z,
      (∀ y ∈ r.out.toList, GB θ (Fm.ofTree G') y (d y)) ∧ (r.out.toList.map d).sum ≤ B) :
    GB θ (compC G G') z (g + B) := by
  have happ : GB θ (NS1.app G .id) z (0 + g) :=
    GB.app (GB.id z) fun s hs => by
      rw [evl_dt (Dt.id _), List.mem_singleton] at hs; subst hs; simpa [Run.det] using hG
  have hHl : ∀ r ∈ NS1.evl θ (.quote G) z, ∀ s ∈ NS1.evl θ .id z, Hl θ (Fm.ofTree r.out) s.out := by
    intro r hr s hs
    rw [evl_dt (Dt.quote _ _), List.mem_singleton] at hr
    rw [evl_dt (Dt.id _), List.mem_singleton] at hs
    subst hr hs; simpa [Run.det] using hG.hl
  refine (GB.lett (body := foldF (stepC G') (.quote .nil) .id) happ (g' := B) fun u hu => ?_).mono
    (by omega)
  obtain ⟨r, hr, s, hs, t, ht, hout⟩ := evl_run_out (GB.quote _ _).hl (GB.id _).hl hHl
    (by simpa [NS1.app] using hu)
  rw [evl_dt (Dt.quote _ _), List.mem_singleton] at hr
  rw [evl_dt (Dt.id _), List.mem_singleton] at hs
  subst hr hs
  simp only [Run.det] at ht
  obtain ⟨hp, hsum⟩ := hpieces t ht
  rw [hout]
  refine (foldF_guesses (GB.quote _ _) (GB.id _) (B := B) fun a ha b hb => ?_).mono (by omega)
  rw [evl_dt (Dt.quote _ _), List.mem_singleton] at ha
  rw [evl_dt (Dt.id _), List.mem_singleton] at hb
  subst ha hb
  have := foldB_guesses (θ := θ) (step := stepC G') (Inv := fun _ _ => True) (d := d)
    (xs := t.out.toList) (fun y ys τ hy _ => ⟨stepC_guesses (hp y hy), fun _ _ => trivial⟩)
    (σ := .nil) trivial
  simp only [Run.det, listT_toList'] at this ⊢
  exact this.mono hsum

end NS1G
