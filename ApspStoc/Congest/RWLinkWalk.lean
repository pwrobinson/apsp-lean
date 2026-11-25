import ApspStoc.Congest.RWLinkGlob

/-!
# The random-walk construction: local knowledge in the global schedule

For seed tables `τ` and the abstract seeds `σ = rwSeedMap C P hR τ`, the walk `w` is at
`posG w j` before step `j`, its step `j` is `stepG w j` (a lazy step by `lazyStepD` with the seed
of its current node), its last step's edge is `lastG w j` and the path position of its last
crossing is `cntG w j`. The trajectory `rwTraj C w.1.1 (σ w)` lists `(posG w j, lastG w j)`
(`traj_get`).

Unless the walks overflow (`rwOverflow`), the local knowledge in the global schedule is:
* `held_eq`: the tokens held by `y` before step `j` are the tokens `tokG w j` of the walks at `y`;
* `known_eq`: after the reversed steps down to `j`, `y` knows the reports of the surviving walks at
  `y` at some step `≥ j`;
* `knownF_eq`: at the end, `y` knows the reports of the surviving walks visiting `y` (including
  their start nodes).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

section Walk

variable (C : Finset (Sym2 V)) (P : Finset (Port V)) {R Rmax ℓ Dmax : ℕ} (hR : R ≤ Rmax)
  (τ : V → RWTable V Rmax ℓ Dmax)

/-- the node of walk `w` before step `j` -/
noncomputable def posG (w : RWIdx P R) (j : ℕ) : V := rwWalkPos C hR τ w j

/-- step `j` of walk `w`: (new node, crossed edge) -/
noncomputable def stepG (w : RWIdx P R) (j : ℕ) : V × Option (Sym2 V) :=
  if h : j < 2 * ℓ then lazyStepD Dmax C (posG C P hR τ w j)
    (τ (posG C P hR τ w j) w.1.1 (Fin.castLE hR w.2) ⟨j, h⟩) else (posG C P hR τ w j, none)

/-- the edge of the last step of `w` before step `j` (the first crossing for `j = 0`) -/
noncomputable def lastG (w : RWIdx P R) : ℕ → Option (Sym2 V)
  | 0 => some w.1.1.2
  | j + 1 => (stepG C P hR τ w j).2

/-- the path position of the last crossing of `w` before step `j` -/
noncomputable def cntG (w : RWIdx P R) : ℕ → ℕ
  | 0 => 0
  | j + 1 => cntG w j + if (stepG C P hR τ w j).2.isSome then 1 else 0

/-- the token of walk `w` before step `j` -/
noncomputable def tokG (w : RWIdx P R) (j : ℕ) : Tok V :=
  (w.1.1, w.2.val, cntG C P hR τ w j, lastG C P hR τ w j)

/-- the tokens of the walks at `y` before step `j` -/
noncomputable def heldG (y : V) (j : ℕ) : Finset (Tok V) :=
  (univ.filter (fun w : RWIdx P R => posG C P hR τ w j = y)).image (fun w => tokG C P hR τ w j)

/-- the end port of `w` (as in `g0At`) -/
noncomputable def endG (w : RWIdx P R) : Port V :=
  (rwEnd C w.1.1 (rwSeedMap C P hR τ w)).getD w.1.1

/-- `w` survives -/
def survG (w : RWIdx P R) : Prop := rwSurv C P w.1.1 (rwSeedMap C P hR τ w)

/-- the report of `w` -/
noncomputable def keyG (w : RWIdx P R) : Rep V := (w.1.1, w.2.val, endG C P hR τ w)

open Classical in
/-- the reports of the surviving walks at `y` at some step in `[j, 2ℓ]` -/
noncomputable def KgS (y : V) (j : ℕ) : Finset (Rep V) :=
  (univ.filter (fun w : RWIdx P R => survG C P hR τ w ∧
    ∃ j', j ≤ j' ∧ j' ≤ 2 * ℓ ∧ posG C P hR τ w j' = y)).image (keyG C P hR τ)

open Classical in
/-- the reports of the surviving walks visiting `y` (start node or a position) -/
noncomputable def KfinG (y : V) : Finset (Rep V) :=
  (univ.filter (fun w : RWIdx P R => survG C P hR τ w ∧
    (w.1.1.1 = y ∨ ∃ j ≤ 2 * ℓ, posG C P hR τ w j = y))).image (keyG C P hR τ)

variable {C P hR τ}

lemma posG_zero (w : RWIdx P R) : posG C P hR τ w 0 = otherEnd w.1.1.2 w.1.1.1 := rfl

lemma stepG_lt (w : RWIdx P R) {j : ℕ} (hj : j < 2 * ℓ) : stepG C P hR τ w j =
    lazyStepD Dmax C (posG C P hR τ w j) (τ (posG C P hR τ w j) w.1.1 (Fin.castLE hR w.2) ⟨j, hj⟩) := by
  rw [stepG, dif_pos hj]

lemma posG_succ (w : RWIdx P R) {j : ℕ} (hj : j < 2 * ℓ) :
    posG C P hR τ w (j + 1) = (stepG C P hR τ w j).1 := by
  rw [stepG_lt w hj]; exact rwWalkPos_succ hR τ w hj

lemma tokG_fst (w : RWIdx P R) (j : ℕ) : (tokG C P hR τ w j).1 = w.1.1 := rfl

/-- The trajectory lists the positions and last edges. -/
lemma traj_get (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (w : RWIdx P R) :
    ∀ j ≤ 2 * ℓ, (rwTraj C w.1.1 (rwSeedMap C P hR τ w))[j]? =
      some (posG C P hR τ w j, lastG C P hR τ w j) := by
  intro j hj
  cases j with
  | zero => rw [rwTraj_getElem?_zero]; rfl
  | succ j =>
    rw [rwTraj_rwSeedMap_getElem?_succ hD hpos hR τ w (by omega), posG_succ w (by omega)]
    show _ = some ((stepG C P hR τ w j).1, (stepG C P hR τ w j).2)
    rw [stepG_lt w (by omega)]
    rfl

lemma traj_succ (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (w : RWIdx P R) {j : ℕ}
    (hj : j < 2 * ℓ) : (rwTraj C w.1.1 (rwSeedMap C P hR τ w))[j + 1]? = some (stepG C P hR τ w j) := by
  rw [traj_get hD hpos w (j + 1) (by omega), posG_succ w hj]; rfl

lemma rwEnd_eq (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (w : RWIdx P R) :
    rwEnd C w.1.1 (rwSeedMap C P hR τ w) =
      (lastG C P hR τ w (2 * ℓ)).map (fun e => (posG C P hR τ w (2 * ℓ), e)) := by
  unfold rwEnd
  rw [List.getLast?_eq_getElem?, rwTraj_length, Nat.add_sub_cancel, traj_get hD hpos w _ le_rfl]
  cases lastG C P hR τ w (2 * ℓ) <;> rfl

lemma survG_iff (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (w : RWIdx P R) :
    survG C P hR τ w ↔ ∃ e, lastG C P hR τ w (2 * ℓ) = some e ∧ (posG C P hR τ w (2 * ℓ), e) ∈ P := by
  unfold survG rwSurv
  rw [rwEnd_eq hD hpos]
  constructor
  · rintro ⟨q, hq, h⟩
    cases hl : lastG C P hR τ w (2 * ℓ) with
    | none => rw [hl] at h; simp at h
    | some e =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨e, rfl, h ▸ hq⟩
  · rintro ⟨e, he, hP⟩
    exact ⟨_, hP, by rw [he]; rfl⟩

lemma endG_eq (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (w : RWIdx P R) {e : Sym2 V}
    (he : lastG C P hR τ w (2 * ℓ) = some e) : endG C P hR τ w = (posG C P hR τ w (2 * ℓ), e) := by
  unfold endG; rw [rwEnd_eq hD hpos, he]; rfl

lemma lst_envG (t : ℕ) (w : RWIdx P R) {j : ℕ} (hj : j < 2 * ℓ) :
    lst (envG C P R t τ (posG C P hR τ w j)) (tokG C P hR τ w j) j = stepG C P hR τ w j := by
  rw [stepG_lt w hj]
  unfold lst
  simp only [envG_Dmax, envG_E, envG_me]
  rw [lazyStepD_filter]
  congr 1
  show seedL (τ (posG C P hR τ w j)) w.1.1 w.2.val j = _
  unfold seedL
  rw [dif_pos ⟨lt_of_lt_of_le w.2.2 hR, hj⟩]
  rfl

lemma stepG_cases (hC : NoLoops C) (w : RWIdx P R) (j : ℕ) :
    stepG C P hR τ w j = (posG C P hR τ w j, none) ∨ ∃ e, stepG C P hR τ w j =
      (otherEnd e (posG C P hR τ w j), some e) ∧ e ∈ C ∧ posG C P hR τ w j ∈ e := by
  by_cases hj : j < 2 * ℓ
  · rw [stepG_lt w hj]; exact lazyStepD_cases _ _ _ _
  · left; rw [stepG, dif_neg hj]

lemma cntG_le (w : RWIdx P R) : ∀ j, cntG C P hR τ w j ≤ j := by
  intro j
  induction j with
  | zero => simp [cntG]
  | succ j ih => simp only [cntG]; split_ifs <;> omega

lemma mem_heldG {y : V} {j : ℕ} {x : Tok V} :
    x ∈ heldG C P hR τ y j ↔ ∃ w, posG C P hR τ w j = y ∧ tokG C P hR τ w j = x := by
  simp [heldG]

/-- Walks are determined by their start port and index. -/
lemma walk_ext {w w' : RWIdx P R} (h1 : w.1.1 = w'.1.1) (h2 : w.2.val = w'.2.val) : w = w' :=
  Prod.ext (Subtype.ext h1) (Fin.ext h2)

lemma keyG_inj {w w' : RWIdx P R} (h : keyG C P hR τ w = keyG C P hR τ w') : w = w' := by
  simp only [keyG, Prod.mk.injEq] at h
  exact walk_ext h.1 h.2.1

/-! ### Crossing and staying tokens -/

lemma crossOf_eq_some {st : V × Option (Sym2 V)} {x : Tok V} {u : V} {z : TokF V} :
    crossOf st x u = some z ↔ ∃ e, st = (u, some e) ∧ z = (x.1, x.2.1, x.2.2.1 + 1, e) := by
  obtain ⟨u', o⟩ := st
  cases o with
  | none =>
    constructor
    · intro h; simp [crossOf] at h
    · rintro ⟨e, h, -⟩; simp at h
  | some e =>
    simp only [crossOf]
    split_ifs with h
    · subst h
      constructor
      · intro h'; exact ⟨e, rfl, (Option.some.inj h').symm⟩
      · rintro ⟨e', h1, rfl⟩
        simp only [Prod.mk.injEq, Option.some.injEq, true_and] at h1
        rw [h1]
    · constructor
      · intro h'; simp at h'
      · rintro ⟨e', h1, -⟩
        simp only [Prod.mk.injEq] at h1
        exact absurd h1.1 h

lemma mem_crossTo_heldG (t : ℕ) {u y : V} {j : ℕ} (hj : j < 2 * ℓ) {z : TokF V} :
    z ∈ crossTo (envG C P R t τ u) (heldG C P hR τ u j) j y ↔
      ∃ w e, posG C P hR τ w j = u ∧ stepG C P hR τ w j = (y, some e) ∧
        z = (w.1.1, w.2.val, cntG C P hR τ w j + 1, e) := by
  unfold crossTo
  simp only [mem_biUnion, Option.mem_toFinset, Option.mem_def, mem_heldG]
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, h⟩
    subst hw
    rw [lst_envG t w hj, crossOf_eq_some] at h
    obtain ⟨e, h1, h2⟩ := h
    exact ⟨w, e, rfl, h1, h2⟩
  · rintro ⟨w, e, hw, h1, h2⟩
    subst hw
    refine ⟨_, ⟨w, rfl, rfl⟩, ?_⟩
    rw [lst_envG t w hj, crossOf_eq_some]
    exact ⟨e, h1, h2⟩

lemma mem_stays_heldG (t : ℕ) {y : V} {j : ℕ} (hj : j < 2 * ℓ) {x : Tok V} :
    x ∈ stays (envG C P R t τ y) (heldG C P hR τ y j) j ↔
      ∃ w, posG C P hR τ w j = y ∧ (stepG C P hR τ w j).2 = none ∧
        x = (w.1.1, w.2.val, cntG C P hR τ w j, none) := by
  unfold stays
  simp only [mem_image, mem_filter, mem_heldG]
  constructor
  · rintro ⟨x', ⟨⟨w, hw, rfl⟩, h⟩, rfl⟩
    subst hw
    rw [lst_envG t w hj] at h
    exact ⟨w, rfl, h, rfl⟩
  · rintro ⟨w, hw, h, rfl⟩
    subst hw
    exact ⟨_, ⟨⟨w, rfl, rfl⟩, by rw [lst_envG t w hj]; exact h⟩, rfl⟩

/-- The walks at `y` after step `j`: those that stayed at `y`, and those that crossed to `y`. -/
lemma heldG_succ (hC : NoLoops C) (t : ℕ) (y : V) {j : ℕ} (hj : j < 2 * ℓ) :
    heldG C P hR τ y (j + 1) = stays (envG C P R t τ y) (heldG C P hR τ y j) j ∪
      univ.biUnion (fun u => (crossTo (envG C P R t τ u) (heldG C P hR τ u j) j y).image asTok) := by
  ext x
  rw [mem_union, mem_stays_heldG t hj, mem_heldG, mem_biUnion]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [posG_succ w hj] at hw
    rcases stepG_cases hC w j with h | ⟨e, h, -, -⟩
    · left
      have hw' : posG C P hR τ w j = y := by rw [h] at hw; exact hw
      refine ⟨w, hw', by rw [h], ?_⟩
      simp [tokG, cntG, lastG, h]
    · right
      have hw' : otherEnd e (posG C P hR τ w j) = y := by rw [h] at hw; exact hw
      refine ⟨posG C P hR τ w j, mem_univ _, mem_image.2 ⟨_, (mem_crossTo_heldG t hj).2
        ⟨w, e, rfl, by rw [h, hw'], rfl⟩, ?_⟩⟩
      simp [tokG, cntG, lastG, h, asTok]
  · rintro (⟨w, hw, h, rfl⟩ | ⟨u, -, hx⟩)
    · refine ⟨w, ?_, ?_⟩
      · rw [posG_succ w hj]
        rcases stepG_cases hC w j with h' | ⟨e, h', -⟩
        · rw [h']; exact hw
        · rw [h'] at h; simp at h
      · simp [tokG, cntG, lastG, h]
    · obtain ⟨z, hz, rfl⟩ := mem_image.1 hx
      obtain ⟨w, e, hw, h, rfl⟩ := (mem_crossTo_heldG t hj).1 hz
      refine ⟨w, by rw [posG_succ w hj, h], ?_⟩
      simp [tokG, cntG, lastG, h, asTok]

/-- Without overflow, at most `t` tokens cross a directed edge in a step. -/
lemma card_crossTo_le (hC : NoLoops C) (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (t : ℕ)
    (hov : ¬ rwOverflow C P R ℓ t (rwSeedMap C P hR τ)) (u y : V) {j : ℕ} (hj : j < 2 * ℓ) :
    (crossTo (envG C P R t τ u) (heldG C P hR τ u j) j y).card ≤ t := by
  classical
  have hsub : crossTo (envG C P R t τ u) (heldG C P hR τ u j) j y ⊆
      (univ.filter (fun w : RWIdx P R => (rwTraj C w.1.1 (rwSeedMap C P hR τ w))[j + 1]? =
        some (y, some s(u, y)))).image
        (fun w => (w.1.1, w.2.val, cntG C P hR τ w j + 1, s(u, y))) := by
    intro z hz
    rw [mem_crossTo_heldG t hj] at hz
    obtain ⟨w, e, hw, h, rfl⟩ := hz
    rcases stepG_cases hC w j with h' | ⟨e', h', he', hy'⟩
    · rw [h'] at h; simp at h
    · rw [h'] at h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨hy, rfl⟩ := h
      have hes : e' = s(u, y) := by rw [← hw, ← hy, rwOtherEnd_spec hy']
      refine mem_image.2 ⟨w, mem_filter.2 ⟨mem_univ _, ?_⟩, by rw [hes]⟩
      rw [traj_succ hD hpos w hj, h', hy, hes]
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  unfold rwOverflow at hov
  push_neg at hov
  convert hov j hj y s(u, y) using 2

/-! ### Receiving the packets of a slot window -/

lemma rcv_window (S : Finset (TokF V)) (t : ℕ) (hS : S.card ≤ t) :
    (range t).biUnion (fun k => ((((S.toList[k]?).map tokMsg).bind parseTok).map asTok).toFinset) =
      S.image asTok := by
  ext x
  simp only [mem_biUnion, mem_range, Option.mem_toFinset, Option.mem_def, mem_image]
  constructor
  · rintro ⟨k, -, h⟩
    cases hk : S.toList[k]? with
    | none => rw [hk] at h; simp at h
    | some z =>
      rw [hk] at h
      simp only [Option.map_some, Option.bind_some, parseTok_tokMsg, Option.some.injEq] at h
      exact ⟨z, mem_toList.1 (List.mem_of_getElem? hk), h⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 (mem_toList.2 hz)
    have hkl : k < S.toList.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hk; simp at hk
    rw [length_toList] at hkl
    refine ⟨k, by omega, ?_⟩
    rw [hk]
    simp

/-! ### The tokens held -/

section Held

variable (N : WNet V) (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C)

include hP in
lemma port_mem {p : Port V} (hp : p ∈ P) : p.2 ∈ C ∧ p.1 ∈ p.2 := by
  have := hP hp
  unfold allPorts portsOf at this
  obtain ⟨v, -, hv⟩ := mem_biUnion.1 this
  obtain ⟨h1, h2, h3⟩ := mem_portsAt.1 hv
  exact ⟨h2, h1 ▸ h3⟩

include hP in
/-- A node has at most one port of `P` towards a given neighbour. -/
lemma port_unique {p p' : Port V} (hp : p ∈ P) (hp' : p' ∈ P) (h1 : p.1 = p'.1)
    (h2 : otherEnd p.2 p.1 = otherEnd p'.2 p'.1) : p = p' := by
  have a := port_mem hP hp
  have a' := port_mem hP hp'
  rw [h1] at h2 a
  exact Prod.ext h1 (eq_of_otherEnd a.2 a'.2 h2)

include hP in
lemma aSend_eq (t : ℕ) (u y : V) (i : ℕ) :
    aSend (envG C P R t τ u) y i = if h : ∃ p ∈ P, p.1 = u ∧ otherEnd p.2 u = y then
      some (tokMsg (h.choose, i, 0, h.choose.2)) else none := by
  unfold aSend
  show (((P.filter (fun p => p.1 = u)).filter (fun p => otherEnd p.2 u = y)).toList.head?).map
    (fun p => tokMsg (p, i, 0, p.2)) = _
  rw [filter_filter]
  split_ifs with h
  · obtain ⟨hp, h1, h2⟩ := h.choose_spec
    have : (P.filter (fun p => p.1 = u ∧ otherEnd p.2 u = y)) = {h.choose} := by
      rw [eq_singleton_iff_unique_mem]
      refine ⟨mem_filter.2 ⟨hp, h1, h2⟩, fun p hp' => ?_⟩
      rw [mem_filter] at hp'
      exact port_unique hP hp'.1 hp (by rw [hp'.2.1, h1]) (by rw [hp'.2.1, h1, hp'.2.2, h2])
    rw [this, toList_singleton]
    rfl
  · have : (P.filter (fun p => p.1 = u ∧ otherEnd p.2 u = y)) = ∅ := by
      rw [filter_eq_empty_iff]
      intro p hp hpu
      exact h ⟨p, hp, hpu⟩
    rw [this, toList_empty]
    rfl

variable (R)

include hCN hP in
/-- **The tokens held** before step `j` in the global schedule are those of the walks at the node
(unless the walks overflow). -/
theorem held_eq (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (t : ℕ)
    (hov : ¬ rwOverflow C P R ℓ t (rwSeedMap C P hR τ)) :
    ∀ j ≤ 2 * ℓ, ∀ y, held (envG C P R t τ y) (fullO C P R t τ y) j = heldG C P hR τ y j := by
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  intro j
  induction j with
  | zero =>
    intro _ y
    simp only [held]
    unfold rcvA
    ext x
    simp only [mem_biUnion, mem_range, mem_univ, true_and, Option.mem_toFinset, Option.mem_def,
      envG_R, mem_heldG]
    constructor
    · rintro ⟨s, hs, u, h⟩
      simp only [fullO] at h
      rw [schedG_A C P R t τ hs, aSend_eq hP] at h
      split_ifs at h with hex
      · simp only [Option.bind_some, parseTok_tokMsg, Option.map_some, Option.some.injEq] at h
        obtain ⟨hp, h1, h2⟩ := hex.choose_spec
        refine ⟨(⟨hex.choose, hp⟩, ⟨s, hs⟩), ?_, ?_⟩
        · show otherEnd hex.choose.2 hex.choose.1 = y
          rw [h1]; exact h2
        · rw [← h]; rfl
      · simp at h
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2.val, w.2.2, w.1.1.1, ?_⟩
      simp only [fullO]
      rw [schedG_A C P R t τ w.2.2, aSend_eq hP]
      have hex : ∃ p ∈ P, p.1 = w.1.1.1 ∧ otherEnd p.2 w.1.1.1 = y := ⟨w.1.1, w.1.2, rfl, hw⟩
      rw [dif_pos hex]
      obtain ⟨hp, h1, h2⟩ := hex.choose_spec
      have he : hex.choose = w.1.1 := port_unique hP hp w.1.2 h1 (by rw [h1, h2]; exact hw.symm)
      simp only [Option.bind_some, parseTok_tokMsg, Option.map_some, Option.some.injEq, he]
      rfl
  | succ j ih =>
    intro hj y
    simp only [held]
    rw [ih (by omega) y, heldG_succ hC t y (by omega)]
    congr 1
    unfold rcvB
    ext x
    simp only [mem_biUnion, mem_range, mem_univ, true_and, envG_R, envG_t]
    constructor
    · rintro ⟨k, hk, u, hx⟩
      refine ⟨u, ?_⟩
      rw [← rcv_window _ t (card_crossTo_le hC hD hpos t hov u y (by omega))]
      refine mem_biUnion.2 ⟨k, mem_range.2 hk, ?_⟩
      simp only [fullO] at hx
      rw [schedG_B C P R t τ (by omega) hk, bSend, ih (by omega) u] at hx
      exact hx
    · rintro ⟨u, hx⟩
      rw [← rcv_window _ t (card_crossTo_le hC hD hpos t hov u y (by omega))] at hx
      obtain ⟨k, hk, hx⟩ := mem_biUnion.1 hx
      refine ⟨k, mem_range.1 hk, u, ?_⟩
      simp only [fullO]
      rw [schedG_B C P R t τ (by omega) (mem_range.1 hk), bSend, ih (by omega) u]
      exact hx

end Held

end Walk

end APSP.Stoc.Congest
