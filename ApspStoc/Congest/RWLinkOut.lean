import ApspStoc.Congest.RWLinkKnown

/-!
# The random-walk construction: the output

Unless the walks overflow, the hop records of a node `v` are the crossings of the walks whose
edge contains `v` (`mem_recs`), the local hop list of a walk is `hopsAt (rwPath …) v`
(`hopsL_eq`), and the local output is the `G₀`-knowledge `g0At` of the walks under the seeds
`rwSeedMap C P hR τ` (`outMS_eq`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Lists -/

/-- The indexed list of the `some` values of `g` on `0, …, N-1`: each value is indexed by the
number of earlier values. -/
lemma zipIdx_filterMap_range {β : Type} (g : ℕ → Option β) (N : ℕ) :
    ((List.range N).filterMap g).zipIdx =
      (List.range N).filterMap (fun j => (g j).map (fun e => (e, ((List.range j).filterMap g).length))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, List.filterMap_append, List.zipIdx_append, ih]
    congr 1
    rcases h : g N with _ | e <;> simp [h]

/-- `hopsAt` of a list of `some` values over a range. -/
lemma hopsAt_filterMap_range (g : ℕ → Option (Sym2 V)) (N : ℕ) (v : V) :
    hopsAt ((List.range N).filterMap g) v = (List.range N).filterMap (fun j => match g j with
      | some e => if v ∈ e then some (((List.range j).filterMap g).length, e) else none
      | none => none) := by
  unfold hopsAt
  rw [zipIdx_filterMap_range, List.filter_filterMap, List.map_filterMap]
  apply List.filterMap_congr
  intro j _
  rcases h : g j with _ | e
  · simp
  · by_cases hv : v ∈ e <;> simp [hv]

section Out

variable {C : Finset (Sym2 V)} {P : Finset (Port V)} {R Rmax ℓ Dmax : ℕ} {hR : R ≤ Rmax}
  {τ : V → RWTable V Rmax ℓ Dmax}

lemma lastG_succ_ge (w : RWIdx P R) {j : ℕ} (hj : 2 * ℓ ≤ j) : lastG C P hR τ w (j + 1) = none := by
  simp only [lastG, stepG, dif_neg (show ¬ j < 2 * ℓ by omega)]

lemma cntG_succ_of (w : RWIdx P R) {j : ℕ} {e : Sym2 V} (h : lastG C P hR τ w (j + 1) = some e) :
    cntG C P hR τ w (j + 1) = cntG C P hR τ w j + 1 := by
  simp only [lastG] at h
  simp [cntG, h]

/-- The number of crossings before entry `j` of a crossing entry is its path position. -/
lemma length_filterMap_lastG (w : RWIdx P R) :
    ∀ j, ((List.range (j + 1)).filterMap (lastG C P hR τ w)).length = cntG C P hR τ w j + 1 := by
  intro j
  induction j with
  | zero => simp [lastG, cntG]
  | succ j ih =>
    rw [List.range_succ, List.filterMap_append, List.length_append, ih]
    rcases h : (stepG C P hR τ w j).2 with _ | e <;> simp [cntG, lastG, h] <;> omega

lemma length_filterMap_lastG_of (w : RWIdx P R) {j : ℕ} {e : Sym2 V}
    (h : lastG C P hR τ w j = some e) :
    ((List.range j).filterMap (lastG C P hR τ w)).length = cntG C P hR τ w j := by
  cases j with
  | zero => simp [cntG]
  | succ j => rw [length_filterMap_lastG, cntG_succ_of w h]

variable (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax)

include hD hpos in
lemma rwTraj_eq_range (w : RWIdx P R) : rwTraj C w.1.1 (rwSeedMap C P hR τ w) =
    (List.range (2 * ℓ + 1)).map (fun j => (posG C P hR τ w j, lastG C P hR τ w j)) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j ≤ 2 * ℓ
  · rw [traj_get hD hpos w j hj, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  · rw [List.getElem?_eq_none (by rw [rwTraj_length]; omega),
      List.getElem?_eq_none (by simp; omega)]

include hD hpos in
lemma rwPath_eq_range (w : RWIdx P R) : rwPath C w.1.1 (rwSeedMap C P hR τ w) =
    (List.range (2 * ℓ + 1)).filterMap (lastG C P hR τ w) := by
  unfold rwPath
  rw [rwTraj_eq_range hD hpos, List.filterMap_map]
  rfl

include hD hpos in
/-- The hops of a walk at `v`, entry by entry. -/
lemma hopsAt_rwPath (w : RWIdx P R) (v : V) :
    hopsAt (rwPath C w.1.1 (rwSeedMap C P hR τ w)) v =
      (List.range (2 * ℓ + 1)).filterMap (fun j => match lastG C P hR τ w j with
        | some e => if v ∈ e then some (cntG C P hR τ w j, e) else none
        | none => none) := by
  rw [rwPath_eq_range hD hpos, hopsAt_filterMap_range]
  apply List.filterMap_congr
  intro j _
  cases h : lastG C P hR τ w j with
  | none => rfl
  | some e => rw [length_filterMap_lastG_of w h]

variable (N : WNet V) (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C) (t : ℕ)
  (hov : ¬ rwOverflow C P R ℓ t (rwSeedMap C P hR τ))

include hP in
lemma posG_mem_lastG (hC : NoLoops C) (w : RWIdx P R) {j : ℕ} {e : Sym2 V}
    (h : lastG C P hR τ w j = some e) : posG C P hR τ w j ∈ e := by
  cases j with
  | zero =>
    simp only [lastG, Option.some.injEq] at h
    subst h
    rw [posG_zero]; exact rwOtherEnd_mem (port_mem hP w.1.2).2
  | succ j =>
    have hj : j < 2 * ℓ := by
      by_contra hj; rw [lastG_succ_ge w (by omega)] at h; simp at h
    simp only [lastG] at h
    rcases stepG_cases hC w j with h' | ⟨e', h', -, hy⟩
    · rw [h'] at h; simp at h
    · rw [h'] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [posG_succ w hj, h']
      exact rwOtherEnd_mem hy

include N hCN hP hD hpos hov in
/-- **The hop records** of `v`: the crossings (entry `j`, path position `cntG w j`, edge `e`) of
the walks whose edge contains `v`. -/
theorem mem_recs (v : V) (r : HRec V) :
    r ∈ recs (envG C P R t τ v) (fullO C P R t τ v) ↔ ∃ (w : RWIdx P R) (j : ℕ) (e : Sym2 V),
      j ≤ 2 * ℓ ∧ lastG C P hR τ w j = some e ∧ v ∈ e ∧
        r = (w.1.1, w.2.val, j, cntG C P hR τ w j, e) := by
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  have hheld := held_eq R N hCN hP hD hpos t hov
  unfold recs
  simp only [envG_ℓ, envG_R, envG_ports, mem_union, mem_biUnion, mem_range, mem_univ, true_and]
  constructor
  · rintro ((⟨j, hj, x, hx, hr⟩ | ⟨j, hj, u, hz⟩) | ⟨p, hp, hr⟩)
    · rw [hheld j (by omega) v, mem_heldG] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      rw [show (tokG C P hR τ w j).2.2.2 = lastG C P hR τ w j from rfl] at hr
      cases hl : lastG C P hR τ w j with
      | none => rw [hl] at hr; simp at hr
      | some e =>
        rw [hl] at hr
        simp only [mem_singleton] at hr
        exact ⟨w, j, e, by omega, hl, hw ▸ posG_mem_lastG hP hC w hl, hr⟩
    · obtain ⟨z, hz', rfl⟩ := mem_image.1 hz
      rw [hheld j (by omega) v, mem_crossTo_heldG t hj] at hz'
      obtain ⟨w, e, hw, h, rfl⟩ := hz'
      have hl : lastG C P hR τ w (j + 1) = some e := by simp only [lastG, h]
      refine ⟨w, j + 1, e, by omega, hl, ?_, by simp only [cntG_succ_of w hl]⟩
      rcases stepG_cases hC w j with h' | ⟨e', h', -, hy⟩
      · rw [h'] at h; simp at h
      · rw [h'] at h
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        rw [← h.2, ← hw]; exact hy
    · rw [mem_filter] at hp
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hr
      refine ⟨(⟨p, hp.1⟩, ⟨i, mem_range.1 hi⟩), 0, p.2, Nat.zero_le _, rfl, ?_, rfl⟩
      rw [← hp.2]; exact (port_mem hP hp.1).2
  · rintro ⟨w, j, e, hj, hl, hv, rfl⟩
    cases j with
    | zero =>
      have hl' := hl
      simp only [lastG, Option.some.injEq] at hl'
      subst hl'
      have hp := port_mem hP w.1.2
      rcases (mem_iff_otherEnd hp.2 v).1 hv with rfl | rfl
      · right
        exact ⟨w.1.1, mem_filter.2 ⟨w.1.2, rfl⟩, mem_image.2 ⟨w.2.val, mem_range.2 w.2.2, rfl⟩⟩
      · left; left
        refine ⟨0, by omega, tokG C P hR τ w 0, ?_, by simp [tokG, lastG, cntG]⟩
        rw [hheld 0 (by omega) _, mem_heldG]
        exact ⟨w, rfl, rfl⟩
    | succ j =>
      have hj' : j < 2 * ℓ := by omega
      have hl' := hl
      simp only [lastG] at hl'
      rcases stepG_cases hC w j with h' | ⟨e', h', -, hy⟩
      · rw [h'] at hl'; simp at hl'
      · rw [h'] at hl'
        simp only [Option.some.injEq] at hl'
        subst hl'
        rcases (mem_iff_otherEnd hy v).1 hv with rfl | rfl
        · left; right
          refine ⟨j, hj', otherEnd e' (posG C P hR τ w j),
            mem_image.2 ⟨(w.1.1, w.2.val, cntG C P hR τ w j + 1, e'), ?_, ?_⟩⟩
          · rw [hheld j (by omega) _]
            exact (mem_crossTo_heldG t hj').2 ⟨w, e', rfl, h', rfl⟩
          · simp only [cntG_succ_of w hl]
        · left; left
          refine ⟨j + 1, by omega, tokG C P hR τ w (j + 1), ?_, by simp [tokG, hl]⟩
          rw [hheld (j + 1) (by omega) _, mem_heldG]
          exact ⟨w, by rw [posG_succ w hj', h'], rfl⟩

include N hCN hP hD hpos hov in
/-- **The local hop list** of a walk is its list of hops `hopsAt (rwPath …) v`. -/
theorem hopsL_eq (v : V) (w : RWIdx P R) :
    hopsL (envG C P R t τ v) (fullO C P R t τ v) w.1.1 w.2.val =
      hopsAt (rwPath C w.1.1 (rwSeedMap C P hR τ w)) v := by
  rw [hopsAt_rwPath hD hpos]
  unfold hopsL
  simp only [envG_ℓ]
  apply List.filterMap_congr
  intro j hj
  have hj := List.mem_range.1 hj
  have hfil : ∀ r, r ∈ (recs (envG C P R t τ v) (fullO C P R t τ v)).filter
      (fun r => r.1 = w.1.1 ∧ r.2.1 = w.2.val ∧ r.2.2.1 = j) ↔
      ∃ e, lastG C P hR τ w j = some e ∧ v ∈ e ∧ r = (w.1.1, w.2.val, j, cntG C P hR τ w j, e) := by
    intro r
    rw [mem_filter, mem_recs hD hpos N hCN hP t hov]
    constructor
    · rintro ⟨⟨w', j', e, -, hl, hv, rfl⟩, h1, h2, h3⟩
      obtain rfl : w' = w := walk_ext h1 h2
      obtain rfl : j' = j := h3
      exact ⟨e, hl, hv, rfl⟩
    · rintro ⟨e, hl, hv, rfl⟩
      exact ⟨⟨w, j, e, by omega, hl, hv, rfl⟩, rfl, rfl, rfl⟩
  cases hl : lastG C P hR τ w j with
  | none =>
    have : (recs (envG C P R t τ v) (fullO C P R t τ v)).filter
        (fun r => r.1 = w.1.1 ∧ r.2.1 = w.2.val ∧ r.2.2.1 = j) = ∅ := by
      ext r; rw [hfil r]; simp [hl]
    rw [this, toList_empty]; rfl
  | some e =>
    simp only
    by_cases hv : v ∈ e
    · have : (recs (envG C P R t τ v) (fullO C P R t τ v)).filter
          (fun r => r.1 = w.1.1 ∧ r.2.1 = w.2.val ∧ r.2.2.1 = j) =
          {(w.1.1, w.2.val, j, cntG C P hR τ w j, e)} := by
        ext r; rw [hfil r, mem_singleton]; simp [hl, hv]
      rw [this, toList_singleton, if_pos hv]; rfl
    · have : (recs (envG C P R t τ v) (fullO C P R t τ v)).filter
          (fun r => r.1 = w.1.1 ∧ r.2.1 = w.2.val ∧ r.2.2.1 = j) = ∅ := by
        ext r; rw [hfil r]; simp [hl, hv]
      rw [this, toList_empty, if_neg hv]; rfl

include hP hD hpos in
/-- A walk with a hop at `v` visits `v` (at its start or at a position). -/
lemma visits_of_hops (hC : NoLoops C) (v : V) (w : RWIdx P R)
    (h : hopsAt (rwPath C w.1.1 (rwSeedMap C P hR τ w)) v ≠ []) :
    w.1.1.1 = v ∨ ∃ j ≤ 2 * ℓ, posG C P hR τ w j = v := by
  rw [hopsAt_rwPath hD hpos] at h
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨j, hj, hx⟩ := List.mem_filterMap.1 hx
  have hj := List.mem_range.1 hj
  cases hl : lastG C P hR τ w j with
  | none => rw [hl] at hx; simp at hx
  | some e =>
    rw [hl] at hx
    simp only at hx
    by_cases hv : v ∈ e
    swap
    · rw [if_neg hv] at hx; simp at hx
    cases j with
    | zero =>
      simp only [lastG, Option.some.injEq] at hl
      subst hl
      rcases (mem_iff_otherEnd (port_mem hP w.1.2).2 v).1 hv with rfl | rfl
      · left; rfl
      · right; exact ⟨0, Nat.zero_le _, rfl⟩
    | succ j =>
      have hj' : j < 2 * ℓ := by
        by_contra hj'; rw [lastG_succ_ge w (by omega)] at hl; simp at hl
      have hl' := hl
      simp only [lastG] at hl'
      rcases stepG_cases hC w j with h' | ⟨e', h', -, hy⟩
      · rw [h'] at hl'; simp at hl'
      · rw [h'] at hl'
        simp only [Option.some.injEq] at hl'
        subst hl'
        rcases (mem_iff_otherEnd hy v).1 hv with rfl | rfl
        · right; exact ⟨j, by omega, rfl⟩
        · right; exact ⟨j + 1, by omega, by rw [posG_succ w hj', h']⟩

include N hCN hP hD hpos hov in
/-- **The local output** is the `G₀`-knowledge of the node. -/
theorem outMS_eq (v : V) (g : G0Data) :
    ((g, outMS (envG C P R t τ v) (fullO C P R t τ v)) : G0K V) =
      g0At C P R ℓ (rwSeedMap C P hR τ) g (.inl v) := by
  classical
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  unfold outMS g0At
  simp only [Prod.mk.injEq, true_and]
  rw [knownF_eq N hCN hP hD hpos t hov v]
  unfold KfinG
  rw [image_val_of_injOn (fun w _ w' _ h => keyG_inj h), Multiset.map_map]
  have hF : ∀ w : RWIdx P R, ((fun r : Rep V => ((r.1, r.2.2),
      hopsL (envG C P R t τ v) (fullO C P R t τ v) r.1 r.2.1)) ∘ keyG C P hR τ) w =
      ((w.1.1, (rwEnd C w.1.1 (rwSeedMap C P hR τ w)).getD w.1.1),
        hopsAt (rwPath C w.1.1 (rwSeedMap C P hR τ w)) v) := by
    intro w
    simp only [Function.comp_apply, keyG]
    rw [hopsL_eq hD hpos N hCN hP t hov v w]
    rfl
  rw [Multiset.map_congr rfl (fun w _ => hF w)]
  unfold rwSurvivors
  rw [Multiset.filter_map, Multiset.filter_map]
  congr 1
  rw [← filter_val, ← filter_val, filter_filter, filter_filter]
  congr 1
  apply filter_congr
  intro w _
  simp only [Function.comp_apply, survG]
  constructor
  · rintro ⟨⟨hs, -⟩, hh⟩; exact ⟨hs, hh⟩
  · rintro ⟨hs, hh⟩
    exact ⟨⟨hs, visits_of_hops hD hpos hP hC v w hh⟩, hh⟩

end Out

end APSP.Stoc.Congest
