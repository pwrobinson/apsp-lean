import ApspStoc.Congest.RWLinkWalk

/-!
# The random-walk construction: reports and hop records in the global schedule

Unless the walks overflow:
* `known_eq`: after the reversed steps `2ℓ - 1, …, j` a node `y` knows the reports (start port,
  index, end port) of the surviving walks at `y` at some step in `[j, 2ℓ]`;
* `knownF_eq`: at the end, `y` knows the reports of the surviving walks visiting `y` (including
  the walks starting at `y`);
* `mem_recs`: the hop records of `y` are the crossings of the walks whose edge contains `y`
  (with their trajectory entry and path position);
* `hopsL_eq`: the local hop list of a walk is `hopsAt (rwPath …) y`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

section Known

variable {C : Finset (Sym2 V)} {P : Finset (Port V)} {R Rmax ℓ Dmax : ℕ} {hR : R ≤ Rmax}
  {τ : V → RWTable V Rmax ℓ Dmax}

lemma mem_KgS {y : V} {j : ℕ} {z : Rep V} : z ∈ KgS C P hR τ y j ↔ ∃ w, (survG C P hR τ w ∧
    ∃ j', j ≤ j' ∧ j' ≤ 2 * ℓ ∧ posG C P hR τ w j' = y) ∧ keyG C P hR τ w = z := by
  classical
  simp only [KgS, mem_image, mem_filter, mem_univ, true_and]

lemma mem_KfinG {y : V} {z : Rep V} : z ∈ KfinG C P hR τ y ↔ ∃ w, (survG C P hR τ w ∧
    (w.1.1.1 = y ∨ ∃ j ≤ 2 * ℓ, posG C P hR τ w j = y)) ∧ keyG C P hR τ w = z := by
  classical
  simp only [KfinG, mem_image, mem_filter, mem_univ, true_and]

/-- Looking up a walk in a set of reports of walks. -/
lemma lookup_image (S : Finset (RWIdx P R)) (w : RWIdx P R) :
    lookup (S.image (keyG C P hR τ)) w.1.1 w.2.val =
      if w ∈ S then some (endG C P hR τ w) else none := by
  unfold lookup
  by_cases h : w ∈ S
  · have e : (S.image (keyG C P hR τ)).filter (fun z => z.1 = w.1.1 ∧ z.2.1 = w.2.val) =
        {keyG C P hR τ w} := by
      ext z
      simp only [mem_filter, mem_image, mem_singleton]
      constructor
      · rintro ⟨⟨w', -, rfl⟩, h1, h2⟩
        rw [walk_ext h1 h2]
      · rintro rfl; exact ⟨⟨w, h, rfl⟩, rfl, rfl⟩
    rw [e, toList_singleton, if_pos h]; rfl
  · have e : (S.image (keyG C P hR τ)).filter (fun z => z.1 = w.1.1 ∧ z.2.1 = w.2.val) = ∅ := by
      ext z
      simp only [mem_filter, mem_image, notMem_empty, iff_false, not_and]
      rintro ⟨w', hw', rfl⟩ h1 h2
      exact h (walk_ext h1 h2 ▸ hw')
    rw [e, toList_empty, if_neg h]; rfl

open Classical in
lemma lookup_KgS (u : V) (j : ℕ) (w : RWIdx P R) :
    lookup (KgS C P hR τ u j) w.1.1 w.2.val = if survG C P hR τ w ∧
      ∃ j', j ≤ j' ∧ j' ≤ 2 * ℓ ∧ posG C P hR τ w j' = u then some (endG C P hR τ w) else none := by
  classical
  unfold KgS
  rw [lookup_image]
  by_cases h : survG C P hR τ w ∧ ∃ j', j ≤ j' ∧ j' ≤ 2 * ℓ ∧ posG C P hR τ w j' = u
  · rw [if_pos (by simpa using h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

lemma repFor_map (K : Finset (Rep V)) (o : Option (TokF V)) :
    (repFor K (o.map tokMsg)).bind parseRep =
      o.bind (fun z => (lookup K z.1 z.2.1).map (fun q => (z.1, z.2.1, q))) := by
  cases o with
  | none => rfl
  | some z =>
    simp only [repFor, Option.map_some, Option.bind_some, parseTok_tokMsg]
    cases lookup K z.1 z.2.1 <;> simp

lemma exists_toList (S : Finset (TokF V)) (t : ℕ) (hS : S.card ≤ t) (z : TokF V) :
    (∃ k < t, S.toList[k]? = some z) ↔ z ∈ S := by
  constructor
  · rintro ⟨k, -, hk⟩; exact mem_toList.1 (List.mem_of_getElem? hk)
  · intro hz
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 (mem_toList.2 hz)
    have hkl : k < S.toList.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hk; simp at hk
    rw [length_toList] at hkl
    exact ⟨k, by omega, hk⟩

variable (N : WNet V) (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C)
  (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (t : ℕ)
  (hov : ¬ rwOverflow C P R ℓ t (rwSeedMap C P hR τ))

include hD hpos in
lemma finRep_heldG (y : V) :
    finRep (envG C P R t τ y) (heldG C P hR τ y (2 * ℓ)) = KgS C P hR τ y (2 * ℓ) := by
  ext z
  rw [mem_KgS]
  unfold finRep
  simp only [mem_biUnion, mem_heldG]
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, hz⟩
    rw [show (tokG C P hR τ w (2 * ℓ)).2.2.2 = lastG C P hR τ w (2 * ℓ) from rfl] at hz
    cases hl : lastG C P hR τ w (2 * ℓ) with
    | none => rw [hl] at hz; simp at hz
    | some e =>
      rw [hl] at hz
      simp only at hz
      by_cases hp : ((envG C P R t τ y).me, e) ∈ (envG C P R t τ y).ports
      · rw [if_pos hp, mem_singleton] at hz
        subst hz
        have hp' : (y, e) ∈ P := (mem_filter.1 hp).1
        refine ⟨w, ⟨(survG_iff hD hpos w).2 ⟨e, hl, by rw [hw]; exact hp'⟩,
          2 * ℓ, le_rfl, le_rfl, hw⟩, ?_⟩
        simp only [keyG, endG_eq hD hpos w hl, hw]
        rfl
      · rw [if_neg hp] at hz; simp at hz
  · rintro ⟨w, ⟨hs, j', h1, h2, hw⟩, rfl⟩
    obtain rfl : j' = 2 * ℓ := by omega
    obtain ⟨e, hl, hp⟩ := (survG_iff hD hpos w).1 hs
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    rw [show (tokG C P hR τ w (2 * ℓ)).2.2.2 = lastG C P hR τ w (2 * ℓ) from rfl, hl]
    simp only
    rw [if_pos (by exact mem_filter.2 ⟨by rw [← hw]; exact hp, rfl⟩), mem_singleton]
    simp only [keyG, endG_eq hD hpos w hl, hw]
    rfl

/-- The reports received in the reversed step `j`: the surviving walks crossing out of `y` in step
`j`. -/
noncomputable def rcvCG (C : Finset (Sym2 V)) (P : Finset (Port V)) {R Rmax ℓ Dmax : ℕ}
    (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) (y : V) (j : ℕ) : Finset (Rep V) := by
  classical exact (univ.filter (fun w : RWIdx P R => survG C P hR τ w ∧ posG C P hR τ w j = y ∧
    (stepG C P hR τ w j).2.isSome)).image (keyG C P hR τ)

include N hCN in
lemma KgS_step (y : V) {j : ℕ} (hj : j < 2 * ℓ) :
    KgS C P hR τ y j = KgS C P hR τ y (j + 1) ∪ rcvCG C P hR τ y j := by
  classical
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  ext z
  simp only [mem_union, mem_KgS, rcvCG, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, ⟨hs, j', h1, h2, hw⟩, rfl⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rcases stepG_cases hC w j with h | ⟨e, h, -⟩
      · left
        refine ⟨w, ⟨hs, j + 1, by omega, by omega, ?_⟩, rfl⟩
        rw [posG_succ w hj, h]; exact hw
      · right
        exact ⟨w, ⟨hs, hw, by rw [h]; rfl⟩, rfl⟩
    · left; exact ⟨w, ⟨hs, j', by omega, h2, hw⟩, rfl⟩
  · rintro (⟨w, ⟨hs, j', h1, h2, hw⟩, rfl⟩ | ⟨w, ⟨hs, hw, -⟩, rfl⟩)
    · exact ⟨w, ⟨hs, j', by omega, h2, hw⟩, rfl⟩
    · exact ⟨w, ⟨hs, j, le_rfl, by omega, hw⟩, rfl⟩

include N hCN hP hD hpos hov in
/-- **The reports known** after the reversed steps down to `j = 2ℓ - r`. -/
theorem known_eq : ∀ r ≤ 2 * ℓ, ∀ y,
    known (envG C P R t τ y) (fullO C P R t τ y) r = KgS C P hR τ y (2 * ℓ - r) := by
  classical
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  have hheld := held_eq R N hCN hP hD hpos t hov
  intro r
  induction r with
  | zero =>
    intro _ y
    simp only [known, envG_ℓ, Nat.sub_zero]
    rw [hheld _ le_rfl y, finRep_heldG hD hpos t y]
  | succ r ih =>
    intro hr y
    simp only [known, envG_ℓ]
    set j := 2 * ℓ - 1 - r with hjdef
    have hj : j < 2 * ℓ := by omega
    rw [ih (by omega) y, show 2 * ℓ - r = j + 1 by omega, show 2 * ℓ - (r + 1) = j by omega,
      KgS_step N hCN y hj]
    congr 1
    ext z
    unfold rcvC
    simp only [mem_biUnion, mem_range, mem_univ, true_and, Option.mem_toFinset, Option.mem_def,
      envG_R, envG_t, envG_ℓ, rcvCG, mem_image, mem_filter]
    have hcs : ∀ u k, k < t → (fullO C P R t τ y (cAt R t ℓ j k) u).bind parseRep =
        ((crossTo (envG C P R t τ y) (heldG C P hR τ y j) j u).toList[k]?).bind
          (fun z => (lookup (KgS C P hR τ u (j + 1)) z.1 z.2.1).map (fun q => (z.1, z.2.1, q))) := by
      intro u k hk
      simp only [fullO]
      rw [schedG_C C P R t τ hj hk, cSend]
      simp only [envG_ℓ, envG_R, envG_t]
      rw [show 2 * ℓ - 1 - j = r by omega, ih (by omega) u, show 2 * ℓ - r = j + 1 by omega]
      simp only [fullO]
      rw [schedG_B C P R t τ hj hk, bSend, hheld j (by omega) y, repFor_map]
    constructor
    · rintro ⟨k, hk, u, hz⟩
      rw [hcs u k hk] at hz
      obtain ⟨z0, hz0, hz⟩ := Option.bind_eq_some_iff.1 hz
      have hz0' := (exists_toList _ t (card_crossTo_le hC hD hpos t hov y u hj) z0).1 ⟨k, hk, hz0⟩
      rw [mem_crossTo_heldG t hj] at hz0'
      obtain ⟨w, e, hw, hst, rfl⟩ := hz0'
      dsimp only at hz
      rw [lookup_KgS] at hz
      by_cases hc : survG C P hR τ w ∧
          ∃ j', j + 1 ≤ j' ∧ j' ≤ 2 * ℓ ∧ posG C P hR τ w j' = u
      · rw [if_pos hc] at hz
        simp only [Option.map_some, Option.some.injEq] at hz
        exact ⟨w, ⟨hc.1, hw, by simp [hst]⟩, hz⟩
      · rw [if_neg hc] at hz; simp at hz
    · rintro ⟨w, ⟨hs, hw, hcr⟩, rfl⟩
      rcases stepG_cases hC w j with h | ⟨e, h, -⟩
      · rw [h] at hcr; simp at hcr
      · set u := otherEnd e (posG C P hR τ w j)
        have hz0 : (w.1.1, w.2.val, cntG C P hR τ w j + 1, e) ∈
            crossTo (envG C P R t τ y) (heldG C P hR τ y j) j u :=
          (mem_crossTo_heldG t hj).2 ⟨w, e, hw, h, rfl⟩
        obtain ⟨k, hk, hkz⟩ :=
          (exists_toList _ t (card_crossTo_le hC hD hpos t hov y u hj) _).2 hz0
        refine ⟨k, hk, u, ?_⟩
        rw [hcs u k hk, hkz, Option.bind_some]
        dsimp only
        rw [lookup_KgS, if_pos (by exact ⟨hs, j + 1, by omega, by omega,
          by rw [posG_succ w hj, h]⟩)]
        rfl

/-- The reports received in phase D: the surviving walks starting at `y`. -/
noncomputable def rcvDG (C : Finset (Sym2 V)) (P : Finset (Port V)) {R Rmax ℓ Dmax : ℕ}
    (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) (y : V) : Finset (Rep V) := by
  classical exact
    (univ.filter (fun w : RWIdx P R => survG C P hR τ w ∧ w.1.1.1 = y)).image (keyG C P hR τ)

include N hCN hP hD hpos hov in
/-- **All reports known at the end**: those of the surviving walks visiting the node. -/
theorem knownF_eq (y : V) :
    knownF (envG C P R t τ y) (fullO C P R t τ y) = KfinG C P hR τ y := by
  classical
  have hknown := known_eq N hCN hP hD hpos t hov
  unfold knownF
  simp only [envG_ℓ]
  rw [hknown _ le_rfl y, Nat.sub_self]
  have hD' : rcvD (envG C P R t τ y) (fullO C P R t τ y) = rcvDG C P hR τ y := by
    ext z
    unfold rcvD
    simp only [mem_biUnion, mem_range, mem_univ, true_and, Option.mem_toFinset, Option.mem_def,
      envG_R, envG_t, envG_ℓ, rcvDG, mem_image, mem_filter]
    have hds : ∀ u i, i < R → (fullO C P R t τ y (dRnd R t ℓ i) u).bind parseRep =
        (if h : ∃ p ∈ P, p.1 = y ∧ otherEnd p.2 y = u then
          (lookup (KgS C P hR τ u 0) h.choose i).map (fun q => (h.choose, i, q)) else none) := by
      intro u i hi
      simp only [fullO]
      rw [schedG_D C P R t τ hi, dSend]
      simp only [envG_ℓ]
      rw [hknown _ le_rfl u, Nat.sub_self]
      simp only [fullO]
      rw [schedG_A C P R t τ hi, aSend_eq hP]
      split_ifs with h
      · rw [show some (tokMsg (h.choose, i, 0, h.choose.2)) =
          (some (h.choose, i, 0, h.choose.2)).map tokMsg from rfl, repFor_map]
        rfl
      · rfl
    constructor
    · rintro ⟨i, hi, u, hz⟩
      rw [hds u i hi] at hz
      by_cases h : ∃ p ∈ P, p.1 = y ∧ otherEnd p.2 y = u
      · rw [dif_pos h] at hz
        obtain ⟨hp, h1, h2⟩ := h.choose_spec
        obtain ⟨w, hw⟩ : ∃ w : RWIdx P R, w = (⟨h.choose, hp⟩, ⟨i, hi⟩) := ⟨_, rfl⟩
        have hw1 : h.choose = w.1.1 := by rw [hw]
        have hw2 : i = w.2.val := by rw [hw]
        rw [hw1, hw2, lookup_KgS] at hz
        by_cases hc : survG C P hR τ w ∧ ∃ j', 0 ≤ j' ∧ j' ≤ 2 * ℓ ∧ posG C P hR τ w j' = u
        · rw [if_pos hc] at hz
          simp only [Option.map_some, Option.some.injEq] at hz
          exact ⟨w, ⟨hc.1, by rw [← hw1]; exact h1⟩, hz⟩
        · rw [if_neg hc] at hz; simp at hz
      · rw [dif_neg h] at hz; simp at hz
    · rintro ⟨w, ⟨hs, hw⟩, rfl⟩
      refine ⟨w.2.val, w.2.2, otherEnd w.1.1.2 y, ?_⟩
      rw [hds _ _ w.2.2]
      have hex : ∃ p ∈ P, p.1 = y ∧ otherEnd p.2 y = otherEnd w.1.1.2 y := ⟨w.1.1, w.1.2, hw, rfl⟩
      rw [dif_pos hex]
      obtain ⟨hp, h1, h2⟩ := hex.choose_spec
      have he : hex.choose = w.1.1 := port_unique hP hp w.1.2 (by rw [h1, hw])
        (by rw [h1, h2, hw])
      rw [he, lookup_KgS, if_pos (by exact ⟨hs, 0, le_rfl, by omega, by rw [posG_zero, hw]⟩)]
      rfl
  rw [hD']
  ext z
  simp only [mem_union, mem_KgS, mem_KfinG, rcvDG, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨w, ⟨hs, j', -, h2, hw⟩, rfl⟩ | ⟨w, ⟨hs, hw⟩, rfl⟩)
    · exact ⟨w, ⟨hs, Or.inr ⟨j', h2, hw⟩⟩, rfl⟩
    · exact ⟨w, ⟨hs, Or.inl hw⟩, rfl⟩
  · rintro ⟨w, ⟨hs, hw | ⟨j, hj, hw⟩⟩, rfl⟩
    · exact Or.inr ⟨w, ⟨hs, hw⟩, rfl⟩
    · exact Or.inl ⟨w, ⟨hs, j, Nat.zero_le _, hj, hw⟩, rfl⟩

end Known

end APSP.Stoc.Congest
