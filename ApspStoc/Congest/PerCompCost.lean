import ApspStoc.Congest.PerCompCtl

/-!
# The costs of the schedule (for `perCompR`)

* `sum_ML_le`: the messages of `ML` over a set of directed pairs `Pr` are at most the token moves
  over `Pr` plus, for every phase, its broadcasts over `Pr` and the hops of its packets over `Pr`
  (`ph_count`: a broadcast is identified by its receiver, a packet hop by its source, cluster and
  hop index).
* `TL_le`: the halting frame is at most `1 + 2|P| + Σ_ℓ (3Π_ℓ + ⌈tB ℓ / 3⌉) + 3Π`.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the hops of the packets of the sources `Q` whose edge satisfies `Pr` -/
noncomputable def hops (E : Overlays V) (j D : ℕ) (Q : Finset V) (Pr : V × V → Prop) :
    Finset (V × Finset (Sym2 V) × ℕ) := by
  classical exact (Q ×ˢ E.cl ×ˢ range D).filter (fun t => t.2.1 ∈ clustersOf E.cl t.1 ∧
    t.2.2 < (E.path j t.1 t.2.1).length ∧
    Pr (vtx (E.path j t.1 t.2.1) t.1 t.2.2, vtx (E.path j t.1 t.2.1) t.1 (t.2.2 + 1)))

lemma sum_card_eq_card_prod {α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β)
    (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    ∑ a ∈ s, (t.filter (P a)).card = ((s ×ˢ t).filter (fun x => P x.1 x.2)).card := by
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun a _ => ?_)
  rw [card_filter]

/-- **The messages of a phase.** -/
lemma ph_count {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V} {j dil : ℕ}
    (hE : EmbValid G E) (hj : j < Fintype.card V) {Y : GPh V} (hY : GOK G dil Y)
    (Pr : V × V → Prop) [DecidablePred Pr] (T : ℕ) :
    ∑ φ ∈ range T, (univ.filter (fun uw : V × V => (phMsg E j dil Y uw.1 uw.2 φ).isSome ∧
      Pr uw)).card ≤
      (Y.Q.filter (fun w => ∃ u, Y.par w = some u ∧ Pr (u, w))).card + (hops E j dil Y.Q Pr).card := by
  classical
  rw [sum_card_eq_card_prod]
  set Ev := (range T ×ˢ (univ : Finset (V × V))).filter
    (fun x => (phMsg E j dil Y x.2.1 x.2.2 x.1).isSome ∧ Pr x.2) with hEv
  have hsplit : Ev ⊆ Ev.filter (fun x => x.1 < Y.A0 + Y.L) ∪
      Ev.filter (fun x => ¬ (x.1 < Y.A0 + Y.L)) := by
    intro x hx
    by_cases h : x.1 < Y.A0 + Y.L
    · exact mem_union.2 (Or.inl (mem_filter.2 ⟨hx, h⟩))
    · exact mem_union.2 (Or.inr (mem_filter.2 ⟨hx, h⟩))
  refine (card_le_card hsplit).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
  · -- broadcasts: identified by the receiver
    refine card_le_card_of_injOn (fun x => x.2.2) ?_ ?_
    · intro x hx
      simp only [coe_filter, Set.mem_setOf_eq, hEv, mem_filter, mem_product, mem_range,
        mem_univ, and_true] at hx
      obtain ⟨⟨-, hs, hPr⟩, hlt⟩ := hx
      obtain ⟨h1, -, hb⟩ := phMsg_some E j dil Y hs
      rcases hb with ⟨-, -, hw, hp⟩ | ⟨hp, -⟩
      · simp only [coe_filter, Set.mem_setOf_eq]
        exact ⟨hw, x.2.1, hp, hPr⟩
      · exfalso; have := PiL_ge dil Y.L; omega
    · intro x hx x' hx' hxx
      simp only [coe_filter, Set.mem_setOf_eq, hEv, mem_filter, mem_product, mem_range,
        mem_univ, and_true] at hx hx'
      obtain ⟨⟨-, hs, -⟩, hlt⟩ := hx
      obtain ⟨⟨-, hs', -⟩, hlt'⟩ := hx'
      obtain ⟨h1, -⟩ := phMsg_some E j dil Y hs
      obtain ⟨h1', -⟩ := phMsg_some E j dil Y hs'
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 hs'
      rw [phMsg_bc_win E j dil Y h1 hlt] at hm
      rw [phMsg_bc_win E j dil Y h1' hlt'] at hm'
      split_ifs at hm with hc
      split_ifs at hm' with hc'
      simp only at hxx
      rw [hxx] at hc
      have hu : x.2.1 = x'.2.1 := by
        rw [hc.2.2.1] at hc'; exact Option.some.inj hc'.2.2.1
      have hφ : x.1 = x'.1 := by
        have := hc.2.2.2; have := hc'.2.2.2; rw [hu] at hc; omega
      exact Prod.ext hφ (Prod.ext hu hxx)
  · -- packets: identified by source, cluster and hop
    let src : ℕ × V × V → V := fun x =>
      (pk E j Y.Q ((x.1 - Y.A0 - PiL dil Y.L) / Y.L) x.2.1 x.2.2).toList.getD
        ((x.1 - Y.A0 - PiL dil Y.L) % Y.L) x.2.1
    have hsrc : ∀ x ∈ Ev.filter (fun x => ¬ (x.1 < Y.A0 + Y.L)),
        src x ∈ pk E j Y.Q ((x.1 - Y.A0 - PiL dil Y.L) / Y.L) x.2.1 x.2.2 ∧
        (pk E j Y.Q ((x.1 - Y.A0 - PiL dil Y.L) / Y.L) x.2.1 x.2.2).toList[(x.1 - Y.A0 -
          PiL dil Y.L) % Y.L]? = some (src x) ∧
        Y.A0 + PiL dil Y.L ≤ x.1 ∧ x.1 < Y.A0 + PiL dil Y.L + dil * Y.L := by
      intro x hx
      simp only [hEv, mem_filter, mem_product, mem_range, mem_univ, and_true] at hx
      obtain ⟨⟨-, hs, -⟩, hlt⟩ := hx
      obtain ⟨h1, h2, hb⟩ := phMsg_some E j dil Y hs
      rcases hb with ⟨hlt', -⟩ | ⟨hp, -⟩
      · exact absurd hlt' hlt
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hs
      rw [phMsg_pk_win E j dil Y (by have := PiL_ge dil Y.L; omega) hp h2 hY.L1] at hm
      obtain ⟨y, hy, -⟩ := slotMsg_eq hm
      have hsy : src x = y := by
        simp only [src]; rw [List.getD_eq_getElem?_getD, hy]; rfl
      rw [hsy]
      exact ⟨Finset.mem_toList.1 (List.mem_of_getElem? hy), hy, hp, h2⟩
    let clu : ℕ × V × V → Finset (Sym2 V) := fun x =>
      if h : ∃ C ∈ clustersOf E.cl (src x), (x.1 - Y.A0 - PiL dil Y.L) / Y.L <
          (E.path j (src x) C).length ∧
          vtx (E.path j (src x) C) (src x) ((x.1 - Y.A0 - PiL dil Y.L) / Y.L) = x.2.1 ∧
          vtx (E.path j (src x) C) (src x) ((x.1 - Y.A0 - PiL dil Y.L) / Y.L + 1) = x.2.2
      then h.choose else ∅
    have hclu : ∀ x ∈ Ev.filter (fun x => ¬ (x.1 < Y.A0 + Y.L)),
        clu x ∈ clustersOf E.cl (src x) ∧ (x.1 - Y.A0 - PiL dil Y.L) / Y.L <
          (E.path j (src x) (clu x)).length ∧
          vtx (E.path j (src x) (clu x)) (src x) ((x.1 - Y.A0 - PiL dil Y.L) / Y.L) = x.2.1 ∧
          vtx (E.path j (src x) (clu x)) (src x) ((x.1 - Y.A0 - PiL dil Y.L) / Y.L + 1) =
            x.2.2 := by
      intro x hx
      have h := (mem_pk.1 (hsrc x hx).1).2
      simp only [clu]
      rw [dif_pos h]
      exact h.choose_spec
    refine card_le_card_of_injOn (fun x => (src x, clu x, (x.1 - Y.A0 - PiL dil Y.L) / Y.L)) ?_ ?_
    · intro x hx
      have hx' := hx
      simp only [coe_filter, Set.mem_setOf_eq] at hx'
      obtain ⟨h1, h2, h3, h4⟩ := hclu x hx
      obtain ⟨-, -, hp, hw⟩ := hsrc x hx
      have hxQ := (mem_pk.1 (hsrc x hx).1).1
      simp only [hEv, mem_filter, mem_product, mem_range, mem_univ, and_true] at hx'
      simp only [hops, coe_filter, Set.mem_setOf_eq, mem_product, mem_range]
      refine ⟨⟨hxQ, (mem_filter.1 h1).1, ?_⟩, h1, h2, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (by have := hY.L1; omega)]; omega
      · rw [h3, h4]; exact hx'.1.2.2
    · intro x hx x' hx' hxx
      simp only [Prod.mk.injEq] at hxx
      obtain ⟨hs, hC, hh⟩ := hxx
      obtain ⟨-, hl1, hp1, hw1⟩ := hsrc x hx
      obtain ⟨-, hl1', hp1', hw1'⟩ := hsrc x' hx'
      obtain ⟨-, -, hu, hw⟩ := hclu x hx
      obtain ⟨-, -, hu', hw'⟩ := hclu x' hx'
      rw [hs, hC, hh] at hu hw
      have huu : x.2.1 = x'.2.1 := hu.symm.trans hu'
      have hww : x.2.2 = x'.2.2 := hw.symm.trans hw'
      -- the slots
      have hnd := Finset.nodup_toList (pk E j Y.Q ((x.1 - Y.A0 - PiL dil Y.L) / Y.L) x.2.1 x.2.2)
      rw [huu, hww, hh] at hl1
      have hslot := List.nodup_iff_injective_getElem.1 (Finset.nodup_toList
        (pk E j Y.Q ((x'.1 - Y.A0 - PiL dil Y.L) / Y.L) x'.2.1 x'.2.2))
      obtain ⟨i1, he1⟩ := List.getElem?_eq_some_iff.1 hl1
      obtain ⟨i2, he2⟩ := List.getElem?_eq_some_iff.1 hl1'
      have : (x.1 - Y.A0 - PiL dil Y.L) % Y.L = (x'.1 - Y.A0 - PiL dil Y.L) % Y.L := by
        have := hslot (a₁ := ⟨_, i1⟩) (a₂ := ⟨_, i2⟩) (by simp only; rw [he1, he2, hs])
        exact congrArg Fin.val this
      have hφ : x.1 = x'.1 := by
        have e1 := Nat.div_add_mod (x.1 - Y.A0 - PiL dil Y.L) Y.L
        have e2 := Nat.div_add_mod (x'.1 - Y.A0 - PiL dil Y.L) Y.L
        rw [hh, this] at e1
        omega
      exact Prod.ext hφ (Prod.ext huu hww)

lemma card_hops_le {E : Overlays V} {j D : ℕ} (Q : Finset V) (Pr : V × V → Prop)
    [DecidablePred Pr] :
    (hops E j D Q Pr).card ≤ ∑ x ∈ Q, ∑ C ∈ clustersOf E.cl x,
      ((range (E.path j x C).length).filter (fun h =>
        Pr (vtx (E.path j x C) x h, vtx (E.path j x C) x (h + 1)))).card := by
  classical
  unfold hops
  calc _ ≤ ((Q.sigma (fun x => clustersOf E.cl x)).sigma
        (fun t => (range (E.path j t.1 t.2).length).filter (fun h =>
          Pr (vtx (E.path j t.1 t.2) t.1 h, vtx (E.path j t.1 t.2) t.1 (h + 1))))).card := by
        refine card_le_card_of_injOn (fun t => ⟨⟨t.1, t.2.1⟩, t.2.2⟩) ?_ ?_
        · intro t ht
          simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range] at ht
          simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_range]
          exact ⟨⟨ht.1.1, ht.2.1⟩, ht.2.2.1, ht.2.2.2⟩
        · intro t _ t' _ h
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
          obtain ⟨⟨h1, h2⟩, h3⟩ := h
          exact Prod.ext h1 (Prod.ext h2 h3)
    _ = _ := by rw [card_sigma, sum_sigma]

lemma card_idx_count : ∀ (l : List (Sym2 V)) (e : Sym2 V),
    ((range l.length).filter (fun h => l[h]? = some e)).card = l.count e
  | [], e => by simp
  | x :: l, e => by
    have ih := card_idx_count l e
    rw [card_filter] at ih ⊢
    rw [List.length_cons, sum_range_succ', List.count_cons, ← ih]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    by_cases hx : x = e
    · simp [hx]
    · simp [hx]

lemma card_range_filter_count (l : List (Sym2 V)) (a : V) (e : Sym2 V)
    (hw : ∃ b, IsEdgeWalk l a b) :
    ((range l.length).filter (fun h => s(vtx l a h, vtx l a (h + 1)) = e)).card = l.count e := by
  classical
  obtain ⟨b, hw⟩ := hw
  rw [← card_idx_count l e]
  congr 1
  apply filter_congr
  intro h hh
  rw [mem_range] at hh
  rw [← walk_getElem l a b hw h hh, List.getElem?_eq_getElem hh, Option.some.injEq]

end APSP.Stoc.Congest
