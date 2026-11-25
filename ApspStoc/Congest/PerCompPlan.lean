import ApspStoc.Congest.PerCompCost

/-!
# The plan of the traversal and its costs (for `perCompR`)

The schedule uses only edges of the instance (`ML_adj`) and valid words (`ML_ok`); the sub-runs
of distinct components are separated (`sub_sep`); the halting frame (`TL_le`), the number of
messages (`msgs_le`) and the load of every edge (`load_le`) of the controllers are within the
overhead budget.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

namespace PCG

variable {X : PCG V} (hX : X.OK)
include hX

lemma ph_Q_sub {Y : GPh V} (hY : IsPh X Y) : Y.Q ⊆ X.P := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · exact comp_sub_P hX ℓ
  · exact subset_rfl

/-- **Only edges of the instance.** -/
lemma ML_adj {u w : V} {φ : ℕ} (h : (X.ML u w φ).isSome) :
    X.N.G.Adj u w ∧ u ∈ footprint X.E X.j X.P ∧ w ∈ footprint X.E X.j X.P := by
  rcases ML_shape hX u w φ with h' | h' | ⟨cc, h'⟩ | ⟨x, cc, l, h'⟩
  · rw [h'] at h; simp at h
  · obtain ⟨k, hk, hk', -⟩ := (ML_tokW hX).1 h'
    rcases (tk_mem_tl hX).1 (hk' ▸ List.getElem_mem hk) with ⟨hwP, hp⟩ | ⟨huP, hp⟩
    · exact ⟨(hX.Padj w hwP u hp).symm, subset_footprint _ _ _ (hX.Pmem w hwP u hp),
        subset_footprint _ _ _ hwP⟩
    · exact ⟨hX.Padj u huP w hp, subset_footprint _ _ _ huP,
        subset_footprint _ _ _ (hX.Pmem u huP w hp)⟩
  · obtain ⟨Y, hY, -, -, huQ, hwQ, hp, -, -⟩ := (ML_bcW hX).1 h'
    have hg := isPh_gok hX hY
    exact ⟨(hg.adj w hwQ u hp).symm, subset_footprint _ _ _ (ph_Q_sub hX hY huQ),
      subset_footprint _ _ _ (ph_Q_sub hX hY hwQ)⟩
  · obtain ⟨Y, hY, -, -, hx, -, -⟩ := (ML_pkW hX).1 h'
    have hxpk := Finset.mem_toList.1 (List.mem_of_getElem? hx)
    have hfp := pk_fp hX.hE hX.hj hxpk
    exact ⟨pk_adj hX.hE hX.hj hxpk, footprint_mono _ _ (ph_Q_sub hX hY) hfp.1,
      footprint_mono _ _ (ph_Q_sub hX hY) hfp.2⟩

/-- **Valid words.** -/
lemma ML_ok {u w : V} {φ : ℕ} {m : W3 V} (h : X.ML u w φ = some m) :
    WordOK (Fintype.card V) m.1 ∧ WordOK (Fintype.card V) m.2.1 ∧
      WordOK (Fintype.card V) m.2.2 := by
  have hP : X.P.card ≤ Fintype.card V := card_le_univ _
  rcases ML_shape hX u w φ with h' | h' | ⟨cc, h'⟩ | ⟨x, cc, l, h'⟩ <;> rw [h'] at h <;> cases h
  · simp [tokW, WordOK]
  · obtain ⟨Y, hY, -, -, -, -, -, -, rfl⟩ := (ML_bcW hX).1 h'
    have : Y.c ≤ X.P.card := by
      rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
      · exact card_le_card (comp_sub_P hX ℓ)
      · simp [ePh]
    simp only [bcW, WordOK]; omega
  · obtain ⟨Y, hY, -, -, -, rfl, -⟩ := (ML_pkW hX).1 h'
    have : Y.c ≤ X.P.card := by
      rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
      · exact card_le_card (comp_sub_P hX ℓ)
      · simp [ePh]
    simp only [pcPkW, WordOK, true_and, and_true]; omega

lemma bOf_lt_end {ℓ : V} (hℓ : ℓ ∈ X.lds) :
    X.aOf ℓ < X.bOf ℓ ∧ 3 * X.bOf ℓ + X.tB ℓ ≤ 3 * X.phEnd ℓ (X.aOf ℓ) := by
  have := aOf_le_A0 hX hℓ
  have := PiK_pos hX hℓ
  rw [phEnd_eq]
  unfold bOf
  constructor
  · show X.aOf ℓ < (X.kPh ℓ).A0 + 2 * X.PiK ℓ; omega
  · omega

/-- **The sub-runs of distinct components are separated.** -/
lemma sub_sep {ℓ ℓ' : V} (hℓ : ℓ ∈ X.lds) (hℓ' : ℓ' ∈ X.lds) (hne : ℓ ≠ ℓ') :
    3 * X.bOf ℓ + X.tB ℓ < 3 * X.bOf ℓ' ∨ 3 * X.bOf ℓ' + X.tB ℓ' < 3 * X.bOf ℓ := by
  obtain ⟨i, hi, h⟩ := exists_ph hX hℓ
  obtain ⟨i', hi', h'⟩ := exists_ph hX hℓ'
  have hii : i ≠ i' := by
    rintro rfl; rw [h] at h'; cases h'; exact hne rfl
  have e1 := stF_ph hX hi h
  have e2 := stF_ph hX hi' h'
  have a1 := aOf_eq hX hi h
  have a2 := aOf_eq hX hi' h'
  have b1 := bOf_lt_end hX hℓ
  have b2 := bOf_lt_end hX hℓ'
  rcases Nat.lt_or_gt_of_ne hii with hlt | hlt
  · left
    have := stF_le hX (show i + 1 ≤ i' by omega) hi'.le
    omega
  · right
    have := stF_le hX (show i' + 1 ≤ i by omega) hi.le
    omega

lemma phEnd_le_TL {ℓ : V} (hℓ : ℓ ∈ X.lds) : X.phEnd ℓ (X.aOf ℓ) ≤ X.TL := by
  obtain ⟨i, hi, h⟩ := exists_ph hX hℓ
  rw [← stF_ph hX hi h]
  have := stF_le hX (show i + 1 ≤ X.tl.length by omega) le_rfl
  have := E0_le_A0 hX
  unfold TL E0 at *
  omega

lemma bOf_pos {ℓ : V} (hℓ : ℓ ∈ X.lds) : 1 ≤ X.bOf ℓ := by
  have := (bOf_lt_end hX hℓ).1
  omega

/-! ## The halting frame -/

lemma stF_sum : ∀ k ≤ X.tl.length,
    X.stF k = 1 + ∑ i ∈ range k, X.dur (X.tl.getD i (.ph X.r)) (X.stF i) := by
  intro k
  induction k with
  | zero => intro _; rw [stF_zero]; simp
  | succ k ih =>
    intro hk
    rw [stF_succ (X := X) (i := k) (by omega), sum_range_succ,
      List.getD_eq_getElem _ _ (show k < X.tl.length by omega), ih (by omega)]
    ring

/-- the bound on the duration of a segment -/
noncomputable def gd (X : PCG V) : TSg V → ℕ
  | .tk _ _ => 1
  | .ph ℓ => 3 * X.PiK ℓ + (X.tB ℓ + 2) / 3

lemma dur_le_gd {i : ℕ} (hi : i < X.tl.length) (a : ℕ) : X.dur X.tl[i] a ≤ gd X X.tl[i] := by
  cases h : X.tl[i] with
  | tk u w => simp [dur, gd]
  | ph ℓ =>
    have hℓ : ℓ ∈ X.lds := (ph_mem_tl hX).1 (h ▸ List.getElem_mem hi)
    simp only [dur, gd, phEnd]
    have := alignUp_lt a (PiK_pos hX hℓ)
    omega

lemma S_biUnion : X.lds.biUnion X.comp = X.S := by
  ext v
  simp only [mem_biUnion]
  constructor
  · rintro ⟨ℓ, -, hv⟩; exact (mem_comp.1 hv).1
  · intro hv; exact ⟨X.rtS v, (rtS_lds hX hv).1, (rtS_lds hX hv).2⟩

lemma comp_pdisj : (X.lds : Set V).PairwiseDisjoint X.comp :=
  fun ℓ _ ℓ' _ hne => comp_disj hX hne

lemma sum_comp_card : ∑ ℓ ∈ X.lds, (X.comp ℓ).card = X.S.card := by
  rw [← card_biUnion (comp_pdisj hX), S_biUnion hX]

/-- the token moves of the traversal -/
lemma card_tk : ((range X.tl.length).filter (fun i => ∃ u w, X.tl.getD i (.ph X.r) = .tk u w)).card
    ≤ 2 * X.P.card := by
  classical
  refine le_trans ?_ (card_treePairs X.P X.parP)
  refine card_le_card_of_injOn (fun i => match X.tl.getD i (.ph X.r) with
    | .tk u w => (u, w) | .ph _ => (X.r, X.r)) ?_ ?_
  · intro i hi
    simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hi
    obtain ⟨hi, u, w, huw⟩ := hi
    rw [List.getD_eq_getElem _ _ hi] at huw
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
    rw [List.getD_eq_getElem _ _ hi, huw]
    rcases (tk_mem_tl hX).1 (huw ▸ List.getElem_mem hi) with h | h
    · right; exact h
    · left; exact h
  · intro i hi i' hi' hii
    simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hi hi'
    obtain ⟨hi, u, w, huw⟩ := hi
    obtain ⟨hi', u', w', huw'⟩ := hi'
    simp only [huw, huw'] at hii
    rw [List.getD_eq_getElem _ _ hi] at huw
    rw [List.getD_eq_getElem _ _ hi'] at huw'
    have := List.nodup_iff_injective_getElem.1 (tl_nodup hX)
    simp only [Prod.mk.injEq] at hii
    obtain ⟨rfl, rfl⟩ := hii
    exact congrArg Fin.val (this (a₁ := ⟨i, hi⟩) (a₂ := ⟨i', hi'⟩) (huw.trans huw'.symm))

lemma sum_gd_le : ∑ i ∈ range X.tl.length, gd X (X.tl.getD i (.ph X.r)) ≤
    2 * X.P.card + ∑ ℓ ∈ X.lds, (3 * X.PiK ℓ + (X.tB ℓ + 2) / 3) := by
  classical
  have hsplit : ∑ i ∈ range X.tl.length, gd X (X.tl.getD i (.ph X.r)) =
      ∑ i ∈ (range X.tl.length).filter (fun i => ∃ u w, X.tl.getD i (.ph X.r) = .tk u w),
        gd X (X.tl.getD i (.ph X.r)) +
      ∑ i ∈ (range X.tl.length).filter (fun i => ¬ ∃ u w, X.tl.getD i (.ph X.r) = .tk u w),
        gd X (X.tl.getD i (.ph X.r)) := (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  refine Nat.add_le_add ?_ ?_
  · refine le_trans (le_of_eq ?_) (card_tk hX)
    rw [card_eq_sum_ones]
    refine sum_congr rfl (fun i hi => ?_)
    obtain ⟨-, u, w, h⟩ := mem_filter.1 hi
    rw [h]; rfl
  · -- the phases: one per leader
    calc _ = ∑ i ∈ (range X.tl.length).filter (fun i => ¬ ∃ u w, X.tl.getD i (.ph X.r) = .tk u w),
          gd X (TSg.ph (match X.tl.getD i (.ph X.r) with | .ph ℓ => ℓ | .tk _ _ => X.r)) := by
          refine sum_congr rfl (fun i hi => ?_)
          obtain ⟨-, hno⟩ := mem_filter.1 hi
          cases h : X.tl.getD i (.ph X.r) with
          | tk u w => exact absurd ⟨u, w, h⟩ hno
          | ph ℓ => rfl
      _ ≤ ∑ ℓ ∈ X.lds, gd X (TSg.ph ℓ) := by
          rw [← sum_image (s := (range X.tl.length).filter
            (fun i => ¬ ∃ u w, X.tl.getD i (.ph X.r) = .tk u w))
            (g := fun i => match X.tl.getD i (.ph X.r) with | .ph ℓ => ℓ | .tk _ _ => X.r)
            (f := fun ℓ => gd X (TSg.ph ℓ))]
          · refine sum_le_sum_of_subset (fun ℓ hℓ => ?_)
            obtain ⟨i, hi, rfl⟩ := mem_image.1 hℓ
            obtain ⟨hi, hno⟩ := mem_filter.1 hi
            rw [mem_range] at hi
            rw [List.getD_eq_getElem _ _ hi] at hno ⊢
            cases h : X.tl[i] with
            | tk u w => exact absurd ⟨u, w, h⟩ hno
            | ph ℓ => exact (ph_mem_tl hX).1 (h ▸ List.getElem_mem hi)
          · intro i hi i' hi' hii
            simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hi hi'
            obtain ⟨hi, hno⟩ := hi
            obtain ⟨hi', hno'⟩ := hi'
            simp only at hii
            rw [List.getD_eq_getElem _ _ hi] at hno hii
            rw [List.getD_eq_getElem _ _ hi'] at hno' hii
            have := List.nodup_iff_injective_getElem.1 (tl_nodup hX)
            refine congrArg Fin.val (this (a₁ := ⟨i, hi⟩) (a₂ := ⟨i', hi'⟩) ?_)
            simp only
            cases h : X.tl[i] with
            | tk u w => exact absurd ⟨u, w, h⟩ hno
            | ph ℓ =>
              cases h' : X.tl[i'] with
              | tk u w => exact absurd ⟨u, w, h'⟩ hno'
              | ph ℓ' => rw [h, h'] at hii; simp only at hii; rw [hii]
      _ = _ := rfl

/-- **The halting frame.** -/
lemma TL_le : X.TL ≤ 1 + 2 * X.P.card + ∑ ℓ ∈ X.lds, (3 * X.PiK ℓ + (X.tB ℓ + 2) / 3) +
    3 * PiL X.dil X.sz := by
  have h1 : X.E0 ≤ 1 + 2 * X.P.card + ∑ ℓ ∈ X.lds, (3 * X.PiK ℓ + (X.tB ℓ + 2) / 3) := by
    unfold E0
    rw [stF_sum hX _ le_rfl]
    have : ∑ i ∈ range X.tl.length, X.dur (X.tl.getD i (.ph X.r)) (X.stF i) ≤
        ∑ i ∈ range X.tl.length, gd X (X.tl.getD i (.ph X.r)) := by
      refine sum_le_sum (fun i hi => ?_)
      rw [mem_range] at hi
      rw [List.getD_eq_getElem _ _ hi]
      exact dur_le_gd hX hi _
    have := sum_gd_le hX
    omega
  have h2 := alignUp_lt X.E0 (PiE_pos hX)
  unfold TL ePh
  simp only at h2 ⊢
  omega

/-! ## Messages and loads of the schedule -/

/-- the counted messages of a phase -/
noncomputable def phc (X : PCG V) (Y : GPh V) (Pr : V × V → Prop) [DecidablePred Pr] : ℕ := by
  classical exact (Y.Q.filter (fun w => ∃ u, Y.par w = some u ∧ Pr (u, w))).card +
    (hops X.E X.j X.dil Y.Q Pr).card

lemma sum_ML_le (Pr : V × V → Prop) [DecidablePred Pr] (T : ℕ) :
    ∑ φ ∈ range T, (univ.filter (fun uw : V × V => (X.ML uw.1 uw.2 φ).isSome ∧ Pr uw)).card ≤
      ((range X.tl.length).filter (fun k => ∃ u w, X.tl.getD k (.ph X.r) = .tk u w ∧
        Pr (u, w))).card + ∑ ℓ ∈ X.lds, phc X (X.kPh ℓ) Pr + phc X X.ePh Pr := by
  classical
  set Tk : ℕ → Finset (V × V) := fun φ => univ.filter (fun uw : V × V =>
    (∃ k, ∃ _ : k < X.tl.length, X.tl[k]? = some (.tk uw.1 uw.2) ∧ X.stF k = φ) ∧ Pr uw) with hTk
  set Ph : GPh V → ℕ → Finset (V × V) := fun Y φ => univ.filter (fun uw : V × V =>
    (phMsg X.E X.j X.dil Y uw.1 uw.2 φ).isSome ∧ Pr uw) with hPh
  have hsub : ∀ φ, univ.filter (fun uw : V × V => (X.ML uw.1 uw.2 φ).isSome ∧ Pr uw) ⊆
      Tk φ ∪ (X.lds.biUnion (fun ℓ => Ph (X.kPh ℓ) φ) ∪ Ph X.ePh φ) := by
    intro φ uw huw
    rw [mem_filter] at huw
    obtain ⟨hs, hPr⟩ := huw.2
    obtain ⟨h1, h2⟩ := ML_TL hX hs
    rcases frame_cases hX h1 h2 with ⟨k, hk, a, b, hab, rfl⟩ | ⟨Y, hY, hw1, hw2⟩
    · rw [ML_tok hX hk hab] at hs
      split_ifs at hs with h
      · obtain ⟨h3, h4⟩ := h
        refine mem_union_left _ (mem_filter.2 ⟨mem_univ _, ⟨k, hk, ?_, rfl⟩, hPr⟩)
        rw [List.getElem?_eq_getElem hk, hab, h3, h4]
      · simp at hs
    · rw [ML_win hX hY hw1 hw2] at hs
      refine mem_union_right _ ?_
      rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
      · exact mem_union_left _ (mem_biUnion.2 ⟨ℓ, hℓ, mem_filter.2 ⟨mem_univ _, hs, hPr⟩⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hs, hPr⟩)
  calc _ ≤ ∑ φ ∈ range T, ((Tk φ).card + (∑ ℓ ∈ X.lds, (Ph (X.kPh ℓ) φ).card +
        (Ph X.ePh φ).card)) := by
        refine sum_le_sum (fun φ _ => (card_le_card (hsub φ)).trans ?_)
        refine (card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
        exact (card_union_le _ _).trans (Nat.add_le_add_right card_biUnion_le _)
    _ = ∑ φ ∈ range T, (Tk φ).card + (∑ ℓ ∈ X.lds, ∑ φ ∈ range T, (Ph (X.kPh ℓ) φ).card +
        ∑ φ ∈ range T, (Ph X.ePh φ).card) := by
        rw [sum_add_distrib, sum_add_distrib, sum_comm]
    _ ≤ _ := by
        rw [add_assoc]
        refine Nat.add_le_add ?_ (Nat.add_le_add (sum_le_sum (fun ℓ hℓ => ?_)) ?_)
        · -- token moves: each counted in its frame
          rw [sum_card_eq_card_prod]
          refine card_le_card_of_injOn (fun x => X.idx x.1) ?_ ?_
          · intro x hx
            simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range, mem_univ,
              and_true, hTk] at hx
            obtain ⟨-, ⟨k, hk, hk', hs⟩, hPr⟩ := hx
            simp only [coe_filter, Set.mem_setOf_eq, mem_range]
            have hkk : X.idx x.1 = k := by
              rw [← hs]
              cases h : X.tl[k] with
              | tk a b => exact idx_eq hX hk le_rfl (by rw [stF_tk hX hk h]; omega)
              | ph ℓ => rw [List.getElem?_eq_getElem hk, h] at hk'; cases hk'
            rw [hkk, List.getD_eq_getElem _ _ hk]
            rw [List.getElem?_eq_getElem hk] at hk'
            exact ⟨hk, x.2.1, x.2.2, Option.some.inj hk', hPr⟩
          · intro x hx x' hx' hxx
            simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range, mem_univ,
              and_true, hTk] at hx hx'
            obtain ⟨-, ⟨k, hk, hk', hs⟩, -⟩ := hx
            obtain ⟨-, ⟨k', hk2, hk2', hs'⟩, -⟩ := hx'
            have i1 : X.idx x.1 = k := by
              rw [← hs]
              cases h : X.tl[k] with
              | tk a b => exact idx_eq hX hk le_rfl (by rw [stF_tk hX hk h]; omega)
              | ph ℓ => rw [List.getElem?_eq_getElem hk, h] at hk'; cases hk'
            have i2 : X.idx x'.1 = k' := by
              rw [← hs']
              cases h : X.tl[k'] with
              | tk a b => exact idx_eq hX hk2 le_rfl (by rw [stF_tk hX hk2 h]; omega)
              | ph ℓ => rw [List.getElem?_eq_getElem hk2, h] at hk2'; cases hk2'
            simp only at hxx
            rw [i1, i2] at hxx
            subst hxx
            rw [hk'] at hk2'
            simp only [Option.some.injEq, TSg.tk.injEq] at hk2'
            exact Prod.ext (hs.symm.trans hs') (Prod.ext hk2'.1 hk2'.2)
        · exact ph_count hX.hE hX.hj (kPh_gok hX hℓ) Pr T
        · exact ph_count hX.hE hX.hj (ePh_gok hX) Pr T

/-- the indicator of the edges of `G` incident to `P` -/
noncomputable def ind (X : PCG V) (e : Sym2 V) : ℕ := by
  classical exact if e ∈ X.N.G.edgeFinset ∧ ∃ v ∈ X.P, v ∈ e then 1 else 0

omit hX in
lemma card_mem_e (e : Sym2 V) : (univ.filter (fun w : V => w ∈ e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    calc _ ≤ ({a, b} : Finset V).card := card_le_card (fun w hw => by
            simp only [mem_filter, mem_univ, true_and, Sym2.mem_iff] at hw
            rcases hw with rfl | rfl <;> simp)
      _ ≤ 2 := card_le_two

lemma tok_load (e : Sym2 V) :
    ((range X.tl.length).filter (fun k => ∃ u w, X.tl.getD k (.ph X.r) = .tk u w ∧
      s(u, w) = e)).card ≤ 2 * ind X e := by
  classical
  by_cases hi : e ∈ X.N.G.edgeFinset ∧ ∃ v ∈ X.P, v ∈ e
  · unfold ind; rw [if_pos hi, mul_one]
    refine le_trans ?_ (card_sym2_fiber e)
    refine card_le_card_of_injOn (fun k => match X.tl.getD k (.ph X.r) with
      | .tk u w => (u, w) | .ph _ => (X.r, X.r)) ?_ ?_
    · intro k hk
      simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hk
      obtain ⟨-, u, w, huw, he⟩ := hk
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and, huw]
      exact he
    · intro k hk k' hk' hkk
      simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hk hk'
      obtain ⟨hk, u, w, huw, -⟩ := hk
      obtain ⟨hk', u', w', huw', -⟩ := hk'
      simp only [huw, huw', Prod.mk.injEq] at hkk
      obtain ⟨rfl, rfl⟩ := hkk
      rw [List.getD_eq_getElem _ _ hk] at huw
      rw [List.getD_eq_getElem _ _ hk'] at huw'
      have := List.nodup_iff_injective_getElem.1 (tl_nodup hX)
      exact congrArg Fin.val (this (a₁ := ⟨k, hk⟩) (a₂ := ⟨k', hk'⟩) (huw.trans huw'.symm))
  · unfold ind; rw [if_neg hi]
    rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    rintro k hk ⟨u, w, huw, rfl⟩
    rw [mem_range] at hk
    rw [List.getD_eq_getElem _ _ hk] at huw
    apply hi
    rcases (tk_mem_tl hX).1 (huw ▸ List.getElem_mem hk) with ⟨hwP, hp⟩ | ⟨huP, hp⟩
    · refine ⟨SimpleGraph.mem_edgeFinset.2 (hX.Padj w hwP u hp).symm, w, hwP, ?_⟩
      exact Sym2.mem_mk_right _ _
    · exact ⟨SimpleGraph.mem_edgeFinset.2 (hX.Padj u huP w hp), u, huP, Sym2.mem_mk_left _ _⟩

lemma bc_load_le {Q : Finset V} (hQ : Q ⊆ X.P) (par : V → Option V)
    (hadj : ∀ w ∈ Q, ∀ u, par w = some u → X.N.G.Adj w u) (e : Sym2 V) :
    (Q.filter (fun w => ∃ u, par w = some u ∧ s(u, w) = e)).card ≤ 2 * ind X e := by
  classical
  by_cases hi : e ∈ X.N.G.edgeFinset ∧ ∃ v ∈ X.P, v ∈ e
  · unfold ind; rw [if_pos hi, mul_one]
    refine le_trans (card_le_card (fun w hw => ?_)) (card_mem_e e)
    obtain ⟨-, u, -, rfl⟩ := mem_filter.1 hw
    simp
  · unfold ind; rw [if_neg hi]
    rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    rintro w hw ⟨u, hu, rfl⟩
    exact hi ⟨SimpleGraph.mem_edgeFinset.2 (hadj w hw u hu).symm, w, hQ hw, Sym2.mem_mk_right _ _⟩

lemma hops_le_aggLen (Q : Finset V) :
    (hops X.E X.j X.dil Q (fun _ => True)).card ≤ X.E.aggLen X.j Q := by
  classical
  refine (card_hops_le Q _).trans (le_of_eq ?_)
  unfold Overlays.aggLen
  refine sum_congr rfl (fun x _ => sum_congr rfl (fun C _ => ?_))
  simp

lemma hops_le_rhoAgg (Q : Finset V) (e : Sym2 V) :
    (hops X.E X.j X.dil Q (fun uw => s(uw.1, uw.2) = e)).card ≤ X.E.rhoAgg X.j Q e := by
  classical
  refine (card_hops_le Q _).trans (le_of_eq ?_)
  unfold Overlays.rhoAgg
  refine sum_congr rfl (fun x _ => sum_congr rfl (fun C hC => ?_))
  exact card_range_filter_count _ _ _ (pc_path_walk hX.hE hX.hj hC)

lemma aggLen_mono {Q Q' : Finset V} (h : Q ⊆ Q') : X.E.aggLen X.j Q ≤ X.E.aggLen X.j Q' := by
  unfold Overlays.aggLen; exact sum_le_sum_of_subset h

lemma rhoAgg_mono {Q Q' : Finset V} (h : Q ⊆ Q') (e : Sym2 V) :
    X.E.rhoAgg X.j Q e ≤ X.E.rhoAgg X.j Q' e := by
  unfold Overlays.rhoAgg; exact sum_le_sum_of_subset h

lemma sum_aggLen : ∑ ℓ ∈ X.lds, X.E.aggLen X.j (X.comp ℓ) = X.E.aggLen X.j X.S := by
  unfold Overlays.aggLen
  rw [← sum_biUnion (comp_pdisj hX), S_biUnion hX]

lemma sum_rhoAgg (e : Sym2 V) : ∑ ℓ ∈ X.lds, X.E.rhoAgg X.j (X.comp ℓ) e = X.E.rhoAgg X.j X.S e := by
  unfold Overlays.rhoAgg
  rw [← sum_biUnion (comp_pdisj hX), S_biUnion hX]

/-- **The messages of the controllers.** -/
lemma msgs_le (T : ℕ) :
    ∑ φ ∈ range T, (univ.filter (fun uw : V × V => (X.ML uw.1 uw.2 φ).isSome ∧ True)).card ≤
      4 * X.P.card + 2 * X.E.aggLen X.j X.P := by
  classical
  refine (sum_ML_le hX (fun _ => True) T).trans ?_
  have h1 : ((range X.tl.length).filter (fun k => ∃ u w, X.tl.getD k (.ph X.r) = .tk u w ∧
      True)).card ≤ 2 * X.P.card := by
    simpa using card_tk hX
  have h2 : ∑ ℓ ∈ X.lds, phc X (X.kPh ℓ) (fun _ => True) ≤ X.S.card + X.E.aggLen X.j X.S := by
    rw [← sum_comp_card hX, ← sum_aggLen hX, ← sum_add_distrib]
    refine sum_le_sum (fun ℓ _ => Nat.add_le_add (card_filter_le _ _) (hops_le_aggLen hX _))
  have h3 : phc X X.ePh (fun _ => True) ≤ X.P.card + X.E.aggLen X.j X.P :=
    Nat.add_le_add (card_filter_le _ _) (hops_le_aggLen hX _)
  have h4 := card_le_card hX.SP
  have h5 := aggLen_mono hX hX.SP
  omega

/-- **The load of the controllers** on an edge. -/
lemma load_le (T : ℕ) (e : Sym2 V) :
    ∑ φ ∈ range T, (univ.filter (fun uw : V × V => (X.ML uw.1 uw.2 φ).isSome ∧
      s(uw.1, uw.2) = e)).card ≤ 6 * X.E.rho X.N.G X.j X.P e := by
  classical
  refine (sum_ML_le hX (fun uw => s(uw.1, uw.2) = e) T).trans ?_
  have h1 := tok_load hX e
  have h2 : ∑ ℓ ∈ X.lds, phc X (X.kPh ℓ) (fun uw => s(uw.1, uw.2) = e) ≤
      2 * ind X e + X.E.rhoAgg X.j X.S e := by
    rw [← sum_rhoAgg hX]
    unfold phc
    rw [sum_add_distrib]
    refine Nat.add_le_add ?_ (sum_le_sum (fun ℓ _ => hops_le_rhoAgg hX _ e))
    show ∑ ℓ ∈ X.lds, ((X.comp ℓ).filter (fun w => ∃ u, X.parS w = some u ∧ s(u, w) = e)).card ≤ _
    rw [← card_biUnion (fun ℓ _ ℓ' _ hne => Finset.disjoint_filter_filter (comp_disj hX hne))]
    refine bc_load_le hX (Q := X.lds.biUnion (fun ℓ => (X.comp ℓ).filter
      (fun w => ∃ u, X.parS w = some u ∧ s(u, w) = e))) ?_ X.parS ?_ e |>.trans' ?_
    · intro w hw
      obtain ⟨ℓ, -, hw⟩ := mem_biUnion.1 hw
      exact comp_sub_P hX ℓ (mem_filter.1 hw).1
    · intro w hw u hu
      obtain ⟨ℓ, -, hw⟩ := mem_biUnion.1 hw
      exact hX.Sadj w (mem_comp.1 (mem_filter.1 hw).1).1 u hu
    · refine le_of_eq (congrArg card ?_)
      ext w
      simp only [mem_filter, mem_biUnion]
      constructor
      · rintro ⟨ℓ, hℓ, hw, h⟩; exact ⟨⟨ℓ, hℓ, hw, h⟩, h⟩
      · rintro ⟨⟨ℓ, hℓ, hw, h⟩, -⟩; exact ⟨ℓ, hℓ, hw, h⟩
  have h3 : phc X X.ePh (fun uw => s(uw.1, uw.2) = e) ≤ 2 * ind X e + X.E.rhoAgg X.j X.P e := by
    unfold phc
    exact Nat.add_le_add (bc_load_le hX subset_rfl X.parP (fun w hw u hu => hX.Padj w hw u hu) e)
      (hops_le_rhoAgg hX _ e)
  have h4 := rhoAgg_mono hX hX.SP e
  have h5 : X.E.rho X.N.G X.j X.P e = ind X e + X.E.rhoAgg X.j X.P e := by
    unfold Overlays.rho ind; rfl
  rw [h5]
  refine le_trans (Nat.add_le_add (Nat.add_le_add h1 h2) h3) ?_
  omega

end PCG

end APSP.Stoc.Congest
