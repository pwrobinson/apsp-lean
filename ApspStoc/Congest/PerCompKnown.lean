import ApspStoc.Congest.PerCompTok

/-!
# The phases known to a node (for `perCompR`)

* `cand_sound`: every phase a node learns in frame `ψ` (`cand`: its own start, a broadcast, a
  packet) is the local view `loc Y v` of the global phase `Y` whose window contains `ψ`, and the
  node is in the footprint of `Y`'s sources.
* `known_Q`, `known_R`, `known_fp`: a source of `Y` knows `Y` after the broadcast window, a node
  that received a packet of `Y` knows `Y`, and every node of the footprint knows `Y` after the
  announcement window.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

lemma orElse_some_cases {α : Type} {a b : Option α} {z : α} (h : (a <|> b) = some z) :
    a = some z ∨ b = some z := by
  cases a with
  | none => right; exact h
  | some a' => left; exact h

lemma orElse_of_some {α : Type} {a b : Option α} {z : α} (h : a = some z) : (a <|> b) = some z := by
  rw [h]; rfl

lemma orElse_of_none {α : Type} {a b : Option α} (h : a = none) : (a <|> b) = b := by
  rw [h]; rfl

lemma orElse_ne_none {α : Type} {a b : Option α} (h : a ≠ none ∨ b ≠ none) : (a <|> b) ≠ none := by
  cases a with
  | none => rcases h with h | h; exact absurd rfl h; exact h
  | some a' => simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

namespace PCG

/-- the local view at `v` of a global phase -/
abbrev loc (Y : GPh V) (v : V) : LPh V := ⟨Y.A0, Y.L, Y.c, Y.l, decide (v ∈ Y.Q)⟩

/-- the context of `v` in the instance of the traversal -/
structure CtxOK (X : PCG V) (c : NCtx V) (v : V) : Prop where
  me : c.me = v
  dil : dilC c = X.dil
  sz : szC c = X.sz
  j : jC c = X.j
  emb : c.emb = ioEmb X.E v

variable {X : PCG V} (hX : X.OK)
include hX

lemma lof_ph {Y : GPh V} (hY : IsPh X Y) : Lof X.sz Y.c = Y.L := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · have := comp_card_pos hX hℓ
    have hc0 : (X.kPh ℓ).c ≠ 0 := by show (X.comp ℓ).card ≠ 0; omega
    show (if (X.kPh ℓ).c = 0 then X.sz else (X.kPh ℓ).c) = (X.kPh ℓ).L
    exact (if_neg hc0).trans rfl
  · unfold Lof; simp [ePh]

lemma c_ph {Y : GPh V} (hY : IsPh X Y) : Y.c = 0 ↔ Y = X.ePh := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · have := comp_card_pos hX hℓ
    simp only [kPh_ne_ePh hX hℓ, iff_false]; simp only [kPh]; omega
  · simp [ePh]

lemma l_mem {Y : GPh V} (hY : IsPh X Y) : Y.l ∈ Y.Q := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · exact self_mem_comp hX hℓ
  · exact hX.rP

/-- The root of a phase's tree is its leader. -/
lemma dep_zero_iff {Y : GPh V} (hY : IsPh X Y) {u : V} (hu : u ∈ Y.Q) :
    dep Y.par Y.rk u = 0 ↔ u = Y.l := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · simp only [kPh] at hu ⊢
    have huS := (mem_comp.1 hu).1
    constructor
    · intro h0
      cases hp : X.parS u with
      | none => rw [← (mem_comp.1 hu).2, hX.Sself u huS hp]
      | some p => rw [dep_some hX.Srk huS hp] at h0; omega
    · rintro rfl
      exact dep_none (mem_lds.1 hℓ).2
  · simp only [ePh] at hu ⊢
    constructor
    · intro h0
      cases hp : X.parP u with
      | none => exact root_unique hX hu hp
      | some p => rw [dep_some hX.Prk hu hp] at h0; omega
    · rintro rfl
      exact dep_none hX.parr

lemma par_of_ne_l {Y : GPh V} (hY : IsPh X Y) {u : V} (hu : u ∈ Y.Q) (hne : u ≠ Y.l) :
    ∃ p, Y.par u = some p ∧ p ∈ Y.Q ∧ dep Y.par Y.rk u = dep Y.par Y.rk p + 1 := by
  have hg := isPh_gok hX hY
  cases hp : Y.par u with
  | none =>
    exfalso
    have : dep Y.par Y.rk u = 0 := dep_none hp
    exact hne ((dep_zero_iff hX hY hu).1 this)
  | some p =>
    refine ⟨p, rfl, hg.par u hu p hp, ?_⟩
    exact dep_some (S := Y.Q) hg.rk hu hp

variable {v : V} {d : LD V} (hd : X.LDOK d v) {c : NCtx V} (hc : X.CtxOK c v)
include hd

lemma memQ_ph {Y : GPh V} (hY : IsPh X Y) : memQ d Y.c Y.l = decide (v ∈ Y.Q) := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · have := comp_card_pos hX hℓ
    have hc0 : (X.kPh ℓ).c ≠ 0 := by show (X.comp ℓ).card ≠ 0; omega
    unfold memQ
    rw [if_neg hc0, hd.bS, hd.rtS]
    show (decide (v ∈ X.S) && decide (X.rtS v = ℓ)) = decide (v ∈ X.comp ℓ)
    have hiff : v ∈ X.comp ℓ ↔ v ∈ X.S ∧ X.rtS v = ℓ := mem_comp
    by_cases h1 : v ∈ X.S <;> by_cases h2 : X.rtS v = ℓ <;> simp [h1, h2, hiff]
  · show (if X.ePh.c = 0 then d.bP else (d.bS && decide (d.rtS = X.ePh.l))) = decide (v ∈ X.ePh.Q)
    rw [if_pos (show X.ePh.c = 0 from rfl)]
    exact hd.bP

lemma l_loc {Y : GPh V} (hY : IsPh X Y) (hv : v ∈ Y.Q) :
    (if Y.c = 0 then d.rtP else d.rtS) = Y.l := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · have hc0 : (X.kPh ℓ).c ≠ 0 := by
      show (X.comp ℓ).card ≠ 0; have := comp_card_pos hX hℓ; omega
    have hv' : v ∈ X.comp ℓ := hv
    rw [if_neg hc0, hd.rtS]
    exact (mem_comp.1 hv').2
  · rw [if_pos (show X.ePh.c = 0 from rfl)]
    exact hd.rtP hv

include hc

/-- **Soundness**: what a node learns in a frame `ψ` (before the current frame, or in the current
frame if it is not in a sub-run) is the phase whose window contains `ψ`. -/
theorem cand_sound {f ψ : ℕ} (hψ : ψ < f ∨ (ψ = f ∧ ¬ X.LB v f)) {Z : LPh V}
    (h : cand c d (X.lh v f) ψ = some Z) :
    ∃ Y, IsPh X Y ∧ Z = loc Y v ∧ v ∈ footprint X.E X.j Y.Q ∧ ws X Y ≤ ψ ∧ ψ < we X Y := by
  classical
  have hlen := lh_length X v f
  unfold cand at h
  rw [hlen, hc.dil, hc.sz, hc.me] at h
  rcases orElse_some_cases h with h | h <;> rcases orElse_some_cases h with h | h
  · -- the start of the own phase
    split_ifs at h with h1
    obtain ⟨hL, hψ1, hψf, hfp⟩ := h1
    simp only [Option.some.injEq] at h
    subst h
    have hℓ := (isLd_iff hX hd).1 hL
    obtain ⟨k, hk, hkph⟩ := exists_ph hX hℓ
    have ha : X.aOf v = ψ := by
      rw [aOf_eq hX hk hkph]
      rcases (fromPar_iff hX hd).1 hfp with ⟨h0, rfl⟩ | ⟨-, p, hp, k', hk', h', hs'⟩
      · rcases ph_pred hX hℓ hk hkph with ⟨rfl, -⟩ | ⟨-, p, -, hp⟩
        · rw [stF_zero]; omega
        · rw [hX.parr] at hp; simp at hp
      · have hn : k' + 1 < X.tl.length := by
          by_contra hge
          have := tl_last hX hk' (by omega)
          rw [h'] at this
          simp only [nxt, hp, ite_true, isL_iff.2 hℓ] at this
          simp at this
        have hs := tl_succ hX hn
        rw [h'] at hs
        simp only [nxt, hp, ite_true, isL_iff.2 hℓ] at hs
        have := List.nodup_iff_injective_getElem.1 (tl_nodup hX)
        have hkk : k' + 1 = k := congrArg Fin.val
          (this (a₁ := ⟨k' + 1, hn⟩) (a₂ := ⟨k, hk⟩) ((Option.some.inj hs).symm.trans hkph.symm))
        rw [← hkk, stF_tk hX hk' h']; omega
    have hvS := (mem_lds.1 hℓ).1
    have hcnt : d.cnt = (X.comp v).card := by rw [hd.cnt hvS, hX.Sself v hvS (mem_lds.1 hℓ).2]
    refine ⟨X.kPh v, Or.inl ⟨v, hℓ, rfl⟩, ?_, subset_footprint _ _ _ (self_mem_comp hX hℓ), ?_, ?_⟩
    · unfold loc kPh
      rw [hcnt, ← ha, decide_eq_true (self_mem_comp hX hℓ)]
      rfl
    · rw [ws_kPh hX hℓ, ha]
    · rw [we_kPh hX hℓ, ha]
      have := phEnd_ge hX hℓ ψ; have := PiK_pos hX hℓ; omega
  · -- the start of the final phase
    split_ifs at h with h1
    obtain ⟨hbP, hpP, hψf, htok, hctl⟩ := h1
    simp only [Option.some.injEq] at h
    subst h
    have hvr := (isRoot_iff hX hd).1 ⟨hbP, hpP⟩
    rw [lh_take X v hψf] at htok
    have hnLB : ¬ X.LB v ψ := by
      rcases hψ with hψ | ⟨rfl, hn⟩
      · intro hB
        have := hctl hψ
        rw [lh_getD X v hψ, if_pos hB] at this
        exact this rfl
      · exact hn
    have hψ1 : 1 ≤ ψ := by
      by_contra h0
      have : ψ = 0 := by omega
      subst this
      unfold tokAct at htok
      rw [lh_length] at htok
      simp at htok
    rw [tokAct_eq hX hd hψ1 hnLB] at htok
    by_cases hseg : ∃ k < X.tl.length, X.stF k = ψ
    · exfalso
      rw [dif_pos hseg] at htok
      split_ifs at htok with hs
      all_goals first
        | (cases hx : X.tl[hseg.choose]'hseg.choose_spec.1 <;> rw [hx] at htok <;> cases htok)
        | cases htok
    rw [dif_neg hseg] at htok
    by_cases hE : v = X.r ∧ ψ = X.E0
    · rw [if_pos hE] at htok
      obtain ⟨-, hψE⟩ := hE
      subst hψE
      refine ⟨X.ePh, Or.inr rfl, ?_, ?_, by rw [ws_ePh], ?_⟩
      · unfold loc ePh; rw [hvr, decide_eq_true hX.rP]
      · rw [hvr]; exact subset_footprint _ _ _ hX.rP
      · rw [we_ePh]; have := E0_le_A0 hX; have := PiE_pos hX; unfold TL; omega
    · rw [if_neg hE] at htok
      cases htok
  · -- a broadcast
    split_ifs at h with h1
    obtain ⟨cc, hcc, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, u, hu⟩ := (bcR_lh hX).1 hcc
    obtain ⟨Y, hY, h2, h3, hu1, hv1, -, -, rfl⟩ := (ML_bcW hX).1 hu
    have hg := isPh_gok hX hY
    have hs := win_sub hX hY
    have := PiL_ge X.dil Y.L
    refine ⟨Y, hY, ?_, subset_footprint _ _ _ hv1, by omega, by omega⟩
    unfold loc
    rw [lof_ph hX hY, floor_window (by unfold PiL; have := hg.L1; exact Nat.mul_pos (Nat.succ_pos _) (by omega)) hg.dvd h2 (by omega),
      l_loc hX hd hY hv1, decide_eq_true hv1]
  · -- a packet
    split_ifs at h with h1
    obtain ⟨cl, hcl, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨cc, l⟩ := cl
    obtain ⟨-, u, x, hu⟩ := (pkR_lh hX).1 hcl
    obtain ⟨Y, hY, h2, h3, hx, rfl, rfl⟩ := (ML_pkW hX).1 hu
    have hg := isPh_gok hX hY
    have hs := win_sub hX hY
    have hP : 0 < PiL X.dil Y.L := by unfold PiL; have := hg.L1; exact Nat.mul_pos (Nat.succ_pos _) (by omega)
    have hle : X.dil * Y.L ≤ PiL X.dil Y.L := by unfold PiL; nlinarith
    have hxpk : x ∈ pk X.E X.j Y.Q ((ψ - Y.A0 - PiL X.dil Y.L) / Y.L) u v :=
      Finset.mem_toList.1 (List.mem_of_getElem? hx)
    refine ⟨Y, hY, ?_, (pk_fp hX.hE hX.hj hxpk).2, by omega, by omega⟩
    unfold loc
    simp only
    rw [lof_ph hX hY, floor_window hP (Nat.dvd_add hg.dvd (dvd_refl _)) h2 (by omega),
      Nat.add_sub_cancel, memQ_ph hX hd hY]

/-- What a node learns in the current frame lies in the future. -/
lemma cand_now {f : ℕ} {Z : LPh V} (h : cand c d (X.lh v f) f = some Z) :
    f ≤ Z.A0 ∧ 1 ≤ Z.L := by
  classical
  have hlen := lh_length X v f
  unfold cand at h
  rw [hlen, hc.dil, hc.sz, hc.me] at h
  rcases orElse_some_cases h with h | h <;> rcases orElse_some_cases h with h | h
  · split_ifs at h with h1
    simp only [Option.some.injEq] at h
    subst h
    have hℓ := (isLd_iff hX hd).1 h1.1
    have hvS := (mem_lds.1 hℓ).1
    have hcnt : d.cnt = (X.comp v).card := by rw [hd.cnt hvS, hX.Sself v hvS (mem_lds.1 hℓ).2]
    have := comp_card_pos hX hℓ
    rw [hcnt]
    exact ⟨le_alignUp _ (by unfold PiL; exact Nat.mul_pos (Nat.succ_pos _) (by omega)), this⟩
  · split_ifs at h with h1
    simp only [Option.some.injEq] at h
    subst h
    have := (ePh_gok hX).L1
    exact ⟨le_alignUp _ (by unfold PiL; simp only [ePh] at this; exact Nat.mul_pos (Nat.succ_pos _) (by omega)), this⟩
  · split_ifs at h with h1; exact absurd h1 (lt_irrefl _)
  · split_ifs at h with h1; exact absurd h1 (lt_irrefl _)

lemma mem_known {f : ℕ} {Z : LPh V} :
    Z ∈ pcKnown c d (X.lh v f) ↔ ∃ ψ ≤ f, cand c d (X.lh v f) ψ = some Z := by
  unfold pcKnown
  rw [List.mem_filterMap, lh_length]
  simp only [List.mem_range]
  constructor
  · rintro ⟨ψ, hψ, h⟩; exact ⟨ψ, by omega, h⟩
  · rintro ⟨ψ, hψ, h⟩; exact ⟨ψ, by omega, h⟩

/-- **Soundness of the known phases.** -/
theorem known_sound {f : ℕ} {Z : LPh V} (h : Z ∈ pcKnown c d (X.lh v f)) :
    (∃ Y, IsPh X Y ∧ Z = loc Y v ∧ v ∈ footprint X.E X.j Y.Q ∧ ws X Y ≤ f) ∨
      (X.LB v f ∧ f ≤ Z.A0 ∧ 1 ≤ Z.L) := by
  obtain ⟨ψ, hψ, hc'⟩ := (mem_known hX hd hc).1 h
  rcases Nat.lt_or_eq_of_le hψ with hlt | rfl
  · obtain ⟨Y, hY, h1, h2, h3, -⟩ := cand_sound hX hd hc (Or.inl hlt) hc'
    exact Or.inl ⟨Y, hY, h1, h2, by omega⟩
  · by_cases hB : X.LB v ψ
    · exact Or.inr ⟨hB, cand_now hX hd hc hc'⟩
    · obtain ⟨Y, hY, h1, h2, h3, -⟩ := cand_sound hX hd hc (Or.inr ⟨rfl, hB⟩) hc'
      exact Or.inl ⟨Y, hY, h1, h2, h3⟩

/-- A frame in a phase's window gives that phase's view, if anything. -/
lemma cand_win {f ψ : ℕ} (hψ : ψ < f ∨ (ψ = f ∧ ¬ X.LB v f)) {Y : GPh V} (hY : IsPh X Y)
    (h1 : ws X Y ≤ ψ) (h2 : ψ < we X Y) (hne : cand c d (X.lh v f) ψ ≠ none) :
    cand c d (X.lh v f) ψ = some (loc Y v) := by
  obtain ⟨Z, hZ⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨Y', hY', rfl, -, h3, h4⟩ := cand_sound hX hd hc hψ hZ
  rw [hZ, win_disj hX hY' hY h3 h4 h1 h2]

/-- **A node that received a packet** of a phase knows the phase. -/
theorem known_R {f ψ : ℕ} (hψ : ψ < f) {u x : V} {cc : ℕ} {l : V}
    (h : X.ML u v ψ = some (pcPkW x cc l)) :
    ∃ Y, IsPh X Y ∧ ws X Y ≤ ψ ∧ ψ < we X Y ∧ loc Y v ∈ pcKnown c d (X.lh v f) := by
  classical
  obtain ⟨Y, hY, h2, h3, -, -, -⟩ := (ML_pkW hX).1 h
  have hs := win_sub hX hY
  have hle : X.dil * Y.L ≤ PiL X.dil Y.L := by unfold PiL; nlinarith
  refine ⟨Y, hY, by omega, by omega, (mem_known hX hd hc).2 ⟨ψ, hψ.le, ?_⟩⟩
  refine cand_win hX hd hc (Or.inl hψ) hY (by omega) (by omega) ?_
  have hpk : pkR (X.lh v f) ψ = some (cc, l) := (pkR_lh hX).2 ⟨hψ, u, x, h⟩
  unfold cand
  rw [lh_length]
  apply orElse_ne_none
  right
  apply orElse_ne_none
  right
  rw [if_pos hψ, hpk]
  simp

/-- **The starter** of a phase (the leader, or the root for the final phase) knows the phase
from the start of its window. -/
theorem known_start {f : ℕ} {Y : GPh V} (hY : IsPh X Y) (hvl : v = Y.l) (hf : ws X Y ≤ f)
    (hctl : ws X Y < f ∨ ¬ X.LB v f) : loc Y v ∈ pcKnown c d (X.lh v f) := by
  classical
  have hψ : ws X Y < f ∨ (ws X Y = f ∧ ¬ X.LB v f) := by
    rcases Nat.lt_or_eq_of_le hf with h | h
    · exact Or.inl h
    · rcases hctl with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
  have hw := win_ok hX hY
  refine (mem_known hX hd hc).2 ⟨ws X Y, hf, cand_win hX hd hc hψ hY le_rfl hw.2 ?_⟩
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · simp only [kPh] at hvl
    subst hvl
    rw [ws_kPh hX hℓ] at hψ hf ⊢
    obtain ⟨k, hk, hkph⟩ := exists_ph hX hℓ
    have ha1 : 1 ≤ X.aOf v := by rw [aOf_eq hX hk hkph]; exact one_le_stF hX hk.le
    unfold cand
    apply orElse_ne_none; left; apply orElse_ne_none; left
    rw [lh_length, if_pos]
    · simp
    refine ⟨(isLd_iff hX hd).2 hℓ, ha1, hf, (fromPar_iff hX hd).2 ?_⟩
    rcases ph_pred hX hℓ hk hkph with ⟨rfl, rfl⟩ | ⟨hk0, p, h', hp⟩
    · left; rw [aOf_eq hX hk hkph, stF_zero]; exact ⟨rfl, rfl⟩
    · right
      have := stF_tk hX (show k - 1 < X.tl.length by omega) h'
      rw [show k - 1 + 1 = k by omega] at this
      refine ⟨by rw [aOf_eq hX hk hkph] at hf; omega, p, hp, k - 1, by omega, h', ?_⟩
      rw [aOf_eq hX hk hkph]; omega
  · simp only [ePh] at hvl
    subst hvl
    rw [ws_ePh] at hψ hf ⊢
    have hE1 : 1 ≤ X.E0 := one_le_stF hX le_rfl
    unfold cand
    apply orElse_ne_none; left; apply orElse_ne_none; right
    rw [lh_length, if_pos]
    · simp
    have hnb := not_LB_E0 hX X.r
    refine ⟨((isRoot_iff hX hd).2 rfl).1, ((isRoot_iff hX hd).2 rfl).2, hf, ?_, ?_⟩
    · rw [lh_take X X.r hf, hc.dil, tokAct_eq hX hd hE1 hnb, dif_neg, if_pos (show X.r = X.r ∧ X.E0 = X.E0 from ⟨rfl, rfl⟩)]
      rintro ⟨k, hk, hs⟩
      have := stF_lt hX hk le_rfl
      unfold E0 at hs; omega
    · intro hlt
      rw [lh_getD X X.r hlt, if_neg hnb]
      simp

/-- **A source** of a phase knows the phase after the broadcast window. -/
theorem known_Q {f : ℕ} {Y : GPh V} (hY : IsPh X Y) (hv : v ∈ Y.Q) (hf : Y.A0 + Y.L ≤ f) :
    loc Y v ∈ pcKnown c d (X.lh v f) := by
  classical
  have hg := isPh_gok hX hY
  have hs := win_sub hX hY
  have := PiL_ge X.dil Y.L
  by_cases hvl : v = Y.l
  · exact known_start hX hd hc hY hvl (by have := hg.L1; omega) (Or.inl (by have := hg.L1; omega))
  · -- another source received the broadcast from its parent
    obtain ⟨p, hp, hpQ, hdep⟩ := par_of_ne_l hX hY hv hvl
    have hdv := hg.dep v hv
    set ψ := Y.A0 + dep Y.par Y.rk p with hψdef
    have hψf : ψ < f := by omega
    have hbc : X.ML p v ψ = some (bcW Y.c) :=
      (ML_bcW hX).2 ⟨Y, hY, by omega, by omega, hpQ, hv, hp, by omega, rfl⟩
    refine (mem_known hX hd hc).2 ⟨ψ, hψf.le, ?_⟩
    refine cand_win hX hd hc (Or.inl hψf) hY (by omega) (by omega) ?_
    unfold cand
    apply orElse_ne_none; right; apply orElse_ne_none; left
    rw [lh_length, if_pos hψf, (bcR_lh hX).2 ⟨hψf, p, hbc⟩]
    simp

/-- **Every node of the footprint** of a phase's sources knows the phase after the announcement
window. -/
theorem known_fp {f : ℕ} {Y : GPh V} (hY : IsPh X Y) (hv : v ∈ footprint X.E X.j Y.Q)
    (hf : Y.A0 + PiL X.dil Y.L + X.dil * Y.L ≤ f) : loc Y v ∈ pcKnown c d (X.lh v f) := by
  classical
  have hg := isPh_gok hX hY
  have := PiL_ge X.dil Y.L
  rcases mem_footprint.1 hv with hvQ | ⟨x, hxQ, C, hC, e, he, hve⟩
  · exact known_Q hX hd hc hY hvQ (by omega)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hwalk := path_edge hX.hE hX.hj hC hi
    rw [hwalk, Sym2.mem_iff] at hve
    have hdil : (X.E.path X.j x C).length ≤ X.dil := by
      unfold dil Overlays.dil
      refine le_trans ?_ (Finset.le_sup (f := fun j => univ.sup (fun v =>
        X.E.cl.sup (fun C => (X.E.path j v C).length))) (Finset.mem_range.2 hX.hj))
      refine le_trans ?_ (Finset.le_sup (f := fun v => X.E.cl.sup (fun C =>
        (X.E.path X.j v C).length)) (mem_univ x))
      exact Finset.le_sup (f := fun C => (X.E.path X.j x C).length) (mem_filter.1 hC).1
    -- `v` is the `(i' + 1)`-th vertex of the walk for some `i' ≤ i`, or the source
    obtain ⟨i', hi', hvi⟩ | hvi : (∃ i' < (X.E.path X.j x C).length,
        v = vtx (X.E.path X.j x C) x (i' + 1)) ∨ v = x := by
      rcases hve with rfl | rfl
      · rcases Nat.eq_zero_or_pos i with rfl | hpos
        · right; exact vtx_zero _ _
        · left; exact ⟨i - 1, by omega, by rw [show i - 1 + 1 = i by omega]⟩
      · left; exact ⟨i, hi, rfl⟩
    · have hxpk : x ∈ pk X.E X.j Y.Q i' (vtx (X.E.path X.j x C) x i') v :=
        mem_pk.2 ⟨hxQ, C, hC, hi', rfl, hvi.symm⟩
      -- the packet of `x` reaches `v` in sub-phase `i'`
      set s := (pk X.E X.j Y.Q i' (vtx (X.E.path X.j x C) x i') v).toList.idxOf x with hsdef
      have hs : s < (pk X.E X.j Y.Q i' (vtx (X.E.path X.j x C) x i') v).toList.length :=
        List.idxOf_lt_length_iff.2 (Finset.mem_toList.2 hxpk)
      have hsL : s < Y.L := by
        rw [Finset.length_toList] at hs
        exact lt_of_lt_of_le hs ((card_pk_le _ _ _ _).trans hg.QL)
      set ψ := Y.A0 + PiL X.dil Y.L + i' * Y.L + s with hψdef
      have hiL : i' * Y.L + s < X.dil * Y.L := by
        have : (i' + 1) * Y.L ≤ X.dil * Y.L := Nat.mul_le_mul_right _ (by omega)
        rw [add_mul, one_mul] at this; omega
      have hψf : ψ < f := by omega
      have hdiv : (ψ - Y.A0 - PiL X.dil Y.L) / Y.L = i' := by
        rw [hψdef, show Y.A0 + PiL X.dil Y.L + i' * Y.L + s - Y.A0 - PiL X.dil Y.L =
          s + i' * Y.L by omega, Nat.add_mul_div_right _ _ (by have := hg.L1; omega),
          Nat.div_eq_of_lt hsL, zero_add]
      have hmod : (ψ - Y.A0 - PiL X.dil Y.L) % Y.L = s := by
        rw [hψdef, show Y.A0 + PiL X.dil Y.L + i' * Y.L + s - Y.A0 - PiL X.dil Y.L =
          s + i' * Y.L by omega, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsL]
      have hpkm : X.ML (vtx (X.E.path X.j x C) x i') v ψ = some (pcPkW x Y.c Y.l) := by
        refine (ML_pkW hX).2 ⟨Y, hY, by omega, by omega, ?_, rfl, rfl⟩
        rw [hdiv, hmod, hsdef, List.getElem?_idxOf (Finset.mem_toList.2 hxpk)]
      obtain ⟨Y', hY', h1, h2, hk⟩ := known_R hX hd hc hψf hpkm
      have hs' := win_sub hX hY
      have hle : X.dil * Y.L ≤ PiL X.dil Y.L := by unfold PiL; nlinarith
      rwa [win_disj hX hY' hY h1 h2 (by omega) (by omega)] at hk
    · subst hvi
      exact known_Q hX hd hc hY hxQ (by omega)

end PCG

end APSP.Stoc.Congest
