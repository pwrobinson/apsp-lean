import ApspStoc.Congest.PerCompKnown

/-!
# The controller follows the schedule (for `perCompR`)

In every frame in which a node of the footprint of `P` is not in a sub-run, its messages
(`lsend`) are those of the schedule `ML` (`lsend_eq`): the token part, the broadcast part and the
packet part of `lsend` are the corresponding parts of `ML` (`onlyTok`, `onlyBc`, `onlyPk`). It
starts the sub-run of component `K` exactly at frame `bOf ℓ` if it is in the footprint of `K`
(`lstart_some`, `lstart_none`), and halts at `TL` (`lhalt_iff`).
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the token part of a message -/
def onlyTok (o : Option (W3 V)) : Option (W3 V) := if o = some tokW then o else none

/-- the broadcast part of a message -/
def onlyBc (o : Option (W3 V)) : Option (W3 V) := (bcOf o).map bcW

/-- the packet part of a message -/
def onlyPk (o : Option (W3 V)) : Option (W3 V) :=
  match o with
  | some (.id x, .num c, .id l) => some (pcPkW x c l)
  | _ => none

lemma decomp3 (o : Option (W3 V))
    (h : o = none ∨ o = some tokW ∨ (∃ c, o = some (bcW c)) ∨ ∃ x c l, o = some (pcPkW x c l)) :
    o = ((onlyTok o <|> onlyBc o) <|> onlyPk o) := by
  rcases h with rfl | rfl | ⟨c, rfl⟩ | ⟨x, c, l, rfl⟩
  · rfl
  · rfl
  · simp [onlyTok, onlyBc, onlyPk, bcOf, tokW, bcW, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  · simp [onlyTok, onlyBc, onlyPk, bcOf, tokW, pcPkW, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

open Classical in
lemma head?_filterMap_const {α β : Type} (l : List α) (g : α → Option β) (z : α)
    (h : ∀ x ∈ l, g x ≠ none → x = z) :
    (l.filterMap g).head? = if z ∈ l then g z else none := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filterMap_cons]
    by_cases ha : g a = none
    · rw [ha]
      simp only
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      by_cases hz : z ∈ l
      · rw [if_pos hz, if_pos (List.mem_cons_of_mem _ hz)]
      · rw [if_neg hz]
        by_cases hza : z = a
        · subst hza; rw [if_pos List.mem_cons_self, ha]
        · rw [if_neg (by simp [hz, hza])]
    · have := h a List.mem_cons_self ha
      subst this
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 ha
      rw [hb, if_pos List.mem_cons_self]
      rfl

namespace PCG

variable {X : PCG V} (hX : X.OK)
include hX

/-- In a packet window, the decoded packets received in the previous sub-phase. -/
lemma idOf_slot {Y : GPh V} (hY : IsPh X Y) {v y : V} {h s : ℕ} (hh : 1 ≤ h) (hhd : h ≤ X.dil)
    (hs : s < Y.L) :
    idOf (X.ML y v (Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s)) =
      (pk X.E X.j Y.Q (h - 1) y v).toList[s]? := by
  classical
  have hg := isPh_gok hX hY
  have hsub := win_sub hX hY
  have hle : X.dil * Y.L ≤ PiL X.dil Y.L := by unfold PiL; nlinarith
  have hlt : (h - 1) * Y.L + s < X.dil * Y.L := by
    have : h * Y.L ≤ X.dil * Y.L := Nat.mul_le_mul_right _ hhd
    have : (h - 1) * Y.L + Y.L = h * Y.L := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hh]
    omega
  rw [ML_win hX hY (by omega) (by omega), phMsg_pk_win _ _ _ _ (by have := PiL_ge X.dil Y.L; omega)
    (by omega) (by omega) hg.L1]
  have e1 : Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s - Y.A0 - PiL X.dil Y.L = s + (h - 1) * Y.L :=
    by omega
  rw [e1, Nat.add_mul_div_right _ _ (by have := hg.L1; omega), Nat.div_eq_of_lt hs, zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  unfold slotMsg
  cases (pk X.E X.j Y.Q (h - 1) y v).toList[s]? <;> rfl

variable {v : V} {d : LD V} (hd : X.LDOK d v) {c : NCtx V} (hc : X.CtxOK c v)
include hd hc

lemma chOf_iff {Y : GPh V} (hY : IsPh X Y) (hv : v ∈ Y.Q) (w : V) :
    chOf d Y.c w ↔ w ∈ Y.Q ∧ Y.par w = some v := by
  unfold chOf
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · have hc0 : (X.kPh ℓ).c ≠ 0 := by
      show (X.comp ℓ).card ≠ 0; have := comp_card_pos hX hℓ; omega
    have hv' : v ∈ X.comp ℓ := hv
    rw [if_neg hc0, hd.kS]
    exact kidsS_comp hX hv' w
  · simp only [ePh, if_pos, hd.kP, mem_kidsOf]

/-- **The token part.** -/
lemma tokPart_eq {f : ℕ} (hctl : ¬ X.LB v f) (w : V) :
    pcTokMsg (dilC c) d (X.lh v f) w = onlyTok (X.ML v w f) := by
  classical
  unfold pcTokMsg
  rw [hc.dil]
  unfold onlyTok
  cases ht : tokAct X.dil d (X.lh v f) with
  | send w' =>
    obtain ⟨k, hk, h1, h2⟩ := (tokAct_send hX hd hctl w').1 ht
    simp only
    by_cases hw : w = w'
    · subst hw
      rw [if_pos rfl, if_pos ((ML_tokW hX).2 ⟨k, hk, h1, h2⟩)]
      exact ((ML_tokW hX).2 ⟨k, hk, h1, h2⟩).symm
    · rw [if_neg hw, if_neg]
      intro h
      obtain ⟨k', hk', h1', h2'⟩ := (ML_tokW hX).1 h
      have := stF_inj hX hk' hk (h2'.trans h2.symm)
      subst this
      rw [h1] at h1'; cases h1'
      exact hw rfl
  | startK =>
    simp only
    rw [if_neg]
    intro h
    obtain ⟨k, hk, h1, h2⟩ := (ML_tokW hX).1 h
    rw [(tokAct_send hX hd hctl w).2 ⟨k, hk, h1, h2⟩] at ht; cases ht
  | startE =>
    simp only
    rw [if_neg]
    intro h
    obtain ⟨k, hk, h1, h2⟩ := (ML_tokW hX).1 h
    rw [(tokAct_send hX hd hctl w).2 ⟨k, hk, h1, h2⟩] at ht; cases ht
  | idle =>
    simp only
    rw [if_neg]
    intro h
    obtain ⟨k, hk, h1, h2⟩ := (ML_tokW hX).1 h
    rw [(tokAct_send hX hd hctl w).2 ⟨k, hk, h1, h2⟩] at ht; cases ht

omit hX hd hc in
lemma onlyBc_none {o : Option (W3 V)} (h : ∀ cc, o ≠ some (bcW cc))
    (hs : o = none ∨ o = some tokW ∨ (∃ c, o = some (bcW c)) ∨ ∃ x c l, o = some (pcPkW x c l)) :
    onlyBc o = none := by
  rcases hs with rfl | rfl | ⟨cc, rfl⟩ | ⟨x, cc, l, rfl⟩
  · rfl
  · rfl
  · exact absurd rfl (h cc)
  · rfl

/-- **The broadcast part.** -/
lemma bcPart_eq {f : ℕ} (hctl : ¬ X.LB v f) (w : V) :
    bcMsg c d (X.lh v f) w = onlyBc (X.ML v w f) := by
  classical
  unfold bcMsg
  rw [lh_length, hc.me]
  by_cases hst : ∃ Y, IsPh X Y ∧ Y.l = v ∧ Y.A0 = f
  · -- `v` starts the broadcast of a phase
    obtain ⟨Y, hY, hl, hA⟩ := hst
    have hsub := win_sub hX hY
    have hw := win_ok hX hY
    have hg := isPh_gok hX hY
    have hPi := PiL_ge X.dil Y.L
    have hL1 := hg.L1
    have hkn : loc Y v ∈ pcKnown c d (X.lh v f) :=
      known_start hX hd hc hY hl.symm (by omega) (Or.inr hctl)
    have hfind : (pcKnown c d (X.lh v f)).find? (fun Z => decide (Z.l = v ∧ Z.A0 = f)) =
        some (loc Y v) := by
      have hsome : ((pcKnown c d (X.lh v f)).find? (fun Z => decide (Z.l = v ∧ Z.A0 = f))).isSome :=
        List.find?_isSome.2 ⟨loc Y v, hkn, by simp [loc, hl, hA]⟩
      obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hsome
      rw [hZ]
      have hpZ := List.find?_some hZ
      simp only [decide_eq_true_eq] at hpZ
      rcases known_sound hX hd hc (List.mem_of_find?_eq_some hZ) with
        ⟨Y', hY', rfl, -, hws⟩ | ⟨hB, -⟩
      · simp only [loc] at hpZ
        have hsub' := win_sub hX hY'
        have hw' := win_ok hX hY'
        have hPi' := PiL_ge X.dil Y'.L
        have hL1' := (isPh_gok hX hY').L1
        rw [win_disj hX hY' hY (φ := f) (by omega) (by omega) (by omega) (by omega)]
      · exact absurd hB hctl
    rw [hfind]
    simp only [loc]
    have hvQ : v ∈ Y.Q := hl ▸ l_mem hX hY
    rw [ML_win hX hY (by omega) (by omega), phMsg_bc_win _ _ _ _ (by omega) (by omega)]
    have hdep : dep Y.par Y.rk v = f - Y.A0 := by
      rw [(dep_zero_iff hX hY hvQ).2 hl.symm]; omega
    by_cases hch : chOf d Y.c w
    · rw [if_pos hch, if_pos ⟨hvQ, ((chOf_iff hX hd hc hY hvQ w).1 hch).1,
        ((chOf_iff hX hd hc hY hvQ w).1 hch).2, hdep⟩]
      rfl
    · rw [if_neg hch, if_neg (fun h' => hch ((chOf_iff hX hd hc hY hvQ w).2 ⟨h'.2.1, h'.2.2.1⟩))]
      rfl
  · -- forwarding the broadcast received from the parent
    have hfind : (pcKnown c d (X.lh v f)).find? (fun Z => decide (Z.l = v ∧ Z.A0 = f)) = none := by
      rw [List.find?_eq_none]
      intro Z hZ hp
      simp only [decide_eq_true_eq] at hp
      rcases known_sound hX hd hc hZ with ⟨Y', hY', rfl, -, -⟩ | ⟨hB, -⟩
      · exact hst ⟨Y', hY', hp.1, hp.2⟩
      · exact hctl hB
    rw [hfind]
    simp only
    by_cases hbc : ∃ cc, 1 ≤ f ∧ bcR (X.lh v f) (f - 1) = some cc
    · obtain ⟨cc, hf1, hcc⟩ := hbc
      rw [if_pos hf1, hcc]
      simp only
      obtain ⟨-, u, hu⟩ := (bcR_lh hX).1 hcc
      obtain ⟨Y, hY, h1, h2, huQ, hvQ, hp, hd1, rfl⟩ := (ML_bcW hX).1 hu
      have hg := isPh_gok hX hY
      have hsub := win_sub hX hY
      have := PiL_ge X.dil Y.L
      have hdv : dep Y.par Y.rk v = dep Y.par Y.rk u + 1 := dep_some (S := Y.Q) hg.rk hvQ hp
      have hdl := hg.dep v hvQ
      rw [ML_win hX hY (by omega) (by omega), phMsg_bc_win _ _ _ _ (by omega) (by omega)]
      by_cases hch : chOf d Y.c w
      · rw [if_pos hch, if_pos ⟨hvQ, ((chOf_iff hX hd hc hY hvQ w).1 hch).1,
          ((chOf_iff hX hd hc hY hvQ w).1 hch).2, by omega⟩]
        rfl
      · rw [if_neg hch, if_neg (fun h' => hch ((chOf_iff hX hd hc hY hvQ w).2 ⟨h'.2.1, h'.2.2.1⟩))]
        rfl
    · have hnone : (if 1 ≤ f then bcR (X.lh v f) (f - 1) else none) = none := by
        split_ifs with hf1
        · cases h : bcR (X.lh v f) (f - 1) with
          | none => rfl
          | some cc => exact absurd ⟨cc, hf1, h⟩ hbc
        · rfl
      rw [hnone]
      symm
      refine onlyBc_none (fun cc hcc => ?_) (ML_shape hX v w f)
      obtain ⟨Y, hY, h1, h2, hvQ, hwQ, hp, hd1, rfl⟩ := (ML_bcW hX).1 hcc
      by_cases hvl : v = Y.l
      · have : dep Y.par Y.rk v = 0 := (dep_zero_iff hX hY hvQ).2 hvl
        exact hst ⟨Y, hY, hvl.symm, by omega⟩
      · obtain ⟨p, hpp, hpQ, hdp⟩ := par_of_ne_l hX hY hvQ hvl
        have hf1 : 1 ≤ f := by omega
        have hbc' : X.ML p v (f - 1) = some (bcW Y.c) :=
          (ML_bcW hX).2 ⟨Y, hY, by omega, by omega, hpQ, hvQ, hpp, by omega, rfl⟩
        exact hbc ⟨Y.c, hf1, (bcR_lh hX).2 ⟨by omega, p, hbc'⟩⟩

/-- The packets computed by a node are those of the schedule. -/
lemma pkLoc_eq {f : ℕ} {Y : GPh V} (hY : IsPh X Y) (h1 : Y.A0 + PiL X.dil Y.L ≤ f)
    (h2 : f < Y.A0 + PiL X.dil Y.L + X.dil * Y.L) (w : V) :
    pkLoc c (X.lh v f) (loc Y v) ((f - Y.A0 - PiL X.dil Y.L) / Y.L) w =
      pk X.E X.j Y.Q ((f - Y.A0 - PiL X.dil Y.L) / Y.L) v w := by
  classical
  have hg := isPh_gok hX hY
  generalize hhdef : (f - Y.A0 - PiL X.dil Y.L) / Y.L = h
  have hhd : h < X.dil := by
    rw [← hhdef, Nat.div_lt_iff_lt_mul (by have := hg.L1; omega)]
    omega
  unfold pkLoc
  simp only [loc]
  rw [hc.me, hc.emb, hc.j, hc.dil]
  ext x
  by_cases h0 : h = 0
  · rw [if_pos h0, h0, pk_zero hX.hE hX.hj]
    split_ifs with hq
    · rw [mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, by simpa using hq.1, hq.2⟩
      · rintro ⟨rfl, -, -⟩; rfl
    · simp only [notMem_empty, false_iff]
      rintro ⟨rfl, hv, hk⟩
      exact hq ⟨by simpa using hv, hk⟩
  · rw [if_neg h0, mem_filter, pk_relay hX.hE hX.hj _ _ (by omega)]
    simp only [mem_univ, true_and]
    apply exists_congr
    intro y
    apply and_congr_left
    intro _
    -- the packets received in sub-phase `h - 1`
    have hrecv : ∀ s < Y.L, idOf (recvAt (X.lh v f) (Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s) y) =
        (pk X.E X.j Y.Q (h - 1) y v).toList[s]? := by
      intro s hs
      have hlt : Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s < f := by
        have : h * Y.L ≤ f - Y.A0 - PiL X.dil Y.L := by rw [← hhdef]; exact Nat.div_mul_le_self _ _
        have : (h - 1) * Y.L + Y.L = h * Y.L := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
        omega
      rw [recvAt_lh hX, if_pos hlt, idOf_slot hX hY (by omega) hhd.le hs]
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [hrecv s hs] at hx
      exact Finset.mem_toList.1 (List.mem_of_getElem? hx)
    · intro hx
      have hm := Finset.mem_toList.2 hx
      refine ⟨(pk X.E X.j Y.Q (h - 1) y v).toList.idxOf x, ?_, ?_⟩
      · have := List.idxOf_lt_length_iff.2 hm
        rw [Finset.length_toList] at this
        exact lt_of_lt_of_le this ((card_pk_le _ _ _ _).trans hg.QL)
      · rw [hrecv _ (by
          have := List.idxOf_lt_length_iff.2 hm
          rw [Finset.length_toList] at this
          exact lt_of_lt_of_le this ((card_pk_le _ _ _ _).trans hg.QL))]
        exact List.getElem?_idxOf hm

/-- **The packet part.** -/
lemma pkPart_eq {f : ℕ} (hctl : ¬ X.LB v f) (w : V) :
    pkMsg c d (X.lh v f) w = onlyPk (X.ML v w f) := by
  classical
  unfold pkMsg
  by_cases hwin : ∃ Y, IsPh X Y ∧ Y.A0 + PiL X.dil Y.L ≤ f ∧
      f < Y.A0 + PiL X.dil Y.L + X.dil * Y.L
  · obtain ⟨Y, hY, h1, h2⟩ := hwin
    have hg := isPh_gok hX hY
    have hsub := win_sub hX hY
    have hle : X.dil * Y.L ≤ PiL X.dil Y.L := by unfold PiL; nlinarith
    rw [head?_filterMap_const _ _ (loc Y v)]
    · have hML : X.ML v w f = slotMsg (pk X.E X.j Y.Q ((f - Y.A0 - PiL X.dil Y.L) / Y.L) v w)
          ((f - Y.A0 - PiL X.dil Y.L) % Y.L) Y.c Y.l := by
        rw [ML_win hX hY (by omega) (by omega),
          phMsg_pk_win _ _ _ _ (by have := PiL_ge X.dil Y.L; omega) h1 h2 hg.L1]
      have hslot : ∀ s : Finset V, ∀ i, onlyPk (slotMsg s i Y.c Y.l) = slotMsg s i Y.c Y.l := by
        intro s i
        unfold slotMsg
        cases s.toList[i]? <;> rfl
      rw [hML, hslot]
      split_ifs with hkn
      · unfold pkFor
        simp only [loc]
        rw [lh_length, hc.dil, if_pos (And.intro h1 h2), pkLoc_eq hX hd hc hY h1 h2]
      · -- a node that does not know the phase has no packets
        symm
        unfold slotMsg
        rw [List.getElem?_eq_none]
        · rfl
        rw [Finset.length_toList]
        suffices hemp : pk X.E X.j Y.Q ((f - Y.A0 - PiL X.dil Y.L) / Y.L) v w = ∅ by
          rw [hemp, Finset.card_empty]; exact Nat.zero_le _
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        apply hkn
        generalize hhdef : (f - Y.A0 - PiL X.dil Y.L) / Y.L = h at hx
        have hhd : h < X.dil := by
          rw [← hhdef, Nat.div_lt_iff_lt_mul (by have := hg.L1; omega)]
          omega
        by_cases h0 : h = 0
        · rw [h0, pk_zero hX.hE hX.hj] at hx
          obtain ⟨rfl, hvQ, -⟩ := hx
          exact known_Q hX hd hc hY hvQ (by have := PiL_ge X.dil Y.L; omega)
        · obtain ⟨y, hy, -⟩ := (pk_relay hX.hE hX.hj _ _ (by omega) _ _ _).1 hx
          have hm := Finset.mem_toList.2 hy
          set s := (pk X.E X.j Y.Q (h - 1) y v).toList.idxOf x
          have hs : s < Y.L := by
            have := List.idxOf_lt_length_iff.2 hm
            rw [Finset.length_toList] at this
            exact lt_of_lt_of_le this ((card_pk_le _ _ _ _).trans hg.QL)
          have hhL1 : h * Y.L ≤ f - Y.A0 - PiL X.dil Y.L := by
            rw [← hhdef]; exact Nat.div_mul_le_self _ _
          have hhL2 : (h - 1) * Y.L + Y.L = h * Y.L := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
          have hhL3 : h * Y.L ≤ X.dil * Y.L := Nat.mul_le_mul_right _ hhd.le
          have hlt : Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s < f := by omega
          have hid := idOf_slot hX hY (v := v) (y := y) (h := h) (s := s) (by omega) hhd.le hs
          rw [List.getElem?_idxOf hm] at hid
          obtain ⟨m, hm', hmx⟩ : ∃ m, X.ML y v (Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s) =
              some m ∧ idOf (some m) = some x := by
            cases hmm : X.ML y v (Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s) with
            | none => rw [hmm] at hid; simp at hid
            | some m => rw [hmm] at hid; exact ⟨m, rfl, hid⟩
          rcases ML_shape hX y v (Y.A0 + PiL X.dil Y.L + (h - 1) * Y.L + s) with
            h' | h' | ⟨cc, h'⟩ | ⟨x', cc, l, h'⟩
          · rw [hm'] at h'; cases h'
          · rw [hm'] at h'; cases h'; simp [idOf, tokW] at hmx
          · rw [hm'] at h'; cases h'; simp [idOf, bcW] at hmx
          · obtain ⟨Y', hY', hw1, hw2, hk⟩ := known_R hX hd hc hlt h'
            have hsub' := win_sub hX hY'
            rwa [win_disj hX hY' hY hw1 hw2 (by omega) (by omega)] at hk
    · intro Z hZ hne
      rcases known_sound hX hd hc hZ with ⟨Y', hY', rfl, -, -⟩ | ⟨hB, -⟩
      · unfold pkFor at hne
        simp only [loc] at hne
        rw [lh_length, hc.dil] at hne
        split_ifs at hne with hw'
        · have hsub' := win_sub hX hY'
          have hle' : X.dil * Y'.L ≤ PiL X.dil Y'.L := by unfold PiL; nlinarith
          rw [win_disj hX hY' hY (φ := f) (by omega) (by omega) (by omega) (by omega)]
        · exact absurd rfl hne
      · exact absurd hB hctl
  · push_neg at hwin
    rw [head?_filterMap_none]
    · symm
      rcases ML_shape hX v w f with h' | h' | ⟨cc, h'⟩ | ⟨x, cc, l, h'⟩ <;> rw [h']
      · rfl
      · rfl
      · rfl
      · obtain ⟨Y, hY, h1, h2, -⟩ := (ML_pkW hX).1 h'
        exact absurd h2 (not_lt.2 (hwin Y hY h1))
    · intro Z hZ
      rcases known_sound hX hd hc hZ with ⟨Y', hY', rfl, -, -⟩ | ⟨hB, -⟩
      · unfold pkFor
        simp only [loc]
        rw [lh_length, hc.dil, if_neg]
        rintro ⟨h1, h2⟩
        exact absurd h2 (not_lt.2 (hwin Y' hY' h1))
      · exact absurd hB hctl

/-- **The messages of the controller are those of the schedule.** -/
theorem lsend_eq {f : ℕ} (hctl : ¬ X.LB v f) :
    lsend c d (X.lh v f) = fun w => X.ML v w f := by
  funext w
  show ((pcTokMsg (dilC c) d (X.lh v f) w <|> bcMsg c d (X.lh v f) w) <|> pkMsg c d (X.lh v f) w) = _
  rw [tokPart_eq hX hd hc hctl, bcPart_eq hX hd hc hctl, pkPart_eq hX hd hc hctl]
  exact (decomp3 _ (ML_shape hX v w f)).symm

/-- **Start of a sub-run**, at frame `bOf ℓ` in the footprint of `comp ℓ`. -/
theorem lstart_some (A : Type → Type) (inp : Agent V → Option Mem) {ℓ : V} (hℓ : ℓ ∈ X.lds)
    (hv : v ∈ footprint X.E X.j (X.comp ℓ)) :
    lstart A c inp d (X.lh v (X.bOf ℓ)) =
      some (ctxK c (X.comp ℓ).card, inpK A inp (decide (v ∈ X.comp ℓ)),
        decide (v ∈ X.comp ℓ)) := by
  classical
  have hY : IsPh X (X.kPh ℓ) := Or.inl ⟨ℓ, hℓ, rfl⟩
  have hg := isPh_gok hX hY
  have hkn : loc (X.kPh ℓ) v ∈ pcKnown c d (X.lh v (X.bOf ℓ)) := by
    refine known_fp hX hd hc hY hv ?_
    have : X.dil * (X.kPh ℓ).L ≤ PiL X.dil (X.kPh ℓ).L := by unfold PiL; nlinarith
    unfold bOf; rw [← kPh_Pi]; omega
  unfold lstart
  rw [lh_length, hc.dil]
  have hfind : (pcKnown c d (X.lh v (X.bOf ℓ))).find?
      (fun Z => decide (Z.c ≠ 0 ∧ Z.A0 + 2 * PiL X.dil Z.L = X.bOf ℓ)) =
      some (loc (X.kPh ℓ) v) := by
    have hc0 : (X.kPh ℓ).c ≠ 0 := by
      show (X.comp ℓ).card ≠ 0; have := comp_card_pos hX hℓ; omega
    have hsome : ((pcKnown c d (X.lh v (X.bOf ℓ))).find?
        (fun Z => decide (Z.c ≠ 0 ∧ Z.A0 + 2 * PiL X.dil Z.L = X.bOf ℓ))).isSome :=
      List.find?_isSome.2 ⟨loc (X.kPh ℓ) v, hkn, by
        simp only [decide_eq_true_eq]
        exact ⟨hc0, rfl⟩⟩
    obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hsome
    rw [hZ]
    have hpZ := List.find?_some hZ
    simp only [decide_eq_true_eq] at hpZ
    rcases known_sound hX hd hc (List.mem_of_find?_eq_some hZ) with
      ⟨Y', hY', rfl, -, -⟩ | ⟨-, h1, h2⟩
    · simp only [loc] at hpZ
      rcases hY' with ⟨ℓ', hℓ', rfl⟩ | rfl
      · have hb : X.bOf ℓ' = X.bOf ℓ := hpZ.2
        have hY' : IsPh X (X.kPh ℓ') := Or.inl ⟨ℓ', hℓ', rfl⟩
        have w1 := win_sub hX hY
        have w2 := win_sub hX hY'
        have hP := PiK_pos hX hℓ
        have hP' := PiK_pos hX hℓ'
        rw [ws_kPh hX hℓ, we_kPh hX hℓ, kPh_Pi] at w1
        rw [ws_kPh hX hℓ', we_kPh hX hℓ', kPh_Pi] at w2
        unfold bOf at hb
        have := win_disj hX hY' hY (φ := X.bOf ℓ - 1)
          (by rw [ws_kPh hX hℓ']; unfold bOf; omega)
          (by rw [we_kPh hX hℓ']; unfold bOf; omega)
          (by rw [ws_kPh hX hℓ]; unfold bOf; omega)
          (by rw [we_kPh hX hℓ]; unfold bOf; omega)
        rw [this]
      · simp [ePh] at hpZ
    · exfalso
      have : 0 < PiL X.dil Z.L := by unfold PiL; exact Nat.mul_pos (Nat.succ_pos _) (by omega)
      omega
  rw [hfind]
  rfl

/-- **No other starts.** -/
theorem lstart_none (A : Type → Type) (inp : Agent V → Option Mem) {f : ℕ}
    (hno : ∀ ℓ ∈ X.lds, v ∈ footprint X.E X.j (X.comp ℓ) → X.bOf ℓ ≠ f) :
    lstart A c inp d (X.lh v f) = none := by
  classical
  unfold lstart
  rw [lh_length, hc.dil]
  have : (pcKnown c d (X.lh v f)).find?
      (fun Z => decide (Z.c ≠ 0 ∧ Z.A0 + 2 * PiL X.dil Z.L = f)) = none := by
    rw [List.find?_eq_none]
    intro Z hZ hp
    simp only [decide_eq_true_eq] at hp
    rcases known_sound hX hd hc hZ with ⟨Y', hY', rfl, hfp, -⟩ | ⟨-, h1, h2⟩
    · simp only [loc] at hp
      rcases hY' with ⟨ℓ', hℓ', rfl⟩ | rfl
      · exact hno ℓ' hℓ' hfp hp.2
      · simp [ePh] at hp
    · have : 0 < PiL X.dil Z.L := by unfold PiL; exact Nat.mul_pos (Nat.succ_pos _) (by omega)
      omega
  rw [this]

/-- **Halting** exactly at `TL`. -/
theorem lhalt_iff (hv : v ∈ footprint X.E X.j X.P) {f : ℕ} (hf : f ≤ X.TL) :
    lhalt c d (X.lh v f) = true ↔ f = X.TL := by
  classical
  unfold lhalt
  rw [lh_length, hc.dil, List.any_eq_true]
  constructor
  · rintro ⟨Z, hZ, hp⟩
    simp only [decide_eq_true_eq] at hp
    rcases known_sound hX hd hc hZ with ⟨Y', hY', rfl, -, -⟩ | ⟨-, h1, h2⟩
    · simp only [loc] at hp
      rcases hY' with ⟨ℓ', hℓ', rfl⟩ | rfl
      · have := comp_card_pos hX hℓ'
        simp only [kPh] at hp; omega
      · rw [← hp.2]; rfl
    · have : 0 < PiL X.dil Z.L := by unfold PiL; exact Nat.mul_pos (Nat.succ_pos _) (by omega)
      omega
  · rintro rfl
    have hY : IsPh X X.ePh := Or.inr rfl
    refine ⟨loc X.ePh v, known_fp hX hd hc hY hv ?_, ?_⟩
    · have : X.dil * X.ePh.L ≤ PiL X.dil X.ePh.L := by unfold PiL; nlinarith
      unfold TL; simp only [ePh] at this ⊢; omega
    · simp [loc, ePh, TL]

end PCG

end APSP.Stoc.Congest
