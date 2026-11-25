import ApspStoc.Congest.PerCompHist

/-!
# The token rule follows the traversal (for `perCompR`)

`tokAct_seg`, `tokAct_end`, `tokAct_idle`: in every frame in which a node is not in a sub-run,
its token action (`tokAct`, computed from its history) is the one of the global traversal: it
performs the segment starting in that frame if the segment is its own (sends the token, or starts
its phase), the root starts the final phase at `E0`, and otherwise the node does nothing.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the node holding the token at the start of a segment -/
def TSg.src {V : Type} : TSg V → V
  | .tk u _ => u
  | .ph l => l

/-- the token action of a segment -/
def TSg.act {V : Type} : TSg V → TA V
  | .tk _ w => .send w
  | .ph _ => .startK

/-- the token action of the next segment (`none`: the end) -/
def toTA {V : Type} : Option (TSg V) → TA V
  | some x => x.act
  | none => .startE

namespace PCG

variable {X : PCG V} (hX : X.OK)
include hX

/-! ## The traversal and the local rule -/

lemma root_unique {v : V} (hv : v ∈ X.P) (hp : X.parP v = none) : v = X.r := by
  have h := hX.Pdesc ▸ hv
  rw [mem_desc] at h
  rcases ReflTransGen.cases_head_iff.1 h.2 with h' | ⟨c, hc, -⟩
  · exact h'
  · simp [PR, hp] at hc

lemma tl_head : X.tl.head? = startA X.P X.parP X.isL X.r := by
  rcases (tl_ok hX).head with h | ⟨h1, h2⟩
  · exact h
  · unfold tl; rw [h1, h2]; simp [upA, hX.parr]

lemma tl_succ {k : ℕ} (hk : k + 1 < X.tl.length) :
    nxt X.P X.parP X.isL X.tl[k] = some X.tl[k + 1] :=
  (tl_ok hX).chain.getElem k hk

lemma tl_last {k : ℕ} (hk : k < X.tl.length) (hk1 : k + 1 = X.tl.length) :
    nxt X.P X.parP X.isL X.tl[k] = none := by
  have h := (tl_ok hX).last
  have hz : X.tl[k] ∈ X.tl.getLast? := by
    rw [List.getLast?_eq_getElem?, show X.tl.length - 1 = k by omega,
      List.getElem?_eq_getElem hk]; rfl
  rw [h _ hz]
  simp [upA, hX.parr]

omit hX in
lemma upA_src {v : V} {x : TSg V} (h : upA X.parP v = some x) : x.src = v ∧ ∃ w, x = .tk v w := by
  unfold upA at h
  cases hp : X.parP v with
  | none => rw [hp] at h; simp at h
  | some p => rw [hp] at h; simp at h; subst h; exact ⟨rfl, p, rfl⟩

omit hX in
lemma aParA_src {v : V} {x : TSg V} (h : aParA X.P X.parP v = some x) :
    x.src = v ∧ ∃ w, x = .tk v w := by
  unfold aParA at h
  split at h
  · simp at h; subst h; exact ⟨rfl, _, rfl⟩
  · exact upA_src h

omit hX in
lemma aKidA_src {v c : V} {x : TSg V} (h : aKidA X.P X.parP v c = some x) :
    x.src = v ∧ ∃ w, x = .tk v w := by
  unfold aKidA at h
  split at h
  · simp at h; subst h; exact ⟨rfl, _, rfl⟩
  · exact upA_src h

omit hX in
lemma nxt_src {z x : TSg V} (h : nxt X.P X.parP X.isL z = some x) : x.src = z.tgt := by
  cases z with
  | tk u v =>
    simp only [nxt] at h
    split_ifs at h
    · simp at h; subst h; rfl
    · exact (aParA_src h).1
    · exact (aKidA_src h).1
  | ph v => exact (aParA_src h).1

omit hX in
lemma nxt_ph {z : TSg V} {w : V} (h : nxt X.P X.parP X.isL z = some (.ph w)) :
    ∃ u, z = .tk u w ∧ X.parP w = some u := by
  cases z with
  | tk u v =>
    simp only [nxt] at h
    split_ifs at h with h1
    · simp at h; subst h; exact ⟨u, rfl, h1⟩
    · obtain ⟨-, w', hw'⟩ := aParA_src h; cases hw'
    · obtain ⟨-, w', hw'⟩ := aKidA_src h; cases hw'
  | ph v => obtain ⟨-, w', hw'⟩ := aParA_src h; cases hw'

/-- The predecessor of the phase of a leader: the token move from its parent, or the start. -/
lemma ph_pred {ℓ : V} (hℓ : ℓ ∈ X.lds) {k : ℕ} (hk : k < X.tl.length) (h : X.tl[k] = .ph ℓ) :
    (k = 0 ∧ ℓ = X.r) ∨ (0 < k ∧ ∃ p, X.tl[k - 1] = .tk p ℓ ∧ X.parP ℓ = some p) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · left
    refine ⟨rfl, ?_⟩
    have h1 := tl_head hX
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk, h] at h1
    unfold startA at h1
    split_ifs at h1
    · simp at h1; exact h1
    · obtain ⟨-, w, hw⟩ := aParA_src h1.symm; cases hw
  · right
    refine ⟨hk0, ?_⟩
    have h1 := tl_succ hX (k := k - 1) (by omega)
    simp only [show k - 1 + 1 = k by omega, h] at h1
    obtain ⟨u, hu, hp⟩ := nxt_ph h1
    exact ⟨u, hu, hp⟩

/-! ## Local data -/

variable {v : V} {d : LD V} (hd : X.LDOK d v)
include hd

lemma isLd_iff : isLd d ↔ v ∈ X.lds := by
  rw [mem_lds]; unfold isLd; rw [hd.bS, hd.parS]; simp

lemma isRoot_iff : (d.bP = true ∧ d.parP = none) ↔ v = X.r := by
  rw [hd.bP, hd.parP]
  constructor
  · rintro ⟨h1, h2⟩; exact root_unique hX (by simpa using h1) h2
  · rintro rfl; exact ⟨by simpa using hX.rP, hX.parr⟩

omit hX in
lemma upT_eq : upT d = toTA (upA X.parP v) := by
  unfold upT upA; rw [hd.parP]
  cases X.parP v <;> rfl

omit hX in
lemma aPar_eq : aPar d = toTA (aParA X.P X.parP v) := by
  unfold aPar aParA kl; rw [hd.kP]
  split <;> simp_all [toTA, TSg.act, upT_eq hd]

omit hX in
lemma aKid_eq (c : V) : aKid d c = toTA (aKidA X.P X.parP v c) := by
  unfold aKid aKidA kl; rw [hd.kP]
  split <;> simp_all [toTA, TSg.act, upT_eq hd]

lemma fromPar_iff {f ψ : ℕ} : fromPar d (X.lh v f) ψ ↔ (ψ = 0 ∧ v = X.r) ∨
    (ψ < f ∧ ∃ p, X.parP v = some p ∧ ∃ k, ∃ _ : k < X.tl.length, X.tl[k] = .tk p v ∧ X.stF k = ψ) := by
  unfold fromPar
  constructor
  · rintro (⟨h0, h1, h2⟩ | ⟨h1, h2, h3⟩)
    · left; exact ⟨h0, (isRoot_iff hX hd).1 ⟨h1, h2⟩⟩
    · right
      rw [hd.parP] at h2 h3
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 h2
      rw [hp] at h3
      obtain ⟨hψ, k, hk, h4, h5⟩ := tokS_lh_spec hX h3
      exact ⟨hψ, p, hp, k, hk, h4, h5⟩
  · rintro (⟨h0, rfl⟩ | ⟨hψ, p, hp, k, hk, h4, h5⟩)
    · left; exact ⟨h0, (isRoot_iff hX hd).2 rfl⟩
    · right
      have hvP : v ∈ X.P := by
        rcases (tk_mem_tl hX).1 (h4 ▸ List.getElem_mem hk) with h | h
        · exact h.1
        · exact hX.Pmem p h.1 v h.2
      refine ⟨by rw [hd.bP]; simpa using hvP, by rw [hd.parP, hp]; simp, ?_⟩
      rw [hd.parP, hp]
      exact tokS_lh_some hX hψ hk h4 h5

omit hd in
/-- The frames of a leader's sub-run. -/
lemma LB_own {ℓ : V} (hℓ : ℓ ∈ X.lds) (hv : v ∈ footprint X.E X.j (X.comp ℓ)) {χ : ℕ}
    (h1 : X.bOf ℓ ≤ χ) (h2 : χ < X.phEnd ℓ (X.aOf ℓ)) : X.LB v χ := by
  rw [phEnd_eq] at h2
  exact ⟨ℓ, hℓ, hv, h1, by omega⟩

omit hd in
/-- A frame starting a token move is not a sub-run frame. -/
lemma not_LB_tok {k : ℕ} (hk : k < X.tl.length) {a b : V} (h : X.tl[k] = .tk a b) (w : V) :
    ¬ X.LB w (X.stF k) := by
  rintro ⟨ℓ, hℓ, -, h1, h2⟩
  have hY : IsPh X (X.kPh ℓ) := Or.inl ⟨ℓ, hℓ, rfl⟩
  refine tok_not_win hX hk h hY ⟨?_, ?_⟩
  · have := win_sub hX hY; unfold bOf at h1; omega
  · rw [we_kPh hX hℓ, phEnd_eq]; omega

omit hd in
lemma not_LB_E0 (w : V) : ¬ X.LB w X.E0 := by
  rintro ⟨ℓ, hℓ, -, h1, h2⟩
  obtain ⟨i, hi, h⟩ := exists_ph hX hℓ
  have := stF_ph hX hi h
  have := stF_le hX (show i + 1 ≤ X.tl.length by omega) le_rfl
  rw [phEnd_eq] at *
  unfold E0 at h1 h2
  omega

omit hd in
/-- The end of a leader's phase is not a sub-run frame. -/
lemma not_LB_end {ℓ : V} (hℓ : ℓ ∈ X.lds) (w : V) : ¬ X.LB w (X.phEnd ℓ (X.aOf ℓ)) := by
  obtain ⟨k, hk, h⟩ := exists_ph hX hℓ
  rw [← stF_ph hX hk h]
  by_cases hk1 : k + 1 < X.tl.length
  · have hn := tl_succ hX hk1
    rw [h] at hn
    obtain ⟨-, w', hw'⟩ := aParA_src hn
    exact not_LB_tok hX hk1 hw' w
  · rw [show k + 1 = X.tl.length by omega]
    exact not_LB_E0 hX w

lemma ruleC_iff {f : ℕ} (hf : 1 ≤ f) (hctl : ¬ X.LB v f) :
    (isLd d ∧ ∃ ψ < f, fromPar d (X.lh v f) ψ ∧ phBL X.dil (ψ + 1) d.cnt ≤ f ∧
      ∀ χ, phBL X.dil (ψ + 1) d.cnt ≤ χ → χ < f → (X.lh v f).getD χ none = none) ↔
    (v ∈ X.lds ∧ f = X.phEnd v (X.aOf v)) := by
  rw [isLd_iff hX hd]
  constructor
  · rintro ⟨hℓ, ψ, hψ, hfp, hb, hall⟩
    refine ⟨hℓ, ?_⟩
    obtain ⟨k, hk, h⟩ := exists_ph hX hℓ
    have hvS := (mem_lds.1 hℓ).1
    have hcnt : d.cnt = (X.comp v).card := by
      rw [hd.cnt hvS, hX.Sself v hvS (mem_lds.1 hℓ).2]
    -- the first visit
    have hψa : ψ + 1 = X.aOf v := by
      rw [aOf_eq hX hk h]
      rcases (fromPar_iff hX hd).1 hfp with ⟨rfl, rfl⟩ | ⟨-, p, hp, k', hk', h', rfl⟩
      · rcases ph_pred hX hℓ hk h with ⟨rfl, -⟩ | ⟨-, p, -, hp⟩
        · rw [stF_zero]
        · rw [hX.parr] at hp; simp at hp
      · rcases ph_pred hX hℓ hk h with ⟨rfl, rfl⟩ | ⟨hk0, p', h'', hp'⟩
        · rw [hX.parr] at hp; simp at hp
        · have := List.nodup_iff_injective_getElem.1 (tl_nodup hX)
          have hkk : k' = k - 1 := by
            rw [hp] at hp'; cases hp'
            exact this (a₁ := ⟨k', hk'⟩) (a₂ := ⟨k - 1, by omega⟩) (h'.trans h''.symm)
              |> congrArg Fin.val
          subst hkk
          have := stF_tk hX (show k - 1 < X.tl.length by omega) h''
          rw [show k - 1 + 1 = k by omega] at this
          omega
    have hbv : phBL X.dil (ψ + 1) d.cnt = X.bOf v := by
      rw [hψa, hcnt]; rfl
    rw [hbv] at hb hall
    have hvfp : v ∈ footprint X.E X.j (X.comp v) :=
      subset_footprint _ _ _ (self_mem_comp hX hℓ)
    rcases lt_trichotomy f (X.phEnd v (X.aOf v)) with hlt | heq | hgt
    · exact absurd (LB_own hX hℓ hvfp hb hlt) hctl
    · exact heq
    · have := hall _ (by rw [phEnd_eq]; omega) hgt
      rw [lh_getD X v hgt, if_neg (not_LB_end hX hℓ v)] at this
      simp at this
  · rintro ⟨hℓ, rfl⟩
    refine ⟨hℓ, X.aOf v - 1, ?_⟩
    obtain ⟨k, hk, h⟩ := exists_ph hX hℓ
    have hvS := (mem_lds.1 hℓ).1
    have hcnt : d.cnt = (X.comp v).card := by
      rw [hd.cnt hvS, hX.Sself v hvS (mem_lds.1 hℓ).2]
    have ha1 : 1 ≤ X.aOf v := by rw [aOf_eq hX hk h]; exact one_le_stF hX hk.le
    have hend := phEnd_ge hX hℓ (X.aOf v)
    have hP := PiK_pos hX hℓ
    have hbv : phBL X.dil (X.aOf v - 1 + 1) d.cnt = X.bOf v := by
      rw [show X.aOf v - 1 + 1 = X.aOf v by omega, hcnt]; rfl
    refine ⟨by omega, ?_, by rw [hbv, phEnd_eq]; omega, ?_⟩
    · rw [fromPar_iff hX hd]
      rcases ph_pred hX hℓ hk h with ⟨rfl, rfl⟩ | ⟨hk0, p, h', hp⟩
      · left
        refine ⟨?_, rfl⟩
        rw [aOf_eq hX hk h, stF_zero]
      · right
        refine ⟨by omega, p, hp, k - 1, by omega, h', ?_⟩
        rw [aOf_eq hX hk h]
        have := stF_tk hX (show k - 1 < X.tl.length by omega) h'
        rw [show k - 1 + 1 = k by omega] at this
        omega
    · intro χ h1 h2
      rw [hbv] at h1
      rw [lh_getD X v h2, if_pos (LB_own hX hℓ (subset_footprint _ _ _ (self_mem_comp hX hℓ))
        h1 h2)]

open Classical in
/-- **The token rule** in a frame `f ≥ 1` in which `v` is not in a sub-run: the action is the one of
the segment starting in `f` (if it is `v`'s), the start of the final phase (the root at `E0`), or
nothing. -/
theorem tokAct_eq {f : ℕ} (hf : 1 ≤ f) (hctl : ¬ X.LB v f) :
    tokAct X.dil d (X.lh v f) =
      if h : ∃ k < X.tl.length, X.stF k = f then
        (if (X.tl[h.choose]'h.choose_spec.1).src = v then (X.tl[h.choose]'h.choose_spec.1).act
          else .idle)
      else if v = X.r ∧ f = X.E0 then .startE else .idle := by
  classical
  -- the segment starting in `f`, if any
  have hseg : ∀ k (hk : k < X.tl.length), X.stF k = f →
      (if h : ∃ k < X.tl.length, X.stF k = f then
        (if (X.tl[h.choose]'h.choose_spec.1).src = v then (X.tl[h.choose]'h.choose_spec.1).act
          else .idle)
      else if v = X.r ∧ f = X.E0 then .startE else .idle) =
        if X.tl[k].src = v then X.tl[k].act else .idle := by
    intro k hk hs
    have hex : ∃ k < X.tl.length, X.stF k = f := ⟨k, hk, hs⟩
    rw [dif_pos hex]
    have hc := hex.choose_spec
    have : hex.choose = k := by
      rcases lt_trichotomy hex.choose k with h | h | h
      · have := stF_lt hX h hk.le; omega
      · exact h
      · have := stF_lt hX h hc.1.le; omega
    have e : ∀ (i : ℕ) (hi : i < X.tl.length), i = k → X.tl[i] = X.tl[k] := by
      intro i hi hik; subst hik; rfl
    rw [e _ _ this]
  have hnoseg : (∀ k < X.tl.length, X.stF k ≠ f) →
      (if h : ∃ k < X.tl.length, X.stF k = f then
        (if (X.tl[h.choose]'h.choose_spec.1).src = v then (X.tl[h.choose]'h.choose_spec.1).act
          else .idle)
      else if v = X.r ∧ f = X.E0 then .startE else .idle) =
        if v = X.r ∧ f = X.E0 then .startE else .idle := by
    intro hno
    rw [dif_neg (fun ⟨k, hk, hs⟩ => hno k hk hs)]
  have hlen := lh_length X v f
  unfold tokAct
  rw [hlen]
  by_cases htok : ∃ u, tokS (X.lh v f) (f - 1) = some u
  · -- a token was received in frame `f - 1`
    obtain ⟨u, hu⟩ := htok
    obtain ⟨-, k, hk, hku, hks⟩ := tokS_lh_spec hX hu
    have hk1f : X.stF (k + 1) = f := by rw [stF_tk hX hk hku]; have := one_le_stF hX hk.le; omega
    have hf2 : 2 ≤ f := by have := one_le_stF hX hk.le; omega
    rcases (tk_mem_tl hX).1 (hku ▸ List.getElem_mem hk) with ⟨hvP, hpv⟩ | ⟨huP, hpu⟩
    · -- from the parent
      have hfp : fromPar d (X.lh v f) (f - 1) :=
        (fromPar_iff hX hd).2 (Or.inr ⟨by omega, u, hpv, k, hk, hku, hks⟩)
      rw [if_pos ⟨hf, hfp⟩]
      have hn : nxt X.P X.parP X.isL (TSg.tk u v) =
          if X.isL v then some (.ph v) else aParA X.P X.parP v := by
        simp only [nxt, hpv, ite_true]
      have hk1 : k + 1 < X.tl.length := by
        by_contra hge
        have := tl_last hX hk (by omega)
        rw [hku, hn] at this
        by_cases hL : X.isL v = true
        · rw [if_pos hL] at this; exact absurd this (by simp)
        · rw [if_neg hL] at this
          unfold aParA at this
          split at this
          · simp at this
          · simp [upA, hpv] at this
      rw [hseg (k + 1) hk1 hk1f]
      have hs := tl_succ hX hk1
      rw [hku, hn] at hs
      have hsrc : X.tl[k + 1].src = v := by
        exact nxt_src (X := X) (z := TSg.tk u v) (by rw [hn]; exact hs)
      rw [if_pos hsrc]
      by_cases hL : X.isL v = true
      · rw [if_pos hL] at hs
        rw [if_pos ((isLd_iff hX hd).2 (isL_iff.1 hL)), ← Option.some.inj hs]
        rfl
      · rw [if_neg hL] at hs
        rw [if_neg (fun h => hL (isL_iff.2 ((isLd_iff hX hd).1 h))), aPar_eq hd, hs]
        rfl
    · -- from a child
      have hne : X.parP v ≠ some u := by
        intro h
        have := hX.Prk u huP v hpu
        have := hX.Prk v (hX.Pmem u huP v hpu) u h
        omega
      have hnfp : ¬ fromPar d (X.lh v f) (f - 1) := by
        rw [fromPar_iff hX hd]
        rintro (⟨h0, -⟩ | ⟨-, p, hp, k', hk', h', hs'⟩)
        · omega
        · have := tok_unique hX hk hk' hku h' (hks.trans hs'.symm)
          subst this
          rw [hku] at h'; cases h'
          exact hne hp
      rw [if_neg (fun h => hnfp h.2), if_pos hf, hu]
      dsimp only
      have hukP : u ∈ d.kP := by rw [hd.kP, mem_kidsOf]; exact ⟨huP, hpu⟩
      rw [if_pos hukP, aKid_eq hd]
      have hn : nxt X.P X.parP X.isL (TSg.tk u v) = aKidA X.P X.parP v u := by
        simp only [nxt, hne, ite_false]
      by_cases hk1 : k + 1 < X.tl.length
      · rw [hseg (k + 1) hk1 hk1f]
        have hs := tl_succ hX hk1
        rw [hku, hn] at hs
        have hsrc : X.tl[k + 1].src = v := (aKidA_src hs).1
        rw [if_pos hsrc, hs]
        rfl
      · have hlast := tl_last hX hk (by omega)
        rw [hku, hn] at hlast
        rw [hlast]
        have hvr : v = X.r := by
          have hvP := hX.Pmem u huP v hpu
          unfold aKidA at hlast
          split at hlast
          · simp at hlast
          · unfold upA at hlast
            cases hp : X.parP v with
            | none => exact root_unique hX hvP hp
            | some p => rw [hp] at hlast; simp at hlast
        have hfE : f = X.E0 := by unfold E0; rw [← hk1f, show k + 1 = X.tl.length by omega]
        rw [hnoseg (fun k' hk' hs' => by have := stF_lt hX hk' le_rfl; unfold E0 at hfE; omega),
          if_pos ⟨hvr, hfE⟩]
        rfl
  · -- no token received in frame `f - 1`
    push_neg at htok
    have hnone : tokS (X.lh v f) (f - 1) = none := by
      cases h : tokS (X.lh v f) (f - 1) with
      | none => rfl
      | some u => exact absurd h (htok u)
    have hnorecv : ∀ k (_ : k < X.tl.length) u, X.tl[k] = .tk u v → X.stF k ≠ f - 1 := by
      intro k hk u h hs
      have := tokS_lh_some hX (show f - 1 < f by omega) hk h hs
      rw [hnone] at this; simp at this
    by_cases hvirt : f = 1 ∧ v = X.r
    · obtain ⟨rfl, rfl⟩ := hvirt
      have hfp : fromPar d (X.lh X.r 1) (1 - 1) := (fromPar_iff hX hd).2 (Or.inl ⟨rfl, rfl⟩)
      rw [if_pos ⟨le_rfl, hfp⟩]
      have hh := tl_head hX
      by_cases hl : 0 < X.tl.length
      · rw [hseg 0 hl (stF_zero)]
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hl] at hh
        unfold startA at hh
        by_cases hL : X.isL X.r = true
        · rw [if_pos hL] at hh
          rw [Option.some.inj hh, if_pos (show (TSg.ph X.r).src = X.r from rfl),
            if_pos ((isLd_iff hX hd).2 (isL_iff.1 hL))]
          rfl
        · rw [if_neg hL] at hh
          rw [if_neg (fun h => hL (isL_iff.2 ((isLd_iff hX hd).1 h))), aPar_eq hd, ← hh,
            if_pos (aParA_src hh.symm).1]
          rfl
      · have hl0 : X.tl.length = 0 := by omega
        rw [hnoseg (fun k hk => absurd hk (by omega)),
          if_pos (show X.r = X.r ∧ 1 = X.E0 from ⟨rfl, by unfold E0; rw [hl0, stF_zero]⟩)]
        rw [List.length_eq_zero_iff.1 hl0] at hh
        unfold startA at hh
        by_cases hL : X.isL X.r = true
        · rw [if_pos hL] at hh; exact absurd hh (by simp)
        · rw [if_neg hL] at hh
          rw [if_neg (fun h => hL (isL_iff.2 ((isLd_iff hX hd).1 h))), aPar_eq hd, ← hh]
          rfl
    · have hnfp : ¬ fromPar d (X.lh v f) (f - 1) := by
        rw [fromPar_iff hX hd]
        rintro (⟨h0, rfl⟩ | ⟨-, p, -, k, hk, h, hs⟩)
        · exact hvirt ⟨by omega, rfl⟩
        · exact hnorecv k hk p h hs
      rw [if_neg (fun h => hnfp h.2), if_pos hf, hnone]
      dsimp only
      by_cases hRC : v ∈ X.lds ∧ f = X.phEnd v (X.aOf v)
      · obtain ⟨hℓ, hfe⟩ := hRC
        rw [if_pos ((ruleC_iff hX hd hf hctl).2 ⟨hℓ, hfe⟩), aPar_eq hd]
        obtain ⟨k, hk, h⟩ := exists_ph hX hℓ
        have hk1f : X.stF (k + 1) = f := by rw [stF_ph hX hk h, hfe]
        by_cases hk1 : k + 1 < X.tl.length
        · rw [hseg (k + 1) hk1 hk1f]
          have hs := tl_succ hX hk1
          rw [h] at hs
          simp only [nxt] at hs
          rw [if_pos (aParA_src hs).1, hs]
          rfl
        · have hlast := tl_last hX hk (by omega)
          rw [h] at hlast
          simp only [nxt] at hlast
          rw [hlast]
          have hvr : v = X.r := by
            have hvP := comp_sub_P hX v (self_mem_comp hX hℓ)
            unfold aParA at hlast
            split at hlast
            · simp at hlast
            · unfold upA at hlast
              cases hp : X.parP v with
              | none => exact root_unique hX hvP hp
              | some p => rw [hp] at hlast; simp at hlast
          have hfE : f = X.E0 := by unfold E0; rw [← hk1f, show k + 1 = X.tl.length by omega]
          rw [hnoseg (fun k' hk' hs' => by have := stF_lt hX hk' le_rfl; unfold E0 at hfE; omega),
            if_pos (show v = X.r ∧ f = X.E0 from ⟨hvr, hfE⟩)]
          rfl
      · rw [if_neg (fun h => hRC ((ruleC_iff hX hd hf hctl).1 h))]
        by_cases hex : ∃ k < X.tl.length, X.stF k = f
        · obtain ⟨k, hk, hs⟩ := hex
          rw [hseg k hk hs]
          by_cases hsrc : X.tl[k].src = v
          · exfalso
            rcases Nat.eq_zero_or_pos k with rfl | hk0
            · have hh := tl_head hX
              rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk] at hh
              have : X.tl[0].src = X.r := by
                unfold startA at hh
                split_ifs at hh
                · rw [Option.some.inj hh]; rfl
                · exact (aParA_src hh.symm).1
              rw [stF_zero] at hs
              exact hvirt ⟨hs.symm, hsrc.symm.trans this⟩
            · have hn := tl_succ hX (k := k - 1) (by omega)
              simp only [show k - 1 + 1 = k by omega] at hn
              have htg := nxt_src hn
              rw [hsrc] at htg
              cases hz : X.tl[k - 1] with
              | tk a b =>
                rw [hz] at htg
                simp only [TSg.tgt] at htg
                subst htg
                have := stF_tk hX (show k - 1 < X.tl.length by omega) hz
                rw [show k - 1 + 1 = k by omega] at this
                exact hnorecv (k - 1) (by omega) a hz (by omega)
              | ph ℓ =>
                rw [hz] at htg
                simp only [TSg.tgt] at htg
                have hℓ : ℓ ∈ X.lds := (ph_mem_tl hX).1 (hz ▸ List.getElem_mem (by omega))
                have := stF_ph hX (show k - 1 < X.tl.length by omega) hz
                rw [show k - 1 + 1 = k by omega] at this
                rw [htg] at hRC
                exact hRC ⟨hℓ, by rw [← this, hs]⟩
          · rw [if_neg hsrc]
        · push_neg at hex
          rw [hnoseg hex]
          by_cases hE : v = X.r ∧ f = X.E0
          · exfalso
            obtain ⟨rfl, rfl⟩ := hE
            by_cases hl : 0 < X.tl.length
            · have hlast := tl_last hX (k := X.tl.length - 1) (by omega) (by omega)
              cases hz : X.tl[X.tl.length - 1] with
              | tk a b =>
                rw [hz] at hlast
                have hb : b = X.r := by
                  simp only [nxt] at hlast
                  by_cases h1 : X.parP b = some a
                  · exfalso
                    rw [if_pos h1] at hlast
                    by_cases hL : X.isL b = true
                    · rw [if_pos hL] at hlast; exact absurd hlast (by simp)
                    · rw [if_neg hL] at hlast
                      unfold aParA at hlast
                      split at hlast
                      · simp at hlast
                      · simp [upA, h1] at hlast
                  · rw [if_neg h1] at hlast
                    have hbP : b ∈ X.P := by
                      rcases (tk_mem_tl hX).1 (hz ▸ List.getElem_mem (by omega)) with h | h
                      · exact h.1
                      · exact hX.Pmem a h.1 b h.2
                    unfold aKidA at hlast
                    split at hlast
                    · simp at hlast
                    · unfold upA at hlast
                      cases hp : X.parP b with
                      | none => exact root_unique hX hbP hp
                      | some p => rw [hp] at hlast; simp at hlast
                subst hb
                have := stF_tk hX (show X.tl.length - 1 < X.tl.length by omega) hz
                rw [show X.tl.length - 1 + 1 = X.tl.length by omega] at this
                exact hnorecv _ (by omega) a hz (by unfold E0; omega)
              | ph ℓ =>
                rw [hz] at hlast
                have hℓ : ℓ ∈ X.lds := (ph_mem_tl hX).1 (hz ▸ List.getElem_mem (by omega))
                have hlr : ℓ = X.r := by
                  have hlP := comp_sub_P hX ℓ (self_mem_comp hX hℓ)
                  simp only [nxt] at hlast
                  unfold aParA at hlast
                  split at hlast
                  · simp at hlast
                  · unfold upA at hlast
                    cases hp : X.parP ℓ with
                    | none => exact root_unique hX hlP hp
                    | some p => rw [hp] at hlast; simp at hlast
                subst hlr
                have := stF_ph hX (show X.tl.length - 1 < X.tl.length by omega) hz
                rw [show X.tl.length - 1 + 1 = X.tl.length by omega] at this
                exact hRC ⟨hℓ, this⟩
            · exact hvirt ⟨by unfold E0; rw [show X.tl.length = 0 by omega, stF_zero], rfl⟩
          · rw [if_neg hE]

lemma tokAct_seg {f : ℕ} (hf : 1 ≤ f) (hctl : ¬ X.LB v f) {k : ℕ} (hk : k < X.tl.length)
    (hs : X.stF k = f) :
    tokAct X.dil d (X.lh v f) = if X.tl[k].src = v then X.tl[k].act else .idle := by
  classical
  rw [tokAct_eq hX hd hf hctl]
  have hex : ∃ k < X.tl.length, X.stF k = f := ⟨k, hk, hs⟩
  rw [dif_pos hex]
  have hc := hex.choose_spec
  have : hex.choose = k := by
    rcases lt_trichotomy hex.choose k with h | h | h
    · have := stF_lt hX h hk.le; omega
    · exact h
    · have := stF_lt hX h hc.1.le; omega
  have e : ∀ (i : ℕ) (hi : i < X.tl.length), i = k → X.tl[i] = X.tl[k] := by
    intro i hi hik; subst hik; rfl
  rw [e _ _ this]

lemma tokAct_noseg {f : ℕ} (hf : 1 ≤ f) (hctl : ¬ X.LB v f)
    (hno : ∀ k < X.tl.length, X.stF k ≠ f) :
    tokAct X.dil d (X.lh v f) = if v = X.r ∧ f = X.E0 then .startE else .idle := by
  classical
  rw [tokAct_eq hX hd hf hctl, dif_neg (fun ⟨k, hk, hs⟩ => hno k hk hs)]

omit hd in
lemma stF_inj {k k' : ℕ} (hk : k < X.tl.length) (hk' : k' < X.tl.length)
    (h : X.stF k = X.stF k') : k = k' := by
  rcases lt_trichotomy k k' with hl | rfl | hl
  · have := stF_lt hX hl hk'.le; omega
  · rfl
  · have := stF_lt hX hl hk.le; omega

/-- **Token moves** of the local rule are those of the traversal. -/
lemma tokAct_send {f : ℕ} (hctl : ¬ X.LB v f) (w : V) :
    tokAct X.dil d (X.lh v f) = .send w ↔ ∃ k, ∃ _ : k < X.tl.length, X.tl[k] = .tk v w ∧ X.stF k = f := by
  classical
  by_cases h0 : f = 0
  · subst h0
    have : tokAct X.dil d (X.lh v 0) = .idle := by
      unfold tokAct; rw [lh_length]; simp
    rw [this]
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro k hk _ hs
    have := one_le_stF hX hk.le
    omega
  by_cases hex : ∃ k < X.tl.length, X.stF k = f
  · obtain ⟨k, hk, hs⟩ := hex
    rw [tokAct_seg hX hd (by omega) hctl hk hs]
    constructor
    · intro h
      cases hx : X.tl[k] with
      | tk a b =>
        rw [hx] at h
        by_cases ha : a = v
        · rw [if_pos (show (TSg.tk a b).src = v from ha)] at h
          have hb : b = w := by simpa [TSg.act] using h
          subst ha; subst hb; exact ⟨k, hk, hx, hs⟩
        · rw [if_neg (show ¬ (TSg.tk a b).src = v from ha)] at h; exact absurd h (by simp)
      | ph ℓ =>
        rw [hx] at h
        by_cases ha : ℓ = v
        · rw [if_pos (show (TSg.ph ℓ).src = v from ha)] at h; exact absurd h (by simp [TSg.act])
        · rw [if_neg (show ¬ (TSg.ph ℓ).src = v from ha)] at h; exact absurd h (by simp)
    · rintro ⟨k', hk', h', hs'⟩
      have := stF_inj hX hk' hk (hs'.trans hs.symm)
      subst this
      rw [h']
      simp [TSg.src, TSg.act]
  · push_neg at hex
    rw [tokAct_noseg hX hd (by omega) hctl hex]
    constructor
    · intro h; split_ifs at h
    · rintro ⟨k, hk, -, hs⟩; exact absurd hs (hex k hk)

/-- **Phase starts** of the local rule are those of the traversal. -/
lemma tokAct_startK {f : ℕ} (hctl : ¬ X.LB v f) :
    tokAct X.dil d (X.lh v f) = .startK ↔ ∃ k, ∃ _ : k < X.tl.length, X.tl[k] = .ph v ∧ X.stF k = f := by
  classical
  by_cases h0 : f = 0
  · subst h0
    have : tokAct X.dil d (X.lh v 0) = .idle := by
      unfold tokAct; rw [lh_length]; simp
    rw [this]
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro k hk _ hs
    have := one_le_stF hX hk.le
    omega
  by_cases hex : ∃ k < X.tl.length, X.stF k = f
  · obtain ⟨k, hk, hs⟩ := hex
    rw [tokAct_seg hX hd (by omega) hctl hk hs]
    constructor
    · intro h
      cases hx : X.tl[k] with
      | tk a b =>
        rw [hx] at h
        by_cases ha : a = v
        · rw [if_pos (show (TSg.tk a b).src = v from ha)] at h; exact absurd h (by simp [TSg.act])
        · rw [if_neg (show ¬ (TSg.tk a b).src = v from ha)] at h; exact absurd h (by simp)
      | ph ℓ =>
        rw [hx] at h
        by_cases ha : ℓ = v
        · subst ha; exact ⟨k, hk, hx, hs⟩
        · rw [if_neg (show ¬ (TSg.ph ℓ).src = v from ha)] at h; exact absurd h (by simp)
    · rintro ⟨k', hk', h', hs'⟩
      have := stF_inj hX hk' hk (hs'.trans hs.symm)
      subst this
      rw [h']
      simp [TSg.src, TSg.act]
  · push_neg at hex
    rw [tokAct_noseg hX hd (by omega) hctl hex]
    constructor
    · intro h; split_ifs at h
    · rintro ⟨k, hk, -, hs⟩; exact absurd hs (hex k hk)

end PCG

end APSP.Stoc.Congest
