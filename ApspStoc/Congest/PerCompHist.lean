import ApspStoc.Congest.PerCompMsg

/-!
# The histories of the schedule (for `perCompR`)

The logical history of node `v` after `f` frames of the schedule (`lh v f`): a frame during which
`v` is (partly) in a sub-run is `none`; otherwise, the messages of `ML` to `v`. Since nothing is
sent during sub-runs, the messages read from the history are exactly those of `ML`
(`recvAt_lh`). The token, broadcast and packet received in a frame (`tokS`, `bcR`, `pkR`) are
read off the schedule.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

lemma head?_filterMap_eq {α β : Type} (l : List α) (f : α → Option β) (b : β)
    (h1 : ∃ x ∈ l, f x = some b) (h2 : ∀ x ∈ l, ∀ b', f x = some b' → b' = b) :
    (l.filterMap f).head? = some b := by
  induction l with
  | nil => obtain ⟨x, hx, -⟩ := h1; simp at hx
  | cons a l ih =>
    rw [List.filterMap_cons]
    cases ha : f a with
    | none =>
      simp only
      refine ih ?_ (fun x hx b' hb' => h2 x (List.mem_cons_of_mem _ hx) b' hb')
      obtain ⟨x, hx, hfx⟩ := h1
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [ha] at hfx; simp at hfx
      · exact ⟨x, hx, hfx⟩
    | some b' =>
      simp only [List.head?_cons]
      rw [h2 a List.mem_cons_self b' ha]

lemma head?_filterMap_none {α β : Type} (l : List α) (f : α → Option β)
    (h : ∀ x ∈ l, f x = none) : (l.filterMap f).head? = none := by
  rw [List.filterMap_eq_nil_iff.2 h]; rfl

namespace PCG

variable (X : PCG V)

/-- `v` is (partly) in a sub-run in frame `φ` -/
def LB (v : V) (φ : ℕ) : Prop := LInB X.lds X.J X.bOf X.tB v φ

/-- the logical history of `v` after `f` frames -/
noncomputable def lh (v : V) (f : ℕ) : LH V := lhx X.lds X.J X.bOf X.tB X.ML v f

lemma J_part {ℓ v : V} : (X.J ℓ).part v ↔ v ∈ footprint X.E X.j (X.comp ℓ) := Iff.rfl

lemma lh_length (v : V) (f : ℕ) : (X.lh v f).length = f := by simp [lh, lhx]

open Classical in
lemma lh_getD (v : V) {f ψ : ℕ} (h : ψ < f) :
    (X.lh v f).getD ψ none = if X.LB v ψ then none else some (fun u => X.ML u v ψ) := by
  classical
  simp [lh, lhx, LB, List.getD_eq_getElem?_getD, List.getElem?_range h]
  exact if_congr Iff.rfl rfl rfl

lemma lh_getD_ge (v : V) {f ψ : ℕ} (h : f ≤ ψ) : (X.lh v f).getD ψ none = none := by
  have h' : (X.lh v f).length ≤ ψ := by rw [lh_length]; exact h
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h']

lemma lh_take (v : V) {f ψ : ℕ} (h : ψ ≤ f) : (X.lh v f).take ψ = X.lh v ψ := by
  unfold lh lhx
  rw [← List.map_take, List.take_range, min_eq_left h]

variable {X} (hX : X.OK)

include hX

lemma LB_iff {v : V} {φ : ℕ} : X.LB v φ ↔ ∃ ℓ ∈ X.lds, v ∈ footprint X.E X.j (X.comp ℓ) ∧
    X.bOf ℓ ≤ φ ∧ 3 * φ < 3 * X.bOf ℓ + X.tB ℓ := Iff.rfl

/-- Nothing is sent during sub-runs. -/
lemma ML_B {ℓ : V} (hℓ : ℓ ∈ X.lds) {φ : ℕ} (h1 : X.bOf ℓ ≤ φ) (h2 : 3 * φ < 3 * X.bOf ℓ + X.tB ℓ)
    (u w : V) : X.ML u w φ = none := by
  have hY : IsPh X (X.kPh ℓ) := Or.inl ⟨ℓ, hℓ, rfl⟩
  have hs := win_sub hX hY
  have hb : X.bOf ℓ = (X.kPh ℓ).A0 + 2 * PiL X.dil (X.kPh ℓ).L := by unfold bOf; rw [kPh_Pi]
  have hwe : we X (X.kPh ℓ) = X.bOf ℓ + (X.tB ℓ + 2) / 3 := by rw [we_kPh hX hℓ, phEnd_eq]
  rw [ML_win hX hY (by omega) (by omega)]
  apply phMsg_quiet
  right; right
  have : X.dil * (X.kPh ℓ).L ≤ PiL X.dil (X.kPh ℓ).L := by
    unfold PiL; nlinarith
  omega

lemma ML_LB {w : V} {φ : ℕ} (h : X.LB w φ) (u u' : V) : X.ML u u' φ = none := by
  obtain ⟨ℓ, hℓ, -, h1, h2⟩ := h
  exact ML_B hX hℓ h1 h2 u u'

lemma recvAt_lh (v : V) (f ψ : ℕ) (u : V) :
    recvAt (X.lh v f) ψ u = if ψ < f then X.ML u v ψ else none := by
  unfold recvAt
  by_cases h : ψ < f
  · rw [lh_getD X v h, if_pos h]
    split_ifs with hB
    · exact (ML_LB hX hB u v).symm
    · rfl
  · rw [lh_getD_ge X v (by omega), if_neg h]

/-! ## Tokens -/

lemma tok_unique {i i' : ℕ} (hi : i < X.tl.length) (hi' : i' < X.tl.length) {a b a' b' : V}
    (h : X.tl[i] = .tk a b) (h' : X.tl[i'] = .tk a' b') (he : X.stF i = X.stF i') :
    i = i' := by
  rcases lt_trichotomy i i' with hl | rfl | hl
  · have := stF_lt hX hl hi'.le; omega
  · rfl
  · have := stF_lt hX hl hi.le; omega

lemma tokS_lh_some {v : V} {f ψ : ℕ} (hψ : ψ < f) {i : ℕ} (hi : i < X.tl.length) {u : V}
    (h : X.tl[i] = .tk u v) (hs : X.stF i = ψ) : tokS (X.lh v f) ψ = some u := by
  classical
  unfold tokS
  have : univ.filter (fun u' => recvAt (X.lh v f) ψ u' = some tokW) = {u} := by
    ext u'
    simp only [mem_filter, mem_univ, true_and, mem_singleton, recvAt_lh hX, if_pos hψ]
    constructor
    · intro h'
      obtain ⟨i', hi', h'', hs'⟩ := (ML_tokW hX).1 h'
      have := tok_unique hX hi hi' h h'' (hs.trans hs'.symm)
      subst this
      rw [h] at h''
      cases h''; rfl
    · rintro rfl
      exact (ML_tokW hX).2 ⟨i, hi, h, hs⟩
  rw [this, Finset.toList_singleton]
  rfl

lemma tokS_lh_spec {v : V} {f ψ : ℕ} {u : V} (h : tokS (X.lh v f) ψ = some u) :
    ψ < f ∧ ∃ i, ∃ _ : i < X.tl.length, X.tl[i] = .tk u v ∧ X.stF i = ψ := by
  classical
  unfold tokS at h
  have hu := List.mem_of_mem_head? h
  rw [Finset.mem_toList, mem_filter, recvAt_lh hX] at hu
  split_ifs at hu with hψ
  · exact ⟨hψ, (ML_tokW hX).1 hu.2⟩
  · simp at hu

lemma tokS_lh_none {v : V} {f ψ : ℕ}
    (h : ∀ i (_ : i < X.tl.length) u, X.tl[i] = .tk u v → X.stF i = ψ → f ≤ ψ) :
    tokS (X.lh v f) ψ = none := by
  cases hs : tokS (X.lh v f) ψ with
  | none => rfl
  | some u =>
    obtain ⟨hψ, i, hi, h1, h2⟩ := tokS_lh_spec hX hs
    have := h i hi u h1 h2
    omega

/-! ## Broadcasts and packets -/

lemma bcR_lh {v : V} {f ψ c : ℕ} : bcR (X.lh v f) ψ = some c ↔
    ψ < f ∧ ∃ u, X.ML u v ψ = some (bcW c) := by
  classical
  unfold bcR
  constructor
  · intro h
    obtain ⟨u, -, hu⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? h)
    rw [recvAt_lh hX] at hu
    by_cases hψ : ψ < f
    · rw [if_pos hψ] at hu
      refine ⟨hψ, u, ?_⟩
      rcases ML_shape hX u v ψ with h' | h' | ⟨c', h'⟩ | ⟨x, c', l, h'⟩ <;> rw [h'] at hu ⊢
      · simp at hu
      · simp at hu
      · simp at hu; rw [hu]
      · simp at hu
    · rw [if_neg hψ] at hu; simp at hu
  · rintro ⟨hψ, u, hu⟩
    refine head?_filterMap_eq _ _ _ ⟨u, Finset.mem_toList.2 (mem_univ _), ?_⟩ ?_
    · rw [recvAt_lh hX, if_pos hψ, hu]; rfl
    · intro u' _ c' hc'
      rw [recvAt_lh hX, if_pos hψ] at hc'
      obtain ⟨Y, hY, h1, h2, -, -, -, -, rfl⟩ := (ML_bcW hX).1 hu
      rcases ML_shape hX u' v ψ with h' | h' | ⟨c'', h'⟩ | ⟨x, c'', l, h'⟩ <;> rw [h'] at hc'
      · simp at hc'
      · simp at hc'
      · simp at hc'
        subst hc'
        obtain ⟨Y', hY', h1', h2', -, -, -, -, rfl⟩ := (ML_bcW hX).1 h'
        have hs := win_sub hX hY
        have hs' := win_sub hX hY'
        have := PiL_ge X.dil Y.L
        have := PiL_ge X.dil Y'.L
        rw [win_disj hX hY hY' (φ := ψ) (by omega) (by omega) (by omega) (by omega)]
      · simp at hc'

lemma pkR_lh {v : V} {f ψ c : ℕ} {l : V} : pkR (X.lh v f) ψ = some (c, l) ↔
    ψ < f ∧ ∃ u x, X.ML u v ψ = some (pcPkW x c l) := by
  classical
  unfold pkR
  constructor
  · intro h
    obtain ⟨u, -, hu⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? h)
    rw [recvAt_lh hX] at hu
    by_cases hψ : ψ < f
    · rw [if_pos hψ] at hu
      refine ⟨hψ, u, ?_⟩
      rcases ML_shape hX u v ψ with h' | h' | ⟨c', h'⟩ | ⟨x, c', l', h'⟩ <;> rw [h'] at hu
      · simp at hu
      · simp at hu
      · simp at hu
      · simp at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact ⟨x, h'⟩
    · rw [if_neg hψ] at hu; simp at hu
  · rintro ⟨hψ, u, x, hu⟩
    refine head?_filterMap_eq _ _ _ ⟨u, Finset.mem_toList.2 (mem_univ _), ?_⟩ ?_
    · rw [recvAt_lh hX, if_pos hψ, hu]; rfl
    · intro u' _ cl hcl
      rw [recvAt_lh hX, if_pos hψ] at hcl
      obtain ⟨Y, hY, h1, h2, -, rfl, rfl⟩ := (ML_pkW hX).1 hu
      rcases ML_shape hX u' v ψ with h' | h' | ⟨c'', h'⟩ | ⟨x', c'', l', h'⟩ <;> rw [h'] at hcl
      · simp at hcl
      · simp at hcl
      · simp at hcl
      · simp at hcl
        subst hcl
        obtain ⟨Y', hY', h1', h2', -, rfl, rfl⟩ := (ML_pkW hX).1 h'
        have hs := win_sub hX hY
        have hs' := win_sub hX hY'
        have hle : X.dil * Y.L ≤ PiL X.dil Y.L := by unfold PiL; nlinarith
        have hle' : X.dil * Y'.L ≤ PiL X.dil Y'.L := by unfold PiL; nlinarith
        rw [win_disj hX hY hY' (φ := ψ) (by omega) (by omega) (by omega) (by omega)]

lemma pkR_lh_none {v : V} {f ψ : ℕ} (h : ∀ u x c l, X.ML u v ψ ≠ some (pcPkW x c l)) :
    pkR (X.lh v f) ψ = none := by
  cases hp : pkR (X.lh v f) ψ with
  | none => rfl
  | some cl =>
    obtain ⟨-, u, x, hu⟩ := (pkR_lh hX).1 hp
    exact absurd hu (h _ _ _ _)

lemma bcR_lh_none {v : V} {f ψ : ℕ} (h : ∀ u c, X.ML u v ψ ≠ some (bcW c)) :
    bcR (X.lh v f) ψ = none := by
  cases hp : bcR (X.lh v f) ψ with
  | none => rfl
  | some c =>
    obtain ⟨-, u, hu⟩ := (bcR_lh hX).1 hp
    exact absurd hu (h _ _)

end PCG

end APSP.Stoc.Congest
