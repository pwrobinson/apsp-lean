import ApspStoc.Congest.PerCompSched

/-!
# The timeline of the component traversal (for `perCompR`)

Basic facts about the global schedule of `PerCompSched`: the components and their trees, the
segments of the traversal, their first frames (`stF`), and the frame classification: every frame
`φ` with `1 ≤ φ < E0` lies in exactly one segment (`idx_eq`), whose messages are those of `ML`
(`ML_tok`, `ML_ph`); the frames from `E0` on belong to the final phase (`ML_end`).
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

namespace PCG

variable {X : PCG V} (hX : X.OK)
include hX

/-! ## Components -/

omit hX in
lemma mem_comp {ℓ v : V} : v ∈ X.comp ℓ ↔ v ∈ X.S ∧ X.rtS v = ℓ := by
  classical
  unfold comp
  simp only [mem_filter]

omit hX in
lemma mem_lds {ℓ : V} : ℓ ∈ X.lds ↔ ℓ ∈ X.S ∧ X.parS ℓ = none := by
  classical
  unfold lds
  simp only [mem_filter]

omit hX in
lemma isL_iff {ℓ : V} : X.isL ℓ = true ↔ ℓ ∈ X.lds := by
  classical
  rw [mem_lds]
  unfold isL
  simp

lemma self_mem_comp {ℓ : V} (hℓ : ℓ ∈ X.lds) : ℓ ∈ X.comp ℓ := by
  rw [mem_lds] at hℓ
  exact mem_comp.2 ⟨hℓ.1, hX.Sself ℓ hℓ.1 hℓ.2⟩

lemma comp_card_pos {ℓ : V} (hℓ : ℓ ∈ X.lds) : 0 < (X.comp ℓ).card :=
  card_pos.2 ⟨ℓ, self_mem_comp hX hℓ⟩

lemma PiK_pos {ℓ : V} (hℓ : ℓ ∈ X.lds) : 0 < X.PiK ℓ := by
  unfold PiK PiL
  have := comp_card_pos hX hℓ
  exact Nat.mul_pos (Nat.succ_pos _) this

lemma comp_sub_P (ℓ : V) : X.comp ℓ ⊆ X.P := fun v hv => hX.SP (mem_comp.1 hv).1

lemma rtS_lds {v : V} (hv : v ∈ X.S) : X.rtS v ∈ X.lds ∧ v ∈ X.comp (X.rtS v) := by
  obtain ⟨h1, h2, -⟩ := root_spec hX.Smem hX.Srk hX.Sroot hX.Sself hv
  exact ⟨mem_lds.2 ⟨h1, h2⟩, mem_comp.2 ⟨hv, rfl⟩⟩

lemma comp_par {ℓ v u : V} (hv : v ∈ X.comp ℓ) (hu : X.parS v = some u) : u ∈ X.comp ℓ := by
  rw [mem_comp] at hv ⊢
  exact ⟨hX.Smem v hv.1 u hu, by rw [hX.Sroot v hv.1 u hu, hv.2]⟩

lemma comp_kid {ℓ v w : V} (hv : v ∈ X.comp ℓ) (hw : w ∈ X.S) (hwv : X.parS w = some v) :
    w ∈ X.comp ℓ := by
  rw [mem_comp] at hv ⊢
  exact ⟨hw, by rw [← hX.Sroot w hw v hwv, hv.2]⟩

lemma comp_disj {ℓ ℓ' : V} (hne : ℓ ≠ ℓ') : Disjoint (X.comp ℓ) (X.comp ℓ') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact hne ((mem_comp.1 hv).2.symm.trans (mem_comp.1 hv').2)

/-- Depths in the tree of a component are smaller than its size. -/
lemma dep_comp {ℓ v : V} (hv : v ∈ X.comp ℓ) : dep X.parS X.rkS v < (X.comp ℓ).card := by
  have hvS := (mem_comp.1 hv).1
  have h1 := card_ancS hX.Smem hX.Srk v hvS
  have h2 : ancS X.parS v ⊆ X.comp ℓ := by
    intro a ha
    rw [mem_ancS] at ha
    rw [mem_comp]
    refine ⟨anc_mem hX.Smem hvS ha, ?_⟩
    rw [root_anc hX.Smem hX.Sroot hvS ha, (mem_comp.1 hv).2]
  have := card_le_card h2
  omega

/-- Depths in the tree of `P` are smaller than `sz`. -/
lemma dep_P {v : V} (hv : v ∈ X.P) : dep X.parP X.rkP v < X.sz :=
  lt_of_lt_of_le (dep_lt hX.Pmem hX.Prk hv) hX.Psz

lemma kidsS_comp {ℓ v : V} (hv : v ∈ X.comp ℓ) (w : V) :
    w ∈ kidsOf X.S X.parS v ↔ w ∈ X.comp ℓ ∧ X.parS w = some v := by
  rw [mem_kidsOf]
  constructor
  · rintro ⟨hw, hwv⟩; exact ⟨comp_kid hX hv hw hwv, hwv⟩
  · rintro ⟨hw, hwv⟩; exact ⟨(mem_comp.1 hw).1, hwv⟩

/-! ## The traversal -/

lemma tl_ok : SegOK (Pp := X.P) (par := X.parP) (rk := X.rkP) (isL := X.isL) X.r :=
  segOK hX.Pmem hX.Prk X.r hX.rP

lemma tl_nodup : X.tl.Nodup := segs_nodup hX.Pmem hX.Prk X.r hX.rP

lemma mem_tl (x : TSg V) : x ∈ X.tl ↔
    (∃ w, x = .ph w ∧ w ∈ X.lds) ∨
    (∃ a b, x = .tk a b ∧ ((b ∈ X.P ∧ X.parP b = some a) ∨ (a ∈ X.P ∧ X.parP a = some b))) := by
  unfold tl
  rw [mem_segs hX.Pmem hX.Prk X.r hX.rP, hX.Pdesc]
  constructor
  · rintro (⟨w, rfl, hL, -⟩ | ⟨a, b, rfl, h | h⟩)
    · exact Or.inl ⟨w, rfl, isL_iff.1 hL⟩
    · exact Or.inr ⟨a, b, rfl, Or.inl ⟨h.1, h.2.1⟩⟩
    · exact Or.inr ⟨a, b, rfl, Or.inr ⟨h.1, h.2.1⟩⟩
  · rintro (⟨w, rfl, hw⟩ | ⟨a, b, rfl, h | h⟩)
    · exact Or.inl ⟨w, rfl, isL_iff.2 hw, hX.SP (mem_lds.1 hw).1⟩
    · exact Or.inr ⟨a, b, rfl, Or.inl ⟨h.1, h.2, hX.Pmem b h.1 a h.2⟩⟩
    · exact Or.inr ⟨a, b, rfl, Or.inr ⟨h.1, h.2, hX.Pmem a h.1 b h.2⟩⟩

lemma ph_mem_tl {ℓ : V} : TSg.ph ℓ ∈ X.tl ↔ ℓ ∈ X.lds := by
  rw [mem_tl hX]
  constructor
  · rintro (⟨w, hw, hl⟩ | ⟨a, b, h, -⟩)
    · cases hw; exact hl
    · cases h
  · intro h; exact Or.inl ⟨ℓ, rfl, h⟩

lemma tk_mem_tl {a b : V} : TSg.tk a b ∈ X.tl ↔
    ((b ∈ X.P ∧ X.parP b = some a) ∨ (a ∈ X.P ∧ X.parP a = some b)) := by
  rw [mem_tl hX]
  constructor
  · rintro (⟨w, hw, -⟩ | ⟨a', b', h, h'⟩)
    · cases hw
    · cases h; exact h'
  · intro h; exact Or.inr ⟨a, b, rfl, h⟩

/-! ## The first frames of the segments -/

omit hX in
lemma stF_zero : X.stF 0 = 1 := by simp [stF]

omit hX in
lemma stF_succ {i : ℕ} (hi : i < X.tl.length) :
    X.stF (i + 1) = X.stF i + X.dur X.tl[i] (X.stF i) := by
  unfold stF
  rw [List.take_succ, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

lemma phEnd_ge {ℓ : V} (hℓ : ℓ ∈ X.lds) (a : ℕ) : a + 2 * X.PiK ℓ ≤ X.phEnd ℓ a := by
  unfold phEnd
  have := le_alignUp a (PiK_pos hX hℓ)
  omega

lemma dur_pos {i : ℕ} (hi : i < X.tl.length) : 1 ≤ X.dur X.tl[i] (X.stF i) := by
  have hm := List.getElem_mem hi
  cases h : X.tl[i] with
  | tk a b => simp [dur]
  | ph ℓ =>
    rw [h] at hm
    have hℓ := (ph_mem_tl hX).1 hm
    have h1 := phEnd_ge hX hℓ (X.stF i)
    have h2 := PiK_pos hX hℓ
    simp only [dur]
    omega

lemma stF_lt {i k : ℕ} (hik : i < k) (hk : k ≤ X.tl.length) : X.stF i < X.stF k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [stF_succ (X := X) (i := k) (by omega)]
    have := dur_pos hX (show k < X.tl.length by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hik with h | h
    · have := ih h (by omega); omega
    · subst h; omega

lemma stF_le {i k : ℕ} (hik : i ≤ k) (hk : k ≤ X.tl.length) : X.stF i ≤ X.stF k := by
  rcases Nat.lt_or_eq_of_le hik with h | h
  · exact (stF_lt hX h hk).le
  · rw [h]

lemma one_le_stF {i : ℕ} (hi : i ≤ X.tl.length) : 1 ≤ X.stF i := by
  have := stF_le hX (Nat.zero_le i) hi
  rwa [stF_zero] at this

/-- The segment containing a frame. -/
lemma idx_eq {i φ : ℕ} (hi : i < X.tl.length) (h1 : X.stF i ≤ φ) (h2 : φ < X.stF (i + 1)) :
    X.idx φ = i := by
  classical
  unfold idx
  have : (range X.tl.length).filter (fun k => X.stF (k + 1) ≤ φ) = range i := by
    ext k
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hk, hle⟩
      by_contra hki
      have := stF_le hX (show i + 1 ≤ k + 1 by omega) (by omega)
      omega
    · intro hk
      exact ⟨by omega, le_trans (stF_le hX (show k + 1 ≤ i by omega) (by omega)) h1⟩
  rw [this, card_range]

lemma exists_seg {φ : ℕ} (h1 : 1 ≤ φ) (h2 : φ < X.E0) :
    ∃ i < X.tl.length, X.stF i ≤ φ ∧ φ < X.stF (i + 1) := by
  by_contra hno
  push_neg at hno
  have : ∀ i ≤ X.tl.length, X.stF i ≤ φ := by
    intro i
    induction i with
    | zero => intro _; rw [stF_zero]; exact h1
    | succ i ih => intro hi; exact hno i (by omega) (ih (by omega))
  have := this X.tl.length le_rfl
  unfold E0 at h2
  omega

lemma stF_tk {i : ℕ} (hi : i < X.tl.length) {a b : V} (h : X.tl[i] = .tk a b) :
    X.stF (i + 1) = X.stF i + 1 := by
  rw [stF_succ hi, h]; rfl

lemma idxOf_ph {i : ℕ} (hi : i < X.tl.length) {ℓ : V} (h : X.tl[i] = .ph ℓ) :
    X.tl.idxOf (TSg.ph ℓ) = i := by
  rw [← h]
  exact List.Nodup.idxOf_getElem (tl_nodup hX) i hi

lemma aOf_eq {i : ℕ} (hi : i < X.tl.length) {ℓ : V} (h : X.tl[i] = .ph ℓ) :
    X.aOf ℓ = X.stF i := by
  unfold aOf; rw [idxOf_ph hX hi h]

lemma stF_ph {i : ℕ} (hi : i < X.tl.length) {ℓ : V} (h : X.tl[i] = .ph ℓ) :
    X.stF (i + 1) = X.phEnd ℓ (X.aOf ℓ) := by
  have hℓ : ℓ ∈ X.lds := (ph_mem_tl hX).1 (h ▸ List.getElem_mem hi)
  rw [stF_succ hi, h, aOf_eq hX hi h]
  simp only [dur]
  have := phEnd_ge hX hℓ (X.stF i)
  omega

/-- every leader has its phase segment -/
lemma exists_ph {ℓ : V} (hℓ : ℓ ∈ X.lds) : ∃ i, ∃ _ : i < X.tl.length, X.tl[i] = .ph ℓ := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem ((ph_mem_tl hX).2 hℓ)
  exact ⟨i, hi, h⟩

/-! ## Phases -/

omit hX in
lemma kPh_A0 (ℓ : V) : (X.kPh ℓ).A0 = alignUp (X.aOf ℓ) (X.PiK ℓ) := rfl

omit hX in
lemma kPh_Pi (ℓ : V) : PiL X.dil (X.kPh ℓ).L = X.PiK ℓ := rfl

omit hX in
lemma phEnd_eq (ℓ : V) : X.phEnd ℓ (X.aOf ℓ) = X.bOf ℓ + (X.tB ℓ + 2) / 3 := by
  unfold phEnd bOf kPh; rfl

lemma aOf_le_A0 {ℓ : V} (hℓ : ℓ ∈ X.lds) : X.aOf ℓ ≤ (X.kPh ℓ).A0 :=
  le_alignUp _ (PiK_pos hX hℓ)

lemma A0_lt {ℓ : V} (hℓ : ℓ ∈ X.lds) : (X.kPh ℓ).A0 < X.aOf ℓ + X.PiK ℓ :=
  alignUp_lt _ (PiK_pos hX hℓ)

lemma PiE_pos : 0 < PiL X.dil X.sz := by
  unfold PiL
  have := card_pos.2 ⟨X.r, hX.rP⟩
  have := hX.Psz
  have : 0 < X.sz := by omega
  exact Nat.mul_pos (Nat.succ_pos _) this

lemma E0_le_A0 : X.E0 ≤ X.ePh.A0 := le_alignUp _ (PiE_pos hX)

/-! ## The schedule by frames -/

lemma ML_zero (u w : V) : X.ML u w 0 = none := by
  unfold ML
  rw [if_neg (by omega), if_neg]
  have := one_le_stF hX (le_refl X.tl.length)
  unfold E0; omega

lemma ML_seg {i φ : ℕ} (hi : i < X.tl.length) (h1 : X.stF i ≤ φ) (h2 : φ < X.stF (i + 1))
    (u w : V) : X.ML u w φ = X.segMsg i u w φ := by
  have hE : X.stF (i + 1) ≤ X.E0 := stF_le hX (by omega) le_rfl
  unfold ML
  rw [if_pos ⟨le_trans (one_le_stF hX (by omega)) h1, by omega⟩, idx_eq hX hi h1 h2]

lemma ML_tok {i : ℕ} (hi : i < X.tl.length) {a b : V} (h : X.tl[i] = .tk a b) (u w : V) :
    X.ML u w (X.stF i) = if u = a ∧ w = b then some tokW else none := by
  classical
  rw [ML_seg hX hi le_rfl (by rw [stF_tk hX hi h]; omega)]
  unfold segMsg
  rw [List.getElem?_eq_getElem hi, h]
  simp

lemma ML_ph {i φ : ℕ} (hi : i < X.tl.length) {ℓ : V} (h : X.tl[i] = .ph ℓ)
    (h1 : X.stF i ≤ φ) (h2 : φ < X.stF (i + 1)) (u w : V) :
    X.ML u w φ = phMsg X.E X.j X.dil (X.kPh ℓ) u w φ := by
  classical
  rw [ML_seg hX hi h1 h2]
  unfold segMsg
  rw [List.getElem?_eq_getElem hi, h]

lemma ML_end {φ : ℕ} (h : X.E0 ≤ φ) (u w : V) :
    X.ML u w φ = phMsg X.E X.j X.dil X.ePh u w φ := by
  unfold ML
  rw [if_neg (by omega), if_pos h]

end PCG

end APSP.Stoc.Congest
