import ApspStoc.Congest.PerCompTime

/-!
# The messages of the schedule (for `perCompR`)

* The three kinds of messages are distinguished by their words (`bcOf`, `pkOf`, `idOf`).
* `phMsg` of a well-formed phase (`GOK`): the broadcast in frames `[A0, A0 + L)`, the packets in
  frames `[A0 + Π, A0 + Π + dil·L)`, nothing else.
* The phases of the traversal (`IsPh`: the phases of the leaders and the final phase) are
  well-formed, and their windows are disjoint; in the window of a phase, `ML` is the phase's
  message (`ML_win`); the messages of `ML` are tokens of token segments, broadcasts or packets of
  phases (`ML_tokW`, `ML_bcW`, `ML_pkW`).
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The words -/

@[simp] lemma bcOf_tok : bcOf (some (tokW : W3 V)) = none := rfl
@[simp] lemma bcOf_bc (c : ℕ) : bcOf (some (bcW c : W3 V)) = some c := rfl
@[simp] lemma bcOf_pk (x : V) (c : ℕ) (l : V) : bcOf (some (pcPkW x c l)) = none := rfl
@[simp] lemma bcOf_none : bcOf (none : Option (W3 V)) = none := rfl
@[simp] lemma pkOf_tok : pkOf (some (tokW : W3 V)) = none := rfl
@[simp] lemma pkOf_bc (c : ℕ) : pkOf (some (bcW c : W3 V)) = none := rfl
@[simp] lemma pkOf_pk (x : V) (c : ℕ) (l : V) : pkOf (some (pcPkW x c l)) = some (c, l) := rfl
@[simp] lemma pkOf_none : pkOf (none : Option (W3 V)) = none := rfl
@[simp] lemma idOf_tok : idOf (some (tokW : W3 V)) = none := rfl
@[simp] lemma idOf_bc (c : ℕ) : idOf (some (bcW c : W3 V)) = none := rfl
@[simp] lemma idOf_pk (x : V) (c : ℕ) (l : V) : idOf (some (pcPkW x c l)) = some x := rfl
@[simp] lemma idOf_none : idOf (none : Option (W3 V)) = none := rfl

lemma tokW_ne_bcW (c : ℕ) : (tokW : W3 V) ≠ bcW c := by simp [tokW, bcW]
lemma tokW_ne_pkW (x : V) (c : ℕ) (l : V) : (tokW : W3 V) ≠ pcPkW x c l := by simp [tokW, pcPkW]
lemma bcW_ne_pkW (c : ℕ) (x : V) (c' : ℕ) (l : V) : (bcW c : W3 V) ≠ pcPkW x c' l := by
  simp [bcW, pcPkW]

lemma slotMsg_eq {s : Finset V} {i c : ℕ} {l : V} {m : W3 V} (h : slotMsg s i c l = some m) :
    ∃ x, s.toList[i]? = some x ∧ m = pcPkW x c l := by
  unfold slotMsg at h
  cases hx : s.toList[i]? with
  | none => rw [hx] at h; simp at h
  | some x => rw [hx] at h; simp at h; exact ⟨x, rfl, h.symm⟩

lemma slotMsg_ne_tok {s : Finset V} {i c : ℕ} {l : V} : slotMsg s i c l ≠ some tokW := by
  intro h
  obtain ⟨x, -, hm⟩ := slotMsg_eq h
  exact tokW_ne_pkW x c l hm

/-! ## Messages of a phase -/

/-- A well-formed phase. -/
structure GOK (G : SimpleGraph V) (dil : ℕ) (Y : GPh V) : Prop where
  L1 : 1 ≤ Y.L
  dvd : PiL dil Y.L ∣ Y.A0
  QL : Y.Q.card ≤ Y.L
  dep : ∀ u ∈ Y.Q, dep Y.par Y.rk u < Y.L
  par : ∀ w ∈ Y.Q, ∀ u, Y.par w = some u → u ∈ Y.Q
  rk : ∀ w ∈ Y.Q, ∀ u, Y.par w = some u → Y.rk u < Y.rk w
  adj : ∀ w ∈ Y.Q, ∀ u, Y.par w = some u → G.Adj w u

section Ph

variable (E : Overlays V) (j dil : ℕ) (Y : GPh V)

lemma PiL_ge (L : ℕ) : L ≤ PiL dil L := by unfold PiL; nlinarith

lemma phMsg_bc_win {φ : ℕ} (h1 : Y.A0 ≤ φ) (h2 : φ < Y.A0 + Y.L) (u w : V) :
    phMsg E j dil Y u w φ =
      if u ∈ Y.Q ∧ w ∈ Y.Q ∧ Y.par w = some u ∧ dep Y.par Y.rk u = φ - Y.A0 then
        some (bcW Y.c) else none := by
  classical
  unfold phMsg
  rw [if_pos ⟨h1, h2⟩]

lemma phMsg_pk_win {φ : ℕ} (h0 : Y.A0 + Y.L ≤ Y.A0 + PiL dil Y.L) (h1 : Y.A0 + PiL dil Y.L ≤ φ)
    (h2 : φ < Y.A0 + PiL dil Y.L + dil * Y.L) (hL : 1 ≤ Y.L) (u w : V) :
    phMsg E j dil Y u w φ =
      slotMsg (pk E j Y.Q ((φ - Y.A0 - PiL dil Y.L) / Y.L) u w) ((φ - Y.A0 - PiL dil Y.L) % Y.L)
        Y.c Y.l := by
  classical
  unfold phMsg
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

lemma phMsg_quiet {φ : ℕ} (h : φ < Y.A0 ∨ (Y.A0 + Y.L ≤ φ ∧ φ < Y.A0 + PiL dil Y.L) ∨
    Y.A0 + PiL dil Y.L + dil * Y.L ≤ φ) (u w : V) : phMsg E j dil Y u w φ = none := by
  classical
  have := PiL_ge dil Y.L
  unfold phMsg
  rw [if_neg (by omega), if_neg (by omega)]

lemma phMsg_ne_tok (u w : V) (φ : ℕ) : phMsg E j dil Y u w φ ≠ some tokW := by
  classical
  unfold phMsg
  split_ifs
  all_goals first
    | exact fun h => tokW_ne_bcW Y.c (Option.some.inj h).symm
    | exact slotMsg_ne_tok
    | simp

lemma phMsg_bcW {u w : V} {φ c : ℕ} (h : phMsg E j dil Y u w φ = some (bcW c)) :
    Y.A0 ≤ φ ∧ φ < Y.A0 + Y.L ∧ u ∈ Y.Q ∧ w ∈ Y.Q ∧ Y.par w = some u ∧
      dep Y.par Y.rk u = φ - Y.A0 ∧ c = Y.c := by
  classical
  unfold phMsg at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq] at h
    refine ⟨h1.1, h1.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, ?_⟩
    simp [bcW] at h; exact h.symm
  · obtain ⟨x, -, hm⟩ := slotMsg_eq h
    exact absurd hm (bcW_ne_pkW _ _ _ _)

lemma phMsg_pkW {u w : V} {φ : ℕ} {x : V} {c : ℕ} {l : V}
    (h : phMsg E j dil Y u w φ = some (pcPkW x c l)) :
    Y.A0 + PiL dil Y.L ≤ φ ∧ φ < Y.A0 + PiL dil Y.L + dil * Y.L ∧ ¬ (φ < Y.A0 + Y.L) ∧
      (pk E j Y.Q ((φ - Y.A0 - PiL dil Y.L) / Y.L) u w).toList[(φ - Y.A0 - PiL dil Y.L) %
        Y.L]? = some x ∧ c = Y.c ∧ l = Y.l := by
  classical
  unfold phMsg at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq] at h
    exact absurd h (bcW_ne_pkW _ _ _ _)
  · obtain ⟨x', hx', hm⟩ := slotMsg_eq h
    simp only [pcPkW, Prod.mk.injEq, Word.id.injEq, Word.num.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨h3.1, h3.2, fun h' => h1 ⟨by omega, h'⟩, hx', rfl, rfl⟩

lemma phMsg_some {u w : V} {φ : ℕ} (h : (phMsg E j dil Y u w φ).isSome) :
    Y.A0 ≤ φ ∧ φ < Y.A0 + PiL dil Y.L + dil * Y.L ∧
      ((φ < Y.A0 + Y.L ∧ u ∈ Y.Q ∧ w ∈ Y.Q ∧ Y.par w = some u) ∨
       (Y.A0 + PiL dil Y.L ≤ φ ∧ ∃ x, x ∈ pk E j Y.Q ((φ - Y.A0 - PiL dil Y.L) / Y.L) u w)) := by
  classical
  unfold phMsg at h
  split_ifs at h with h1 h2 h3
  · refine ⟨h1.1, ?_, Or.inl ⟨h1.2, h2.1, h2.2.1, h2.2.2.1⟩⟩
    have := PiL_ge dil Y.L; omega
  · simp at h
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨x, hx, -⟩ := slotMsg_eq hm
    refine ⟨by omega, h3.2, Or.inr ⟨h3.1, x, ?_⟩⟩
    exact Finset.mem_toList.1 (List.mem_of_getElem? hx)
  · simp at h

end Ph

/-! ## The phases of the traversal -/

namespace PCG

variable {X : PCG V} (hX : X.OK)
include hX

omit hX in
/-- the phases of the traversal -/
def IsPh (X : PCG V) (Y : GPh V) : Prop := (∃ ℓ ∈ X.lds, Y = X.kPh ℓ) ∨ Y = X.ePh

omit hX in
open Classical in
/-- the first frame of the window of a phase -/
noncomputable def ws (X : PCG V) (Y : GPh V) : ℕ := if Y = X.ePh then X.E0 else X.aOf Y.l

omit hX in
open Classical in
/-- the end of the window of a phase -/
noncomputable def we (X : PCG V) (Y : GPh V) : ℕ :=
  if Y = X.ePh then X.TL else X.phEnd Y.l (X.aOf Y.l)

lemma kPh_ne_ePh {ℓ : V} (hℓ : ℓ ∈ X.lds) : X.kPh ℓ ≠ X.ePh := by
  intro h
  have h1 : (X.kPh ℓ).c = X.ePh.c := by rw [h]
  simp only [kPh, ePh] at h1
  have := comp_card_pos hX hℓ
  omega

lemma ws_kPh {ℓ : V} (hℓ : ℓ ∈ X.lds) : ws X (X.kPh ℓ) = X.aOf ℓ := by
  unfold ws; rw [if_neg (kPh_ne_ePh hX hℓ)]; rfl

lemma we_kPh {ℓ : V} (hℓ : ℓ ∈ X.lds) : we X (X.kPh ℓ) = X.phEnd ℓ (X.aOf ℓ) := by
  unfold we; rw [if_neg (kPh_ne_ePh hX hℓ)]; rfl

omit hX in
lemma ws_ePh : ws X X.ePh = X.E0 := by unfold ws; rw [if_pos rfl]

omit hX in
lemma we_ePh : we X X.ePh = X.TL := by unfold we; rw [if_pos rfl]

lemma kPh_gok {ℓ : V} (hℓ : ℓ ∈ X.lds) : GOK X.N.G X.dil (X.kPh ℓ) where
  L1 := comp_card_pos hX hℓ
  dvd := dvd_alignUp _ _
  QL := le_rfl
  dep := fun u hu => dep_comp hX hu
  par := fun w hw u hu => comp_par hX hw hu
  rk := fun w hw u hu => hX.Srk w (mem_comp.1 hw).1 u hu
  adj := fun w hw u hu => hX.Sadj w (mem_comp.1 hw).1 u hu

lemma ePh_gok : GOK X.N.G X.dil X.ePh where
  L1 := by have := card_pos.2 ⟨X.r, hX.rP⟩; have := hX.Psz; show 1 ≤ X.sz; omega
  dvd := dvd_alignUp _ _
  QL := hX.Psz
  dep := fun u hu => dep_P hX hu
  par := fun w hw u hu => hX.Pmem w hw u hu
  rk := fun w hw u hu => hX.Prk w hw u hu
  adj := fun w hw u hu => hX.Padj w hw u hu

lemma isPh_gok {Y : GPh V} (hY : IsPh X Y) : GOK X.N.G X.dil Y := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · exact kPh_gok hX hℓ
  · exact ePh_gok hX

/-- The messages of a phase lie in its window. -/
lemma win_sub {Y : GPh V} (hY : IsPh X Y) :
    ws X Y ≤ Y.A0 ∧ Y.A0 + 2 * PiL X.dil Y.L ≤ we X Y := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · rw [ws_kPh hX hℓ, we_kPh hX hℓ, phEnd_eq, kPh_Pi]
    exact ⟨aOf_le_A0 hX hℓ, by unfold bOf; omega⟩
  · rw [ws_ePh, we_ePh]
    exact ⟨E0_le_A0 hX, by unfold TL; rfl⟩

lemma win_ok {Y : GPh V} (hY : IsPh X Y) : 1 ≤ ws X Y ∧ ws X Y < we X Y := by
  have h1 := win_sub hX hY
  have h2 := (isPh_gok hX hY).L1
  have h3 : 0 < PiL X.dil Y.L := by unfold PiL; exact Nat.mul_pos (Nat.succ_pos _) (by omega)
  refine ⟨?_, by omega⟩
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · rw [ws_kPh hX hℓ]
    obtain ⟨i, hi, h⟩ := exists_ph hX hℓ
    rw [aOf_eq hX hi h]; exact one_le_stF hX hi.le
  · rw [ws_ePh]; exact one_le_stF hX le_rfl

/-- In the window of a phase, the schedule is the phase's message. -/
lemma ML_win {Y : GPh V} (hY : IsPh X Y) {φ : ℕ} (h1 : ws X Y ≤ φ) (h2 : φ < we X Y)
    (u w : V) : X.ML u w φ = phMsg X.E X.j X.dil Y u w φ := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · rw [ws_kPh hX hℓ] at h1
    rw [we_kPh hX hℓ] at h2
    obtain ⟨i, hi, h⟩ := exists_ph hX hℓ
    rw [aOf_eq hX hi h] at h1
    rw [← stF_ph hX hi h] at h2
    exact ML_ph hX hi h h1 h2 u w
  · rw [ws_ePh] at h1
    exact ML_end hX h1 u w

/-- The frames of the traversal: token frames, phase windows. -/
lemma frame_cases {φ : ℕ} (h1 : 1 ≤ φ) (h2 : φ < X.TL) :
    (∃ i, ∃ _ : i < X.tl.length, ∃ a b, X.tl[i] = .tk a b ∧ X.stF i = φ) ∨
    (∃ Y, IsPh X Y ∧ ws X Y ≤ φ ∧ φ < we X Y) := by
  by_cases hE : X.E0 ≤ φ
  · exact Or.inr ⟨X.ePh, Or.inr rfl, by rw [ws_ePh]; exact hE, by rw [we_ePh]; exact h2⟩
  · obtain ⟨i, hi, hs1, hs2⟩ := exists_seg hX h1 (by omega)
    cases h : X.tl[i] with
    | tk a b =>
      left
      rw [stF_tk hX hi h] at hs2
      exact ⟨i, hi, a, b, h, by omega⟩
    | ph ℓ =>
      right
      have hℓ : ℓ ∈ X.lds := (ph_mem_tl hX).1 (h ▸ List.getElem_mem hi)
      refine ⟨X.kPh ℓ, Or.inl ⟨ℓ, hℓ, rfl⟩, ?_, ?_⟩
      · rw [ws_kPh hX hℓ, aOf_eq hX hi h]; exact hs1
      · rw [we_kPh hX hℓ, ← stF_ph hX hi h]; exact hs2

/-- Phase windows are disjoint, and contain no token frame. -/
lemma win_disj {Y Y' : GPh V} (hY : IsPh X Y) (hY' : IsPh X Y') {φ : ℕ}
    (h1 : ws X Y ≤ φ) (h2 : φ < we X Y) (h1' : ws X Y' ≤ φ) (h2' : φ < we X Y') : Y = Y' := by
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl <;> rcases hY' with ⟨ℓ', hℓ', rfl⟩ | rfl
  · obtain ⟨i, hi, h⟩ := exists_ph hX hℓ
    obtain ⟨i', hi', h'⟩ := exists_ph hX hℓ'
    rw [ws_kPh hX hℓ, aOf_eq hX hi h] at h1
    rw [we_kPh hX hℓ, ← stF_ph hX hi h] at h2
    rw [ws_kPh hX hℓ', aOf_eq hX hi' h'] at h1'
    rw [we_kPh hX hℓ', ← stF_ph hX hi' h'] at h2'
    have : i = i' := by
      rw [← idx_eq hX hi h1 h2, idx_eq hX hi' h1' h2']
    subst this
    rw [h] at h'
    cases h'
    rfl
  · obtain ⟨i, hi, h⟩ := exists_ph hX hℓ
    rw [we_kPh hX hℓ, ← stF_ph hX hi h] at h2
    rw [ws_ePh] at h1'
    have := stF_le hX (show i + 1 ≤ X.tl.length by omega) le_rfl
    unfold E0 at h1'; omega
  · obtain ⟨i, hi, h⟩ := exists_ph hX hℓ'
    rw [we_kPh hX hℓ', ← stF_ph hX hi h] at h2'
    rw [ws_ePh] at h1
    have := stF_le hX (show i + 1 ≤ X.tl.length by omega) le_rfl
    unfold E0 at h1; omega
  · rfl

lemma tok_not_win {i : ℕ} (hi : i < X.tl.length) {a b : V} (h : X.tl[i] = .tk a b) {Y : GPh V}
    (hY : IsPh X Y) : ¬ (ws X Y ≤ X.stF i ∧ X.stF i < we X Y) := by
  rintro ⟨h1, h2⟩
  rcases hY with ⟨ℓ, hℓ, rfl⟩ | rfl
  · obtain ⟨i', hi', h'⟩ := exists_ph hX hℓ
    rw [ws_kPh hX hℓ, aOf_eq hX hi' h'] at h1
    rw [we_kPh hX hℓ, ← stF_ph hX hi' h'] at h2
    have := idx_eq hX hi' h1 h2
    rw [idx_eq hX hi le_rfl (by rw [stF_tk hX hi h]; omega)] at this
    subst this
    rw [h] at h'; cases h'
  · rw [ws_ePh] at h1
    have := stF_lt hX hi le_rfl
    unfold E0 at h1; omega

/-! ## The kinds of messages -/

lemma ML_tokW {u w : V} {φ : ℕ} : X.ML u w φ = some tokW ↔
    ∃ i, ∃ _ : i < X.tl.length, X.tl[i] = .tk u w ∧ X.stF i = φ := by
  constructor
  · intro h
    by_cases h0 : φ = 0
    · subst h0; rw [ML_zero hX] at h; simp at h
    by_cases hT : φ < X.TL
    · rcases frame_cases hX (by omega) hT with ⟨i, hi, a, b, hab, rfl⟩ | ⟨Y, hY, h1, h2⟩
      · rw [ML_tok hX hi hab] at h
        by_cases hh : u = a ∧ w = b
        · obtain ⟨rfl, rfl⟩ := hh; exact ⟨i, hi, hab, rfl⟩
        · rw [if_neg hh] at h; simp at h
      · rw [ML_win hX hY h1 h2] at h
        exact absurd h (phMsg_ne_tok _ _ _ _ _ _ _)
    · rw [ML_end hX (by have := E0_le_A0 hX; unfold TL at hT; omega)] at h
      exact absurd h (phMsg_ne_tok _ _ _ _ _ _ _)
  · rintro ⟨i, hi, h, rfl⟩
    rw [ML_tok hX hi h]; simp

lemma ML_TL {u w : V} {φ : ℕ} (h : (X.ML u w φ).isSome) : 1 ≤ φ ∧ φ < X.TL := by
  by_cases h0 : φ = 0
  · subst h0; rw [ML_zero hX] at h; simp at h
  refine ⟨by omega, ?_⟩
  by_contra hT
  have hE : X.E0 ≤ φ := by have := E0_le_A0 hX; unfold TL at hT; omega
  rw [ML_end hX hE] at h
  obtain ⟨-, h2, -⟩ := phMsg_some _ _ _ _ h
  have h3 : X.dil * X.ePh.L ≤ PiL X.dil X.ePh.L := by unfold PiL; nlinarith
  have hL : X.ePh.L = X.sz := rfl
  rw [hL] at h2 h3
  unfold TL at hT
  omega

lemma ML_bcW {u w : V} {φ c : ℕ} : X.ML u w φ = some (bcW c) ↔
    ∃ Y, IsPh X Y ∧ Y.A0 ≤ φ ∧ φ < Y.A0 + Y.L ∧ u ∈ Y.Q ∧ w ∈ Y.Q ∧ Y.par w = some u ∧
      dep Y.par Y.rk u = φ - Y.A0 ∧ c = Y.c := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := ML_TL hX (by rw [h]; rfl)
    rcases frame_cases hX h1 h2 with ⟨i, hi, a, b, hab, rfl⟩ | ⟨Y, hY, hw1, hw2⟩
    · rw [ML_tok hX hi hab] at h
      by_cases hh : u = a ∧ w = b
      · rw [if_pos hh] at h; exact absurd (Option.some.inj h) (tokW_ne_bcW c)
      · rw [if_neg hh] at h; simp at h
    · rw [ML_win hX hY hw1 hw2] at h
      exact ⟨Y, hY, phMsg_bcW _ _ _ _ h⟩
  · rintro ⟨Y, hY, h1, h2, hu, hw, hp, hd, rfl⟩
    have hs := win_sub hX hY
    have := PiL_ge X.dil Y.L
    rw [ML_win hX hY (by omega) (by omega), phMsg_bc_win _ _ _ _ h1 h2,
      if_pos ⟨hu, hw, hp, hd⟩]

lemma ML_pkW {u w : V} {φ : ℕ} {x : V} {c : ℕ} {l : V} : X.ML u w φ = some (pcPkW x c l) ↔
    ∃ Y, IsPh X Y ∧ Y.A0 + PiL X.dil Y.L ≤ φ ∧ φ < Y.A0 + PiL X.dil Y.L + X.dil * Y.L ∧
      (pk X.E X.j Y.Q ((φ - Y.A0 - PiL X.dil Y.L) / Y.L) u w).toList[(φ - Y.A0 -
        PiL X.dil Y.L) % Y.L]? = some x ∧ c = Y.c ∧ l = Y.l := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := ML_TL hX (by rw [h]; rfl)
    rcases frame_cases hX h1 h2 with ⟨i, hi, a, b, hab, rfl⟩ | ⟨Y, hY, hw1, hw2⟩
    · rw [ML_tok hX hi hab] at h
      by_cases hh : u = a ∧ w = b
      · rw [if_pos hh] at h; exact absurd (Option.some.inj h) (tokW_ne_pkW x c l)
      · rw [if_neg hh] at h; simp at h
    · rw [ML_win hX hY hw1 hw2] at h
      obtain ⟨p1, p2, -, p4, p5, p6⟩ := phMsg_pkW _ _ _ _ h
      exact ⟨Y, hY, p1, p2, p4, p5, p6⟩
  · rintro ⟨Y, hY, h1, h2, hx, rfl, rfl⟩
    have hs := win_sub hX hY
    have hg := isPh_gok hX hY
    have := PiL_ge X.dil Y.L
    have hle : X.dil * Y.L ≤ PiL X.dil Y.L := by unfold PiL; nlinarith
    rw [ML_win hX hY (by omega) (by omega), phMsg_pk_win _ _ _ _ (by omega) h1 h2 hg.L1]
    unfold slotMsg
    rw [hx]
    rfl

lemma ML_shape (u w : V) (φ : ℕ) : X.ML u w φ = none ∨ X.ML u w φ = some tokW ∨
    (∃ c, X.ML u w φ = some (bcW c)) ∨ ∃ x c l, X.ML u w φ = some (pcPkW x c l) := by
  classical
  by_cases h0 : φ = 0
  · left; subst h0; exact ML_zero hX u w
  by_cases hT : φ < X.TL
  · rcases frame_cases hX (by omega) hT with ⟨i, hi, a, b, hab, rfl⟩ | ⟨Y, hY, h1, h2⟩
    · rw [ML_tok hX hi hab]
      by_cases hh : u = a ∧ w = b
      · right; left; rw [if_pos hh]
      · left; rw [if_neg hh]
    · rw [ML_win hX hY h1 h2]
      have hg := isPh_gok hX hY
      have := PiL_ge X.dil Y.L
      by_cases hb : Y.A0 ≤ φ ∧ φ < Y.A0 + Y.L
      · rw [phMsg_bc_win _ _ _ _ hb.1 hb.2]
        by_cases hc : u ∈ Y.Q ∧ w ∈ Y.Q ∧ Y.par w = some u ∧ dep Y.par Y.rk u = φ - Y.A0
        · right; right; left; exact ⟨Y.c, if_pos hc⟩
        · left; exact if_neg hc
      · by_cases hp : Y.A0 + PiL X.dil Y.L ≤ φ ∧ φ < Y.A0 + PiL X.dil Y.L + X.dil * Y.L
        · rw [phMsg_pk_win _ _ _ _ (by omega) hp.1 hp.2 hg.L1]
          cases hsm : slotMsg (pk X.E X.j Y.Q ((φ - Y.A0 - PiL X.dil Y.L) / Y.L) u w)
              ((φ - Y.A0 - PiL X.dil Y.L) % Y.L) Y.c Y.l with
          | none => left; rfl
          | some m =>
            obtain ⟨x, -, rfl⟩ := slotMsg_eq hsm
            right; right; right; exact ⟨x, Y.c, Y.l, rfl⟩
        · left
          apply phMsg_quiet
          omega
  · left
    cases h : X.ML u w φ with
    | none => rfl
    | some m => exact absurd (ML_TL hX (by rw [h]; rfl)).2 hT

end PCG

end APSP.Stoc.Congest
