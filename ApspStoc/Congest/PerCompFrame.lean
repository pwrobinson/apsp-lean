import ApspStoc.Congest.PerCompEmb

/-!
# Frames: three-word messages for controllers (for `perCompR`)

A *logical controller* (`LCtl`) works in *frames* of three rounds: in every frame it sends a
three-word message (`W3`) to some neighbours, one word per round, and it decides from the decoded
frames received so far (`frameDec`). A frame during which the node was (partly) in a sub-run is
decoded as `none`. `LCtl.toCtl` turns a logical controller into a controller of `embP`; it sends
nothing in a frame that started inside a sub-run, starts sub-runs and halts only at frame
boundaries.

`embOK_of_frames`: if the logical controllers follow a logical schedule `ML` (in frames, with
sub-runs starting at frame boundaries `3 * lb k`), then the physical controllers follow the
physical schedule `M u v s = (ML u v (s / 3)).map (sel3 (s % 3))`, i.e. the hypotheses `EmbOK` of
the simulation lemma hold. The physical costs are three times the logical ones
(`sum_card_frames`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

/-- a three-word message -/
abbrev W3 (V : Type) := Word V × Word V × Word V

/-- a logical history: for every frame, the decoded messages, or `none` for a frame spent (partly)
in a sub-run -/
abbrev LH (V : Type) := List (Option (V → Option (W3 V)))

/-- word `i` of a three-word message -/
def sel3 {V : Type} (i : ℕ) (w : W3 V) : Word V :=
  if i = 0 then w.1 else if i = 1 then w.2.1 else w.2.2

/-- decoding of a frame from its three rounds -/
def decFr {V : Type} (a b c : Option (V → Option (Word V))) : Option (V → Option (W3 V)) :=
  match a, b, c with
  | some a, some b, some c => some (fun u => match a u, b u, c u with
      | some x, some y, some z => some (x, y, z)
      | _, _, _ => none)
  | _, _, _ => none

/-- the decoded complete frames of a physical history -/
def frameDec {V : Type} (H : PH V) : LH V :=
  (List.range (H.length / 3)).map
    (fun φ => decFr (H.getD (3 * φ) none) (H.getD (3 * φ + 1) none) (H.getD (3 * φ + 2) none))

/-- A logical controller (working on frames). -/
structure LCtl (V : Type) : Type 1 where
  send : NCtx V → (Agent V → Option Mem) → LH V → V → Option (W3 V)
  start : NCtx V → (Agent V → Option Mem) → LH V →
    Option (NCtx V × (Agent V → Option Mem) × Bool)
  halt : NCtx V → (Agent V → Option Mem) → LH V → Bool
  out : NCtx V → (Agent V → Option Mem) → Option (Agent V → Option Mem) → Agent V → Option Mem

/-- The physical controller of a logical one: word `s % 3` of the message of frame `s / 3`, unless
the frame started inside a sub-run; starts and halts at frame boundaries. -/
def LCtl.toCtl {V : Type} (L : LCtl V) : Ctl V where
  send c i H v := if (H.drop (3 * (H.length / 3))).all (fun o => o.isSome) then
      (L.send c i (frameDec H) v).map (sel3 (H.length % 3)) else none
  start c i H := if H.length % 3 = 0 then L.start c i (frameDec H) else none
  halt c i H := (H.length % 3 == 0) && L.halt c i (frameDec H)
  out := L.out

variable {V : Type} [Fintype V] [DecidableEq V]

section Frames

variable {ι : Type} (ks : Finset ι) (J : ι → Inst V) (lb ts : ι → ℕ)

/-- `v` is (partly) in a sub-run during frame `φ`. -/
def LInB (v : V) (φ : ℕ) : Prop := ∃ k ∈ ks, (J k).part v ∧ lb k ≤ φ ∧ 3 * φ < 3 * lb k + ts k

open Classical in
/-- the logical history of `v` after `φ` frames of the logical schedule `ML` -/
noncomputable def lhx (ML : V → V → ℕ → Option (W3 V)) (v : V) (φ : ℕ) : LH V :=
  (List.range φ).map (fun ψ => if LInB ks J lb ts v ψ then none else some (fun u => ML u v ψ))

/-- the physical schedule of a logical one -/
def physM (ML : V → V → ℕ → Option (W3 V)) (u v : V) (s : ℕ) : Option (Word V) :=
  (ML u v (s / 3)).map (sel3 (s % 3))

variable {ks J lb ts}

lemma inB_iff {v : V} {s : ℕ} :
    InB ks J (fun k => 3 * lb k) ts v s ↔
      ∃ k ∈ ks, (J k).part v ∧ 3 * lb k ≤ s ∧ s < 3 * lb k + ts k := Iff.rfl

lemma linB_of_inB {v : V} {s : ℕ} (h : InB ks J (fun k => 3 * lb k) ts v s) :
    LInB ks J lb ts v (s / 3) := by
  obtain ⟨k, hk, hv, h1, h2⟩ := h
  dsimp only at h1 h2
  refine ⟨k, hk, hv, by omega, by omega⟩

lemma inB_of_linB {v : V} {φ : ℕ} (h : LInB ks J lb ts v φ) :
    InB ks J (fun k => 3 * lb k) ts v (3 * φ) := by
  obtain ⟨k, hk, hv, h1, h2⟩ := h
  exact ⟨k, hk, hv, by dsimp only; omega, by dsimp only; omega⟩

lemma decFr_phys (ML : V → V → ℕ → Option (W3 V)) (v : V) (ψ : ℕ) :
    decFr (some (fun u => physM ML u v (3 * ψ))) (some (fun u => physM ML u v (3 * ψ + 1)))
      (some (fun u => physM ML u v (3 * ψ + 2))) = some (fun u => ML u v ψ) := by
  simp only [decFr, physM]
  congr 1
  funext u
  have e0 : 3 * ψ / 3 = ψ := by omega
  have e1 : (3 * ψ + 1) / 3 = ψ := by omega
  have e2 : (3 * ψ + 2) / 3 = ψ := by omega
  have m0 : 3 * ψ % 3 = 0 := by omega
  have m1 : (3 * ψ + 1) % 3 = 1 := by omega
  have m2 : (3 * ψ + 2) % 3 = 2 := by omega
  rw [e0, e1, e2, m0, m1, m2]
  cases ML u v ψ with
  | none => rfl
  | some w => obtain ⟨a, b, c⟩ := w; rfl

open Classical in
lemma getD_hx (ML : V → V → ℕ → Option (W3 V)) (v : V) {s i : ℕ} (hi : i < s) :
    (hx ks J (fun k => 3 * lb k) ts (physM ML) v s).getD i none =
      if InB ks J (fun k => 3 * lb k) ts v i then none else some (fun u => physM ML u v i) := by
  classical
  simp [hx, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- **Decoding the frames** of the physical history of a logical schedule gives the logical
history. -/
lemma frameDec_hx (ML : V → V → ℕ → Option (W3 V)) (v : V) (s : ℕ) :
    frameDec (hx ks J (fun k => 3 * lb k) ts (physM ML) v s) = lhx ks J lb ts ML v (s / 3) := by
  classical
  unfold frameDec lhx
  have hlen : (hx ks J (fun k => 3 * lb k) ts (physM ML) v s).length = s := by simp [hx]
  rw [hlen]
  apply List.map_congr_left
  intro ψ hψ
  rw [List.mem_range] at hψ
  have hlt : 3 * ψ + 2 < s := by omega
  rw [getD_hx (ks := ks) (J := J) (lb := lb) (ts := ts) ML v (show 3 * ψ < s by omega),
    getD_hx (ks := ks) (J := J) (lb := lb) (ts := ts) ML v (show 3 * ψ + 1 < s by omega),
    getD_hx (ks := ks) (J := J) (lb := lb) (ts := ts) ML v hlt]
  by_cases hL : LInB ks J lb ts v ψ
  · rw [if_pos hL, if_pos (inB_of_linB hL)]
    rfl
  · rw [if_neg hL]
    have hn : ∀ i < 3, ¬ InB ks J (fun k => 3 * lb k) ts v (3 * ψ + i) := by
      intro i hi hB
      have := linB_of_inB hB
      rw [show (3 * ψ + i) / 3 = ψ by omega] at this
      exact hL this
    rw [if_neg (by simpa using hn 0 (by omega)), if_neg (hn 1 (by omega)), if_neg (hn 2 (by omega))]
    exact decFr_phys ML v ψ

end Frames

section Lift

variable {ι : Type} (L : LCtl V) (B : Proto V) (I : Inst V) (x : Agent V → Mem) (ω : V → B.Ω)
  (ks : Finset ι) (J : ι → Inst V) (xs : ι → Agent V → Mem) (lb ts : ι → ℕ) (own : ι → V → Bool)
  (ML : V → V → ℕ → Option (W3 V)) (TL : ℕ)

/-- The hypotheses on a logical plan. -/
structure LOK : Prop where
  part : ∀ k ∈ ks, ∀ v, (J k).part v → I.part v
  adj : ∀ k ∈ ks, ∀ u v, (J k).G.Adj u v → I.G.Adj u v
  sep : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' →
    3 * lb k + ts k < 3 * lb k' ∨ 3 * lb k' + ts k' < 3 * lb k
  ownU : ∀ v, ∀ k ∈ ks, ∀ k' ∈ ks, (J k).part v → own k v = true → (J k').part v →
    own k' v = true → k = k'
  b1 : ∀ k ∈ ks, 1 ≤ lb k
  bT : ∀ k ∈ ks, 3 * lb k + ts k ≤ 3 * TL
  halts : ∀ k ∈ ks, HaltsAt B (J k) (xs k) ω (ts k)
  proper : ∀ k ∈ ks, ProperUpTo B (J k) (xs k) ω (ts k)
  Madj : ∀ φ u v, (ML u v φ).isSome → I.G.Adj u v
  Mok : ∀ φ u v w, ML u v φ = some w →
    WordOK (Fintype.card V) w.1 ∧ WordOK (Fintype.card V) w.2.1 ∧ WordOK (Fintype.card V) w.2.2
  MB : ∀ φ u v, (ML u v φ).isSome → ¬ LInB ks J lb ts u φ ∧ ¬ LInB ks J lb ts v φ
  send : ∀ v, I.part v → ∀ φ < TL, ¬ LInB ks J lb ts v φ →
    L.send (I.ctx v) (inpAt I x v) (lhx ks J lb ts ML v φ) = fun u => ML v u φ
  start : ∀ v, I.part v → ∀ φ, 1 ≤ φ → φ ≤ TL →
    (∀ k ∈ ks, (J k).part v → lb k = φ →
      L.start (I.ctx v) (inpAt I x v) (lhx ks J lb ts ML v φ) =
        some ((J k).ctx v, inpAt (J k) (xs k) v, own k v)) ∧
    ((∀ k ∈ ks, (J k).part v → lb k ≠ φ) →
      L.start (I.ctx v) (inpAt I x v) (lhx ks J lb ts ML v φ) = none)
  halt : ∀ v, I.part v → ∀ φ ≤ TL,
    (L.halt (I.ctx v) (inpAt I x v) (lhx ks J lb ts ML v φ) = true ↔ φ = TL)

variable {L B I x ω ks J xs lb ts own ML TL}

lemma sel3_ok {w : W3 V} (h : WordOK (Fintype.card V) w.1 ∧ WordOK (Fintype.card V) w.2.1 ∧
    WordOK (Fintype.card V) w.2.2) (i : ℕ) : WordOK (Fintype.card V) (sel3 i w) := by
  unfold sel3
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- **From frames to rounds**: a logical plan gives a physical plan. -/
theorem embOK_of_frames (h : LOK L B I x ω ks J xs lb ts own ML TL) :
    EmbOK L.toCtl B I x ω ks J xs (fun k => 3 * lb k) ts own (physM ML) (3 * TL) where
  part := h.part
  adj := h.adj
  sep := h.sep
  ownU := h.ownU
  b1 := fun k hk => by have := h.b1 k hk; omega
  bT := h.bT
  halts := h.halts
  proper := h.proper
  Madj := fun s u v hs => h.Madj (s / 3) u v (by
    unfold physM at hs
    cases hm : ML u v (s / 3) with
    | none => rw [hm] at hs; exact absurd hs (by simp)
    | some w => rfl)
  Mok := fun s u v w hw => by
    unfold physM at hw
    cases hm : ML u v (s / 3) with
    | none => rw [hm] at hw; exact absurd hw (by simp)
    | some w' =>
      rw [hm] at hw
      simp only [Option.map_some, Option.some.injEq] at hw
      rw [← hw]
      exact sel3_ok (h.Mok _ _ _ _ hm) _
  MB := fun s u v hs => by
    have hs' : (ML u v (s / 3)).isSome := by
      unfold physM at hs
      cases hm : ML u v (s / 3) with
      | none => rw [hm] at hs; exact absurd hs (by simp)
      | some w => rfl
    obtain ⟨h1, h2⟩ := h.MB _ u v hs'
    exact ⟨fun hB => h1 (linB_of_inB hB), fun hB => h2 (linB_of_inB hB)⟩
  send := fun v hv s hs hB => by
    classical
    have hlen : (hx ks J (fun k => 3 * lb k) ts (physM ML) v s).length = s := by simp [hx]
    funext u
    show (if ((hx ks J (fun k => 3 * lb k) ts (physM ML) v s).drop
        (3 * ((hx ks J (fun k => 3 * lb k) ts (physM ML) v s).length / 3))).all
        (fun o => o.isSome) then _ else none) = _
    rw [hlen]
    by_cases hL : LInB ks J lb ts v (s / 3)
    · -- the frame started inside a sub-run
      have h0 := inB_of_linB hL
      have hs0 : 3 * (s / 3) < s := by
        by_contra hge
        have : s = 3 * (s / 3) := by omega
        rw [← this] at h0
        exact hB h0
      have hdrop : ((hx ks J (fun k => 3 * lb k) ts (physM ML) v s).drop (3 * (s / 3))).all
          (fun o => o.isSome) = false := by
        rw [List.all_eq_false]
        refine ⟨none, ?_, by simp⟩
        rw [List.mem_iff_getElem?]
        refine ⟨0, ?_⟩
        rw [List.getElem?_drop, Nat.add_zero]
        have := getD_hx (ks := ks) (J := J) (lb := lb) (ts := ts) ML v hs0
        rw [if_pos h0] at this
        rw [List.getD_eq_getElem?_getD] at this
        cases hh : (hx ks J (fun k => 3 * lb k) ts (physM ML) v s)[3 * (s / 3)]? with
        | none =>
          exfalso
          rw [List.getElem?_eq_none_iff] at hh
          rw [hlen] at hh
          omega
        | some o => rw [hh] at this; simp at this; rw [this]
      rw [hdrop]
      simp only [Bool.false_eq_true, ite_false]
      unfold physM
      cases hm : ML v u (s / 3) with
      | none => rfl
      | some w => exact absurd (h.MB _ v u (by rw [hm]; rfl)).1 (fun h' => h' hL)
    · have hall : ((hx ks J (fun k => 3 * lb k) ts (physM ML) v s).drop (3 * (s / 3))).all
          (fun o => o.isSome) = true := by
        rw [List.all_eq_true]
        intro o ho
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
        rw [List.getElem_drop]
        have hi' : 3 * (s / 3) + i < s := by
          rw [List.length_drop, hlen] at hi; omega
        have := getD_hx (ks := ks) (J := J) (lb := lb) (ts := ts) ML v hi'
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi')] at this
        simp only [Option.getD_some] at this
        rw [this]
        rw [if_neg]
        · rfl
        · intro hB'
          have := linB_of_inB hB'
          rw [show (3 * (s / 3) + i) / 3 = s / 3 by omega] at this
          exact hL this
      rw [hall, if_pos rfl, frameDec_hx, h.send v hv (s / 3) (by omega) hL]
      rfl
  start := fun v hv s hs1 hsT _ => by
    classical
    have hlen : (hx ks J (fun k => 3 * lb k) ts (physM ML) v s).length = s := by simp [hx]
    by_cases hm : s % 3 = 0
    · obtain ⟨φ, rfl⟩ : ∃ φ, s = 3 * φ := ⟨s / 3, by omega⟩
      have hst := h.start v hv φ (by omega) (by omega)
      have e : (3 * φ) / 3 = φ := by omega
      refine ⟨fun k hk hvk hbk => ?_, fun hno => ?_⟩
      · show (if (hx ks J (fun k => 3 * lb k) ts (physM ML) v (3 * φ)).length % 3 = 0 then _
          else none) = _
        rw [hlen, if_pos hm, frameDec_hx, e]
        exact hst.1 k hk hvk (by omega)
      · show (if (hx ks J (fun k => 3 * lb k) ts (physM ML) v (3 * φ)).length % 3 = 0 then _
          else none) = _
        rw [hlen, if_pos hm, frameDec_hx, e]
        exact hst.2 (fun k hk hvk hb => hno k hk hvk (by omega))
    · refine ⟨fun k hk hvk hbk => absurd hbk (by omega), fun _ => ?_⟩
      show (if (hx ks J (fun k => 3 * lb k) ts (physM ML) v s).length % 3 = 0 then _
        else none) = _
      rw [hlen, if_neg hm]
  halt := fun v hv s hs _ => by
    classical
    have hlen : (hx ks J (fun k => 3 * lb k) ts (physM ML) v s).length = s := by simp [hx]
    show ((hx ks J (fun k => 3 * lb k) ts (physM ML) v s).length % 3 == 0 &&
      L.halt _ _ (frameDec (hx ks J (fun k => 3 * lb k) ts (physM ML) v s))) = true ↔ _
    rw [hlen, frameDec_hx]
    by_cases hm : s % 3 = 0
    · obtain ⟨φ, rfl⟩ : ∃ φ, s = 3 * φ := ⟨s / 3, by omega⟩
      rw [show (3 * φ) / 3 = φ by omega]
      simp only [hm, beq_self_eq_true, Bool.true_and]
      rw [h.halt v hv φ (by omega)]
      omega
    · have : (s % 3 == 0) = false := by simpa using hm
      rw [this, Bool.false_and]
      simp only [Bool.false_eq_true, false_iff]
      omega

end Lift

/-! ## Counting the words of three-word messages -/

lemma sum_card_frames (ML : V → V → ℕ → Option (W3 V)) (TL : ℕ) (Pr : V × V → Prop)
    [DecidablePred Pr] :
    ∑ s ∈ range (3 * TL), ((univ.filter (fun uv : V × V => (physM ML uv.1 uv.2 s).isSome)).filter
      Pr).card =
      3 * ∑ φ ∈ range TL, ((univ.filter (fun uv : V × V => (ML uv.1 uv.2 φ).isSome)).filter
        Pr).card := by
  induction TL with
  | zero => simp
  | succ TL ih =>
    rw [show 3 * (TL + 1) = 3 * TL + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, ih, sum_range_succ]
    have key : ∀ i < 3, (univ.filter (fun uv : V × V => (physM ML uv.1 uv.2 (3 * TL + i)).isSome))
        = univ.filter (fun uv : V × V => (ML uv.1 uv.2 TL).isSome) := by
      intro i hi
      ext uv
      simp only [mem_filter, mem_univ, true_and, physM, show (3 * TL + i) / 3 = TL by omega]
      cases ML uv.1 uv.2 TL <;> simp
    have k0 := key 0 (by omega)
    have k1 := key 1 (by omega)
    have k2 := key 2 (by omega)
    simp only [Nat.add_zero] at k0
    rw [k0, k1, k2]
    ring

end APSP.Stoc.Congest
