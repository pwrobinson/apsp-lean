import ApspStoc.Congest.Core

/-!
# Combinators of the CONGEST semantics

* `seqP A B`: every node runs `A`; in the round where `A` halts at the node, the node starts `B`
  on the pair (its input, its output of `A`) for every agent it simulates. If all participants halt
  `A` in the same round (which a successful run of `A` guarantees), then `B` starts everywhere in
  that round, and the run of `seqP A B` is the run of `A` followed by the run of `B`.
* `callP F P`: every node applies the uniform local function `F` to the data of its agents and runs
  `P` on the results.
* `locP F`: a local computation (`0` rounds, no messages).
* `skipP`: the empty protocol.

The main result is `bindI`: the costs of `seqP A B` add up and the failure probabilities add up
(union bound over independent seeds). A run of `seqP A B` sends properly (`ProperUpTo`) if the runs
of `A` and `B` do (`properUpTo_seq`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Pairing of two dynamically typed values. -/
def pairMem (m m' : Mem) : Mem := ⟨m.1 × m'.1, (m.2, m'.2)⟩

/-- Pairing of the data of the agents of a node. -/
def pairIn (a b : Agent V → Option Mem) : Agent V → Option Mem := fun g =>
  match a g, b g with
  | some m, some m' => some (pairMem m m')
  | _, _ => none

/-! ## Sequential composition -/

/-- States of `seqP A B`: in phase `A` (with the saved input and the seed of `B`), or in phase `B`. -/
abbrev SeqS (A B : Proto V) : Type 1 := (A.S × (Agent V → Option Mem) × B.Ω) ⊕ B.S

/-- Switch to `B` as soon as `A` has halted. -/
def toB (A B : Proto V) (c : NCtx V) (inp : Agent V → Option Mem) (ωB : B.Ω) (sA : A.S) :
    SeqS A B :=
  match A.out sA with
  | some y => .inr (B.init c (pairIn inp y) ωB)
  | none => .inl (sA, inp, ωB)

/-- Sequential composition. -/
@[reducible] def seqP (A B : Proto V) : Proto V where
  S := SeqS A B
  Ω := A.Ω × B.Ω
  init c inp ω := toB A B c inp ω.2 (A.init c inp ω.1)
  send c s u := Sum.elim (fun a => A.send c a.1 u) (fun b => B.send c b u) s
  recv c s m := Sum.elim (fun a => toB A B c a.2.1 a.2.2 (A.recv c a.1 m))
    (fun b => .inr (B.recv c b m)) s
  out s := Sum.elim (fun _ => none) B.out s

omit [Fintype V] [DecidableEq V] in
lemma seqP_out_inl {A B : Proto V} (a) : (seqP A B).out (.inl a) = none := rfl
omit [Fintype V] [DecidableEq V] in
lemma seqP_out_inr {A B : Proto V} (b) : (seqP A B).out (.inr b) = B.out b := rfl
omit [Fintype V] [DecidableEq V] in
lemma seqP_recv_inl {A B : Proto V} (c : NCtx V) (a) (m) :
    (seqP A B).recv c (.inl a) m = toB A B c a.2.1 a.2.2 (A.recv c a.1 m) := rfl
omit [Fintype V] [DecidableEq V] in
lemma seqP_recv_inr {A B : Proto V} (c : NCtx V) (b) (m) :
    (seqP A B).recv c (.inr b) m = .inr (B.recv c b m) := rfl

/-! ### The run of `seqP A B` -/

section SeqRun

variable {A B : Proto V} {I : Inst V} {x x' : Agent V → Mem} {ωA : V → A.Ω} {ωB : V → B.Ω}
  {tA : ℕ}

/-- the combined seeds -/
def combine (ωA : V → A.Ω) (ωB : V → B.Ω) : V → (seqP A B).Ω := fun v => (ωA v, ωB v)

/-- The expected state of `seqP A B` at time `t`. -/
noncomputable def expSt (A B : Proto V) (I : Inst V) (x x' : Agent V → Mem) (ωA : V → A.Ω)
    (ωB : V → B.Ω) (tA t : ℕ) (v : V) : SeqS A B :=
  if t < tA then .inl (st A I x ωA t v, inpAt I x v, ωB v) else .inr (st B I x' ωB (t - tA) v)

set_option linter.unusedVariables false in
/-- the input of `B` at the participants is the pair (input, output of `A`) -/
def SwitchOK (A B : Proto V) (I : Inst V) (x x' : Agent V → Mem) (ωA : V → A.Ω) (tA : ℕ) : Prop :=
  ∀ v, I.part v → ∀ m, A.out (st A I x ωA tA v) = some m → pairIn (inpAt I x v) m = inpAt I x' v

lemma msg_seq_A (hA : HaltsAt A I x ωA tA) {t : ℕ} (ht : t < tA)
    (hst : ∀ v, I.part v → st (seqP A B) I x (combine ωA ωB) t v =
      .inl (st A I x ωA t v, inpAt I x v, ωB v)) (u v : V) :
    msg (seqP A B) I (st (seqP A B) I x (combine ωA ωB) t) u v = msg A I (st A I x ωA t) u v := by
  classical
  by_cases hadj : I.G.Adj u v
  · have hu := I.adj_part u v hadj
    have hnone := hA.2 t ht u hu
    simp only [msg, hadj, true_and, hst u hu, hnone]
    rfl
  · simp only [msg, hadj, false_and, ite_false]

lemma msg_seq_B (hst : ∀ v, I.part v → st (seqP A B) I x (combine ωA ωB) t v =
      .inr (st B I x' ωB s v)) (u v : V) :
    msg (seqP A B) I (st (seqP A B) I x (combine ωA ωB) t) u v = msg B I (st B I x' ωB s) u v := by
  classical
  by_cases hadj : I.G.Adj u v
  · have hu := I.adj_part u v hadj
    simp only [msg, hadj, true_and, hst u hu]
    rfl
  · simp only [msg, hadj, false_and, ite_false]

/-- The run of `seqP A B` follows the runs of `A` and `B` at all participants. -/
lemma st_seq (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) :
    ∀ t v, I.part v → st (seqP A B) I x (combine ωA ωB) t v = expSt A B I x x' ωA ωB tA t v := by
  intro t
  induction t with
  | zero =>
    intro v hv
    simp only [st, st0, seqP, combine, expSt]
    by_cases h0 : 0 < tA
    · have hn : A.out (A.init (I.ctx v) (inpAt I x v) (ωA v)) = none := hA.2 0 h0 v hv
      simp only [toB, hn, h0, ite_true]
    · have htA : tA = 0 := by omega
      subst htA
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (hA.1 v hv)
      have hm' : A.out (A.init (I.ctx v) (inpAt I x v) (ωA v)) = some m := hm
      simp only [toB, hm', lt_irrefl, ite_false, Nat.sub_zero, st, st0]
      rw [hsw v hv m hm]
  | succ t ih =>
    intro v hv
    rw [st_succ]
    unfold step
    by_cases ht : t < tA
    · have hst : ∀ w, I.part w → st (seqP A B) I x (combine ωA ωB) t w =
          .inl (st A I x ωA t w, inpAt I x w, ωB w) := fun w hw => by
        rw [ih w hw, expSt, ite_eq_left_iff.2 (fun h => absurd ht h)]
      have hmsg := msg_seq_A (B := B) hA ht hst
      rw [hst v hv, seqP_out_inl, seqP_recv_inl, if_neg (by simp)]
      simp only [hmsg]
      have hn : A.out (st A I x ωA t v) = none := hA.2 t ht v hv
      have hA1 : st A I x ωA (t + 1) v = A.recv (I.ctx v) (st A I x ωA t v)
          (fun u => msg A I (st A I x ωA t) u v) := by
        rw [st_succ]; simp [step, hn]
      rw [← hA1]
      unfold expSt
      by_cases ht1 : t + 1 < tA
      · have hn1 : A.out (st A I x ωA (t + 1) v) = none := hA.2 (t + 1) ht1 v hv
        rw [if_pos ht1]
        unfold toB
        rw [hn1]
      · have htA : tA = t + 1 := by omega
        subst htA
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (hA.1 v hv)
        simp only [toB, hm, lt_irrefl, ite_false, Nat.sub_self]
        rw [hsw v hv m hm]
        rfl
    · have hst : ∀ w, I.part w → st (seqP A B) I x (combine ωA ωB) t w =
          .inr (st B I x' ωB (t - tA) w) := fun w hw => by
        rw [ih w hw, expSt, if_neg ht]
      have hmsg := msg_seq_B (A := A) (s := t - tA) hst
      rw [hst v hv, seqP_out_inr, seqP_recv_inr]
      have ht1 : ¬ t + 1 < tA := by omega
      have hsub : t + 1 - tA = t - tA + 1 := by omega
      rw [expSt, if_neg ht1, hsub, st_succ]
      simp only [hmsg, step]
      by_cases hb : (B.out (st B I x' ωB (t - tA) v)).isSome <;> simp [hb]

lemma st_seq_A (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) {t : ℕ} (ht : t < tA)
    (v : V) (hv : I.part v) :
    st (seqP A B) I x (combine ωA ωB) t v = .inl (st A I x ωA t v, inpAt I x v, ωB v) := by
  rw [st_seq hA hsw t v hv, expSt, if_pos ht]

lemma st_seq_B (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) (s : ℕ)
    (v : V) (hv : I.part v) :
    st (seqP A B) I x (combine ωA ωB) (tA + s) v = .inr (st B I x' ωB s v) := by
  rw [st_seq hA hsw (tA + s) v hv, expSt, if_neg (by omega), Nat.add_sub_cancel_left]

lemma sentSet_seq_A (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) {t : ℕ}
    (ht : t < tA) :
    sentSet (seqP A B) I (st (seqP A B) I x (combine ωA ωB) t) = sentSet A I (st A I x ωA t) := by
  classical
  unfold sentSet
  simp only [msg_seq_A (B := B) hA ht (fun v hv => st_seq_A hA hsw ht v hv)]

lemma sentSet_seq_B (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) (s : ℕ) :
    sentSet (seqP A B) I (st (seqP A B) I x (combine ωA ωB) (tA + s)) =
      sentSet B I (st B I x' ωB s) := by
  classical
  unfold sentSet
  simp only [msg_seq_B (fun v hv => st_seq_B (ωB := ωB) hA hsw s v hv)]

lemma msgsUpTo_seq (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) (s : ℕ) :
    msgsUpTo (seqP A B) I x (combine ωA ωB) (tA + s) =
      msgsUpTo A I x ωA tA + msgsUpTo B I x' ωB s := by
  unfold msgsUpTo
  rw [sum_range_add]
  congr 1
  · exact sum_congr rfl (fun t ht => by rw [sentSet_seq_A hA hsw (mem_range.1 ht)])
  · exact sum_congr rfl (fun t _ => by rw [sentSet_seq_B hA hsw t])

lemma loadUpTo_seq (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) (s : ℕ)
    (e : Sym2 V) :
    loadUpTo (seqP A B) I x (combine ωA ωB) (tA + s) e =
      loadUpTo A I x ωA tA e + loadUpTo B I x' ωB s e := by
  classical
  unfold loadUpTo
  rw [sum_range_add]
  congr 1
  · exact sum_congr rfl (fun t ht => by rw [sentSet_seq_A hA hsw (mem_range.1 ht)])
  · exact sum_congr rfl (fun t _ => by rw [sentSet_seq_B hA hsw t])

lemma haltsAt_seq (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) {tB : ℕ}
    (hB : HaltsAt B I x' ωB tB) : HaltsAt (seqP A B) I x (combine ωA ωB) (tA + tB) := by
  refine ⟨fun v hv => ?_, fun s hs v hv => ?_⟩
  · rw [st_seq_B hA hsw tB v hv]; exact hB.1 v hv
  · by_cases h : s < tA
    · rw [st_seq_A hA hsw h v hv]; rfl
    · obtain ⟨s', rfl⟩ : ∃ s', s = tA + s' := ⟨s - tA, by omega⟩
      rw [st_seq_B hA hsw s' v hv]
      exact hB.2 s' (by omega) v hv

/-- Proper sends of `seqP A B`: those of `A`, then those of `B`. -/
lemma properUpTo_seq (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA)
    (hpA : ProperUpTo A I x ωA tA) {tB : ℕ} (hpB : ProperUpTo B I x' ωB tB) :
    ProperUpTo (seqP A B) I x (combine ωA ωB) (tA + tB) := by
  intro s hs u hu hout v hv
  by_cases h : s < tA
  · rw [st_seq_A hA hsw h u hu] at hv
    exact hpA s h u hu (hA.2 s h u hu) v hv
  · obtain ⟨s', rfl⟩ : ∃ s', s = tA + s' := ⟨s - tA, by omega⟩
    rw [st_seq_B hA hsw s' u hu] at hout hv
    exact hpB s' (by omega) u hu hout v hv

lemma outAt_seq (hA : HaltsAt A I x ωA tA) (hsw : SwitchOK A B I x x' ωA tA) (s : ℕ)
    (g : Agent V) : outAt (seqP A B) I x (combine ωA ωB) (tA + s) g = outAt B I x' ωB s g := by
  unfold outAt
  cases hg : I.host g with
  | none => rfl
  | some v =>
    dsimp only
    rw [st_seq_B hA hsw s v (I.host_part g v hg)]
    rfl

/-- If `A` succeeds with outputs `y`, the input of `B` is the pair (input, `y`). -/
lemma switchOK_of {y : Agent V → Mem} (hy : ∀ g, (I.host g).isSome → outAt A I x ωA tA g = some (y g)) :
    SwitchOK A B I x (fun g => pairMem (x g) (y g)) ωA tA := by
  intro v hv m hm
  funext g
  unfold pairIn inpAt
  by_cases hg : I.host g = some v
  · have h1 := hy g (by simp [hg])
    simp only [outAt, hg, hm, Option.bind_some] at h1
    simp only [hg, ite_true, h1]
  · simp only [hg, ite_false]

end SeqRun

/-! ### Counting over product seeds -/

open Classical in
lemma card_filter_arrow_prod {α β : Type} [Fintype α] [Fintype β] (R : (V → α × β) → Prop) :
    (((univ.filter R).card : ℕ) : ℝ) =
      ∑ a : V → α, (((univ.filter (fun b : V → β => R (fun v => (a v, b v)))).card : ℕ) : ℝ) := by
  classical
  have e : (V → α × β) ≃ (V → α) × (V → β) := Equiv.arrowProdEquivProdArrow V (fun _ => α) (fun _ => β)
  have h1 : (univ.filter R).card =
      (univ.filter (fun ab : (V → α) × (V → β) => R (fun v => (ab.1 v, ab.2 v)))).card := by
    refine card_bij (fun ω _ => ((fun v => (ω v).1), (fun v => (ω v).2))) ?_ ?_ ?_
    · intro ω hω; simpa using hω
    · intro ω₁ _ ω₂ _ h
      simp only [Prod.mk.injEq] at h
      funext v
      exact Prod.ext (congrFun h.1 v) (congrFun h.2 v)
    · intro ab hab
      exact ⟨fun v => (ab.1 v, ab.2 v), by simpa using hab, rfl⟩
  rw [h1, card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl (fun a _ => ?_)
  rw [card_filter]
  push_cast
  rfl

lemma card_arrow_prod {α β : Type} [Fintype α] [Fintype β] :
    (Fintype.card (V → α × β) : ℝ) = (Fintype.card (V → α) : ℝ) * (Fintype.card (V → β) : ℝ) := by
  rw [Fintype.card_congr (Equiv.arrowProdEquivProdArrow V (fun _ => α) (fun _ => β)), Fintype.card_prod]
  push_cast; ring

/-! ### Soundness of sequential composition -/

/-- **Sequential composition**: costs add up, failure probabilities add up. -/
theorem bindI {A B : Proto V} {I : Inst V} {x : Agent V → Mem} {QA QB : (Agent V → Mem) → Prop}
    {p q : Prof V} {δ δ' : ℝ} (hA : ImplI A I x QA p δ)
    (hB : ∀ y, QA y → ImplI B I (fun g => pairMem (x g) (y g)) QB q δ') (hδ' : 0 ≤ δ') :
    ImplI (seqP A B) I x QB (p + q) (δ + δ') := by
  classical
  -- a success of `A` determines the input of `B`
  have key : ∀ (ωA : V → A.Ω) (hs : Succ A I x QA p ωA), ∃ y, QA y ∧ ∀ ωB : V → B.Ω,
      Succ B I (fun g => pairMem (x g) (y g)) QB q ωB →
        Succ (seqP A B) I x QB (p + q) (combine ωA ωB) := by
    intro ωA hs
    obtain ⟨tA, hhA, hpA, hrA, hmA, hlA, y, hy, hQy⟩ := hs
    refine ⟨y, hQy, fun ωB hsB => ?_⟩
    obtain ⟨tB, hhB, hpB, hrB, hmB, hlB, z, hz, hQz⟩ := hsB
    have hsw := switchOK_of (B := B) (tA := tA) hy
    refine ⟨tA + tB, haltsAt_seq hhA hsw hhB, properUpTo_seq hhA hsw hpA hpB, ?_, ?_,
      fun e => ?_, z, fun g hg => ?_, hQz⟩
    · simp only [Prof.rounds_add]; omega
    · rw [msgsUpTo_seq hhA hsw]; simp only [Prof.msgs_add]; omega
    · rw [loadUpTo_seq hhA hsw]; simp only [Prof.load_add, Pi.add_apply]
      exact Nat.add_le_add (hlA e) (hlB e)
    · rw [outAt_seq hhA hsw]; exact hz g hg
  -- count
  unfold ImplI failProb at *
  set nA := (Fintype.card (V → A.Ω) : ℝ)
  set nB := (Fintype.card (V → B.Ω) : ℝ)
  have hnA : 0 < nA := card_pos_fun A
  have hnB : 0 < nB := card_pos_fun B
  have hcard : (Fintype.card (V → (seqP A B).Ω) : ℝ) = nA * nB := card_arrow_prod
  rw [hcard]
  have hsplit := card_filter_arrow_prod (V := V) (α := A.Ω) (β := B.Ω)
    (fun ω => ¬ Succ (seqP A B) I x QB (p + q) ω)
  have hsplit' : (((univ.filter (fun ω : V → (seqP A B).Ω =>
      ¬ Succ (seqP A B) I x QB (p + q) ω)).card : ℕ) : ℝ) = ∑ ωA : V → A.Ω,
        (((univ.filter (fun ωB : V → B.Ω =>
          ¬ Succ (seqP A B) I x QB (p + q) (fun v => (ωA v, ωB v)))).card : ℕ) : ℝ) := by
    convert hsplit using 3 <;> first | (ext; simp) | (congr 1; ext; simp)
  rw [hsplit']
  -- bound each slice
  have hslice : ∀ ωA : V → A.Ω,
      (((univ.filter (fun ωB : V → B.Ω =>
          ¬ Succ (seqP A B) I x QB (p + q) (fun v => (ωA v, ωB v)))).card : ℕ) : ℝ) ≤
        (if Succ A I x QA p ωA then δ' * nB else nB) := by
    intro ωA
    split_ifs with hs
    · obtain ⟨y, hQy, hy⟩ := key ωA hs
      have hb := hB y hQy
      rw [div_le_iff₀ hnB] at hb
      refine le_trans ?_ hb
      exact_mod_cast card_le_card (fun ωB => by
        simp only [mem_filter, mem_univ, true_and]
        exact fun h1 h2 => h1 (hy ωB h2))
    · rw [show nB = ((Fintype.card (V → B.Ω) : ℕ) : ℝ) from rfl]
      exact_mod_cast card_le_univ _
  calc (∑ ωA : V → A.Ω, (((univ.filter (fun ωB : V → B.Ω =>
          ¬ Succ (seqP A B) I x QB (p + q) (fun v => (ωA v, ωB v)))).card : ℕ) : ℝ)) / (nA * nB)
      ≤ (∑ ωA : V → A.Ω, (if Succ A I x QA p ωA then δ' * nB else nB)) / (nA * nB) := by
        gcongr with ωA; exact hslice ωA
    _ ≤ (∑ ωA : V → A.Ω, ((if Succ A I x QA p ωA then 0 else nB) + δ' * nB)) / (nA * nB) := by
        gcongr with ωA
        split_ifs <;> nlinarith
    _ = ((univ.filter (fun ωA : V → A.Ω => ¬ Succ A I x QA p ωA)).card : ℝ) / nA + δ' := by
        have h1 : (∑ ωA : V → A.Ω, (if Succ A I x QA p ωA then (0 : ℝ) else nB)) =
            ((univ.filter (fun ωA : V → A.Ω => ¬ Succ A I x QA p ωA)).card : ℝ) * nB := by
          rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
        have h2 : (∑ _ωA : V → A.Ω, δ' * nB) = nA * (δ' * nB) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
        rw [sum_add_distrib, h1, h2]
        field_simp
    _ ≤ δ + δ' := by linarith

/-! ## Local computations and calls -/

open Classical in
/-- The uniform local function `F` applied to the data of the agents of a node (with their local
views); `none` if the data has the wrong type or the agent's view is unknown. -/
noncomputable def locOut (F : LocFn) (c : NCtx V) (inp : Agent V → Option Mem) :
    Agent V → Option Mem := fun g =>
  match inp g, c.view g with
  | some m, some vw => if h : m.1 = F.α V then some ⟨F.β V, F.f V g vw (cast h m.2)⟩ else none
  | _, _ => none

/-- Run `P` on the results of the local computation `F`. -/
@[reducible] noncomputable def callP (F : LocFn) (P : Proto V) : Proto V where
  S := P.S
  Ω := P.Ω
  init c inp ω := P.init c (locOut F c inp) ω
  send := P.send
  recv := P.recv
  out := P.out

/-- A local computation: halts in round `0`. -/
@[reducible] noncomputable def locP (F : LocFn) : Proto V where
  S := Agent V → Option Mem
  Ω := Unit
  init c inp _ := locOut F c inp
  send _ _ _ := none
  recv _ s _ := s
  out s := some s

/-- The empty protocol: halts in round `0` with its input as output. -/
@[reducible] def skipP : Proto V where
  S := Agent V → Option Mem
  Ω := Unit
  init _ inp _ := inp
  send _ _ _ := none
  recv _ s _ := s
  out s := some s

lemma st_callP (F : LocFn) (P : Proto V) (I : Inst V) {x x' : Agent V → Mem}
    (hx : ∀ v, locOut F (I.ctx v) (inpAt I x v) = inpAt I x' v) (ω : V → P.Ω) (t : ℕ) :
    st (callP F P) I x ω t = st P I x' ω t := by
  induction t with
  | zero => funext v; simp only [st, st0, callP, hx]
  | succ t ih => rw [st_succ, st_succ, ← ih]; rfl

theorem callI (F : LocFn) {P : Proto V} {I : Inst V} {x x' : Agent V → Mem}
    {Q : (Agent V → Mem) → Prop} {p : Prof V} {δ : ℝ}
    (hx : ∀ v, locOut F (I.ctx v) (inpAt I x v) = inpAt I x' v) (h : ImplI P I x' Q p δ) :
    ImplI (callP F P) I x Q p δ := by
  have hst := st_callP F P I hx
  have hS : ∀ ω, Succ (callP F P) I x Q p ω ↔ Succ P I x' Q p ω := fun ω => by
    have h1 : st (callP F P) I x ω = st P I x' ω := funext (hst ω)
    simp only [Succ, HaltsAt, ProperUpTo, msgsUpTo, loadUpTo, outAt, sentSet, msg]
    rw [h1]; rfl
  unfold ImplI failProb at *
  convert h using 4
  ext ω; simp [hS ω]

/-- A deterministic run that halts in round `0` succeeds at no cost. -/
lemma implI_round0 {P : Proto V} {I : Inst V} {x : Agent V → Mem} {Q : (Agent V → Mem) → Prop}
    {p : Prof V} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ ω, (∀ v, (P.out (st P I x ω 0 v)).isSome) ∧
      ∃ y, (∀ g, (I.host g).isSome → outAt P I x ω 0 g = some (y g)) ∧ Q y) :
    ImplI P I x Q p δ := by
  classical
  have hs : ∀ ω, Succ P I x Q p ω := fun ω => by
    obtain ⟨h1, y, hy, hQ⟩ := h ω
    exact ⟨0, ⟨fun v _ => h1 v, fun s hs => absurd hs (Nat.not_lt_zero s)⟩,
      properUpTo_zero P I x ω, Nat.zero_le _,
      by simp [msgsUpTo], fun e => by simp [loadUpTo], y, hy, hQ⟩
  unfold ImplI failProb
  rw [filter_false_of_mem (fun ω _ => not_not.2 (hs ω))]
  simpa using hδ

theorem locI (F : LocFn) {I : Inst V} {x : Agent V → Mem} {Q : (Agent V → Mem) → Prop}
    {p : Prof V} {δ : ℝ} (hδ : 0 ≤ δ) (y : Agent V → Mem)
    (hy : ∀ g v, I.host g = some v → locOut F (I.ctx v) (inpAt I x v) g = some (y g))
    (hQ : Q y) : ImplI (locP F) I x Q p δ := by
  refine implI_round0 hδ (fun ω => ⟨fun v => rfl, y, fun g hg => ?_, hQ⟩)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hg
  simp only [outAt, hv]
  exact hy g v hv

theorem skipI {I : Inst V} {x : Agent V → Mem} {Q : (Agent V → Mem) → Prop}
    {p : Prof V} {δ : ℝ} (hδ : 0 ≤ δ) (hQ : Q x) : ImplI skipP I x Q p δ := by
  refine implI_round0 hδ (fun ω => ⟨fun v => rfl, x, fun g hg => ?_, hQ⟩)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hg
  simp only [outAt, hv]
  show (some (inpAt I x v)).bind (fun m => m g) = some (x g)
  simp [inpAt, hv]

end APSP.Stoc.Congest
