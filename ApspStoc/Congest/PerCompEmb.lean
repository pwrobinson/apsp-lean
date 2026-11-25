import ApspStoc.Congest.Core

/-!
# Protocols with embedded sub-runs (for `perCompR`)

`embP C B` runs a *controller* `C` (a full-information protocol: what a node sends, when it starts
a sub-run and when it halts are functions of its context, its input and the history of the
messages it received) and, when the controller says so, a *sub-run* of the protocol `B` with a
context and inputs computed by the controller. While the sub-run lasts, the node behaves exactly
as `B` (it sends and receives `B`'s messages); when `B` halts, the node records `B`'s output (if the
controller marked the run as *own*) and returns to the controller. The history records a `none`
for every round spent in a sub-run.

`succ_embP` is the generic simulation lemma. Suppose that a global plan is given: a control
schedule `M` (the messages of the controllers), and sub-runs `k ∈ ks` of `B` on sub-instances
`J k` (participants contained in those of `I`, edges among the edges of `I`) with inputs `xs k`,
starting in round `bs k ≥ 1` and lasting `ts k` rounds, the intervals of distinct sub-runs being
disjoint, every sub-run halting at `ts k` and sending properly (as a successful standalone run of
`B` does, `ProperUpTo`). If every controller, fed with the history of the plan, sends the
messages of `M`, starts the sub-runs at the planned rounds with the contexts and inputs of the
sub-instances, and halts at `T`, then the run of `embP C B` follows the plan: during a sub-run the
states of its participants are those of the standalone run of `B` with the same seeds (by proper
sends, `B` sends nothing to the nodes outside the sub-instance, which are silent), and its costs are
those of `M` plus those of the sub-runs.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

/-- A physical history: for every round, the messages received from the controllers (`some`), or
`none` for a round spent in a sub-run. -/
abbrev PH (V : Type) := List (Option (V → Option (Word V)))

/-- A controller: what a node sends, when it starts a sub-run (with which context and inputs, and
whether the run is its *own*: then its output is kept), when it halts, and its final outputs (from
the kept output of its own sub-run). -/
structure Ctl (V : Type) : Type 1 where
  send : NCtx V → (Agent V → Option Mem) → PH V → V → Option (Word V)
  start : NCtx V → (Agent V → Option Mem) → PH V →
    Option (NCtx V × (Agent V → Option Mem) × Bool)
  halt : NCtx V → (Agent V → Option Mem) → PH V → Bool
  out : NCtx V → (Agent V → Option Mem) → Option (Agent V → Option Mem) → Agent V → Option Mem

/-- The state of a node of `embP C B`. -/
structure EmbS (V : Type) (B : Proto V) : Type 1 where
  ctx : NCtx V
  inp : Agent V → Option Mem
  seed : B.Ω
  hist : PH V
  sub : Option (NCtx V × B.S × Bool)
  res : Option (Agent V → Option Mem)

/-- Leave a sub-run whose state `b` has halted (keeping its output if it is the own run). -/
def exitOr {V : Type} (B : Proto V) (c' : NCtx V) (b : B.S) (own : Bool)
    (res : Option (Agent V → Option Mem)) :
    Option (NCtx V × B.S × Bool) × Option (Agent V → Option Mem) :=
  match B.out b with
  | some o => (none, if own then some o else res)
  | none => (some (c', b, own), res)

/-- The controller `C` with sub-runs of `B`. -/
def embP {V : Type} (C : Ctl V) (B : Proto V) : Proto V where
  S := EmbS V B
  Ω := B.Ω
  init c inp ω := ⟨c, inp, ω, [], none, none⟩
  send c s v := match s.sub with
    | some (c', b, _) => B.send c' b v
    | none => C.send c s.inp s.hist v
  recv c s m := match s.sub with
    | some (c', b, own) =>
      ⟨s.ctx, s.inp, s.seed, s.hist ++ [none], (exitOr B c' (B.recv c' b m) own s.res).1,
        (exitOr B c' (B.recv c' b m) own s.res).2⟩
    | none =>
      match C.start c s.inp (s.hist ++ [some m]) with
      | some (c', i', own) =>
        ⟨s.ctx, s.inp, s.seed, s.hist ++ [some m], (exitOr B c' (B.init c' i' s.seed) own s.res).1,
          (exitOr B c' (B.init c' i' s.seed) own s.res).2⟩
      | none => ⟨s.ctx, s.inp, s.seed, s.hist ++ [some m], none, s.res⟩
  out s := if s.sub.isNone && C.halt s.ctx s.inp s.hist then some (C.out s.ctx s.inp s.res)
    else none

variable {V : Type} [Fintype V] [DecidableEq V]

section Plan

variable {ι : Type} (ks : Finset ι) (J : ι → Inst V) (bs ts : ι → ℕ)

/-- `v` is in a sub-run in round `s`. -/
def InB (v : V) (s : ℕ) : Prop := ∃ k ∈ ks, (J k).part v ∧ bs k ≤ s ∧ s < bs k + ts k

open Classical in
/-- The history of `v` after `s` rounds of the plan. -/
noncomputable def hx (M : V → V → ℕ → Option (Word V)) (v : V) (s : ℕ) : PH V :=
  (List.range s).map (fun i => if InB ks J bs ts v i then none else some (fun u => M u v i))

open Classical in
lemma hx_succ (M : V → V → ℕ → Option (Word V)) (v : V) (s : ℕ) :
    hx ks J bs ts M v (s + 1) = hx ks J bs ts M v s ++
      [if InB ks J bs ts v s then none else some (fun u => M u v s)] := by
  classical
  simp [hx, List.range_succ]

end Plan

section Sim

variable {ι : Type} (C : Ctl V) (B : Proto V) (I : Inst V) (x : Agent V → Mem) (ω : V → B.Ω)
  (ks : Finset ι) (J : ι → Inst V) (xs : ι → Agent V → Mem) (bs ts : ι → ℕ) (own : ι → V → Bool)
  (M : V → V → ℕ → Option (Word V)) (T : ℕ)

/-- The hypotheses of the simulation lemma: the plan is consistent, and the controllers follow
it. -/
structure EmbOK : Prop where
  part : ∀ k ∈ ks, ∀ v, (J k).part v → I.part v
  adj : ∀ k ∈ ks, ∀ u v, (J k).G.Adj u v → I.G.Adj u v
  sep : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → bs k + ts k < bs k' ∨ bs k' + ts k' < bs k
  ownU : ∀ v, ∀ k ∈ ks, ∀ k' ∈ ks, (J k).part v → own k v = true → (J k').part v →
    own k' v = true → k = k'
  b1 : ∀ k ∈ ks, 1 ≤ bs k
  bT : ∀ k ∈ ks, bs k + ts k ≤ T
  halts : ∀ k ∈ ks, HaltsAt B (J k) (xs k) ω (ts k)
  proper : ∀ k ∈ ks, ProperUpTo B (J k) (xs k) ω (ts k)
  Madj : ∀ s u v, (M u v s).isSome → I.G.Adj u v
  Mok : ∀ s u v w, M u v s = some w → WordOK (Fintype.card V) w
  MB : ∀ s u v, (M u v s).isSome → ¬ InB ks J bs ts u s ∧ ¬ InB ks J bs ts v s
  send : ∀ v, I.part v → ∀ s < T, ¬ InB ks J bs ts v s →
    C.send (I.ctx v) (inpAt I x v) (hx ks J bs ts M v s) = fun u => M v u s
  start : ∀ v, I.part v → ∀ s, 1 ≤ s → s ≤ T → ¬ InB ks J bs ts v (s - 1) →
    (∀ k ∈ ks, (J k).part v → bs k = s →
      C.start (I.ctx v) (inpAt I x v) (hx ks J bs ts M v s) =
        some ((J k).ctx v, inpAt (J k) (xs k) v, own k v)) ∧
    ((∀ k ∈ ks, (J k).part v → bs k ≠ s) →
      C.start (I.ctx v) (inpAt I x v) (hx ks J bs ts M v s) = none)
  halt : ∀ v, I.part v → ∀ s ≤ T, ¬ InB ks J bs ts v s →
    (C.halt (I.ctx v) (inpAt I x v) (hx ks J bs ts M v s) = true ↔ s = T)

open Classical in
/-- the expected sub-run state -/
noncomputable def subX (v : V) (s : ℕ) : Option (NCtx V × B.S × Bool) :=
  if h : ∃ k ∈ ks, (J k).part v ∧ bs k ≤ s ∧ s < bs k + ts k then
    some ((J h.choose).ctx v, st B (J h.choose) (xs h.choose) ω (s - bs h.choose) v,
      own h.choose v)
  else none

open Classical in
/-- the expected kept output -/
noncomputable def resX (v : V) (s : ℕ) : Option (Agent V → Option Mem) :=
  if h : ∃ k ∈ ks, (J k).part v ∧ own k v = true ∧ bs k + ts k ≤ s then
    B.out (st B (J h.choose) (xs h.choose) ω (ts h.choose) v)
  else none

/-- the expected state -/
noncomputable def expS (v : V) (s : ℕ) : (embP C B).S :=
  ⟨I.ctx v, inpAt I x v, ω v, hx ks J bs ts M v s, subX B ω ks J xs bs ts own v s,
    resX B ω ks J xs bs ts own v s⟩

variable {C B I x ω ks J xs bs ts own M T}

/-- Distinct sub-runs have disjoint intervals. -/
lemma EmbOK.disj (h : EmbOK C B I x ω ks J xs bs ts own M T) :
    ∀ k ∈ ks, ∀ k' ∈ ks, ∀ s, bs k ≤ s → s < bs k + ts k → bs k' ≤ s → s < bs k' + ts k' →
      k = k' := by
  intro k hk k' hk' s h1 h2 h3 h4
  by_contra hne
  rcases h.sep k hk k' hk' hne with h5 | h5 <;> omega


lemma subX_of (h : EmbOK C B I x ω ks J xs bs ts own M T) {k : ι} (hk : k ∈ ks) {v : V}
    (hv : (J k).part v) {s : ℕ} (h1 : bs k ≤ s) (h2 : s < bs k + ts k) :
    subX B ω ks J xs bs ts own v s =
      some ((J k).ctx v, st B (J k) (xs k) ω (s - bs k) v, own k v) := by
  have hex : ∃ k ∈ ks, (J k).part v ∧ bs k ≤ s ∧ s < bs k + ts k := ⟨k, hk, hv, h1, h2⟩
  unfold subX
  rw [dif_pos hex]
  have hs := hex.choose_spec
  have he : hex.choose = k := h.disj _ hs.1 k hk s hs.2.2.1 hs.2.2.2 h1 h2
  rw [he]

lemma subX_none {v : V} {s : ℕ} (h : ¬ InB ks J bs ts v s) :
    subX B ω ks J xs bs ts own v s = none := by
  unfold subX
  rw [dif_neg (show ¬ ∃ k ∈ ks, (J k).part v ∧ bs k ≤ s ∧ s < bs k + ts k from h)]

lemma resX_of (h : EmbOK C B I x ω ks J xs bs ts own M T) {k : ι} (hk : k ∈ ks) {v : V}
    (hv : (J k).part v) (ho : own k v = true) {s : ℕ} (h1 : bs k + ts k ≤ s) :
    resX B ω ks J xs bs ts own v s = B.out (st B (J k) (xs k) ω (ts k) v) := by
  have hex : ∃ k ∈ ks, (J k).part v ∧ own k v = true ∧ bs k + ts k ≤ s := ⟨k, hk, hv, ho, h1⟩
  unfold resX
  rw [dif_pos hex]
  have hs := hex.choose_spec
  have he : hex.choose = k := h.ownU v _ hs.1 k hk hs.2.1 hs.2.2.1 hv ho
  rw [he]

lemma resX_none {v : V} {s : ℕ}
    (h : ∀ k ∈ ks, (J k).part v → own k v = true → s < bs k + ts k) :
    resX B ω ks J xs bs ts own v s = none := by
  unfold resX
  rw [dif_neg]
  rintro ⟨k, hk, hv, ho, hle⟩
  have := h k hk hv ho
  omega

/-- The message of a node in a sub-run to a node outside it is `none` (proper sends). -/
lemma send_out (h : EmbOK C B I x ω ks J xs bs ts own M T) {k : ι} (hk : k ∈ ks) {u v : V}
    (hu : (J k).part u) {s : ℕ} (h1 : bs k ≤ s) (h2 : s < bs k + ts k)
    (hv : ¬ (J k).G.Adj u v) :
    B.send ((J k).ctx u) (st B (J k) (xs k) ω (s - bs k) u) v = none := by
  cases hs : B.send ((J k).ctx u) (st B (J k) (xs k) ω (s - bs k) u) v with
  | none => rfl
  | some w =>
    exact absurd (h.proper k hk (s - bs k) (by omega) u hu ((h.halts k hk).2 _ (by omega) u hu) v
      (by rw [hs]; rfl)) hv

/-- The out of the expected state before the end. -/
lemma out_expS (h : EmbOK C B I x ω ks J xs bs ts own M T) {v : V} (hv : I.part v) {s : ℕ}
    (hs : s < T) :
    (embP C B).out (expS C B I x ω ks J xs bs ts own M v s) = none := by
  show (if (subX B ω ks J xs bs ts own v s).isNone &&
      C.halt (I.ctx v) (inpAt I x v) (hx ks J bs ts M v s) then _ else none) = none
  by_cases hB : InB ks J bs ts v s
  · obtain ⟨k, hk, hvk, h1, h2⟩ := hB
    rw [subX_of h hk hvk h1 h2]
    rfl
  · rw [subX_none hB]
    have := (h.halt v hv s hs.le hB).1
    cases hc : C.halt (I.ctx v) (inpAt I x v) (hx ks J bs ts M v s)
    · rfl
    · exact absurd (this hc) (by omega)

open Classical in
/-- **The messages of the plan**, from a node in sub-run `k`. -/
lemma msg_inB (h : EmbOK C B I x ω ks J xs bs ts own M T) {s : ℕ} (hs : s < T)
    (hst : ∀ v, I.part v → st (embP C B) I x ω s v = expS C B I x ω ks J xs bs ts own M v s)
    {k : ι} (hk : k ∈ ks) {u : V} (hu : (J k).part u) (h1 : bs k ≤ s) (h2 : s < bs k + ts k)
    (v : V) :
    msg (embP C B) I (st (embP C B) I x ω s) u v =
      if I.G.Adj u v then
        (match B.send ((J k).ctx u) (st B (J k) (xs k) ω (s - bs k) u) v with
          | some w => if WordOK (Fintype.card V) w then some w else none
          | none => none) else none := by
  classical
  have hu' := h.part k hk u hu
  by_cases hadj : I.G.Adj u v
  · unfold msg
    rw [hst u hu', if_pos ⟨hadj, out_expS h hu' hs⟩, if_pos hadj]
    show (match (match (subX B ω ks J xs bs ts own u s) with
      | some (c', b, _) => B.send c' b v
      | none => C.send (I.ctx u) (inpAt I x u) (hx ks J bs ts M u s) v) with
      | some w => if WordOK (Fintype.card V) w then some w else none
      | none => none) = _
    rw [subX_of h hk hu h1 h2]
    try rfl
  · unfold msg
    rw [if_neg (fun h' => hadj h'.1), if_neg hadj]

/-- **The messages of the plan**, from a node in control mode. -/
lemma msg_ctlS (h : EmbOK C B I x ω ks J xs bs ts own M T) {s : ℕ} (hs : s < T)
    (hst : ∀ v, I.part v → st (embP C B) I x ω s v = expS C B I x ω ks J xs bs ts own M v s)
    {u : V} (hB : ¬ InB ks J bs ts u s) (v : V) :
    msg (embP C B) I (st (embP C B) I x ω s) u v = M u v s := by
  classical
  by_cases hadj : I.G.Adj u v
  · have hu := I.adj_part u v hadj
    unfold msg
    rw [hst u hu, if_pos ⟨hadj, out_expS h hu hs⟩]
    show (match (match (subX B ω ks J xs bs ts own u s) with
      | some (c', b, _) => B.send c' b v
      | none => C.send (I.ctx u) (inpAt I x u) (hx ks J bs ts M u s) v) with
      | some w => if WordOK (Fintype.card V) w then some w else none
      | none => none) = _
    rw [subX_none hB]
    dsimp only
    rw [h.send u hu s hs hB]
    dsimp only
    cases hm : M u v s with
    | none => rfl
    | some w => simp [h.Mok s u v w hm]
  · unfold msg
    rw [if_neg (fun h' => hadj h'.1)]
    cases hm : M u v s with
    | none => rfl
    | some w => exact absurd (h.Madj s u v (by rw [hm]; rfl)) hadj

/-- In control mode, a node receives exactly the messages of `M`. -/
lemma msg_ctl (h : EmbOK C B I x ω ks J xs bs ts own M T) {s : ℕ} (hs : s < T)
    (hst : ∀ v, I.part v → st (embP C B) I x ω s v = expS C B I x ω ks J xs bs ts own M v s)
    {v : V} (hvB : ¬ InB ks J bs ts v s) (u : V) :
    msg (embP C B) I (st (embP C B) I x ω s) u v = M u v s := by
  by_cases hB : InB ks J bs ts u s
  · obtain ⟨k, hk, hu, h1, h2⟩ := hB
    rw [msg_inB h hs hst hk hu h1 h2]
    have hnadj : ¬ (J k).G.Adj u v := fun ha =>
      hvB ⟨k, hk, (J k).adj_part v u ha.symm, h1, h2⟩
    rw [send_out h hk hu h1 h2 hnadj]
    have hM : M u v s = none := by
      cases hm : M u v s with
      | none => rfl
      | some w => exact absurd (h.MB s u v (by rw [hm]; rfl)).1 (fun h' => h' ⟨k, hk, hu, h1, h2⟩)
    rw [hM]
    split_ifs <;> rfl
  · exact msg_ctlS h hs hst hB v

/-- In sub-run `k`, a node receives exactly the messages of the standalone run. -/
lemma msg_sub (h : EmbOK C B I x ω ks J xs bs ts own M T) {s : ℕ} (hs : s < T)
    (hst : ∀ v, I.part v → st (embP C B) I x ω s v = expS C B I x ω ks J xs bs ts own M v s)
    {k : ι} (hk : k ∈ ks) {v : V} (hv : (J k).part v) (h1 : bs k ≤ s) (h2 : s < bs k + ts k)
    (u : V) :
    msg (embP C B) I (st (embP C B) I x ω s) u v =
      msg B (J k) (st B (J k) (xs k) ω (s - bs k)) u v := by
  classical
  by_cases hu : (J k).part u
  · rw [msg_inB h hs hst hk hu h1 h2]
    have hout : B.out (st B (J k) (xs k) ω (s - bs k) u) = none :=
      (h.halts k hk).2 _ (by omega) u hu
    by_cases hJ : (J k).G.Adj u v
    · unfold msg
      rw [if_pos (h.adj k hk u v hJ), if_pos ⟨hJ, hout⟩]
      cases B.send ((J k).ctx u) (st B (J k) (xs k) ω (s - bs k) u) v with
      | none => rfl
      | some w => exact if_congr Iff.rfl rfl rfl
    · unfold msg
      rw [if_neg (show ¬ ((J k).G.Adj u v ∧ B.out (st B (J k) (xs k) ω (s - bs k) u) = none) from
        fun h' => hJ h'.1), send_out h hk hu h1 h2 hJ]
      split_ifs <;> rfl
  · have hB : ¬ InB ks J bs ts u s := by
      rintro ⟨k', hk', hu', h1', h2'⟩
      have := h.disj k' hk' k hk s h1' h2' h1 h2
      subst this
      exact hu hu'
    rw [msg_ctlS h hs hst hB v]
    unfold msg
    rw [if_neg (fun h' => hu ((J k).adj_part u v h'.1))]
    cases hm : M u v s with
    | none => rfl
    | some w => exact absurd (h.MB s u v (by rw [hm]; rfl)).2 (fun h' => h' ⟨k, hk, hv, h1, h2⟩)

/-- the standalone run of a sub-run makes a step while the node has not halted -/
lemma st_sub_succ (h : EmbOK C B I x ω ks J xs bs ts own M T) {k : ι} (hk : k ∈ ks) {v : V}
    (hv : (J k).part v) {r : ℕ} (hr : r < ts k) :
    st B (J k) (xs k) ω (r + 1) v = B.recv ((J k).ctx v) (st B (J k) (xs k) ω r v)
      (fun u => msg B (J k) (st B (J k) (xs k) ω r) u v) := by
  rw [st_succ]
  unfold step
  rw [if_neg (by rw [(h.halts k hk).2 r hr v hv]; simp)]

lemma resX_succ_eq (h : EmbOK C B I x ω ks J xs bs ts own M T) {v : V} {s : ℕ}
    (hno : ∀ k ∈ ks, (J k).part v → own k v = true → bs k + ts k ≠ s + 1) :
    resX B ω ks J xs bs ts own v (s + 1) = resX B ω ks J xs bs ts own v s := by
  unfold resX
  have hiff : (∃ k ∈ ks, (J k).part v ∧ own k v = true ∧ bs k + ts k ≤ s + 1) ↔
      (∃ k ∈ ks, (J k).part v ∧ own k v = true ∧ bs k + ts k ≤ s) := by
    constructor
    · rintro ⟨k, hk, hv, ho, hle⟩
      exact ⟨k, hk, hv, ho, by have := hno k hk hv ho; omega⟩
    · rintro ⟨k, hk, hv, ho, hle⟩
      exact ⟨k, hk, hv, ho, by omega⟩
  by_cases h1 : ∃ k ∈ ks, (J k).part v ∧ own k v = true ∧ bs k + ts k ≤ s
  · rw [dif_pos (hiff.2 h1), dif_pos h1]
    have e1 := (hiff.2 h1).choose_spec
    have e2 := h1.choose_spec
    have : (hiff.2 h1).choose = h1.choose :=
      h.ownU v _ e1.1 _ e2.1 e1.2.1 e1.2.2.1 e2.2.1 e2.2.2.1
    rw [this]
  · rw [dif_neg (fun h' => h1 (hiff.1 h')), dif_neg h1]

/-- **The run follows the plan.** -/
theorem st_embP (h : EmbOK C B I x ω ks J xs bs ts own M T) :
    ∀ s ≤ T, ∀ v, I.part v → st (embP C B) I x ω s v = expS C B I x ω ks J xs bs ts own M v s := by
  intro s
  induction s with
  | zero =>
    intro _ v hv
    have hsub : subX B ω ks J xs bs ts own v 0 = none := subX_none (by
      rintro ⟨k, hk, -, h1, h2⟩
      have := h.b1 k hk
      omega)
    have hres : resX B ω ks J xs bs ts own v 0 = none := resX_none (fun k hk _ _ => by
      have := h.b1 k hk
      omega)
    show (⟨I.ctx v, inpAt I x v, ω v, [], none, none⟩ : (embP C B).S) = _
    unfold expS
    rw [hsub, hres]
    rfl
  | succ s ih =>
    intro hs v hv
    have hst := fun w hw => ih (by omega) w hw
    show step (embP C B) I (st (embP C B) I x ω s) v = _
    unfold step
    rw [hst v hv, out_expS h hv (by omega)]
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases hB : InB ks J bs ts v s
    · -- in a sub-run
      obtain ⟨k, hk, hvk, h1, h2⟩ := hB
      have hmsg := msg_sub h (by omega) hst hk hvk h1 h2
      have hsub := subX_of h hk hvk h1 h2
      show (match subX B ω ks J xs bs ts own v s with
        | some (c', b, own) => _
        | none => _) = _
      rw [hsub]
      dsimp only
      have hrecv : B.recv ((J k).ctx v) (st B (J k) (xs k) ω (s - bs k) v)
          (fun u => msg (embP C B) I (st (embP C B) I x ω s) u v) =
          st B (J k) (xs k) ω (s + 1 - bs k) v := by
        rw [show s + 1 - bs k = (s - bs k) + 1 by omega, st_sub_succ h hk hvk (by omega)]
        simp only [hmsg]
      rw [hrecv]
      unfold expS
      rw [hx_succ, if_pos ⟨k, hk, hvk, h1, h2⟩]
      unfold exitOr
      -- other sub-runs of `v` end before `s` or start after `bs k + ts k`
      have hoth : ∀ k' ∈ ks, k' ≠ k → bs k' + ts k' < bs k ∨ bs k + ts k < bs k' :=
        fun k' hk' hne => h.sep k' hk' k hk hne
      by_cases hend : s + 1 = bs k + ts k
      · -- the sub-run halts
        obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 ((h.halts k hk).1 v hvk)
        have ho' : B.out (st B (J k) (xs k) ω (s + 1 - bs k) v) = some o := by
          rw [show s + 1 - bs k = ts k by omega]; exact ho
        rw [ho']
        dsimp only
        have hsub' : subX B ω ks J xs bs ts own v (s + 1) = none := subX_none (by
          rintro ⟨k', hk', hvk', h1', h2'⟩
          by_cases hkk : k' = k
          · subst hkk; omega
          · rcases hoth k' hk' hkk with h3 | h3 <;> omega)
        rw [hsub']
        congr 1
        cases hown : own k v
        · simp only [Bool.false_eq_true, ite_false]
          refine (resX_succ_eq h (fun k' hk' hvk' ho'' => ?_)).symm
          by_cases hkk : k' = k
          · subst hkk; rw [hown] at ho''; exact absurd ho'' (by simp)
          · rcases hoth k' hk' hkk with h3 | h3 <;> omega
        · simp only [ite_true]
          rw [resX_of h hk hvk hown (s := s + 1) (by omega), ho]
      · -- the sub-run continues
        have hn : B.out (st B (J k) (xs k) ω (s + 1 - bs k) v) = none :=
          (h.halts k hk).2 _ (by omega) v hvk
        rw [hn]
        dsimp only
        rw [subX_of h hk hvk (s := s + 1) (by omega) (by omega)]
        congr 1
        refine (resX_succ_eq h (fun k' hk' hvk' ho'' => ?_)).symm
        by_cases hkk : k' = k
        · subst hkk; omega
        · rcases hoth k' hk' hkk with h3 | h3 <;> omega
    · -- in control mode
      have hmsg : (fun u => msg (embP C B) I (st (embP C B) I x ω s) u v) = fun u => M u v s :=
        funext (msg_ctl h (by omega) hst hB)
      have hsub := subX_none (B := B) (ω := ω) (xs := xs) (own := own) hB
      show (match subX B ω ks J xs bs ts own v s with
        | some (c', b, own) => _
        | none => _) = _
      rw [hsub]
      dsimp only [expS]
      rw [hmsg]
      have hh : hx ks J bs ts M v s ++ [some (fun u => M u v s)] = hx ks J bs ts M v (s + 1) := by
        rw [hx_succ, if_neg hB]
      rw [hh]
      have hst1 := h.start v hv (s + 1) (by omega) hs (by simpa using hB)
      by_cases hb : ∃ k ∈ ks, (J k).part v ∧ bs k = s + 1
      · obtain ⟨k, hk, hvk, hbk⟩ := hb
        rw [hst1.1 k hk hvk hbk]
        dsimp only
        unfold exitOr
        have hst0 : st B (J k) (xs k) ω 0 v =
            B.init ((J k).ctx v) (inpAt (J k) (xs k) v) (ω v) := rfl
        have hoth : ∀ k' ∈ ks, k' ≠ k → bs k' + ts k' < bs k ∨ bs k + ts k < bs k' :=
          fun k' hk' hne => h.sep k' hk' k hk hne
        by_cases ht0 : ts k = 0
        · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 ((h.halts k hk).1 v hvk)
          rw [ht0, hst0] at ho
          rw [ho]
          dsimp only
          have hsub' : subX B ω ks J xs bs ts own v (s + 1) = none := subX_none (by
            rintro ⟨k', hk', hvk', h1', h2'⟩
            by_cases hkk : k' = k
            · subst hkk; omega
            · rcases hoth k' hk' hkk with h3 | h3 <;> omega)
          rw [hsub']
          congr 1
          cases hown : own k v
          · simp only [Bool.false_eq_true, ite_false]
            refine (resX_succ_eq h (fun k' hk' hvk' ho'' => ?_)).symm
            by_cases hkk : k' = k
            · subst hkk; rw [hown] at ho''; exact absurd ho'' (by simp)
            · rcases hoth k' hk' hkk with h3 | h3 <;> omega
          · simp only [ite_true]
            rw [resX_of h hk hvk hown (s := s + 1) (by omega), ht0, hst0, ho]
        · have hn : B.out (B.init ((J k).ctx v) (inpAt (J k) (xs k) v) (ω v)) = none := by
            rw [← hst0]; exact (h.halts k hk).2 0 (by omega) v hvk
          rw [hn]
          dsimp only
          rw [subX_of h hk hvk (s := s + 1) (by omega) (by omega), show s + 1 - bs k = 0 by omega]
          congr 1
          refine (resX_succ_eq h (fun k' hk' hvk' ho'' => ?_)).symm
          by_cases hkk : k' = k
          · subst hkk; omega
          · rcases hoth k' hk' hkk with h3 | h3 <;> omega
      · push_neg at hb
        rw [hst1.2 (fun k hk hvk => hb k hk hvk)]
        dsimp only
        have hsub' : subX B ω ks J xs bs ts own v (s + 1) = none := subX_none (by
          rintro ⟨k', hk', hvk', h1', h2'⟩
          by_cases hs' : bs k' ≤ s
          · exact hB ⟨k', hk', hvk', hs', by omega⟩
          · exact hb k' hk' hvk' (by omega))
        rw [hsub']
        congr 1
        refine (resX_succ_eq h (fun k' hk' hvk' ho'' => ?_)).symm
        intro hend
        by_cases hts : ts k' = 0
        · exact hb k' hk' hvk' (by omega)
        · exact hB ⟨k', hk', hvk', by omega, by omega⟩

lemma sum_window (f : ℕ → ℕ) {b t T : ℕ} (h : b + t ≤ T) :
    ∑ s ∈ range T, (if b ≤ s ∧ s < b + t then f (s - b) else 0) = ∑ r ∈ range t, f r := by
  obtain ⟨c, rfl⟩ : ∃ c, T = b + t + c := ⟨T - b - t, by omega⟩
  rw [sum_range_add, sum_range_add]
  have h1 : ∑ s ∈ range b, (if b ≤ s ∧ s < b + t then f (s - b) else 0) = 0 :=
    sum_eq_zero (fun s hs => by rw [mem_range] at hs; rw [if_neg (by omega)])
  have h2 : ∑ r ∈ range c, (if b ≤ b + t + r ∧ b + t + r < b + t then f (b + t + r - b) else 0) = 0 :=
    sum_eq_zero (fun r _ => by rw [if_neg (by omega)])
  rw [h1, h2, zero_add, add_zero]
  refine sum_congr rfl (fun r hr => ?_)
  rw [mem_range] at hr
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-- The messages sent in round `s` of the plan: those of `M`, and those of the running sub-run. -/
lemma sentSet_sub (h : EmbOK C B I x ω ks J xs bs ts own M T) {s : ℕ} (hs : s < T)
    (hst : ∀ v, I.part v → st (embP C B) I x ω s v = expS C B I x ω ks J xs bs ts own M v s)
    (Pr : V × V → Prop) [DecidablePred Pr] :
    ((sentSet (embP C B) I (st (embP C B) I x ω s)).filter Pr).card ≤
      ((univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome)).filter Pr).card +
      ∑ k ∈ ks, (if bs k ≤ s ∧ s < bs k + ts k then
        ((sentSet B (J k) (st B (J k) (xs k) ω (s - bs k))).filter Pr).card else 0) := by
  classical
  have hsub : (sentSet (embP C B) I (st (embP C B) I x ω s)).filter Pr ⊆
      (univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome)).filter Pr ∪
      ks.biUnion (fun k => if bs k ≤ s ∧ s < bs k + ts k then
        (sentSet B (J k) (st B (J k) (xs k) ω (s - bs k))).filter Pr else ∅) := by
    intro uv huv
    simp only [sentSet, mem_filter, mem_univ, true_and] at huv
    obtain ⟨hm, hPr⟩ := huv
    by_cases hB : InB ks J bs ts uv.1 s
    · -- a message of the sub-run
      obtain ⟨k, hk, hu, h1, h2⟩ := hB
      rw [msg_inB h hs hst hk hu h1 h2] at hm
      refine mem_union_right _ (mem_biUnion.2 ⟨k, hk, ?_⟩)
      rw [if_pos ⟨h1, h2⟩]
      simp only [sentSet, mem_filter, mem_univ, true_and]
      refine ⟨?_, hPr⟩
      split_ifs at hm with hadj
      · have hsend : (B.send ((J k).ctx uv.1) (st B (J k) (xs k) ω (s - bs k) uv.1) uv.2).isSome := by
          revert hm
          cases B.send ((J k).ctx uv.1) (st B (J k) (xs k) ω (s - bs k) uv.1) uv.2 <;> simp
        have hJ := h.proper k hk (s - bs k) (by omega) uv.1 hu
          ((h.halts k hk).2 _ (by omega) uv.1 hu) uv.2 hsend
        unfold msg
        rw [if_pos ⟨hJ, (h.halts k hk).2 _ (by omega) uv.1 hu⟩]
        exact hm
      · simp at hm
    · rw [msg_ctlS h hs hst hB] at hm
      exact mem_union_left _ (mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hm⟩, hPr⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  refine card_biUnion_le.trans (le_of_eq (sum_congr rfl (fun k _ => ?_)))
  split_ifs <;> rfl

/-- **Success of the plan**: the run of `embP C B` succeeds within the costs of `M` plus those of
the sub-runs, with the outputs of the controllers. -/
theorem succ_embP (h : EmbOK C B I x ω ks J xs bs ts own M T) {Q : (Agent V → Mem) → Prop}
    {p : Prof V} (hr : T ≤ p.rounds)
    (hm : ∑ s ∈ range T, ((univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome)).filter
        (fun _ => True)).card + ∑ k ∈ ks, msgsUpTo B (J k) (xs k) ω (ts k) ≤ p.msgs)
    (hl : ∀ e, ∑ s ∈ range T, ((univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome)).filter
        (fun uv => s(uv.1, uv.2) = e)).card + ∑ k ∈ ks, loadUpTo B (J k) (xs k) ω (ts k) e ≤
        p.load e)
    (y : Agent V → Mem)
    (hy : ∀ g v, I.host g = some v →
      C.out (I.ctx v) (inpAt I x v) (resX B ω ks J xs bs ts own v T) g = some (y g))
    (hQ : Q y) : Succ (embP C B) I x Q p ω := by
  classical
  have hst := st_embP h
  have hnB : ∀ v, ¬ InB ks J bs ts v T := by
    rintro v ⟨k, hk, -, -, h2⟩; have := h.bT k hk; omega
  have hout : ∀ v, I.part v → (embP C B).out (st (embP C B) I x ω T v) =
      some (C.out (I.ctx v) (inpAt I x v) (resX B ω ks J xs bs ts own v T)) := by
    intro v hv
    rw [hst T le_rfl v hv]
    show (if (subX B ω ks J xs bs ts own v T).isNone &&
      C.halt (I.ctx v) (inpAt I x v) (hx ks J bs ts M v T) then _ else none) = _
    rw [subX_none (hnB v), (h.halt v hv T le_rfl (hnB v)).2 rfl]
    rfl
  -- costs: the sum over rounds of the sub-runs
  have hcost : ∀ (Pr : V × V → Prop) [DecidablePred Pr],
      ∑ s ∈ range T, ((sentSet (embP C B) I (st (embP C B) I x ω s)).filter Pr).card ≤
        ∑ s ∈ range T, ((univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome)).filter Pr).card +
        ∑ k ∈ ks, ∑ r ∈ range (ts k), ((sentSet B (J k) (st B (J k) (xs k) ω r)).filter Pr).card := by
    intro Pr _
    refine (sum_le_sum (fun s hs => sentSet_sub h (mem_range.1 hs)
      (fun v hv => hst s (mem_range.1 hs).le v hv) Pr)).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_comm]
    congr 1
    refine sum_congr rfl (fun k hk => ?_)
    exact sum_window (fun r => ((sentSet B (J k) (st B (J k) (xs k) ω r)).filter Pr).card)
      (h.bT k hk)
  refine ⟨T, ⟨fun v hv => by rw [hout v hv]; rfl, fun s hs v hv => by
    rw [hst s hs.le v hv]; exact out_expS h hv hs⟩, ?_, hr, ?_, fun e => ?_, y, fun g hg => ?_, hQ⟩
  · -- proper sends
    intro s hs u hu _ v hv
    rw [hst s hs.le u hu] at hv
    by_cases hB : InB ks J bs ts u s
    · obtain ⟨k, hk, hku, h1, h2⟩ := hB
      have hsub := subX_of (B := B) h hk hku h1 h2
      have hv' : (B.send ((J k).ctx u) (st B (J k) (xs k) ω (s - bs k) u) v).isSome := by
        revert hv
        show (match (subX B ω ks J xs bs ts own u s) with
          | some (c', b, _) => B.send c' b v
          | none => C.send (I.ctx u) (inpAt I x u) (hx ks J bs ts M u s) v).isSome = true → _
        rw [hsub]; exact id
      exact h.adj k hk u v (h.proper k hk (s - bs k) (by omega) u hku
        ((h.halts k hk).2 _ (by omega) u hku) v hv')
    · have hv' : (C.send (I.ctx u) (inpAt I x u) (hx ks J bs ts M u s) v).isSome := by
        revert hv
        show (match (subX B ω ks J xs bs ts own u s) with
          | some (c', b, _) => B.send c' b v
          | none => C.send (I.ctx u) (inpAt I x u) (hx ks J bs ts M u s) v).isSome = true → _
        rw [subX_none hB]; exact id
      rw [h.send u hu s hs hB] at hv'
      exact h.Madj s u v hv'
  · -- messages
    have := hcost (fun _ => True)
    unfold msgsUpTo
    refine le_trans ?_ (le_trans this ?_)
    · exact le_of_eq (sum_congr rfl (fun s _ => by rw [filter_true_of_mem (fun _ _ => trivial)]))
    · refine le_trans (Nat.add_le_add_left (le_of_eq (sum_congr rfl (fun k _ => ?_))) _) hm
      unfold msgsUpTo
      exact sum_congr rfl (fun r _ => by rw [filter_true_of_mem (fun _ _ => trivial)])
  · -- loads
    have := hcost (fun uv => s(uv.1, uv.2) = e)
    unfold loadUpTo
    exact le_trans this (le_trans (le_of_eq rfl) (hl e))
  · -- outputs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hg
    unfold outAt
    rw [hv]
    dsimp only
    rw [hout v (I.host_part g v hv), Option.bind_some]
    exact hy g v hv

end Sim

end APSP.Stoc.Congest
