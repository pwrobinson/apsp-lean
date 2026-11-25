import ApspStoc.Congest.TreeCast

/-!
# Packet protocols with private seeds

A generic layer used by the random-walk construction (`RWLink*.lean`).

* **Macro-rounds and packets.** Time is divided into *macro-rounds* of `L = encLen Bw b` rounds. In
  a macro-round a node may send one *packet* (a value `m : Msg V` with at most `b` words and numbers
  `< (n+4)^(Bw+1)`, `EncOK`) to each neighbour: the `L` words of its encoding `enc` (from
  `TreeCastAux.lean`), one per round. The receiver detects a packet by its first word and decodes it
  with `dec`.
* **Seeded full-information protocols** (`pktP`): a node keeps its context, its input, its private
  seed and the history of all words received. Its packet for a neighbour in macro-round `s` is a
  function `F` of these (through the decoded packet history of the first `s` macro-rounds); it
  halts after `T` macro-rounds (`T` a function of the public context) with outputs `O`.
* `succ_pktP`: for fixed seeds `ω`, if the protocol, fed with the packet histories of an explicit
  packet schedule `MP` (which may depend on all seeds), sends exactly the packets of `MP` at every
  participant, and `MP` sends only along edges of the instance and only encodable packets, then the
  run succeeds with `T·L` rounds, `L` messages per packet and the outputs of `O` on the schedule's
  histories.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A packet history: the packets received in each macro-round so far. -/
abbrev PHist (V : Type) := List (V → Option (Msg V))

/-- The packets of macro-round `s` in a packet history (`none` beyond its end). -/
def pget (h : PHist V) (s : ℕ) : V → Option (Msg V) := h.getD s (fun _ => none)

/-- Decoding the packet received from `u` in macro-round `s` of a word history (macro-rounds of
`encLen Bw b` rounds): present iff the first word of the macro-round was received. -/
def decPk (n Bw b : ℕ) (h : Hist V) (s : ℕ) (u : V) : Option (Msg V) :=
  if (hget h (s * encLen Bw b) u).isSome then
    some (dec n Bw b ((List.range (encLen Bw b)).filterMap
      (fun r => hget h (s * encLen Bw b + r) u)))
  else none

/-- The decoded packet history of the first `k` macro-rounds of a word history. -/
def decH (n Bw b : ℕ) (h : Hist V) (k : ℕ) : PHist V := (List.range k).map (decPk n Bw b h)

/-- **Seeded packet protocol.** State: context, input, private seed, word history. In round
`s·L + r` (`L = encLen Bw b`) a node sends word `r` of the encoding of its packet `F … v` for
macro-round `s`, computed from the decoded packet history of the first `s` macro-rounds; it halts
after `T = Tf c` macro-rounds with outputs `O` (on the decoded packet history). -/
@[reducible] def pktP (Ω : Type) [Fintype Ω] [Nonempty Ω] (b : ℕ) (Bwf Tf : NCtx V → ℕ)
    (F : NCtx V → (Agent V → Option Mem) → Ω → PHist V → V → Option (Msg V))
    (O : NCtx V → (Agent V → Option Mem) → Ω → PHist V → Agent V → Option Mem) : Proto V where
  S := NCtx V × (Agent V → Option Mem) × Ω × Hist V
  Ω := Ω
  init c inp ω := (c, inp, ω, [])
  send c s v := (F c s.2.1 s.2.2.1 (decH (Fintype.card V) (Bwf c) b s.2.2.2
      (s.2.2.2.length / encLen (Bwf c) b)) v).map
    (fun m => encAt (Fintype.card V) (Bwf c) m (s.2.2.2.length % encLen (Bwf c) b))
  recv _ s m := (s.1, s.2.1, s.2.2.1, s.2.2.2 ++ [m])
  out s := if Tf s.1 * encLen (Bwf s.1) b ≤ s.2.2.2.length then
    some (O s.1 s.2.1 s.2.2.1 (decH (Fintype.card V) (Bwf s.1) b s.2.2.2 (Tf s.1))) else none

/-- The packet history of `v` after `s` macro-rounds of a packet schedule `MP` (`MP u v i`: the
packet from `u` to `v` in macro-round `i`). -/
def pschedHist (MP : V → V → ℕ → Option (Msg V)) (v : V) (s : ℕ) : PHist V :=
  (List.range s).map (fun i w => MP w v i)

lemma pget_pschedHist (MP : V → V → ℕ → Option (Msg V)) (v : V) {s i : ℕ} (hi : i < s) (w : V) :
    pget (pschedHist MP v s) i w = MP w v i := by
  simp [pget, pschedHist, List.getD_eq_getElem?_getD, List.getElem?_range hi]

lemma pget_pschedHist_ge (MP : V → V → ℕ → Option (Msg V)) (v : V) {s i : ℕ} (hi : s ≤ i)
    (w : V) : pget (pschedHist MP v s) i w = none := by
  unfold pget
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [pschedHist] using hi)]
  rfl

lemma length_pschedHist (MP : V → V → ℕ → Option (Msg V)) (v : V) (s : ℕ) :
    (pschedHist MP v s).length = s := by simp [pschedHist]

/-- The word schedule of a packet schedule: word `r` of the packet of macro-round `s` in round
`s·L + r`. -/
def wSched (n Bw b : ℕ) (MP : V → V → ℕ → Option (Msg V)) (u v : V) (s' : ℕ) : Option (Word V) :=
  (MP u v (s' / encLen Bw b)).map (fun m => encAt n Bw m (s' % encLen Bw b))

lemma wSched_isSome (n Bw b : ℕ) (MP : V → V → ℕ → Option (Msg V)) (u v : V) (s' : ℕ) :
    (wSched n Bw b MP u v s').isSome = (MP u v (s' / encLen Bw b)).isSome := by
  simp [wSched]

lemma wSched_slot (n Bw b : ℕ) (MP : V → V → ℕ → Option (Msg V)) (u v : V) (s r : ℕ)
    (hr : r < encLen Bw b) :
    wSched n Bw b MP u v (s * encLen Bw b + r) = (MP u v s).map (fun m => encAt n Bw m r) := by
  have hL : 0 < encLen Bw b := encLen_pos Bw b
  have h1 : (s * encLen Bw b + r) / encLen Bw b = s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hr, zero_add]
  have h2 : (s * encLen Bw b + r) % encLen Bw b = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  simp only [wSched, h1, h2]

/-- Decoding the word history of a packet schedule gives the packet history. -/
lemma decPk_sched (n Bw b : ℕ) (MP : V → V → ℕ → Option (Msg V))
    (hok : ∀ u v s m, MP u v s = some m → EncOK n Bw b m) (v : V) {s s' : ℕ}
    (hs : (s + 1) * encLen Bw b ≤ s') (u : V) :
    decPk n Bw b (schedHist (wSched n Bw b MP) v s') s u = MP u v s := by
  have hL : 0 < encLen Bw b := encLen_pos Bw b
  have hw : ∀ r < encLen Bw b, hget (schedHist (wSched n Bw b MP) v s') (s * encLen Bw b + r) u =
      (MP u v s).map (fun m => encAt n Bw m r) := by
    intro r hr
    rw [hget_schedHist _ v (by nlinarith), wSched_slot n Bw b MP u v s r hr]
  unfold decPk
  rw [show s * encLen Bw b = s * encLen Bw b + 0 by rfl, hw 0 hL]
  cases hm : MP u v s with
  | none => simp
  | some m =>
    simp only [Option.map_some, Option.isSome_some, ite_true]
    congr 1
    have : (List.range (encLen Bw b)).filterMap
        (fun r => hget (schedHist (wSched n Bw b MP) v s') (s * encLen Bw b + 0 + r) u) =
        enc n Bw b m := by
      unfold enc
      rw [← List.filterMap_eq_map]
      apply List.filterMap_congr
      intro r hr
      rw [Nat.add_zero, hw r (List.mem_range.1 hr), hm]
      rfl
    rw [this]
    exact dec_enc n Bw b m (hok u v s m hm).1 (hok u v s m hm).2

lemma decH_sched (n Bw b : ℕ) (MP : V → V → ℕ → Option (Msg V))
    (hok : ∀ u v s m, MP u v s = some m → EncOK n Bw b m) (v : V) {k s' : ℕ}
    (hs : k * encLen Bw b ≤ s') :
    decH n Bw b (schedHist (wSched n Bw b MP) v s') k = pschedHist MP v k := by
  unfold decH pschedHist
  apply List.map_congr_left
  intro s hs'
  funext u
  have := List.mem_range.1 hs'
  exact decPk_sched n Bw b MP hok v (le_trans (Nat.mul_le_mul_right _ (by omega)) hs) u

section Run

variable {Ω : Type} [Fintype Ω] [Nonempty Ω] {b : ℕ} {Bwf Tf : NCtx V → ℕ}
  {F : NCtx V → (Agent V → Option Mem) → Ω → PHist V → V → Option (Msg V)}
  {O : NCtx V → (Agent V → Option Mem) → Ω → PHist V → Agent V → Option Mem}
  {I : Inst V} {x : Agent V → Mem} {ω : V → Ω} {T Bw : ℕ}

/-- Before halting, the state of a node is its context, input, seed and word history. -/
lemma st_pktP (hT : ∀ v, Tf (I.ctx v) = T) (hB : ∀ v, Bwf (I.ctx v) = Bw) :
    ∀ t ≤ T * encLen Bw b, ∀ v, st (pktP Ω b Bwf Tf F O) I x ω t v =
      (I.ctx v, inpAt I x v, ω v, histOf (pktP Ω b Bwf Tf F O) I x ω v t) := by
  intro t
  induction t with
  | zero => intro _ v; rfl
  | succ t ih =>
    intro ht v
    rw [st_succ]
    unfold step
    rw [ih (by omega) v]
    have hout : (pktP Ω b Bwf Tf F O).out
        (I.ctx v, inpAt I x v, ω v, histOf (pktP Ω b Bwf Tf F O) I x ω v t) = none := by
      simp only [pktP, histOf, List.length_map, List.length_range, hT, hB]
      rw [ite_eq_right (by intro h; omega)]
    rw [hout]
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false, pktP, histOf, List.range_succ,
      List.map_append, List.map_cons, List.map_nil]

/-- The hypothesis of `succ_pktP`: every participant, fed with the packet history of `MP`, sends
the packets of `MP`; `MP` sends only along edges and only encodable packets. -/
def PktSchedOK (Ω : Type) [Fintype Ω] [Nonempty Ω] (b : ℕ)
    (F : NCtx V → (Agent V → Option Mem) → Ω → PHist V → V → Option (Msg V))
    (I : Inst V) (x : Agent V → Mem) (ω : V → Ω) (T Bw : ℕ) (MP : V → V → ℕ → Option (Msg V)) :
    Prop :=
  (∀ s < T, ∀ u v, I.part u → F (I.ctx u) (inpAt I x u) (ω u) (pschedHist MP u s) v = MP u v s) ∧
  (∀ s u v, ¬ I.G.Adj u v → MP u v s = none) ∧
  (∀ u v s m, MP u v s = some m → EncOK (Fintype.card V) Bw b m)

/-- **Runs of packet protocols** follow the word schedule of a packet schedule. -/
theorem msg_pktP (hT : ∀ v, Tf (I.ctx v) = T) (hB : ∀ v, Bwf (I.ctx v) = Bw)
    (MP : V → V → ℕ → Option (Msg V)) (hM : PktSchedOK Ω b F I x ω T Bw MP) :
    ∀ s < T * encLen Bw b, ∀ u v, msg (pktP Ω b Bwf Tf F O) I (st (pktP Ω b Bwf Tf F O) I x ω s) u v =
      wSched (Fintype.card V) Bw b MP u v s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs u v
    have hh : histOf (pktP Ω b Bwf Tf F O) I x ω u s =
        schedHist (wSched (Fintype.card V) Bw b MP) u s := by
      unfold histOf schedHist
      apply List.map_congr_left
      intro i hi
      funext w
      exact ih i (List.mem_range.1 hi) (by have := List.mem_range.1 hi; omega) w u
    have hst := st_pktP (F := F) (O := O) (x := x) (ω := ω) hT hB s hs.le u
    have hL : 0 < encLen Bw b := encLen_pos Bw b
    unfold msg
    by_cases hadj : I.G.Adj u v
    · have hout : (pktP Ω b Bwf Tf F O).out (st (pktP Ω b Bwf Tf F O) I x ω s u) = none := by
        rw [hst]
        simp only [pktP, histOf, List.length_map, List.length_range, hT, hB]
        rw [ite_eq_right (by intro h; omega)]
      rw [ite_eq_left ⟨hadj, hout⟩, hst]
      simp only [pktP]
      rw [hh, length_schedHist, hB u]
      have hsT : s / encLen Bw b < T := (Nat.div_lt_iff_lt_mul hL).2 hs
      rw [decH_sched _ Bw b MP hM.2.2 u (Nat.div_mul_le_self s _),
        hM.1 _ hsT u v (I.adj_part u v hadj)]
      cases hm : MP u v (s / encLen Bw b) with
      | none => simp [wSched, hm]
      | some m =>
        simp [wSched, hm, encAt_ok]
    · rw [ite_eq_right (fun h => hadj h.1)]
      simp [wSched, hM.2.1 _ u v hadj]

lemma histOf_pktP (hT : ∀ v, Tf (I.ctx v) = T) (hB : ∀ v, Bwf (I.ctx v) = Bw)
    (MP : V → V → ℕ → Option (Msg V)) (hM : PktSchedOK Ω b F I x ω T Bw MP)
    {s : ℕ} (hs : s ≤ T * encLen Bw b) (v : V) :
    histOf (pktP Ω b Bwf Tf F O) I x ω v s = schedHist (wSched (Fintype.card V) Bw b MP) v s := by
  unfold histOf schedHist
  apply List.map_congr_left
  intro i hi
  funext w
  exact msg_pktP hT hB MP hM i (lt_of_lt_of_le (List.mem_range.1 hi) hs) w v

lemma sentSet_pktP (hT : ∀ v, Tf (I.ctx v) = T) (hB : ∀ v, Bwf (I.ctx v) = Bw)
    (MP : V → V → ℕ → Option (Msg V)) (hM : PktSchedOK Ω b F I x ω T Bw MP)
    {s : ℕ} (hs : s < T * encLen Bw b) :
    sentSet (pktP Ω b Bwf Tf F O) I (st (pktP Ω b Bwf Tf F O) I x ω s) =
      univ.filter (fun uv : V × V => (MP uv.1 uv.2 (s / encLen Bw b)).isSome) := by
  unfold sentSet
  ext uv
  simp only [mem_filter, mem_univ, true_and]
  rw [msg_pktP hT hB MP hM s hs, wSched_isSome]

/-- Summing a function of the macro-round over the rounds. -/
lemma sum_range_mul_div (T L : ℕ) (hL : 0 < L) (f : ℕ → ℕ) :
    ∑ s ∈ range (T * L), f (s / L) = L * ∑ s ∈ range T, f s := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => f T)]
    · simp
    · intro r hr
      rw [mem_range] at hr
      congr 1
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hr, zero_add]

/-- **Success of seeded packet protocols** following a packet schedule `MP`. -/
theorem succ_pktP (hT : ∀ v, Tf (I.ctx v) = T) (hB : ∀ v, Bwf (I.ctx v) = Bw)
    (MP : V → V → ℕ → Option (Msg V)) (hM : PktSchedOK Ω b F I x ω T Bw MP)
    {Q : (Agent V → Mem) → Prop} {p : Prof V} (hr : T * encLen Bw b ≤ p.rounds)
    (hm : encLen Bw b * ∑ s ∈ range T,
      (univ.filter (fun uv : V × V => (MP uv.1 uv.2 s).isSome)).card ≤ p.msgs)
    (hl : ∀ e, encLen Bw b * ∑ s ∈ range T, ((univ.filter (fun uv : V × V =>
      (MP uv.1 uv.2 s).isSome)).filter (fun uv => s(uv.1, uv.2) = e)).card ≤ p.load e)
    (y : Agent V → Mem)
    (hy : ∀ g v, I.host g = some v → O (I.ctx v) (inpAt I x v) (ω v) (pschedHist MP v T) g =
      some (y g))
    (hQ : Q y) : Succ (pktP Ω b Bwf Tf F O) I x Q p ω := by
  classical
  have hL : 0 < encLen Bw b := encLen_pos Bw b
  have hfin : ∀ v, st (pktP Ω b Bwf Tf F O) I x ω (T * encLen Bw b) v =
      (I.ctx v, inpAt I x v, ω v, schedHist (wSched (Fintype.card V) Bw b MP) v
        (T * encLen Bw b)) := by
    intro v
    rw [st_pktP hT hB _ le_rfl v, histOf_pktP hT hB MP hM le_rfl v]
  refine ⟨T * encLen Bw b, ⟨fun v _ => ?_, fun s hs v _ => ?_⟩,
    fun s hs u hu _ v hv => ?_, hr, ?_, fun e => ?_, y, fun g hg => ?_, hQ⟩
  · rw [hfin v]
    simp [length_schedHist, hT, hB]
  · rw [st_pktP hT hB s hs.le v]
    simp only [pktP, histOf, List.length_map, List.length_range, hT, hB]
    rw [ite_eq_right (by intro h; omega)]
  · -- proper sends
    rw [st_pktP hT hB s hs.le u, histOf_pktP hT hB MP hM hs.le u] at hv
    simp only [length_schedHist, hB u] at hv
    have hsT : s / encLen Bw b < T := (Nat.div_lt_iff_lt_mul hL).2 hs
    rw [decH_sched _ Bw b MP hM.2.2 u (Nat.div_mul_le_self s _), hM.1 _ hsT u v hu] at hv
    by_contra hadj
    rw [hM.2.1 _ u v hadj] at hv
    exact absurd hv (by simp)
  · unfold msgsUpTo
    refine le_trans (le_of_eq ?_) hm
    rw [← sum_range_mul_div T _ hL (fun s =>
      (univ.filter (fun uv : V × V => (MP uv.1 uv.2 s).isSome)).card)]
    exact sum_congr rfl (fun s hs => by rw [sentSet_pktP hT hB MP hM (mem_range.1 hs)])
  · unfold loadUpTo
    refine le_trans (le_of_eq ?_) (hl e)
    rw [← sum_range_mul_div T _ hL (fun s => ((univ.filter (fun uv : V × V =>
      (MP uv.1 uv.2 s).isSome)).filter (fun uv => s(uv.1, uv.2) = e)).card)]
    refine sum_congr rfl (fun s hs => ?_)
    rw [sentSet_pktP hT hB MP hM (mem_range.1 hs)]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hg
    unfold outAt
    rw [hv]
    dsimp only
    rw [hfin v]
    simp only [length_schedHist, hT, hB, le_refl, ite_true, Option.bind_some]
    rw [decH_sched _ Bw b MP hM.2.2 v le_rfl]
    exact hy g v hv

end Run

end APSP.Stoc.Congest
