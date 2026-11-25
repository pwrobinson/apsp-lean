import ApspStoc.Congest.TreeCastAux

/-!
# Tree convergecast and broadcast in the CONGEST semantics

`treeCast_congest` is the concrete version of the toolkit field `treeCast` (`Toolkit.lean`), with
the algorithm `treeCastAlg Bw` and the constant `K = tcK Bw = 4 * Bw + 10`.

## The protocol (`tcProto`, a full-information protocol `histP`)
Let `L = encLen Bw b = (b + 1) * (Bw + 2)` (the length of an encoded value) and
`bStart = 1 + sz * L`.
* Round `0`: every node of `S` with a parent sends a word to its parent (parents learn their
  children).
* Rounds `1, …, sz * L`, in slots of `L` rounds: a node streams the encoding of its aggregate (own
  value, then the decoded values of the children, combined by `op` in the order of `toList`) to its
  parent in the first slot by whose start all children have sent their value. This is the slot
  `hgt u` (height of `u`), and `hgt u < |S| ≤ sz`.
* Rounds `bStart, …`: a root streams its aggregate to its children in rounds
  `bStart, …, bStart + L - 1`; every other node forwards to its children the word received from its
  parent in the previous round (pipelining), i.e. in rounds `bStart + dep u + i`, `i < L`.
* All nodes halt at round `tEnd = bStart + sz + L`, a function of the public `sz`; a node of `S`
  outputs its root's aggregate (decoded from the stream received from its parent), all other
  agents output `none`.

## The proof
`tcSched` is the explicit schedule (the message from `u` to `v` in round `s`), defined from the
height, depth and subtree aggregates of `TreeCastAux.lean`. `tcSend_sched`: fed with the history
of the schedule, the protocol sends exactly the messages of the schedule; by `succ_histP` the run
follows the schedule. The costs are read off the schedule: at most `1 + 2L` messages per directed
tree pair (`tcSched_count`), and messages only on tree edges (`tcSched_isSome`).
`tc_succ` states success on a general instance whose graph contains the tree edges.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The protocol -/

/-- the input type of the task: parent, root, value and aggregation operator (nodes of `S`) -/
abbrev TCIn (V : Type) : Type := Option (Option V × V × Msg V × (Msg V → Msg V → Msg V))

open Classical in
/-- the node's own input (`none` if absent or of another type) -/
noncomputable def myIn (inp : Agent V → Option Mem) (me : V) : TCIn V :=
  match inp (.inl me) with
  | some m => if h : m.1 = TCIn V then cast h m.2 else none
  | none => none

/-- the public size bound -/
def szOf (c : NCtx V) : ℕ := c.pub.getD 1 0

/-- the first round of the broadcast -/
def bStart (Bw b sz : ℕ) : ℕ := 1 + sz * encLen Bw b

/-- the halting round -/
def tEnd (Bw b sz : ℕ) : ℕ := bStart Bw b sz + sz + encLen Bw b

/-- the words received from `c` in rounds `1, …, N` -/
def upW (H : ℕ → V → Option (Word V)) (c : V) (N : ℕ) : List (Word V) :=
  (List.range N).filterMap (fun j => H (j + 1) c)

/-- the children: the neighbours that sent a word in round `0` -/
def kidsH (H : ℕ → V → Option (Word V)) : Finset V := univ.filter (fun w => (H 0 w).isSome)

/-- all children have sent their full value within the first `k` slots -/
def rdy (L : ℕ) (H : ℕ → V → Option (Word V)) (k : ℕ) : Prop :=
  ∀ c ∈ kidsH H, L ≤ (upW H c (k * L)).length

instance (L : ℕ) (H : ℕ → V → Option (Word V)) (k : ℕ) : Decidable (rdy L H k) := by
  unfold rdy; infer_instance

/-- own value aggregated with the decoded values of the children (received in rounds `1..N`) -/
noncomputable def myAgg (Bw b : ℕ) (H : ℕ → V → Option (Word V)) (va : Msg V)
    (op : Msg V → Msg V → Msg V) (N : ℕ) : Msg V :=
  (kidsH H).toList.foldl (fun a c => op a (dec (Fintype.card V) Bw b (upW H c N))) va

/-- The message sent to `v` in round `s`, given the own input `d` and the history `H`.
* round `0`: announce yourself to the parent;
* rounds `1, …, sz·L` (slots of `L = encLen Bw b` rounds): in the first slot by whose start the
  values of all children have arrived, stream the encoding of the aggregate to the parent;
* rounds `bStart = 1 + sz·L, …`: a root streams its aggregate to its children; every other node
  forwards to its children the word received from its parent in the previous round. -/
noncomputable def tcSend (Bw b sz : ℕ) (d : TCIn V) (s : ℕ) (H : ℕ → V → Option (Word V))
    (v : V) : Option (Word V) :=
  match d with
  | none => none
  | some (pa, _, va, op) =>
    if s = 0 then (if pa = some v then some (.num 0) else none)
    else if s < bStart Bw b sz then
      (if pa = some v ∧ rdy (encLen Bw b) H ((s - 1) / encLen Bw b) ∧
          ¬ (0 < (s - 1) / encLen Bw b ∧ rdy (encLen Bw b) H ((s - 1) / encLen Bw b - 1)) then
        some (encAt (Fintype.card V) Bw
          (myAgg Bw b H va op ((s - 1) / encLen Bw b * encLen Bw b)) ((s - 1) % encLen Bw b))
      else none)
    else if v ∈ kidsH H then
      (match pa with
       | none => if s - bStart Bw b sz < encLen Bw b then
           some (encAt (Fintype.card V) Bw (myAgg Bw b H va op (sz * encLen Bw b))
             (s - bStart Bw b sz))
         else none
       | some p => if bStart Bw b sz < s then H (s - 1) p else none)
    else none

/-- The result of a node: a root's aggregate, or the decoded value received from the parent. -/
noncomputable def tcRes (Bw b sz : ℕ) (d : TCIn V) (H : ℕ → V → Option (Word V)) :
    Option (Msg V) :=
  match d with
  | none => none
  | some (pa, _, va, op) => some (match pa with
      | none => myAgg Bw b H va op (sz * encLen Bw b)
      | some p => dec (Fintype.card V) Bw b
          ((List.range (sz + encLen Bw b)).filterMap (fun j => H (bStart Bw b sz + j) p)))

/-- **The tree convergecast/broadcast protocol** (a full-information protocol). -/
noncomputable def tcProto (Bw b : ℕ) (V : Type) [Fintype V] [DecidableEq V] : Proto V :=
  histP (fun c inp h v => tcSend Bw b (szOf c) (myIn inp c.me) h.length (hget h) v)
    (fun c => tEnd Bw b (szOf c))
    (fun c inp h g => some ⟨Option (Msg V),
      if g = .inl c.me then tcRes Bw b (szOf c) (myIn inp c.me) (hget h) else none⟩)

/-- the algorithm (it does not use `ν`) -/
noncomputable def treeCastAlg (Bw : ℕ) (_ν b : ℕ) : CAlg := fun V _ _ => tcProto Bw b V

/-! ## The schedule -/

/-- hypotheses on the forest -/
structure TreeOK (S : Finset V) (par : V → Option V) (rk : V → ℕ) (root : V → V) : Prop where
  mem : ∀ v ∈ S, ∀ u, par v = some u → u ∈ S
  rank : ∀ v ∈ S, ∀ u, par v = some u → rk u < rk v
  root_par : ∀ v ∈ S, ∀ u, par v = some u → root u = root v
  root_self : ∀ v ∈ S, par v = none → root v = v

/-- a value that can be encoded -/
def EncOK (n Bw b : ℕ) (m : Msg V) : Prop :=
  m.length ≤ b ∧ ∀ k, Word.num k ∈ m → k < (n + 4) ^ (Bw + 1)

section Sched

variable (Bw b sz : ℕ) (S : Finset V) (par : V → Option V) (rk : V → ℕ) (val : V → Msg V)
  (op : Msg V → Msg V → Msg V) (root : V → V)

/-- The schedule: the message from `u` to `v` in round `s`. A node of height `h` sends its
aggregate up in slot `h`; a node of depth `d` sends the final aggregate of its tree to its children
in rounds `bStart + d, …, bStart + d + L - 1`. -/
noncomputable def tcSched (u v : V) (s : ℕ) : Option (Word V) :=
  if s = 0 then (if u ∈ S ∧ par u = some v then some (.num 0) else none)
  else if s < bStart Bw b sz then
    (if u ∈ S ∧ par u = some v ∧ (s - 1) / encLen Bw b = hgt S par rk u then
      some (encAt (Fintype.card V) Bw (agg S par rk val op u) ((s - 1) % encLen Bw b)) else none)
  else (if v ∈ S ∧ par v = some u ∧ dep par rk u ≤ s - bStart Bw b sz ∧
      s - bStart Bw b sz < dep par rk u + encLen Bw b then
      some (encAt (Fintype.card V) Bw (agg S par rk val op (root u))
        (s - bStart Bw b sz - dep par rk u))
    else none)

lemma tcSched_zero (u v : V) : tcSched Bw b sz S par rk val op root u v 0 =
    if u ∈ S ∧ par u = some v then some (.num 0) else none := by
  rw [tcSched, ite_eq_left rfl]

lemma tcSched_up (u v : V) {s : ℕ} (h0 : s ≠ 0) (h1 : s < bStart Bw b sz) :
    tcSched Bw b sz S par rk val op root u v s =
      if u ∈ S ∧ par u = some v ∧ (s - 1) / encLen Bw b = hgt S par rk u then
        some (encAt (Fintype.card V) Bw (agg S par rk val op u) ((s - 1) % encLen Bw b))
      else none := by
  rw [tcSched, ite_eq_right h0, ite_eq_left h1]

lemma tcSched_down (u v : V) {s : ℕ} (h1 : bStart Bw b sz ≤ s) :
    tcSched Bw b sz S par rk val op root u v s =
      if v ∈ S ∧ par v = some u ∧ dep par rk u ≤ s - bStart Bw b sz ∧
        s - bStart Bw b sz < dep par rk u + encLen Bw b then
        some (encAt (Fintype.card V) Bw (agg S par rk val op (root u))
          (s - bStart Bw b sz - dep par rk u))
      else none := by
  have h0 : s ≠ 0 := by unfold bStart at h1; omega
  rw [tcSched, ite_eq_right h0, ite_eq_right (by omega)]

lemma encLen_pos : 0 < encLen Bw b := by unfold encLen; positivity

variable {Bw b sz S par rk val op root}

/-- the history of `u` after `s` rounds of the schedule -/
local notation "HS" u:max s:max =>
  hget (schedHist (tcSched Bw b sz S par rk val op root) u s)

lemma kidsH_sched (u : V) {s : ℕ} (hs : 0 < s) : kidsH (HS u s) = kidsOf S par u := by
  ext w
  simp only [kidsH, mem_filter, mem_univ, true_and, mem_kidsOf]
  rw [hget_schedHist _ u hs, tcSched_zero]
  split_ifs with h <;> simp [h]

lemma upW_sched {u c : V} (hc : c ∈ kidsOf S par u) {s k : ℕ}
    (hks : k * encLen Bw b < s) (hk : k ≤ sz) :
    upW (HS u s) c (k * encLen Bw b) =
      if hgt S par rk c < k then enc (Fintype.card V) Bw b (agg S par rk val op c) else [] := by
  have hc' := mem_kidsOf.1 hc
  unfold upW enc
  rw [← filterMap_slot (encLen Bw b) (hgt S par rk c) (encLen_pos Bw b)]
  apply List.filterMap_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [hget_schedHist _ u (by omega), tcSched_up _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  · simp only [hc', true_and, Nat.add_sub_cancel]
  · unfold bStart
    have : k * encLen Bw b ≤ sz * encLen Bw b := Nat.mul_le_mul_right _ hk
    omega

lemma rdy_sched (hT : TreeOK S par rk root) {u : V} {s k : ℕ} (hks : k * encLen Bw b < s)
    (hk : k ≤ sz) : rdy (encLen Bw b) (HS u s) k ↔ hgt S par rk u ≤ k := by
  unfold rdy
  rw [kidsH_sched u (by omega), hgt_eq hT.rank u, Finset.sup_le_iff]
  apply forall₂_congr
  intro c hc
  rw [upW_sched (val := val) (op := op) hc hks hk]
  have hL := encLen_pos Bw b
  split_ifs with h
  · rw [length_enc]; simp only [le_refl, true_iff]; omega
  · simp only [List.length_nil]; constructor <;> intro h' <;> omega

lemma myAgg_sched (hT : TreeOK S par rk root)
    (henc : ∀ c ∈ S, EncOK (Fintype.card V) Bw b (agg S par rk val op c)) {u : V} {s k : ℕ}
    (hks : k * encLen Bw b < s) (hk : k ≤ sz) (hh : hgt S par rk u ≤ k) :
    myAgg Bw b (HS u s) (val u) op (k * encLen Bw b) = agg S par rk val op u := by
  unfold myAgg
  rw [kidsH_sched u (by omega), agg_eq hT.rank]
  apply List.foldl_ext
  intro a c hc
  rw [Finset.mem_toList] at hc
  have hcS := (mem_kidsOf.1 hc).1
  rw [upW_sched hc hks hk, ite_eq_left (lt_of_lt_of_le (hgt_kid hT.rank hc) hh),
    dec_enc _ _ _ _ (henc c hcS).1 (henc c hcS).2]

/-- **The protocol follows the schedule**: fed with the history of the schedule, a node sends
exactly the messages of the schedule. -/
lemma tcSend_sched (hT : TreeOK S par rk root) (hsz : S.card ≤ sz)
    (henc : ∀ c ∈ S, EncOK (Fintype.card V) Bw b (agg S par rk val op c)) (u v : V) {s : ℕ}
    (hs : s < tEnd Bw b sz) :
    tcSend Bw b sz (if u ∈ S then some (par u, root u, val u, op) else none) s (HS u s) v =
      tcSched Bw b sz S par rk val op root u v s := by
  by_cases hu : u ∈ S
  · rw [ite_eq_left hu]
    simp only [tcSend]
    by_cases hs0 : s = 0
    · subst hs0; rw [tcSched_zero, ite_eq_left rfl]; simp [hu]
    · rw [ite_eq_right hs0]
      have hkids := kidsH_sched (Bw := Bw) (b := b) (sz := sz) (S := S) (par := par) (rk := rk)
        (val := val) (op := op) (root := root) u (Nat.pos_of_ne_zero hs0)
      have hL := encLen_pos Bw b
      by_cases hup : s < bStart Bw b sz
      · rw [ite_eq_left hup, tcSched_up _ _ _ _ _ _ _ _ _ _ _ hs0 hup]
        have hkL : (s - 1) / encLen Bw b * encLen Bw b ≤ s - 1 := Nat.div_mul_le_self _ _
        have hksz : (s - 1) / encLen Bw b ≤ sz := by
          by_contra h
          replace h := Nat.lt_of_not_le h
          have h1 : (sz + 1) * encLen Bw b ≤ (s - 1) / encLen Bw b * encLen Bw b :=
            Nat.mul_le_mul_right _ h
          unfold bStart at hup
          rw [add_mul, one_mul] at h1
          omega
        have hr1 : rdy (encLen Bw b) (HS u s) ((s - 1) / encLen Bw b) ↔
            hgt S par rk u ≤ (s - 1) / encLen Bw b :=
          rdy_sched (val := val) (op := op) hT (by omega) hksz
        have hr2 : 0 < (s - 1) / encLen Bw b →
            (rdy (encLen Bw b) (HS u s) ((s - 1) / encLen Bw b - 1) ↔
              hgt S par rk u ≤ (s - 1) / encLen Bw b - 1) := fun hk0 => by
          have h1 : ((s - 1) / encLen Bw b - 1) * encLen Bw b ≤
              (s - 1) / encLen Bw b * encLen Bw b := Nat.mul_le_mul_right _ (Nat.sub_le _ 1)
          exact rdy_sched (val := val) (op := op) hT (by omega) (by omega)
        by_cases hc : par u = some v ∧ hgt S par rk u = (s - 1) / encLen Bw b
        · rw [ite_eq_left ⟨hc.1, hr1.2 hc.2.le, fun h => by have := (hr2 h.1).1 h.2; omega⟩,
            ite_eq_left ⟨hu, hc.1, hc.2.symm⟩, myAgg_sched hT henc (by omega) hksz hc.2.le]
        · rw [ite_eq_right, ite_eq_right]
          · rintro ⟨_, h1, h2⟩; exact hc ⟨h1, h2.symm⟩
          · rintro ⟨h1, h2, h3⟩
            apply hc ⟨h1, _⟩
            have := hr1.1 h2
            by_contra hne
            have hk0 : 0 < (s - 1) / encLen Bw b := by omega
            exact h3 ⟨hk0, (hr2 hk0).2 (by omega)⟩
      · rw [ite_eq_right hup, tcSched_down _ _ _ _ _ _ _ _ _ _ _ (by omega), hkids]
        by_cases hv : v ∈ kidsOf S par u
        · rw [ite_eq_left hv]
          have hv' := mem_kidsOf.1 hv
          cases hp : par u with
          | none =>
            have hh : hgt S par rk u ≤ sz := (hgt_lt hT.mem hT.rank hu).le.trans hsz
            unfold bStart at hup
            dsimp only
            rw [myAgg_sched hT henc (by omega) le_rfl hh, dep_none hp,
              hT.root_self u hu hp]
            by_cases hw : s - bStart Bw b sz < encLen Bw b
            · rw [ite_eq_left hw, ite_eq_left ⟨hv'.1, hv'.2, Nat.zero_le _, by omega⟩, Nat.sub_zero]
            · rw [ite_eq_right hw, ite_eq_right (by omega)]
          | some p =>
            dsimp only
            have hdep := dep_some hT.rank hu hp
            have hroot := hT.root_par u hu p hp
            by_cases hs1 : bStart Bw b sz < s
            · rw [ite_eq_left hs1, hget_schedHist _ u (by omega),
                tcSched_down _ _ _ _ _ _ _ _ _ _ _ (by omega), hroot]
              by_cases hw : dep par rk p ≤ s - 1 - bStart Bw b sz ∧
                  s - 1 - bStart Bw b sz < dep par rk p + encLen Bw b
              · rw [ite_eq_left ⟨hu, hp, hw⟩, ite_eq_left ⟨hv'.1, hv'.2, by omega, by omega⟩]
                rw [show s - 1 - bStart Bw b sz - dep par rk p = s - bStart Bw b sz - dep par rk u by
                  omega]
              · rw [ite_eq_right (fun h => hw ⟨h.2.2.1, h.2.2.2⟩),
                  ite_eq_right (fun h => hw ⟨by omega, by omega⟩)]
            · rw [ite_eq_right hs1, ite_eq_right (by omega)]
        · rw [ite_eq_right hv, ite_eq_right (fun h => hv (mem_kidsOf.2 ⟨h.1, h.2.1⟩))]
  · rw [ite_eq_right hu]
    simp only [tcSend]
    symm
    rw [tcSched]
    by_cases h0 : s = 0
    · rw [ite_eq_left h0, ite_eq_right (fun h => hu h.1)]
    · rw [ite_eq_right h0]
      by_cases h1 : s < bStart Bw b sz
      · rw [ite_eq_left h1, ite_eq_right (fun h => hu h.1)]
      · rw [ite_eq_right h1, ite_eq_right (fun h => hu (hT.mem v h.1 u h.2.1))]

/-- **Outputs**: at the halting round, every node of `S` holds the aggregate of its tree. -/
lemma tcRes_sched (hT : TreeOK S par rk root) (hsz : S.card ≤ sz)
    (henc : ∀ c ∈ S, EncOK (Fintype.card V) Bw b (agg S par rk val op c)) {u : V} (hu : u ∈ S) :
    tcRes Bw b sz (some (par u, root u, val u, op)) (HS u (tEnd Bw b sz)) =
      some (agg S par rk val op (root u)) := by
  simp only [tcRes]
  congr 1
  have hL := encLen_pos Bw b
  cases hp : par u with
  | none =>
    dsimp only
    have hh : hgt S par rk u ≤ sz := (hgt_lt hT.mem hT.rank hu).le.trans hsz
    rw [myAgg_sched hT henc (by unfold tEnd bStart; omega) le_rfl hh, hT.root_self u hu hp]
  | some p =>
    dsimp only
    have hpS := hT.mem u hu p hp
    have hroot := hT.root_par u hu p hp
    have hdp : dep par rk p < sz := (dep_lt hT.mem hT.rank hpS).trans_le hsz
    have hrS := (root_spec hT.mem hT.rank hT.root_par hT.root_self hpS).1
    rw [← hroot]
    have hw : (List.range (sz + encLen Bw b)).filterMap
        (fun j => hget (schedHist (tcSched Bw b sz S par rk val op root) u (tEnd Bw b sz))
          (bStart Bw b sz + j) p) =
        enc (Fintype.card V) Bw b (agg S par rk val op (root p)) := by
      unfold enc
      rw [← filterMap_window (dep par rk p) (encLen Bw b) (sz + encLen Bw b) _ (by omega)]
      apply List.filterMap_congr
      intro j hj
      rw [List.mem_range] at hj
      rw [hget_schedHist _ u (by unfold tEnd; omega), tcSched_down _ _ _ _ _ _ _ _ _ _ _ (by omega)]
      simp only [hu, hp, true_and, Nat.add_sub_cancel_left]
    rw [hw, dec_enc _ _ _ _ (henc _ hrS).1 (henc _ hrS).2]

/-- Only tree edges carry messages. -/
lemma tcSched_isSome {u v : V} {s : ℕ} (h : (tcSched Bw b sz S par rk val op root u v s).isSome) :
    (u ∈ S ∧ par u = some v) ∨ (v ∈ S ∧ par v = some u) := by
  by_cases h0 : s = 0
  · rw [h0, tcSched_zero] at h
    split_ifs at h with h1
    · exact Or.inl h1
    · simp at h
  · by_cases h1 : s < bStart Bw b sz
    · rw [tcSched_up _ _ _ _ _ _ _ _ _ _ _ h0 h1] at h
      split_ifs at h with h2
      · exact Or.inl ⟨h2.1, h2.2.1⟩
      · simp at h
    · rw [tcSched_down _ _ _ _ _ _ _ _ _ _ _ (by omega)] at h
      split_ifs at h with h2
      · exact Or.inr ⟨h2.1, h2.2.1⟩
      · simp at h

/-- At most `1 + 2L` messages per directed pair: the announcement, the value sent up, the value
sent down. -/
lemma tcSched_count (u v : V) (T : ℕ) :
    ((range T).filter (fun s => (tcSched Bw b sz S par rk val op root u v s).isSome)).card ≤
      1 + 2 * encLen Bw b := by
  have hL := encLen_pos Bw b
  have hsub : (range T).filter (fun s => (tcSched Bw b sz S par rk val op root u v s).isSome) ⊆
      (range 1 ∪ Ico (1 + encLen Bw b * hgt S par rk u) (1 + encLen Bw b * hgt S par rk u +
        encLen Bw b)) ∪ Ico (bStart Bw b sz + dep par rk u)
          (bStart Bw b sz + dep par rk u + encLen Bw b) := by
    intro s hs
    rw [mem_filter] at hs
    have h' := hs.2
    simp only [mem_union, mem_range, mem_Ico]
    by_cases h0 : s = 0
    · left; left; omega
    · by_cases h1 : s < bStart Bw b sz
      · rw [tcSched_up _ _ _ _ _ _ _ _ _ _ _ h0 h1] at h'
        split_ifs at h' with h2
        · left; right
          have e1 := Nat.div_add_mod (s - 1) (encLen Bw b)
          have e2 := Nat.mod_lt (s - 1) hL
          rw [h2.2.2] at e1
          omega
        · simp at h'
      · rw [tcSched_down _ _ _ _ _ _ _ _ _ _ _ (by omega)] at h'
        split_ifs at h' with h2
        · right; omega
        · simp at h'
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have := card_union_le (range 1) (Ico (1 + encLen Bw b * hgt S par rk u)
    (1 + encLen Bw b * hgt S par rk u + encLen Bw b))
  simp only [card_range, Nat.card_Ico] at this ⊢
  omega

end Sched

/-! ## Success on a general instance -/

/-- the constant of the cost bounds -/
def tcK (Bw : ℕ) : ℕ := 4 * Bw + 10

/-- the specification of the task -/
def TCSpec (S : Finset V) (root : V → V) (val : V → Msg V) (op : Msg V → Msg V → Msg V)
    (y : Agent V → Option (Msg V)) : Prop :=
  ∀ v ∈ S, ∃ Y, y (.inl v) = some Y ∧
    AggOf op ((S.filter (fun u => root u = root v)).val.map val) Y ∧
    ∀ u ∈ S, root u = root v → y (.inl u) = some Y

/-- **Correctness and costs of the protocol on any instance** whose graph contains the tree edges,
where every node knows `sz`, its own identity and its own input, and where `.inl u` is hosted
(if at all) by `u`. -/
theorem tc_succ (Bw b : ℕ) (I : Inst V) (x : Agent V → Mem) (S : Finset V) (par : V → Option V)
    (rk : V → ℕ) (val : V → Msg V) (op : Msg V → Msg V → Msg V) (root : V → V) (sz : ℕ)
    (Fp : Finset (Sym2 V)) (hT : TreeOK S par rk root) (hsz : S.card ≤ sz)
    (henc : ∀ c ∈ S, EncOK (Fintype.card V) Bw b (agg S par rk val op c))
    (hFp : ∀ v ∈ S, ∀ u, par v = some u → s(v, u) ∈ Fp)
    (hadj : ∀ v ∈ S, ∀ u, par v = some u → I.G.Adj v u)
    (hctx : ∀ v, szOf (I.ctx v) = sz ∧ (I.ctx v).me = v)
    (hin : ∀ v, myIn (inpAt I x v) v = if v ∈ S then some (par v, root v, val v, op) else none)
    (hhost : ∀ u v, I.host (.inl u) = some v → u = v) (ω : V → Unit) :
    Succ (tcProto Bw b V) I x (postOf I (TCSpec S root val op))
      (Prof.mk (tcK Bw * (b + 1) * (sz + 1)) (onEdges Fp (tcK Bw * (b + 1)))
        (tcK Bw * (b + 1) * (S.card + 1))) ω := by
  classical
  set M := tcSched Bw b sz S par rk val op root with hMdef
  set L := encLen Bw b with hLdef
  have hL : L = (b + 1) * (Bw + 2) := rfl
  have hTP : ∀ u v s, (M u v s).isSome → s(u, v) ∈ Fp ∧ I.G.Adj u v := by
    intro u v s h
    rcases tcSched_isSome h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hFp u h1 v h2, hadj u h1 v h2⟩
    · exact ⟨Sym2.eq_swap ▸ hFp v h1 u h2, (hadj v h1 u h2).symm⟩
  have hM : ∀ s < tEnd Bw b sz, ∀ u v, (I.part u → tcSend Bw b (szOf (I.ctx u))
      (myIn (inpAt I x u) (I.ctx u).me) (schedHist M u s).length (hget (schedHist M u s)) v =
        M u v s) ∧ (¬ I.G.Adj u v → M u v s = none) ∧
        ∀ w, M u v s = some w → WordOK (Fintype.card V) w := by
    intro s hs u v
    refine ⟨fun _ => ?_, fun hn => ?_, fun w hw => ?_⟩
    · rw [(hctx u).1, (hctx u).2, hin u, length_schedHist]
      exact tcSend_sched hT hsz henc u v hs
    · cases h : M u v s with
      | none => rfl
      | some w => exact absurd (hTP u v s (by simp [h])).2 hn
    · rw [hMdef] at hw
      unfold tcSched at hw
      split_ifs at hw <;> simp only [Option.some.injEq] at hw <;> subst hw <;>
        first | exact encAt_ok _ _ _ _ | (simp only [WordOK]; omega)
  have hcnt : ∀ u v, ((range (tEnd Bw b sz)).filter (fun s => (M u v s).isSome)).card ≤
      1 + 2 * L := fun u v => tcSched_count u v _
  unfold tcProto
  refine succ_histP
    (F := fun c inp h v => tcSend Bw b (szOf c) (myIn inp c.me) h.length (hget h) v)
    (Tf := fun c => tEnd Bw b (szOf c))
    (O := fun c inp h g => some ⟨Option (Msg V),
      if g = .inl c.me then tcRes Bw b (szOf c) (myIn inp c.me) (hget h) else none⟩)
    (T := tEnd Bw b sz) (fun v => by simp only [(hctx v).1]) M hM ?_ ?_ ?_
    (fun g => ⟨Option (Msg V), match g with
      | .inl v => if v ∈ S then some (agg S par rk val op (root v)) else none
      | .inr _ => none⟩) ?_ ?_
  · -- rounds
    simp only [Prof.rounds_mk, tEnd, bStart, tcK]
    rw [← hLdef, hL]
    nlinarith
  · -- messages
    simp only [Prof.msgs_mk]
    rw [sum_card_filter_swap]
    refine (sum_le_mul_card _ (fun uv : V × V => (uv.1 ∈ S ∧ par uv.1 = some uv.2) ∨
      (uv.2 ∈ S ∧ par uv.2 = some uv.1)) (1 + 2 * L) (fun uv => ?_)).trans ?_
    · split_ifs with h
      · exact hcnt uv.1 uv.2
      · rw [Finset.card_eq_zero.2]
        apply filter_eq_empty_iff.2
        intro s _ hs
        exact h (tcSched_isSome hs)
    · have h1 := card_treePairs S par
      have h2 : 2 * (1 + 2 * L) ≤ tcK Bw * (b + 1) := by
        rw [hL]; unfold tcK; nlinarith
      calc (1 + 2 * L) * _ ≤ (1 + 2 * L) * (2 * S.card) := Nat.mul_le_mul_left _ h1
        _ = 2 * (1 + 2 * L) * S.card := by ring
        _ ≤ tcK Bw * (b + 1) * S.card := Nat.mul_le_mul_right _ h2
        _ ≤ tcK Bw * (b + 1) * (S.card + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · -- load
    intro e
    simp only [Prof.load_mk, onEdges]
    simp only [filter_filter]
    rw [sum_card_filter_swap]
    refine (sum_le_mul_card _ (fun uv : V × V => s(uv.1, uv.2) = e ∧ s(uv.1, uv.2) ∈ Fp)
      (1 + 2 * L) (fun uv => ?_)).trans ?_
    · split_ifs with h
      · refine (card_le_card (fun s hs => ?_)).trans (hcnt uv.1 uv.2)
        simp only [mem_filter] at hs ⊢
        exact ⟨hs.1, hs.2.1⟩
      · rw [Finset.card_eq_zero.2]
        apply filter_eq_empty_iff.2
        intro s _ hs
        exact h ⟨hs.2, hs.2 ▸ (hTP _ _ _ hs.1).1⟩
    · split_ifs with he
      · have h1 : (univ.filter (fun uv : V × V => s(uv.1, uv.2) = e ∧ s(uv.1, uv.2) ∈ Fp)).card ≤ 2 :=
          (card_le_card (fun uv h => by
            simp only [mem_filter] at h ⊢; exact ⟨h.1, h.2.1⟩)).trans (card_sym2_fiber e)
        have h2 : 2 * (1 + 2 * L) ≤ tcK Bw * (b + 1) := by
          rw [hL]; unfold tcK; nlinarith
        calc (1 + 2 * L) * _ ≤ (1 + 2 * L) * 2 := Nat.mul_le_mul_left _ h1
          _ ≤ tcK Bw * (b + 1) := by linarith
      · rw [Finset.card_eq_zero.2]
        · simp
        apply filter_eq_empty_iff.2
        rintro uv - ⟨h1, h2⟩
        exact he (h1 ▸ h2)
  · -- outputs
    intro g v hg
    simp only [(hctx v).2, (hctx v).1]
    cases g with
    | inl u =>
      obtain rfl := hhost u v hg
      rw [ite_eq_left rfl, hin u]
      by_cases hu : u ∈ S
      · rw [ite_eq_left hu, tcRes_sched hT hsz henc hu]; simp [hu]
      · rw [ite_eq_right hu]; simp [hu, tcRes]
    | inr C =>
      rw [ite_eq_right (by simp)]
  · -- postcondition
    refine ⟨_, fun g _ => rfl, ?_⟩
    intro v hv
    refine ⟨agg S par rk val op (root v), by simp [hv], ?_, fun u hu hr => by simp [hu, hr]⟩
    obtain ⟨hrS, hrp, -⟩ := root_spec hT.mem hT.rank hT.root_par hT.root_self hv
    have := agg_spec hT.mem hT.rank val op (root v) hrS
    rwa [desc_root hT.mem hT.rank hT.root_par hT.root_self hrS hrp] at this

/-! ## The theorem -/

/-- **Tree convergecast followed by broadcast** in the CONGEST semantics: the concrete version of
the toolkit field `treeCast` (`TreeCastC` in `Model.lean`), with `K = 4 * Bw + 10`, on the overlay
instance with participants `Pt ⊇ S` (nodes of `Pt \ S` idle until the public halting round). -/
theorem treeCast_congest (Bw : ℕ) : ∃ (K : ℕ) (A : ℕ → ℕ → CAlg), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (ν : ℕ), ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (b : ℕ) (par : V → Option V)
    (root : V → V) (val : V → Msg V) (op : Msg V → Msg V → Msg V) (Fp : Finset (Sym2 V))
    (x : Agent V → Option (Option V × V × Msg V × (Msg V → Msg V → Msg V))),
    (∀ v, x (.inl v) = if v ∈ S then some (par v, root v, val v, op) else none) →
    S.card ≤ sz → S ⊆ Pt → Fp ⊆ N.G.edgeFinset →
    (∀ v ∈ S, ∀ u, par v = some u → u ∈ S ∧ s(v, u) ∈ Fp) →
    (∀ v ∈ S, ∀ u, par v = some u → root u = root v) → (∀ v ∈ S, par v = none → root v = v) →
    (∃ r : V → ℕ, ∀ v ∈ S, ∀ u, par v = some u → r u < r v) →
    (∀ v ∈ S, (val v).Small b (ν ^ Bw)) →
    (∀ m m', m.Small b (ν ^ Bw) → m'.Small b (ν ^ Bw) → (op m m').Small b (ν ^ Bw)) →
    CImplT (A ν b) N (.io E j sz Pt (Option (Option V × V × Msg V × (Msg V → Msg V → Msg V)))
        (Option (Msg V)) x
      (fun y => ∀ v ∈ S, ∃ Y, y (.inl v) = some Y ∧
        AggOf op ((S.filter (fun u => root u = root v)).val.map val) Y ∧
        ∀ u ∈ S, root u = root v → y (.inl u) = some Y))
      (Prof.mk (K * (b + 1) * (sz + 1)) (onEdges Fp (K * (b + 1))) (K * (b + 1) * (S.card + 1)))
      0 := by
  refine ⟨tcK Bw, treeCastAlg Bw, ?_⟩
  intro V _ _ N ν hν E j sz Pt S b par root val op Fp x hx hsz hSPt hFpG hpar hroot hself
    ⟨rk, hrk⟩ hval hop
  have hT : TreeOK S par rk root := ⟨fun v hv u h => (hpar v hv u h).1, hrk, hroot, hself⟩
  have henc : ∀ c ∈ S, EncOK (Fintype.card V) Bw b (agg S par rk val op c) := by
    intro c hc
    have h := agg_pres hrk val op (fun m => m.Small b (ν ^ Bw)) hval hop c hc
    refine ⟨h.1, fun k hk => ?_⟩
    calc k ≤ ν ^ Bw := h.2 k hk
      _ ≤ (Fintype.card V + 4) ^ Bw := Nat.pow_le_pow_left (by omega) _
      _ < (Fintype.card V + 4) ^ (Bw + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  show ImplI (tcProto Bw b V) (ioInst N E j sz Pt) (inOf x)
    (postOf (ioInst N E j sz Pt) (TCSpec S root val op)) _ 0
  refine ImplI.of_forall _ _ le_rfl (fun ω => ?_)
  refine tc_succ Bw b (ioInst N E j sz Pt) (inOf x) S par rk val op root sz Fp hT hsz henc
    (fun v hv u h => (hpar v hv u h).2) (fun v hv u h => ?_) (fun v => ⟨rfl, rfl⟩) (fun v => ?_)
    (fun u v h => ?_) ω
  · -- tree edges are edges of the overlay graph, since `S ⊆ Pt`
    have := hFpG (hpar v hv u h).2
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    exact ⟨this, hSPt hv, hSPt (hpar v hv u h).1⟩
  · -- the own input
    by_cases hv : v ∈ Pt
    · rw [← hx v]
      simp [myIn, inpAt, ioInst, ioHost, inOf, hv]
    · have hvS : v ∉ S := fun h => hv (hSPt h)
      rw [ite_eq_right hvS]
      simp [myIn, inpAt, ioInst, ioHost, hv]
  · -- hosting of the physical agents
    simp only [ioInst, ioHost] at h
    split_ifs at h
    exact Option.some.inj h

end APSP.Stoc.Congest
