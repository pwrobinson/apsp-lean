import ApspStoc.Congest.RingComb
import ApspStoc.Congest.TreeCastAux

/-!
# Ring orientation in CONGEST: basic material (`ringLE_congest`, part 1)

This file provides the building blocks of the ring-orientation protocol of `RingLE.lean`:

* **Probe packets** (`Pk`): a probe crossing one ring link is a packet of `7` words: the origin
  end `(o, oi)` of the probe, the departure end's node `v`, the link's edges `e` (at `v`) and `e'`
  (at the partner), the partner node `w`, and the key edge of the embedded path the packet is
  currently travelling (`key`). `pkWord`/`pkDec`: encoding as words and decoding.
* **Ranks** (`rank`, `atRank`): packets held by a node at the same hop are sent one after another,
  in slots ordered by the origin of the probe.
* **Walks** (`oth`, `wnode`): the node at a position of an embedded path.
* **Time layout**: phases `i ≤ Φ`, each of `2^i` link steps; a link step has `2 D` hops
  (`D = dil + 1`: `D` hops up the departure node's path to the aggregator's host, then `D` hops
  down the partner's path); a hop has `slots B i` slots of `7` rounds. `Tm` is a time point
  (phase, link step, hop, slot, word) and `rnd` its round; `tq` recovers the time point of a round.
* **Local rules** of a node, from its context only: `keyL` (the key edge of the cluster of an own
  segment edge), `hostC`/`turnL` (the host of an aggregator turns a packet to the partner's path),
  `stepL` (where a held packet goes at a hop), `sendFrom` (what is sent in a slot), `pkL`
  (the packet of a departing probe), `arrIdx` (the own end at which a packet arrives).
-/

namespace APSP.Stoc.Congest
namespace RingLE

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Packets -/

/-- A probe packet: origin end `(o, oi)`, departure node `v`, the link's edges `e` (at `v`) and
`e'` (at the partner `w`), and the key edge `key` of the embedded path it currently travels. -/
structure Pk (V : Type) where
  /-- origin node of the probe -/
  o : V
  /-- origin index of the probe (an end of `o`) -/
  oi : ℕ
  /-- departure node of the link -/
  v : V
  /-- the link's edge at `v` -/
  e : Sym2 V
  /-- the link's edge at `w` -/
  e' : Sym2 V
  /-- the partner (arrival) node of the link -/
  w : V
  /-- key edge of the path travelled: `v`'s path (up) or `w`'s path (down) -/
  key : Sym2 V
  deriving DecidableEq

/-- the origin end of a packet's probe -/
def Pk.orig (π : Pk V) : V × ℕ := (π.o, π.oi)

/-- the `t`-th word of a packet (`t < 7`) -/
def pkWord (π : Pk V) : ℕ → Word V
  | 0 => .id π.o
  | 1 => .num π.oi
  | 2 => .id π.v
  | 3 => .edge π.e
  | 4 => .edge π.e'
  | 5 => .id π.w
  | _ => .edge π.key

/-- decoding a packet from its `7` words (`none` if a word is missing or ill-formed) -/
def pkDec (f : ℕ → Option (Word V)) : Option (Pk V) :=
  match f 0, f 1, f 2, f 3, f 4, f 5, f 6 with
  | some (.id o), some (.num oi), some (.id v), some (.edge e), some (.edge e'), some (.id w),
      some (.edge k) => some ⟨o, oi, v, e, e', w, k⟩
  | _, _, _, _, _, _, _ => none

omit [Fintype V] [DecidableEq V] in
lemma pkDec_word (π : Pk V) : pkDec (fun t => some (pkWord π t)) = some π := by
  cases π; rfl

omit [Fintype V] [DecidableEq V] in
lemma pkDec_none : pkDec (V := V) (fun _ => none) = none := rfl

omit [Fintype V] [DecidableEq V] in
lemma pkDec_congr {f g : ℕ → Option (Word V)} (h : ∀ t < 7, f t = g t) : pkDec f = pkDec g := by
  unfold pkDec
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega)]

omit [DecidableEq V] in
/-- the words of a packet are valid if its origin index is at most `n + 3` -/
lemma pkWord_ok (π : Pk V) (h : π.oi ≤ Fintype.card V + 3) (t : ℕ) :
    WordOK (Fintype.card V) (pkWord π t) := by
  rcases t with _ | _ | _ | _ | _ | _ | t <;> simp [pkWord, WordOK, h]

/-! ## Ranks -/

/-- the sorting key of a packet: its origin end, lexicographically -/
noncomputable def pkKey (π : Pk V) : ℕ ×ₗ ℕ := toLex (((Fintype.equivFin V π.o : Fin _) : ℕ), π.oi)

omit [DecidableEq V] in
lemma pkKey_eq {π π' : Pk V} (h : pkKey π = pkKey π') : π.orig = π'.orig := by
  simp only [pkKey, toLex_inj, Prod.mk.injEq, Fin.val_inj] at h
  exact Prod.ext ((Fintype.equivFin V).injective h.1) h.2

/-- the rank of a packet in a set: the number of packets with a smaller key -/
noncomputable def rank (X : Finset (Pk V)) (π : Pk V) : ℕ := (X.filter (fun π' => pkKey π' < pkKey π)).card

/-- the packet of rank `σ` in `X` -/
noncomputable def atRank (X : Finset (Pk V)) (σ : ℕ) : Option (Pk V) :=
  if h : ∃ π ∈ X, rank X π = σ then some h.choose else none

/-- keys are injective on `X` -/
def KeyInj (X : Finset (Pk V)) : Prop := ∀ π ∈ X, ∀ π' ∈ X, pkKey π = pkKey π' → π = π'

lemma atRank_some {X : Finset (Pk V)} {σ : ℕ} {π : Pk V} (h : atRank X σ = some π) :
    π ∈ X ∧ rank X π = σ := by
  unfold atRank at h
  by_cases hex : ∃ π ∈ X, rank X π = σ
  · rw [dite_eq_left hex] at h; cases h; exact hex.choose_spec
  · rw [dite_eq_right hex] at h; cases h

lemma rank_lt_card {X : Finset (Pk V)} {π : Pk V} (h : π ∈ X) : rank X π < X.card := by
  apply card_lt_card
  refine ⟨filter_subset _ _, fun hsub => ?_⟩
  have := hsub h
  simp at this

lemma rank_inj {X : Finset (Pk V)} (hX : KeyInj X) {π π' : Pk V} (h : π ∈ X) (h' : π' ∈ X)
    (hr : rank X π = rank X π') : π = π' := by
  by_contra hne
  have hk : pkKey π ≠ pkKey π' := fun hk => hne (hX π h π' h' hk)
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · have : rank X π < rank X π' := by
      apply card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
      · have := hsub (mem_filter.2 ⟨h, hlt⟩); simp at this
    omega
  · have : rank X π' < rank X π := by
      apply card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
      · have := hsub (mem_filter.2 ⟨h', hlt⟩); simp at this
    omega

lemma atRank_rank {X : Finset (Pk V)} (hX : KeyInj X) {π : Pk V} (h : π ∈ X) :
    atRank X (rank X π) = some π := by
  have hex : ∃ π' ∈ X, rank X π' = rank X π := ⟨π, h, rfl⟩
  unfold atRank
  rw [dite_eq_left hex]
  congr 1
  exact rank_inj hX hex.choose_spec.1 h hex.choose_spec.2

/-! ## Walks -/

section Walks

variable {W : Type}

open Classical in
/-- the other endpoint of the edge `e` seen from `u` (`u` if `u ∉ e`) -/
noncomputable def oth (u : W) (e : Sym2 W) : W := if h : ∃ y, e = s(u, y) then h.choose else u

lemma oth_mk (u y : W) : oth u s(u, y) = y := by
  have hex : ∃ y', s(u, y) = s(u, y') := ⟨y, rfl⟩
  unfold oth
  rw [dite_eq_left hex]
  have := hex.choose_spec
  rw [Sym2.eq_iff] at this
  rcases this with ⟨_, h⟩ | ⟨h1, h2⟩
  · exact h.symm
  · rw [← h1, h2]

lemma oth_mk' (u y : W) : oth u s(y, u) = y := by
  rw [Sym2.eq_swap]; exact oth_mk u y

/-- the node at position `p` of the walk `l` from `a` (the end of the walk for `p ≥ |l|`) -/
noncomputable def wnode : List (Sym2 W) → W → ℕ → W
  | [], a, _ => a
  | _ :: _, a, 0 => a
  | e :: l, a, p + 1 => wnode l (oth a e) p

@[simp] lemma wnode_zero (l : List (Sym2 W)) (a : W) : wnode l a 0 = a := by
  cases l <;> rfl

lemma isEdgeWalk_cons {e : Sym2 W} {l : List (Sym2 W)} {a b : W} (h : IsEdgeWalk (e :: l) a b) :
    e = s(a, oth a e) ∧ IsEdgeWalk l (oth a e) b := by
  obtain ⟨x, rfl, hx⟩ := h
  rw [oth_mk]; exact ⟨rfl, hx⟩

/-- the end of a walk is determined -/
lemma isEdgeWalk_unique : ∀ {l : List (Sym2 W)} {a b b' : W}, IsEdgeWalk l a b →
    IsEdgeWalk l a b' → b = b'
  | [], _, _, _, h, h' => h.symm.trans h'
  | _ :: _, _, _, _, h, h' => isEdgeWalk_unique (isEdgeWalk_cons h).2 (isEdgeWalk_cons h').2

lemma wnode_ge : ∀ {l : List (Sym2 W)} {a b : W} {p : ℕ}, IsEdgeWalk l a b → l.length ≤ p →
    wnode l a p = b
  | [], _, _, _, h, _ => h
  | _ :: _, _, _, 0, _, hp => by simp at hp
  | _ :: _, _, _, p + 1, h, hp => by
    simp only [wnode]
    exact wnode_ge (isEdgeWalk_cons h).2 (by simp at hp; omega)

lemma wnode_get : ∀ {l : List (Sym2 W)} {a b : W} {p : ℕ}, IsEdgeWalk l a b →
    ∀ (hp : p < l.length), l[p] = s(wnode l a p, wnode l a (p + 1))
  | [], _, _, _, _, hp => by simp at hp
  | e :: l, a, b, 0, h, _ => by
    obtain ⟨h1, h2⟩ := isEdgeWalk_cons h
    simp only [List.getElem_cons_zero, wnode_zero, wnode]
    exact h1
  | e :: l, a, b, p + 1, h, hp => by
    simp only [List.getElem_cons_succ, wnode]
    exact wnode_get (isEdgeWalk_cons h).2 (by simp at hp; omega)

lemma oth_wnode {l : List (Sym2 W)} {a b : W} {p : ℕ} (h : IsEdgeWalk l a b) (hp : p < l.length) :
    oth (wnode l a p) l[p] = wnode l a (p + 1) := by
  rw [wnode_get h hp, oth_mk]

lemma oth_wnode' {l : List (Sym2 W)} {a b : W} {p : ℕ} (h : IsEdgeWalk l a b)
    (hp : p < l.length) : oth (wnode l a (p + 1)) l[p] = wnode l a p := by
  rw [wnode_get h hp, oth_mk']

/-- the nodes of a walk lie on it -/
lemma wnode_onWalk : ∀ (l : List (Sym2 W)) (a : W) (p : ℕ), OnWalk l a (wnode l a p)
  | [], _, _ => Or.inl rfl
  | _ :: _, _, 0 => Or.inl rfl
  | e :: l, a, p + 1 => by
    simp only [wnode]
    rcases wnode_onWalk l (oth a e) p with h | ⟨e', he', hx⟩
    · rw [h]
      by_cases hex : ∃ y, e = s(a, y)
      · right
        refine ⟨e, List.mem_cons_self, ?_⟩
        obtain ⟨y, rfl⟩ := hex
        rw [oth_mk]; exact Sym2.mem_mk_right _ _
      · left
        unfold oth; rw [dite_eq_right hex]
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hx⟩

end Walks

/-! ## Time layout -/

/-- the number of phases is `Φ + 1` -/
def phiOf (B : ℕ) : ℕ := Nat.log 2 B + 1

/-- the number of slots of a hop in phase `i` (a bound on the probes in flight) -/
def slots (B i : ℕ) : ℕ := 4 * B / 2 ^ i + 1

/-- the length of a hop in phase `i`: `slots` slots of `7` rounds -/
def hopLen (B i : ℕ) : ℕ := slots B i * 7

/-- the length of a link step in phase `i`: `2 D` hops -/
def stepLen (D B i : ℕ) : ℕ := 2 * D * hopLen B i

/-- the length of phase `i`: `2^i` link steps -/
def phLen (D B i : ℕ) : ℕ := 2 ^ i * stepLen D B i

/-- the first round of phase `i` -/
def phStart (D B : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => phStart D B i + phLen D B i

/-- the halting round -/
def tEnd (D B : ℕ) : ℕ := phStart D B (phiOf B + 1)

/-- a time point: phase, link step, hop, slot, word -/
structure Tm where
  /-- phase -/
  i : ℕ
  /-- link step -/
  k : ℕ
  /-- hop -/
  h : ℕ
  /-- slot -/
  σ : ℕ
  /-- word -/
  t : ℕ

/-- the first round of hop `h` of link step `k` of phase `i` -/
def hopStart (D B i k h : ℕ) : ℕ := phStart D B i + k * stepLen D B i + h * hopLen B i

/-- the round of a time point -/
def rnd (D B : ℕ) (q : Tm) : ℕ := hopStart D B q.i q.k q.h + q.σ * 7 + q.t

/-- a valid time point -/
def Tm.Valid (D B : ℕ) (q : Tm) : Prop :=
  q.i ≤ phiOf B ∧ q.k < 2 ^ q.i ∧ q.h < 2 * D ∧ q.σ < slots B q.i ∧ q.t < 7

open Classical in
/-- the time point of a round (if any) -/
noncomputable def tq (D B s : ℕ) : Option Tm :=
  if h : ∃ q : Tm, q.Valid D B ∧ rnd D B q = s then some h.choose else none

lemma slots_pos (B i : ℕ) : 0 < slots B i := Nat.succ_pos _

lemma phStart_succ (D B i : ℕ) : phStart D B (i + 1) = phStart D B i + phLen D B i := rfl

lemma phStart_mono (D B : ℕ) {i i' : ℕ} (h : i ≤ i') : phStart D B i ≤ phStart D B i' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [phStart_succ]; omega)

/-- mixed radix: `k * A + r = k' * A + r'` with `r, r' < A` -/
lemma mixed_eq {A k k' r r' : ℕ} (h : k * A + r = k' * A + r') (hr : r < A) (hr' : r' < A) :
    k = k' ∧ r = r' := by
  have hA : 0 < A := by omega
  have h1 : (k * A + r) / A = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt hr, zero_add]
  have h2 : (k' * A + r') / A = k' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt hr', zero_add]
  have hk : k = k' := by rw [← h1, ← h2, h]
  subst hk
  exact ⟨rfl, by omega⟩

/-- the offset of a valid time point within its phase -/
lemma rnd_lt (D B : ℕ) {q : Tm} (hq : q.Valid D B) :
    phStart D B q.i ≤ rnd D B q ∧ rnd D B q < phStart D B (q.i + 1) := by
  obtain ⟨_, hk, hh, hσ, ht⟩ := hq
  have e1 : q.σ * 7 + q.t < hopLen B q.i := by unfold hopLen; nlinarith
  have e2 : q.h * hopLen B q.i + (q.σ * 7 + q.t) < stepLen D B q.i := by
    unfold stepLen
    have : (q.h + 1) * hopLen B q.i ≤ 2 * D * hopLen B q.i := Nat.mul_le_mul_right _ hh
    nlinarith
  have e3 : q.k * stepLen D B q.i + (q.h * hopLen B q.i + (q.σ * 7 + q.t)) < phLen D B q.i := by
    unfold phLen
    have : (q.k + 1) * stepLen D B q.i ≤ 2 ^ q.i * stepLen D B q.i := Nat.mul_le_mul_right _ hk
    nlinarith
  unfold rnd hopStart
  rw [phStart_succ]
  omega

/-- different valid time points have different rounds -/
lemma rnd_inj (D B : ℕ) {q q' : Tm} (hq : q.Valid D B) (hq' : q'.Valid D B)
    (h : rnd D B q = rnd D B q') : q = q' := by
  have hi : q.i = q'.i := by
    have a := rnd_lt D B hq
    have b := rnd_lt D B hq'
    rcases lt_trichotomy q.i q'.i with hlt | heq | hgt
    · have := phStart_mono D B (show q.i + 1 ≤ q'.i from hlt); omega
    · exact heq
    · have := phStart_mono D B (show q'.i + 1 ≤ q.i from hgt); omega
  obtain ⟨i, k, h1, σ, t⟩ := q
  obtain ⟨i', k', h1', σ', t'⟩ := q'
  simp only at hi
  subst hi
  obtain ⟨_, hk, hh, hσ, ht⟩ := hq
  obtain ⟨_, hk', hh', hσ', ht'⟩ := hq'
  simp only at hk hh hσ ht hk' hh' hσ' ht'
  unfold rnd hopStart at h
  simp only at h
  have hl1 : σ * 7 + t < hopLen B i := by unfold hopLen; nlinarith
  have hl1' : σ' * 7 + t' < hopLen B i := by unfold hopLen; nlinarith
  have hl2 : h1 * hopLen B i + (σ * 7 + t) < stepLen D B i := by
    unfold stepLen
    have : (h1 + 1) * hopLen B i ≤ 2 * D * hopLen B i := Nat.mul_le_mul_right _ hh
    nlinarith
  have hl2' : h1' * hopLen B i + (σ' * 7 + t') < stepLen D B i := by
    unfold stepLen
    have : (h1' + 1) * hopLen B i ≤ 2 * D * hopLen B i := Nat.mul_le_mul_right _ hh'
    nlinarith
  have e := mixed_eq (A := stepLen D B i) (k := k) (k' := k')
    (r := h1 * hopLen B i + (σ * 7 + t)) (r' := h1' * hopLen B i + (σ' * 7 + t'))
    (by omega) hl2 hl2'
  obtain ⟨rfl, e2⟩ := e
  obtain ⟨rfl, e3⟩ := mixed_eq e2 hl1 hl1'
  obtain ⟨rfl, rfl⟩ := mixed_eq e3 ht ht'
  rfl

lemma tq_rnd (D B : ℕ) {q : Tm} (hq : q.Valid D B) : tq D B (rnd D B q) = some q := by
  have hex : ∃ q' : Tm, q'.Valid D B ∧ rnd D B q' = rnd D B q := ⟨q, hq, rfl⟩
  unfold tq
  rw [dite_eq_left hex]
  congr 1
  exact rnd_inj D B hex.choose_spec.1 hq hex.choose_spec.2

lemma tq_some {D B s : ℕ} {q : Tm} (h : tq D B s = some q) : q.Valid D B ∧ rnd D B q = s := by
  unfold tq at h
  by_cases hex : ∃ q : Tm, q.Valid D B ∧ rnd D B q = s
  · rw [dite_eq_left hex] at h; cases h; exact hex.choose_spec
  · rw [dite_eq_right hex] at h; cases h

/-- rounds within a hop come before the next hop -/
lemma rnd_lt_hopStart (D B : ℕ) {q : Tm} (hq : q.Valid D B) :
    hopStart D B q.i q.k q.h ≤ rnd D B q ∧ rnd D B q < hopStart D B q.i q.k (q.h + 1) := by
  obtain ⟨_, _, _, hσ, ht⟩ := hq
  have : q.σ * 7 + q.t < hopLen B q.i := by unfold hopLen; nlinarith
  unfold rnd hopStart
  constructor
  · omega
  · rw [Nat.add_mul, one_mul]; omega

lemma hopStart_mono_h (D B i k : ℕ) {h h' : ℕ} (hh : h ≤ h') :
    hopStart D B i k h ≤ hopStart D B i k h' := by
  unfold hopStart
  have := Nat.mul_le_mul_right (hopLen B i) hh
  omega

/-- the end of a link step is the start of the next one -/
lemma hopStart_end (D B i k : ℕ) : hopStart D B i k (2 * D) = hopStart D B i (k + 1) 0 := by
  unfold hopStart stepLen
  ring

lemma hopStart_le_phStart (D B : ℕ) {i k h : ℕ} (hk : k < 2 ^ i) (hh : h ≤ 2 * D) :
    hopStart D B i k h ≤ phStart D B (i + 1) := by
  have h1 := hopStart_mono_h D B i k hh
  rw [hopStart_end] at h1
  have h2 : hopStart D B i (k + 1) 0 ≤ phStart D B (i + 1) := by
    unfold hopStart
    rw [phStart_succ]
    unfold phLen
    have := Nat.mul_le_mul_right (stepLen D B i) (show k + 1 ≤ 2 ^ i from hk)
    simp only [zero_mul, add_zero]
    omega
  omega

lemma phStart_le_hopStart (D B i k h : ℕ) : phStart D B i ≤ hopStart D B i k h := by
  unfold hopStart; omega

/-! ## Contexts -/

/-- the overlay index (public) -/
def rJ (c : NCtx V) : ℕ := c.pub.getD 0 0
/-- the size bound (public) -/
def rSz (c : NCtx V) : ℕ := c.pub.getD 1 0
/-- the dilation (public) -/
def rDil (c : NCtx V) : ℕ := c.pub.getD 2 0
/-- the overlap (public) -/
def rOv (c : NCtx V) : ℕ := c.pub.getD 3 0
/-- half the hops of a link step: `dil + 1` -/
def hD (c : NCtx V) : ℕ := rDil c + 1
/-- the public bound on the number of elements: `ov · min(sz, n)` -/
def bnd (c : NCtx V) : ℕ := rOv c * min (rSz c) (Fintype.card V)

/-! ## Local rules -/

open Classical in
/-- the key edge of the cluster of an own edge `e`: the key `k` of an own path whose cluster slice
contains `e` -/
noncomputable def keyL (c : NCtx V) (e : Sym2 V) : Sym2 V :=
  if h : ∃ k, (c.emb (rJ c) c.me k).isSome ∧ ∃ s ∈ c.sl, e ∈ s ∧ k ∈ s then h.choose else e

open Classical in
/-- the cluster of a hosted aggregator containing `e` -/
noncomputable def hostC (c : NCtx V) (e : Sym2 V) : Finset (Sym2 V) :=
  if h : ∃ C : Finset (Sym2 V), (c.view (.inr C)).isSome ∧ e ∈ C then h.choose else ∅

/-- the host turns a packet to the partner's path: the key edge of the partner in the cluster -/
noncomputable def turnL (c : NCtx V) (π : Pk V) : Pk V :=
  { π with key := (srcPort (hostC c π.e) π.w).2 }

/-- where the held packet `π` goes at hop `h` (`none`: it stays): up the departure node's path
at hops `h < D` (edge `h`), down the partner's path at hops `D ≤ h < 2 D` (edge `2 D - 1 - h`) -/
noncomputable def stepL (c : NCtx V) (h : ℕ) (π : Pk V) : Option V :=
  if h < hD c then ((c.emb (rJ c) π.v π.key).bind (fun P => P[h]?)).map (oth c.me)
  else ((c.emb (rJ c) π.w π.key).bind (fun P => P[2 * hD c - 1 - h]?)).map (oth c.me)

/-- the packet update entering hop `h`: turned at the host at hop `D` -/
noncomputable def adjL (c : NCtx V) (h : ℕ) (π : Pk V) : Pk V := if h = hD c then turnL c π else π

/-- the word sent to `v` in slot `σ`, word `t` of hop `h`, by a node holding `X` -/
noncomputable def sendFrom (c : NCtx V) (h σ t : ℕ) (X : Finset (Pk V)) (v : V) :
    Option (Word V) :=
  match atRank X σ with
  | some π => if stepL c h π = some v then some (pkWord π t) else none
  | none => none

/-- the packet of a probe with origin `a` departing from the own end `ix` (`none` if there is no
such end) -/
noncomputable def pkL (c : NCtx V) (rv : RingIn V) (a : V × ℕ) (ix : ℕ) : Option (Pk V) :=
  (rv[ix]?).map (fun t => ⟨a.1, a.2, c.me, t.1, t.2.2, t.2.1, keyL c t.1⟩)

omit [Fintype V] [DecidableEq V] in
lemma ite_some_eq {α : Type} {p : Prop} [Decidable p] {a b : α}
    (h : (if p then some a else none) = some b) : p ∧ a = b := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; exact ⟨hp, Option.some.inj h⟩
  · rw [ite_eq_right hp] at h; cases h

/-- the own end at which a packet arrives -/
def arrIdx (rv : RingIn V) (π : Pk V) : ℕ := rv.idxOf (π.e', π.v, π.e)

end RingLE
end APSP.Stoc.Congest
