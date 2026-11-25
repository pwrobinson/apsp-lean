import ApspStoc.Congest.AggUpDownWalk

/-!
# Store-and-forward along the embedded aggregator paths (core of `AggUpDown.lean`)

This file contains the part of the protocols of `aggUp` and `aggDown` that is common to both
directions: hop-synchronised store-and-forward of packets along the embedded aggregator paths of
overlay `j`, upwards (`d = false`: a packet `(u, C)` travels along `E.path j u C` from `u` to the
host of the aggregator of `C`) or downwards (`d = true`: along the reversed path, from the host to
`u`). A packet carries the value `val u C` (`none`: no packet).

## Schedule
Let `L = 1 + encLen Bw μ` (a header word `.id u`, then the encoded value), `B = sz * L` and
`T = E.dil * B`. Rounds `h * B, …, h * B + B - 1` form sub-phase `h < E.dil`, in which every packet
crosses the `h`-th edge of its walk; sub-phase `h` consists of `sz` slots of `L` rounds. The packets
crossing a directed edge `(a, b)` in sub-phase `h` have the sources `srcs a b h ⊆ S` (`|S| ≤ sz`);
the packet of `u` uses the slot `rkIn (srcs a b h) u` (rank of the source ID). `sfM` is this
explicit global schedule (the word from `a` to `b` in round `s`).

## Local rules (`sfSend`)
* In sub-phase `0` a node sends the packets it originates (`orig`, given per direction: the node's
  own value upwards, the values of the aggregators it hosts downwards).
* In sub-phase `h ≥ 1` a node `a` forwards every packet it received in sub-phase `h - 1`: a header
  `.id u` received from `y` identifies the walk, since `a` knows the paths of `u` through it
  (`emb`), and only the path of the cluster containing the edge `s(y, a)` crosses that edge at hop
  `h - 1` (`relOut`, `relWord`).
* At the end, the last node of a walk decodes the value from the stream received at the last hop
  (`rcv`).

## Proof
`sfSend_sched`: fed with the history of `sfM`, every participant sends exactly the words of
`sfM` (`relOut_eq`, `relWord_eq`: a relay reconstructs the packets of the schedule from the
headers it received, since a path known to it that crosses the edge of arrival is the walk of the
packet; `srcs_step`, `srcs_prev`). `rcv_sched`: at the end, the last vertex of a packet's walk
decodes its value (`dec_enc`), and finds nothing if the packet does not exist. The costs and the
success theorem `sf_succ` are in `AggUpDownCost.lean`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Definitions -/

/-- the walk of a path in direction `d` (`false`: as is, `true`: reversed) -/
def trB (d : Bool) (l : List (Sym2 V)) : List (Sym2 V) := if d then l.reverse else l

/-- the slot length: a header word and the encoded value -/
def sfL (Bw μ : ℕ) : ℕ := 1 + encLen Bw μ

/-- the word at position `r` of the packet of `u` with value `m` -/
def pword (n Bw : ℕ) (u : V) (m : Msg V) (r : ℕ) : Word V :=
  if r = 0 then .id u else encAt n Bw m (r - 1)

section Glob

variable (E : Overlays V) (j : ℕ) (d : Bool) (val : V → Finset (Sym2 V) → Option (Msg V))

/-- the walk of the packet `(u, C)` -/
def pkW (u : V) (C : Finset (Sym2 V)) : List (Sym2 V) := trB d (E.path j u C)

/-- the last vertex of the path of `u` in `C` (the host of the aggregator) -/
def pEnd (u : V) (C : Finset (Sym2 V)) : V := wv (E.path j u C) u (E.path j u C).length

/-- the first vertex of the walk of the packet `(u, C)` -/
def pkS (u : V) (C : Finset (Sym2 V)) : V := if d then pEnd E j u C else u

/-- the last vertex of the walk of the packet `(u, C)` -/
def pkE (u : V) (C : Finset (Sym2 V)) : V := if d then u else pEnd E j u C

/-- the packet `(u, C)` exists -/
def Act (u : V) (C : Finset (Sym2 V)) : Prop := C ∈ E.cl ∧ u ∈ nodes C ∧ (val u C).isSome

open Classical in
/-- the sources of the packets crossing the directed edge `(a, b)` at hop `h` -/
noncomputable def srcs (a b : V) (h : ℕ) : Finset V :=
  univ.filter (fun u => ∃ C, Act E val u C ∧ (pkW E j d u C)[h]? = some s(a, b) ∧
    wv (pkW E j d u C) (pkS E j d u C) h = a)

open Classical in
/-- the cluster containing the edge `e` -/
noncomputable def clOf (e : Sym2 V) : Finset (Sym2 V) :=
  if h : ∃ C ∈ E.cl, e ∈ C then h.choose else ∅

/-- the value carried by the packet of `u` over the edge `e` -/
noncomputable def pay (u : V) (e : Sym2 V) : Msg V := (val u (clOf E e)).getD []

/-- **The schedule**: the word from `a` to `b` in round `s`. -/
noncomputable def sfM (Bw μ sz : ℕ) (a b : V) (s : ℕ) : Option (Word V) :=
  if s < E.dil * (sz * sfL Bw μ) then
    (pickR (srcs E j d val a b (s / (sz * sfL Bw μ))) (s % (sz * sfL Bw μ) / sfL Bw μ)).map
      (fun u => pword (Fintype.card V) Bw u (pay E val u s(a, b))
        (s % (sz * sfL Bw μ) % sfL Bw μ))
  else none

end Glob

/-! ### Local rules -/

/-- the overlay index (public) -/
def jOf (c : NCtx V) : ℕ := c.pub.getD 0 0

/-- the dilation (public) -/
def dilOf (c : NCtx V) : ℕ := c.pub.getD 2 0

/-- the length of a sub-phase -/
def sfB (Bw μ : ℕ) (c : NCtx V) : ℕ := szOf c * sfL Bw μ

/-- the halting round -/
def sfT (Bw μ : ℕ) (c : NCtx V) : ℕ := dilOf c * sfB Bw μ c

/-- The relay condition at node `c.me`, hop `h ≥ 1`: in slot `q` of sub-phase `h - 1` the node
received the header `.id u` from `y`, and the walk of a path of `u` known to the node crosses
`s(y, me)` at hop `h - 1` and `s(me, b)` at hop `h`. -/
def RelC (Bw μ : ℕ) (d : Bool) (c : NCtx V) (H : ℕ → V → Option (Word V)) (h : ℕ) (b u y : V)
    (q : ℕ) : Prop :=
  q < szOf c ∧ H ((h - 1) * sfB Bw μ c + q * sfL Bw μ) y = some (.id u) ∧
    ∃ k l, c.emb (jOf c) u k = some l ∧ (trB d l)[h - 1]? = some s(y, c.me) ∧
      (trB d l)[h]? = some s(c.me, b)

open Classical in
/-- the sources of the packets that the node forwards to `b` at hop `h ≥ 1` -/
noncomputable def relOut (Bw μ : ℕ) (d : Bool) (c : NCtx V) (H : ℕ → V → Option (Word V))
    (h : ℕ) (b : V) : Finset V :=
  univ.filter (fun u => ∃ y q, RelC Bw μ d c H h b u y q)

open Classical in
/-- the word at position `r` of the packet of `u` forwarded to `b` at hop `h ≥ 1`: the word
received at the same position in sub-phase `h - 1` -/
noncomputable def relWord (Bw μ : ℕ) (d : Bool) (c : NCtx V) (H : ℕ → V → Option (Word V))
    (h : ℕ) (b u : V) (r : ℕ) : Option (Word V) :=
  if hx : ∃ y q, RelC Bw μ d c H h b u y q then
    H ((h - 1) * sfB Bw μ c + hx.choose_spec.choose * sfL Bw μ + r) hx.choose
  else none

/-- the packets originated by a node: `orig c inp b u` is the value of the packet with header `u`
that the node sends to `b` at hop `0` (`none`: no such packet) -/
abbrev Orig (V : Type) := NCtx V → (Agent V → Option Mem) → V → V → Option (Msg V)

open Classical in
/-- the sources of the packets sent to `b` at hop `h` -/
noncomputable def sfOut (Bw μ : ℕ) (d : Bool) (orig : Orig V) (c : NCtx V)
    (inp : Agent V → Option Mem) (H : ℕ → V → Option (Word V)) (h : ℕ) (b : V) : Finset V :=
  if h = 0 then univ.filter (fun u => (orig c inp b u).isSome) else relOut Bw μ d c H h b

/-- **The local rule**: the word sent to `b`, given the history. Round `s = h·B + q·L + r`: the
packet of rank `q` among those sent to `b` at hop `h`, at position `r`. -/
noncomputable def sfSend (Bw μ : ℕ) (d : Bool) (orig : Orig V) (c : NCtx V)
    (inp : Agent V → Option Mem) (hist : Hist V) (b : V) : Option (Word V) :=
  if hist.length < sfT Bw μ c then
    (pickR (sfOut Bw μ d orig c inp (hget hist) (hist.length / sfB Bw μ c) b)
      (hist.length % sfB Bw μ c / sfL Bw μ)).bind (fun u =>
      if hist.length % sfB Bw μ c % sfL Bw μ = 0 then some (.id u)
      else if hist.length / sfB Bw μ c = 0 then
        (orig c inp b u).map (fun m => encAt (Fintype.card V) Bw m
          (hist.length % sfB Bw μ c % sfL Bw μ - 1))
      else relWord Bw μ d c (hget hist) (hist.length / sfB Bw μ c) b u
        (hist.length % sfB Bw μ c % sfL Bw μ))
  else none

/-- the last edge of a walk (a dummy loop if empty) -/
def lastE (c : NCtx V) (w : List (Sym2 V)) : Sym2 V := w[w.length - 1]?.getD s(c.me, c.me)

open Classical in
/-- **Reception**: the value with header `u` received at the last hop of the walk `w` (from the
other endpoint of its last edge), decoded. -/
noncomputable def rcv (Bw μ : ℕ) (c : NCtx V) (H : ℕ → V → Option (Word V)) (u : V)
    (w : List (Sym2 V)) : Option (Msg V) :=
  if hq : ∃ q < szOf c, H ((w.length - 1) * sfB Bw μ c + q * sfL Bw μ) (oth (lastE c w) c.me) =
      some (.id u) then
    some (dec (Fintype.card V) Bw μ ((List.range (encLen Bw μ)).filterMap (fun i =>
      H ((w.length - 1) * sfB Bw μ c + hq.choose * sfL Bw μ + (1 + i)) (oth (lastE c w) c.me))))
  else none

/-- **The store-and-forward protocol** with origin rule `orig` and output rule `O`. -/
noncomputable def sfProto (Bw μ : ℕ) (d : Bool) (orig : Orig V)
    (O : NCtx V → (Agent V → Option Mem) → Hist V → Agent V → Option Mem) : Proto V :=
  histP (sfSend Bw μ d orig) (sfT Bw μ) O

/-! ## Facts about the packets -/

section Pk

variable {N : WNet V} {E : Overlays V} {j : ℕ} (d : Bool)
  {val : V → Finset (Sym2 V) → Option (Msg V)}

lemma trB_mem {l : List (Sym2 V)} {e : Sym2 V} : e ∈ trB d l ↔ e ∈ l := by
  unfold trB; split <;> simp

lemma length_trB (l : List (Sym2 V)) : (trB d l).length = l.length := by
  unfold trB; split <;> simp

lemma count_trB (l : List (Sym2 V)) (e : Sym2 V) : (trB d l).count e = l.count e := by
  unfold trB; split <;> simp

lemma trB_eq_nil {l : List (Sym2 V)} : trB d l = [] ↔ l = [] := by
  unfold trB; split <;> simp

variable (hE : EmbValid N.G E) (hj : j < Fintype.card V)
include hE hj

/-- The path of `u` in `C` is a walk from `u` to its end. -/
lemma path_walk {u : V} {C : Finset (Sym2 V)} (hC : C ∈ E.cl) (hu : u ∈ nodes C) :
    IsEdgeWalk (E.path j u C) u (pEnd E j u C) := by
  obtain ⟨h, -, hw⟩ := hE.walk j hj C hC
  have := hw u hu
  unfold pEnd
  rwa [walk_end _ u h this]

/-- The walk of a packet is an edge walk from its first to its last vertex. -/
lemma pk_walk {u : V} {C : Finset (Sym2 V)} (hC : C ∈ E.cl) (hu : u ∈ nodes C) :
    IsEdgeWalk (pkW E j d u C) (pkS E j d u C) (pkE E j d u C) := by
  have h := path_walk hE hj hC hu
  unfold pkW pkS pkE trB
  cases d
  · simpa using h
  · simpa using isEdgeWalk_reverse _ _ _ h

omit hj in
/-- The edges of a packet's walk are edges of its cluster. -/
lemma pk_edge {u : V} {C : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ pkW E j d u C) : e ∈ C :=
  hE.local_ j u C e ((trB_mem d).1 he)

omit hE in
/-- Paths have length at most the dilation. -/
lemma path_len {u : V} {C : Finset (Sym2 V)} (hC : C ∈ E.cl) :
    (E.path j u C).length ≤ E.dil := by
  unfold Overlays.dil
  refine le_trans ?_ (le_sup (f := fun j => univ.sup (fun v => E.cl.sup
    (fun C => (E.path j v C).length))) (mem_range.2 hj))
  refine le_trans ?_ (le_sup (f := fun v => E.cl.sup (fun C => (E.path j v C).length))
    (mem_univ u))
  exact le_sup (f := fun C => (E.path j u C).length) hC

omit hj in
/-- An edge lies in at most one cluster. -/
lemma clOf_eq {C : Finset (Sym2 V)} {e : Sym2 V} (hC : C ∈ E.cl) (he : e ∈ C) :
    clOf E e = C := by
  classical
  have hex : ∃ C ∈ E.cl, e ∈ C := ⟨C, hC, he⟩
  unfold clOf
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  by_contra hne
  exact disjoint_left.1 (hE.disj _ h1 C hC hne) h2 he

omit hj in
lemma clu_eq {C C' : Finset (Sym2 V)} {e : Sym2 V} (hC : C ∈ E.cl) (hC' : C' ∈ E.cl)
    (he : e ∈ C) (he' : e ∈ C') : C = C' := by
  rw [← clOf_eq hE hC he, clOf_eq hE hC' he']

/-- Every vertex of a packet's walk lies on the path, so it knows the path. -/
lemma pk_onWalk {u : V} {C : Finset (Sym2 V)} (hC : C ∈ E.cl) (hu : u ∈ nodes C) {i : ℕ}
    (hi : i ≤ (pkW E j d u C).length) : OnWalk (E.path j u C) u (wv (pkW E j d u C) (pkS E j d u C) i) := by
  by_cases hnil : E.path j u C = []
  · left
    have h1 : pkW E j d u C = [] := (trB_eq_nil d).2 hnil
    have h2 : pkS E j d u C = u := by
      unfold pkS pEnd; cases d <;> simp [hnil]
    rw [h1, h2]; cases i <;> rfl
  · right
    obtain ⟨e, he, hm⟩ := wv_mem_edge (pk_walk d hE hj hC hu) (by unfold pkW; rwa [ne_eq, trB_eq_nil]) hi
    exact ⟨e, (trB_mem d).1 he, hm⟩

lemma emb_pk {u : V} {C : Finset (Sym2 V)} (hC : C ∈ E.cl) (hu : u ∈ nodes C) {i : ℕ}
    (hi : i ≤ (pkW E j d u C).length) :
    ioEmb E (wv (pkW E j d u C) (pkS E j d u C) i) j u (srcPort C u).2 = some (E.path j u C) :=
  ioEmb_eq_some hE.disj hC hu (pk_onWalk d hE hj hC hu hi)

/-- The sources crossing an edge are in `S`. -/
lemma srcs_sub {S : Finset V} (hS : ∀ u C, Act E val u C → u ∈ S) (a b : V) (h : ℕ) :
    srcs E j d val a b h ⊆ S := by
  intro u hu
  simp only [srcs, mem_filter, mem_univ, true_and] at hu
  obtain ⟨C, hA, -⟩ := hu
  exact hS u C hA

end Pk

/-! ## The schedule -/

/-- What a node knows in the overlay instance: its ID, the public numbers, the paths through it. -/
structure CtxOK (E : Overlays V) (j sz : ℕ) (a : V) (c : NCtx V) : Prop where
  /-- the node's ID -/
  me : c.me = a
  /-- the overlay index -/
  j : jOf c = j
  /-- the size bound -/
  sz : szOf c = sz
  /-- the dilation -/
  dil : dilOf c = E.dil
  /-- the embedded paths through the node -/
  emb : c.emb = ioEmb E a

lemma ctxOK_ioInst (N : WNet V) (E : Overlays V) (j sz : ℕ) (Pt : Finset V) (a : V) :
    CtxOK E j sz a ((ioInst N E j sz Pt).ctx a) := ⟨rfl, rfl, rfl, rfl, rfl⟩

lemma sfL_pos (Bw μ : ℕ) : 0 < sfL Bw μ := by unfold sfL; omega

section Sched

variable {N : WNet V} {E : Overlays V} {j : ℕ} {d : Bool}
  {val : V → Finset (Sym2 V) → Option (Msg V)} {Bw μ sz : ℕ}

/-- The schedule at round `h·B + q·L + r`. -/
lemma sfM_slot (a b : V) {h q r : ℕ} (hh : h < E.dil) (hq : q < sz) (hr : r < sfL Bw μ) :
    sfM E j d val Bw μ sz a b (h * (sz * sfL Bw μ) + q * sfL Bw μ + r) =
      (pickR (srcs E j d val a b h) q).map
        (fun u => pword (Fintype.card V) Bw u (pay E val u s(a, b)) r) := by
  obtain ⟨h1, h2, h3⟩ := slot_decomp (h := h) hq hr
  have hlt : h * (sz * sfL Bw μ) + q * sfL Bw μ + r < E.dil * (sz * sfL Bw μ) := by
    have h4 : q * sfL Bw μ + r < sz * sfL Bw μ := by
      calc q * sfL Bw μ + r < q * sfL Bw μ + sfL Bw μ := by omega
        _ = (q + 1) * sfL Bw μ := by ring
        _ ≤ sz * sfL Bw μ := Nat.mul_le_mul_right _ hq
    calc h * (sz * sfL Bw μ) + q * sfL Bw μ + r < h * (sz * sfL Bw μ) + sz * sfL Bw μ := by
          omega
      _ = (h + 1) * (sz * sfL Bw μ) := by ring
      _ ≤ E.dil * (sz * sfL Bw μ) := Nat.mul_le_mul_right _ hh
  unfold sfM
  rw [ite_eq_left hlt, h1, h2, h3]

lemma sfM_of_lt (a b : V) {s : ℕ} (hs : s < E.dil * (sz * sfL Bw μ)) :
    sfM E j d val Bw μ sz a b s =
      (pickR (srcs E j d val a b (s / (sz * sfL Bw μ))) (s % (sz * sfL Bw μ) / sfL Bw μ)).map
        (fun u => pword (Fintype.card V) Bw u (pay E val u s(a, b))
          (s % (sz * sfL Bw μ) % sfL Bw μ)) := by
  unfold sfM; rw [ite_eq_left hs]

/-- The header word of slot `q` of sub-phase `h`. -/
lemma sfM_header (a b u : V) {h q : ℕ} (hh : h < E.dil) (hq : q < sz) :
    sfM E j d val Bw μ sz a b (h * (sz * sfL Bw μ) + q * sfL Bw μ) = some (.id u) ↔
      pickR (srcs E j d val a b h) q = some u := by
  have := sfM_slot (E := E) (j := j) (d := d) (val := val) a b hh hq (sfL_pos Bw μ)
  rw [add_zero] at this
  rw [this, Option.map_eq_some_iff]
  constructor
  · rintro ⟨w, hw, hw'⟩
    simp only [pword, ite_true] at hw'
    cases hw'; exact hw
  · intro h; exact ⟨u, h, by simp [pword]⟩

/-- A non-trivial word of the schedule belongs to a packet crossing the edge. -/
lemma sfM_isSome {a b : V} {s : ℕ} (h : (sfM E j d val Bw μ sz a b s).isSome) :
    s < E.dil * (sz * sfL Bw μ) ∧ ∃ u, pickR (srcs E j d val a b (s / (sz * sfL Bw μ)))
      (s % (sz * sfL Bw μ) / sfL Bw μ) = some u := by
  unfold sfM at h
  split_ifs at h with hs
  · refine ⟨hs, ?_⟩
    cases hp : pickR (srcs E j d val a b (s / (sz * sfL Bw μ))) (s % (sz * sfL Bw μ) / sfL Bw μ)
    · rw [hp] at h; simp at h
    · exact ⟨_, rfl⟩
  · simp at h

lemma sfM_wordOK {a b : V} {s : ℕ} {w : Word V} (h : sfM E j d val Bw μ sz a b s = some w) :
    WordOK (Fintype.card V) w := by
  unfold sfM at h
  split_ifs at h
  obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold pword
  split_ifs
  · trivial
  · exact encAt_ok _ _ _ _

variable (hE : EmbValid N.G E) (hj : j < Fintype.card V) {S : Finset V}
  (hS : ∀ u C, Act E val u C → u ∈ S) (hsz : S.card ≤ sz)
include hE hj

omit hj in
/-- A path known to a node shares an edge with an active packet's walk only if it is that walk. -/
lemma emb_walk_eq {a u : V} {k : Sym2 V} {l : List (Sym2 V)} (hl : ioEmb E a j u k = some l)
    {C : Finset (Sym2 V)} (hC : C ∈ E.cl) {e : Sym2 V} (he : e ∈ trB d l)
    (he' : e ∈ pkW E j d u C) : trB d l = pkW E j d u C := by
  obtain ⟨C', hC', -, -, -, rfl⟩ := ioEmb_spec hl
  have h1 : e ∈ C' := hE.local_ j u C' e ((trB_mem d).1 he)
  have h2 : e ∈ C := pk_edge d hE he'
  rw [clu_eq hE hC' hC h1 h2]; rfl

omit hj in
/-- The edges of a path known to a node lie in one cluster. -/
lemma emb_clOf {a u : V} {k : Sym2 V} {l : List (Sym2 V)} (hl : ioEmb E a j u k = some l)
    {e e' : Sym2 V} (he : e ∈ trB d l) (he' : e' ∈ trB d l) : clOf E e = clOf E e' := by
  obtain ⟨C', hC', -, -, -, rfl⟩ := ioEmb_spec hl
  rw [clOf_eq hE hC' (hE.local_ j u C' e ((trB_mem d).1 he)),
    clOf_eq hE hC' (hE.local_ j u C' e' ((trB_mem d).1 he'))]

/-- Packets crossing `(y, a)` at hop `h - 1` and then `(a, b)` at hop `h`. -/
lemma srcs_step {a b y u : V} {h : ℕ} (h1 : 1 ≤ h) (hy : u ∈ srcs E j d val y a (h - 1))
    {k : Sym2 V} {l : List (Sym2 V)} (hl : ioEmb E a j u k = some l)
    (hl1 : (trB d l)[h - 1]? = some s(y, a)) (hl2 : (trB d l)[h]? = some s(a, b)) :
    u ∈ srcs E j d val a b h := by
  classical
  simp only [srcs, mem_filter, mem_univ, true_and] at hy ⊢
  obtain ⟨C, hA, hW, hv⟩ := hy
  have heq := emb_walk_eq hE hl hA.1 (List.mem_of_getElem? hl1) (List.mem_of_getElem? hW)
  rw [heq] at hl1 hl2
  refine ⟨C, hA, hl2, ?_⟩
  have hlt : h - 1 < (pkW E j d u C).length := (List.getElem?_eq_some_iff.1 hW).1
  have hw := walk_get? (pk_walk d hE hj hA.1 hA.2.1) hlt
  rw [hW, hv, Nat.sub_add_cancel h1] at hw
  exact (Sym2.congr_right.1 (Option.some.inj hw)).symm

include hS hsz in
/-- Conversely, a packet crossing `(a, b)` at hop `h ≥ 1` crossed `(y, a)` at hop `h - 1`, for
the previous vertex `y` of its walk, in its slot there. -/
lemma srcs_prev {a b u : V} {h : ℕ} (h1 : 1 ≤ h) (hu : u ∈ srcs E j d val a b h) :
    ∃ y, u ∈ srcs E j d val y a (h - 1) ∧ rkIn (srcs E j d val y a (h - 1)) u < sz ∧
      ∃ k l, ioEmb E a j u k = some l ∧ (trB d l)[h - 1]? = some s(y, a) ∧
        (trB d l)[h]? = some s(a, b) := by
  classical
  have hu' := hu
  simp only [srcs, mem_filter, mem_univ, true_and] at hu'
  obtain ⟨C, hA, hW, hv⟩ := hu'
  have hlt : h < (pkW E j d u C).length := (List.getElem?_eq_some_iff.1 hW).1
  have hwk := pk_walk d hE hj hA.1 hA.2.1
  set y := wv (pkW E j d u C) (pkS E j d u C) (h - 1)
  have hW1 : (pkW E j d u C)[h - 1]? = some s(y, a) := by
    rw [walk_get? hwk (by omega), Nat.sub_add_cancel h1, hv]
  have hyS : u ∈ srcs E j d val y a (h - 1) := by
    simp only [srcs, mem_filter, mem_univ, true_and]
    exact ⟨C, hA, hW1, rfl⟩
  refine ⟨y, hyS, lt_of_lt_of_le (rkIn_lt hyS)
    ((card_le_card (srcs_sub d hE hj hS _ _ _)).trans hsz), (srcPort C u).2, E.path j u C, ?_,
    hW1, hW⟩
  have := emb_pk d hE hj hA.1 hA.2.1 hlt.le
  rwa [hv] at this

/-- the history of `a` after `s` rounds of the schedule -/
local notation "HS" a:max s:max => hget (schedHist (sfM E j d val Bw μ sz) a s)

/-- The relay condition, evaluated on the history of the schedule. -/
lemma relC_sched {a : V} {c : NCtx V} (hc : CtxOK E j sz a c) {h s : ℕ} (h1 : 1 ≤ h)
    (hh : h < E.dil) (hs : h * (sz * sfL Bw μ) ≤ s) (b u y : V) (q : ℕ) :
    RelC Bw μ d c (HS a s) h b u y q ↔ q < sz ∧
      pickR (srcs E j d val y a (h - 1)) q = some u ∧
      ∃ k l, ioEmb E a j u k = some l ∧ (trB d l)[h - 1]? = some s(y, a) ∧
        (trB d l)[h]? = some s(a, b) := by
  unfold RelC sfB
  rw [hc.sz, hc.me, hc.j, hc.emb]
  constructor
  · rintro ⟨hq, hH, hk⟩
    have hidx : (h - 1) * (sz * sfL Bw μ) + q * sfL Bw μ < s := by
      have : q * sfL Bw μ < sz * sfL Bw μ := Nat.mul_lt_mul_of_pos_right hq (sfL_pos Bw μ)
      have h2 : (h - 1) * (sz * sfL Bw μ) + sz * sfL Bw μ = h * (sz * sfL Bw μ) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h1]
      omega
    rw [hget_schedHist _ a hidx, sfM_header y a u (by omega) hq] at hH
    exact ⟨hq, hH, hk⟩
  · rintro ⟨hq, hp, hk⟩
    have hidx : (h - 1) * (sz * sfL Bw μ) + q * sfL Bw μ < s := by
      have : q * sfL Bw μ < sz * sfL Bw μ := Nat.mul_lt_mul_of_pos_right hq (sfL_pos Bw μ)
      have h2 : (h - 1) * (sz * sfL Bw μ) + sz * sfL Bw μ = h * (sz * sfL Bw μ) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h1]
      omega
    refine ⟨hq, ?_, hk⟩
    rw [hget_schedHist _ a hidx, sfM_header y a u (by omega) hq]
    exact hp

include hS hsz in
/-- **Relays**: on the history of the schedule, the packets a node forwards to `b` at hop `h ≥ 1`
are exactly those of the schedule. -/
lemma relOut_eq {a : V} {c : NCtx V} (hc : CtxOK E j sz a c) {h s : ℕ} (h1 : 1 ≤ h)
    (hh : h < E.dil) (hs : h * (sz * sfL Bw μ) ≤ s) (b : V) :
    relOut Bw μ d c (HS a s) h b = srcs E j d val a b h := by
  classical
  ext u
  simp only [relOut, mem_filter, mem_univ, true_and]
  simp only [relC_sched hE hj hc h1 hh hs]
  constructor
  · rintro ⟨y, q, -, hp, k, l, hl, hl1, hl2⟩
    exact srcs_step hE hj h1 (mem_of_pickR hp) hl hl1 hl2
  · intro hu
    obtain ⟨y, hy, hq, hk⟩ := srcs_prev hE hj hS hsz h1 hu
    exact ⟨y, _, hq, pickR_rkIn hy, hk⟩

include hS hsz in
/-- **Relays**: the forwarded words are those of the schedule. -/
lemma relWord_eq {a : V} {c : NCtx V} (hc : CtxOK E j sz a c) {h s : ℕ} (h1 : 1 ≤ h)
    (hh : h < E.dil) (hs : h * (sz * sfL Bw μ) ≤ s) {b u : V}
    (hu : u ∈ srcs E j d val a b h) {r : ℕ} (hr1 : r ≠ 0) (hr : r < sfL Bw μ) :
    relWord Bw μ d c (HS a s) h b u r =
      some (encAt (Fintype.card V) Bw (pay E val u s(a, b)) (r - 1)) := by
  classical
  have hex : ∃ y q, RelC Bw μ d c (HS a s) h b u y q := by
    obtain ⟨y, hy, hq, hk⟩ := srcs_prev hE hj hS hsz h1 hu
    exact ⟨y, _, (relC_sched hE hj hc h1 hh hs b u y _).2 ⟨hq, pickR_rkIn hy, hk⟩⟩
  unfold relWord
  rw [dite_eq_left hex]
  obtain ⟨hq, hp, k, l, hl, hl1, hl2⟩ :=
    (relC_sched hE hj hc h1 hh hs b u _ _).1 hex.choose_spec.choose_spec
  set y := hex.choose
  set q := hex.choose_spec.choose
  unfold sfB
  rw [hc.sz]
  have hidx : (h - 1) * (sz * sfL Bw μ) + q * sfL Bw μ + r < s := by
    have : q * sfL Bw μ + r < sz * sfL Bw μ := by
      calc q * sfL Bw μ + r < q * sfL Bw μ + sfL Bw μ := by omega
        _ = (q + 1) * sfL Bw μ := by ring
        _ ≤ sz * sfL Bw μ := Nat.mul_le_mul_right _ hq
    have h2 : (h - 1) * (sz * sfL Bw μ) + sz * sfL Bw μ = h * (sz * sfL Bw μ) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h1]
    omega
  rw [hget_schedHist _ a hidx, sfM_slot y a (by omega) hq hr, hp]
  simp only [Option.map_some, pword, ite_eq_right hr1]
  unfold pay
  rw [emb_clOf hE hl (List.mem_of_getElem? hl1) (List.mem_of_getElem? hl2)]

include hS hsz in
/-- **The protocol follows the schedule**: fed with the history of the schedule, a participant
whose origin rule produces the packets of the schedule at hop `0` sends exactly the words of the
schedule. -/
lemma sfSend_sched (orig : Orig V) {a : V} {c : NCtx V} (hc : CtxOK E j sz a c)
    {inp : Agent V → Option Mem}
    (horig : ∀ b u, orig c inp b u =
      if u ∈ srcs E j d val a b 0 then some (pay E val u s(a, b)) else none)
    {s : ℕ} (hs : s < E.dil * (sz * sfL Bw μ)) (b : V) :
    sfSend Bw μ d orig c inp (schedHist (sfM E j d val Bw μ sz) a s) b =
      sfM E j d val Bw μ sz a b s := by
  classical
  have hB : sfB Bw μ c = sz * sfL Bw μ := by unfold sfB; rw [hc.sz]
  have hT : sfT Bw μ c = E.dil * (sz * sfL Bw μ) := by unfold sfT; rw [hc.dil, hB]
  have hBpos : 0 < sz * sfL Bw μ := by
    rcases Nat.eq_zero_or_pos (sz * sfL Bw μ) with h0 | h0
    · rw [h0, mul_zero] at hs; omega
    · exact h0
  have hhd : s / (sz * sfL Bw μ) < E.dil := by
    rw [Nat.div_lt_iff_lt_mul hBpos]; exact hs
  have hsB : s / (sz * sfL Bw μ) * (sz * sfL Bw μ) ≤ s := Nat.div_mul_le_self _ _
  have hr : s % (sz * sfL Bw μ) % sfL Bw μ < sfL Bw μ := Nat.mod_lt _ (sfL_pos Bw μ)
  unfold sfSend
  rw [length_schedHist, hT, hB, ite_eq_left hs, sfM_of_lt a b hs]
  have hout : sfOut Bw μ d orig c inp (HS a s) (s / (sz * sfL Bw μ)) b =
      srcs E j d val a b (s / (sz * sfL Bw μ)) := by
    unfold sfOut
    split_ifs with h0
    · ext u
      rw [mem_filter, horig, h0]
      split_ifs with hu <;> simp [hu]
    · exact relOut_eq hE hj hS hsz hc (Nat.pos_of_ne_zero h0) hhd hsB b
  rw [hout]
  cases hp : pickR (srcs E j d val a b (s / (sz * sfL Bw μ))) (s % (sz * sfL Bw μ) / sfL Bw μ) with
  | none => rfl
  | some u =>
    have hu := mem_of_pickR hp
    simp only [Option.bind_some, Option.map_some]
    by_cases hr0 : s % (sz * sfL Bw μ) % sfL Bw μ = 0
    · rw [ite_eq_left hr0, hr0]; rfl
    · rw [ite_eq_right hr0]
      by_cases h0 : s / (sz * sfL Bw μ) = 0
      · rw [ite_eq_left h0, horig, ite_eq_left (h0 ▸ hu)]
        simp only [Option.map_some, pword, ite_eq_right hr0]
      · rw [ite_eq_right h0, relWord_eq hE hj hS hsz hc (Nat.pos_of_ne_zero h0) hhd hsB hu hr0 hr]
        simp only [pword, ite_eq_right hr0]

include hS hsz in
/-- **Reception**: at the end, the last vertex of a packet's walk (non-empty) decodes the value of
the packet from the history of the schedule; if the packet does not exist, it finds nothing. -/
lemma rcv_sched {u : V} {C : Finset (Sym2 V)} (hC : C ∈ E.cl) (hu : u ∈ nodes C)
    (hne : E.path j u C ≠ []) {a : V} (ha : pkE E j d u C = a) {c : NCtx V}
    (hc : CtxOK E j sz a c) (henc : ∀ m, val u C = some m → EncOK (Fintype.card V) Bw μ m)
    {s : ℕ} (hs : E.dil * (sz * sfL Bw μ) ≤ s) :
    rcv Bw μ c (HS a s) u (pkW E j d u C) = val u C := by
  classical
  have hwk := pk_walk d hE hj hC hu
  have hlen : 1 ≤ (pkW E j d u C).length := by
    rw [pkW, length_trB]; exact List.length_pos_iff.2 hne
  have hlend : (pkW E j d u C).length ≤ E.dil := by rw [pkW, length_trB]; exact path_len hj hC
  obtain ⟨g, hg⟩ : ∃ g, g = (pkW E j d u C).length - 1 := ⟨_, rfl⟩
  set y := wv (pkW E j d u C) (pkS E j d u C) g
  have hlast : (pkW E j d u C)[g]? = some s(y, a) := by
    rw [walk_get? hwk (by omega), show g + 1 = (pkW E j d u C).length by omega,
      walk_end _ _ _ hwk, ha]
  have hlE : lastE c (pkW E j d u C) = s(y, a) := by unfold lastE; rw [← hg, hlast]; rfl
  have hoth : oth (lastE c (pkW E j d u C)) c.me = y := by rw [hlE, hc.me, oth_mk']
  have hgd : g < E.dil := by omega
  unfold rcv sfB
  rw [hoth, hc.sz, ← hg]
  have hidx : ∀ q < sz, ∀ r < sfL Bw μ, g * (sz * sfL Bw μ) + q * sfL Bw μ + r < s := by
    intro q hq r hr
    have : q * sfL Bw μ + r < sz * sfL Bw μ := by
      calc q * sfL Bw μ + r < q * sfL Bw μ + sfL Bw μ := by omega
        _ = (q + 1) * sfL Bw μ := by ring
        _ ≤ sz * sfL Bw μ := Nat.mul_le_mul_right _ hq
    have h2 : (g + 1) * (sz * sfL Bw μ) ≤ E.dil * (sz * sfL Bw μ) := Nat.mul_le_mul_right _ hgd
    have h3 : (g + 1) * (sz * sfL Bw μ) = g * (sz * sfL Bw μ) + sz * sfL Bw μ := by ring
    omega
  have hhead : ∀ q < sz, hget (schedHist (sfM E j d val Bw μ sz) a s)
      (g * (sz * sfL Bw μ) + q * sfL Bw μ) y = some (.id u) ↔
      pickR (srcs E j d val y a g) q = some u := by
    intro q hq
    have := hidx q hq 0 (sfL_pos Bw μ)
    rw [add_zero] at this
    rw [hget_schedHist _ a this, sfM_header y a u hgd hq]
  cases hv : val u C with
  | none =>
    rw [dite_eq_right]
    rintro ⟨q, hq, hH⟩
    have hm := mem_of_pickR ((hhead q hq).1 hH)
    simp only [srcs, mem_filter, mem_univ, true_and] at hm
    obtain ⟨C1, hA1, hW1, -⟩ := hm
    have h1 : s(y, a) ∈ C1 := pk_edge d hE (List.mem_of_getElem? hW1)
    have h2 : s(y, a) ∈ C := pk_edge d hE (List.mem_of_getElem? hlast)
    have h3 := hA1.2.2
    rw [clu_eq hE hA1.1 hC h1 h2, hv] at h3
    simp at h3
  | some m =>
    have hA : Act E val u C := ⟨hC, hu, by simp [hv]⟩
    have hyS : u ∈ srcs E j d val y a g := by
      simp only [srcs, mem_filter, mem_univ, true_and]
      exact ⟨C, hA, hlast, rfl⟩
    have hrk : rkIn (srcs E j d val y a g) u < sz :=
      lt_of_lt_of_le (rkIn_lt hyS) ((card_le_card (srcs_sub d hE hj hS _ _ _)).trans hsz)
    have hex : ∃ q < sz, hget (schedHist (sfM E j d val Bw μ sz) a s)
        (g * (sz * sfL Bw μ) + q * sfL Bw μ) y = some (.id u) :=
      ⟨_, hrk, (hhead _ hrk).2 (pickR_rkIn hyS)⟩
    rw [dite_eq_left hex]
    obtain ⟨hq, hH⟩ := hex.choose_spec
    have hp := (hhead _ hq).1 hH
    have hpay : pay E val u s(y, a) = m := by
      unfold pay
      rw [clOf_eq hE hC (pk_edge d hE (List.mem_of_getElem? hlast)), hv]; rfl
    have hlist : (List.range (encLen Bw μ)).filterMap (fun i =>
        hget (schedHist (sfM E j d val Bw μ sz) a s)
          (g * (sz * sfL Bw μ) + hex.choose * sfL Bw μ + (1 + i)) y) =
        enc (Fintype.card V) Bw μ m := by
      unfold enc
      rw [← List.filterMap_eq_map]
      apply List.filterMap_congr
      intro i hi
      rw [List.mem_range] at hi
      have hi' : 1 + i < sfL Bw μ := by unfold sfL; omega
      rw [hget_schedHist _ a (hidx _ hq _ hi'), sfM_slot y a hgd hq hi', hp]
      simp only [Option.map_some, pword, ite_eq_right (show 1 + i ≠ 0 by omega), Function.comp_apply,
        hpay, Nat.add_sub_cancel_left]
    rw [hlist, dec_enc _ _ _ _ (henc m hv).1 (henc m hv).2]

end Sched

end APSP.Stoc.Congest
