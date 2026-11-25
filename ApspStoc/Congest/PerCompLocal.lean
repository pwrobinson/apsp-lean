import ApspStoc.Congest.PerCompSeg
import ApspStoc.Congest.PerCompPath
import ApspStoc.Congest.PerCompFrame

/-!
# The controller of the component traversal (for `perCompR`)

The *logical controller* `pcCtl A Bt` of the traversal (frames of three words, `PerCompFrame`).
A node knows (from the preparation phases) whether it is in `P` and in `S`, its parents and roots
in the spanning tree of `P` and in the spanning forest of `G[S]`, the size `|K|` of its component,
and its children in both. Messages:
* the token: `(0, 0, 0)`;
* a phase broadcast `(1, c, 0)`: `c = |K|` for the phase of component `K`, `c = 0` for the final
  phase (the end);
* an announcement packet `(x, c, ℓ)`: source `x`, `c` as above, leader `ℓ` of the phase.

A *phase* with size parameter `L` (`|K|`, or `sz` for the final phase) and period
`Π = (dil + 1)·L` starts at the frame `A0`, a multiple of `Π`: the broadcast on the tree in frames
`[A0, A0 + L)`, the announcements in frames `[A0 + Π, A0 + Π + dil·L)` (sub-phase `h` in frames
`A0 + Π + h·L + slot`), and the sub-run of `B` (or the end) at frame `A0 + 2Π`. Every node of the
footprint can compute `A0` from the frame of any broadcast or packet it receives
(`Π * (ψ / Π)`, resp. minus `Π`), because these frames lie in one period.

* `tokAct`: the token (the depth-first traversal, `PerCompSeg`): after receiving it from the
  parent (the root: at frame `1`), a leader starts its phase, another node sends it to its first
  child; after receiving it back from child `c`, a node sends it to the next child; after its
  phase (the first frame after the sub-run of `B`), a leader sends it to its first child; when there
  is no further child, the token goes back to the parent, or, at the root, the final phase starts.
* `pcKnown`: the phases known to the node, one candidate (`cand`) per frame: from its own start, from
  a broadcast, or from a packet.
* `lsend`: token, broadcast (the start of an own phase, or forwarding a broadcast received in the
  previous frame), packets (`pkFor`: sub-phase `h`, slot `s`; the packets of sub-phase `h` are
  computed by `pkLoc` from the packets received in sub-phase `h - 1`).
* `lstart`: start `B` at frame `A0 + 2Π` of a known phase with `c ≠ 0`, with public size bound
  `c = |K|` and membership flag `x ∈ K` (`memQ`); `lhalt`: halt at frame `A0 + 2Π` of the final
  phase.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

/-- the smallest multiple of `Π` that is at least `x` -/
def alignUp (x q : ℕ) : ℕ := q * ((x + q - 1) / q)

/-- the period of a phase with size parameter `L` -/
def PiL (dil L : ℕ) : ℕ := (dil + 1) * L

/-- the size parameter of a phase with content `c` -/
def Lof (sz c : ℕ) : ℕ := if c = 0 then sz else c

section Words
variable {V : Type}

/-- the token -/
def tokW : W3 V := (.num 0, .num 0, .num 0)
/-- a phase broadcast -/
def bcW (c : ℕ) : W3 V := (.num 1, .num c, .num 0)
/-- an announcement packet -/
def pcPkW (x : V) (c : ℕ) (l : V) : W3 V := (.id x, .num c, .id l)

/-- the packet of slot `i` of the packets `s` of a directed edge -/
noncomputable def slotMsg (s : Finset V) (i c : ℕ) (l : V) : Option (W3 V) :=
  (s.toList[i]?).map (fun x => pcPkW x c l)

end Words

/-- The local data of a node after the preparation. -/
structure LD (V : Type) where
  bP : Bool
  bS : Bool
  parP : Option V
  parS : Option V
  rtP : V
  rtS : V
  cnt : ℕ
  kP : Finset V
  kS : Finset V

/-- A phase known to a node: start frame `A0`, size parameter `L`, content `c`, leader `l`, and
whether the node is a source of the phase. -/
structure LPh (V : Type) where
  A0 : ℕ
  L : ℕ
  c : ℕ
  l : V
  q : Bool
  deriving DecidableEq

/-- token actions -/
inductive TA (V : Type) where
  | send (w : V)
  | startK
  | startE
  | idle
  deriving DecidableEq

section Local

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the data received from `u` in frame `ψ` -/
def recvAt (H : LH V) (ψ : ℕ) (u : V) : Option (W3 V) :=
  match H.getD ψ none with
  | some m => m u
  | none => none

/-- the sender of a token received in frame `ψ` -/
noncomputable def tokS (H : LH V) (ψ : ℕ) : Option V :=
  (univ.filter (fun u => recvAt H ψ u = some tokW)).toList.head?

/-- the content of a broadcast `(1, c, _)` -/
def bcOf : Option (W3 V) → Option ℕ
  | some (.num 1, .num c, _) => some c
  | _ => none

/-- the content and leader of a packet `(x, c, ℓ)` -/
def pkOf : Option (W3 V) → Option (ℕ × V)
  | some (.id _, .num c, .id l) => some (c, l)
  | _ => none

/-- the source of a packet -/
def idOf : Option (W3 V) → Option V
  | some (.id x, _, _) => some x
  | _ => none

/-- the content of a broadcast received in frame `ψ` -/
noncomputable def bcR (H : LH V) (ψ : ℕ) : Option ℕ :=
  (univ.toList.filterMap (fun u => bcOf (recvAt H ψ u))).head?

/-- the content and leader of a packet received in frame `ψ` -/
noncomputable def pkR (H : LH V) (ψ : ℕ) : Option (ℕ × V) :=
  (univ.toList.filterMap (fun u => pkOf (recvAt H ψ u))).head?

/-- the token came from the parent in frame `ψ` (the root: virtually, in frame `0`) -/
def fromPar (d : LD V) (H : LH V) (ψ : ℕ) : Prop :=
  (ψ = 0 ∧ d.bP = true ∧ d.parP = none) ∨ (d.bP = true ∧ d.parP ≠ none ∧ tokS H ψ = d.parP)

/-- the node is a leader (the root of its tree in the forest of `S`) -/
def isLd (d : LD V) : Prop := d.bS = true ∧ d.parS = none

/-- back to the parent, or the end at the root -/
def upT (d : LD V) : TA V :=
  match d.parP with
  | some p => .send p
  | none => .startE

/-- after the token came from the parent (or after the phase) -/
noncomputable def aPar (d : LD V) : TA V :=
  match d.kP.toList.head? with
  | some c => .send c
  | none => upT d

/-- after the token came back from child `c` -/
noncomputable def aKid (d : LD V) (c : V) : TA V :=
  match nextIn d.kP.toList c with
  | some c' => .send c'
  | none => upT d

/-- the frame at which `B` starts in a phase started in frame `a` with size parameter `L` -/
def phBL (dil a L : ℕ) : ℕ := alignUp a (PiL dil L) + 2 * PiL dil L

open Classical in
/-- **The token action** in frame `H.length`. -/
noncomputable def tokAct (dil : ℕ) (d : LD V) (H : LH V) : TA V :=
  if 1 ≤ H.length ∧ fromPar d H (H.length - 1) then (if isLd d then .startK else aPar d)
  else match (if 1 ≤ H.length then tokS H (H.length - 1) else none) with
    | some c => if c ∈ d.kP then aKid d c else .idle
    | none => if isLd d ∧ ∃ ψ < H.length, fromPar d H ψ ∧ phBL dil (ψ + 1) d.cnt ≤ H.length ∧
        ∀ χ, phBL dil (ψ + 1) d.cnt ≤ χ → χ < H.length → H.getD χ none = none then aPar d
      else .idle

/-- the public numbers of the context -/
def jC (c : NCtx V) : ℕ := c.pub.getD 0 0
/-- the public size bound -/
def szC (c : NCtx V) : ℕ := c.pub.getD 1 0
/-- the public dilation -/
def dilC (c : NCtx V) : ℕ := c.pub.getD 2 0

/-- is the node a source of the phase with content `c` and leader `l`? -/
def memQ (d : LD V) (c : ℕ) (l : V) : Bool := if c = 0 then d.bP else (d.bS && decide (d.rtS = l))

open Classical in
/-- the phase learnt in frame `ψ` -/
noncomputable def cand (c : NCtx V) (d : LD V) (H : LH V) (ψ : ℕ) : Option (LPh V) :=
  ((if isLd d ∧ 1 ≤ ψ ∧ ψ ≤ H.length ∧ fromPar d H (ψ - 1) then
      some ⟨alignUp ψ (PiL (dilC c) d.cnt), d.cnt, d.cnt, c.me, true⟩ else none) <|>
    (if d.bP = true ∧ d.parP = none ∧ ψ ≤ H.length ∧ tokAct (dilC c) d (H.take ψ) = .startE ∧
        (ψ < H.length → H.getD ψ none ≠ none) then
      some ⟨alignUp ψ (PiL (dilC c) (szC c)), szC c, 0, c.me, true⟩ else none)) <|>
  ((if ψ < H.length then (bcR H ψ).map (fun cc =>
      ⟨PiL (dilC c) (Lof (szC c) cc) * (ψ / PiL (dilC c) (Lof (szC c) cc)), Lof (szC c) cc, cc,
        if cc = 0 then d.rtP else d.rtS, true⟩) else none) <|>
    (if ψ < H.length then (pkR H ψ).map (fun t =>
      ⟨PiL (dilC c) (Lof (szC c) t.1) * (ψ / PiL (dilC c) (Lof (szC c) t.1)) -
        PiL (dilC c) (Lof (szC c) t.1), Lof (szC c) t.1, t.1, t.2, memQ d t.1 t.2⟩) else none))

/-- the phases known in frame `H.length` -/
noncomputable def pcKnown (c : NCtx V) (d : LD V) (H : LH V) : List (LPh V) :=
  (List.range (H.length + 1)).filterMap (cand c d H)

/-- `w` is a child in the tree of a phase with content `c` -/
def chOf (d : LD V) (c : ℕ) (w : V) : Prop := if c = 0 then w ∈ d.kP else w ∈ d.kS

open Classical in
/-- the packets to `w` in sub-phase `h` of the known phase `X` -/
noncomputable def pkLoc (c : NCtx V) (H : LH V) (X : LPh V) (h : ℕ) (w : V) : Finset V :=
  if h = 0 then
    (if X.q = true ∧ ∃ k l e, c.emb (jC c) c.me k = some l ∧ l[0]? = some e ∧ pcOth e c.me = w
      then {c.me} else ∅)
  else univ.filter (fun x => ∃ y, (∃ s < X.L,
      idOf (recvAt H (X.A0 + PiL (dilC c) X.L + (h - 1) * X.L + s) y) = some x) ∧
    ∃ k l e, c.emb (jC c) x k = some l ∧ l[h - 1]? = some s(y, c.me) ∧ l[h]? = some e ∧
      pcOth e c.me = w)

/-- the packet to `w` in frame `H.length` for the known phase `X` -/
noncomputable def pkFor (c : NCtx V) (H : LH V) (X : LPh V) (w : V) : Option (W3 V) :=
  if X.A0 + PiL (dilC c) X.L ≤ H.length ∧
      H.length < X.A0 + PiL (dilC c) X.L + dilC c * X.L then
    slotMsg (pkLoc c H X ((H.length - X.A0 - PiL (dilC c) X.L) / X.L) w)
      ((H.length - X.A0 - PiL (dilC c) X.L) % X.L) X.c X.l
  else none

/-- the token part of the messages of a node in frame `H.length` -/
noncomputable def pcTokMsg (dil : ℕ) (d : LD V) (H : LH V) (w : V) : Option (W3 V) :=
  match tokAct dil d H with
  | .send w' => if w = w' then some tokW else none
  | _ => none

open Classical in
/-- the broadcast part of the messages of a node in frame `H.length`: the start of an own phase,
or forwarding a broadcast received in the previous frame -/
noncomputable def bcMsg (c : NCtx V) (d : LD V) (H : LH V) (w : V) : Option (W3 V) :=
  match (pcKnown c d H).find? (fun X => decide (X.l = c.me ∧ X.A0 = H.length)) with
  | some X => if chOf d X.c w then some (bcW X.c) else none
  | none => match (if 1 ≤ H.length then bcR H (H.length - 1) else none) with
    | some cc => if chOf d cc w then some (bcW cc) else none
    | none => none

/-- the packet part of the messages of a node in frame `H.length` -/
noncomputable def pkMsg (c : NCtx V) (d : LD V) (H : LH V) (w : V) : Option (W3 V) :=
  ((pcKnown c d H).filterMap (fun X => pkFor c H X w)).head?

/-- **The messages** of a node in frame `H.length`. -/
noncomputable def lsend (c : NCtx V) (d : LD V) (H : LH V) (w : V) : Option (W3 V) :=
  (pcTokMsg (dilC c) d H w <|> bcMsg c d H w) <|> pkMsg c d H w

/-- the context of a sub-run with public size bound `cc` -/
def ctxK (c : NCtx V) (cc : ℕ) : NCtx V :=
  ⟨c.me, c.view, [c.pub.getD 0 0, cc, c.pub.getD 2 0, c.pub.getD 3 0], c.emb, c.sl⟩

/-- the data of the agents of a node after the preparation -/
abbrev X5 (A : Type → Type) (V : Type) : Type :=
  (((((((Bool × Bool) × A V) × (Option V × V)) × (Option V × V)) × Option (Msg V)) × Finset V) ×
    Finset V)

open Classical in
/-- the input of a sub-run: the membership flag and the data -/
noncomputable def inpK (A : Type → Type) (inp : Agent V → Option Mem) (q : Bool) : Agent V → Option Mem :=
  fun g => (inp g).map (fun m => if h : m.1 = X5 A V then
    ⟨Bool × A V, ((match g with | .inl _ => q | .inr _ => false), (cast h m.2).1.1.1.1.1.2)⟩
    else m)

/-- the number in a one-word value -/
def numW : Option (Msg V) → ℕ
  | some (Word.num k :: _) => k
  | _ => 0

/-- the local data from the data of the own agent -/
def ldOf {A : Type → Type} (x : X5 A V) : LD V :=
  ⟨x.1.1.1.1.1.1.1, x.1.1.1.1.1.1.2, x.1.1.1.1.2.1, x.1.1.1.2.1, x.1.1.1.1.2.2,
    x.1.1.1.2.2, numW x.1.1.2, x.1.2, x.2⟩

open Classical in
/-- the local data of a node -/
noncomputable def myD (A : Type → Type) (inp : Agent V → Option Mem) (me : V) : LD V :=
  match inp (.inl me) with
  | some m => if h : m.1 = X5 A V then ldOf (cast h m.2) else ⟨false, false, none, none, me, me,
      0, ∅, ∅⟩
  | none => ⟨false, false, none, none, me, me, 0, ∅, ∅⟩

open Classical in
/-- **Start of a sub-run** at frame `A0 + 2Π` of a known phase of a component. -/
noncomputable def lstart (A : Type → Type) (c : NCtx V) (inp : Agent V → Option Mem) (d : LD V)
    (H : LH V) : Option (NCtx V × (Agent V → Option Mem) × Bool) :=
  match (pcKnown c d H).find?
      (fun X => decide (X.c ≠ 0 ∧ X.A0 + 2 * PiL (dilC c) X.L = H.length)) with
  | some X => some (ctxK c X.c, inpK A inp X.q, X.q)
  | none => none

open Classical in
/-- **Halting** at frame `A0 + 2Π` of the final phase. -/
noncomputable def lhalt (c : NCtx V) (d : LD V) (H : LH V) : Bool :=
  (pcKnown c d H).any (fun X => decide (X.c = 0 ∧ X.A0 + 2 * PiL (dilC c) X.L = H.length))

open Classical in
/-- a default value of the output type -/
noncomputable def dfltM (Bt : Type → Type) (V : Type) : Mem :=
  if h : Nonempty (Bt V) then ⟨Bt V, Classical.choice h⟩ else ⟨Unit, ()⟩

open Classical in
/-- the final outputs: the output of the own sub-run for a node of `S`, a default value
otherwise -/
noncomputable def pcOut (A Bt : Type → Type) (c : NCtx V) (inp : Agent V → Option Mem)
    (res : Option (Agent V → Option Mem)) (g : Agent V) : Option Mem :=
  some (if g = .inl c.me ∧ (myD A inp c.me).bS = true then
    ((res.bind (fun o => o g)).getD (dfltM Bt V)) else dfltM Bt V)

/-- **The logical controller of the traversal.** -/
noncomputable def pcCtl (A Bt : Type → Type) (V : Type) [Fintype V] [DecidableEq V] : LCtl V where
  send c inp H w := lsend c (myD A inp c.me) H w
  start c inp H := lstart A c inp (myD A inp c.me) H
  halt c inp H := lhalt c (myD A inp c.me) H
  out := pcOut A Bt

end Local

end APSP.Stoc.Congest
