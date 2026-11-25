import ApspStoc.Congest.RWLinkPkt
import ApspStoc.Congest.RWCouple

/-!
# The random-walk construction of `G₀`: the protocol

The protocol `rwProto Rf ℓ tf gf` (the algorithm `rwAlgC Rf ℓ tf gf`) is a seeded packet protocol
(`pktP`, `RWLinkPkt.lean`): one packet (`b = 5` words, numbers `< (n+4)^(Bw+1)` with
`Bw = log_{n+4}(R + 2ℓ + 2)`) per directed edge and macro-round. With `R = Rf n_C m_C` tokens per
port, `t = tf n_C m_C` slots per step and walk length `2ℓ` (all public), the macro-rounds are:

* **A** (`s < R`): every port `p = (v, e)` of `P` at `v` sends its token `(p, s)` over `e`
  (packet `tokMsg p s 0 e`: start port, index, path position `0`, edge).
* **B** (`bAt j k = R + j·t + k`, step `j < 2ℓ`, slot `k < t`): a node `y` holding the tokens
  `held j` before step `j` makes each token's lazy step with `lazyStepD` and its own seed
  `τ_y p i j`; the tokens crossing to a neighbour `u` (with their new path position `c + 1` and the
  crossed edge) are sent to `u`, the `k`-th one (in the order of `Finset.toList`) in slot `k`
  (`bSend`). Tokens beyond the `t`-th are not sent (overflow: the run is then a failure).
* **C** (`cAt j k`, reversed steps `j = 2ℓ-1, …, 0`): a node that knows the end port `q` of the
  (surviving) walk of the token it received from `u` in slot `(j, k)` of phase B returns the report
  `repMsg p i q` to `u` in the same slot (`cSend`). Initially the final node of a walk knows its end
  port if the walk survives: its last step entered through a port `(y, e) ∈ P` (`finRep`).
* **D** (`dRnd i = R + 4ℓt + i`): the reports for the first crossings return to the start nodes.

After `T = 2R + 4ℓt` macro-rounds every node outputs the public parameters `gf n_C m_C` and, for
every walk whose report it knows, ((start port, end port), its hops at the node) (`outMS`): the hop
records are the crossings it made or received (with their path positions), and its start ports.

All local computations are functions of a local environment `LEnv` (own ID, own cluster edges,
own ports, public parameters, own seeds) and of the oracle `H s u` = packet received from `u` in
macro-round `s`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Packets -/

/-- A token held by a node: (start port, index, path position of its last crossing, edge of its
last step if that step crossed). -/
abbrev Tok (V : Type) := Port V × ℕ × ℕ × Option (Sym2 V)

/-- A token in flight: (start port, index, path position of the crossing, crossed edge). -/
abbrev TokF (V : Type) := Port V × ℕ × ℕ × Sym2 V

/-- A report: (start port, index, end port). -/
abbrev Rep (V : Type) := Port V × ℕ × Port V

/-- The packet of a token in flight. -/
def tokMsg (z : TokF V) : Msg V := [.id z.1.1, .edge z.1.2, .num z.2.1, .num z.2.2.1, .edge z.2.2.2]

/-- Parsing a token packet. -/
def parseTok : Msg V → Option (TokF V)
  | [.id v, .edge e, .num i, .num c, .edge e'] => some ((v, e), i, c, e')
  | _ => none

/-- The packet of a report. -/
def repMsg (r : Rep V) : Msg V := [.id r.1.1, .edge r.1.2, .num r.2.1, .id r.2.2.1, .edge r.2.2.2]

/-- Parsing a report packet. -/
def parseRep : Msg V → Option (Rep V)
  | [.id v, .edge e, .num i, .id x, .edge e'] => some ((v, e), i, (x, e'))
  | _ => none

omit [Fintype V] [DecidableEq V] in
@[simp] lemma parseTok_tokMsg (z : TokF V) : parseTok (tokMsg z) = some z := by
  obtain ⟨⟨v, e⟩, i, c, e'⟩ := z; rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma parseRep_repMsg (r : Rep V) : parseRep (repMsg r) = some r := by
  obtain ⟨⟨v, e⟩, i, ⟨x, e'⟩⟩ := r; rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma parseRep_tokMsg (z : TokF V) : parseRep (tokMsg z) = none := by
  obtain ⟨⟨v, e⟩, i, c, e'⟩ := z; rfl

/-- A token in flight as a held token. -/
def asTok (z : TokF V) : Tok V := (z.1, z.2.1, z.2.2.1, some z.2.2.2)

/-! ## The local environment and the macro-round layout -/

/-- What a node knows: its ID, its cluster edges, its ports in `P`, the public parameters `R`
(tokens per port), `t` (slots per step), `ℓ` (half walk length), `Dmax` (seed range), and its
seeds `sd p i j` (for token `(p, i)` at step `j`). -/
structure LEnv (V : Type) where
  /-- own ID -/
  me : V
  /-- own cluster edges -/
  E : Finset (Sym2 V)
  /-- own ports in `P` -/
  ports : Finset (Port V)
  /-- tokens per port -/
  R : ℕ
  /-- slots per step -/
  t : ℕ
  /-- half walk length -/
  ℓ : ℕ
  /-- seed range -/
  Dmax : ℕ
  /-- own seeds -/
  sd : Port V → ℕ → ℕ → ℕ

/-- macro-round of slot `k` of step `j` (phase B) -/
def bAt (R t j k : ℕ) : ℕ := R + j * t + k

/-- macro-round of slot `k` of the reversed step `j` (phase C) -/
def cAt (R t ℓ j k : ℕ) : ℕ := R + 2 * ℓ * t + (2 * ℓ - 1 - j) * t + k

/-- macro-round of slot `i` of phase D -/
def dRnd (R t ℓ i : ℕ) : ℕ := R + 4 * ℓ * t + i

/-- the number of macro-rounds -/
def tEndRW (R t ℓ : ℕ) : ℕ := 2 * R + 4 * ℓ * t

/-! ## Local computations -/

section Local

variable (en : LEnv V) (H : ℕ → V → Option (Msg V))

/-- The lazy step of a held token at step `j` (own seed, own edges). -/
noncomputable def lst (x : Tok V) (j : ℕ) : V × Option (Sym2 V) :=
  lazyStepD en.Dmax en.E en.me (en.sd x.1 x.2.1 j)

/-- The token in flight to `u` produced by a lazy step `st` of token `x` (if it crosses to `u`). -/
def crossOf (st : V × Option (Sym2 V)) (x : Tok V) (u : V) : Option (TokF V) :=
  match st with
  | (u', some e) => if u' = u then some (x.1, x.2.1, x.2.2.1 + 1, e) else none
  | (_, none) => none

/-- The tokens of `S` crossing to `u` in step `j`. -/
noncomputable def crossTo (S : Finset (Tok V)) (j : ℕ) (u : V) : Finset (TokF V) :=
  S.biUnion (fun x => (crossOf (lst en x j) x u).toFinset)

/-- The tokens of `S` staying in step `j` (their last step did not cross). -/
noncomputable def stays (S : Finset (Tok V)) (j : ℕ) : Finset (Tok V) :=
  (S.filter (fun x => (lst en x j).2 = none)).image (fun x => (x.1, x.2.1, x.2.2.1, none))

/-- The tokens received in phase A. -/
def rcvA : Finset (Tok V) :=
  (range en.R).biUnion (fun s => univ.biUnion (fun u => (((H s u).bind parseTok).map asTok).toFinset))

/-- The tokens received in step `j` (phase B). -/
def rcvB (j : ℕ) : Finset (Tok V) :=
  (range en.t).biUnion (fun k => univ.biUnion (fun u =>
    (((H (bAt en.R en.t j k) u).bind parseTok).map asTok).toFinset))

/-- The tokens held before step `j`. -/
noncomputable def held : ℕ → Finset (Tok V)
  | 0 => rcvA en H
  | j + 1 => stays en (held j) j ∪ rcvB en H j

/-- The reports of the walks ending here and surviving: the last step entered through own port. -/
def finRep (S : Finset (Tok V)) : Finset (Rep V) :=
  S.biUnion (fun x => match x.2.2.2 with
    | some e => if (en.me, e) ∈ en.ports then {(x.1, x.2.1, (en.me, e))} else ∅
    | none => ∅)

/-- The reports received in the reversed step `j` (phase C). -/
def rcvC (j : ℕ) : Finset (Rep V) :=
  (range en.t).biUnion (fun k => univ.biUnion (fun u =>
    ((H (cAt en.R en.t en.ℓ j k) u).bind parseRep).toFinset))

/-- The reports known after `r` reversed steps (`2ℓ - 1, …, 2ℓ - r`). -/
noncomputable def known : ℕ → Finset (Rep V)
  | 0 => finRep en (held en H (2 * en.ℓ))
  | r + 1 => known r ∪ rcvC en H (2 * en.ℓ - 1 - r)

/-- The reports received in phase D. -/
def rcvD : Finset (Rep V) :=
  (range en.R).biUnion (fun i => univ.biUnion (fun u =>
    ((H (dRnd en.R en.t en.ℓ i) u).bind parseRep).toFinset))

/-- All reports known at the end. -/
noncomputable def knownF : Finset (Rep V) := known en H (2 * en.ℓ) ∪ rcvD en H

/-- The end port recorded in `K` for the walk `(p, i)`. -/
noncomputable def lookup (K : Finset (Rep V)) (p : Port V) (i : ℕ) : Option (Port V) :=
  ((K.filter (fun z => z.1 = p ∧ z.2.1 = i)).toList.head?).map (fun z => z.2.2)

/-- The report for the token in packet `m`, if its end port is recorded in `K`. -/
noncomputable def repFor (K : Finset (Rep V)) (m : Option (Msg V)) : Option (Msg V) :=
  match m.bind parseTok with
  | some z => (lookup K z.1 z.2.1).map (fun q => repMsg (z.1, z.2.1, q))
  | none => none

/-- Phase A: the token `(p, i)` of the own port `p` whose edge leads to `u`. -/
noncomputable def aSend (u : V) (i : ℕ) : Option (Msg V) :=
  ((en.ports.filter (fun p => otherEnd p.2 en.me = u)).toList.head?).map
    (fun p => tokMsg (p, i, 0, p.2))

/-- Phase B: the `k`-th token crossing to `u` in step `j`. -/
noncomputable def bSend (j k : ℕ) (u : V) : Option (Msg V) :=
  ((crossTo en (held en H j) j u).toList[k]?).map tokMsg

/-- Phase C: the report for the token received from `u` in slot `k` of step `j`. -/
noncomputable def cSend (j k : ℕ) (u : V) : Option (Msg V) :=
  repFor (known en H (2 * en.ℓ - 1 - j)) (H (bAt en.R en.t j k) u)

/-- Phase D: the report for the token received from `u` in slot `i` of phase A. -/
noncomputable def dSend (i : ℕ) (u : V) : Option (Msg V) :=
  repFor (known en H (2 * en.ℓ)) (H i u)

/-- The packet for `u` in macro-round `s`. -/
noncomputable def sendL (s : ℕ) (u : V) : Option (Msg V) :=
  if s < en.R then aSend en u s
  else if s < en.R + 2 * en.ℓ * en.t then bSend en H ((s - en.R) / en.t) ((s - en.R) % en.t) u
  else if s < en.R + 4 * en.ℓ * en.t then
    cSend en H (2 * en.ℓ - 1 - (s - en.R - 2 * en.ℓ * en.t) / en.t)
      ((s - en.R - 2 * en.ℓ * en.t) % en.t) u
  else if s < tEndRW en.R en.t en.ℓ then dSend en H (s - en.R - 4 * en.ℓ * en.t) u
  else none

/-- A hop record: (start port, index, trajectory entry, path position, edge). -/
abbrev HRec (V : Type) := Port V × ℕ × ℕ × ℕ × Sym2 V

/-- The hop records: (start port, index, trajectory entry, path position, edge) of the crossings
received here (entry `j`: the token held before step `j` arrived by its last step), made here
(entry `j + 1`: crossing in step `j`), and of the first crossings of the own ports (entry `0`). -/
noncomputable def recs : Finset (HRec V) :=
  (range (2 * en.ℓ + 1)).biUnion (fun j => (held en H j).biUnion (fun x => match x.2.2.2 with
      | some e => {(x.1, x.2.1, j, x.2.2.1, e)}
      | none => ∅)) ∪
  (range (2 * en.ℓ)).biUnion (fun j => univ.biUnion (fun u =>
    (crossTo en (held en H j) j u).image (fun z => (z.1, z.2.1, j + 1, z.2.2.1, z.2.2.2)))) ∪
  en.ports.biUnion (fun p => (range en.R).image (fun i => (p, i, 0, 0, p.2)))

/-- The hops of the walk `(p, i)` here (path position, edge), in the order of the trajectory. -/
noncomputable def hopsL (p : Port V) (i : ℕ) : List (ℕ × Sym2 V) :=
  (List.range (2 * en.ℓ + 1)).filterMap (fun j =>
    (((recs en H).filter (fun r => r.1 = p ∧ r.2.1 = i ∧ r.2.2.1 = j)).toList.head?).map
      (fun r => (r.2.2.2.1, r.2.2.2.2)))

/-- The local output: for every walk with a known report, ((start port, end port), hops here),
keeping the walks with hops here. -/
noncomputable def outMS : Multiset ((Port V × Port V) × List (ℕ × Sym2 V)) :=
  ((knownF en H).val.map (fun r => ((r.1, r.2.2), hopsL en H r.1 r.2.1))).filter
    (fun z => z.2 ≠ [])

end Local

/-! ## The protocol -/

/-- the own ports in `P`, read from the routing input (`∅` if absent) -/
noncomputable def myPortsOf (y : V) (inp : Agent V → Option Mem) : Finset (Port V) := by
  classical exact match inp (.inl y) with
  | some m => if h : m.1 = RIn V then (cast h m.2).1 else ∅
  | none => ∅

/-- the own cluster edges, read from the local view (edges of positive weight) -/
noncomputable def viewE (c : NCtx V) : Finset (Sym2 V) :=
  match c.view (.inl c.me) with
  | some vw => univ.filter (fun e => vw e ≠ 0)
  | none => ∅

/-- the seed of token `(p, i)` at step `j` in a node's table -/
def seedL {Rmax ℓ Dmax : ℕ} (τy : RWTable V Rmax ℓ Dmax) (p : Port V) (i j : ℕ) : ℕ :=
  if h : i < Rmax ∧ j < 2 * ℓ then (τy p ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `n_C` from the public numbers -/
def pubN (c : NCtx V) : ℕ := c.pub.getD 0 0

/-- `m_C` from the public numbers -/
def pubM (c : NCtx V) : ℕ := c.pub.getD 1 0

/-- The local environment of a node from its context, input and seed table. -/
noncomputable def envOf (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (c : NCtx V)
    (inp : Agent V → Option Mem)
    (τy : RWTable V (rwRmax Rf (Fintype.card V)) ℓ (rwDmax (Fintype.card V))) : LEnv V :=
  ⟨c.me, viewE c, myPortsOf c.me inp, Rf (pubN c) (pubM c), tf (pubN c) (pubM c), ℓ,
    rwDmax (Fintype.card V), fun p i j => seedL τy p i j⟩

/-- the digit parameter: numbers `< R + 2ℓ + 2 < (n+4)^(Bw+1)` -/
noncomputable def bwOf (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (c : NCtx V) : ℕ :=
  Nat.log (Fintype.card V + 4) (Rf (pubN c) (pubM c) + 2 * ℓ + 2)

/-- the number of macro-rounds -/
def tEndOf (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (c : NCtx V) : ℕ :=
  tEndRW (Rf (pubN c) (pubM c)) (tf (pubN c) (pubM c)) ℓ

/-- the seed table of a node -/
abbrev RWΩ (V : Type) [Fintype V] [DecidableEq V] (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) : Type :=
  RWTable V (rwRmax Rf (Fintype.card V)) ℓ (rwDmax (Fintype.card V))

instance (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) : Nonempty (RWΩ V Rf ℓ) :=
  ⟨fun _ _ _ => ⟨0, rwDmax_pos _⟩⟩

/-- **The random-walk protocol.** -/
noncomputable def rwProto (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data)
    (V : Type) [Fintype V] [DecidableEq V] : Proto V :=
  pktP (RWΩ V Rf ℓ) 5 (bwOf Rf ℓ) (tEndOf Rf ℓ tf)
    (fun c inp τy h v => sendL (envOf Rf ℓ tf c inp τy) (pget h) h.length v)
    (fun c inp τy h g => if g = .inl c.me then
      some ⟨G0K V, (gf (pubN c) (pubM c), outMS (envOf Rf ℓ tf c inp τy) (pget h))⟩ else none)

/-- **The random-walk algorithm** `rwAlgC Rf ℓ tf gf`. -/
noncomputable def rwAlgC (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data) :
    CAlg := fun V _ _ => rwProto Rf ℓ tf gf V

end APSP.Stoc.Congest
