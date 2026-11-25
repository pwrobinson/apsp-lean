import ApspStoc.Congest.RingLEGlobal

/-!
# Ring orientation in CONGEST: the protocol (`ringLE_congest`, part 3)

The protocol `ringProto` is a full-information protocol (`histP`): a node keeps its context, its
ring data `rv` (its input) and the history `H` of the words it received, and recomputes from them
(`lHeld`) which probe packets it holds at the current hop:

* `lRecv`: the packets received during a hop (decoded from the `7` words of every slot and
  neighbour);
* `lHeldFrom`: the packets held at hop `h + 1` are those held at hop `h` that do not move, and the
  received ones, updated by `adjL` (the host turns them to the partner's path at hop `D`);
* `dep0`: in the first link step of a phase, both ends of every *active candidate* send their own
  probe; `depF`: in the next link steps, a probe that arrived at an own end is forwarded from the
  paired end if the phase's hop budget is not spent and the arrival end is not the originator's
  (the local rule `forward_iff` of `RingComb`);
* `lPhase`: the packets arriving at the end of each link step; `lSt`: the status (candidate,
  decided) of the node's elements: a candidate stays one iff no probe with a larger ID arrived in
  the phase, and is decided once its own probe returned;
* `sendL`: in slot `σ`, word `t` of a hop, the node sends the word `t` of its held packet of rank
  `σ` to the node it moves to;
* `outL`: at the end, every own end outputs the direction induced by the largest probe that
  crossed it (`bestDir`, departure = out for an even start, arrival = out for an odd start).

All nodes halt at the public round `tEnd (dil + 1) (ov · min(sz, n))`.
-/

namespace APSP.Stoc.Congest
namespace RingLE

open APSP Finset APSP.Stoc.RingComb

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

section Local

variable (c : NCtx V) (rv : RingIn V) (H : ℕ → V → Option (Word V))

/-- the packets received during hop `h` of link step `k` of phase `i` -/
noncomputable def lRecv (i k h : ℕ) : Finset (Pk V) :=
  (univ ×ˢ range (slots (bnd c) i)).biUnion
    (fun p => (pkDec (fun t => H (rnd (hD c) (bnd c) ⟨i, k, h, p.2, t⟩) p.1)).toFinset)

/-- the packets held at hop `h` of link step `k` of phase `i`, from the departing packets `X0` -/
noncomputable def lHeldFrom (i k : ℕ) (X0 : Finset (Pk V)) : ℕ → Finset (Pk V)
  | 0 => X0
  | h + 1 => (((lHeldFrom i k X0 h).filter (fun π => stepL c h π = none)) ∪ lRecv c H i k h).image
      (adjL c (h + 1))

/-- the departing packets of the first link step of a phase: the own probes of both ends of every
active candidate (status `st`: (candidate, decided)) -/
noncomputable def dep0 (st : ℕ → Bool × Bool) : Finset (Pk V) :=
  ((range rv.length).filter (fun ix => (st (ix / 2)).1 = true ∧ (st (ix / 2)).2 = false)).biUnion
    (fun ix => (pkL c rv (c.me, ix) ix).toFinset)

/-- the forwarding condition of an arrived packet at link step `k` of phase `i` -/
def FwdOK (i k : ℕ) (π : Pk V) : Prop :=
  k + 1 < 2 ^ i ∧ (c.me, arrIdx rv π / 2) ≠ (π.o, π.oi / 2)

open Classical in
/-- the departing packets of link step `k + 1`: the forwarded arrivals `X` of link step `k` -/
noncomputable def depF (i k : ℕ) (X : Finset (Pk V)) : Finset (Pk V) :=
  (X.filter (FwdOK c rv i k)).biUnion (fun π => (pkL c rv π.orig (pairIdx (arrIdx rv π))).toFinset)

/-- the packets arriving at the end of link step `k` of phase `i`, with the status `st` -/
noncomputable def lPhase (i : ℕ) (st : ℕ → Bool × Bool) : ℕ → Finset (Pk V)
  | 0 => lHeldFrom c H i 0 (dep0 c rv st) (2 * hD c)
  | k + 1 => lHeldFrom c H i (k + 1) (depF c rv i k (lPhase i st k)) (2 * hD c)

/-- a probe with a larger ID arrived at the element `m` in phase `i` -/
def BigArr (i : ℕ) (arr : ℕ → Finset (Pk V)) (m : ℕ) : Prop :=
  ∃ k < 2 ^ i, ∃ π ∈ arr k, arrIdx rv π / 2 = m ∧ eid (c.me, m) < eid (π.o, π.oi / 2)

/-- the own probe of the element `m` returned in phase `i` -/
def OwnArr (i : ℕ) (arr : ℕ → Finset (Pk V)) (m : ℕ) : Prop :=
  ∃ k < 2 ^ i, ∃ π ∈ arr k, arrIdx rv π / 2 = m ∧ (π.o, π.oi / 2) = (c.me, m)

open Classical in
/-- the status update at the end of phase `i` -/
noncomputable def updSt (i : ℕ) (st : ℕ → Bool × Bool) (arr : ℕ → Finset (Pk V)) :
    ℕ → Bool × Bool :=
  fun m => ((st m).1 && !decide (BigArr c rv i arr m), (st m).2 || decide (OwnArr c rv i arr m))

/-- the status (candidate, decided) of the elements at the start of phase `i` -/
noncomputable def lSt : ℕ → ℕ → Bool × Bool
  | 0 => fun _ => (true, false)
  | i + 1 => updSt c rv i (lSt i) (lPhase c rv H i (lSt i))

/-- the departing packets of link step `k` of phase `i` -/
noncomputable def lDep (i : ℕ) : ℕ → Finset (Pk V)
  | 0 => dep0 c rv (lSt c rv H i)
  | k + 1 => depF c rv i k (lPhase c rv H i (lSt c rv H i) k)

/-- the packets held at hop `h` of link step `k` of phase `i` -/
noncomputable def lHeld (i k h : ℕ) : Finset (Pk V) := lHeldFrom c H i k (lDep c rv H i k) h

lemma lPhase_eq (i k : ℕ) :
    lPhase c rv H i (lSt c rv H i) k = lHeld c rv H i k (2 * hD c) := by
  cases k <;> rfl

/-- the message to `v` in round `s` -/
noncomputable def sendL (s : ℕ) (v : V) : Option (Word V) :=
  match tq (hD c) (bnd c) s with
  | some q => sendFrom c q.h q.σ q.t (lHeld c rv H q.i q.k q.h) v
  | none => none

/-- the own end from which a packet departs -/
def depIdx (π : Pk V) : ℕ := rv.idxOf (π.e, π.w, π.e')

open Classical in
/-- the crossing events of the own end `ix`: (origin of the probe, departure?) -/
noncomputable def lEv (ix : ℕ) : Finset ((V × ℕ) × Bool) :=
  (range (phiOf (bnd c) + 1)).biUnion (fun i => (range (2 ^ i)).biUnion (fun k =>
    ((lDep c rv H i k).filter (fun π => depIdx rv π = ix)).image (fun π => (π.orig, true)) ∪
    ((lPhase c rv H i (lSt c rv H i) k).filter (fun π => arrIdx rv π = ix)).image
      (fun π => (π.orig, false))))

end Local

/-- the direction induced by a crossing event: a departure is `out` for an even start, an arrival
is `out` for an odd start -/
def evDir (p : (V × ℕ) × Bool) : Bool :=
  if p.2 then decide (p.1.2 % 2 = 0) else decide (p.1.2 % 2 = 1)

/-- the direction induced by the event of the largest probe -/
noncomputable def bestDir (X : Finset ((V × ℕ) × Bool)) : Bool :=
  if h : X.Nonempty then evDir (Classical.choose (X.exists_max_image (fun p => eid (elemOf p.1)) h))
  else false

/-- the output: the direction of every own end -/
noncomputable def outL (c : NCtx V) (rv : RingIn V) (H : ℕ → V → Option (Word V)) : List Bool :=
  (List.range rv.length).map (fun ix => bestDir (lEv c rv H ix))

open Classical in
/-- the node's ring data, read from its input -/
noncomputable def myRing (inp : Agent V → Option Mem) (me : V) : RingIn V :=
  match inp (.inl me) with
  | some m => if h : m.1 = RingIn V then cast h m.2 else []
  | none => []

/-- **The ring orientation protocol** (a full-information protocol). -/
noncomputable def ringProto (V : Type) [Fintype V] [DecidableEq V] : Proto V :=
  histP (fun c inp h v => sendL c (myRing inp c.me) (hget h) h.length v)
    (fun c => tEnd (hD c) (bnd c))
    (fun c inp h g => some ⟨List Bool,
      if g = .inl c.me then outL c (myRing inp c.me) (hget h) else []⟩)

/-- the algorithm (it does not use `ν`) -/
noncomputable def ringAlg (_ν : ℕ) : CAlg := fun V _ _ => ringProto V

end RingLE
end APSP.Stoc.Congest
