import ApspStoc.Congest.EmbConstructBase

/-!
# Definitions of the protocol of `embedConstruct` (`EmbConstruct.lean`)

This file only contains definitions; the proofs are in `EmbConstructLocal.lean` (local
computability of the routing inputs, the per-cluster pipeline), `EmbConstructBfs.lean` (the BFS
tree), `EmbConstructPar.lean` (the parallel composition with termination detection) and
`EmbConstructOut.lean` (the final output).

## Local data (Lemmas 3.8 and 3.9 inputs)
After the cluster setup, a node `v` of a cluster `C` knows its slice `C ∩ inc(v)` (and the
weights of its edges, from its view), the (ID, degree) table `tabOf C` and the ports `portsA C`
of the aggregator set. The choices made in `Base/Demands.lean` (`aggSet`, `srcSet`, `srcAssign`,
`srcPort`, `portAssign`) are `Classical.choose`/`epsilon` of predicates that only depend on this
data, so they are functions of it (`aggSetT`, `srcSetL`, `balL`, `srcPortL`, `portAssignL`);
`dstAssign` is canonical and local by construction (`dstAssignL`, `dstAssign_local` in
`Base/Demands.lean`). Hence `v` can compute its routing inputs `rin2L` (topology packets with
payloads `[edge e] ++ digits of w(e)`) and `rin3L` (dummy packets).

## The per-cluster pipeline `pipeP`
`A₁` (setup); `A₂` with the context of `clInst N C` and the inputs `rin2L` (`ctxP g2`); `A₃`
likewise (`ctxP g3`); finally `skipP` keeps all the data: the output is
`((((), setup output), topology knowledge), route knowledge)` (`PipeOut`).

## The main phase `mainP`
Every node runs one copy of a protocol `P` per own cluster slice (seed: the slice's component
of the node's seed), and a termination detection on a spanning tree (from the BFS phase):
* a copy at `v` sends to `u` only if the edge `vu` is in its slice, and only while it runs; the
  messages over an edge are delivered to the copy of the edge's cluster while it runs at the
  receiver, and otherwise recorded in the *tree history* `th`;
* when all own copies have halted (round `D_v`, recorded in `dt`) and all children have
  reported, a node streams its report to its parent (`L = 2 Dg` words: the `Dg` base-`(n+4)`
  digits of the maximum of the first and of the second local values over its subtree);
* the root then streams the global report to its children; every node forwards what it
  receives from its parent `L` rounds later (`tSend`);
* a node of depth `d` that starts its broadcast in round `B` halts in round `B + L·(n - d)`
  (`tHalt`), which is the same round at all nodes, and outputs `finF` of its copies' final states
  and the global values (`gVal`).
-/

namespace APSP.Stoc.Congest

namespace EmbC

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Data of the phases -/

/-- output of the BFS phase at a node: depth, parent, children -/
abbrev BfsOut (V : Type) := ℕ × Option V × Finset V

/-- input of the main phase at a node: the task's input and the BFS output -/
abbrev MIn (V : Type) := (Unit × DState V) × BfsOut V

/-- the node's cluster slices, read from its input -/
noncomputable def mSl (inp : Agent V → Option Mem) (me : V) : Finset (Finset (Sym2 V)) :=
  match rdIn (MIn V) inp me with
  | some a => a.1.2.2
  | none => ∅

/-- the node's depth in the BFS tree -/
noncomputable def mDep (inp : Agent V → Option Mem) (me : V) : ℕ :=
  match rdIn (MIn V) inp me with
  | some a => a.2.1
  | none => 0

/-- the node's parent in the BFS tree -/
noncomputable def mPar (inp : Agent V → Option Mem) (me : V) : Option V :=
  match rdIn (MIn V) inp me with
  | some a => a.2.2.1
  | none => none

/-- the node's children in the BFS tree -/
noncomputable def mKids (inp : Agent V → Option Mem) (me : V) : Finset V :=
  match rdIn (MIn V) inp me with
  | some a => a.2.2.2
  | none => ∅

/-! ## Local data of a cluster after the setup -/

/-- the degree of `u` in a table of (ID, degree) pairs -/
def degT (tab : Finset (V × ℕ)) (u : V) : ℕ := ∑ x ∈ tab.filter (fun x => x.1 = u), x.2

/-- the nodes of a table -/
def nodesT (tab : Finset (V × ℕ)) : Finset V := tab.image Prod.fst

/-- the number of edges: half the total degree -/
def mT (tab : Finset (V × ℕ)) : ℕ := (∑ x ∈ tab, x.2) / 2

/-- the (ID, degree) table of a cluster (output of the setup) -/
def tabOf (C : Finset (Sym2 V)) : Finset (V × ℕ) := (nodes C).image (fun u => (u, degIn C u))

/-- the aggregator set, computed from the table -/
noncomputable def aggSetT (tab : Finset (V × ℕ)) : Finset V :=
  Classical.epsilon (fun A => IsAggSet (nodesT tab) A (degT tab))

/-- the number of source ports (`kPorts`), computed from the table -/
noncomputable def kPortsT (tab : Finset (V × ℕ)) (v : V) : ℕ :=
  if v ∈ aggSetT tab then degT tab v
  else min (degT tab v) (cdiv (degT tab v * tab.card) (mT tab))

/-- the ports of `v` given its slice -/
def portsSl (v : V) (sl : Finset (Sym2 V)) : Finset (Port V) := sl.image (fun e => (v, e))

/-- the source ports `srcSet` as a function of the node's ports and their number -/
noncomputable def srcSetL (Pv : Finset (Port V)) (k : ℕ) : Finset (Port V) := by
  classical exact if h : ∃ T, T ⊆ Pv ∧ T.card = k then Classical.choose h else ∅

/-- the balanced assignment of `Base/Demands.lean` (`exists_balanced`) as a function of its data -/
noncomputable def balL {β γ : Type} [DecidableEq β] [DecidableEq γ] (X : Finset β) (Y : Finset γ)
    (d : β → γ) : β → γ :=
  if h : Y.Nonempty then Classical.choose (exists_balanced X Y h) else d

/-- the designated port `srcPort` as a function of the node's slice -/
noncomputable def srcPortL (v : V) (sl : Finset (Sym2 V)) : Port V := by
  classical exact if h : ∃ e, e ∈ sl then (v, h.choose) else (v, s(v, v))

/-- the port assignment of the overlays `portAssign` as a function of `portsA C` (default port at
`v` if empty) -/
noncomputable def portAssignL (v : V) (pa : Finset (Port V)) (j : ℕ) : Port V :=
  if h : pa.Nonempty then Classical.choose (exists_balanced (range (Fintype.card V)) pa h) j
  else (v, s(v, v))

/-! ## Routing inputs -/

/-- the payload of a topology packet: the edge and the `wexp + 1` base-`(n + 4)` digits of its
weight -/
def topoPay (n wexp w : ℕ) (e : Sym2 V) : Msg V := .edge e :: digW (n + 4) (wexp + 1) w

/-- the topology packets of Lemma 3.8 with their payloads -/
noncomputable def pl2 (N : WNet V) (wexp : ℕ) (C : Finset (Sym2 V)) : Multiset (PktP V) :=
  (allPorts C ×ˢ aggSet C).val.map (fun x => ((srcAssign C x.1.1 x, dstAssign C x.2 x.1),
    topoPay (Fintype.card V) wexp (N.w x.1.2) x.1.2))

/-- the dummy packets of Lemma 3.9 (empty payloads) -/
noncomputable def pl3 (C : Finset (Sym2 V)) : Multiset (PktP V) :=
  (nodes C ×ˢ portsA C).val.map (fun x => ((srcPort C x.1, x.2), ([] : Msg V)))

/-- the topology packets of `v`, computed from its slice `sl`, the table, `portsA` and the weights
`vw` of its edges -/
noncomputable def pl2L (wexp : ℕ) (v : V) (sl : Finset (Sym2 V)) (tab : Finset (V × ℕ))
    (pa : Finset (Port V)) (vw : Sym2 V → ℕ) : Multiset (PktP V) :=
  (portsSl v sl ×ˢ aggSetT tab).val.map (fun x =>
    ((balL (portsSl v sl ×ˢ aggSetT tab) (srcSetL (portsSl v sl) (kPortsT tab v))
        (fun _ => (v, s(v, v))) x,
      dstAssignL (degT tab) sl (pa.filter (fun p => p.1 = x.2)) x.1),
     topoPay (Fintype.card V) wexp (vw x.1.2) x.1.2))

/-- the input of `A₂` at `v`, computed locally -/
noncomputable def rin2L (wexp : ℕ) (v : V) (sl : Finset (Sym2 V))
    (tab : Finset (V × ℕ)) (pa : Finset (Port V)) (vw : Sym2 V → ℕ) : RIn V :=
  (pa.filter (fun p => p.1 = v) ∪ srcSetL (portsSl v sl) (kPortsT tab v),
    pl2L wexp v sl tab pa vw, 6 * tab.card)

/-- the input of `A₃` at `v`, computed locally -/
noncomputable def rin3L (v : V) (sl : Finset (Sym2 V)) (tab : Finset (V × ℕ))
    (pa : Finset (Port V)) : RIn V :=
  (pa.filter (fun p => p.1 = v) ∪ {srcPortL v sl},
    pa.val.map (fun q => ((srcPortL v sl, q), ([] : Msg V))), 3 * tab.card)

/-! ## The per-cluster pipeline -/

/-- the weights of the own edges, from the context's view -/
noncomputable def ownVw (c : NCtx V) : Sym2 V → ℕ := (c.view (.inl c.me)).getD (fun _ => 0)

/-- the own edges (non-zero weight in the view) -/
noncomputable def ownSl (c : NCtx V) : Finset (Sym2 V) := by
  classical exact univ.filter (fun e => ownVw c e ≠ 0)

open Classical in
/-- context and data of `A₂`: public `[n_C, m_C]` and the topology packets -/
noncomputable def g2 (wexp : ℕ) (c : NCtx V) (inp : Agent V → Option Mem) :
    NCtx V × (Agent V → Option Mem) :=
  match rdIn (Unit × SetupOut V) inp c.me with
  | some a => ({ c with pub := [a.2.2.2.1.card, mT a.2.2.2.1] }, fun g =>
      if g = .inl c.me then some ⟨RIn V, rin2L wexp c.me (ownSl c) a.2.2.2.1 a.2.2.2.2 (ownVw c)⟩
      else none)
  | none => (c, fun _ => none)

open Classical in
/-- context and data of `A₃`: public `[n_C, m_C]` and the dummy packets -/
noncomputable def g3 (c : NCtx V) (inp : Agent V → Option Mem) : NCtx V × (Agent V → Option Mem) :=
  match rdIn ((Unit × SetupOut V) × RK V) inp c.me with
  | some a => ({ c with pub := [a.1.2.2.2.1.card, mT a.1.2.2.2.1] }, fun g =>
      if g = .inl c.me then some ⟨RIn V, rin3L c.me (ownSl c) a.1.2.2.2.1 a.1.2.2.2.2⟩
      else none)
  | none => (c, fun _ => none)

/-- **The per-cluster pipeline**: setup, topology collection, dummy routing; the output keeps all
the data. -/
noncomputable def pipeP (wexp : ℕ) (A₁ A₂ A₃ : Proto V) : Proto V :=
  seqP A₁ (seqP (ctxP (g2 wexp) A₂) (seqP (ctxP g3 A₃) skipP))

/-- the output of the pipeline at a node -/
abbrev PipeOut (V : Type) := ((Unit × SetupOut V) × RK V) × RK V

/-- Specification of the pipeline in cluster `C`: the setup output, and the knowledge after the
topology collection and after the dummy routing (whose routes satisfy `GR`). -/
def PipeSpec (N : WNet V) (wexp : ℕ) (C : Finset (Sym2 V)) (GR : Routes V → Prop)
    (z : Agent V → PipeOut V) : Prop :=
  ∃ (ℓ : V) (par : V → Option V) (r₂ r₃ : Routes V), GR r₃ ∧ ∀ v ∈ nodes C,
    z (.inl v) = ((((), (ℓ, par v, tabOf C, portsA C)),
      rkAt r₂ (topoDemand C) (pl2 N wexp C) (.inl v)), rkAt r₃ (portsDemand C) (pl3 C) (.inl v))

/-! ## The main phase -/

open Classical in
/-- the context of the copy of slice `s` (that of `clInst0 N C` for the cluster `C` of `s`) -/
noncomputable def cctx (c : NCtx V) (s : Finset (Sym2 V)) : NCtx V :=
  ⟨c.me, fun g => if g = .inl c.me then
      some (fun e => if e ∈ s then (c.view (.inl c.me)).getD (fun _ => 0) e else 0) else none,
    [], fun _ _ _ => none, ∅⟩

open Classical in
/-- the data of a copy (that of `clInst0 N C` with input `()`) -/
noncomputable def cinp (c : NCtx V) : Agent V → Option Mem :=
  fun g => if g = .inl c.me then some ⟨Unit, ()⟩ else none

/-- the state of the main phase at a node -/
structure MainS (V : Type) (P : Proto V) : Type 1 where
  /-- the node's context -/
  c : NCtx V
  /-- the node's data -/
  inp : Agent V → Option Mem
  /-- the states of the cluster copies, keyed by the slices (only the own slices are used) -/
  cp : Finset (Sym2 V) → P.S
  /-- the round in which all own copies were first found halted -/
  dt : Option ℕ
  /-- the tree history: per round, the words received over edges whose copy does not run -/
  th : Hist V

/-- the copy of the slice of the edge to `u` runs -/
def runSl (P : Proto V) (st : MainS V P) (u : V) : Prop :=
  ∃ s ∈ mSl st.inp st.c.me, s(st.c.me, u) ∈ s ∧ P.out (st.cp s) = none

/-- all own copies have halted -/
def allH (P : Proto V) (st : MainS V P) : Prop :=
  ∀ s ∈ mSl st.inp st.c.me, (P.out (st.cp s)).isSome

open Classical in
/-- the round in which all own copies were first found halted, if it has come -/
noncomputable def effDt (P : Proto V) (st : MainS V P) : Option ℕ :=
  match st.dt with
  | some d => some d
  | none => if allH P st then some st.th.length else none

open Classical in
/-- the first round in which a word from `u` was recorded in the history -/
noncomputable def fstIdx (h : Hist V) (u : V) : Option ℕ :=
  if hh : ∃ i, i < h.length ∧ (hget h i u).isSome then some (Nat.find hh) else none

open Classical in
/-- the round in which the own report starts: once done (`ed`) and all children have started
reporting, the maximum of the done round and the children's start rounds plus `L` -/
noncomputable def repSt (L : ℕ) (kids : Finset V) (ed : Option ℕ) (h : Hist V) : Option ℕ :=
  match ed with
  | none => none
  | some d => if ∀ c ∈ kids, (fstIdx h c).isSome then
      some (max d (kids.sup (fun c => (fstIdx h c).getD 0 + L))) else none

/-- word `j` of a report of the pair `a`: the `Dg` base-`β` digits of `a.1`, then of `a.2` -/
def repWord (β Dg : ℕ) (a : ℕ × ℕ) (j : ℕ) : Word V :=
  if j < Dg then .num (a.1 / β ^ j % β) else .num (a.2 / β ^ (j - Dg) % β)

/-- decoding of a report received from `u` starting in round `a` -/
noncomputable def decRep (β Dg : ℕ) (h : Hist V) (u : V) (a : ℕ) : ℕ × ℕ :=
  (decD β Dg (fun i => (hget h i u).getD (.num 0)) a,
    decD β Dg (fun i => (hget h i u).getD (.num 0)) (a + Dg))

/-- the own values aggregated (maximum) with the children's reports -/
noncomputable def ecAgg (β Dg : ℕ) (val : ℕ × ℕ) (kids : Finset V) (h : Hist V) : ℕ × ℕ :=
  (max val.1 (kids.sup (fun c => (decRep β Dg h c ((fstIdx h c).getD 0)).1)),
    max val.2 (kids.sup (fun c => (decRep β Dg h c ((fstIdx h c).getD 0)).2)))

/-- the round in which the own broadcast starts: the report start at the root, `L` rounds after
the first word from the parent elsewhere -/
noncomputable def bSt (L : ℕ) (par : Option V) (kids : Finset V) (ed : Option ℕ) (h : Hist V) :
    Option ℕ :=
  match par with
  | none => repSt L kids ed h
  | some p => (fstIdx h p).map (· + L)

/-- the global values: the own aggregate at the root, the parent's broadcast elsewhere -/
noncomputable def gVal (β Dg : ℕ) (val : ℕ × ℕ) (par : Option V) (kids : Finset V) (h : Hist V) :
    ℕ × ℕ :=
  match par with
  | none => ecAgg β Dg val kids h
  | some p => decRep β Dg h p ((fstIdx h p).getD 0)

open Classical in
/-- the tree word to `u` in the current round (`h.length`): the report to the parent, the
broadcast to the children -/
noncomputable def tSend (n Dg : ℕ) (val : ℕ × ℕ) (par : Option V) (kids : Finset V)
    (ed : Option ℕ) (h : Hist V) (u : V) : Option (Word V) :=
  if par = some u then
    (match repSt (2 * Dg) kids ed h with
     | some R => if R ≤ h.length ∧ h.length < R + 2 * Dg then
         some (repWord (n + 4) Dg (ecAgg (n + 4) Dg val kids h) (h.length - R)) else none
     | none => none)
  else if u ∈ kids then
    (match bSt (2 * Dg) par kids ed h with
     | some B => if B ≤ h.length ∧ h.length < B + 2 * Dg then
         (match par with
          | none => some (repWord (n + 4) Dg (ecAgg (n + 4) Dg val kids h) (h.length - B))
          | some p => hget h (h.length - 2 * Dg) p)
       else none
     | none => none)
  else none

/-- halting: `L·(n - dep)` rounds after the start of the own broadcast -/
def tHalt (n Dg dep : ℕ) (par : Option V) (kids : Finset V) (ed : Option ℕ) (h : Hist V) :
    Prop :=
  ∃ B, bSt (2 * Dg) par kids ed h = some B ∧ B + 2 * Dg * (n - dep) ≤ h.length

open Classical in
/-- **The main phase**: the copies of `P` in all own cluster slices, in parallel, and the
termination detection with the convergecast of the local values `valF` (two numbers of `Dg`
digits); output `finF` of the copies' states and the global values. -/
@[reducible] noncomputable def mainP (P : Proto V) (Dg : ℕ)
    (valF : NCtx V → (Agent V → Option Mem) → (Finset (Sym2 V) → P.S) → ℕ × ℕ)
    (finF : NCtx V → (Agent V → Option Mem) → (Finset (Sym2 V) → P.S) → ℕ × ℕ →
      Agent V → Option Mem) : Proto V where
  S := MainS V P
  Ω := Finset (Sym2 V) → P.Ω
  init c inp ω := ⟨c, inp, fun s => P.init (cctx c s) (cinp c) (ω s), none, []⟩
  send _ st u := if h : runSl P st u then
      P.send (cctx st.c (Exists.choose h)) (st.cp (Exists.choose h)) u
    else tSend (Fintype.card V) Dg (valF st.c st.inp st.cp) (mPar st.inp st.c.me)
      (mKids st.inp st.c.me) (effDt P st) st.th u
  recv _ st m := ⟨st.c, st.inp, fun s => if s ∈ mSl st.inp st.c.me ∧ P.out (st.cp s) = none then
      P.recv (cctx st.c s) (st.cp s) (fun u => if s(st.c.me, u) ∈ s then m u else none)
      else st.cp s, effDt P st, st.th ++ [fun u => if runSl P st u then none else m u]⟩
  out st := if tHalt (Fintype.card V) Dg (mDep st.inp st.c.me) (mPar st.inp st.c.me)
      (mKids st.inp st.c.me) (effDt P st) st.th then
    some (finF st.c st.inp st.cp (gVal (Fintype.card V + 4) Dg (valF st.c st.inp st.cp)
      (mPar st.inp st.c.me) (mKids st.inp st.c.me) st.th)) else none

/-! ## The local values and the final output -/

/-- the pipeline output of a copy in state `s` at node `me` -/
noncomputable def cOut (P : Proto V) (me : V) (s : P.S) : Option (PipeOut V) :=
  rdIn (PipeOut V) ((P.out s).getD (fun _ => none)) me

/-- the route function recorded by the dummy routing -/
def oRt (o : PipeOut V) : Port V × Port V → List (Sym2 V) := o.2.1

/-- the ports of `A(C)` from the setup output -/
def oPa (o : PipeOut V) : Finset (Port V) := o.1.1.2.2.2.2

/-- the topology packets received at the node's ports -/
def oRcv (o : PipeOut V) : Multiset (PktP V) := o.1.2.2

/-- the length of the own path in overlay `j` of the cluster of slice `s` -/
noncomputable def pathLenL (me : V) (s : Finset (Sym2 V)) (o : Option (PipeOut V)) (j : ℕ) : ℕ :=
  match o with
  | some o => (oRt o (srcPortL me s, portAssignL me (oPa o) j)).length
  | none => 0

/-- **The local values** of a node: the maximum length of its own overlay paths, and its number
of clusters. -/
noncomputable def valE (P : Proto V) (c : NCtx V) (inp : Agent V → Option Mem)
    (cp : Finset (Sym2 V) → P.S) : ℕ × ℕ :=
  ((range (Fintype.card V)).sup (fun j => (mSl inp c.me).sup (fun s =>
      pathLenL c.me s (cOut P c.me (cp s)) j)),
    (mSl inp c.me).card)

/-- the edge at the head of a payload -/
def hdE : Msg V → Option (Sym2 V)
  | .edge e :: _ => some e
  | _ => none

/-- the topology of the cluster (the edges named by the received payloads) -/
noncomputable def topoL (o : PipeOut V) : Finset (Sym2 V) :=
  ((oRcv o).filterMap (fun x => hdE x.2)).toFinset

open Classical in
/-- the weight of `e` decoded from a received payload naming `e` -/
noncomputable def wL (wexp : ℕ) (o : PipeOut V) (e : Sym2 V) : ℕ :=
  if h : ∃ x ∈ oRcv o, hdE x.2 = some e then
    decD (Fintype.card V + 4) (wexp + 1) (fun i => h.choose.2.getD i (.num 0)) 1
  else 0

/-- the node hosts the aggregator of the cluster of output `o` in overlay `j` -/
def hostsL (me : V) (o : PipeOut V) (j : ℕ) : Prop :=
  j < Fintype.card V ∧ (oPa o).Nonempty ∧ (portAssignL me (oPa o) j).1 = me

open Classical in
/-- the views of the agents hosted by the node in overlay `j` -/
noncomputable def viewL (wexp : ℕ) (P : Proto V) (c : NCtx V) (inp : Agent V → Option Mem)
    (cp : Finset (Sym2 V) → P.S) (j : ℕ) : Agent V → Option (Sym2 V → ℕ)
  | .inl u => if u = c.me then some (ownVw c) else none
  | .inr C' => if h : ∃ s ∈ mSl inp c.me, ∃ o, cOut P c.me (cp s) = some o ∧ hostsL c.me o j ∧
        topoL o = C' then
      some (fun e => if e ∈ C' then
        (match cOut P c.me (cp h.choose) with
         | some o => wL wexp o e
         | none => 0) else 0)
    else none

open Classical in
/-- the embedded paths known to the node (key-edge model) -/
noncomputable def embL (P : Proto V) (c : NCtx V) (inp : Agent V → Option Mem)
    (cp : Finset (Sym2 V) → P.S) (j : ℕ) (u : V) (k : Sym2 V) : Option (List (Sym2 V)) :=
  if j < Fintype.card V then
    (if u = c.me then
      (if h : ∃ s ∈ mSl inp c.me, (srcPortL c.me s).2 = k then
        (match cOut P c.me (cp h.choose) with
         | some o => some (oRt o (srcPortL c.me h.choose, portAssignL c.me (oPa o) j))
         | none => none)
       else none)
    else
      (if h : ∃ s ∈ mSl inp c.me, ∃ o, cOut P c.me (cp s) = some o ∧
          oRt o ((u, k), portAssignL c.me (oPa o) j) ≠ [] then
        (match cOut P c.me (cp h.choose) with
         | some o => some (oRt o ((u, k), portAssignL c.me (oPa o) j))
         | none => none)
       else none))
  else (if u = c.me ∧ ∃ s ∈ mSl inp c.me, (srcPortL c.me s).2 = k then some [] else none)

/-- **The final output** of a node: its embedding knowledge (`EK`), with the global dilation and
overlap `gd`. -/
noncomputable def ekL (wexp : ℕ) (P : Proto V) (c : NCtx V) (inp : Agent V → Option Mem)
    (cp : Finset (Sym2 V) → P.S) (gd : ℕ × ℕ) : EK V :=
  (viewL wexp P c inp cp, embL P c inp cp, mSl inp c.me, gd.1, gd.2)

open Classical in
/-- the output of the main phase: the embedding knowledge of the own physical agent -/
noncomputable def finE (wexp : ℕ) (P : Proto V) (c : NCtx V) (inp : Agent V → Option Mem)
    (cp : Finset (Sym2 V) → P.S) (gd : ℕ × ℕ) : Agent V → Option Mem :=
  fun g => if g = .inl c.me then some ⟨EK V, ekL wexp P c inp cp gd⟩ else none

end EmbC

end APSP.Stoc.Congest
