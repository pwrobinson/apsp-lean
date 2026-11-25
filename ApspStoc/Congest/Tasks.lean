import ApspStoc.Toolkit
import ApspStoc.Congest.Comb
import ApspStoc.Congest.ExpDiam

/-!
# The tasks in the CONGEST semantics

This file fixes, for every task of `Toolkit.lean`, its *instance* (communication graph,
participants, hosts, local contexts), the data its agents hold at the start, and its
postcondition. It then defines the concrete judgement `CImplT` and proves the generic [STD] rules of
the toolkit for it. In every instance a participant may send only along the edges of the
instance's communication graph (proper sends, `Core.lean`); in particular a protocol run on a
cluster instance only uses edges of its cluster.

## Instances
* `ioInst N E j sz Pt` (tasks on overlay `L_j` with participants `Pt`): the nodes of `Pt` take
  part and communicate over the edges of the network between them; the other nodes are not
  involved. The agents are the physical nodes of `Pt` and the aggregators of the clusters of `E`
  whose host (the common endpoint of the embedded paths of `C` in overlay `j`) is in `Pt`. A node
  knows its own local view and that of the aggregators it hosts (the topology of their clusters),
  the public numbers `j`, `sz`, `E.dil`, `E.ov`, its cluster slices `C ∩ inc(v)` (`clLoc`), and the
  embedded paths through it in the *key-edge model* (`ioEmb`): a node cannot know a cluster as a
  whole edge set, so the path of `u` to the aggregator of its cluster `C` is keyed by `u` and the
  key edge `(srcPort C u).2 ∈ C` (distinct clusters of `u` have distinct key edges).
* `baseInst N` (the preprocessing and the whole algorithm): all nodes take part, only physical
  agents, every node knows its incident edges and their weights.
* `clInst0 N C` (cluster setup) and `clInst N C` (routing in a cluster): the participants are the
  nodes of `C`, communication only over edges of `C`. In `clInst N C` the numbers `n_C` and `m_C`
  are public: the cluster setup broadcasts them (every node learns all degrees).

## Data of the preprocessing
* `resLoc F v`: the residual edges at `v`; `clLoc cl v`: the slices `C ∩ inc(v)` of the clusters
  of `cl` at `v` (which incident edges belong to the same cluster).
* `ekAt N E v`: what a node knows about the embedded overlays (its views for every overlay, the
  embedded paths through it in the key-edge model, its cluster slices, and the public dilation and
  overlap). A node thus knows its clusters: `ioEmb E v j v k ≠ none` iff `k` is the key edge
  `(srcPort C v).2` of one of its clusters `C ∈ E.cl`.
* the cluster setup (`SetupSpec`): leader, parent in a spanning tree, the (ID, degree) table of the
  cluster, and the ports of `A(C)` (`portsA C`).
* routing tasks (`.route`, `.routeViaG0`): every packet carries a payload of at most `pw` words
  (`PktP`, `PayloadOK`). A node knows its ports in `P`, the packets (with payloads) it must send,
  and `λ`; afterwards it knows the recorded routes through it and the packets (with payloads)
  delivered to its ports (`rkAt`).
* the embedded `G₀` (`.buildG0`, `.routeViaG0`), *local* knowledge (`g0At`): its public
  parameters, and for every surviving walk through the node its end ports and the positions and
  edges of the walk at the node (not the whole walk, which would cost `ℓ²` per walk).
-/

namespace APSP.Stoc.Congest

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Local knowledge -/

/-- the residual edges at `v` -/
def resLoc (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) := F.filter (fun e => v ∈ e)

/-- the slices `C ∩ inc(v)` of the clusters of `cl` at `v` -/
def clLoc (cl : Finset (Finset (Sym2 V))) (v : V) : Finset (Finset (Sym2 V)) :=
  (cl.image (fun C => C.filter (fun e => v ∈ e))).filter (fun s => s.Nonempty)

/-- the state of the iterative decomposition at a node: residual edges and cluster slices -/
abbrev DState (V : Type) := Finset (Sym2 V) × Finset (Finset (Sym2 V))

/-- `v` lies on the walk `l` starting at `u` -/
def OnWalk (l : List (Sym2 V)) (u v : V) : Prop := v = u ∨ ∃ e ∈ l, v ∈ e

open Classical in
/-- The host of the aggregator of `C` in overlay `j`: the common endpoint of the embedded paths. -/
noncomputable def aggHost (E : Overlays V) (j : ℕ) (C : Finset (Sym2 V)) : Option V :=
  if h : C ∈ E.cl ∧ (nodes C).Nonempty ∧ ∃ hv : V, ∀ v ∈ nodes C, IsEdgeWalk (E.path j v C) v hv
  then some (Classical.choose h.2.2) else none

/-- hosts of the agents of overlay `j` among the participants `Pt`: a node of `Pt` hosts its own
agent; the aggregator of `C` is hosted by its host if that host takes part -/
noncomputable def ioHost (E : Overlays V) (j : ℕ) (Pt : Finset V) : Agent V → Option V
  | .inl v => if v ∈ Pt then some v else none
  | .inr C => match aggHost E j C with
    | some h => if h ∈ Pt then some h else none
    | none => none

open Classical in
/-- what node `v` knows about overlay `j`: the local views of the agents it hosts -/
noncomputable def ioView (N : WNet V) (E : Overlays V) (j : ℕ) (Pt : Finset V) (v : V) :
    Agent V → Option (Sym2 V → ℕ) :=
  fun g => if ioHost E j Pt g = some v then some (lview N g) else none

open Classical in
/-- The embedded paths known to node `x`, in the key-edge model: `ioEmb E x j u k = some path` iff
`path` is the path of `u` to the aggregator of a cluster `C ∈ E.cl` with `u ∈ nodes C` in
overlay `j`, `k = (srcPort C u).2` is the key edge of `C` at `u`, and `x` lies on the path. -/
noncomputable def ioEmb (E : Overlays V) (x : V) : ℕ → V → Sym2 V → Option (List (Sym2 V)) :=
  fun j u k => if h : ∃ C ∈ E.cl, u ∈ nodes C ∧ (srcPort C u).2 = k ∧ OnWalk (E.path j u C) u x
    then some (E.path j u h.choose) else none

/-- The key edge of a cluster at one of its nodes is an edge of the cluster at that node. -/
lemma srcPort_snd_mem {C : Finset (Sym2 V)} {u : V} (hu : u ∈ nodes C) :
    (srcPort C u).2 ∈ C ∧ u ∈ (srcPort C u).2 := by
  have h := mem_portsAt.1 (srcPort_mem C hu)
  exact ⟨h.2.1, h.1 ▸ h.2.2⟩

/-- For pairwise disjoint clusters, the paths known to a node are exactly the paths through it:
`ioEmb E x j u k = some (E.path j u C)` for the cluster `C ∋ u` with key edge `k` at `u`. -/
lemma ioEmb_eq_some {E : Overlays V} (hdisj : ∀ C ∈ E.cl, ∀ C' ∈ E.cl, C ≠ C' → Disjoint C C')
    {x u : V} {j : ℕ} {C : Finset (Sym2 V)} (hC : C ∈ E.cl) (hu : u ∈ nodes C)
    (hx : OnWalk (E.path j u C) u x) : ioEmb E x j u (srcPort C u).2 = some (E.path j u C) := by
  classical
  have hex : ∃ C' ∈ E.cl, u ∈ nodes C' ∧ (srcPort C' u).2 = (srcPort C u).2 ∧
      OnWalk (E.path j u C') u x := ⟨C, hC, hu, rfl, hx⟩
  unfold ioEmb
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hC', hu', hk, -⟩ := hex.choose_spec
  by_contra hne
  have hCC : hex.choose ≠ C := fun h => hne (by rw [h])
  exact Finset.disjoint_left.1 (hdisj _ hC' C hC hCC) (srcPort_snd_mem hu').1
    (by rw [hk]; exact (srcPort_snd_mem hu).1)

/-- A node knows only paths through it, and only paths of clusters of the source with their key
edge. -/
lemma ioEmb_spec {E : Overlays V} {x u : V} {j : ℕ} {k : Sym2 V} {l : List (Sym2 V)}
    (h : ioEmb E x j u k = some l) : ∃ C ∈ E.cl, u ∈ nodes C ∧ (srcPort C u).2 = k ∧
      OnWalk (E.path j u C) u x ∧ l = E.path j u C := by
  classical
  unfold ioEmb at h
  split_ifs at h with hex
  · obtain ⟨hC, hu, hk, hx⟩ := hex.choose_spec
    exact ⟨hex.choose, hC, hu, hk, hx, (Option.some.inj h).symm⟩

/-- the communication graph of an overlay task: edges of the network between participants -/
def ioG (N : WNet V) (Pt : Finset V) : SimpleGraph V where
  Adj u v := N.G.Adj u v ∧ u ∈ Pt ∧ v ∈ Pt
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => N.G.loopless.irrefl _ h.1⟩

instance (N : WNet V) (Pt : Finset V) : DecidableRel (ioG N Pt).Adj := fun u v =>
  inferInstanceAs (Decidable (N.G.Adj u v ∧ u ∈ Pt ∧ v ∈ Pt))

lemma ioHost_mem {E : Overlays V} {j : ℕ} {Pt : Finset V} {g : Agent V} {v : V}
    (h : ioHost E j Pt g = some v) : v ∈ Pt := by
  cases g with
  | inl u =>
    simp only [ioHost] at h
    split_ifs at h with hu
    cases h; exact hu
  | inr C =>
    simp only [ioHost] at h
    split at h
    · split_ifs at h with hh
      cases h; exact hh
    · cases h

/-- Instance of a task on overlay `j` of `E` with public size bound `sz` and participants `Pt`. The
other nodes are not involved: they have no edges in this instance and host no agent. A node knows
the views of the agents it hosts, the public numbers `[j, sz, E.dil, E.ov]`, the embedded paths
through it (key-edge model, `ioEmb`) and its cluster slices (`clLoc E.cl`). -/
noncomputable def ioInst (N : WNet V) (E : Overlays V) (j sz : ℕ) (Pt : Finset V) : Inst V where
  G := ioG N Pt
  part v := v ∈ Pt
  host := ioHost E j Pt
  ctx v := ⟨v, ioView N E j Pt v, [j, sz, E.dil, E.ov], ioEmb E v, clLoc E.cl v⟩
  adj_part _ _ h := h.2.1
  host_part _ _ h := ioHost_mem h

/-- hosts of the physical agents -/
def physHost : Agent V → Option V
  | .inl v => some v
  | .inr _ => none

open Classical in
/-- Instance of the preprocessing and of the whole algorithm. -/
noncomputable def baseInst (N : WNet V) : Inst V where
  G := N.G
  part _ := True
  host := physHost
  ctx v := ⟨v, fun g => if g = .inl v then some (lview N g) else none, [], fun _ _ _ => none, ∅⟩
  adj_part _ _ _ := trivial
  host_part _ _ _ := trivial

open Classical in
/-- hosts of the physical agents of the nodes of `C` -/
noncomputable def clHost (C : Finset (Sym2 V)) : Agent V → Option V
  | .inl v => if v ∈ nodes C then some v else none
  | .inr _ => none

/-- the communication graph of a cluster task: edges of `C` that are edges of the network -/
def clG (N : WNet V) (C : Finset (Sym2 V)) : SimpleGraph V := clGraph C ⊓ N.G

instance (N : WNet V) (C : Finset (Sym2 V)) : DecidableRel (clG N C).Adj := fun u v =>
  inferInstanceAs (Decidable ((clGraph C).Adj u v ∧ N.G.Adj u v))

/-- local view of a node in a cluster task: its incident edges in `C` and their weights -/
noncomputable def clView (N : WNet V) (C : Finset (Sym2 V)) (v : V) : Sym2 V → ℕ := by
  classical exact fun e => if e ∈ C ∧ v ∈ e then N.w e else 0

open Classical in
/-- Instance of a task in cluster `C` with public numbers `pub`. -/
noncomputable def clInstP (N : WNet V) (C : Finset (Sym2 V)) (pub : List ℕ) : Inst V where
  G := clG N C
  part v := v ∈ nodes C
  host := clHost C
  ctx v := ⟨v, fun g => if g = .inl v then some (clView N C v) else none, pub, fun _ _ _ => none,
    ∅⟩
  adj_part _ _ h := mem_nodes_of_adj h.1
  host_part g v h := by
    cases g with
    | inl u =>
      simp only [clHost] at h
      split_ifs at h with hu
      cases h; exact hu
    | inr _ => cases h

/-- the cluster setup: nothing about `C` is public -/
noncomputable def clInst0 (N : WNet V) (C : Finset (Sym2 V)) : Inst V := clInstP N C []

/-- routing in a cluster: `n_C` and `m_C` are public (established by the setup) -/
noncomputable def clInst (N : WNet V) (C : Finset (Sym2 V)) : Inst V :=
  clInstP N C [(nodes C).card, C.card]

/-! ## Data types of the tasks -/

/-- What a node knows about the embedded overlays: for every overlay its view of the agents it
hosts, the embedded paths through it (key-edge model, `ioEmb`), its cluster slices, and the public
dilation and overlap. -/
abbrev EK (V : Type) :=
  (ℕ → Agent V → Option (Sym2 V → ℕ)) × (ℕ → V → Sym2 V → Option (List (Sym2 V))) ×
    Finset (Finset (Sym2 V)) × ℕ × ℕ

/-- the embedding knowledge of agent `g` (physical agents only) -/
noncomputable def ekAt (N : WNet V) (E : Overlays V) : Agent V → EK V
  | .inl v => (fun j => ioView N E j univ v, ioEmb E v, clLoc E.cl v, E.dil, E.ov)
  | .inr _ => (fun _ _ => none, fun _ _ _ => none, ∅, 0, 0)

/-- the decomposition state of a physical agent -/
def dAt (F : Finset (Sym2 V)) (acc : Finset (Finset (Sym2 V))) : Agent V → DState V
  | .inl v => (resLoc F v, clLoc acc v)
  | .inr _ => (∅, ∅)

/-- a packet with its payload: (source port, destination port) and the payload words -/
abbrev PktP (V : Type) := (Port V × Port V) × Msg V

/-- input of a routing task: own ports in `P`, own packets with their payloads, the load bound -/
abbrev RIn (V : Type) := Finset (Port V) × Multiset (PktP V) × ℕ

/-- the routing input of a physical agent: its ports, the packets it sends, the load bound -/
noncomputable def rinAt (P : Finset (Port V)) (pl : Multiset (PktP V)) (lam : ℕ) : Agent V → RIn V
  | .inl v => by
    classical exact (P.filter (fun p => p.1 = v), pl.filter (fun x => x.1.1.1 = v), lam)
  | .inr _ => (∅, 0, lam)

/-- every payload has at most `pw` words, each valid for the bandwidth of a network with `n`
nodes -/
def PayloadOK (n pw : ℕ) (pl : Multiset (PktP V)) : Prop :=
  ∀ x ∈ pl, x.2.length ≤ pw ∧ ∀ w ∈ x.2, WordOK n w

/-- the hops of the walk `l` at `v`: the pairs `(i, e_i)` with `v ∈ e_i` (`e_i` the `i`-th edge
of `l`), in increasing order of `i` -/
def hopsAt (l : List (Sym2 V)) (v : V) : List (ℕ × Sym2 V) :=
  (l.zipIdx.filter (fun ei => v ∈ ei.1)).map (fun ei => (ei.2, ei.1))

/-- *Local* knowledge of the embedded `G₀`: its (public) parameters, and for every surviving walk
through the node its (start port, end port) and its hops at the node -/
abbrev G0K (V : Type) := G0Data × Multiset ((Port V × Port V) × List (ℕ × Sym2 V))

/-- the `G₀`-knowledge of a physical agent `v`: for every surviving walk `w` whose path visits `v`,
the edge `(start port, end port)` of `G₀` and the hops `hopsAt (rwPath …) v` of the walk at `v` -/
noncomputable def g0At (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ)
    (ω : RWSeeds C P R ℓ) (g : G0Data) : Agent V → G0K V
  | .inl v => by classical exact (g, ((rwSurvivors C P R ℓ ω).val.map (fun w =>
      ((w.1.1, (rwEnd C w.1.1 (ω w)).getD w.1.1), hopsAt (rwPath C w.1.1 (ω w)) v))).filter
        (fun t => t.2 ≠ []))
  | .inr _ => (g, 0)

/-- what a node knows after routing: the recorded routes of the packets through it, and the
packets (with payloads) delivered to its ports -/
abbrev RK (V : Type) := (Port V × Port V → List (Sym2 V)) × Multiset (PktP V)

/-- the routing knowledge of a physical agent `v`: the recorded routes through `v`, and the
packets received at `v`'s ports -/
noncomputable def rkAt (r : Routes V) (D : Demand V) (pl : Multiset (PktP V)) : Agent V → RK V
  | .inl v => by classical exact
      (fun pq => if pq ∈ D ∧ OnWalk (r pq) pq.1.1 v then r pq else [],
        pl.filter (fun x => x.1.2.1 = v))
  | .inr _ => (fun _ => [], 0)

/-- output of the cluster setup: leader, parent, all (ID, degree) pairs, the ports of `A(C)` -/
abbrev SetupOut (V : Type) := V × Option V × Finset (V × ℕ) × Finset (Port V)

/-- Specification of the cluster setup: a leader `ℓ ∈ nodes C` and a spanning tree of `C` rooted
at `ℓ` (parent pointers), and every node of `C` knows `ℓ`, its parent, the degrees of all nodes
of `C` (from which `n_C`, `m_C` and `A(C)` are computed locally), and the ports of `A(C)`
(`portsA C`, which needs the incident edges of the nodes of `A(C)`). -/
def SetupSpec (C : Finset (Sym2 V)) (z : Agent V → SetupOut V) : Prop :=
  ∃ ℓ ∈ nodes C, ∃ par : V → Option V, SpanForest (nodes C) C par (fun _ => ℓ) ∧
    ∀ v ∈ nodes C, z (.inl v) = (ℓ, par v, (nodes C).image (fun u => (u, degIn C u)), portsA C)

/-! ## The concrete judgement -/

/-- an algorithm: a uniform protocol for every node set -/
def CAlg : Type 2 := ∀ (V : Type) [Fintype V] [DecidableEq V], Proto V

/-- typed data as dynamically typed data -/
def inOf {α : Type} (x : Agent V → α) : Agent V → Mem := fun g => ⟨α, x g⟩

/-- a typed postcondition on the outputs of the simulated agents -/
def postOf {β : Type} (I : Inst V) (R : (Agent V → β) → Prop) : (Agent V → Mem) → Prop :=
  fun y => ∃ z : Agent V → β, (∀ g, (I.host g).isSome → y g = ⟨β, z g⟩) ∧ R z

/-- **The concrete judgement**: algorithm `A` solves task `t` on `N` within cost `p` except with
probability `≤ δ`, for every allowed input. -/
noncomputable def CImplT (A : CAlg) {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) :
    Task V → Prof V → ℝ → Prop
  | .io E j sz Pt _ _ x R, p, δ =>
      ImplI (A V) (ioInst N E j sz Pt) (inOf x) (postOf (ioInst N E j sz Pt) R) p δ
  | .compute none β spec, p, δ =>
      ImplI (A V) (baseInst N) (inOf (fun _ => ()))
        (postOf (baseInst N) (fun z : Agent V → β => spec (fun v => z (.inl v)))) p δ
  | .compute (some E) β spec, p, δ =>
      ImplI (A V) (baseInst N) (inOf (fun g => ((), ekAt N E g)))
        (postOf (baseInst N) (fun z : Agent V → β => spec (fun v => z (.inl v)))) p δ
  | .mst E j sz Pt S, p, δ =>
      ImplI (A V) (ioInst N E j sz Pt) (inOf (memAg S))
        (postOf (ioInst N E j sz Pt) (fun z : Agent V → Option V × V =>
          SpanForest S (inducedEdges N.G S) (fun v => (z (.inl v)).1) (fun v => (z (.inl v)).2)))
        p δ
  | .embedOverlays Good, p, δ =>
      ImplI (A V) (baseInst N) (inOf (fun _ => ()))
        (postOf (baseInst N) (fun z : Agent V → EK V =>
          ∃ E, Good E ∧ ∀ v, z (.inl v) = ekAt N E (.inl v))) p δ
  | .decompose Good, p, δ =>
      ImplI (A V) (baseInst N) (inOf (fun _ => ()))
        (postOf (baseInst N) (fun z : Agent V → DState V =>
          ∃ cl, Good cl ∧ ∀ v, (z (.inl v)).2 = clLoc cl v)) p δ
  | .decompRest F acc Good, p, δ =>
      ImplI (A V) (baseInst N) (inOf (dAt F acc))
        (postOf (baseInst N) (fun z : Agent V → DState V =>
          ∃ cl, Good cl ∧ ∀ v, (z (.inl v)).2 = clLoc cl v)) p δ
  | .expDecompOnce F _ GP, p, δ =>
      ∀ a : V → Finset (Finset (Sym2 V)),
      ImplI (A V) (baseInst N)
        (inOf (fun g => match g with | .inl v => ((resLoc F v, a v) : DState V) | .inr _ => (∅, ∅)))
        (postOf (baseInst N) (fun z : Agent V → Finset (Finset (Sym2 V)) =>
          ∃ P, GP P ∧ ∀ v, z (.inl v) = clLoc P v)) p δ
  | .embedFrom cl Good, p, δ =>
      ∀ r : V → Finset (Sym2 V),
      ImplI (A V) (baseInst N)
        (inOf (fun g => match g with
          | .inl v => (((), (r v, clLoc cl v)) : Unit × DState V) | .inr _ => ((), (∅, ∅))))
        (postOf (baseInst N) (fun z : Agent V → EK V =>
          ∃ E, Good E ∧ ∀ v, z (.inl v) = ekAt N E (.inl v))) p δ
  | .clusterSetup C, p, δ =>
      ImplI (A V) (clInst0 N C) (inOf (fun _ => ())) (postOf (clInst0 N C) (SetupSpec C)) p δ
  | .buildG0 C P Good, p, δ =>
      ∀ (pl : Multiset (PktP V)) (lam : ℕ),
      ImplI (A V) (clInst N C) (inOf (rinAt P pl lam))
        (postOf (clInst N C) (fun z : Agent V → G0K V =>
          ∃ (R ℓ : ℕ) (ω : RWSeeds C P R ℓ) (g : G0Data), TrueParams C P R ℓ ω g ∧ Good g ∧
            ∀ v ∈ nodes C, z (.inl v) = g0At C P R ℓ ω g (.inl v))) p δ
  | .routeViaG0 C P g D lam pw GR, p, δ =>
      ∀ (R ℓ : ℕ) (ω : RWSeeds C P R ℓ), TrueParams C P R ℓ ω g →
      ∀ pl : Multiset (PktP V), pl.map Prod.fst = D → PayloadOK (Fintype.card V) pw pl →
      ImplI (A V) (clInst N C) (inOf (fun a => (rinAt P pl lam a, g0At C P R ℓ ω g a)))
        (postOf (clInst N C) (fun z : Agent V → RK V =>
          ∃ r, GR r ∧ ∀ v ∈ nodes C, z (.inl v) = rkAt r D pl (.inl v))) p δ
  | .route C P D lam pw GR, p, δ =>
      ∀ pl : Multiset (PktP V), pl.map Prod.fst = D → PayloadOK (Fintype.card V) pw pl →
      ImplI (A V) (clInst N C) (inOf (rinAt P pl lam))
        (postOf (clInst N C) (fun z : Agent V → RK V =>
          ∃ r, GR r ∧ ∀ v ∈ nodes C, z (.inl v) = rkAt r D pl (.inl v))) p δ

end APSP.Stoc.Congest
