import ApspStoc.G0Model

/-!
# The distributed-computing toolkit for the STOC submission: model and assumptions

## The judgement

`T.Alg` is an abstract type of *algorithms*: uniform randomized CONGEST protocols (`O(log n)`-bit
messages), i.e. a single local program run by every node, depending only on the node's local
knowledge. `T.Impl A N t p δ` is a Hoare-style judgement:

> algorithm `A`, run on network `N` from any configuration satisfying the precondition of task
> `t`, achieves the postcondition of `t` within `p.rounds` rounds, sending at most `p.load e`
> messages over every edge `e` and at most `p.msgs` messages in total, except with probability at
> most `δ`.

Composite algorithms are built with the combinators of `Toolkit`, so an algorithm never depends on
the network: the main theorem has the shape `∃ A, ∃ C k K, ∀ N, Impl (A n) N APSP ...`.

## Semantic tasks

The tasks of the shortest-path phase carry their meaning.
A task `.io E j sz Π α β x spec` (in Lean the participant set is named `Pt`, since `Π` is a token)
refers to the overlay `L_j` of the embedded overlay family `E`; its *agents* are the physical nodes
and the virtual aggregators of `L_j` (the aggregator of a cluster `C` is simulated by its host in
`A(C)`). Its precondition is "every agent `g` holds `x g`" and its postcondition "every agent `g`
holds some `y g`, where `spec y`". Algorithms are composed with a
generic sequencing rule (`bind`: the second algorithm starts from the inputs together with the first
one's outputs), free *uniform* local computations (`loc`), and local calls (`call F B`: every agent
computes the input of `B` locally from its data, then `B` runs on these values). There is no
general frame rule: a protocol cannot take apart a value of an arbitrary product type. Its role is
played by `call` with the uniform projection `sndF Γ A` (`Basics.lean`), which drops the first
component of data of the explicit shape `Γ V × A V`. Hence the correctness of the paper's own
compositions (Lemma 4.2, Lemma 5.3, Theorem 5.5) is *proved* from the specifications of the
building blocks below.

## Participants and public budgets

In the executable synchronous semantics of `Impl`, a run succeeds only if all *participating*
nodes halt in the same round; this is what makes sequential composition (`bind`) sound. Hence
every participant must be able to compute when a phase ends, i.e. every round budget must be a
function of quantities known to all participants.

* **Participants.** An overlay task `.io E j sz Π …` (and `.mst E j sz Π S`) names its participant
  set `Π`: the nodes of `Π` take part (they know `sz` and halt together), the other nodes are not
  involved, and agents hosted outside `Π` are not simulated. In the paper's model a subproblem on a
  set `S` involves only its *footprint* `footprint E j S` (`Defs.lean`): `S`, the nodes on the
  embedded aggregator paths of `S` in `L_j`, and their endpoints, the hosts. The contracts of the
  building blocks working on a set `S` require `footprint E j S ⊆ Π` (or only `S ⊆ Π` for those
  using only edges inside `S`: `ghs`, `treeCast`, `notify`). The generic rules relating `.io` tasks
  (`weakenIO`, `bind`, `callR`, `locR`) keep `Π` fixed. Without explicit participants, every task
  would involve all nodes, and the recursion of Theorem 5.5, which runs subproblems on the
  components of subsets one after another, each with a budget proportional to its own size, would
  be unimplementable: a node far from a component cannot know its size or when its subproblem
  starts. With participants, each component runs on its own footprint (`perCompR`).
* **Public budgets.** For the same reason, the parameters on which a round budget depends are
  parameters of the algorithm: the inverse conductance `φinv` of the expander decomposition
  (`expDecomp`, `A ν φinv`), the message size `μ` of the aggregator exchanges (`aggUp`, `aggDown`,
  `A ν μ`), a public bound `kb` on the number of virtual nodes of an Eulerian-orientation instance
  (`eoVirt`, `eoAlg ν kb M P`), and public bounds `R`, `Cg` on the rounds and the congestion of the
  scheduled instances (`schedule`, `sched c ν R Cg A`). In every use, these are constants or
  functions of `ν` and of the public value size.

## The size bound

The contracts take a public size bound `ν` with `Fintype.card V ≤ ν` and `ν ≤ Fintype.card V`,
i.e. `ν = n`. The upper bound is needed because the concrete semantics bounds the numbers in a
message by `n + 3`: a number `≤ ν^Bw` fits in `O(Bw)` words only if `ν ≤ n`. The main theorem
instantiates `ν = n`.

## The assumptions

All assumptions are fields of `Toolkit`, each tagged with its source. The tags distinguish
generic facts, cited theorems, cited theorems used in a stronger form, and implementation
assumptions about how the paper's steps are carried out:

* **[STD]** standard facts about CONGEST: sequencing, local computation, local calls, weakening,
  tree broadcast/convergecast [35], one round of direct messages, leader election and spanning
  trees in a cluster, and the sequencing steps of the preprocessing (including the local
  bookkeeping of the iterative decomposition, `dstart`/`dstep`).
* **[IMPL]** implementation and cost-accounting assumptions for the paper's own steps, which are
  standard techniques but not cited theorems: Lemma 2.2 on aggregator edges (`aggUp`, `aggDown`;
  its proof is random-delay routing [17]), the simulation of ring leader election over aggregator
  edges (`ringLE`), sequential execution on components (`perCompR`, not described in the paper),
  the random-walk construction (`rwLink`), and the preprocessing construction
  (`clusterPar`/`embedConstruct`).
* **[PRIOR+]** a cited theorem used in a stronger form than the paper states it: `routeG0`
  (Lemma 3.2 exposing the hierarchical structure of its routes, from which the per-route length
  bound is derived, `RoutesHier.routesOK`).
* **[PRIOR]** theorems from prior work used by the paper: expander decomposition [9] (Lemma 2.8),
  expander routing [19, 7] (Lemma 3.2), random-delay scheduling [17], GHS [16], Hirschberg–Sinclair
  ring leader election [23], the approximate-SSSP algorithm of [37] (Lemma 5.1), MST in `O(log n)`
  Minor-Aggregation rounds [16, 38], and the technique of [37] for the virtual nodes of an Eulerian
  orientation instance (as recalled in the proof of Lemma 5.3).
The paper's own lemmas and claims are proved, except Lemma 2.2 (simulating an embedded overlay;
its proof in the paper is an application of [17]), which enters in `[IMPL]` form through `aggUp`,
`aggDown` and `routeG0`. Besides the toolkit, the main theorem takes one hypothesis, `Mixing`
(`G0Model.lean`): the mixing bound for lazy random walks on expanders (Jerrum–Sinclair /
Cheeger), a theorem of mathematics used in Claims 3.4/3.5.

The abstract judgement `Impl` is constrained only by these fields. In particular, a field whose
postcondition is unsatisfiable for an allowed input would be false under the intended reading.
`SatModel.lean` constructs a model of the whole toolkit in which a judgement with failure bound
`δ < 1` implies that its postcondition is satisfiable: every contract is realizable, and the
generic rules preserve realizability.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Tasks -/

/-- The tasks of the algorithm. -/
inductive Task (V : Type) [Fintype V] [DecidableEq V] : Type 1 where
  /-- every node `v` ends with an output `o v : β` such that `spec o` holds; if `ctx = some E`, the
  overlay embedding `E` (and the knowledge established with it) is available -/
  | compute (ctx : Option (Overlays V)) (β : Type) (spec : (V → β) → Prop)
  /-- with the overlay family `E` embedded, from "every agent `g` of `L_j` holds `x g`" reach
  "every agent `g` holds `y g`" with `spec y`. `sz` is the task's *public size bound* and `Pt`
  (`Π` in prose) its *participant set*: the nodes of `Pt` take part, know `sz`, and halt together
  (in the same round); the other nodes are not involved (they send nothing and do not wait for
  the phase), and agents hosted outside `Pt` are not simulated. An aggregator acts only on data or
  messages of the task, which carry `sz`. All round budgets of the building blocks are functions
  of public quantities (`ν`, `sz`, message sizes, and the public dilation `E.dil` and overlap `E.ov`
  of the embedding), so every participant knows when each phase ends; this is what makes
  sequential composition (`bind`) meaningful. -/
  | io (E : Overlays V) (j sz : ℕ) (Pt : Finset V) (α β : Type) (x : Agent V → α)
      (spec : (Agent V → β) → Prop)
  /-- MST / leader election and spanning trees on the connected components of `G[S]` (overlay `j`,
  public size bound `sz`, participant set `Pt` as for `io`: the nodes of `Pt` take part, know `sz`
  and halt together, the other nodes are not involved, and agents hosted outside `Pt` are not
  simulated) -/
  | mst (E : Overlays V) (j sz : ℕ) (Pt : Finset V) (S : Finset V)
  /-- compute and algorithmically embed overlays `{L_j}_{j<n}` satisfying `Good`; afterwards every
  aggregator knows the topology of its cluster and every node knows the set of all IDs -/
  | embedOverlays (Good : Overlays V → Prop)
  /-- compute an expander edge decomposition satisfying `Good` -/
  | decompose (Good : Finset (Finset (Sym2 V)) → Prop)
  /-- continue the decomposition of Lemma 2.10: residual edges `F`, clusters found so far `acc` -/
  | decompRest (F : Finset (Sym2 V)) (acc : Finset (Finset (Sym2 V)))
      (Good : Finset (Finset (Sym2 V)) → Prop)
  /-- one run of the expander decomposition of [9] on the subgraph with edge set `F` -/
  | expDecompOnce (F : Finset (Sym2 V)) (φinv : ℕ) (Good : Finset (Finset (Sym2 V)) → Prop)
  /-- given the decomposition `cl`, build the overlays (Theorem 3.10) -/
  | embedFrom (cl : Finset (Finset (Sym2 V))) (Good : Overlays V → Prop)
  /-- leader, spanning tree and selection of `A(C)` in cluster `C` -/
  | clusterSetup (C : Finset (Sym2 V))
  /-- build and embed the virtual expander `G₀` on port set `P` of cluster `C` (proof of Thm 3.3) -/
  | buildG0 (C : Finset (Sym2 V)) (P : Finset (Port V)) (Good : G0Data → Prop)
  /-- route demand `D` (known load bound `lam`) on `P` through the embedded `G₀`; every packet
  carries a payload of at most `pw` words, delivered to its destination -/
  | routeViaG0 (C : Finset (Sym2 V)) (P : Finset (Port V)) (g : G0Data) (D : Demand V) (lam : ℕ)
      (pw : ℕ) (Good : Routes V → Prop)
  /-- Theorem 3.3: route a demand supported on `P` in cluster `C`, preprocessing included; every
  packet carries a payload of at most `pw` words, delivered to its destination -/
  | route (C : Finset (Sym2 V)) (P : Finset (Port V)) (D : Demand V) (lam : ℕ) (pw : ℕ)
      (Good : Routes V → Prop)

/-- Specification of a Minor-Aggregation round as a task on overlay `j` with participants `Pt`. -/
abbrev maTask (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j sz : ℕ) (Pt : Finset V)
    (I : MAInst V) : Task V := .io E j sz Pt (MAIn V) (MAOut V) (maInput I) (MASpec G E.cl I)

/-- Specification of an Eulerian-orientation instance as a task on overlay `j` with participants
`Pt`. -/
noncomputable abbrev eoTask (E : Overlays V) (j sz : ℕ) (Pt : Finset V) (H : EOInst V) : Task V :=
  .io E j sz Pt (EOIn V) (EOOut V) (eoInput H) (EOSpec E.cl H)

/-! ## The toolkit -/

/-- Assumptions (standard facts and prior work) about CONGEST, see the module docstring. -/
structure Toolkit where
  /-- algorithms (uniform randomized CONGEST protocols). It lives in `Type 2` because concrete
  protocols keep dynamically typed node memory (`Σ T : Type, T`, in `Type 1`) in their state. -/
  Alg : Type 2
  /-- the judgement (see module docstring) -/
  Impl : Alg → ∀ {V : Type} [Fintype V] [DecidableEq V], WNet V → Task V → Prof V → ℝ → Prop

  /-- [STD] sequential composition -/
  seq : Alg → Alg → Alg
  /-- [STD] the empty algorithm -/
  skip : Alg
  /-- [STD] a uniform local computation -/
  loc : LocFn → Alg
  /-- [STD] a local call: every agent `g` computes `F.f V g (lview N g) (x g)` from its data
  `x g`, then the algorithm runs on these values; the output is the inner algorithm's output -/
  call : LocFn → Alg → Alg
  /-- [STD] start of the iterative decomposition: every node initialises the residual edge set to
  its incident edges and the accumulated cluster list to empty, then runs the given algorithm -/
  dstart : Alg → Alg
  /-- [STD] one step of the iterative decomposition: run the first algorithm, update the residual
  edges and the accumulated clusters locally from its output, then run the second algorithm -/
  dstep : Alg → Alg → Alg
  /-- [PRIOR] random-delay scheduler [17] (confidence `c`, size bound `ν`, public bounds `R` on
  the rounds and `Cg` on the congestion of the instances: `sched c ν R Cg A`) -/
  sched : ℕ → ℕ → ℕ → ℕ → Alg → Alg
  /-- [IMPL] the per-cluster preprocessing of Theorem 3.10 (public exponents `Lb` of the route
  length bound and `wexp` of the weight bound: `clusterPar Lb wexp A₁ A₂ A₃`) -/
  clusterPar : ℕ → ℕ → Alg → Alg → Alg → Alg
  /-- [IMPL] the random-walk construction of `G₀` (proof of Theorem 3.3): tokens per port `Rf`,
  half walk length `ℓ`, rounds per step `tf`, and the public parameters `gf` that the nodes output
  for the constructed `G₀` (all computed from `(n_C, m_C)`) -/
  rwAlg : (ℕ → ℕ → ℕ) → ℕ → (ℕ → ℕ → ℕ) → (ℕ → ℕ → G0Data) → Alg
  /-- [IMPL] sequential execution of an algorithm on the connected components of a subset (given
  the type families `A` of the data and `Bt` of the outputs: `perComp A Bt Am B`) -/
  perComp : (Type → Type) → (Type → Type) → Alg → Alg → Alg
  /-- [PRIOR] MST in Minor-Aggregation rounds (size bound `ν`), using the given MA-round algorithm -/
  mstAlg : ℕ → Alg → Alg
  /-- [PRIOR] the approximate-SSSP algorithm of [37] (size bound `ν`), using the given MA-round and
  Eulerian-orientation algorithms -/
  approxAlg : ℕ → Alg → Alg → Alg
  /-- [PRIOR] the treatment of virtual nodes in Eulerian orientation of [37] (size bound `ν`,
  public bound `kb` on the number of virtual nodes: `eoAlg ν kb M P`), using the given MA-round
  algorithm and an algorithm for physical instances -/
  eoAlg : ℕ → ℕ → Alg → Alg → Alg

  -- ### Generic rules

  /-- [STD] weakening of the cost bounds -/
  mono : ∀ {A : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V} {t : Task V}
    {p p' : Prof V} {δ δ' : ℝ}, Impl A N t p δ → p ≤ p' → δ ≤ δ' → Impl A N t p' δ'

  /-- [STD] weakening of an output specification -/
  weaken : ∀ {A : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {ctx : Option (Overlays V)} {β : Type} {spec spec' : (V → β) → Prop} {p : Prof V} {δ : ℝ},
    (∀ o, spec o → spec' o) → Impl A N (.compute ctx β spec) p δ →
    Impl A N (.compute ctx β spec') p δ

  /-- [STD] weakening of an output specification (agents of an overlay; same participants) -/
  weakenIO : ∀ {A : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V} {E : Overlays V}
    {j sz : ℕ} {Pt : Finset V} {α β : Type} {x : Agent V → α} {R R' : (Agent V → β) → Prop}
    {p : Prof V} {δ : ℝ},
    (∀ y, R y → R' y) → Impl A N (.io E j sz Pt α β x R) p δ → Impl A N (.io E j sz Pt α β x R') p δ

  /-- [STD] sequencing with binding of intermediate results: the second algorithm starts with
  every agent holding its input together with its output of the first algorithm. The failure
  bound `δ'` of the continuation must be non-negative: if no output satisfies `R`, the second
  premise is vacuous, and a negative `δ'` would make the rule false (it would certify any `R'`,
  even an unsatisfiable one, with failure probability `δ + δ' < 1`). The same premise appears in
  every sequencing rule below (`embThen`, `decompThen`, `decompStep`, `g0Then`). Both phases
  have the same participants `Pt`, which halt together at the end of the first phase and start the
  second one together. -/
  bind : ∀ {A B : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V} {E : Overlays V}
    {j sz : ℕ} {Pt : Finset V} {α β γ : Type} {x : Agent V → α} {R : (Agent V → β) → Prop}
    {R' : (Agent V → γ) → Prop} {p q : Prof V} {δ δ' : ℝ},
    Impl A N (.io E j sz Pt α β x R) p δ →
    (∀ y, R y → Impl B N (.io E j sz Pt (α × β) γ (fun g => (x g, y g)) R') q δ') → 0 ≤ δ' →
    Impl (seq A B) N (.io E j sz Pt α γ x R') (p + q) (δ + δ')

  /-- [STD] a local call is free: if `B` solves the task on the locally computed values
  `F.f V g (lview N g) (x g)`, then `call F B` solves it from `x`, at the same cost. It replaces
  the former frame rule (additional local data does not hurt), which cannot hold for executable
  protocols: a protocol cannot take apart a value of an arbitrary product type. With the uniform
  projection `sndF Γ A`, `call (sndF Γ A) B` plays the role of the frame rule on data of the
  shape `Γ V × A V` (`Toolkit.frameCall`, `Basics.lean`). The participants are unchanged. -/
  callR : ∀ (F : LocFn) {B : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {E : Overlays V} {j sz : ℕ} {Pt : Finset V} {β : Type} (x : Agent V → F.α V)
    {R : (Agent V → β) → Prop} {p : Prof V} {δ : ℝ},
    Impl B N (.io E j sz Pt (F.β V) β (fun g => F.f V g (lview N g) (x g)) R) p δ →
    Impl (call F B) N (.io E j sz Pt (F.α V) β x R) p δ

  /-- [STD] local computation is free (for any participant set `Pt`; it takes no round) -/
  locR : ∀ (F : LocFn) {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (E : Overlays V)
    (j sz : ℕ) (Pt : Finset V) (x : Agent V → F.α V),
    Impl (loc F) N (.io E j sz Pt (F.α V) (F.β V) x
      (fun y => ∀ g, y g = F.f V g (lview N g) (x g))) 0 0

  -- ### The preprocessing (Section 3)

  /-- [STD] sequencing: first compute and embed the overlays, then use them -/
  embThen : ∀ {A B : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {Good : Overlays V → Prop} {β : Type} {spec : (V → β) → Prop} {p q : Prof V} {δ δ' : ℝ},
    Impl A N (.embedOverlays Good) p δ →
    (∀ E, Good E → Impl B N (.compute (some E) β spec) q δ') → 0 ≤ δ' →
    Impl (seq A B) N (.compute none β spec) (p + q) (δ + δ')

  /-- [STD] weakening of the property of the computed overlays -/
  embWeaken : ∀ {A : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {Good Good' : Overlays V → Prop} {p : Prof V} {δ : ℝ}, (∀ E, Good E → Good' E) →
    Impl A N (.embedOverlays Good) p δ → Impl A N (.embedOverlays Good') p δ

  /-- [STD] sequencing: decomposition, then construction of the overlays -/
  decompThen : ∀ {A B : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {GoodD : Finset (Finset (Sym2 V)) → Prop} {Good : Overlays V → Prop} {p q : Prof V} {δ δ' : ℝ},
    Impl A N (.decompose GoodD) p δ → (∀ cl, GoodD cl → Impl B N (.embedFrom cl Good) q δ') →
    0 ≤ δ' → Impl (seq A B) N (.embedOverlays Good) (p + q) (δ + δ')

  /-- [STD] start of the iterative decomposition of Lemma 2.10: every node initialises the
  residual edge set to its incident edges (so the residual edges are all edges of `G`) and the
  accumulated cluster list to empty, then runs `A` -/
  decompStart : ∀ {A : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {Good : Finset (Finset (Sym2 V)) → Prop} {p : Prof V} {δ : ℝ},
    Impl A N (.decompRest N.G.edgeFinset ∅ Good) p δ → Impl (dstart A) N (.decompose Good) p δ

  /-- [STD] end of the iterative decomposition (no residual edges left) -/
  decompBase : ∀ {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {Good : Finset (Finset (Sym2 V)) → Prop} {acc : Finset (Finset (Sym2 V))},
    Good acc → Impl skip N (.decompRest ∅ acc Good) 0 0

  /-- [STD] one step of the iterative decomposition: run `A` ([9] on the residual edges), update
  the residual edges (remove the edges of the found clusters) and the accumulated clusters (add
  the found clusters) locally from `A`'s output, then run `B` (continue on the crossing edges) -/
  decompStep : ∀ {A B : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {Good : Finset (Finset (Sym2 V)) → Prop} {GP : Finset (Finset (Sym2 V)) → Prop}
    {F : Finset (Sym2 V)} {acc : Finset (Finset (Sym2 V))} {φinv : ℕ} {p q : Prof V} {δ δ' : ℝ},
    Impl A N (.expDecompOnce F φinv GP) p δ →
    (∀ P, GP P → Impl B N (.decompRest (F \ P.biUnion id) (acc ∪ P) Good) q δ') → 0 ≤ δ' →
    Impl (dstep A B) N (.decompRest F acc Good) (p + q) (δ + δ')

  /-- [PRIOR] Lemma 2.8 (Chen–Meierhans–Probst Gutenberg–Saranurak [9]), run on the subgraph with
  edge set `F`: a vertex partition into `1/φinv`-expanders (conductance w.r.t. degrees inside the
  part; we keep the edge sets of the parts with at least one edge) with `Õ(1/φinv)·|F|` crossing
  edges, in `Õ(φinv⁴)` rounds and `Õ(φinv⁴ |F|)` messages. The algorithm is `A ν φinv`: the
  round budget `K·lg^k ν·φinv⁴` depends on `φinv`, so the nodes must know `φinv` to know when the
  run ends (all nodes take part and halt together). -/
  expDecomp : ∀ c : ℕ, ∃ (K k Kδ : ℕ) (A : ℕ → ℕ → Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (F : Finset (Sym2 V)) (φinv : ℕ),
    F ⊆ N.G.edgeFinset → 1 ≤ φinv →
    Impl (A ν φinv) N (.expDecompOnce F φinv
        (fun P => (∀ C ∈ P, C ⊆ F ∧ C.Nonempty ∧ IsExpander C φinv) ∧
        (∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint (nodes C) (nodes C')) ∧
        φinv * (F \ P.biUnion id).card ≤ K * lg ν ^ k * F.card))
      (Prof.mk (K * lg ν ^ k * φinv ^ 4) (onEdges F (2 * K * lg ν ^ k * φinv ^ 4))
        (K * lg ν ^ k * φinv ^ 4 * F.card))
      (whp Kδ c ν)

  /-- [STD] tree primitives [35] in a `1/polylog`-expander cluster `C` (diameter `polylog`): elect
  a leader and build a spanning tree of `C` by flooding the maximum ID, upcast and broadcast the
  `n_C` (ID, port, degree) triples over it, and select `A(C)` at the root. -/
  clusterSetup : ∀ Kφ kφ : ℕ, ∃ (K k : ℕ) (A : ℕ → Alg), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (ν : ℕ) (C : Finset (Sym2 V)) (φinv : ℕ),
    Fintype.card V ≤ ν → ν ≤ Fintype.card V → C ⊆ N.G.edgeFinset → C.Nonempty →
    IsExpander C φinv → φinv ≤ Kφ * lg ν ^ kφ →
    Impl (A ν) N (.clusterSetup C) (Prof.mk (K * lg ν ^ k * (nodes C).card)
      (onEdges C (2 * (K * lg ν ^ k * (nodes C).card))) (K * lg ν ^ k * (nodes C).card ^ 2)) 0

  /-- [IMPL] The random-walk construction of the virtual expander `G₀` (proof of Theorem 3.3),
  with parameters computed from `(n_C, m_C)` by `Rf` (tokens per port) and `tf` (rounds per step),
  and walk length `2ℓ`: every port of `P` sends `R` tokens over its edge (`R` rounds), the tokens
  perform `2ℓ` lazy random-walk steps with independent uniform seeds (each step allotted `t`
  rounds), every walk's final node keeps the token iff it entered through a port of `P`, and the
  survival is reported back along the reversed walk; nodes on a walk record its next hops. Every
  step sends at most two messages per edge and round, and every walk costs `O(ℓ)` messages. Unless
  the construction overflows (a step needs more than `t` rounds), the result is the multigraph
  `rwG0` on `P`, algorithmically embedded along the walks (`G0Model.lean`); the task
  `.buildG0 C P Good` asks that its true parameters satisfy `Good`. Claims 3.4/3.5 are proved from
  this and `Mixing` in `G0.lean`.
  The nodes cannot compute the true parameters of `G₀` (its conductance, congestion and size are
  global quantities), so they output the *public* parameters `gf (n_C, m_C)`, which must satisfy
  `Good` (premise); the construction fails if `G₀` does not meet them (`TrueParams` is part of the
  failure event).
  A token carries its walk index `i < R` (to select its seed) and the path position of its
  crossing (`≤ 2ℓ`); with words of `O(log n)` bits this takes `O(log_n (R + ℓ))` words, so the
  constant `Kc` depends on an exponent `kB` with `R + 2ℓ + 2 ≤ (n + 4)^kB` (premise). -/
  rwLink : ∀ kB : ℕ, ∃ Kc : ℕ, ∀ (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data)
    {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (C : Finset (Sym2 V)) (P : Finset (Port V))
    (Good : G0Data → Prop),
    C ⊆ N.G.edgeFinset → C.Nonempty → P ⊆ allPorts C → Good (gf (nodes C).card C.card) →
    Rf (nodes C).card C.card + 2 * ℓ + 2 ≤ (Fintype.card V + 4) ^ kB →
    Impl (rwAlg Rf ℓ tf gf) N (.buildG0 C P Good)
      (Prof.mk (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1))
        (onEdges C (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1)))
        (Kc * (P.card * Rf (nodes C).card C.card * (ℓ + 1))))
      (rwProb C P (Rf (nodes C).card C.card) ℓ (fun ω =>
        rwOverflow C P (Rf (nodes C).card C.card) ℓ (tf (nodes C).card C.card) ω ∨
        ¬ TrueParams C P (Rf (nodes C).card C.card) ℓ ω (gf (nodes C).card C.card)))

  /-- [PRIOR+] Lemma 3.2 via Ghaffari–Kuhn–Su [19] with the constant hierarchy depth `h` of
  Chang–Saranurak [7, §3], with `ε = 1`, run on the embedded virtual expander `G₀` via Lemma 2.2
  (random delays [17]): preprocessing in `Õ(n₀)` rounds and `Õ(m₀ n₀)` messages of `G₀`, then
  delivery of a demand of known load `λ` and size `M` in `Õ(λ)` rounds and `Õ(M)` messages of
  `G₀`; each `G₀`-round costs `Õ(cong + dil)` rounds of `G` and each `G₀`-message `dil` messages of
  `G`. With constant `h`, the preprocessing `τ(hβ lg^{O(h)} + hβ² lg)`, `β = m₀^{1/h}`, of
  [19, 7] is `Õ(n₀)`. Recorded routes are walks inside `C` between the endpoints of their packets,
  and each edge carries at most `2·rounds` packets (bandwidth).
  **Structure of the routes** (`RoutesHier`): the routes are produced by the forwarding procedure
  of [19, §3.2] on a routing hierarchy of depth `h` (`Hier`, `Hier.Gen`, `Hier.Route`). Mapping
  each component: the per-level dilation `b = Kb·lg^kb ν` is that of the embeddings of
  [19, Lemmas 3.1–3.4]; `τ = Kτ·(φ(G₀)⁻¹ + 1)²·lg ν` bounds the mixing-length walks of the
  random-graph overlay (and the initial redistribution walk), `O(φ⁻² log(m₀ n))`, which is
  polylog because `n₀ ≤ Kφ·n` and `m₀ ≤ Kφ lg^kφ n·n₀`; `dil` is the dilation of the embedding of
  `G₀` into `C`. The per-route length bound `RoutesOK.len`, `dil·τ·(1 + (2b + 1)^h (b + 1))`,
  i.e. `Õ(dil)` (every packet crosses `polylog` edges of `G₀`, as used in Lemma 3.9), is no longer
  assumed but derived (`RoutesHier.routesOK`).
  **Strengthened** (`[PRIOR+]`): the paper's statement of Lemma 3.2 bounds only rounds and the
  total number of messages; what remains a strengthening relative to it is that the contract
  exposes this structure of the routes (to be checked against [19, 7]).
  As in its only use (Theorem 3.3), the cluster `C` is a `1/polylog`-expander (inverse conductance
  `φC`), `P` consists of ports of `C`, and `G₀` has polynomial size (`n₀ ≤ Kφ·n`) and `Õ(n₀)`
  edges. Without the first two hypotheses the postcondition can be unsatisfiable: on a path
  cluster, a `G₀` of conductance `1/3` whose consecutive ports are joined by exponentially many
  parallel edges would force routes of length `Θ(n)` (`SatModel.lean` proves the postcondition
  satisfiable under these hypotheses). The bounds of [19, 7] depend on the size of `G₀` through
  its mixing time, hence the bounds on `n₀` and `m₀`. Every packet carries a payload of at most
  `pw` words (numbers `≤ n + 3`), delivered to its destination; the constants may depend on `pw`.
  The size `g.n0` of `G₀` is a public upper bound on `|P|`.
  Every node on a recorded route learns the whole route (`rkAt` in the CONGEST semantics; the
  overlays of Theorem 3.10 are built from these routes, and a node knows the embedded paths
  through it). [19, 7] deliver packets; to record the routes, a packet appends every hop to its
  header, and the destination sends the completed route back along it. A route has
  `L ≤ dil·τ·(1 + (2b + 1)^h (b + 1)) ≤ K·lg^k ν·dil` hops, so a packet then has `O(L)` words:
  this multiplies the rounds by `O(L / lg^k)`, i.e. by the factor `dil + 1`, and the messages per
  packet by `O(L)`, i.e. by `dil + 1` once more. Hence rounds `Õ((n₀ + λ)(cong + dil)(dil + 1))`
  and messages `Õ((m₀n₀ + M)(dil + 1)²)` (at the use, Theorem 3.3, `dil` is polylog). -/
  routeG0 : ∀ (c Kφ kφ pw : ℕ), ∃ (K k Kδ h Kb kb Kτ : ℕ) (A : ℕ → Alg), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (C : Finset (Sym2 V))
    (P : Finset (Port V)) (φC : ℕ) (g : G0Data) (D : Demand V) (lam : ℕ), C ⊆ N.G.edgeFinset →
    IsExpander C φC → φC ≤ Kφ * lg ν ^ kφ → P ⊆ allPorts C →
    P.card ≤ g.n0 → g.n0 ≤ Kφ * ν → g.m0 ≤ Kφ * lg ν ^ kφ * g.n0 → g.φinv ≤ Kφ * lg ν ^ kφ →
    D.SupportedOn P → (∀ x, D.load x ≤ lam) →
    Impl (A ν) N (.routeViaG0 C P g D lam pw (fun r => RoutesHier C D r
        (2 * (K * lg ν ^ k * (g.n0 + lam) * (g.cong + g.dil)))
        h (Kb * lg ν ^ kb) (Kτ * (g.φinv + 1) ^ 2 * lg ν) g.dil))
      (Prof.mk (K * lg ν ^ k * (g.n0 + lam) * (g.cong + g.dil) * (g.dil + 1))
        (onEdges C (2 * (K * lg ν ^ k * (g.n0 + lam) * (g.cong + g.dil) * (g.dil + 1))))
        (K * lg ν ^ k * (g.m0 * g.n0 + D.size) * (g.dil + 1) ^ 2))
      (whp Kδ c ν)

  /-- [STD] sequencing: build `G₀`, then route through it -/
  g0Then : ∀ {A B : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {C : Finset (Sym2 V)} {P : Finset (Port V)} {D : Demand V} {lam pw : ℕ} {GG : G0Data → Prop}
    {GR : Routes V → Prop} {p q : Prof V} {δ δ' : ℝ},
    Impl A N (.buildG0 C P GG) p δ → (∀ g, GG g → Impl B N (.routeViaG0 C P g D lam pw GR) q δ') →
    0 ≤ δ' → Impl (seq A B) N (.route C P D lam pw GR) (p + q) (δ + δ')

  /-- [STD] weakening of the recorded-route property (routing through `G₀`) -/
  routeViaWeaken : ∀ {A : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {C : Finset (Sym2 V)} {P : Finset (Port V)} {g : G0Data} {D : Demand V} {lam pw : ℕ}
    {GR GR' : Routes V → Prop} {p : Prof V} {δ : ℝ}, (∀ r, GR r → GR' r) →
    Impl A N (.routeViaG0 C P g D lam pw GR) p δ → Impl A N (.routeViaG0 C P g D lam pw GR') p δ

  /-- [STD] weakening of the recorded-route property -/
  routeWeaken : ∀ {A : Alg} {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    {C : Finset (Sym2 V)} {P : Finset (Port V)} {D : Demand V} {lam pw : ℕ}
    {GR GR' : Routes V → Prop} {p : Prof V} {δ : ℝ},
    (∀ r, GR r → GR' r) → Impl A N (.route C P D lam pw GR) p δ →
    Impl A N (.route C P D lam pw GR') p δ

  /-- [IMPL] the construction of Theorem 3.10: run, in every cluster in parallel (the clusters are
  edge-disjoint and each cluster's work only uses its own edges), the cluster setup, the topology
  collection of Lemma 3.8 and the dummy-packet routing of Lemma 3.9; every node records the next
  hops of the routes through it. Then all `n` IDs are gathered and broadcast over a BFS tree of the
  union of the clusters' spanning trees (`O(n)` rounds, `O(n²)` messages, `O(n)` load per edge).
  Every node now knows `n` and all IDs, and the overlays are `construct cl r` for the recorded
  routes `r`; the dilation `E.dil` and the overlap `E.ov` of the embedding are computed by a
  convergecast and broadcast over the same tree (within the same `O(n)` bounds), so they are
  public. The parallel execution requires the clusters to be pairwise edge-disjoint (explicit
  premise).
  The topology packets of Lemma 3.8 carry the described edge and its weight (`wexp + 2` words: the
  weights are at most `n^wexp`, premise); the recorded dummy routes of Lemma 3.9 are walks inside
  the cluster from the source node to the port's node, of length at most `n^Lb` (premise), so that
  the dilation fits in `Lb + 1` words. -/
  embedConstruct : ∀ Lb wexp : ℕ, ∃ K : ℕ, ∀ (A₁ A₂ A₃ : Alg) {V : Type} [Fintype V]
    [DecidableEq V]
    {N : WNet V} (cl : Finset (Finset (Sym2 V))) (p₁ p₂ p₃ : Finset (Sym2 V) → Prof V)
    (δ₁ δ₂ δ₃ : Finset (Sym2 V) → ℝ) (GR : Finset (Sym2 V) → Routes V → Prop)
    (Good : Overlays V → Prop),
    (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp) →
    (∀ e ∈ N.G.edgeFinset, ∃ C ∈ cl, e ∈ C) →
    (∀ C ∈ cl, C ⊆ N.G.edgeFinset ∧ C.Nonempty) →
    (∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C') →
    (∀ C ∈ cl, Impl A₁ N (.clusterSetup C) (p₁ C) (δ₁ C)) →
    (∀ C ∈ cl, Impl A₂ N (.route C (topoP C) (topoDemand C) (6 * (nodes C).card) (wexp + 2)
      (fun _ => True)) (p₂ C) (δ₂ C)) →
    (∀ C ∈ cl, Impl A₃ N (.route C (portsP C) (portsDemand C) (3 * (nodes C).card) 0 (GR C))
      (p₃ C) (δ₃ C)) →
    (∀ C ∈ cl, ∀ e ∉ C, (p₁ C + p₂ C + p₃ C).load e = 0) →
    (∀ C ∈ cl, ∀ r, GR C r → ∀ v ∈ nodes C, ∀ q ∈ portsA C,
      IsEdgeWalk (r (srcPort C v, q)) v q.1 ∧ (∀ e ∈ r (srcPort C v, q), e ∈ C) ∧
      (r (srcPort C v, q)).length ≤ Fintype.card V ^ Lb) →
    (∀ r : Finset (Sym2 V) → Routes V, (∀ C ∈ cl, GR C (r C)) → Good (construct cl r)) →
    Impl (clusterPar Lb wexp A₁ A₂ A₃) N (.embedFrom cl Good)
      (Prof.mk (cl.sup (fun C => (p₁ C + p₂ C + p₃ C).rounds) + K * Fintype.card V)
        (∑ C ∈ cl, (p₁ C + p₂ C + p₃ C).load + fun _ => K * Fintype.card V)
        (∑ C ∈ cl, (p₁ C + p₂ C + p₃ C).msgs + K * Fintype.card V ^ 2))
      (∑ C ∈ cl, (δ₁ C + δ₂ C + δ₃ C))

  -- ### Building blocks of the shortest-path phase

  /-- [IMPL] Lemma 2.2 on the aggregator edges of `S` in `L_j` (node-to-aggregator direction):
  every node of `S` sends one message of `≤ μ` words to all its aggregators in `L_j`. The phase
  has the public round budget `K·lg^k ν·(μ+1)·(E.dil+1)·(sz+1)`, which depends only on public
  quantities (`ν`, `μ`, the size bound `sz ≥ |S|` of the task and the dilation of the embedding):
  the embedded paths of `S` have congestion `≤ E.dil·|S|` (the clusters are disjoint) and length
  `≤ E.dil`, so random delays [17] deliver every message within the budget. The message size `μ`
  must be known to the participants to compute this budget, so it is a parameter of the algorithm
  (`A ν μ`). The participants `Pt` contain the footprint of `S` (the nodes of `S`, the relays on
  their aggregator paths and the hosts of their aggregators), which is where the messages travel;
  as participants, the relays and the hosts know `sz`, hence when the phase ends. An aggregator
  that receives no message holds the empty table, which is its correct output (in particular the
  aggregators hosted outside `Pt`, which are not simulated, have no node of `S`: by `EmbValid`, the
  host of an aggregator of a node `v` is the endpoint of the path of `v`).
  Every message over an embedded path of length `ℓ` costs `O(μ + 1)` words per edge: its numbers
  are at most `ν^Bw` with `ν = n`, so each takes `O(Bw)` words of `O(log n)` bits (see "The size
  bound" in the module docstring), and a header names the path; hence the constant `K` in the
  load and the message count. -/
  aggUp : ∀ c Bw : ℕ, ∃ (K k Kδ : ℕ) (A : ℕ → ℕ → Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V)
    (μ : ℕ) (x : Agent V → Option (Msg V)), EmbValid N.G E → j < Fintype.card V → S.card ≤ sz →
    footprint E j S ⊆ Pt →
    (∀ v, x (.inl v) ≠ none → v ∈ S) → (∀ v m, x (.inl v) = some m → m.Small μ (ν ^ Bw)) →
    Impl (A ν μ) N (.io E j sz Pt (Option (Msg V)) (V → Option (Msg V)) x
      (fun y => ∀ C ∈ E.cl, ∀ v, y (.inr C) v = if v ∈ nodes C then x (.inl v) else none))
      (Prof.mk (K * lg ν ^ k * (μ + 1) * (E.dil + 1) * (sz + 1)) ((K * (μ + 1)) • E.rhoAgg j S)
        (K * (μ + 1) * E.aggLen j S))
      (whp Kδ c ν)

  /-- [IMPL] Lemma 2.2 on the aggregator edges of `S` in `L_j` (aggregator-to-node direction):
  the aggregator of every cluster `C` sends one message of `≤ μ` words to (some of) the nodes of
  `C ∩ S`; every node receives the multiset of messages sent to it. Same public round budget as
  `aggUp`, hence the same reason for the parameter `μ` (`A ν μ`: the message size must be known to
  the participants); an aggregator that sends holds data of the task, which carries `sz`. The
  participants `Pt` contain the footprint of `S`. As in `aggUp`, `ν = n` bounds the numbers in the
  messages. -/
  aggDown : ∀ c Bw : ℕ, ∃ (K k Kδ : ℕ) (A : ℕ → ℕ → Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V)
    (μ : ℕ) (x : Agent V → V → Option (Msg V)), EmbValid N.G E → j < Fintype.card V →
    S.card ≤ sz → footprint E j S ⊆ Pt →
    (∀ C ∈ E.cl, ∀ v, x (.inr C) v ≠ none → v ∈ S ∧ v ∈ nodes C) →
    (∀ C ∈ E.cl, ∀ v m, x (.inr C) v = some m → m.Small μ (ν ^ Bw)) →
    Impl (A ν μ) N (.io E j sz Pt (V → Option (Msg V)) (Multiset (Msg V)) x
      (fun y => ∀ v, y (.inl v) = (clustersOf E.cl v).val.filterMap (fun C => x (.inr C) v)))
      (Prof.mk (K * lg ν ^ k * (μ + 1) * (E.dil + 1) * (sz + 1)) ((K * (μ + 1)) • E.rhoAgg j S)
        (K * (μ + 1) * E.aggLen j S))
      (whp Kδ c ν)

  /-- [STD] one round of direct messages: every node `v` of `S` sends one message to each node
  of `x v` (neighbours `u` with `s(v,u) ∈ F`); every node learns which nodes notified it. The
  senders and the receivers take part (`S ⊆ Pt`, and every receiver is in `Pt`). -/
  notify : ∃ A : Alg, ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (E : Overlays V)
    (j sz : ℕ) (Pt S : Finset V) (F : Finset (Sym2 V)) (x : Agent V → Finset V),
    (∀ v, ∀ u ∈ x (.inl v), v ∈ S ∧ N.G.Adj v u ∧ s(v, u) ∈ F) →
    (∀ v, ∀ u ∈ x (.inl v), u ∈ Pt) → S ⊆ Pt →
    Impl A N (.io E j sz Pt (Finset V) (Finset V) x
      (fun y => ∀ v, y (.inl v) = univ.filter (fun u => v ∈ x (.inl u))))
      (Prof.mk 1 (onEdges F 2) (2 * F.card)) 0

  /-- [PRIOR] Gallager–Humblet–Spira [16] on the subgraph `(S, F)` (every node of `S` knows its
  `F`-neighbours): a rooted spanning forest of `(S, F)` (one tree per component, rooted at its
  leader) in `O(|S| log n)` rounds, `O(|F| + |S| log n)` messages, `O(log n)` messages per edge.
  It only uses edges inside `S`, so it suffices that the nodes of `S` take part (`S ⊆ Pt`). -/
  ghs : ∃ (K : ℕ) (A : ℕ → Alg), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (ν : ℕ),
    Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (F : Finset (Sym2 V))
    (x : Agent V → Option (Finset V)), F ⊆ N.G.edgeFinset → (∀ e ∈ F, ∀ v ∈ e, v ∈ S) →
    S.card ≤ sz → S ⊆ Pt → (∀ v, x (.inl v) = if v ∈ S then some (nbrsIn F v) else none) →
    Impl (A ν) N (.io E j sz Pt (Option (Finset V)) (Option V × V) x
      (fun y => SpanForest S F (fun v => (y (.inl v)).1) (fun v => (y (.inl v)).2)))
      (Prof.mk (K * lg ν * (sz + 1)) (onEdges F (K * lg ν)) (K * lg ν * (F.card + S.card))) 0

  /-- [STD] tree convergecast followed by broadcast [35] of `b`-word values on a rooted forest of
  `G[S]` (depth `≤ |S|`), with an arbitrary aggregation operator: every node learns an
  `op`-aggregate of the values of its tree (the same in the whole tree). The value size `b` is a
  parameter of the algorithm (`A ν b`): the round budget `K·(b+1)·(sz+1)` depends on `b`, and every
  node must know `b` to know when the phase ends, which sequential composition requires. The
  numbers in the values are at most `ν^Bw` with `ν ≤ n` (see "The size bound" in the module
  docstring). It only uses edges inside `S`, so it suffices that the nodes of `S` take part
  (`S ⊆ Pt`). -/
  treeCast : ∀ Bw : ℕ, ∃ (K : ℕ) (A : ℕ → ℕ → Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), ν ≤ Fintype.card V →
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
    Impl (A ν b) N (.io E j sz Pt (Option (Option V × V × Msg V × (Msg V → Msg V → Msg V)))
        (Option (Msg V)) x
      (fun y => ∀ v ∈ S, ∃ Y, y (.inl v) = some Y ∧
        AggOf op ((S.filter (fun u => root u = root v)).val.map val) Y ∧
        ∀ u ∈ S, root u = root v → y (.inl u) = some Y))
      (Prof.mk (K * (b + 1) * (sz + 1)) (onEdges Fp (K * (b + 1))) (K * (b + 1) * (S.card + 1)))
      0

  /-- [PRIOR + IMPL] Hirschberg–Sinclair ring leader election [23] (`O(log r)` messages per link of
  a ring of size `r`) on every ring of the segment graph, followed by a broadcast of the chosen
  direction along the ring; each segment (ring link) is simulated by the two aggregator edges
  through the aggregator of its cluster, with asynchronous FIFO forwarding over the embedded paths
  (proof of Lemma 5.3). Since every aggregator edge serves at most one segment end (`RingWF`), it
  carries `O(log n)` messages; since at least one message moves in every round, the number of rounds
  is at most the number of messages, which is at most the public budget
  `K·lg ν·(E.ov+1)·(E.dil+1)·(sz+1)`. The messages travel over the aggregator paths of `S`, so the
  participants contain the footprint of `S`. -/
  ringLE : ∃ (K : ℕ) (A : ℕ → Alg), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V)
    (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (r : V → RingIn V)
    (x : Agent V → RingIn V), EmbValid N.G E → j < Fintype.card V → RingWF E.cl S r →
    S.card ≤ sz → footprint E j S ⊆ Pt → (∀ v, x (.inl v) = r v) →
    Impl (A ν) N (.io E j sz Pt (RingIn V) (List Bool) x
      (fun y => RingSpec r (fun v => y (.inl v))))
      (Prof.mk (K * lg ν * (E.ov + 1) * (E.dil + 1) * (sz + 1)) ((K * lg ν) • E.rhoAgg j S)
        (K * lg ν * E.aggLen j S)) 0

  /-- [IMPL] sequential execution of `B` on the connected components `K` of `G[S]`, `S ⊆ P`, with
  `P` connected. Agents hold `((v ∈ P, v ∈ S), data)`; `B` runs on `K` with `(v ∈ K, data)`, the
  public size bound `|K|` and the participants `footprint E j K` (every component runs on its own
  footprint, which is what makes the sequential execution implementable). The specifications `R K`
  only concern the nodes of `K`. The participants of the whole are the footprint of `P`.
  The algorithm `perComp A Bt Am B` is given the type families `A` of the data and `Bt` of the
  outputs (`α = A V`, `β = Bt V`): a protocol cannot take apart a value of an arbitrary product
  type (to pass `(v ∈ K, data)` to `B` it must project `((v ∈ P, v ∈ S), data)`), and an agent that
  is in no component (if `S = ∅`, or a node outside `S`) must output *some* value of type `Bt V`
  without receiving one from `B`. As for the other contracts on aggregator paths (`aggUp`,
  `ringLE`), the embedding is valid (`EmbValid`) and `j < n`: the announcements travel along the
  embedded paths, which must be walks in `G` starting at their sources, so that the whole footprint
  can be reached and halt together.
  Implementation and accounting (the paper does not describe this coordination):
  * the MST computation `Am` on `P` gives a spanning tree of `P` (cost `pm`); the MST computation
    `Am` on `S` gives a spanning forest of `G[S]` with one rooted tree and leader per component
    (cost `pm'`); both run on the footprint of `P`;
  * every component computes `|K|` by a convergecast and broadcast on its tree; the components
    are node-disjoint and their tree edges are direct edges of `G[S]`, so this runs in parallel
    in `O(sz)` rounds and `O(|S|)` messages;
  * a token traverses the tree of `P` depth-first (`O(|P|)` rounds and messages); when it reaches
    the leader of a component `K`, the leader broadcasts the start time on `K`'s tree, and every
    node of `K` announces it along its aggregator paths, so the whole footprint of `K` (the nodes
    of `K`, the relays on their paths and the hosts of their aggregators) starts `B` in the same
    round. An announcement packet carries its source (to be routed along the source's path),
    `|K|` (the public size bound of `B`, needed by the relays) and the leader (a relay must know
    whether it belongs to `K`), so it has a constant number `O(1)` of words: the announcements
    cost `O(aggLen j K)` messages and put load `O(rhoAgg j K)` on every edge; hop-synchronised,
    they finish within `O(E.dil·|K|)` rounds, and over all components this gives
    `O(aggLen j S) ≤ O(aggLen j P)` messages and `O((E.dil+1)·(sz+1))` rounds. Then `B` runs on
    the footprint of `K`, within its budget, which is public within that footprint (a function of
    `|K|`); the token waits until `B` halts and moves on. Meanwhile the nodes of
    `footprint E j P` outside the running component are idle;
  * at the end of the traversal, the root of `P`'s tree announces the end on `P`'s tree and along
    `P`'s aggregator paths, so the whole footprint of `P`, including the path relays, halts in the
    same round (`O(|P|) + O(aggLen j P)` messages, `O((E.dil+1)·(sz+1))` rounds).
  All budgets are public within the participants: the overhead budget depends only on `E.dil` and
  `sz`, and the budget of each component is announced with its start. Hence the overhead is
  `O((E.dil+1)²(sz+1))` rounds, load `O(ρ^P)` (tree edges are edges of `G` incident to `P`,
  announcement paths are aggregator paths of `S ⊆ P` and of `P`) and
  `O(|P| + 1) + O(aggLen j P)` messages (the start announcements on the components' paths and the
  end announcement on `P`'s paths); it is deterministic. The output type is inhabited
  (`[Nonempty (Bt V)]`): if `S = ∅` no component runs, and the agents still have to hold an
  output. -/
  perCompR : ∃ K₀ : ℕ, ∀ (A Bt : Type → Type) (Am B : Alg) {V : Type} [Fintype V] [DecidableEq V]
    [Nonempty (Bt V)] (N : WNet V) (E : Overlays V) (j sz : ℕ) (P S : Finset V)
    (z : Agent V → A V) (R : Finset V → (Agent V → Bt V) → Prop) (pm pm' : Prof V) (δm δm' : ℝ)
    (p : Finset V → Prof V) (δ : Finset V → ℝ),
    EmbValid N.G E → j < Fintype.card V →
    S ⊆ P → ConnSet N.G P → P.card ≤ sz →
    (∀ K y y', (∀ v ∈ K, y (.inl v) = y' (.inl v)) → R K y → R K y') →
    Impl Am N (.mst E j sz (footprint E j P) P) pm δm →
    Impl Am N (.mst E j sz (footprint E j P) S) pm' δm' →
    (∀ K ∈ comps N.G S, Impl B N (.io E j K.card (footprint E j K) (Bool × A V) (Bt V)
      (fun g => (memAg K g, z g)) (R K)) (p K) (δ K)) →
    Impl (perComp A Bt Am B) N (.io E j sz (footprint E j P) ((Bool × Bool) × A V) (Bt V)
        (fun g => ((memAg P g, memAg S g), z g)) (fun y => ∀ K ∈ comps N.G S, R K y))
      (pm + pm' + ∑ K ∈ comps N.G S, p K +
        Prof.mk (K₀ * (E.dil + 1) ^ 2 * (sz + 1)) (fun e => K₀ * E.rho N.G j P e)
          (K₀ * (P.card + 1) + K₀ * E.aggLen j P))
      (δm + δm' + ∑ K ∈ comps N.G S, δ K)

  /-- [PRIOR] MST (hence leader election and spanning trees per component) in `O(log n)`
  Minor-Aggregation rounds with `O(1)`-word values (GHS in the Minor-Aggregation model [16, 38]).
  The participants contain the footprint of `S`; the Minor-Aggregation rounds run with the same
  participants. -/
  mstRed : ∃ K : ℕ, ∀ (M : Alg) {V : Type} [Fintype V] [DecidableEq V] {N : WNet V} (ν : ℕ),
    Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (p : Prof V) (δ : ℝ),
    S.card ≤ sz → footprint E j S ⊆ Pt →
    (∀ I : MAInst V, I.S ⊆ S → I.Small K (ν ^ K) → Impl M N (maTask N.G E j sz Pt I) p δ) →
    Impl (mstAlg ν M) N (.mst E j sz Pt S) ((K * lg ν) • p) (((K * lg ν : ℕ) : ℝ) * δ)

  /-- [PRIOR] Lemma 5.1 (Rozhoň–Grunau–Haeupler–Zuzic–Li [37]) with `ε = 1/2`, on a connected set
  `S` with a virtual source: `3/2`-approximate SSSP (distances and an approximate shortest-path
  tree) on `G[S]` reduces to `polylog` Minor-Aggregation rounds (with `polylog`-word values whose
  numbers are polynomial in `ν` and the weights) and `polylog` Eulerian-orientation instances on
  graphs `H ⊆ G[S] + polylog` virtual nodes. The participants contain the footprint of `S`; the
  sub-tasks run with the same participants. -/
  approxRed : ∀ Bw : ℕ, ∃ K k : ℕ, ∀ (M Eo : Alg) {V : Type} [Fintype V] [DecidableEq V]
    {N : WNet V} (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V)
    (w0 : V → Option (ℕ × V)) (pM pE : Prof V) (δM δE : ℝ),
    ConnSet N.G S → S.card ≤ sz → footprint E j S ⊆ Pt → (∀ e ∈ N.G.edgeFinset, N.w e ≤ ν ^ Bw) →
    (∀ v c p, w0 v = some (c, p) → c ≤ ν ^ Bw) →
    (∀ I : MAInst V, I.S ⊆ S → I.Small (K * lg ν ^ k) (ν ^ (K * (Bw + 1))) →
      Impl M N (maTask N.G E j sz Pt I) pM δM) →
    (∀ H : EOInst V, H.S = S → H.WF N.G → H.k ≤ K * lg ν ^ k →
      Impl Eo N (eoTask E j sz Pt H) pE δE) →
    Impl (approxAlg ν M Eo) N (.io E j sz Pt (SubIn V) (Option (ℕ × V)) (subInput S w0)
        (fun y => ApproxSpec N S w0 (fun v => y (.inl v))))
      ((K * lg ν ^ k) • (pM + pE)) (((K * lg ν ^ k : ℕ) : ℝ) * (δM + δE))

  /-- [PRIOR] the technique of [37] for the virtual nodes of an Eulerian-orientation instance, as
  recalled in the proof of Lemma 5.3 ("With Virtual Nodes"), on a connected set `S` with `k`
  virtual nodes: `k` phases of spanning forests and path pairings ([37, Lemma 6.4]) in
  `polylog` Minor-Aggregation rounds on forests of `G[S]`, an orientation of the resulting
  virtual multigraph from `O(k²)` counts aggregated over a spanning tree of `S`, and threshold
  labels found by `O(log n)` convergecasts of `O(k²)` words. This orients all virtual edges and some
  physical edges consistently; the remaining physical edges form an even-degree subgraph of the
  physical part, which is oriented by the given algorithm for physical instances.
  The number `k` of virtual nodes is not public, while the number of phases and the sizes of the
  convergecasts determine the round budget, which the participants must be able to compute. Hence
  the algorithm `eoAlg ν kb M P` takes a public bound `kb ≥ k` on the number of virtual nodes,
  and the number of phases and all sizes are stated in terms of `kb`.
  The Minor-Aggregation instances used are small *at every size level* `b ≥ K·lg^k ν·(kb+1)²`
  (their values have at most `K·lg^k ν·(kb+1)²` words, and their operators preserve every larger
  word bound), so that they can be run by the MA-round algorithm `M` of any public value size
  `b` above this threshold (Lemma 4.2 runs `A ν b`; `MAInst.Small b B` is not monotone in `b`).
  The participants contain the footprint of `S`; the sub-tasks run with the same participants. -/
  eoVirt : ∃ K k : ℕ, ∀ (M P : Alg) {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt : Finset V) (H : EOInst V) (kb : ℕ) (pM pP : Prof V)
    (δM δP : ℝ), ConnSet N.G H.S → H.WF N.G → H.S.card ≤ sz → H.k ≤ kb →
    footprint E j H.S ⊆ Pt →
    (∀ I : MAInst V, I.S ⊆ H.S → (∀ b, K * lg ν ^ k * (kb + 1) ^ 2 ≤ b → I.Small b (ν ^ K)) →
      Impl M N (maTask N.G E j sz Pt I) pM δM) →
    (∀ H' : EOInst V, H'.S = H.S → H'.Physical → H'.Hp ⊆ H.Hp → H'.WF N.G →
      Impl P N (eoTask E j sz Pt H') pP δP) →
    Impl (eoAlg ν kb M P) N (eoTask E j sz Pt H)
      ((K * lg ν ^ k * (kb + 1) ^ 2) • (pM + Prof.mk (sz + 1) (fun e => E.rho N.G j H.S e)
        (H.S.card + 1)) + pP)
      (((K * lg ν ^ k * (kb + 1) ^ 2 : ℕ) : ℝ) * δM + δP)

  /-- [PRIOR] random-delay scheduling [17] (Ghaffari, PODC'15, Theorem 1.1; Leighton–Maggs–Rao):
  `n` instances with dilation `≤ D` and combined per-edge load `≤ C` can be executed
  simultaneously in `O(C + D·log n)` rounds, w.h.p., if the nodes share the random delays of the
  instances; outputs are paired. Instance `s` runs on overlay `rank(s)` with public size bound `n`
  (every node knows `n`) and all nodes as participants (`Pt = univ`), and every agent knows its tag
  `s`. The scheduler's round budget `K·lg^k ν·(Cg + R + ν)` must be computable by all nodes, so the
  algorithm `sched c ν R Cg A` takes public bounds `R` on the rounds of every instance and `Cg` on
  the congestion (the combined load of the instances on every edge), which the instances must
  satisfy.

  Costs: [17] does not count messages, and in this model a message is one word, so the overhead is
  multiplicative (`K·lg^k ν` times the instances' loads and messages), plus a setup on `G`:
  * every scheduled message carries the tag `s` of its instance (the receiver needs it to assign
    the message to an instance), so it takes `O(1)` words; with a fixed word size, the instances'
    loads and messages cannot simply add up (an instance's messages may carry `Θ(log n)` bits of
    information each, and the tags another `log n` bits);
  * the shared delays: a BFS tree of `G` from the smallest ID by flooding (`n` rounds, `O(m)`
    messages; `G` is connected), then every node draws the delay of its instance, and the `n`
    delays are gathered at the root and broadcast on the tree, pipelined. This uses no property
    of the overlays. A delay lies in a range of size `≤ Cg + R`, and a word holds a number
    `≤ n + 3`, so the contract asks `R + Cg ≤ (n+4)^kB` for an exponent `kB` (as `rwLink` does):
    a delay is then `kB` words (its digits in base `n+4`), the gathering and broadcast take
    `O(kB·n)` rounds, `O(kB·n)` words per tree edge and `O(kB·n²)` messages, and the constants
    depend on `kB`. In Theorem 5.6, `R` and `Cg` are `Õ(n)`.
  So the load is `≤ K·lg^k ν·(∑ load + ν)` and the messages `≤ K·lg^k ν·(∑ msgs + ν²)`. -/
  schedule : ∀ c kB : ℕ, ∃ K k Kδ : ℕ, ∀ (A : Alg) {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (β : Type) (R Cg : ℕ)
    (spec : V → (V → β) → Prop) (p : V → Prof V) (δ : V → ℝ),
    R + Cg ≤ (ν + 4) ^ kB →
    (∀ s, Impl A N (.io E (Fintype.equivFin V s : ℕ) (Fintype.card V) univ V β (fun _ => s)
      (fun y => spec s (fun v => y (.inl v)))) (p s) (δ s)) →
    (∀ s, (p s).rounds ≤ R) → (∀ e, ∑ s, (p s).load e ≤ Cg) →
    Impl (sched c ν R Cg A) N (.compute (some E) (V → β) (fun o => ∀ s, spec s (fun v => o v s)))
      (Prof.mk (K * lg ν ^ k * (Cg + R + ν))
        ((K * lg ν ^ k) • (∑ s, (p s).load + fun _ => ν))
        (K * lg ν ^ k * (∑ s, (p s).msgs + ν ^ 2)))
      (∑ s, δ s + whp Kδ c ν)

end APSP.Stoc
