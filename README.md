# Lean formalization of "Near-Singularly Optimal Distributed APSP" (STOC submission)

The paper: Fabien Dufoulon, Shreyas Pai, Gopal Pandurangan, Peter Robinson and Jacob Way,
*Near-Singularly Optimal Distributed APSP*, STOC submission of November 5, 2026. Theorem numbers
refer to this version.

Lean 4.35.0 + Mathlib v4.35.0. Build with `lake build` (fetch the Mathlib cache first with
`lake exe cache get`).

The formalization is the library **`ApspStoc/`**: the main theorem of the paper, Theorem 5.6
(= Theorem 1.1). It assumes standard facts about CONGEST, theorems of prior work, and explicitly
tagged implementation assumptions (including the paper's Lemma 2.2). The paper's other lemmas and
claims, including the probabilistic Claims 3.4/3.5, are proved. It depends only on Mathlib. The
basic definitions (weighted networks, distances, the APSP specification, cost profiles, clusters,
ports, demands and overlays) are in `ApspStoc/Base/`.

There are no `sorry`s and no `axiom` declarations. `#print axioms APSP.Stoc.thm_5_6` reports only
`propext`, `Classical.choice` and `Quot.sound`. This certifies the derivation, not the
hypotheses: the result is conditional on the fields of `Toolkit` and on `Mixing`, and its meaning
as a statement about CONGEST depends on those fields being true (see "What the result certifies").

`ApspStoc/Congest/` gives the toolkit an executable synchronous CONGEST semantics (`O(log n)`-bit
messages, uniform protocols, private random seeds, simultaneous halting). Every standard [STD]
field and every implementation contract [IMPL] (including Lemma 2.2), with its round, load and
message bounds, is a theorem about concrete protocols there. The main theorem holds for this
semantics, assuming only the cited theorems [PRIOR]/[PRIOR+] and `Mixing` (`thm_5_6_congest`; see
"Fifth round" and "Sixth round"). `thm_5_6_kt1` is the same theorem in the usual KT1 model,
where a node does not know the set of IDs; it first gathers the IDs ("Ninth round").
`AUDIT.md` is a reviewer's guide to `thm_5_6_kt1`: what has to be read (the statement, the
semantics, the hypotheses) and what can be skipped (all proofs).

## The main theorem (`ApspStoc/Main.lean`)

```lean
theorem thm_5_6 (T : Toolkit) (hmix : Mixing) (wexp c : ℕ) :
    ∃ (A : ℕ → T.Alg) (C k K : ℕ), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V),
      1 ≤ n → (∀ e ∈ N.G.edgeSet, N.w e ≤ n ^ wexp) →
      ∃ (p : Prof V) (δ : ℝ),
        T.Impl (A n) N (.compute none (V → ℕ × V) (APSPSpec N)) p δ ∧
        p.rounds ≤ C * lg n ^ k * n ∧ p.msgs ≤ C * lg n ^ k * n ^ 2 ∧ δ ≤ K / n ^ c
```

(`n = Fintype.card V`; `thm_1_1` is the same statement.) `WNet` is a connected weighted graph with
positive integer weights; the bound `n ^ wexp` is required on the edges only (the weight
function `N.w` is defined on all of `Sym2 V`, and its values on non-edges play no role).
`APSPSpec N o` says that every node `v` outputs, for every `u`, the
exact distance `dist(v,u)` and (for `u ≠ v`) a neighbour on a shortest `v`–`u` path. The algorithm
`A` and the constants `C, k, K` are chosen before the network.

The two hypotheses are:

* `T : Toolkit`: CONGEST, treated axiomatically. Its fields are standard facts, theorems of prior
  work (one used in a stronger form), and implementation assumptions, each tagged; see below.
* `hmix : Mixing` (`ApspStoc/G0Model.lean`): on a cluster with conductance `≥ 1/φ`, the lazy
  random walk is within a factor `[1/2, 3/2]` of stationarity after `Km·(φ+1)²·lg ν` steps. This
  is the Jerrum–Sinclair / Cheeger spectral mixing bound. It is a theorem of mathematics, not a
  fact about CONGEST, so it is a separate hypothesis rather than a toolkit field.

## How CONGEST is modelled (`ApspStoc/Toolkit.lean`)

`Toolkit` provides an abstract type of algorithms `Alg`, built only by combinators, so an
algorithm cannot depend on the network. It also provides a judgement `Impl A N t p δ`: *run on
`N` from a configuration satisfying task `t`'s precondition, `A` achieves `t` within `p.rounds`
rounds, with at most `p.load e` messages per edge and `p.msgs` messages in total, except with
probability `δ`.*

The tasks of the shortest-path phase carry their meaning.

**Semantic tasks.** A task `.io E j sz Π α β x spec` lives on overlay `L_j`. Its agents are the
nodes and the virtual aggregators (`Agent V = V ⊕ cluster`). The nodes of `Π` take part and know
the public size bound `sz`; every contract on a set `S` assumes that `Π` contains the footprint of
`S` (`S` and its embedded aggregator paths). The precondition is "agent `g` holds `x g`" and the
postcondition is "agent `g` holds `y g` with `spec y`".

**Generic rules.** Algorithms compose with:

* `bind`: sequencing; the second algorithm sees the inputs together with the first one's outputs;
* `call`: run an algorithm on locally computed data (this replaces the earlier frame rule);
* `locR`: free *uniform* local computations, i.e. one Lean function for all networks;
* weakening.

**Mathematical specifications** (`ApspStoc/Defs.lean`) cover:

* `MASpec`, one Minor-Aggregation round (Def. 2.5); the aggregation operators may be
  non-associative and are aggregated in any order (`AggOf`, Def. 2.4);
* `EOSpec`, Eulerian orientation with virtual nodes;
* `ApproxSpec`, `3/2`-approximate SSSP with an approximate shortest-path tree from a virtual source;
* `RingSpec`, consistent orientation of rings.

This is what lets the paper's own composition claims be *proved*.

### The assumptions (fields of `Toolkit`)

**[STD]** standard facts:

| Field | Content |
|---|---|
| `bind`, `call`/`callR`, `locR`, `mono`, `weaken`, `weakenIO` | sequencing, local calls, local computation, weakening |
| `notify` | one round of direct messages |
| `treeCast` | tree convergecast and broadcast [35], with any aggregation operator |
| `clusterSetup`, `embThen`, `decomp*` (with `dstart`, `dstep`), `g0Then`, `route*Weaken` | leader election and spanning trees in a cluster; sequencing steps of the preprocessing |

All of these are proved, with their costs, in the CONGEST semantics of `ApspStoc/Congest/`.

**[IMPL]** implementation and cost-accounting steps of the paper's own algorithm:

| Field | Content |
|---|---|
| `aggUp`, `aggDown` | the paper's Lemma 2.2 on the aggregator edges of `L_j` (the paper proves it by random-delay routing [17]; the CONGEST proof uses deterministic store-and-forward). Requires a valid embedding (`EmbValid`: one host per virtual aggregator, disjoint clusters). Round budget depends only on public quantities (`sz`, `E.dil`, and the message size `μ`, which is an algorithm parameter); messages carry `sz`. Load and messages scale with `K·(μ+1)`: a number `≤ ν^Bw` takes `O(Bw)` words |
| `ringLE` | Hirschberg–Sinclair [23] on the segment rings, simulated over the aggregator edges; the own edge of a segment end is incident to its node (`RingWF.inc`); postcondition proved satisfiable (`ringSpec_realizable`) |
| `perCompR` | runs an algorithm on the connected components of a subset `S ⊆ P` one after another, each on its own footprint, within the footprint of `P`. Takes MST computations on `P` (token tree) and on `S` (component trees and leaders) as premises, gives each component's run the public size `|K|`, and charges the start and end announcements along the aggregator paths explicitly (`K₀·aggLen j P` messages, `O((E.dil+1)²(sz+1))` rounds); costs add up. The algorithm gets the type families of the data and the outputs (`perComp A Bt Am B`), the output type must be inhabited (`[Nonempty (Bt V)]`), and the embedding must be valid (`EmbValid`, `j < n`). Not described in the paper |
| `rwLink` | the random-walk construction of `G₀` outputs the multigraph defined by uniformly seeded lazy walks (`G0Model.lean`), unless a step overflows its round budget or `G₀` misses the public parameters `gf n_C m_C` the algorithm outputs. Tokens carry their walk index and position, so the constant depends on an exponent `kB` with `R + 2ℓ + 2 ≤ (n+4)^kB` |
| `clusterPar`/`embedConstruct` | the per-cluster preprocessing of Theorem 3.10 on pairwise edge-disjoint, nonempty clusters of edges of `G` (explicit premises), with edge weights `≤ n^wexp` and recorded dummy routes of length `≤ n^Lb`. Includes the ID gathering the paper does not describe, the delivery of the cluster topologies to the hosts, and making `E.dil`, `E.ov` public |

All of these are proved, with their costs, in the CONGEST semantics (see "Sixth round").

**[PRIOR+]** a cited theorem in a stronger form:

| Field | Source |
|---|---|
| `routeG0` | expander routing [19, 7] (Lemma 3.2), run on `G₀` via Lemma 2.2, **exposing the structure of the recorded routes**: they are produced by the forwarding procedure of a routing hierarchy of constant depth (`RoutesHier`; ninth round). The per-route length bound needed for Lemma 3.9's "each packet crosses polylog(n) edges", which is not part of Lemma 3.2 as stated, is derived from it (`RoutesHier.routesOK`). `G₀` has polynomial size (`n₀ ≤ K·n`). Hypotheses, as at its only use (Theorem 3.3): `C` is a `1/polylog`-expander, `P ⊆ allPorts C`, `G₀` has `Õ(n₀)` edges and polylog inverse conductance. Every node on a recorded route learns the whole route; recording and returning the routes is charged by a factor `dil + 1` on rounds and messages (seventh round) |

**[PRIOR]** theorems of prior work:

| Field | Source |
|---|---|
| `expDecomp` | expander decomposition [9] (Lemma 2.8); the algorithm knows `φ⁻¹` |
| `ghs` | GHS [16] |
| `mstRed` | MST in `O(log n)` Minor-Aggregation rounds [16, 38] |
| `approxRed` | the approximate-SSSP algorithm of [37] (Lemma 5.1), with an approximate shortest-path tree ([37] treats the approximate SSSP-tree problem) |
| `eoVirt` | the treatment of virtual nodes in Eulerian orientation, which the paper attributes to [37] ("we use the same technique as [37]", proof of Lemma 5.3); its translation into the aggregator framework's costs is part of the assumption. The algorithm gets a public bound `kb` on the number of virtual nodes |
| `schedule` | random-delay scheduling [17, Theorem 1.1], with public bounds `R`, `Cg` on the instances' rounds and congestion, polynomial in `n` (`R + Cg ≤ (n+4)^kB`; eighth round). Loads and messages are multiplied by a polylog factor (instance tags on the messages; the shared delays are distributed over a BFS tree of `G`) (seventh round) |

`ApspStoc/Consistency.lean` shows that the trivial model (`Impl := True`) satisfies every field,
so the assumptions are consistent. `ApspStoc/SatModel.lean` gives a more informative model: there
`Impl A N t p δ` means "`0 ≤ δ`, and if `δ < 1` the postcondition of `t` is satisfiable", and every
field holds, so **every contract is realizable** (see "Fourth round" below).

The content of `thm_5_6` is the derivation relative to the intended semantics: Lean checks the
reasoning, and the meaning comes from reading each field as the stated CONGEST fact.

## What is proved

| Paper | Lean | Content |
|---|---|---|
| Obs. 2.3 | `Basics.lean` (`observation_2_3`) | physical load ≤ direct + `c`·overlay; transmissions ≤ direct + `d`·overlay |
| Lemma 2.10 | `Sec3.lean` (`lemma_2_10`) | iterating [9]: geometric decrease, overlap ≤ `lg(n²)` |
| Claims 3.4/3.5 | `G0.lean` (`buildG0_of`), `G0Aux*.lean` | the random-walk construction: cost; w.h.p. no overflow, `G₀` an expander with `Õ(|P|)` edges and no isolated port, embedding congestion and dilation polylog. Includes multiplicative Chernoff bounds proved from scratch, stationarity and the Markov property of the seeded walk, and a union bound over all subsets for the expansion |
| Thm 3.3 | `Sec3.lean` (`thm_3_3`) | Claims 3.4/3.5 + Lemma 3.2 + Lemma 2.2 |
| Lemma 3.7 | `Base/AggregatorSet.lean` | the three properties of `A(C)` |
| Lemmas 3.8, 3.9 | `Base/Demands.lean`, `Sec3.lean` | the concrete demands: port sets, loads, sizes |
| Thm 3.10 | `Base/Overlays.lean`, `Sec3.lean` (`thm_3_10`) | overlay construction; congestion `n + 2βn`; subset congestion; `Õ(n)` rounds, `Õ(n²)` messages (`∑_C n_C² = Õ(n²)`) |
| Lemma 4.2 (Thm 4.1) | `Sec4.lean` (`lemma_4_2`) | **correctness** and cost of the aggregator-based simulation of an arbitrary Minor-Aggregation round on a subset: per-cluster spanning forests, GHS, two tree casts, two node↔aggregator exchanges |
| Lemma 5.3 | `Sec5EO.lean`, `Sec5EOAux.lean` (`eo_physical`); `Sec5a.lean` (`lemma_5_3_of`) | **correctness** of the paper's physical Eulerian orientation (cluster pairings, segments, ring leader election, consistent orientation of segments); with virtual nodes via `eoVirt` |
| Lemma 5.4 | `Sec5a.lean` | [37] + Lemma 4.2 + Lemma 5.3 |
| Thm 5.5 | `Sec5b.lean`, `Sec5bAux1-5.lean` (`thm_5_5_of`) | the thresholded recursion, defined as a Lean algorithm from the primitives. Proved: **exact distances and SSSP-tree parents**, the invariant "distance in `[a, a+3δ]`" (strengthened to an inductive one), and `Õ(n)` rounds and messages with load `Õ(1)·ρ` via a per-node window count |
| Thm 5.6 | `MainOf.lean`, `Main.lean` | `n` SSSPs on separate overlays via random delays; union bound over `poly(n)` events |

Failure probabilities are tracked explicitly throughout.

## What the result certifies

`thm_5_6` is a machine-checked *conditional* theorem. It says: for every interpretation of the
abstract algorithms and of the judgement `Impl` satisfying the toolkit fields, and assuming
`Mixing`, the composed algorithm solves APSP within the stated bounds. It verifies a *specified,
repaired* version of the paper's algorithm (see the issues below, e.g. Step 5 of Theorem 5.5), not
every literal step of the manuscript. The trivial model in `Consistency.lean` shows only that the
fields are not contradictory; it is not a realization by actual protocols. The satisfiability model
in `SatModel.lean` shows more: no field demands an output that does not exist (every postcondition
is satisfiable whenever the premises hold with failure bound `< 1`), and the generic rules preserve
this. It does not validate costs. The operational semantics of `ApspStoc/Congest/` does: there,
every [STD] and [IMPL] field is proved with its costs, and `thm_5_6_congest` is the main theorem
for concrete protocols, relative to the [PRIOR] and [PRIOR+] fields and `Mixing` only. That
statement still depends on the semantics (`Core.lean`, `Tasks.lean`) being a faithful model of
CONGEST, which has to be checked by reading.

The toolkit tags separate the kinds of trust involved:

| Tag | Meaning | Fields |
|---|---|---|
| [STD] | textbook CONGEST facts and generic rules; all proved in the CONGEST semantics (`ApspStoc/Congest/`) | `bind`, `callR`, `locR`, `mono`, weakening, `notify`, `treeCast`, `clusterSetup`, sequencing of the preprocessing |
| [PRIOR] | theorems of cited prior work | `expDecomp` [9], `ghs` [16], `mstRed` [16, 38], `approxRed` [37], `eoVirt` [37], `schedule` [17] |
| [PRIOR+] | a cited theorem in a stronger form than the paper states | `routeG0` (Lemma 3.2 with a per-route length bound) |
| [IMPL] | implementation and cost-accounting steps of the paper's own algorithm; all proved in the CONGEST semantics | `aggUp`, `aggDown` (Lemma 2.2), `ringLE` (simulation of [23]), `perCompR`, `rwLink`, `clusterPar`/`embedConstruct` |

## Repairs after the independent audit

An independent audit of the first version of this package found two defects in the interfaces
between the proof and CONGEST. Both are repaired:

1. **`ringLE` promised an impossible output.** `RingWF` did not exclude a segment end being its own
   partner. On such an input `RingSpec` demands `d ≠ d`, yet `ringLE` promised it with failure
   probability 0. `RingWF` now has the field `ne` (the two ends of a segment are different ends).
   It is proved for the paper's segment construction (`FamOK.ringWF` in `Sec5EOAux.lean`, from
   `oend_spec`). `Realizability.lean` proves `ringSpec_realizable`: every input satisfying the
   repaired `RingWF` has an output satisfying `RingSpec`.
2. **An overlay's virtual aggregator need not have had one host.** `EmbValid` said `∀ v ∃ h`: the
   paths of different nodes could end at different nodes of `A(C)`. With all paths empty, one
   aggregator could then "collect" the inputs of all nodes without communication. `EmbValid`
   (`Base/Overlays.lean`) now requires one host per overlay and cluster (`∃ h ∀ v`). It also
   requires that embedded paths use only edges of their cluster and that clusters consist of
   edges of `G`. The construction of Theorem 3.10 satisfies this: its host `portAssign C h j`
   does not depend on `v`.

Both counterexamples are kept as regression tests in `Realizability.lean`: the bad ring input
has no valid output and is rejected by `RingWF`, and the empty-path embedding is rejected by
`EmbValid`.

### Second audit

A second review confirmed both repairs and raised two further points about the implementation
assumptions:

3. **When does an aggregation phase end?** `aggUp`'s round bound depended on the participating set
   `S` and its path congestion, which an aggregator host outside `S` cannot know. So a host could
   not tell "this node has no message" from "its message has not arrived yet". For example, in a
   star with the host at the centre, a run where only the centre sends and a run where a leaf also
   sends look the same to the host at time 0. Repair:
   - Every semantic task now carries a **public size bound** `sz` (`Task.io E j sz …`,
     `Task.mst E j sz S`). The participating nodes know `sz`, and messages carry it, so an
     aggregator that receives a message knows when the phase ends. An aggregator that receives
     none holds the empty table, which is its correct output.
   - All round budgets of the building blocks are functions of public quantities only: `ν`, `sz`,
     message sizes, and the dilation `E.dil` and overlap `E.ov` of the embedding. The last two are
     computed and broadcast during the preprocessing. For example, `aggUp`/`aggDown` take
     `K·lg^k ν·(μ+1)·(E.dil+1)·(sz+1)` rounds, and the hypothesis `S.card ≤ sz` replaces the
     earlier caller-chosen congestion and length bounds.
   - `perCompR` gives each component's run the public size `|K|`. The component's leader
     computes it and announces it, within the existing overhead.
   - `EmbValid` additionally requires the clusters to be pairwise disjoint. This yields
     `rhoAgg ≤ E.dil·|S|`.
   - The top level runs with `sz = n`.
4. **Parallel cluster preprocessing needs edge-disjointness.** `embedConstruct` now has the
   premise that the clusters are pairwise edge-disjoint; its caller discharges it with the
   decomposition's `disj`.

### Third audit

A third review confirmed the second round of repairs and found two gaps in the implementation
rule `perCompR` (sequential execution on the components of `G[S]`):

5. **Its MST premise on `P` does not give the trees of the components of `G[S]`.** A spanning
   tree of `P` restricted to `S` need not span the components of `G[S]`. `perCompR` now also takes
   an MST computation on `S` (`.mst E j sz S`: one tree and leader per component). Its cost and
   failure probability are added.
6. **The announcements of `|K|` to the aggregators were not paid for.** One message per node of
   `K` to each of its aggregators costs `aggLen j K` messages, more than a constant times `|P|`.
   An example is a node with `log n` singleton-edge clusters. The overhead is now charged
   explicitly: `aggLen j S` messages, and `K₀·(E.dil+1)²·(sz+1)` rounds (store-and-forward, so
   deterministic). Since `aggLen j S ≤ E.ov·E.dil·|S|`, Theorem 5.5's `Õ(n)` bounds are
   unaffected.

**Statement alignment.** The subset lemmas (4.2, 5.3, 5.4, MST) bound rounds by the public size
bound `sz`, not automatically by the size of the actual subset. Tight sizes are supplied by
`perCompR`, which gives every recursive call of Theorem 5.5 the size of its component.

### Fourth round: realizability of all contracts

`ApspStoc/SatModel.lean` builds a model of the whole toolkit, `satToolkit (hmix : Mixing)`, with

  `Impl A N t p δ  :=  0 ≤ δ ∧ (δ < 1 → Sat t)`,

where `Sat t` says that the postcondition of `t` has a solution. Under the intended reading both
conjuncts are necessary for a field to be true, so the model checks that no contract demands
impossible outputs. The existence results it needs are proved, from scratch, in:

| File | Theorem | Used for |
|---|---|---|
| `RealDecomp.lean` | `expDecomp_exists_lg`: every edge set has a node-disjoint expander decomposition with `φ⁻¹·#crossing ≤ 6·lg ν·|F|` (sparse-cut recursion with the potential `W·⌈log₂ W⌉`) | `expDecomp` |
| `RealRoute.lean` | `route_exists`: in a cluster with inverse conductance `φ`, every demand on its ports with load `≤ λ` routes along walks of length `≤ K(φ+1)^k lg^k ν` with `≤ K(φ+1)^k lg^k ν·λ` packets per edge (random-walk bridges, `Mixing`, Chernoff, union bound) | `routeG0` |
| `RealEO.lean` | `eoSpec_realizable`: every well-formed Eulerian-orientation instance with virtual nodes has a solution (darts with two involutions) | `eoVirt` |
| `RealMisc.lean` | `spanForest_exists`, `approxSpec_realizable` (exact distances with shortest-path parents), `aggOf_exists` | `ghs`, `approxRed`, `treeCast` |
| `Realizability.lean` | `ringSpec_realizable` | `ringLE` |

The remaining fields are direct (`aggUp`, `aggDown`, `notify`, `locR`: explicit outputs), combine
outputs by choice (`schedule`, `embedConstruct`, `perCompR`, using that components are disjoint), or
use that an event of probability `< 1` misses some seed (`rwLink`).

Building the model exposed three defects, now repaired:

7. **The sequencing rules were false under the intended reading.** In `bind`, `embThen`,
   `decompThen`, `decompStep` and `g0Then`, the continuation premise `∀ y, R y → Impl B … δ'` is
   vacuous when no output satisfies `R`; a first step with failure bound `δ = 1` and a continuation
   with `δ' = -1` then "proved" any postcondition, even `False`, with failure bound `0`. The rules
   now require `0 ≤ δ'`. No proof used a negative bound; the call sites now supply the premise.
8. **`routeG0` could demand impossible routes.** Its route-length bound `Õ(dil)` is unsatisfiable on
   some inputs it allowed. Example: a path cluster with a `G₀` (from adversarial seeds and
   exponentially many tokens) whose consecutive ports are joined by `4^i` parallel edges: its
   conductance is `≥ 1/3`, but a packet from one end to the other needs a route of length `Θ(n)`.
   Ports outside `C` are another failure. `routeG0` now assumes, as at its only use, that `C` is a
   `1/polylog`-expander and `P ⊆ allPorts C`. It also assumes `m₀ = Õ(n₀)`: the bounds of [19, 7]
   depend on the size of `G₀` through its mixing time.
9. **`perCompR` with `S = ∅`.** No component runs, yet every agent must hold an output of type
   `β`; for an empty `β` none exists. The field now requires `[Nonempty β]` (filled by instance
   search at its use).

### Fifth round: an executable CONGEST semantics; costs of the standard contracts

`ApspStoc/Congest/` gives the judgement `Impl` a concrete operational meaning. Every [STD] field is
proved in it, including its round, per-edge load and message bounds. The [PRIOR], [PRIOR+] and
[IMPL] fields become assumptions about concrete protocols (`CAssume`). The main theorem is
re-derived for this semantics (`thm_5_6_congest`).

**The semantics** (`Core.lean`, `Comb.lean`, `Tasks.lean`):

* *Rounds.* Rounds are synchronous. In each round, every node that has not halted sends at most
  one message to each neighbour, then updates its state from the messages it received. A halted
  node is frozen and silent.
* *Bandwidth.* A message is one `Word`: an ID, an edge, or a number `≤ n + 3`. So a message has
  `O(log n)` bits; the network drops larger words.
* *Uniformity.* An algorithm (`CAlg`) is a protocol for every node set `V`. Each node runs a state
  machine whose transitions see only the node's local context: its ID, its local weight views,
  the public numbers of the task, and the embedded paths through it. It never sees the network.
* *Randomness.* Each node draws an independent uniform seed from a finite type. A run is a
  function of the seeds, and failure probabilities are counted exactly.
* *Agents.* Agent data is dynamically typed (`Σ T : Type, T`). An aggregator is simulated by its
  host, the common endpoint of its embedded paths.
* *Participants.* An instance fixes its participating nodes. Non-participants have no edges in the
  instance and host no agent.
  - Overlay tasks `.io E j sz Π …` and `.mst E j sz Π S` carry their participant set `Π`.
  - Cluster tasks (`clusterSetup`, `buildG0`, `routeViaG0`, `route`) run on the cluster's edges,
    with its nodes as participants.
  - The preprocessing and the whole algorithm involve all nodes.
* *Success.* A run succeeds when all of the following hold:
  - all participants halt in the same round `t ≤ p.rounds`, and none earlier;
  - at most `p.msgs` messages were sent, and at most `p.load e` over every edge `e`;
  - the outputs satisfy the postcondition.

  Simultaneous halting is what makes sequential composition sound: the next protocol starts at
  every participant in the same round. It forces every round budget to be computable by the
  participants.
* *Tasks.* `CImplT` (`Tasks.lean`) fixes, for every task:
  - its participants, and what they know at the start;
  - where inputs and outputs live;
  - the postcondition.

  `clusterSetup` and `mst` now have real postconditions: a rooted spanning tree in which every
  node knows the leader, its parent and all degrees; and a spanning forest of `G[S]`.

**What is proved in the semantics:**

| Field(s) | Lean | Content |
|---|---|---|
| `bind` | `Comb.lean` (`bindI`) | sequential composition: rounds, loads and messages add up; failure probabilities add up over independent seeds |
| `callR`, `locR`, `decompBase` | `Comb.lean` (`callI`, `locI`, `skipI`) | local computation is free: 0 rounds, 0 messages |
| `mono`, `weaken`, `weakenIO`, `embWeaken`, `routeViaWeaken`, `routeWeaken`, `embThen`, `decompThen`, `decompStart`, `decompStep`, `g0Then` | `Rules.lean` | the generic rules |
| `notify` | `Notify.lean` | one round; ≤ 2 messages per edge of `F`, ≤ `2·|F|` in total |
| `treeCast` | `TreeCastAux.lean`, `TreeCast.lean` | convergecast and broadcast of `b`-word values on a rooted forest. Values are serialised into `(b+1)(Bw+2)` words in base `n+4`. The halting round `1 + sz·L + sz + L` is public. `K = 4·Bw + 10` |
| `clusterSetup` | `SetupProto/Tree/Run.lean`, `Setup.lean`, `ExpDiam.lean` | leader election and BFS tree by flooding for `D` rounds, then a subtree count gives `n_C`, then gossip of the (ID, degree) table along the tree for `2D` windows; every node computes `A(C)` from the table (`aggSet_eq_aggT`), and the ports of `A(C)` are gossiped along the tree for `2D` more windows (output `portsA C`). `D` is a public diameter bound: a `1/φ`-expander has diameter `O(φ·log m)` (`expander_dist_le`). Cost: `≤ K·lg^k ν·n_C` rounds and `K·lg^k ν·n_C²` messages |

`toToolkit` (`Model.lean`) assembles these with a `CAssume` into a `Toolkit`, and
`thm_5_6_congest` is `thm_5_6` for it. Given the assumed contracts and `Mixing`, a uniform CONGEST
protocol solves APSP in `Õ(n)` rounds and `Õ(n²)` messages, with failure probability `≤ K/n^c`.
`CAssume` is generated from the text of `Toolkit.lean` (by replacing `Impl` and `Alg`), and
`toToolkit` typechecks only if its fields match the toolkit's.

**Changes to the abstract toolkit.** The semantics forced these changes; the statement of
`thm_5_6` is unchanged.

10. **`frame` is replaced by `call`.** The frame rule says an algorithm run on `(z g, x g)` behaves
    as on `x g`. It cannot hold for executable protocols, because a protocol cannot take apart a
    value of an arbitrary product type. The new constructor `call F B` computes `F` locally and
    runs `B` on the result (`callR`). `call (sndF Γ A) B` plays the role of the frame rule
    (`Toolkit.frameCall`).
11. **The decomposition loop has its own constructors**, `dstart` and `dstep`. The residual edges
    and the accumulated clusters are a node's state, updated locally between the runs of [9].
    With the pairing `seq`, the loop's data would be nested to a depth no protocol can know.
12. **`treeCast`'s algorithm takes the value size `b`** (`A ν b`), and so does Lemma 4.2's
    algorithm. The round budget depends on `b`.
13. **`ν ≤ n`** is added wherever `n ≤ ν` is assumed. With `O(log n)`-bit messages, a number
    `≤ ν^Bw` fits in `O(Bw)` words only if `ν ≤ poly(n)`. All uses have `ν = n`.
14. **`eoVirt`'s Minor-Aggregation premise** asks for instances that are small at every size level
    above its bound, because `MAInst.Small` is not monotone in the size.
15. **Participant sets.** Overlay tasks carry their participants `Π`, and every overlay contract
    on a set `S` assumes `footprint E j S ⊆ Π`. The footprint is `S`, the nodes on the embedded
    aggregator paths of `S`, and their hosts.
    - Without explicit participants, every node takes part in every overlay task. A node far from
      `S` then cannot know when a phase on `S` ends, since its budget depends on `|S|`.
    - In particular, the recursion of Theorem 5.5 could not be implemented.

**Five assumed contracts were unrealizable as stated, and are repaired.** In each, the round
budget depended on a quantity the participants cannot know.

16. **`expDecomp`** [PRIOR] did not let the nodes know `φ⁻¹`. With the same input, the output
    would have to be a `1/φ`-expander decomposition for every `φ` at once. The algorithm is now
    `A ν φinv`; its use passes a public function of `ν`.
17. **`aggUp`, `aggDown`** [IMPL]: the round budget depends on the message size `μ`. A node cannot
    learn whether some far-away message is long. The algorithm is now `A ν μ`, and every use has a
    public `μ` (a constant or a function of `b`).
18. **`eoVirt`** [PRIOR]: the number of phases depends on the number `H.k` of virtual nodes. The
    constructor is now `eoAlg ν kb M P` with `H.k ≤ kb`; Lemma 5.3 uses the public bound
    `kb = kv ν`.
19. **`schedule`** [PRIOR]: the delay range and the round budget depend on the instances' congestion
    and dilation, but the cost profiles were arbitrary. The constructor is now `sched c ν R Cg A`,
    with premises `(p s).rounds ≤ R` and `∑ s, (p s).load e ≤ Cg`.
    - `MainOf` passes `R = q ν·ν` and `Cg = q ν·fX ν·ν`, both functions of `ν`.
    - The resulting budget equals the previous one, so the main cost argument is unchanged.
20. **`perCompR`** [IMPL] ran the components of `G[S]` one after another with every node taking
    part. A node outside `P` cannot learn when each run starts within the budget. Now:
    - every component `K` runs `B` on its own footprint (`.io E j |K| (footprint E j K) …`), and the
      composite runs on `footprint E j P`;
    - before `K`'s run, its leader broadcasts the start time and `|K|` on `K`'s tree, and every
      node of `K` relays it along its aggregator paths, so the whole footprint of `K` starts
      together;
    - at the end, `P`'s root announces the end on `P`'s tree and paths.

    The message overhead is now `K₀(|P|+1) + 2·aggLen j P`: start announcements cost
    `∑_K aggLen j K ≤ aggLen j P`, and the end announcement costs `aggLen j P`. The Theorem 5.5
    recursion now runs a call on `S` on `footprint E j S`, and the component premise is the
    induction hypothesis on `footprint E j K`.

After these repairs, the round budget of every assumed contract is, as far as a reading of the
contracts shows, a function of quantities its participants know. This is a manual check, not a
Lean theorem. In this round the assumed contracts remained assumptions: the cited theorems
[9, 16, 17, 19, 7, 23, 37, 38] and the implementation steps were not proved. The sixth round
proves the implementation steps (including the simulation of [23]); the cited theorems remain
assumptions whose truth in this semantics has to be checked by reading (`Assume.lean`).

### Sixth round: the implementation contracts proved in the CONGEST semantics

The six [IMPL] contracts (`aggUp`, `aggDown`, `ringLE`, `perCompR`, `rwLink`, `embedConstruct`)
and their algorithm constructors (`clusterPar`, `rwAlg`, `perComp`) are now theorems about
concrete protocols. `CAssume` keeps only the [PRIOR] and [PRIOR+] fields, and `toToolkit` takes
the six contracts from the proofs below. So **`thm_5_6_congest` assumes only the cited theorems
(`expDecomp`, `ghs`, `mstRed`, `approxRed`, `eoVirt`, `schedule` and their constructors, and
`routeG0`) and `Mixing`.** Its statement and that of `thm_5_6` are unchanged.

**What is proved:**

| Field | Lean (`ApspStoc/Congest/`) | Protocol |
|---|---|---|
| `aggUp`, `aggDown` | `AggUpDown{Walk,Core,Cost,}.lean` (`aggUp_congest`, `aggDown_congest`) | deterministic store-and-forward along the embedded aggregator paths, hop by hop: each hop has `sz` slots of `L = 1 + encLen Bw μ` words (a header with the source, then the value encoded in base `n+4`), and a node sends the packets crossing an edge in the order of their sources. A relay recognises a packet from its header and the edge it came from (the paths are disjoint per cluster, `EmbValid`). Halts in round `E.dil·sz·L`; `K = Bw + 3`, `δ = 0` |
| `ringLE` | `RingComb.lean` (the election combinatorics), `RingLE{Base,Global,Local,Match,Step,Out,Cost,}.lean` (`ringLE_congest`) | deterministic probe election on the segment rings in the style of Hirschberg–Sinclair, with `⌊log₂(ov·min(sz,n))⌋ + 2` phases; phase `i` has `2^i` link steps, and the number of probes in flight halves as the reach doubles (`card_flightA_mul`). A link step goes up the departing end's path to the aggregator's host and down the partner's path. Every segment end outputs the direction of the largest probe that crossed it, which is a consistent orientation (`ringDir_spec`). `K = 336`, `δ = 0` |
| `perCompR` | `PerComp{Emb,Frame,Seg,Path,Local,Sched,Time,Msg,Hist,Tok,Known,Ctl,Cost,Plan,Trav,}.lean` (`perCompR_congest`, algorithm `perCompC`) | `Am` on `P` and on `S` (a spanning tree of `P`, a spanning forest of `G[S]` rooted at the component leaders), a tree cast that gives every node `\|K\|`, and two `notify` rounds (children). Then a token traverses `P`'s tree depth-first. At its first visit to a component's leader, the start is broadcast on `K`'s tree and announced hop by hop along the aggregator paths of `K` (3-word frames: source, `\|K\|`, leader), with phase starts aligned to multiples of `(dil+1)\|K\|`. So the whole footprint of `K` starts `B` in the same round, with the context and inputs of `K`'s instance. Since `B` sends properly, its run inside the traversal is its standalone run (`PerCompEmb.lean`; one seed per node, union bound over the components). When `B` halts the token moves on; a final announcement on `P` makes the footprint of `P` halt together. `K₀ = 60` |
| `rwLink` | `RWCouple.lean` (the coupling), `RWLink{Pkt,Proto,Glob,Walk,Known,Out,Cost,}.lean` (`rwLink_congest`) | every node draws a table of seeds, one per (port, walk index, step); a token carries its walk index and position and takes each lazy step at the node it is on, with that node's seed. Reports travel back along the walks so that every node learns its hops. `rwSeedMap_prob`: the walks defined by uniform seed tables are distributed as the seeded walks of `G0Model.lean`, so the failure probability is exactly the contract's. `Kc = 48·(kB + 2)` |
| `clusterPar`/`embedConstruct` | `EmbConstruct{Base,Defs,Par,Local,Bfs,Out,}.lean` (`embedConstruct_congest`) | a BFS tree from the node of smallest index (flooding, `n` rounds); then every node runs one copy of the per-cluster pipeline `A₁; A₂; A₃` per cluster slice, all clusters in parallel. The routing inputs of `A₂` (topology packets: an edge and the digits of its weight) and `A₃` (dummy packets) are computed locally from the setup's output. A generic parallel-composition lemma (`PD.Ok.par_run`) runs copies on edge-disjoint clusters side by side, with termination detection on the BFS tree and a convergecast/broadcast of the dilation and overlap, so all nodes halt together and output `E.dil`, `E.ov`. Costs add up over the clusters, with a union bound on the failure probabilities. `K = 4·Lb + 6` |
| `clusterSetup` ([STD]) | `Setup*.lean` | extended: every node computes `A(C)` from the degree table (`aggSet_eq_aggT`), and the ports of `A(C)` are gossiped along the BFS tree (`portsA C`, needed by the routing inputs of Lemma 3.8) |

**Changes to the semantics.** These make the knowledge and communication of the nodes precise
enough for the protocols:

21. **Proper sends** (`Core.lean`, `ProperUpTo`, part of `Succ`). A participant may send only
    along edges of the instance's communication graph; any other send makes the run fail. In a
    composite run (`perCompR` runs `B` inside a larger footprint, `embedConstruct` runs clusters in
    parallel) a sub-protocol must not reach nodes outside its instance, which are idle or run other
    copies. All protocols proved earlier already satisfied this.
22. **Knowledge of embedded paths** (`NCtx.emb`, `NCtx.sl`, `ioEmb`). A node no longer knows the
    clusters as whole edge sets: that knowledge would cost `Σ_C n_C·m_C` messages to establish.
    Embedded paths are keyed by the overlay, the source and the source's *key edge* in the
    cluster, and a node knows its cluster slices `C ∩ inc(v)`.
23. **Routing with payloads** (`Task.route`, `Task.routeViaG0`, `rinAt`, `rkAt`, `PayloadOK`).
    Every routed packet carries a payload of at most `pw` words, delivered to its destination
    (Lemma 3.8 delivers the cluster topology this way). `routeG0` is `∀ c Kφ kφ pw, ∃ …`: its
    constants may depend on `pw`.
24. **Local knowledge of `G₀`** (`g0At`, `hopsAt`). After the random-walk construction, a node
    knows, for each surviving walk through it, its end ports and the positions at which the walk
    crosses it, not the whole walk.
25. **Cluster setup output** (`SetupSpec`): it also contains `portsA C`, and the destination
    assignment of Lemma 3.8 (`dstAssign`, `Base/Demands.lean`) is now canonical and computable
    by the sender from the degree table and its own slice (`dstAssign_local`); `dstAssign_spec` is
    unchanged.

**Repaired contracts.** As stated, these could not be implemented; each repair is discharged at
the contract's use, and `thm_5_6` is unchanged.

26. **`aggUp`, `aggDown`**: load `(K·(μ+1))•rhoAgg` and messages `K·(μ+1)·aggLen` (were
    `(μ+1)•rhoAgg` and `(μ+1)·aggLen`). A value of `μ` numbers `≤ ν^Bw` takes `O(Bw)` words per
    number, plus a header naming the source.
27. **`rwLink`**:
    - the nodes cannot compute the true parameters of `G₀`, so the algorithm `rwAlg Rf ℓ tf gf`
      outputs public parameters `gf n_C m_C`, and failing to meet them (`¬ TrueParams`) is part of
      the failure event; `TrueParams` asks `P.card ≤ g.n0` (was `=`), and `routeG0` likewise;
    - a token carries its walk index `< R` and a path position `≤ 2ℓ`, i.e. `O(log_n(R + ℓ))`
      words, so the constant depends on an exponent `kB` with `R + 2ℓ + 2 ≤ (n+4)^kB` (new
      premise; `∀ kB, ∃ Kc`). In Theorem 3.3, `R` and `ℓ` are polynomial in `n`
      (`g0_digits_le`).
28. **`embedConstruct`** is `∀ Lb wexp, ∃ K`, with constructor `clusterPar Lb wexp A₁ A₂ A₃`. New
    premises: edge weights `≤ n^wexp` (the weights travel in the topology packets: `wexp + 2`
    words of payload for `A₂`, `0` for `A₃`); clusters are nonempty subsets of `E(G)`; and the
    dummy routes recorded by `A₃` are walks in `C` of length `≤ n^Lb` (they are the overlay's
    aggregator paths, and the final dilation is broadcast as a number). All hold at the use in
    Theorem 3.10 (`Lb` from `routeG0`'s route-length bound).
29. **`ringLE`**: `RingWF` has a new field `inc`: the own edge of a segment end is incident to the
    node. A node finds the cluster of each of its segment ends from its cluster slices. The ring
    data built for Lemma 5.3 satisfies it (segment ends are darts).
30. **`perCompR`**:
    - the algorithm is `perComp A Bt Am B`: it is given the type families of the data (`α = A V`)
      and of the outputs (`β = Bt V`, with `[Nonempty (Bt V)]`). A uniform protocol cannot project
      a value of type `(Bool × Bool) × α` for an unknown `α` to `Bool × α`, and an agent in no
      component must produce an output of type `β` by itself;
    - new premises `EmbValid N.G E` and `j < n` (as for `aggUp` and `ringLE`): the announcements
      travel along the aggregator paths, which must be walks in `G` from their sources for the
      whole footprint to be reached;
    - messages `K₀·(|P|+1) + K₀·aggLen j P` (was `+ 2·aggLen j P`): an announcement carries its
      source, `|K|` and the leader, a constant number of words per hop.

    At the use in Theorem 5.5, `EmbValid` and `j < n` are among the theorem's hypotheses, and the
    overhead polynomial is `K₀·(fov·fd)` instead of `2·(fov·fd)`.

The constants of `clusterSetup` changed (`K = 40·(20Kφ + 22)`, was `16·(20Kφ + 22)`); its
statement did not.

After this round, the assumptions of `thm_5_6_congest` are the cited theorems [9, 16, 17, 19, 7,
37, 38] and `Mixing`. They, and the definitions of the semantics (`Core.lean`, `Tasks.lean`), have
to be checked by reading.

### Seventh round: repairs after the sixth audit

An independent audit of the sixth-round package found that one [PRIOR] contract was false in the
concrete semantics, and named three places where the trust boundary had to be stated more
precisely. A false field makes `thm_5_6_congest` vacuous (Lean checks the implication, not its
hypotheses), so this matters even though everything compiles.

31. **`schedule`** [PRIOR] was **false as stated** (the auditor's counterexample). Its loads and
    messages were the instances' sums with coefficient one, plus additive overhead
    (`∑ msgs + K·lg^k ν·ν`). In the concrete model a message is one word, so this fails:
    - Take a leaf `b` whose neighbour `a` holds a table of `R = n²` entries (instance `s_t`, an
      `edge` word `z_t`), encoded in the weight of another edge at `a` (the contract quantifies
      over all networks and overlays). Instance `s` sends `z_t` from `a` to `b` in round `t` iff
      `s_t = s`. Then the instances send `R` messages in total, and their outputs at `b` determine
      the table, about `3R·log₂ n` bits.
    - A scheduled run with `(1+o(1))·R` messages in `Õ(R)` rounds can convey only about
      `2R·log₂ n` bits over the edge `ab`: a word carries `≤ 2·log₂ n + O(1)` bits, and the choice
      of rounds adds `o(R log n)`.

    [17] does not count messages; a scheduled message must also carry the tag of its instance.
    The paper's "random delay scheduling has no additional message cost" (Section 1.2) holds up
    to a constant factor. Now the load is `K·lg^k ν·(∑ load + ν)` and the messages
    `K·lg^k ν·(∑ msgs + ν²)`. The overhead pays for the tags and for the shared delays that
    [17, Theorem 1.1] assumes. A BFS tree of `G` is built by flooding from the smallest ID (`G` is
    connected). Then every node draws the delay of its instance, and the `n` delays are gathered
    and broadcast on the tree. This no longer refers to the overlays (the previous docstring
    charged a seed broadcast over the clusters' trees, which the premises did not provide). The
    round bound is unchanged. In Theorem 5.6 the message bound becomes
    `Ks·lg^ks ν·(q₆(ν)+1)·ν²` (was `(q₆(ν) + Ks·lg^ks ν)·ν²`), still `Õ(n²)`.
32. **`routeG0`** [PRIOR+]: every node on a recorded route learns the whole route (`rkAt`). The
    overlays of Theorem 3.10 rely on this, because a node knows the embedded paths through it. The
    contract's justification did not cover it. [19, 7] deliver packets; to record the routes, a
    packet appends its hops to its header, and the destination sends the completed route back.
    A route has `L = O(lg^k ν·dil)` hops, so this costs `O(L)` words per hop. The contract's
    rounds and messages were linear in the dilation `dil` of `G₀`, which does not allow this when
    `dil` is large. They now carry a factor `dil + 1` (rounds `Õ((n₀+λ)(cong+dil)(dil+1))`) and
    `(dil + 1)²` (messages `Õ((m₀n₀ + M)(dil+1)²)`, was `Õ((m₀n₀ + M)·dil)`). At its only use
    (Theorem 3.3), `dil` is polylog, so the constant of Theorem 3.3 absorbs the factor and its
    statement is unchanged. The per-route length bound remains the [PRIOR+] strengthening, to be
    checked against [19, 7].
33. **Initial knowledge** is now stated explicitly as a modelling assumption (see "Modelling notes"
    below): nodes know the set of all IDs, and an ID is one word.
34. **What is verified.** As stated in "What the result certifies", the development verifies a
    repaired version of the paper's algorithm. The repairs are listed in "Issues found while
    formalizing the STOC submission" and in the rounds above.

The statements of `thm_5_6` and `thm_5_6_congest` are unchanged.

### Eighth round: after the seventh audit

The audit of the seventh-round package found no counterexample. It confirmed that the repairs of
`schedule` and `routeG0` are carried through `MainOf.lean` and `Sec3.lean`, and it raised one
scope issue.

35. **`schedule`**: the parameters `R` and `Cg` were unrestricted, but the delays of [17] lie in a
    range of size about `Cg`. So a delay need not fit in the `O(1)` words that the justification
    of the setup cost assumed. The contract is now `∀ c kB, ∃ K k Kδ`, with the premise
    `R + Cg ≤ (n+4)^kB`: a delay is then `kB` words, and the constants depend on `kB` (as for
    `rwLink`, item 27). In Theorem 5.6, `R = q₆(n)·n` and `Cg = q₆(n)·f_X(n)·n` are polynomial in
    `n`. `MainOf.lean` computes the exponent from the polylog bounds of `q₆` and `f_X`
    (`IsPL.le_pow`, `mul_pow_le_add_four_pow`) before the network is chosen.

The other points of that audit are qualifications that this package does not remove:

* **`routeG0`'s per-route length bound** remains a strengthening of the cited Lemma 3.2
  ([PRIOR+]). The auditor considers it plausible from the hierarchical embeddings of [19] and the
  tunable recursion depth of [7]. The expected argument, which has not been checked against the
  papers here: a packet follows embedded paths through a bounded number of levels of the
  hierarchy, each with polylog dilation in `G₀`, and every `G₀` edge is a walk of length `≤ dil`
  in `G`. This is an inference from their constructions, not a quoted theorem. A written
  derivation from [19, 7] of the exact interface (short routes, local route knowledge, the stated
  costs) would close it. (Ninth round: the length argument is now formalized, item 37.)
* **Initial knowledge**: the concrete theorem starts from nodes that know all IDs (item 33). The
  wrapper that establishes this knowledge is described but not formalized. (Ninth round: it is
  formalized, `thm_5_6_kt1`, item 36.)
* **Reproduction**: the claims about the build rest on running Lean (`AUDIT.md`, section 1).

### Ninth round: the ID-gathering wrapper and the route-length argument

36. **The KT1 model is formalized.** `thm_5_6_kt1` (`Congest/KT1.lean`) is the main theorem in the
    usual CONGEST model.
    - IDs come from a known universe `U` of size `≤ (n+1)^idexp`. The node set `S ⊆ U` is
      unknown. A node knows its ID, its incident edges with their weights (hence its neighbours'
      IDs) and `n` (`ktInst`, `ktView`; outputs read back by `ktOut`; `KTDefs.lean`).
    - The algorithm first gathers the IDs, deterministically, in exactly `(B + 6)·n` rounds with at
      most `(B + 11)·n²` messages, where `B = lg|U|` (`KTGather*.lean`):
      - a leader is elected by binary search on the least index: `B` windows of `n` rounds, in
        each of which the nodes whose index lies in the lower half of the current interval flood
        a token;
      - a BFS tree is built from the leader, and nodes learn their children in the same window;
      - subtree sizes are convergecast (scheduled by depth), and preorder numbers are sent top
        down, one window each;
      - every ID is uploaded to the root and broadcast back down, in one window of `3n` rounds.
        The slots come from the preorder numbers, so no two words share an edge in a round.
    - Then it runs the algorithm of `thm_5_6_congest` on `S` (`KTSim.lean`). IDs and words are
      translated, and the run is exactly the run on `baseInst N`. Each node's seed is a table with
      one inner seed per possible node set, and the node uses the entry for `S`. This is
      equivalent to drawing the inner seed after the gathering: the failure probability is the
      inner one (`seedEquiv`).
    - The bounds are those of Theorem 5.6 with larger constants (`C + idexp + 12`, `k + 1`).
      `thm_5_6_kt1` is derived from `thm_5_6_congest`, whose statement is unchanged.
37. **`routeG0`: the route-length argument is formalized** (`Defs.lean`: `Hier`, `Hier.Gen`,
    `Hier.Route`, `RoutesHier`). The contract no longer asserts a bound on the length of each
    route. Instead it states the shape of the routes of Ghaffari–Kuhn–Su [19, §3.1–3.2], with the
    constant hierarchy depth `h` that Chang–Saranurak [7, §3] allow:
    - levels `0..h`; every edge of level `i+1` is embedded as `≤ b` edges of level `i`;
    - a terminal route uses `≤ b` edges of level `h`;
    - a route of level `i < h` is one route of level `i+1` expanded into level `i`, or two such
      routes joined by one edge of level `i` (via a portal);
    - every level-0 edge, and the initial redistribution walk, is a walk of `≤ τ` edges of `G₀`;
    - every edge of `G₀` is a walk of `≤ dil` edges of the cluster.

    Here `b = K_b·lg^{k_b} n`, and `τ = K_τ·(φ(G₀)⁻¹+1)²·lg n` (mixing-length walks, polylog
    because `G₀` has polynomial size: new premise `n₀ ≤ K_φ·n`, which holds at the use,
    `n₀ ≤ a·n_C`). Lean proves the hop-count recurrence `L_i ≤ 2b·L_{i+1} + 1`, so
    `L_0 ≤ (2b+1)^h (b+1)` (`Hier.Gen.length_le`). It also proves the physical bound
    `|route| ≤ dil·τ·(1 + (2b+1)^h (b+1))` (`RoutesHier.routesOK`), which Theorem 3.3 now uses.
    The constant depth is what makes this polylog. With constant `h`, the preprocessing of
    [19, 7] stays within `Õ(n₀)`.

    **What this does and does not establish.** The hierarchy in `RoutesHier` is existential, with
    arbitrary edge types and no constraint on the endpoints of the embedded edges, since the
    length argument uses only the shape. So `RoutesHier` is logically close to the length bound
    it implies: a depth-0 hierarchy that cuts a route into pieces satisfies it, which is how
    `SatModel.lean` proves it realizable. What the formalization adds is that the route-length
    claim is now the conclusion of a checked argument from explicit structural parameters (the
    depth `h`, the per-level dilation `b`, the mixing length `τ`, `dil`), each matched to a
    statement of [19, 7] in the docstring of `routeG0`, together with the polynomial-size premise.
    That [19, 7] produce routes of this shape with these parameters still has to be checked
    against the papers. `routeG0` remains [PRIOR+].

### Tenth round: a self-contained development

38. **No dependency on the earlier formalization.** `ApspStoc` used to import six modules of the
    earlier formalization of an earlier version of the paper. The definitions and lemmas it used
    from them (weighted networks, `APSPSpec`, `Prof`, `lg`, `whp`, clusters, ports, aggregator sets,
    demands, overlays) are now in `ApspStoc/Base/`, with comments renumbered to the STOC submission;
    the unused parts are dropped, and one counting lemma moved to `Sec5bAux1.lean`. The package
    builds only `ApspStoc` and depends only on Mathlib. The definitions and statements that were
    kept are unchanged.

## Issues found while formalizing the STOC submission

Theorem 5.5:

1. **Step 5 must keep the existing virtual edges.** The paper says nodes "receive back the minimum
   new distance". For correctness, `x ∈ S₁∖S₂` must take `w'(x) = min(w(σ,x), BF candidates)`.
   Counterexample: `S = {x}`, `w(σ,x) = 3`, `δ = 2`, `Δ = 4`. Then `x ∈ S₁∖S₂` has no neighbour
   in `S₂`, so the second call would never reach `x`, although `dist(x) = 3 ≤ Δ`.
2. **The invariant "every node of a subproblem with offset `a` has distance in `[a, a+3δ]`" is not
   inductive by itself.** It has to be strengthened by three facts:
   - every virtual edge stands for a real path: `dist ≤ c + a`;
   - nodes with `dist ≤ a+Δ` have subproblem distance exactly `dist − a`;
   - `2^level` divides `a`.
3. **The thresholded subproblem must output "unknown" above its threshold.** Otherwise `S₂` cannot
   be read off the first call. In the base case `Δ = 1`, only estimates `≤ 1` are exact.
4. **How the recursive calls on the components of `S₁` and `S₁∖S₂` are run is not described.**
   The overall `Õ(n)` round bound adds costs over all subproblems, which requires running them one
   after another. We coordinate this with a token over the MST of `S` (`perCompR`).
5. **"Every aggregator knows `d(σ,v)` for all `v ∈ S₂`" needs explicit communication.** It is
   charged as one node→aggregator exchange.

Lemma 4.2:

6. **Aggregators do not know which endpoints lie in `S`.** An extra membership round is needed.
   Deciding whether an edge crosses two supernodes needs supernode IDs, so the GHS root is sent
   with the consensus value.
7. **Correctness uses three facts about the clusters that the paper leaves implicit:**
   - they cover all edges, so the union of per-cluster forests has the components of the
     contracted edges;
   - they are pairwise disjoint, so every crossing value is counted once;
   - the overlap bound, so the forest has `≤ fov·|S|` edges.
8. **An aggregate over no edges is undefined in Def. 2.5.** This is handled with an "absent" value.

Lemma 5.3:

9. **Statements the paper uses without proof:**
   - "cycles" are closed trails;
   - every node has an even number of left-over edges (by parity of the cluster degrees);
   - a segment's two ends are distinct;
   - a consistent orientation inside a cluster always exists (proved by contracting pairs).

Claims 3.4/3.5:

10. **The expansion argument needs a union bound over all subsets `A`.** The paper fixes one `A`.
    The bound works only because the Chernoff exponent is `Θ(|A| log n)`, which forces the
    constant `c` in `R = c(m/n)log n` to depend on the confidence.
11. **Survival needs the last step to move,** so mixing is needed after `2ℓ − 1` steps.
12. **Tokens start at the other endpoint of their port.** Stationarity still holds because
    `(v,e) ↦ (other end, e)` permutes all ports.
13. **"Each surviving walk leaves `A` with probability `Θ(1)`" hides a conditioning.** It is
    replaced by an unconditional count.
14. **The paper's round budget per step is larger than needed.** It takes `t = O(R log n)`; `2R +
    O(log n)` suffices.

Further points:

15. **Per-packet hop bound in Lemma 3.9.** "Each packet crosses polylog(n) edges" does not follow
    from Lemma 3.2 as stated, which only bounds the total number of messages. Here it is derived
    from the hierarchical route structure that `routeG0` ([PRIOR+]) provides
    (`RoutesHier.routesOK`).
16. **Smaller points**, each handled in the formalization:
    - in Lemma 3.8, `⌈deg_C(v)·n_C/m_C⌉` can exceed `deg_C(v)` when `m_C < n_C` (e.g. a star
      cluster); it is capped at `deg_C(v)`, and the bounds still hold;
    - Lemma 3.7 needs `n_C ≥ 2` and cluster degrees `≥ 1`; both hold for the clusters of an edge
      decomposition (`Base/AggregatorSet.lean`);
    - the expander decomposition [9] must give conductance with respect to the cluster's internal
      degrees for Theorem 3.3 to route inside clusters; `expDecomp` states that form;
    - a subroutine run on a cluster uses the global `n` as its size parameter, so that it fails
      with probability `n^{-c}` rather than `n_C^{-c}`;
    - the cost of computing `A(C)` (`clusterSetup`) and of gathering the IDs, which are needed to
      assign the sources to overlays (`embedConstruct`), is charged;
    - the random delays of [17] need shared randomness; gathering and broadcasting the delays is
      charged in `schedule`.

## Modelling notes and remaining trust points

* **Realizability.** Every contract's postcondition is proved satisfiable (`SatModel.lean`).
  Realizability is a necessary condition for a field to be true, not a sufficient one. In the
  satisfiability model the tasks `mst` and `clusterSetup` carry no formal postcondition, so their
  realizability is vacuous; the CONGEST semantics gives them real ones. `routeG0`'s realizability
  uses `Mixing`.
* **The CONGEST semantics.** It is a model of the paper's setting, and its definitions
  (`Core.lean`, `Tasks.lean`) must be read.
  - *Free local computation.* Local computation is unrestricted Lean functions.
  - *What nodes know.* After the preprocessing, a node's knowledge of its results is its local
    share of a global object (`Tasks.lean`):
    - a node knows the embedded paths through it, keyed by the overlay, the source and the
      source's key edge in the cluster, and its cluster slices `C ∩ inc(v)`;
    - a host knows the topology of its cluster;
    - after the random-walk construction, a node knows its part of `G₀` (`g0At`, `hopsAt`);
    - in routing tasks the cluster's `n_C` and `m_C` are public (the cluster setup broadcasts
      them).

    `embedConstruct_congest` proves that the preprocessing's protocol establishes exactly this
    knowledge.
  - *Topology delivery.* The cluster topologies reach the hosts in Theorem 3.10 as routing
    payloads (an edge and the digits of its weight per packet). This is part of the proof of
    `embedConstruct`, not an assumption.
  - *Bandwidth.* Messages are single words: an ID, an edge, or a number `≤ n + 3`. So an ID
    is assumed to fit in `O(log n)` bits.
  - *Initial knowledge.* In `thm_5_6_congest`, nodes know `V`, i.e. `n` and the set of all IDs
    (`Core.lean`; the algorithms use it, e.g. the node of smallest index as the root of a BFS
    tree and the rank of an ID as an overlay index). In the usual CONGEST model (KT1), a node
    knows only its own ID, its neighbours' IDs and `n`. `thm_5_6_kt1` (`Congest/KT1.lean`) is the
    main theorem in that model: IDs come from a known universe `U` of size `≤ (n+1)^idexp`, the
    node set `S ⊆ U` is unknown (`ktInst`, `KTDefs.lean`), and the algorithm first gathers the
    IDs deterministically ("Ninth round", item 36).
  - *Synchronisation.* All participants of a task halt in the same round.

* **Local functions.** `LocFn`s are arbitrary Lean functions, uniform over networks. Some use
  classical choice, e.g. picking a spanning forest or an argmin. Each stands for a deterministic
  local computation, but Lean does not check computability or locality beyond the types: an
  aggregator `.inr C` sees its cluster's edges and weights, and a node sees its incident weights
  and the data it holds.
* **Per-component execution.** `perCompR` (sequential execution on components) and the costs of
  `ringLE`/`aggUp`/`aggDown` are fields of the abstract toolkit, and theorems in the CONGEST
  semantics (sixth round).
* **Approximate SSSP tree.** `approxRed` assumes that [37] provides approximate distances
  *together with* an approximate shortest-path tree. The paper relies on this for the parents in
  Theorem 5.5 ("parent information is provided by the approximate SSSP algorithm").
* **Virtual nodes in Eulerian orientation.** `eoVirt` is attributed to [37] as the paper does. If
  that part is regarded as the paper's own contribution, it is the one remaining unproved step.

## Building and checking

```
lake build               # builds ApspStoc
lake env lean scripts/CheckAxioms.lean
```

`tools/leand.py` is a small helper that keeps a Lean language server running for fast
incremental checks: `python3 tools/leand.py serve DIR` and `python3 tools/leand.py check DIR FILE`.

## License

The Lean sources, the build files and the scripts in `tools/` are licensed under the GNU Affero
General Public License, version 3 only (SPDX identifier `AGPL-3.0-only`); see `LICENSE`. The
paper itself is not covered by this license.
