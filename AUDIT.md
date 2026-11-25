# Audit guide

This package contains the Lean formalization of Theorem 5.6 (= Theorem 1.1) of
"Near-Singularly Optimal Distributed APSP" by Dufoulon, Pai, Pandurangan, Robinson and Way (the
STOC submission of November 5, 2026; library `ApspStoc/`):

> There is a randomized Monte-Carlo distributed algorithm solving weighted undirected APSP in
> `Õ(n)` rounds and `Õ(n²)` messages w.h.p.

The theorem to check is **`APSP.Stoc.Congest.thm_5_6_kt1`** (`ApspStoc/Congest/KT1.lean`). It
states Theorem 5.6 for concrete protocols in an executable synchronous CONGEST semantics. Nodes
start with only their own ID, their incident edges with their weights, and `n`. The theorem
assumes the cited prior work (the structure `CAssume`) and a mixing bound for random walks
(`Mixing`).

This guide says what a reviewer has to read to be convinced that `thm_5_6_kt1` accurately
formalizes Theorem 5.6, taking the Lean kernel on trust (sections 2–3). It also says what can be
skipped (section 4). It is about 1,100 lines: 164 definitions in 14 files, about 670 lines of
code and the rest docstrings, out of about 41,000. About 200 of them (the statement, the model
and the semantics) suffice to check what the theorem says. The rest are the hypotheses and the
definitions they use, which is where knowledge of the literature is needed. These counts take
every definition reachable from `thm_5_6_kt1`, `CAssume` and `Mixing`, stopping at Mathlib and
excluding proofs. The module docstrings of `Core.lean` and `Tasks.lean` (about 60 lines) help
but are not required.

`README.md` gives the overview, the proved results, the issues found in the paper and the
history of repairs. The development depends only on Mathlib.

## 1. Build and check

Requirements: `elan`, which installs the toolchain named in `lean-toolchain` (Lean 4.35.0), and
network access to fetch Mathlib v4.35.0. To install `elan` (it provides `lean` and `lake`):

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.elan/env
```

Then, in the unpacked or cloned directory:

```
lake exe cache get                     # prebuilt Mathlib (otherwise Mathlib is compiled: hours)
lake build                             # expected: "Build completed successfully"
lake env lean scripts/CheckAxioms.lean # expected: only [propext, Classical.choice, Quot.sound]
grep -rn "sorry\|admit\|^axiom" ApspStoc --include='*.lean'   # expected: no output
```

`scripts/CheckAxioms.lean` prints the axioms of `thm_5_6_kt1` and of every other main result. Any
`sorry`, added axiom or `native_decide` would show up there. It also prints the statement of
`thm_5_6_kt1`. Trusted without reading: the Lean kernel, the toolchain, and the Mathlib
definitions used (`SimpleGraph`, `Finset`, `Sym2`, `ℝ`).

## 2. The statement

```lean
theorem thm_5_6_kt1 (H : CAssume) (hmix : Mixing) (wexp c idexp : ℕ) :
    ∃ (A : ℕ → CAlg) (C k K : ℕ), ∀ {U : Type} [Fintype U] [DecidableEq U] (S : Finset U)
      (N : WNet S), 1 ≤ S.card → Fintype.card U ≤ (S.card + 1) ^ idexp →
      (∀ e ∈ N.G.edgeSet, N.w e ≤ S.card ^ wexp) →
      ∃ (p : Prof U) (δ : ℝ),
        ImplI (A S.card U) (ktInst S N) (inOf (fun _ => ()))
          (postOf (ktInst S N) (fun z : Agent U → (U → ℕ × U) => APSPSpec N (ktOut S z))) p δ ∧
        p.rounds ≤ C * lg S.card ^ k * S.card ∧
        p.msgs ≤ C * lg S.card ^ k * S.card ^ 2 ∧
        δ ≤ (K : ℝ) / (S.card : ℝ) ^ c
```

Check these points against the paper:

* **Quantifiers.** For every weight exponent `wexp`, confidence exponent `c` and ID-range exponent
  `idexp`, one algorithm family `A` and constants `C, k, K` are chosen *before* the network. `A n`
  is the protocol for `n` nodes, so `n` is known. `A n U` is a protocol over the ID universe `U`:
  it is one program for every node set `S ⊆ U`.
* **Networks.** `S` is the node set, `n = |S| ≥ 1`. `N` is a connected weighted graph on `S`
  (`WNet`: positive integer weights, connected), with weights `≤ n^wexp`. IDs come from a universe
  of size `≤ (n+1)^idexp`, so an ID has `O(log n)` bits.
* **Correctness.** `APSPSpec`: every node outputs, for every node `u`, the exact weighted distance
  and, for `u ≠ v`, a neighbour on a shortest path. That is the paper's output plus next hops.
* **Costs.** `≤ C·lg^k n·n` rounds and `≤ C·lg^k n·n²` messages, i.e. `Õ(n)` and `Õ(n²)`.
* **Probability.** The run fails (wrong output, a budget exceeded, or no simultaneous halting) with
  probability `≤ K/n^c`, i.e. w.h.p. for every fixed `c`.

## 3. What must be read: the trusted base

### 3.1 The definitions in the statement

| Where | Definitions | What to check |
|---|---|---|
| `ApspStoc/Base/Basic.lean` | `WNet`, `wdist`, `SSSPSpec`, `APSPSpec`, `Prof`, `lg` | `wdist` is the minimum weight of a walk. `APSPSpec` asks for exact distances and shortest-path next hops at every node. `Prof` is a cost profile: rounds, per-edge load, messages. |
| `ApspStoc/Congest/KTDefs.lean`, first 60 lines | `ktView`, `ktInst`, `ktOut` | The instance runs on the edges of `N` and its participants are `S`. Each node knows only its ID and its incident edges with their weights (`ktView`). It does not know `S`, and it gets no other public data. `ktOut` reads node `v`'s outputs for the nodes of `S` and maps a next hop outside `S` to `v` itself, which `APSPSpec` rejects. |
| `ApspStoc/Congest/Tasks.lean` | `CAlg`, `inOf`, `postOf` | An algorithm is a protocol for every node set. `postOf` reads the outputs of the hosted agents (here the physical nodes of `S`) at their stated type. |
| `ApspStoc/Defs.lean` | `Agent`, `Word` | Agents are the physical nodes and virtual aggregators. A word is an ID, an edge or a number. |

### 3.2 The semantics: `ApspStoc/Congest/Core.lean`, lines 1–190

This is a model of synchronous CONGEST, and judging that it is faithful is part of the review.
The module docstring summarizes it. Check:

* `NCtx`, `Proto`: a node's program sees only its local context (ID, local views, public numbers,
  embedded paths). It never sees the network. Initial states depend on the context, the node's
  inputs and its own seed.
* `msg`, `step`, `st`: rounds are synchronous. A node that has not halted sends at most one word
  to each neighbour per round, and only along edges of the instance. A word is delivered only if
  `WordOK (Fintype.card V)` holds: numbers are `≤ |U| + 3`, IDs and edges are single words. Halted
  nodes are frozen and silent.
* `msgsUpTo`, `loadUpTo`: messages, and messages per edge (both directions), are counted up to the
  halting round.
* `HaltsAt`, `ProperUpTo`, `Succ`: success means all participants halt in the same round
  `t ≤ p.rounds`. No participant may try to send to a non-neighbour before `t`. Messages and loads
  must stay within budget, and the outputs read at `t` must satisfy the postcondition.
* `failProb`, `ImplI`: seeds are independent and uniform, one per node, from a finite type. The
  failure probability is the exact fraction of seed vectors for which the run does not succeed.

Modelling choices to accept or reject:
* local computation is free, and seeds are unbounded;
* a message is one word (an ID, an edge, or a number `≤ |U| + 3`), not an arbitrary
  `O(log n)`-bit string;
* all nodes must halt in the same round, which is stricter than usual.

### 3.3 The hypotheses: `Mixing` and `CAssume`

Lean checks that the hypotheses imply the conclusion, not that they are true. A false hypothesis
makes the theorem vacuous, as happened with an earlier `schedule` (`README.md`, item 31).
Checking the hypotheses is the part of the review that needs the literature.

**`Mixing`** (`ApspStoc/G0Model.lean`, about 160 lines): the mixing bound for lazy random walks on
expanders (Jerrum–Sinclair / Cheeger), for the seeded walk defined there. Check that
`lazyStep`/`seedRange` give the lazy walk (stay with probability 1/2, otherwise cross a uniform
incident edge; also proved as `step1_formula` in `G0AuxWalk.lean`). Then check that the stated
bound is a true theorem for some constant `Km`.

**`CAssume`** (`ApspStoc/Congest/Assume.lean`, 220 lines): 11 fields, each with a docstring
giving its source and justification. Four are algorithm constructors (`sched`, `mstAlg`,
`approxAlg`, `eoAlg`). The other seven are contracts: they state that the constructed algorithms
solve their tasks within their costs, in this semantics. Each contract must be a true statement
of the cited result, costs included:

| Field | Source | What to check |
|---|---|---|
| `expDecomp` | [9] (Lemma 2.8) | One step of expander decomposition with known `φ⁻¹`: rounds `K·lg^k ν·φ⁻⁴`, messages `K·lg^k ν·φ⁻⁴·|F|`, and the fraction of removed edges. |
| `ghs` | [16] | A rooted spanning forest of the subgraph `(S, F)` (one tree per component), on an overlay task, in `K·lg ν·(sz+1)` rounds and `K·lg ν·(|F| + |S|)` messages (`SpanForest`). |
| `mstRed` | [16, 38] | MST in `O(log n)` Minor-Aggregation rounds; costs are `K·lg ν` times one round's. |
| `approxRed` | [37] (Lemma 5.1) | `3/2`-approximate distances **and** an approximate shortest-path tree (`ApproxSpec` includes the parent condition), from polylog Minor-Aggregation rounds and Eulerian orientations. |
| `eoVirt` | [37] | Eulerian orientation with virtual nodes, reduced to Minor-Aggregation and physical orientation; the algorithm gets a public bound `kb` on the number of virtual nodes. If this is the paper's own contribution rather than [37]'s, it is the one unproved step. |
| `schedule` | [17, Theorem 1.1] | `n` instances on separate overlays run simultaneously in `K·lg^k ν·(Cg + R + ν)` rounds. Load and messages are multiplied by `K·lg^k ν` (instance tags, since a message is one word), plus `ν` per edge and `ν²` messages to share the random delays over a BFS tree of `G`. `R + Cg ≤ (n+4)^kB`, so a delay fits in `kB` words. |
| `routeG0` | [19, 7] (Lemma 3.2), **[PRIOR+]** | Routing in a `1/polylog`-expander cluster via the virtual expander `G₀`, which has polynomial size (`n₀ ≤ K·n`). The costs include recording the routes: a factor `dil + 1` on rounds, `(dil + 1)²` on messages. **Stronger than the paper's Lemma 3.2:** the recorded routes have the shape `RoutesHier`. They come from the forwarding procedure of a routing hierarchy of constant depth `h` [19, §3.1–3.2], [7, §3], with polylog per-level dilation `b` and mixing length `τ`. From this, the per-route length bound `dil·τ·(1 + (2b+1)^h(b+1))` is proved (`RoutesHier.routesOK`). The hierarchy is existential and constrains only the shape, so this is logically close to that length bound. Check against [19, 7] that their routes have this shape with these parameters. |

What the contracts mean depends on these definitions, which also have to be read:

* `ApspStoc/Congest/Tasks.lean` (about 370 lines, apart from a few lemmas): `CImplT`, the meaning
  of every task. It covers:
  - the instances `ioInst`, `baseInst`, `clInst0`, `clInst`;
  - what nodes know at the start: `ioEmb`, `clLoc`, `ekAt`, `dAt`, `g0At`, `hopsAt`;
  - the routing data `rinAt`, `rkAt`, `PayloadOK`, and `SetupSpec`.
* `ApspStoc/Toolkit.lean`, lines 113–171 only: the task type `Task` and `maTask`, `eoTask` (not
  the toolkit's fields).
* `ApspStoc/Defs.lean`:
  - `IsExpander`, `onEdges`, `ConnSet`, `comps`, `nbrsIn`, `SpanForest`, `footprint`;
  - `Msg`, `Msg.Small`, `AggOf`, `MAInst`, `MASpec`, `EOInst`, `EOSpec`, `SubIn`, `subInput`,
    `ApproxSpec`, `lview`;
  - `G0Data`, `Hier`, `Hier.Dil`, `Hier.Gen`, `Hier.Route`, `RoutesHier`.
* `ApspStoc/G0Model.lean`: `TrueParams` and the random-walk definitions it uses.
* `ApspStoc/Base/`:
  - `whp` (`Basic.lean`);
  - `Overlays`, `rho`, `rhoAgg`, `aggLen`, `EmbValid` (`Overlays.lean`);
  - `nodes`, `Port` (`Clusters.lean`);
  - `Demand`, `allPorts` (`Demands.lean`).

A contract can be wrong in three ways. Look for each:

* **too strong a cost.** Check every cost against the bandwidth of one word per edge and round.
  E.g. the earlier `schedule` added the instances' messages with coefficient one, which is
  impossible when every message must carry an instance tag.
* **too much knowledge.** A task meaning in `Tasks.lean` that gives nodes data they could not have
  would make a contract easier than the cited result.
* **an unsatisfiable or too weak postcondition.** Unsatisfiability is excluded by a Lean proof:
  `ApspStoc/SatModel.lean` shows every postcondition is satisfiable whenever the premises hold,
  using `Mixing` for `routeG0`. That is evidence about outputs only, not about costs. To rely on
  it, check that `Sat` in `SatModel.lean` states each task's postcondition faithfully.

A further check: every round budget must be computable by the participants (they halt
together). For the cited contracts this is a matter of reading, e.g. `schedule` and `eoVirt` get
public bounds as parameters.

## 4. What need not be read

Every proof is checked by Lean. In particular, these can be skipped entirely:

| Files | Content |
|---|---|
| `Congest/KTSim.lean`, `KTGraph.lean`, `KTGather*.lean`, the proof in `KT1.lean` | the ID-gathering phase (leader election, BFS tree, numbering, upload and broadcast of the IDs) and the simulation of the inner algorithm |
| `Congest/Model.lean` (`toToolkit`, `thm_5_6_congest`) | the main theorem for nodes that know all IDs, from which `thm_5_6_kt1` is derived |
| `Congest/Comb.lean`, `Rules.lean`, `Notify.lean`, `TreeCast*.lean`, `Setup*.lean`, `ExpDiam.lean` | the standard CONGEST facts, proved in the semantics |
| `Congest/AggUpDown*.lean`, `RingComb.lean`, `RingLE*.lean`, `PerComp*.lean`, `RWCouple.lean`, `RWLink*.lean`, `EmbConstruct*.lean` | the paper's own steps (Lemma 2.2, ring leader election, execution on components, the random-walk construction of `G₀`, the per-cluster preprocessing), proved in the semantics |
| `Toolkit.lean` (apart from lines 113–171), `Main.lean` (`thm_5_6`), `Statements.lean`, `Polylog.lean` | the abstract layer. `thm_5_6` is the theorem relative to an arbitrary judgement satisfying the toolkit's fields. `toToolkit` fills these fields from the semantics, and Lean checks that they match. `Assume.lean` is generated from the toolkit (`python3 tools/gen_assume.py`) and carries the same docstrings. |
| `Sec3.lean`, `G0*.lean`, `Sec4.lean`, `Sec5EO*.lean`, `Sec5a.lean`, `Sec5b*.lean`, `MainOf.lean`, `Basics.lean` | the paper's lemmas and theorems (Lemma 2.10, Theorem 3.3, Claims 3.4/3.5, Lemmas 3.8–3.9, Theorem 3.10, Lemma 4.2, Lemmas 5.3/5.4, Theorems 5.5/5.6, Observation 2.3) |
| `SatModel.lean`, `Consistency.lean`, `Real*.lean`, `Realizability.lean` | evidence that the hypotheses are consistent and their postconditions satisfiable; not needed for soundness |
| `Base/` apart from the definitions in 3.1 and 3.3 | lemmas about logarithms, cost profiles, distances, aggregator sets (Lemma 3.7), demands (Lemmas 3.8, 3.9) and overlays (Theorem 3.10) |

**The algorithm.** Theorem 5.6 says only that an algorithm exists, so whether the protocol defined
in the proofs matches the paper's pseudocode does not affect the truth of the statement. It
matters only for the claim that *the paper's* algorithm works. What is verified is a repaired
version (`README.md`, "Issues found while formalizing the STOC submission" and the rounds of
repairs). Its main parts are:
* `maAlg` (`Sec4.lean`);
* the physical Eulerian orientation (`Sec5EO*.lean`);
* `recAlg`/`topAlg` (`Sec5bAux2.lean`);
* the protocols in `Congest/`.

## 5. History

`README.md` records the audits and the repairs they led to: "Repairs after the independent audit"
and the second to tenth rounds. Repairs that changed what has to be read:

* the CONGEST semantics (fifth round);
* proper sends, key-edge knowledge of paths, routing payloads, local knowledge of `G₀` (sixth
  round);
* the costs of `schedule`, which was false as stated, and of route recording in `routeG0`
  (seventh round);
* polynomially bounded parameters for `schedule` (eighth round);
* the KT1 model with `thm_5_6_kt1`, and the route shape `RoutesHier` in `routeG0` (ninth round);
* the basic definitions moved into `ApspStoc/Base/`, so that the development depends only on
  Mathlib (tenth round).

`ApspStoc/Realizability.lean` contains Lean regression tests for the counterexamples of the first
audit.

## 6. Contents

```
README.md, AUDIT.md          overview and this guide
LICENSE                      AGPL-3.0-only (the sources and scripts; not the paper)
lakefile.toml, lake-manifest.json, lean-toolchain
ApspStoc.lean, ApspStoc/     formalization of the STOC submission. Congest/: the CONGEST semantics
                             (Core, Tasks), the cited results as hypotheses (Assume), the proofs
                             of all other steps, thm_5_6_congest (Model) and thm_5_6_kt1 (KTDefs,
                             KT1). Base/: networks, distances, APSPSpec, cost profiles, clusters,
                             demands, overlays. The rest: the paper's lemmas, the abstract layer
                             (Toolkit, Main) and the satisfiability model (SatModel, Real*).
scripts/CheckAxioms.lean     axiom check
tools/leand.py               optional helper keeping a Lean server alive for fast re-checks
tools/gen_assume.py          generates Congest/Assume.lean from the toolkit fields
```
