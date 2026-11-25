import ApspStoc.Congest.Rules

/-!
# The assumed contracts in the CONGEST semantics

`CAssume` collects the toolkit fields tagged [PRIOR] and [PRIOR+] — the theorems of prior work —
stated for the concrete judgement `CImplT` of `Tasks.lean`: their algorithm constructors are concrete algorithms (`CAlg`), and their contracts
are claims about concrete protocols. The statements are generated from `Toolkit.lean` by replacing
`Impl` with `CImplT` and `Alg` with `CAlg`; `Model.lean` checks that they match the toolkit's
fields (the construction of a `Toolkit` from a `CAssume` typechecks only if they do).
-/

namespace APSP.Stoc.Congest

open APSP Finset

/-- The [PRIOR] and [PRIOR+] contracts of the toolkit, for the CONGEST semantics (the [STD] and
[IMPL] contracts are proved: `Model.lean`). -/
structure CAssume where
  /-- [PRIOR] random-delay scheduler [17] (confidence `c`, size bound `ν`, public bounds `R` on
  the rounds and `Cg` on the congestion of the instances: `sched c ν R Cg A`) -/
  sched : ℕ → ℕ → ℕ → ℕ → CAlg → CAlg

  /-- [PRIOR] MST in Minor-Aggregation rounds (size bound `ν`), using the given MA-round algorithm -/
  mstAlg : ℕ → CAlg → CAlg

  /-- [PRIOR] the approximate-SSSP algorithm of [37] (size bound `ν`), using the given MA-round and
  Eulerian-orientation algorithms -/
  approxAlg : ℕ → CAlg → CAlg → CAlg

  /-- [PRIOR] the treatment of virtual nodes in Eulerian orientation of [37] (size bound `ν`,
  public bound `kb` on the number of virtual nodes: `eoAlg ν kb M P`), using the given MA-round
  algorithm and an algorithm for physical instances -/
  eoAlg : ℕ → ℕ → CAlg → CAlg → CAlg

  /-- [PRIOR] Lemma 2.8 (Chen–Meierhans–Probst Gutenberg–Saranurak [9]), run on the subgraph with
  edge set `F`: a vertex partition into `1/φinv`-expanders (conductance w.r.t. degrees inside the
  part; we keep the edge sets of the parts with at least one edge) with `Õ(1/φinv)·|F|` crossing
  edges, in `Õ(φinv⁴)` rounds and `Õ(φinv⁴ |F|)` messages. The algorithm is `A ν φinv`: the
  round budget `K·lg^k ν·φinv⁴` depends on `φinv`, so the nodes must know `φinv` to know when the
  run ends (all nodes take part and halt together). -/
  expDecomp : ∀ c : ℕ, ∃ (K k Kδ : ℕ) (A : ℕ → ℕ → CAlg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (F : Finset (Sym2 V)) (φinv : ℕ),
    F ⊆ N.G.edgeFinset → 1 ≤ φinv →
    CImplT (A ν φinv) N (.expDecompOnce F φinv
        (fun P => (∀ C ∈ P, C ⊆ F ∧ C.Nonempty ∧ IsExpander C φinv) ∧
        (∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint (nodes C) (nodes C')) ∧
        φinv * (F \ P.biUnion id).card ≤ K * lg ν ^ k * F.card))
      (Prof.mk (K * lg ν ^ k * φinv ^ 4) (onEdges F (2 * K * lg ν ^ k * φinv ^ 4))
        (K * lg ν ^ k * φinv ^ 4 * F.card))
      (whp Kδ c ν)

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
  routeG0 : ∀ (c Kφ kφ pw : ℕ), ∃ (K k Kδ h Kb kb Kτ : ℕ) (A : ℕ → CAlg), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (C : Finset (Sym2 V))
    (P : Finset (Port V)) (φC : ℕ) (g : G0Data) (D : Demand V) (lam : ℕ), C ⊆ N.G.edgeFinset →
    IsExpander C φC → φC ≤ Kφ * lg ν ^ kφ → P ⊆ allPorts C →
    P.card ≤ g.n0 → g.n0 ≤ Kφ * ν → g.m0 ≤ Kφ * lg ν ^ kφ * g.n0 → g.φinv ≤ Kφ * lg ν ^ kφ →
    D.SupportedOn P → (∀ x, D.load x ≤ lam) →
    CImplT (A ν) N (.routeViaG0 C P g D lam pw (fun r => RoutesHier C D r
        (2 * (K * lg ν ^ k * (g.n0 + lam) * (g.cong + g.dil)))
        h (Kb * lg ν ^ kb) (Kτ * (g.φinv + 1) ^ 2 * lg ν) g.dil))
      (Prof.mk (K * lg ν ^ k * (g.n0 + lam) * (g.cong + g.dil) * (g.dil + 1))
        (onEdges C (2 * (K * lg ν ^ k * (g.n0 + lam) * (g.cong + g.dil) * (g.dil + 1))))
        (K * lg ν ^ k * (g.m0 * g.n0 + D.size) * (g.dil + 1) ^ 2))
      (whp Kδ c ν)

  /-- [PRIOR] Gallager–Humblet–Spira [16] on the subgraph `(S, F)` (every node of `S` knows its
  `F`-neighbours): a rooted spanning forest of `(S, F)` (one tree per component, rooted at its
  leader) in `O(|S| log n)` rounds, `O(|F| + |S| log n)` messages, `O(log n)` messages per edge.
  It only uses edges inside `S`, so it suffices that the nodes of `S` take part (`S ⊆ Pt`). -/
  ghs : ∃ (K : ℕ) (A : ℕ → CAlg), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (ν : ℕ),
    Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (F : Finset (Sym2 V))
    (x : Agent V → Option (Finset V)), F ⊆ N.G.edgeFinset → (∀ e ∈ F, ∀ v ∈ e, v ∈ S) →
    S.card ≤ sz → S ⊆ Pt → (∀ v, x (.inl v) = if v ∈ S then some (nbrsIn F v) else none) →
    CImplT (A ν) N (.io E j sz Pt (Option (Finset V)) (Option V × V) x
      (fun y => SpanForest S F (fun v => (y (.inl v)).1) (fun v => (y (.inl v)).2)))
      (Prof.mk (K * lg ν * (sz + 1)) (onEdges F (K * lg ν)) (K * lg ν * (F.card + S.card))) 0

  /-- [PRIOR] MST (hence leader election and spanning trees per component) in `O(log n)`
  Minor-Aggregation rounds with `O(1)`-word values (GHS in the Minor-Aggregation model [16, 38]).
  The participants contain the footprint of `S`; the Minor-Aggregation rounds run with the same
  participants. -/
  mstRed : ∃ K : ℕ, ∀ (M : CAlg) {V : Type} [Fintype V] [DecidableEq V] {N : WNet V} (ν : ℕ),
    Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (p : Prof V) (δ : ℝ),
    S.card ≤ sz → footprint E j S ⊆ Pt →
    (∀ I : MAInst V, I.S ⊆ S → I.Small K (ν ^ K) → CImplT M N (maTask N.G E j sz Pt I) p δ) →
    CImplT (mstAlg ν M) N (.mst E j sz Pt S) ((K * lg ν) • p) (((K * lg ν : ℕ) : ℝ) * δ)

  /-- [PRIOR] Lemma 5.1 (Rozhoň–Grunau–Haeupler–Zuzic–Li [37]) with `ε = 1/2`, on a connected set
  `S` with a virtual source: `3/2`-approximate SSSP (distances and an approximate shortest-path
  tree) on `G[S]` reduces to `polylog` Minor-Aggregation rounds (with `polylog`-word values whose
  numbers are polynomial in `ν` and the weights) and `polylog` Eulerian-orientation instances on
  graphs `H ⊆ G[S] + polylog` virtual nodes. The participants contain the footprint of `S`; the
  sub-tasks run with the same participants. -/
  approxRed : ∀ Bw : ℕ, ∃ K k : ℕ, ∀ (M Eo : CAlg) {V : Type} [Fintype V] [DecidableEq V]
    {N : WNet V} (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V)
    (w0 : V → Option (ℕ × V)) (pM pE : Prof V) (δM δE : ℝ),
    ConnSet N.G S → S.card ≤ sz → footprint E j S ⊆ Pt → (∀ e ∈ N.G.edgeFinset, N.w e ≤ ν ^ Bw) →
    (∀ v c p, w0 v = some (c, p) → c ≤ ν ^ Bw) →
    (∀ I : MAInst V, I.S ⊆ S → I.Small (K * lg ν ^ k) (ν ^ (K * (Bw + 1))) →
      CImplT M N (maTask N.G E j sz Pt I) pM δM) →
    (∀ H : EOInst V, H.S = S → H.WF N.G → H.k ≤ K * lg ν ^ k →
      CImplT Eo N (eoTask E j sz Pt H) pE δE) →
    CImplT (approxAlg ν M Eo) N (.io E j sz Pt (SubIn V) (Option (ℕ × V)) (subInput S w0)
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
  eoVirt : ∃ K k : ℕ, ∀ (M P : CAlg) {V : Type} [Fintype V] [DecidableEq V] {N : WNet V}
    (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt : Finset V) (H : EOInst V) (kb : ℕ) (pM pP : Prof V)
    (δM δP : ℝ), ConnSet N.G H.S → H.WF N.G → H.S.card ≤ sz → H.k ≤ kb →
    footprint E j H.S ⊆ Pt →
    (∀ I : MAInst V, I.S ⊆ H.S → (∀ b, K * lg ν ^ k * (kb + 1) ^ 2 ≤ b → I.Small b (ν ^ K)) →
      CImplT M N (maTask N.G E j sz Pt I) pM δM) →
    (∀ H' : EOInst V, H'.S = H.S → H'.Physical → H'.Hp ⊆ H.Hp → H'.WF N.G →
      CImplT P N (eoTask E j sz Pt H') pP δP) →
    CImplT (eoAlg ν kb M P) N (eoTask E j sz Pt H)
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
  schedule : ∀ c kB : ℕ, ∃ K k Kδ : ℕ, ∀ (A : CAlg) {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (β : Type) (R Cg : ℕ)
    (spec : V → (V → β) → Prop) (p : V → Prof V) (δ : V → ℝ),
    R + Cg ≤ (ν + 4) ^ kB →
    (∀ s, CImplT A N (.io E (Fintype.equivFin V s : ℕ) (Fintype.card V) univ V β (fun _ => s)
      (fun y => spec s (fun v => y (.inl v)))) (p s) (δ s)) →
    (∀ s, (p s).rounds ≤ R) → (∀ e, ∑ s, (p s).load e ≤ Cg) →
    CImplT (sched c ν R Cg A) N (.compute (some E) (V → β) (fun o => ∀ s, spec s (fun v => o v s)))
      (Prof.mk (K * lg ν ^ k * (Cg + R + ν))
        ((K * lg ν ^ k) • (∑ s, (p s).load + fun _ => ν))
        (K * lg ν ^ k * (∑ s, (p s).msgs + ν ^ 2)))
      (∑ s, δ s + whp Kδ c ν)

end APSP.Stoc.Congest
