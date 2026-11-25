import ApspStoc.Base.Overlays

/-!
# Semantic notions for the formalization of the STOC submission

This file collects the mathematical (algorithm-independent) notions used to state the tasks of the
algorithm: auxiliary graph notions, the agents of an overlay graph, uniform local computations,
messages, aggregates (Definition 2.4), Minor-Aggregation rounds (Definition 2.5), Eulerian
orientation instances (Section 5.1), the ring structure of the proof of Lemma 5.3, and the
distances from a virtual source used by Lemma 5.4 and Theorem 5.5.

Theorem numbers refer to the STOC submission of the paper.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Auxiliary notions -/

/-- Edges of `C` crossing the cut `(S, V \ S)`. -/
noncomputable def cutEdges (C : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) := by
  classical exact C.filter (fun e => (∃ u ∈ e, u ∈ S) ∧ (∃ u ∈ e, u ∉ S))

/-- Volume of a node set inside cluster `C`. -/
def vol (C : Finset (Sym2 V)) (S : Finset V) : ℕ := ∑ v ∈ S, degIn C v

/-- `C` (as a graph on `nodes C`) has conductance at least `1/φinv` (Definition 2.6). -/
def IsExpander (C : Finset (Sym2 V)) (φinv : ℕ) : Prop :=
  ∀ S ⊆ nodes C, min (vol C S) (vol C (nodes C \ S)) ≤ φinv * (cutEdges C S).card

/-- Parameters of the virtual expander `G₀` of Theorem 3.3 (nodes, edges, inverse conductance,
congestion and dilation of its embedding into the cluster). -/
structure G0Data where
  n0 : ℕ
  m0 : ℕ
  φinv : ℕ
  cong : ℕ
  dil : ℕ

/-- The recorded routes of a demand stay in `C`, have length `≤ d`, and put at most `B`
packets on every edge. -/
structure RoutesOK (C : Finset (Sym2 V)) (D : Demand V) (r : Routes V) (d B : ℕ) : Prop where
  walk : ∀ pq ∈ D, IsEdgeWalk (r pq) pq.1.1 pq.2.1
  local_ : ∀ pq ∈ D, ∀ e ∈ r pq, e ∈ C
  len : ∀ pq ∈ D, (r pq).length ≤ d
  cong : ∀ e, (D.map (fun pq => (r pq).count e)).sum ≤ B

/-- **A routing hierarchy** (Ghaffari–Kuhn–Su [19, §3.1–3.2]): levels `i = 0, 1, …` with edge
types `E i`; every edge of level `i + 1` is embedded into level `i` as a list of level-`i` edges
(`emb i`); every level-0 edge is a walk of `G₀` (`base`; `G0E` is the type of edges of `G₀`); every
edge of `G₀` is a walk of the cluster (`phys`). -/
structure Hier (V : Type) where
  E : ℕ → Type
  emb : ∀ i, E (i + 1) → List (E i)
  G0E : Type
  base : E 0 → List G0E
  phys : G0E → List (Sym2 V)

namespace Hier
variable (H : Hier V)
/-- the dilations: `b` per level, `τ` from level 0 to `G₀` (mixing-length walks), `dil` from `G₀`
to the cluster -/
structure Dil (b τ dil : ℕ) : Prop where
  emb : ∀ i e, (H.emb i e).length ≤ b
  base : ∀ e, (H.base e).length ≤ τ
  phys : ∀ e, (H.phys e).length ≤ dil

/-- the level-`i` routes produced by the forwarding procedure of [19, §3.2] with depth `h`:
terminal routes use at most `b` edges of level `h`; at a level `i < h` a route is one route of
level `i + 1` expanded into level `i`, or two such routes joined by one edge of level `i` (via a
portal). Only the shape is recorded, which is all the length bound uses; that the routes are walks
between the right endpoints is part of `RoutesHier.walk`. -/
inductive Gen (h b : ℕ) : (i : ℕ) → List (H.E i) → Prop
  | term (l : List (H.E h)) : l.length ≤ b → Gen h b h l
  | one {i : ℕ} : i < h → ∀ l : List (H.E (i + 1)), Gen h b (i + 1) l →
      Gen h b i (l.flatMap (H.emb i))
  | two {i : ℕ} : i < h → ∀ (l₁ l₂ : List (H.E (i + 1))) (e : H.E i), Gen h b (i + 1) l₁ →
      Gen h b (i + 1) l₂ → Gen h b i (l₁.flatMap (H.emb i) ++ e :: l₂.flatMap (H.emb i))

/-- a physical route produced by the hierarchy: a redistribution walk of at most `τ` edges of `G₀`,
then a generated level-0 route expanded into `G₀`, all expanded into the cluster -/
def Route (h b τ : ℕ) (r : List (Sym2 V)) : Prop :=
  ∃ (w : List H.G0E) (l : List (H.E 0)), w.length ≤ τ ∧ H.Gen h b 0 l ∧
    r = (w ++ l.flatMap H.base).flatMap H.phys
end Hier

/-- The routes of [19, 7]: walks in `C` between the endpoints, putting at most `B` packets on
every edge, and produced by a routing hierarchy of depth `h` with dilations `b`, `τ`, `dil`. -/
structure RoutesHier (C : Finset (Sym2 V)) (D : Demand V) (r : Routes V) (B h b τ dil : ℕ) :
    Prop where
  walk : ∀ pq ∈ D, IsEdgeWalk (r pq) pq.1.1 pq.2.1
  local_ : ∀ pq ∈ D, ∀ e ∈ r pq, e ∈ C
  cong : ∀ e, (D.map (fun pq => (r pq).count e)).sum ≤ B
  hier : ∃ H : Hier V, H.Dil b τ dil ∧ ∀ pq ∈ D, H.Route h b τ (r pq)

/-- expanding every element of a list into at most `b` elements -/
lemma length_flatMap_le {α β : Type} {f : α → List β} {b : ℕ} (hf : ∀ a, (f a).length ≤ b)
    (l : List α) : (l.flatMap f).length ≤ l.length * b := by
  rw [List.length_flatMap]
  simpa using List.sum_le_length_nsmul (l.map fun a => (f a).length) b
    (by simpa using fun a _ => hf a)

/-- one level less: `(2b + 1)^(h - i) c = (2b + 1) · (2b + 1)^(h - (i + 1)) c` for `i < h` -/
lemma pow_sub_eq_mul_pow_sub_succ {b h i : ℕ} (hi : i < h) (c : ℕ) :
    (2 * b + 1) ^ (h - i) * c = (2 * b + 1) * ((2 * b + 1) ^ (h - (i + 1)) * c) := by
  rw [show h - i = h - (i + 1) + 1 by omega, pow_succ]; ring

omit [Fintype V] [DecidableEq V] in
/-- **The hop count of the forwarding procedure**: a generated level-`i` route has at most
`(2b + 1)^(h - i) (b + 1)` edges (the recurrence `L_i ≤ 2b L_{i+1} + 1`, `L_h ≤ b`). -/
theorem Hier.Gen.length_le {H : Hier V} {h b τ dil i : ℕ} {l : List (H.E i)}
    (hD : H.Dil b τ dil) (hg : H.Gen h b i l) : l.length ≤ (2 * b + 1) ^ (h - i) * (b + 1) := by
  induction hg with
  | term l hl => simp only [Nat.sub_self, pow_zero, one_mul]; omega
  | @one i hi l _ ih =>
    rw [pow_sub_eq_mul_pow_sub_succ hi]
    calc (l.flatMap (H.emb i)).length ≤ l.length * b := length_flatMap_le (hD.emb i) l
      _ ≤ (2 * b + 1) ^ (h - (i + 1)) * (b + 1) * b := Nat.mul_le_mul_right _ ih
      _ ≤ (2 * b + 1) * ((2 * b + 1) ^ (h - (i + 1)) * (b + 1)) := by nlinarith
  | @two i hi l₁ l₂ e _ _ ih₁ ih₂ =>
    have h1 : 1 ≤ (2 * b + 1) ^ (h - (i + 1)) * (b + 1) :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    rw [pow_sub_eq_mul_pow_sub_succ hi, List.length_append, List.length_cons]
    have e1 := (length_flatMap_le (hD.emb i) l₁).trans (Nat.mul_le_mul_right b ih₁)
    have e2 := (length_flatMap_le (hD.emb i) l₂).trans (Nat.mul_le_mul_right b ih₂)
    nlinarith

omit [Fintype V] in
/-- **The length bound of the routes of [19, 7]** (no longer assumed): a route produced by a
hierarchy of depth `h` with dilations `b`, `τ`, `dil` has at most
`dil · τ · (1 + (2b + 1)^h (b + 1))` edges, whatever the demand. -/
theorem RoutesHier.routesOK {C : Finset (Sym2 V)} {D : Demand V} {r : Routes V}
    {B h b τ dil : ℕ} (hr : RoutesHier C D r B h b τ dil) :
    RoutesOK C D r (dil * τ * (1 + (2 * b + 1) ^ h * (b + 1))) B := by
  obtain ⟨H, hD, hR⟩ := hr.hier
  refine ⟨hr.walk, hr.local_, fun pq hpq => ?_, hr.cong⟩
  obtain ⟨w, l, hw, hl, hrq⟩ := hR pq hpq
  have h1 := hl.length_le hD
  rw [Nat.sub_zero] at h1
  have h2 := length_flatMap_le hD.base l
  have h3 := length_flatMap_le hD.phys (w ++ l.flatMap H.base)
  rw [List.length_append] at h3
  rw [hrq]
  calc _ ≤ (w.length + (l.flatMap H.base).length) * dil := h3
    _ ≤ (τ + (2 * b + 1) ^ h * (b + 1) * τ) * dil := by
        gcongr
        exact h2.trans (Nat.mul_le_mul_right _ h1)
    _ = dil * τ * (1 + (2 * b + 1) ^ h * (b + 1)) := by ring

/-- Output property of the expander edge decomposition (Definition 2.9 / Lemma 2.10). -/
structure DecompOK (G : SimpleGraph V) [DecidableRel G.Adj] (cl : Finset (Finset (Sym2 V)))
    (φinv ov : ℕ) : Prop where
  sub : ∀ C ∈ cl, C ⊆ G.edgeFinset
  ne : ∀ C ∈ cl, C.Nonempty
  exp : ∀ C ∈ cl, IsExpander C φinv
  disj : ∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C'
  cover : ∀ e ∈ G.edgeFinset, ∃ C ∈ cl, e ∈ C
  overlap : ∀ v, (clustersOf cl v).card ≤ ov

/-- Edge-load envelope "at most `x` messages on every edge of `F`, none elsewhere". -/
def onEdges (F : Finset (Sym2 V)) (x : ℕ) : Sym2 V → ℕ := fun e => if e ∈ F then x else 0

/-! ## Connectivity -/

/-- `u` and `v` are connected by a path using edges of `F` (reflexive). -/
def EReach (F : Finset (Sym2 V)) : V → V → Prop :=
  Relation.ReflTransGen (fun a b => s(a, b) ∈ F)

/-- The edges of the induced subgraph `G[S]`. -/
noncomputable def inducedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) := by
  classical exact G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)

/-- `S` is non-empty and induces a connected subgraph. -/
def ConnSet (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, EReach (inducedEdges G S) u v

/-- The connected components of `G[S]` (as node sets). -/
noncomputable def comps (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Finset V) := by
  classical exact S.image (fun v => S.filter (fun u => EReach (inducedEdges G S) u v))

/-- Neighbours of `v` along edges of `F`. -/
noncomputable def nbrsIn (F : Finset (Sym2 V)) (v : V) : Finset V := by
  classical exact univ.filter (fun u => s(v, u) ∈ F)

/-- Parent pointers `par` and roots `root` describe a rooted spanning forest of the graph
`(S, F)`: pointers follow edges of `F` and stay in `S`, roots are propagated along pointers, a node
without parent is its own root, pointers decrease a rank function (no cycles), and two nodes of `S`
have the same root iff they are connected in `(S, F)`. -/
structure SpanForest (S : Finset V) (F : Finset (Sym2 V)) (par : V → Option V) (root : V → V) :
    Prop where
  edge : ∀ v ∈ S, ∀ u, par v = some u → s(v, u) ∈ F
  mem : ∀ v ∈ S, ∀ u, par v = some u → u ∈ S
  root_par : ∀ v ∈ S, ∀ u, par v = some u → root u = root v
  root_self : ∀ v ∈ S, par v = none → root v = v
  rank : ∃ r : V → ℕ, ∀ v ∈ S, ∀ u, par v = some u → r u < r v
  conn : ∀ u ∈ S, ∀ v ∈ S, (root u = root v ↔ EReach F u v)

/-! ## Agents of an overlay, local knowledge, uniform local computations -/

/-- The agents of an overlay graph `L_j`: the physical nodes and the virtual aggregators (one per
cluster, identified with the cluster's edge set; the aggregator of `C` is simulated by its host in
`A(C)`, which knows the topology of `C` after Lemma 3.8). -/
abbrev Agent (V : Type) := V ⊕ Finset (Sym2 V)

/-- Local knowledge about edge weights: a node knows the weights of its incident edges, an
aggregator those of the edges of its cluster. (Non-edges get weight `0`; edge weights are `≥ 1`.) -/
def lview (N : WNet V) : Agent V → Sym2 V → ℕ
  | .inl v, e => if e ∈ N.G.edgeFinset ∧ v ∈ e then N.w e else 0
  | .inr C, e => if e ∈ C then N.w e else 0

/-- A *uniform* local computation: one function for all networks, which an agent applies to its
identity, its local weight knowledge and its current data. (After the preprocessing every node
knows the set of all IDs, which the `Fintype` instance represents.) -/
structure LocFn where
  α : Type → Type
  β : Type → Type
  f : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → α V → β V

/-! ## Public parameters of an embedding -/

/-- Dilation of the embedding of the overlays `L_j`, `j < n`: the maximum length of an embedded
aggregator path. It is public: computed during the preprocessing (`embedConstruct`). -/
noncomputable def _root_.APSP.Overlays.dil (E : Overlays V) : ℕ :=
  (range (Fintype.card V)).sup (fun j => univ.sup (fun v => E.cl.sup (fun C => (E.path j v C).length)))

/-- Overlap of the clusters: the maximum number of clusters containing a node. It is public:
computed during the preprocessing (`embedConstruct`). -/
noncomputable def _root_.APSP.Overlays.ov (E : Overlays V) : ℕ :=
  univ.sup (fun v => (clustersOf E.cl v).card)

/-! ## Footprints: the participants of a task on a node set -/

/-- The footprint of `S` in overlay `j`: `S` and the nodes on the embedded aggregator paths of `S`
(whose endpoints are the hosts of the aggregators). In the paper's model, a subproblem on `S`
involves exactly these nodes: the nodes of `S`, the relays of their aggregator edges, and the hosts
of their aggregators. -/
noncomputable def footprint (E : Overlays V) (j : ℕ) (S : Finset V) : Finset V := by
  classical exact univ.filter (fun w => w ∈ S ∨ ∃ v ∈ S, ∃ C ∈ clustersOf E.cl v,
    ∃ e ∈ E.path j v C, w ∈ e)

lemma mem_footprint {E : Overlays V} {j : ℕ} {S : Finset V} {w : V} :
    w ∈ footprint E j S ↔
      w ∈ S ∨ ∃ v ∈ S, ∃ C ∈ clustersOf E.cl v, ∃ e ∈ E.path j v C, w ∈ e := by
  unfold footprint; simp

lemma subset_footprint (E : Overlays V) (j : ℕ) (S : Finset V) : S ⊆ footprint E j S :=
  fun _ hw => mem_footprint.2 (Or.inl hw)

lemma footprint_mono (E : Overlays V) (j : ℕ) {S S' : Finset V} (h : S ⊆ S') :
    footprint E j S ⊆ footprint E j S' := by
  intro w hw
  rcases mem_footprint.1 hw with hw | ⟨v, hv, C, hC, e, he, hwe⟩
  · exact mem_footprint.2 (Or.inl (h hw))
  · exact mem_footprint.2 (Or.inr ⟨v, h hv, C, hC, e, he, hwe⟩)

@[simp] lemma footprint_univ (E : Overlays V) (j : ℕ) : footprint E j univ = univ :=
  eq_univ_of_forall (fun w => subset_footprint E j univ (mem_univ w))

/-! ## Messages -/

/-- A word of a message: an ID, a number, or an edge (a pair of IDs). -/
inductive Word (V : Type) where
  | id (v : V)
  | num (k : ℕ)
  | edge (e : Sym2 V)
  deriving DecidableEq

/-- A message is a list of words (`b`-word messages have length `≤ b`). -/
abbrev Msg (V : Type) := List (Word V)

/-- All numbers occurring in `m` are at most `B` (so that a word has `O(log B)` bits). -/
def Msg.Bnd (B : ℕ) (m : Msg V) : Prop := ∀ k, Word.num k ∈ m → k ≤ B

/-- `m` has at most `b` words, each number at most `B`. -/
def Msg.Small (b B : ℕ) (m : Msg V) : Prop := m.length ≤ b ∧ m.Bnd B

/-! ## Aggregates (Definition 2.4) -/

/-- `AggOf op s a`: `a` is obtained from the (non-empty) multiset of inputs `s` by repeatedly
replacing two inputs by their `op`-aggregate, in an arbitrary order. -/
inductive AggOf {M : Type} (op : M → M → M) : Multiset M → M → Prop
  | single (a : M) : AggOf op {a} a
  | comb {s t : Multiset M} {a b : M} : AggOf op s a → AggOf op t b → AggOf op (s + t) (op a b)

/-! ## Minor-Aggregation rounds (Definition 2.5) -/

/-- One round of a Minor-Aggregation algorithm on the graph `(S, F)`, where `F` consists of the
edges of `G[S]` that are *present* (a forest, or all of `G[S]`). The data is distributed as the
model prescribes: nodes know their consensus input, edge processors (simulated by the aggregators
of their clusters) know whether they are present and contracted, and their aggregation function. -/
structure MAInst (V : Type) where
  S : Finset V
  pres : Sym2 V → Bool
  con : Sym2 V → Bool
  x : V → Msg V
  op₁ : Msg V → Msg V → Msg V
  zf : Sym2 V → V → Msg V → Msg V → Msg V
  op₂ : Msg V → Msg V → Msg V

namespace MAInst
variable (G : SimpleGraph V) [DecidableRel G.Adj] (I : MAInst V)

/-- the edges of the round -/
noncomputable def edges : Finset (Sym2 V) := by
  classical exact (inducedEdges G I.S).filter (fun e => I.pres e = true)

/-- the contracted edges -/
noncomputable def cedges : Finset (Sym2 V) := by
  classical exact (I.edges G).filter (fun e => I.con e = true)

/-- all values involved have at most `b` words with numbers `≤ B`, and the operators and edge
functions preserve this -/
def Small (b B : ℕ) : Prop :=
  (∀ v, (I.x v).Small b B) ∧
  (∀ m m', m.Small b B → m'.Small b B → (I.op₁ m m').Small b B ∧ (I.op₂ m m').Small b B) ∧
  (∀ e u m m', m.Small b B → m'.Small b B → (I.zf e u m m').Small b B)

end MAInst

/-- Data held by an agent at the start of a Minor-Aggregation round. -/
structure MAIn (V : Type) where
  inS : Bool
  x : Msg V
  edata : Sym2 V → Option (Bool × (V → Msg V → Msg V → Msg V))
  op₁ : Msg V → Msg V → Msg V
  op₂ : Msg V → Msg V → Msg V

/-- The distribution of an instance: node `v` holds its membership and input; the aggregator of
`C` holds, for every present edge of `C`, its contraction bit and aggregation function. Both know
the operators. -/
def maInput (I : MAInst V) : Agent V → MAIn V
  | .inl v => ⟨decide (v ∈ I.S), I.x v, fun _ => none, I.op₁, I.op₂⟩
  | .inr C => ⟨false, [], fun e => if e ∈ C ∧ I.pres e = true then some (I.con e, I.zf e) else none,
      I.op₁, I.op₂⟩

/-- Data held by an agent at the end of a round: a node its supernode's consensus value `y_s` and
aggregate `z_s` (`none` if the supernode has no incident edge of the round); an aggregator, for each
edge of the round in its cluster and each endpoint, the consensus value of that endpoint's
supernode (which the edge processor learns in the aggregation step). -/
structure MAOut (V : Type) where
  y : Option (Msg V)
  z : Option (Msg V)
  ey : Sym2 V → V → Option (Msg V)

open Classical in
/-- The specification of one Minor-Aggregation round (Definition 2.5): supernodes are the
components of the contracted edges; each node learns a `⊕`-aggregate of its supernode's inputs
(the same for the whole supernode) and a `⊗`-aggregate of the values `z_{e,s}` chosen by the edges
leaving its supernode (the same for the whole supernode); each edge processor learns the consensus
values of its endpoints' supernodes. -/
def MASpec (G : SimpleGraph V) [DecidableRel G.Adj] (cl : Finset (Finset (Sym2 V)))
    (I : MAInst V) (o : Agent V → MAOut V) : Prop :=
  ∃ Y : V → Msg V,
    (∀ v ∈ I.S, (o (.inl v)).y = some (Y v)) ∧
    (∀ u ∈ I.S, ∀ v ∈ I.S, EReach (I.cedges G) u v → Y u = Y v) ∧
    (∀ v ∈ I.S, AggOf I.op₁ ((I.S.filter (fun u => EReach (I.cedges G) u v)).val.map I.x) (Y v)) ∧
    (∀ v ∈ I.S,
      let Z : Multiset (Msg V) := ((I.S ×ˢ I.S).filter (fun p => s(p.1, p.2) ∈ I.edges G ∧
          EReach (I.cedges G) p.1 v ∧ ¬ EReach (I.cedges G) p.1 p.2)).val.map
          (fun p => I.zf s(p.1, p.2) p.1 (Y p.1) (Y p.2))
      (Z = 0 → (o (.inl v)).z = none) ∧ (Z ≠ 0 → ∃ z, (o (.inl v)).z = some z ∧ AggOf I.op₂ Z z)) ∧
    (∀ u ∈ I.S, ∀ v ∈ I.S, EReach (I.cedges G) u v → (o (.inl u)).z = (o (.inl v)).z) ∧
    (∀ C ∈ cl, ∀ e ∈ I.edges G, e ∈ C → ∀ u ∈ e, (o (.inr C)).ey e u = some (Y u))

/-! ## Eulerian orientation (Section 5.1) -/

/-- An Eulerian-orientation instance `H ⊆ H'`, where `H'` is `G[S]` plus `k` virtual nodes
`0, …, k-1`: physical edges `Hp ⊆ G[S]`, for each physical node the list of its virtual neighbours
(with multiplicity), and the list of virtual–virtual edges. -/
structure EOInst (V : Type) where
  S : Finset V
  Hp : Finset (Sym2 V)
  k : ℕ
  vv : V → List ℕ
  uu : List (ℕ × ℕ)

namespace EOInst
variable (H : EOInst V)

/-- physical degree of `v` in `H` -/
noncomputable def pdeg (v : V) : ℕ := by classical exact (H.Hp.filter (fun e => v ∈ e)).card

/-- degree of the virtual node `i` -/
noncomputable def vdeg (i : ℕ) : ℕ :=
  (∑ v ∈ H.S, (H.vv v).count i) + (H.uu.map (fun p => (if p.1 = i then 1 else 0) +
    (if p.2 = i then 1 else 0))).sum

/-- well-formed instance on `G[S]` with all degrees even -/
structure WF (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  sub : H.Hp ⊆ inducedEdges G H.S
  vv_out : ∀ v ∉ H.S, H.vv v = []
  vv_lt : ∀ v, ∀ i ∈ H.vv v, i < H.k
  uu_lt : ∀ p ∈ H.uu, p.1 < H.k ∧ p.2 < H.k
  even_p : ∀ v ∈ H.S, Even (H.pdeg v + (H.vv v).length)
  even_v : ∀ i < H.k, Even (H.vdeg i)

/-- a physical instance (no virtual nodes) -/
def Physical : Prop := H.k = 0 ∧ (∀ v, H.vv v = []) ∧ H.uu = []

end EOInst

/-- Data held by an agent of an Eulerian-orientation instance. -/
structure EOIn (V : Type) where
  inS : Bool
  vv : List ℕ
  uu : List (ℕ × ℕ)
  hp : Sym2 V → Bool

/-- Nodes know their membership, their virtual neighbours and all virtual–virtual edges; the
aggregator of `C` knows which edges of `C` are physical edges of `H` (as edge processors do). -/
noncomputable def eoInput (H : EOInst V) : Agent V → EOIn V
  | .inl v => ⟨decide (v ∈ H.S), H.vv v, H.uu, fun _ => false⟩
  | .inr C => ⟨false, [], H.uu, fun e => by classical exact decide (e ∈ C ∧ e ∈ H.Hp)⟩

/-- Output of an Eulerian orientation: nodes know the orientation of their virtual edges
(`true` = away from the node) and of the virtual–virtual edges (`true` = from `p.1` to `p.2`);
aggregators know the head of every physical edge of `H` in their cluster. -/
structure EOOut (V : Type) where
  vdir : List Bool
  udir : List Bool
  head : Sym2 V → Option V

open Classical in
/-- Specification of the Eulerian orientation problem: an orientation of all edges of `H`, known as
required, with in-degree equal to out-degree at every physical and every virtual node. -/
def EOSpec (cl : Finset (Finset (Sym2 V))) (H : EOInst V) (o : Agent V → EOOut V) : Prop :=
  ∃ (head : Sym2 V → V) (vd : V → List Bool) (ud : List Bool),
    (∀ e ∈ H.Hp, head e ∈ e) ∧
    (∀ C ∈ cl, ∀ e ∈ H.Hp, e ∈ C → (o (.inr C)).head e = some (head e)) ∧
    (∀ v ∈ H.S, (o (.inl v)).vdir = vd v ∧ (vd v).length = (H.vv v).length ∧
      (o (.inl v)).udir = ud) ∧
    ud.length = H.uu.length ∧
    (∀ v ∈ H.S,
      (H.Hp.filter (fun e => v ∈ e ∧ head e = v)).card + (vd v).count false =
      (H.Hp.filter (fun e => v ∈ e ∧ head e ≠ v)).card + (vd v).count true) ∧
    (∀ i < H.k,
      (∑ v ∈ H.S, ((H.vv v).zip (vd v)).count (i, true)) +
          ((H.uu.zip ud).filter (fun t => (t.1.2 = i ∧ t.2 = true) ∨ (t.1.1 = i ∧ t.2 = false))).length =
      (∑ v ∈ H.S, ((H.vv v).zip (vd v)).count (i, false)) +
          ((H.uu.zip ud).filter (fun t => (t.1.1 = i ∧ t.2 = true) ∨ (t.1.2 = i ∧ t.2 = false))).length)

/-! ## Rings of segments (proof of Lemma 5.3) -/

/-- The ring data of a node: its segment ends `(own edge e, partner node x, partner edge e')`,
listed so that consecutive pairs (positions `2i, 2i+1`) are paired at the node. -/
abbrev RingIn (V : Type) := List (Sym2 V × V × Sym2 V)

/-- Well-formed ring data over the aggregator edges of `S`: ends are distinct, paired at nodes,
symmetric (the partner end lists the reverse end), both edges of a segment lie in the same cluster,
— the property established in the proof of Lemma 5.3 — every node has at most one segment end
in each cluster (so every aggregator edge serves at most one segment end), and the two ends of a
segment are different ends (`ne`). Under these conditions `RingSpec` is satisfiable
(`ringSpec_realizable` in `Realizability.lean`); without `ne` it need not be. Finally, the own edge
of a segment end is incident to the node (`inc`: segment ends are darts `(v, e)`, `v ∈ e`); this is
what lets a node find the cluster of each of its segment ends from its cluster slices
`C ∩ inc(v)`, which the distributed protocol needs (`ringLE_congest`). -/
structure RingWF (cl : Finset (Finset (Sym2 V))) (S : Finset V) (r : V → RingIn V) : Prop where
  out : ∀ v ∉ S, r v = []
  even : ∀ v, Even (r v).length
  nodup : ∀ v, (r v).Nodup
  symm : ∀ v e x e', (e, x, e') ∈ r v → (e', v, e) ∈ r x
  clus : ∀ v e x e', (e, x, e') ∈ r v → ∃ C ∈ cl, e ∈ C ∧ e' ∈ C ∧ v ∈ nodes C ∧ x ∈ nodes C
  simple : ∀ v, ∀ C ∈ cl, ((r v).filter (fun t => decide (t.1 ∈ C))).length ≤ 1
  ne : ∀ v e x e', (e, x, e') ∈ r v → (v, e) ≠ (x, e')
  inc : ∀ v e x e', (e, x, e') ∈ r v → v ∈ e

/-- A consistent orientation of the rings: the two ends paired at a node get different directions
(one in, one out), and the two ends of a segment get different directions (out at one end, in at
the other). `true` = out. -/
def RingSpec (r : V → RingIn V) (d : V → List Bool) : Prop :=
  (∀ v, (d v).length = (r v).length) ∧
  (∀ v i, 2 * i + 1 < (r v).length → (d v).getD (2 * i) false ≠ (d v).getD (2 * i + 1) false) ∧
  (∀ v x e e' i i', (r v)[i]? = some (e, x, e') → (r x)[i']? = some (e', v, e) →
    (d v).getD i false ≠ (d x).getD i' false)

/-! ## Distances from a virtual source (Lemma 5.4, Theorem 5.5) -/

/-- Input format of subset shortest-path tasks: membership in `S` and the virtual source edge
`(σ, v)` (weight and a label: the real predecessor it stands for). -/
abbrev SubIn (V : Type) := Bool × Option (ℕ × V)

/-- The distribution of a subset shortest-path instance. -/
def subInput (S : Finset V) (w0 : V → Option (ℕ × V)) : Agent V → SubIn V
  | .inl v => (decide (v ∈ S), w0 v)
  | .inr _ => (false, none)

/-- Weighted distance from the virtual source `σ` in `G[S]` plus the virtual edges `(σ, u)`
(`u ∈ S`) of weight `c` for `w0 u = some (c, _)`; `⊤` if unreachable. -/
noncomputable def subDist (N : WNet V) (S : Finset V) (w0 : V → Option (ℕ × V)) (v : V) : ℕ∞ :=
  sInf {d : ℕ∞ | ∃ u ∈ S, ∃ c p, w0 u = some (c, p) ∧
    ∃ q : N.G.Walk u v, (∀ x ∈ q.support, x ∈ S) ∧ d = ((c + N.wlen q : ℕ) : ℕ∞)}

/-- Specification of `3/2`-approximate SSSP from the virtual source on `G[S]` (Lemma 5.4 with
`ε = 1/2`): every node of `S` reachable from `σ` outputs an estimate `d` with
`dist ≤ d ≤ 3/2·dist` and a parent in an approximate shortest-path tree: a neighbour `p ∈ S` whose
estimate `d_p` satisfies `d = d_p + w(p, v)`, or the virtual source (then `d = w0 v` and the
parent is the label of the virtual edge). Unreachable nodes output `none`. -/
def ApproxSpec (N : WNet V) (S : Finset V) (w0 : V → Option (ℕ × V)) (y : V → Option (ℕ × V)) :
    Prop :=
  ∀ v ∈ S, (y v = none ↔ subDist N S w0 v = ⊤) ∧
    ∀ d p, y v = some (d, p) →
      subDist N S w0 v ≤ d ∧ 2 * (d : ℕ∞) ≤ 3 * subDist N S w0 v ∧
      ((p ∈ S ∧ N.G.Adj v p ∧ ∃ dp p', y p = some (dp, p') ∧ dp + N.w s(p, v) = d) ∨
        w0 v = some (d, p))

end APSP.Stoc

namespace APSP.Stoc
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Membership flag of an agent in a node set (aggregators: `false`). -/
def memAg (K : Finset V) : Agent V → Bool
  | .inl v => decide (v ∈ K)
  | .inr _ => false

end APSP.Stoc
