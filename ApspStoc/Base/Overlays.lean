import ApspStoc.Base.Demands

/-!
# The overlay graphs `L_j` and their embedding (Section 3.3)

`L_j` consists of the nodes and edges of `G` plus one virtual aggregator `a_{C,j}` per cluster `C`,
adjacent to every node of `C`. Edges of `G` are embedded as themselves; the virtual edge
`(v, a_{C,j})` is embedded as a path `path j v C` in `G`.

`rhoAgg E j S e` is the number of times edge `e` of `G` is used by the embedded paths of the
virtual edges of `L_j` incident to `S`, and `rho` additionally counts the `G`-edges incident to
`S` (embedded as themselves). These are the "congestion of the path set corresponding to the edges
incident to `S` in `L_j`" of Theorem 3.10. Theorem numbers refer to the STOC submission of the
paper.
-/

namespace APSP

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Routes recorded by a routing execution: the list of edges traversed by the packet with a
given (source port, destination port). -/
abbrev Routes (V : Type) := Port V × Port V → List (Sym2 V)

/-- An overlay family together with its embedding into `G`. -/
structure Overlays (V : Type) where
  cl : Finset (Finset (Sym2 V))
  path : ℕ → V → Finset (Sym2 V) → List (Sym2 V)

namespace Overlays
variable (E : Overlays V)

/-- usage of edge `e` by the embedded aggregator edges of `L_j` incident to `S` -/
def rhoAgg (j : ℕ) (S : Finset V) (e : Sym2 V) : ℕ :=
  ∑ v ∈ S, ∑ C ∈ clustersOf E.cl v, (E.path j v C).count e

/-- total length of the embedded aggregator edges of `L_j` incident to `S` -/
def aggLen (j : ℕ) (S : Finset V) : ℕ :=
  ∑ v ∈ S, ∑ C ∈ clustersOf E.cl v, (E.path j v C).length

/-- usage of edge `e` by all embedded edges of `L_j` incident to `S` -/
def rho (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (S : Finset V) (e : Sym2 V) : ℕ :=
  (if e ∈ G.edgeFinset ∧ ∃ v ∈ S, v ∈ e then 1 else 0) + E.rhoAgg j S e

end Overlays

/-- `l` is (the edge sequence of) a walk from `a` to `b`. -/
def IsEdgeWalk : List (Sym2 V) → V → V → Prop
  | [], a, b => a = b
  | e :: l, a, b => ∃ x, e = s(a, x) ∧ IsEdgeWalk l x b

/-- Validity of an overlay embedding (Definition 2.1 / Section 3.3): the clusters are pairwise
disjoint sets of edges of `G` covering all edges of `G` (so every edge is simulated by exactly one
aggregator); every
embedded path uses only edges of its cluster (hence physical edges of `G`); and for every overlay
`j < n` and cluster `C`, the virtual aggregator `a_{C,j}` is hosted at a *single* node `h ∈ A(C)`:
the embedded path of every virtual edge `(v, a_{C,j})`, `v ∈ C`, is a walk from `v` to that `h`. -/
structure EmbValid (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) : Prop where
  cover : ∀ e ∈ G.edgeFinset, ∃ C ∈ E.cl, e ∈ C
  sub : ∀ C ∈ E.cl, C ⊆ G.edgeFinset
  disj : ∀ C ∈ E.cl, ∀ C' ∈ E.cl, C ≠ C' → Disjoint C C'
  local_ : ∀ j v C, ∀ e ∈ E.path j v C, e ∈ C
  walk : ∀ j < Fintype.card V, ∀ C ∈ E.cl, ∃ h ∈ aggSet C, ∀ v ∈ nodes C,
    IsEdgeWalk (E.path j v C) v h

/-- The properties of the overlay embedding established by Theorem 3.10 (with path length `d`,
cluster overlap `ov`, and total congestion `X` over all `n` overlays). -/
structure OverlayProps (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (ov d X : ℕ) :
    Prop where
  valid : EmbValid G E
  sub : ∀ C ∈ E.cl, C ⊆ G.edgeFinset
  disj : ∀ C ∈ E.cl, ∀ C' ∈ E.cl, C ≠ C' → Disjoint C C'
  overlap : ∀ v, (clustersOf E.cl v).card ≤ ov
  len : ∀ j v C, (E.path j v C).length ≤ d
  local_ : ∀ j v C, ∀ e ∈ E.path j v C, e ∈ C
  total : ∀ e, ∑ j ∈ range (Fintype.card V), E.rho G j univ e ≤ X

section Props
variable {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V} {ov d X : ℕ}

lemma card_filter_mem_le_one (hE : OverlayProps G E ov d X) (s : Finset (Finset (Sym2 V)))
    (hs : s ⊆ E.cl) (e : Sym2 V) : (s.filter (fun C => e ∈ C)).card ≤ 1 := by
  rw [card_le_one]
  intro C hC C' hC'
  rw [mem_filter] at hC hC'
  by_contra hne
  exact disjoint_left.1 (hE.disj C (hs hC.1) C' (hs hC'.1) hne) hC.2 hC'.2

/-- Subset congestion (second item of Theorem 3.10): `rhoAgg ≤ d · |S|`. -/
lemma rhoAgg_le (hE : OverlayProps G E ov d X) (j : ℕ) (S : Finset V) (e : Sym2 V) :
    E.rhoAgg j S e ≤ d * S.card := by
  unfold Overlays.rhoAgg
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum; intro v _
  have hzero : ∀ C ∈ clustersOf E.cl v, C ∉ (clustersOf E.cl v).filter (fun C => e ∈ C) →
      (E.path j v C).count e = 0 := by
    intro C hC hnot
    rw [List.count_eq_zero]
    intro hmem
    exact hnot (mem_filter.2 ⟨hC, hE.local_ j v C e hmem⟩)
  rw [← sum_subset (filter_subset _ _) hzero]
  have h1 := card_filter_mem_le_one hE (clustersOf E.cl v) (filter_subset _ _) e
  calc ∑ C ∈ (clustersOf E.cl v).filter (fun C => e ∈ C), (E.path j v C).count e
      ≤ ∑ C ∈ (clustersOf E.cl v).filter (fun C => e ∈ C), d :=
        sum_le_sum (fun C _ => (List.count_le_length).trans (hE.len j v C))
    _ = _ * d := by rw [sum_const, smul_eq_mul]
    _ ≤ 1 * d := Nat.mul_le_mul_right _ h1
    _ = d := one_mul d

lemma aggLen_le (hE : OverlayProps G E ov d X) (j : ℕ) (S : Finset V) :
    E.aggLen j S ≤ ov * d * S.card := by
  unfold Overlays.aggLen
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum; intro v _
  calc ∑ C ∈ clustersOf E.cl v, (E.path j v C).length ≤ ∑ C ∈ clustersOf E.cl v, d :=
        sum_le_sum (fun C _ => hE.len j v C)
    _ = (clustersOf E.cl v).card * d := by rw [sum_const, smul_eq_mul]
    _ ≤ ov * d := Nat.mul_le_mul_right _ (hE.overlap v)

end Props

section Mono
variable (E : Overlays V) {G : SimpleGraph V} [DecidableRel G.Adj]

lemma rhoAgg_mono (j : ℕ) {S S' : Finset V} (h : S ⊆ S') (e : Sym2 V) :
    E.rhoAgg j S e ≤ E.rhoAgg j S' e :=
  sum_le_sum_of_subset h

lemma rho_mono (j : ℕ) {S S' : Finset V} (h : S ⊆ S') (e : Sym2 V) :
    E.rho G j S e ≤ E.rho G j S' e := by
  unfold Overlays.rho
  apply Nat.add_le_add _ (rhoAgg_mono E j h e)
  split_ifs with h1 h2 <;> try simp
  exact h2 ⟨h1.1, let ⟨v, hv, hve⟩ := h1.2; ⟨v, h hv, hve⟩⟩

lemma le_rho_of_mem (j : ℕ) {S : Finset V} {e : Sym2 V} (he : e ∈ G.edgeFinset) {v : V}
    (hv : v ∈ S) (hve : v ∈ e) : 1 ≤ E.rho G j S e := by
  unfold Overlays.rho; rw [if_pos ⟨he, v, hv, hve⟩]; omega

lemma rhoAgg_le_rho (j : ℕ) (S : Finset V) (e : Sym2 V) : E.rhoAgg j S e ≤ E.rho G j S e :=
  Nat.le_add_left _ _

end Mono

/-! ## The construction of Theorem 3.10 -/

section Construction

/-- Balanced assignment of overlay indices `j < n` to the ports of `A(C)`. -/
noncomputable def portAssign (C : Finset (Sym2 V)) (h : (portsA C).Nonempty) : ℕ → Port V :=
  Classical.choose (exists_balanced (range (Fintype.card V)) (portsA C) h)

lemma portAssign_spec (C : Finset (Sym2 V)) (h : (portsA C).Nonempty) :
    (∀ j ∈ range (Fintype.card V), portAssign C h j ∈ portsA C) ∧
    ∀ p, ((range (Fintype.card V)).filter (fun j => portAssign C h j = p)).card ≤
      (range (Fintype.card V)).card / (portsA C).card + 1 :=
  Classical.choose_spec (exists_balanced (range (Fintype.card V)) (portsA C) h)

/-- The overlays of Theorem 3.10: in cluster `C`, overlay `j`'s virtual aggregator is simulated
at port `portAssign C j` of `A(C)`, and the virtual edge `(v, a_{C,j})` is embedded as the route
taken by the dummy packet of Lemma 3.9 from `v` to that port. -/
noncomputable def construct (cl : Finset (Finset (Sym2 V))) (r : Finset (Sym2 V) → Routes V) :
    Overlays V where
  cl := cl
  path j v C := if h : (portsA C).Nonempty then
      (if v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V then r C (srcPort C v, portAssign C h j)
        else []) else []

/-- Properties of the dummy routes of Lemma 3.9 in cluster `C` (congestion bound `B`, length
`d`): all routes stay inside `C`. -/
structure DummyRoutesOK (C : Finset (Sym2 V)) (r : Routes V) (d B : ℕ) : Prop where
  walk : ∀ v ∈ nodes C, ∀ p ∈ portsA C, IsEdgeWalk (r (srcPort C v, p)) v p.1
  local_ : ∀ v ∈ nodes C, ∀ p ∈ portsA C, ∀ e ∈ r (srcPort C v, p), e ∈ C
  len : ∀ v ∈ nodes C, ∀ p ∈ portsA C, (r (srcPort C v, p)).length ≤ d
  cong : ∀ e, ∑ x ∈ nodes C ×ˢ portsA C, (r (srcPort C x.1, x.2)).count e ≤ B

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma sum_clustersOf_comm (cl : Finset (Finset (Sym2 V))) (g : V → Finset (Sym2 V) → ℕ) :
    ∑ v, ∑ C ∈ clustersOf cl v, g v C = ∑ C ∈ cl, ∑ v ∈ nodes C, g v C := by
  unfold clustersOf
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun C _ => ?_)
  rw [← sum_filter]; congr 1; ext v; simp

lemma sum_range_portAssign (C : Finset (Sym2 V)) (h : (portsA C).Nonempty) (f : Port V → ℕ) :
    ∑ j ∈ range (Fintype.card V), f (portAssign C h j) ≤
      (Fintype.card V / (portsA C).card + 1) * ∑ p ∈ portsA C, f p := by
  rw [← sum_fiberwise_of_maps_to (portAssign_spec C h).1, mul_sum]
  apply sum_le_sum; intro p _
  rw [sum_congr rfl (fun j hj => by rw [(mem_filter.1 hj).2]), sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  have := (portAssign_spec C h).2 p
  rwa [card_range] at this

/-- Theorem 3.10, congestion: if in every cluster the dummy routes have congestion at most
`β · n_C`, then all embedded edges of all `n` overlays put load at most `n + 2βn` on every edge. -/
theorem construct_props (cl : Finset (Finset (Sym2 V))) (r : Finset (Sym2 V) → Routes V)
    (ov d β : ℕ)
    (hsub : ∀ C ∈ cl, C ⊆ G.edgeFinset) (hne : ∀ C ∈ cl, C.Nonempty)
    (hcover : ∀ e ∈ G.edgeFinset, ∃ C ∈ cl, e ∈ C)
    (hdisj : ∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C')
    (hov : ∀ v, (clustersOf cl v).card ≤ ov)
    (hr : ∀ C ∈ cl, DummyRoutesOK C (r C) d (β * (nodes C).card)) :
    OverlayProps G (construct cl r) ov d (Fintype.card V + 2 * β * Fintype.card V) := by
  have hnl : ∀ C ∈ cl, NoLoops C := fun C hC e he =>
    G.not_isDiag_of_mem_edgeSet (by simpa using hsub C hC he)
  -- the path, when non-trivial
  have hpath : ∀ j v C, (construct cl r).path j v C ≠ [] → ∃ h : (portsA C).Nonempty,
      v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V ∧
        (construct cl r).path j v C = r C (srcPort C v, portAssign C h j) := by
    intro j v C hne'
    by_cases h : (portsA C).Nonempty
    · by_cases h2 : v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V
      · exact ⟨h, h2.1, h2.2.1, h2.2.2, by simp only [construct, dif_pos h, if_pos h2]⟩
      · exfalso; apply hne'; simp only [construct, dif_pos h, if_neg h2]
    · exfalso; apply hne'; simp only [construct, dif_neg h]
  have hloc : ∀ j v C, ∀ e ∈ (construct cl r).path j v C, e ∈ C := by
    intro j v C e he
    obtain ⟨h, hv, hC, hj, heq⟩ := hpath j v C (List.ne_nil_of_mem he)
    rw [heq] at he
    exact (hr C hC).local_ v hv _ ((portAssign_spec C h).1 j (mem_range.2 hj)) e he
  have hvalid : EmbValid G (construct cl r) := by
    refine ⟨hcover, hsub, hdisj, hloc, fun j hj C hC => ?_⟩
    have hb := card_portsA_bounds (hnl C hC) (hne C hC)
    have h : (portsA C).Nonempty :=
      card_pos.1 (by have := two_le_card_nodes (hnl C hC) (hne C hC); omega)
    have hp := (portAssign_spec C h).1 j (mem_range.2 hj)
    -- the host `portAssign C h j` depends only on the cluster and the overlay, not on `v`
    refine ⟨(portAssign C h j).1, ?_, fun v hv => ?_⟩
    · unfold portsA portsOf at hp
      obtain ⟨a, ha, hpa⟩ := mem_biUnion.1 hp
      rw [(mem_portsAt.1 hpa).1]; exact ha
    · have hc : v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V := ⟨hv, hC, hj⟩
      simp only [construct, dif_pos h, if_pos hc]
      exact (hr C hC).walk v hv _ hp
  refine ⟨hvalid, hsub, hdisj, hov, ?_, hloc, ?_⟩
  · intro j v C
    by_cases hnil : (construct cl r).path j v C = []
    · rw [hnil]; simp
    · obtain ⟨h, hv, hC, hj, heq⟩ := hpath j v C hnil
      rw [heq]; exact (hr C hC).len v hv _ ((portAssign_spec C h).1 j (mem_range.2 hj))
  · intro e
    unfold Overlays.rho
    rw [sum_add_distrib]
    have h1 : ∑ j ∈ range (Fintype.card V), (if e ∈ G.edgeFinset ∧ ∃ v ∈ (univ : Finset V), v ∈ e then 1 else 0)
        ≤ Fintype.card V := by
      have := sum_le_card_nsmul (range (Fintype.card V))
        (fun _ => if e ∈ G.edgeFinset ∧ ∃ v ∈ (univ : Finset V), v ∈ e then 1 else 0) 1
        (fun j _ => by split_ifs <;> simp)
      simpa using this
    -- the aggregator part
    let T : Finset (Sym2 V) → ℕ := fun C =>
      ∑ v ∈ nodes C, ∑ j ∈ range (Fintype.card V), ((construct cl r).path j v C).count e
    have h2 : ∑ j ∈ range (Fintype.card V), (construct cl r).rhoAgg j univ e = ∑ C ∈ cl, T C := by
      unfold Overlays.rhoAgg
      rw [sum_comm]
      simp_rw [sum_comm (s := range (Fintype.card V))]
      exact sum_clustersOf_comm cl _
    have hT : ∀ C ∈ cl, T C ≤ 2 * β * Fintype.card V := by
      intro C hC
      have hb := card_portsA_bounds (hnl C hC) (hne C hC)
      have h : (portsA C).Nonempty := card_pos.1 (by have := two_le_card_nodes (hnl C hC) (hne C hC); omega)
      have hT1 : T C ≤ (Fintype.card V / (portsA C).card + 1) *
          ∑ x ∈ nodes C ×ˢ portsA C, (r C (srcPort C x.1, x.2)).count e := by
        simp only [T]
        rw [sum_product, mul_sum]
        apply sum_le_sum; intro v hv
        have : ∀ j ∈ range (Fintype.card V), ((construct cl r).path j v C).count e =
            (r C (srcPort C v, portAssign C h j)).count e := by
          intro j hj
          have hc : v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V := ⟨hv, hC, mem_range.1 hj⟩
          simp only [construct, dif_pos h, if_pos hc]
        rw [sum_congr rfl this]
        exact sum_range_portAssign C h (fun p => (r C (srcPort C v, p)).count e)
      have hT2 := (hr C hC).cong e
      have hnC : (nodes C).card ≤ Fintype.card V := card_le_univ _
      have h3 : Fintype.card V / (portsA C).card * (nodes C).card ≤ Fintype.card V :=
        (Nat.mul_le_mul_left _ hb.1).trans (Nat.div_mul_le_self (Fintype.card V) _)
      calc T C ≤ (Fintype.card V / (portsA C).card + 1) * (β * (nodes C).card) :=
            hT1.trans (Nat.mul_le_mul_left _ hT2)
        _ = β * (Fintype.card V / (portsA C).card * (nodes C).card + (nodes C).card) := by ring
        _ ≤ β * (Fintype.card V + Fintype.card V) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * β * Fintype.card V := by ring
    have hT0 : ∀ C ∈ cl, e ∉ C → T C = 0 := by
      intro C _ heC
      simp only [T]
      apply sum_eq_zero; intro v _; apply sum_eq_zero; intro j _
      rw [List.count_eq_zero]; intro hmem; exact heC (hloc j v C e hmem)
    have h4 : ∑ C ∈ cl, T C ≤ 2 * β * Fintype.card V := by
      rw [← sum_subset (filter_subset (fun C => e ∈ C) cl)
        (fun C hC hnot => hT0 C hC (fun h => hnot (mem_filter.2 ⟨hC, h⟩)))]
      have hle1 : (cl.filter (fun C => e ∈ C)).card ≤ 1 := by
        rw [card_le_one]; intro C hC C' hC'; rw [mem_filter] at hC hC'
        by_contra hneq
        exact disjoint_left.1 (hdisj C hC.1 C' hC'.1 hneq) hC.2 hC'.2
      calc ∑ C ∈ cl.filter (fun C => e ∈ C), T C ≤ ∑ C ∈ cl.filter (fun C => e ∈ C), 2 * β * Fintype.card V :=
            sum_le_sum (fun C hC => hT C (mem_filter.1 hC).1)
        _ = _ * (2 * β * Fintype.card V) := by rw [sum_const, smul_eq_mul]
        _ ≤ 1 * (2 * β * Fintype.card V) := Nat.mul_le_mul_right _ hle1
        _ = 2 * β * Fintype.card V := one_mul _
    rw [h2]; omega

end Construction

end APSP
