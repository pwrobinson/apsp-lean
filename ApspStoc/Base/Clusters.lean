import ApspStoc.Base.AggregatorSet

/-!
# Clusters, ports, aggregator sets, demands

A cluster of the expander edge decomposition is represented by its edge set
`C : Finset (Sym2 V)`; its node set is the set of endpoints of its edges.
-/

namespace APSP

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

section ClusterBasics
variable (C : Finset (Sym2 V))

/-- Node set of a cluster. -/
def nodes : Finset V := univ.filter (fun v => ∃ e ∈ C, v ∈ e)

/-- Degree of `v` inside the cluster. -/
def degIn (v : V) : ℕ := (C.filter (fun e => v ∈ e)).card

variable {C}

lemma mem_nodes {v : V} : v ∈ nodes C ↔ ∃ e ∈ C, v ∈ e := by simp [nodes]

lemma degIn_pos {v : V} (hv : v ∈ nodes C) : 1 ≤ degIn C v := by
  obtain ⟨e, he, hve⟩ := mem_nodes.1 hv
  exact card_pos.2 ⟨e, mem_filter.2 ⟨he, hve⟩⟩

lemma degIn_eq_zero {v : V} (hv : v ∉ nodes C) : degIn C v = 0 := by
  unfold degIn; rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hve; exact hv (mem_nodes.2 ⟨e, he, hve⟩)

/-- Simple-graph clusters: no loops. -/
def NoLoops (C : Finset (Sym2 V)) : Prop := ∀ e ∈ C, ¬ e.IsDiag

lemma degIn_succ_le (hC : NoLoops C) {v : V} (hv : v ∈ nodes C) :
    degIn C v + 1 ≤ (nodes C).card := by
  classical
  let f : Sym2 V → V := fun e => if h : v ∈ e then Sym2.Mem.other h else v
  have hmaps : ∀ e ∈ C.filter (fun e => v ∈ e), f e ∈ (nodes C).erase v := by
    intro e he
    rw [mem_filter] at he
    simp only [f, dif_pos he.2]
    refine mem_erase.2 ⟨fun heq => hC e he.1 ?_, mem_nodes.2 ⟨e, he.1, Sym2.other_mem he.2⟩⟩
    rw [← Sym2.other_spec he.2, heq]; exact Sym2.mk_isDiag_iff.2 rfl
  have hinj : Set.InjOn f (C.filter (fun e => v ∈ e)) := by
    intro e he e' he' heq
    simp only [coe_filter, Set.mem_setOf_eq] at he he'
    simp only [f, dif_pos he.2, dif_pos he'.2] at heq
    rw [← Sym2.other_spec he.2, ← Sym2.other_spec he'.2, heq]
  have := card_le_card_of_injOn f hmaps hinj
  rw [card_erase_of_mem hv] at this
  have hpos : 0 < (nodes C).card := card_pos.2 ⟨v, hv⟩
  unfold degIn; omega

lemma card_filter_mem_of_not_diag {e : Sym2 V} (he : ¬ e.IsDiag) :
    (univ.filter (fun v => v ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (Sym2.mk_isDiag_iff.2 h)
    have : univ.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext x; simp [Sym2.mem_iff]
    rw [this, card_pair hab]

/-- Handshake lemma for clusters. -/
lemma sum_degIn (hC : NoLoops C) : ∑ v ∈ nodes C, degIn C v = 2 * C.card := by
  have h1 : ∑ v ∈ nodes C, degIn C v = ∑ v : V, degIn C v := by
    apply sum_subset (subset_univ _)
    intro v _ hv; exact degIn_eq_zero hv
  rw [h1]
  unfold degIn
  have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset V)) (t := C) (r := fun v e => v ∈ e)
  simp only [bipartiteAbove, bipartiteBelow] at this
  rw [this, sum_congr rfl (fun e he => card_filter_mem_of_not_diag (hC e he))]
  simp [mul_comm]

lemma two_le_card_nodes (hC : NoLoops C) (hne : C.Nonempty) : 2 ≤ (nodes C).card := by
  obtain ⟨e, he⟩ := hne
  have h := sum_degIn hC
  obtain ⟨v, hv⟩ : (nodes C).Nonempty := by
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, mem_nodes.2 ⟨_, he, Sym2.mem_mk_left a b⟩⟩
  have := degIn_succ_le hC hv
  have : 1 ≤ degIn C v := degIn_pos hv
  omega

lemma card_nodes_le_sum_degIn (hC : NoLoops C) : (nodes C).card ≤ 2 * C.card := by
  rw [← sum_degIn hC]
  have := card_nsmul_le_sum (nodes C) (degIn C) 1 (fun v hv => degIn_pos hv)
  simpa using this

lemma card_le_sq (hC : NoLoops C) : C.card ≤ (nodes C).card ^ 2 := by
  have h := sum_degIn hC
  have hle : ∀ v ∈ nodes C, degIn C v ≤ (nodes C).card := fun v hv => by
    have := degIn_succ_le hC hv; omega
  have := sum_le_card_nsmul (nodes C) (degIn C) _ hle
  simp only [smul_eq_mul] at this
  nlinarith

end ClusterBasics

/-! ## Clusters of a decomposition -/

/-- The clusters (of a family `cl`) containing node `v`. -/
def clustersOf (cl : Finset (Finset (Sym2 V))) (v : V) : Finset (Finset (Sym2 V)) :=
  cl.filter (fun C => v ∈ nodes C)

/-- `∑_C n_C = ∑_v (#clusters containing v)`. -/
lemma sum_card_nodes_eq (cl : Finset (Finset (Sym2 V))) :
    ∑ C ∈ cl, (nodes C).card = ∑ v : V, (clustersOf cl v).card := by
  have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := cl) (t := (univ : Finset V)) (r := fun C v => v ∈ nodes C)
  simp only [bipartiteAbove, bipartiteBelow] at this
  unfold clustersOf
  rw [← this]
  refine sum_congr rfl (fun C _ => ?_)
  congr 1; ext x; simp

lemma sum_card_nodes_le (cl : Finset (Finset (Sym2 V))) (ov : ℕ)
    (hov : ∀ v, (clustersOf cl v).card ≤ ov) :
    ∑ C ∈ cl, (nodes C).card ≤ ov * Fintype.card V := by
  rw [sum_card_nodes_eq]
  have := sum_le_card_nsmul (univ : Finset V) (fun v => (clustersOf cl v).card) ov
    (fun v _ => hov v)
  simpa [mul_comm] using this

/-! ## Aggregator sets -/

/-- The aggregator set `A(C)` of a cluster (Definition 3.6), chosen by `Classical.choice`. -/
noncomputable def aggSet (C : Finset (Sym2 V)) : Finset V :=
  Classical.epsilon (fun A => IsAggSet (nodes C) A (degIn C))

lemma aggSet_spec {C : Finset (Sym2 V)} (hC : NoLoops C) (hne : C.Nonempty) :
    IsAggSet (nodes C) (aggSet C) (degIn C) := by
  have hex : ∃ A, IsAggSet (nodes C) A (degIn C) := by
    apply exists_aggSet
    · have := two_le_card_nodes hC hne; omega
    · rw [sum_degIn hC]; exact card_nodes_le_sum_degIn hC
  exact Classical.epsilon_spec hex

/-! ## Ports -/

/-- A port is a node–edge incidence. -/
abbrev Port (V : Type) := V × Sym2 V

/-- The ports of `v` in cluster `C`. -/
def portsAt (C : Finset (Sym2 V)) (v : V) : Finset (Port V) :=
  (C.filter (fun e => v ∈ e)).image (fun e => (v, e))

lemma card_portsAt (C : Finset (Sym2 V)) (v : V) : (portsAt C v).card = degIn C v := by
  unfold portsAt degIn
  rw [card_image_of_injective _ (fun e e' h => (Prod.ext_iff.1 h).2)]

lemma mem_portsAt {C : Finset (Sym2 V)} {v : V} {p : Port V} :
    p ∈ portsAt C v ↔ p.1 = v ∧ p.2 ∈ C ∧ v ∈ p.2 := by
  unfold portsAt; constructor
  · intro h; obtain ⟨e, he, rfl⟩ := mem_image.1 h; rw [mem_filter] at he; exact ⟨rfl, he⟩
  · rintro ⟨h1, h2, h3⟩; exact mem_image.2 ⟨p.2, mem_filter.2 ⟨h2, h3⟩, by rw [← h1]⟩

lemma portsAt_disjoint (C : Finset (Sym2 V)) {u v : V} (h : u ≠ v) :
    Disjoint (portsAt C u) (portsAt C v) := by
  rw [disjoint_left]; intro p hu hv
  exact h ((mem_portsAt.1 hu).1.symm.trans (mem_portsAt.1 hv).1)

/-- Ports of a set of nodes. -/
def portsOf (C : Finset (Sym2 V)) (A : Finset V) : Finset (Port V) := A.biUnion (portsAt C)

lemma card_portsOf (C : Finset (Sym2 V)) (A : Finset V) :
    (portsOf C A).card = ∑ a ∈ A, degIn C a := by
  unfold portsOf
  rw [card_biUnion (fun u _ v _ h => portsAt_disjoint C h)]
  exact sum_congr rfl (fun a _ => card_portsAt C a)

/-- The ports of the aggregator set `A(C)`. -/
noncomputable def portsA (C : Finset (Sym2 V)) : Finset (Port V) := portsOf C (aggSet C)

lemma card_portsA_bounds {C : Finset (Sym2 V)} (hC : NoLoops C) (hne : C.Nonempty) :
    (nodes C).card ≤ (portsA C).card ∧ (portsA C).card < 2 * (nodes C).card := by
  have hA := aggSet_spec hC hne
  unfold portsA; rw [card_portsOf]
  exact ⟨hA.enough, aggSet_sum_lt hA (fun v hv => degIn_succ_le hC hv)⟩

end APSP
