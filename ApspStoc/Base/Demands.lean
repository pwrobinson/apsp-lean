import ApspStoc.Base.Clusters

/-!
# Demands (Definition 3.1) and the demands of Lemmas 3.8 and 3.9

We construct the two concrete demands used by the paper on a cluster `C` and verify the
port-set sizes, loads and sizes claimed in the proofs of Lemmas 3.8 and 3.9 (these are the
quantities fed into Theorem 3.3). Theorem numbers refer to the STOC submission of the paper.
-/

namespace APSP

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A demand: a multiset of packets `(source port, destination port)`. -/
abbrev Demand (V : Type) := Multiset (Port V × Port V)

namespace Demand

/-- load of a port: number of packets having it as source plus number having it as destination -/
def load (D : Demand V) (x : Port V) : ℕ :=
  (D.filter (fun pq => pq.1 = x)).card + (D.filter (fun pq => pq.2 = x)).card

/-- size of a demand: total number of packets -/
def size (D : Demand V) : ℕ := Multiset.card D

/-- `D` is supported on the port set `P`. -/
def SupportedOn (D : Demand V) (P : Finset (Port V)) : Prop := ∀ pq ∈ D, pq.1 ∈ P ∧ pq.2 ∈ P

lemma card_filter_map {β : Type*} (S : Finset β) (f : β → Port V × Port V)
    (p : Port V × Port V → Prop) [DecidablePred p] :
    ((S.val.map f).filter p).card = (S.filter (fun x => p (f x))).card := by
  rw [Multiset.filter_map, Multiset.card_map]; rfl

end Demand

/-! ## Ceiling division -/

/-- `⌈a / b⌉` -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

lemma le_cdiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ cdiv a b * b := by
  show a ≤ (a + b - 1) / b * b
  have h := Nat.div_add_mod (a + b - 1) b
  have hr := Nat.mod_lt (a + b - 1) hb
  rw [mul_comm] at h
  omega

lemma cdiv_mul_lt (a b : ℕ) (hb : 0 < b) : cdiv a b * b < a + b := by
  show (a + b - 1) / b * b < a + b
  have := Nat.div_mul_le_self (a + b - 1) b
  omega

lemma one_le_cdiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 1 ≤ cdiv a b := by
  have h := le_cdiv_mul a b hb
  rcases Nat.eq_zero_or_pos (cdiv a b) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

/-! ## Balanced assignments -/

lemma exists_balanced {β γ : Type*} [DecidableEq β] [DecidableEq γ] (X : Finset β) (Y : Finset γ)
    (hY : Y.Nonempty) :
    ∃ f : β → γ, (∀ x ∈ X, f x ∈ Y) ∧ ∀ y, (X.filter (fun x => f x = y)).card ≤ X.card / Y.card + 1 := by
  classical
  have hk : 0 < Y.card := card_pos.2 hY
  let eX := X.equivFin
  let eY := Y.equivFin
  let f : β → γ := fun x =>
    if hx : x ∈ X then (eY.symm ⟨(eX ⟨x, hx⟩ : ℕ) % Y.card, Nat.mod_lt _ hk⟩ : γ) else hY.choose
  refine ⟨f, fun x hx => ?_, fun y => ?_⟩
  · simp only [f, dif_pos hx]; exact (eY.symm _).2
  · let g : β → ℕ := fun x => if hx : x ∈ X then (eX ⟨x, hx⟩ : ℕ) / Y.card else 0
    have hmaps : ∀ x ∈ X.filter (fun x => f x = y), g x ∈ range (X.card / Y.card + 1) := by
      intro x hx
      rw [mem_filter] at hx
      simp only [g, dif_pos hx.1, mem_range]
      have : (eX ⟨x, hx.1⟩ : ℕ) < X.card := (eX ⟨x, hx.1⟩).2
      exact Nat.lt_succ_of_le (Nat.div_le_div_right this.le)
    have hinj : Set.InjOn g (X.filter (fun x => f x = y)) := by
      intro x hx x' hx' hg
      simp only [coe_filter, Set.mem_setOf_eq] at hx hx'
      obtain ⟨hxX, hfx⟩ := hx
      obtain ⟨hxX', hfx'⟩ := hx'
      simp only [g, dif_pos hxX, dif_pos hxX'] at hg
      have hf : f x = f x' := hfx.trans hfx'.symm
      simp only [f, dif_pos hxX, dif_pos hxX'] at hf
      have hmod := congrArg (fun z => (eY z : ℕ)) (Subtype.ext hf)
      simp only [Equiv.apply_symm_apply] at hmod
      have h1 := Nat.div_add_mod (eX ⟨x, hxX⟩ : ℕ) Y.card
      have h2 := Nat.div_add_mod (eX ⟨x', hxX'⟩ : ℕ) Y.card
      have heq : (eX ⟨x, hxX⟩ : ℕ) = eX ⟨x', hxX'⟩ := by
        rw [← h1, ← h2, hg]; congr 1
      have := eX.injective (Fin.ext heq)
      exact congrArg Subtype.val this
    have := card_le_card_of_injOn g hmaps hinj
    simpa using this

/-! ## A canonical, locally computable assignment of destination ports

The packets of Lemma 3.8 destined to an aggregator `a` are spread over the ports of `a` by a rule
that the *sending* node can evaluate: the ports of the cluster are ranked by (index of the node,
index of the edge) in the fixed enumerations `Fintype.equivFin V` and `Fintype.equivFin (Sym2 V)`,
and the packet from port `x` goes to the port of `a` at position `rank x mod deg_C(a)` among the
ports of `a` ordered by edge index. The rank of `x = (v, e)` is the total degree of the nodes of
smaller index than `v` plus the number of edges of `C` at `v` of smaller index than `e`
(`rankL`): it needs only the degree table of the cluster and the sender's own cluster edges. -/

section Canonical

set_option linter.unusedSectionVars false

/-- the index of a node in the fixed enumeration `Fintype.equivFin V` -/
noncomputable def vIdx (v : V) : ℕ := (Fintype.equivFin V v : ℕ)

/-- the index of an edge in the fixed enumeration `Fintype.equivFin (Sym2 V)` -/
noncomputable def eIdx (e : Sym2 V) : ℕ := (Fintype.equivFin (Sym2 V) e : ℕ)

lemma vIdx_inj {u v : V} (h : vIdx u = vIdx v) : u = v :=
  (Fintype.equivFin V).injective (Fin.ext h)

lemma eIdx_inj {e e' : Sym2 V} (h : eIdx e = eIdx e') : e = e' :=
  (Fintype.equivFin (Sym2 V)).injective (Fin.ext h)

/-- The rank of the port `x = (v, e)`, computed from the degree function `deg` of the cluster and
the slice `sl` of the sender (its incident cluster edges): the total degree of the nodes of
smaller index than `v`, plus the number of edges of `sl` of smaller index than `e`. -/
noncomputable def rankL (deg : V → ℕ) (sl : Finset (Sym2 V)) (x : Port V) : ℕ :=
  ∑ u ∈ univ.filter (fun u => vIdx u < vIdx x.1), deg u +
    (sl.filter (fun e => eIdx e < eIdx x.2)).card

/-- the position of the port `p` in the port set `pa`, ordered by edge index -/
noncomputable def posL (pa : Finset (Port V)) (p : Port V) : ℕ :=
  (pa.filter (fun q => eIdx q.2 < eIdx p.2)).card

/-- the port of `pa` at position `i` (ordered by edge index); the default `d` if there is none -/
noncomputable def pickL (pa : Finset (Port V)) (i : ℕ) (d : Port V) : Port V :=
  if h : ∃ p ∈ pa, posL pa p = i then h.choose else d

/-- **Local destination assignment.** The packet from port `x` to the aggregator whose ports are
`pa` goes to the port of `pa` at position `rankL deg sl x mod |pa|` (ordered by edge index). It
depends only on the degree function `deg` (from the setup table), the sender's own cluster edges
`sl`, and the ports `pa` of the aggregator (known from `portsA C`). -/
noncomputable def dstAssignL (deg : V → ℕ) (sl : Finset (Sym2 V)) (pa : Finset (Port V))
    (x : Port V) : Port V :=
  pickL pa (rankL deg sl x % pa.card) x

/-- ports of `pa` with the same edge are equal (true for the ports of one node) -/
def EdgeInj (pa : Finset (Port V)) : Prop := ∀ p ∈ pa, ∀ q ∈ pa, p.2 = q.2 → p = q

lemma posL_lt {pa : Finset (Port V)} {p : Port V} (hp : p ∈ pa) : posL pa p < pa.card :=
  card_lt_card (filter_ssubset.2 ⟨p, hp, lt_irrefl _⟩)

lemma posL_lt_posL {pa : Finset (Port V)} {p q : Port V} (hp : p ∈ pa)
    (hlt : eIdx p.2 < eIdx q.2) : posL pa p < posL pa q := by
  apply card_lt_card
  rw [ssubset_iff_of_subset (fun r hr => by
    rw [mem_filter] at hr ⊢; exact ⟨hr.1, hr.2.trans hlt⟩)]
  exact ⟨p, mem_filter.2 ⟨hp, hlt⟩, fun h => lt_irrefl _ (mem_filter.1 h).2⟩

lemma posL_injOn {pa : Finset (Port V)} (hpa : EdgeInj pa) {p q : Port V} (hp : p ∈ pa)
    (hq : q ∈ pa) (h : posL pa p = posL pa q) : p = q := by
  rcases lt_trichotomy (eIdx p.2) (eIdx q.2) with hlt | heq | hlt
  · exact absurd h (posL_lt_posL hp hlt).ne
  · exact hpa p hp q hq (eIdx_inj heq)
  · exact absurd h (posL_lt_posL hq hlt).ne'

/-- every position below `|pa|` is taken -/
lemma posL_surj {pa : Finset (Port V)} (hpa : EdgeInj pa) {i : ℕ} (hi : i < pa.card) :
    ∃ p ∈ pa, posL pa p = i := by
  have hsub : pa.image (posL pa) ⊆ range pa.card := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hk
    exact mem_range.2 (posL_lt hp)
  have hcard : (range pa.card).card ≤ (pa.image (posL pa)).card := by
    rw [card_range, card_image_of_injOn (fun p hp q hq h => posL_injOn hpa hp hq h)]
  have heq := eq_of_subset_of_card_le hsub hcard
  have hi' : i ∈ pa.image (posL pa) := heq ▸ mem_range.2 hi
  obtain ⟨p, hp, h⟩ := mem_image.1 hi'
  exact ⟨p, hp, h⟩

lemma pickL_spec {pa : Finset (Port V)} (hpa : EdgeInj pa) {i : ℕ} (hi : i < pa.card)
    (d : Port V) : pickL pa i d ∈ pa ∧ posL pa (pickL pa i d) = i := by
  have h := posL_surj hpa hi
  unfold pickL
  rw [dite_eq_left h]
  exact h.choose_spec

lemma edgeInj_portsAt (C : Finset (Sym2 V)) (a : V) : EdgeInj (portsAt C a) :=
  fun _ hp _ hq h => Prod.ext ((mem_portsAt.1 hp).1.trans (mem_portsAt.1 hq).1.symm) h

end Canonical

/-! ## Lemma 3.9: every node sends one packet to every aggregator port -/

section Lemma39
variable (C : Finset (Sym2 V))

/-- the designated port of node `v` in cluster `C` -/
noncomputable def srcPort (v : V) : Port V := by
  classical exact if h : ∃ e, e ∈ C ∧ v ∈ e then (v, h.choose) else (v, s(v, v))

lemma srcPort_fst (v : V) : (srcPort C v).1 = v := by
  unfold srcPort; split <;> rfl

lemma srcPort_mem {v : V} (hv : v ∈ nodes C) : srcPort C v ∈ portsAt C v := by
  have hex : ∃ e, e ∈ C ∧ v ∈ e := by obtain ⟨e, he, h⟩ := mem_nodes.1 hv; exact ⟨e, he, h⟩
  unfold srcPort; rw [dif_pos hex]
  exact mem_portsAt.2 ⟨rfl, hex.choose_spec.1, hex.choose_spec.2⟩

/-- The demand of Lemma 3.9: node `v` sends a packet from its designated port to every port of
`A(C)`. -/
noncomputable def portsDemand : Demand V :=
  (nodes C ×ˢ portsA C).val.map (fun x => (srcPort C x.1, x.2))

/-- The port set `P'` of Lemma 3.9. -/
noncomputable def portsP : Finset (Port V) := portsA C ∪ (nodes C).image (srcPort C)

variable {C}

lemma portsDemand_supported : (portsDemand C).SupportedOn (portsP C) := by
  intro pq hpq
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hpq
  rw [mem_val, mem_product] at hx
  exact ⟨mem_union_right _ (mem_image_of_mem _ hx.1), mem_union_left _ hx.2⟩

lemma portsDemand_size : (portsDemand C).size = (nodes C).card * (portsA C).card := by
  unfold portsDemand Demand.size; rw [Multiset.card_map, card_val, card_product]

lemma portsDemand_load (x : Port V) :
    (portsDemand C).load x ≤ (portsA C).card + (nodes C).card := by
  unfold Demand.load portsDemand
  rw [Demand.card_filter_map, Demand.card_filter_map]
  apply Nat.add_le_add
  · calc _ ≤ ({x.1} ×ˢ portsA C).card := by
          apply card_le_card; intro y hy
          rw [mem_filter, mem_product] at hy
          rw [mem_product, mem_singleton]
          exact ⟨by rw [← hy.2, srcPort_fst], hy.1.2⟩
      _ = _ := by simp
  · calc _ ≤ (nodes C ×ˢ {x}).card := by
          apply card_le_card; intro y hy
          rw [mem_filter, mem_product] at hy
          rw [mem_product, mem_singleton]; exact ⟨hy.1.1, hy.2⟩
      _ = _ := by simp

lemma portsP_card_le : (portsP C).card ≤ (portsA C).card + (nodes C).card :=
  (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)

lemma portsA_subset_portsP : portsA C ⊆ portsP C := subset_union_left

end Lemma39

/-! ## Lemma 3.8: the topology-collection demand -/

section Lemma38
variable (C : Finset (Sym2 V))

/-- Number of source ports used by node `v`: the paper's `⌈deg_C(v) · n_C / m_C⌉` (capped by
`deg_C(v)`, which the paper leaves implicit); aggregators use all their ports. -/
noncomputable def kPorts (v : V) : ℕ :=
  if v ∈ aggSet C then degIn C v else min (degIn C v) (cdiv (degIn C v * (nodes C).card) C.card)

lemma kPorts_le (v : V) : kPorts C v ≤ degIn C v := by
  unfold kPorts; split_ifs
  · exact le_refl _
  · exact min_le_left _ _

lemma exists_srcSet (v : V) : ∃ T, T ⊆ portsAt C v ∧ T.card = kPorts C v :=
  exists_subset_card_eq (by rw [card_portsAt]; exact kPorts_le C v)

/-- the source ports of `v` (the "first" `kPorts v` ports of `v`) -/
noncomputable def srcSet (v : V) : Finset (Port V) := Classical.choose (exists_srcSet C v)

lemma srcSet_sub (v : V) : srcSet C v ⊆ portsAt C v := (Classical.choose_spec (exists_srcSet C v)).1
lemma srcSet_card (v : V) : (srcSet C v).card = kPorts C v :=
  (Classical.choose_spec (exists_srcSet C v)).2

/-- All ports of the cluster. -/
def allPorts : Finset (Port V) := portsOf C (nodes C)

/-- packets of node `v`: one per (incident cluster edge, aggregator) -/
noncomputable def pktsOf (v : V) : Finset (Port V × V) := portsAt C v ×ˢ aggSet C

/-- balanced assignment of `v`'s packets to its source ports -/
noncomputable def srcAssign (v : V) : Port V × V → Port V := by
  classical exact if h : (srcSet C v).Nonempty then
    Classical.choose (exists_balanced (pktsOf C v) (srcSet C v) h) else fun _ => (v, s(v, v))

/-- The rank of the port `x = (v, e)` among the ports of `C`, ordered by (node index, edge
index): the total degree of the nodes of `C` of smaller index than `v`, plus the number of edges
of `C` at `v` of smaller index than `e`. On `allPorts C` it is a bijection onto
`[0, |allPorts C|)` (`portRank_lt`, `portRank_injOn`). -/
noncomputable def portRank (x : Port V) : ℕ :=
  ∑ u ∈ (nodes C).filter (fun u => vIdx u < vIdx x.1), degIn C u +
    (C.filter (fun e => x.1 ∈ e ∧ eIdx e < eIdx x.2)).card

/-- Canonical balanced assignment of the packets destined to aggregator `a` to the ports of `a`:
the packet from port `x` goes to the port of `a` at position `portRank C x mod deg_C(a)` among the
ports of `a` ordered by edge index. The sender computes it locally (`dstAssign_local`). -/
noncomputable def dstAssign (a : V) (x : Port V) : Port V :=
  pickL (portsAt C a) (portRank C x % degIn C a) x

/-- The demand of Lemma 3.8: for every cluster edge `e` incident to `v` and every aggregator
`a ∈ A(C)`, a packet carrying `e` is sent from one of `v`'s source ports to a port of `a`. -/
noncomputable def topoDemand : Demand V :=
  (allPorts C ×ˢ aggSet C).val.map (fun x => (srcAssign C x.1.1 x, dstAssign C x.2 x.1))

/-- The port set `P'` of Lemma 3.8. -/
noncomputable def topoP : Finset (Port V) := portsA C ∪ (nodes C).biUnion (srcSet C)

variable {C}

lemma srcAssign_spec {v : V} (h : (srcSet C v).Nonempty) :
    (∀ x ∈ pktsOf C v, srcAssign C v x ∈ srcSet C v) ∧
    ∀ y, ((pktsOf C v).filter (fun x => srcAssign C v x = y)).card ≤
      (pktsOf C v).card / (srcSet C v).card + 1 := by
  unfold srcAssign; rw [dif_pos h]
  exact Classical.choose_spec (exists_balanced (pktsOf C v) (srcSet C v) h)

lemma mem_allPorts {p : Port V} : p ∈ allPorts C ↔ p.1 ∈ nodes C ∧ p ∈ portsAt C p.1 := by
  unfold allPorts portsOf; rw [mem_biUnion]
  constructor
  · rintro ⟨v, hv, hp⟩; have := (mem_portsAt.1 hp).1; subst this; exact ⟨hv, hp⟩
  · rintro ⟨h1, h2⟩; exact ⟨_, h1, h2⟩

/-! ### The rank of a port -/

/-- the edges of `C` at `x.1` of smaller index than `x.2` are fewer than `deg_C(x.1)` -/
lemma card_lowerEdges_lt {x : Port V} (hx : x ∈ allPorts C) :
    (C.filter (fun e => x.1 ∈ e ∧ eIdx e < eIdx x.2)).card < degIn C x.1 := by
  obtain ⟨-, hp⟩ := mem_allPorts.1 hx
  obtain ⟨-, he, hve⟩ := mem_portsAt.1 hp
  unfold degIn
  apply card_lt_card
  rw [ssubset_iff_of_subset (fun e he' => by
    rw [mem_filter] at he' ⊢; exact ⟨he'.1, he'.2.1⟩)]
  exact ⟨x.2, mem_filter.2 ⟨he, hve⟩, fun h => lt_irrefl _ (mem_filter.1 h).2.2⟩

lemma sum_lowerNodes_add_le {u v : V} (hu : u ∈ nodes C) (huv : vIdx u < vIdx v) :
    ∑ w ∈ (nodes C).filter (fun w => vIdx w < vIdx u), degIn C w + degIn C u ≤
      ∑ w ∈ (nodes C).filter (fun w => vIdx w < vIdx v), degIn C w := by
  have hnot : u ∉ (nodes C).filter (fun w => vIdx w < vIdx u) :=
    fun h => lt_irrefl _ (mem_filter.1 h).2
  rw [add_comm, ← sum_insert hnot]
  apply sum_le_sum_of_subset
  intro w hw
  rw [mem_insert] at hw
  rw [mem_filter]
  rcases hw with rfl | hw
  · exact ⟨hu, huv⟩
  · rw [mem_filter] at hw; exact ⟨hw.1, hw.2.trans huv⟩

lemma sum_lowerNodes_add_le_card {v : V} (hv : v ∈ nodes C) :
    ∑ w ∈ (nodes C).filter (fun w => vIdx w < vIdx v), degIn C w + degIn C v ≤
      (allPorts C).card := by
  have hnot : v ∉ (nodes C).filter (fun w => vIdx w < vIdx v) :=
    fun h => lt_irrefl _ (mem_filter.1 h).2
  rw [add_comm, ← sum_insert hnot, allPorts, card_portsOf]
  apply sum_le_sum_of_subset
  intro w hw
  rw [mem_insert] at hw
  rcases hw with rfl | hw
  · exact hv
  · exact (mem_filter.1 hw).1

lemma portRank_lt {x : Port V} (hx : x ∈ allPorts C) : portRank C x < (allPorts C).card := by
  have h1 := card_lowerEdges_lt hx
  have h2 := sum_lowerNodes_add_le_card (mem_allPorts.1 hx).1
  unfold portRank; omega

lemma portRank_injOn {x y : Port V} (hx : x ∈ allPorts C) (hy : y ∈ allPorts C)
    (h : portRank C x = portRank C y) : x = y := by
  have key1 : ∀ x ∈ allPorts C, ∀ y : Port V, vIdx x.1 < vIdx y.1 →
      portRank C x < portRank C y := by
    intro x hx y hlt
    have h1 := card_lowerEdges_lt hx
    have h2 := sum_lowerNodes_add_le (C := C) (mem_allPorts.1 hx).1 hlt
    unfold portRank; omega
  have h1 : x.1 = y.1 := by
    rcases lt_trichotomy (vIdx x.1) (vIdx y.1) with hlt | heq | hlt
    · exact absurd h (key1 x hx y hlt).ne
    · exact vIdx_inj heq
    · exact absurd h (key1 y hy x hlt).ne'
  have key2 : ∀ x ∈ allPorts C, ∀ y : Port V, x.1 = y.1 → eIdx x.2 < eIdx y.2 →
      portRank C x < portRank C y := by
    intro x hx y h1 hlt
    obtain ⟨-, hp⟩ := mem_allPorts.1 hx
    obtain ⟨-, he, hve⟩ := mem_portsAt.1 hp
    unfold portRank
    rw [h1]
    apply Nat.add_lt_add_left
    apply card_lt_card
    rw [ssubset_iff_of_subset (fun e he' => by
      rw [mem_filter] at he' ⊢; exact ⟨he'.1, he'.2.1, he'.2.2.trans hlt⟩)]
    exact ⟨x.2, mem_filter.2 ⟨he, h1 ▸ hve, hlt⟩, fun h => lt_irrefl _ (mem_filter.1 h).2.2⟩
  have h2 : x.2 = y.2 := by
    rcases lt_trichotomy (eIdx x.2) (eIdx y.2) with hlt | heq | hlt
    · exact absurd h (key2 x hx y h1 hlt).ne
    · exact eIdx_inj heq
    · exact absurd h (key2 y hy x h1.symm hlt).ne'
  exact Prod.ext h1 h2

/-- The rank of a port is computed locally by the sender (`rankL`), from the degree function and
its own cluster edges. -/
lemma portRank_eq_rankL (x : Port V) :
    portRank C x = rankL (degIn C) (C.filter (fun e => x.1 ∈ e)) x := by
  unfold portRank rankL
  congr 1
  · apply sum_subset
    · intro u hu
      rw [mem_filter] at hu ⊢
      exact ⟨mem_univ _, hu.2⟩
    · intro u hu hn
      rw [mem_filter] at hu
      exact degIn_eq_zero (fun h => hn (mem_filter.2 ⟨h, hu.2⟩))
  · rw [filter_filter]

lemma dstAssign_mem_posL {a : V} (h : (portsAt C a).Nonempty) (x : Port V) :
    dstAssign C a x ∈ portsAt C a ∧
      posL (portsAt C a) (dstAssign C a x) = portRank C x % degIn C a := by
  have hd : 0 < degIn C a := by rw [← card_portsAt]; exact card_pos.2 h
  have hi : portRank C x % degIn C a < (portsAt C a).card := by
    rw [card_portsAt]; exact Nat.mod_lt _ hd
  exact pickL_spec (edgeInj_portsAt C a) hi x

/-- **Balance**: every port of `a` receives at most `|allPorts C| / deg_C(a) + 1` packets. -/
lemma dstAssign_spec {a : V} (h : (portsAt C a).Nonempty) :
    (∀ x ∈ allPorts C, dstAssign C a x ∈ portsAt C a) ∧
    ∀ y, ((allPorts C).filter (fun x => dstAssign C a x = y)).card ≤
      (allPorts C).card / (portsAt C a).card + 1 := by
  refine ⟨fun x _ => (dstAssign_mem_posL h x).1, fun y => ?_⟩
  have hd : 0 < degIn C a := by rw [← card_portsAt]; exact card_pos.2 h
  rw [card_portsAt]
  have hsub : (allPorts C).filter (fun x => dstAssign C a x = y) ⊆
      (allPorts C).filter (fun x => portRank C x % degIn C a = posL (portsAt C a) y) := by
    intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [← hx.2]
    exact (dstAssign_mem_posL h x).2.symm
  refine (card_le_card hsub).trans ?_
  have hmaps : ∀ x ∈ (allPorts C).filter
      (fun x => portRank C x % degIn C a = posL (portsAt C a) y),
      portRank C x / degIn C a ∈ range ((allPorts C).card / degIn C a + 1) := by
    intro x hx
    rw [mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (portRank_lt (mem_filter.1 hx).1).le)
  have hinj : Set.InjOn (fun x => portRank C x / degIn C a) ((allPorts C).filter
      (fun x => portRank C x % degIn C a = posL (portsAt C a) y)) := by
    intro x hx x' hx' hq
    rw [mem_coe, mem_filter] at hx hx'
    apply portRank_injOn hx.1 hx'.1
    have h1 := Nat.div_add_mod (portRank C x) (degIn C a)
    have h2 := Nat.div_add_mod (portRank C x') (degIn C a)
    simp only at hq
    rw [← h1, ← h2, hq, hx.2, hx'.2]
  simpa using card_le_card_of_injOn _ hmaps hinj

/-- The destination port is a function of local data, for every port `x`. -/
lemma dstAssign_eq_dstAssignL (a : V) (x : Port V) :
    dstAssign C a x = dstAssignL (degIn C) (C.filter (fun e => x.1 ∈ e)) (portsAt C a) x := by
  unfold dstAssign dstAssignL
  rw [card_portsAt, portRank_eq_rankL]

set_option linter.unusedVariables false in
/-- **The destination port is computed locally by the sender** of the packet `x`: from the degree
function of the cluster (the setup table), its own cluster edges `C ∩ inc(x.1)`, and the ports of
`a` (known from `portsA C`). (The identity holds for every port, `dstAssign_eq_dstAssignL`.) -/
theorem dstAssign_local {C : Finset (Sym2 V)} (a : V) {x : Port V} (hx : x ∈ allPorts C) :
    dstAssign C a x = dstAssignL (degIn C) (C.filter (fun e => x.1 ∈ e)) (portsAt C a) x :=
  dstAssign_eq_dstAssignL a x

lemma card_allPorts (hC : NoLoops C) : (allPorts C).card = 2 * C.card := by
  unfold allPorts; rw [card_portsOf, sum_degIn hC]

lemma srcSet_nonempty (hne : C.Nonempty) {v : V} (hv : v ∈ nodes C) : (srcSet C v).Nonempty := by
  rw [← card_pos, srcSet_card]
  have hd := degIn_pos hv
  have hm : 0 < C.card := card_pos.2 hne
  have hn : 0 < (nodes C).card := card_pos.2 ⟨v, hv⟩
  unfold kPorts; split_ifs
  · exact hd
  · exact lt_min hd (one_le_cdiv (Nat.mul_pos hd hn) hm)

lemma portsAt_nonempty {v : V} (hv : v ∈ nodes C) : (portsAt C v).Nonempty := by
  rw [← card_pos, card_portsAt]; exact degIn_pos hv

lemma topoDemand_supported (hC : NoLoops C) (hne : C.Nonempty) :
    (topoDemand C).SupportedOn (topoP C) := by
  have hA := aggSet_spec hC hne
  intro pq hpq
  obtain ⟨⟨p, a⟩, hx, rfl⟩ := Multiset.mem_map.1 hpq
  rw [mem_val, mem_product] at hx
  obtain ⟨hp, ha⟩ := hx
  obtain ⟨hp1, hp2⟩ := mem_allPorts.1 hp
  refine ⟨?_, ?_⟩
  · apply mem_union_right; rw [mem_biUnion]
    exact ⟨p.1, hp1, (srcAssign_spec (srcSet_nonempty hne hp1)).1 _ (mem_product.2 ⟨hp2, ha⟩)⟩
  · apply mem_union_left
    have haN : a ∈ nodes C := hA.top.1 ha
    have := (dstAssign_spec (portsAt_nonempty haN)).1 p hp
    unfold portsA portsOf; exact mem_biUnion.2 ⟨a, ha, this⟩

lemma topoDemand_size (hC : NoLoops C) :
    (topoDemand C).size = 2 * C.card * (aggSet C).card := by
  unfold topoDemand Demand.size
  rw [Multiset.card_map, card_val, card_product, card_allPorts hC]

/-- arithmetic core of the source-load bound of Lemma 3.8 -/
lemma src_arith {d q k n m : ℕ} (hd : 1 ≤ d) (hm : 0 < m) (hq : q ≤ n) (hqm : q * m < n ^ 2)
    (hk : k = d ∨ k = cdiv (d * n) m) : d * q / k ≤ n := by
  rcases hk with rfl | rfl
  · rw [Nat.mul_div_cancel_left _ (by omega)]; exact hq
  · apply Nat.div_le_of_le_mul
    have h2 := le_cdiv_mul (d * n) m hm
    have : m * (d * q) < m * (cdiv (d * n) m * n) := by nlinarith
    exact (Nat.lt_of_mul_lt_mul_left this).le

lemma topoDemand_load (hC : NoLoops C) (hne : C.Nonempty) (y : Port V) :
    (topoDemand C).load y ≤ 5 * (nodes C).card + 2 := by
  have hA := aggSet_spec hC hne
  have hm : 0 < C.card := card_pos.2 hne
  unfold Demand.load topoDemand
  rw [Demand.card_filter_map, Demand.card_filter_map]
  -- source part
  have hsrc : ((allPorts C ×ˢ aggSet C).filter
      (fun x => srcAssign C x.1.1 x = y)).card ≤ (nodes C).card + 1 := by
    by_cases hy : y.1 ∈ nodes C
    · have hsub : (allPorts C ×ˢ aggSet C).filter (fun x => srcAssign C x.1.1 x = y) ⊆
          (pktsOf C y.1).filter (fun x => srcAssign C y.1 x = y) := by
        intro x hx
        rw [mem_filter, mem_product] at hx
        obtain ⟨⟨hp, ha⟩, heq⟩ := hx
        obtain ⟨hp1, hp2⟩ := mem_allPorts.1 hp
        have hmem := (srcAssign_spec (srcSet_nonempty hne hp1)).1 x (mem_product.2 ⟨hp2, ha⟩)
        have h1 : x.1.1 = y.1 := by
          rw [← heq]; exact (mem_portsAt.1 (srcSet_sub C _ hmem)).1.symm
        rw [mem_filter, ← h1]; exact ⟨mem_product.2 ⟨hp2, ha⟩, heq⟩
      refine (card_le_card hsub).trans ((srcAssign_spec (srcSet_nonempty hne hy)).2 y |>.trans ?_)
      rw [srcSet_card]
      unfold pktsOf; rw [card_product, card_portsAt]
      apply Nat.add_le_add_right
      apply src_arith (degIn_pos hy) hm (card_le_card hA.top.1)
        (aggSet_card_mul_lt hA (fun v hv => degIn_succ_le hC hv) (sum_degIn hC))
      unfold kPorts; split_ifs
      · exact Or.inl rfl
      · rcases min_choice (degIn C y.1) (cdiv (degIn C y.1 * (nodes C).card) C.card) with h | h
        · exact Or.inl h
        · exact Or.inr h
    · have : (allPorts C ×ˢ aggSet C).filter (fun x => srcAssign C x.1.1 x = y) = ∅ := by
        rw [filter_eq_empty_iff]
        intro x hx heq
        rw [mem_product] at hx
        obtain ⟨hp1, hp2⟩ := mem_allPorts.1 hx.1
        have hmem := (srcAssign_spec (srcSet_nonempty hne hp1)).1 x (mem_product.2 ⟨hp2, hx.2⟩)
        rw [heq] at hmem
        have := (mem_portsAt.1 (srcSet_sub C _ hmem)).1
        exact hy (this ▸ hp1)
      rw [this, card_empty]; omega
  -- destination part
  have hdst : ((allPorts C ×ˢ aggSet C).filter
      (fun x => dstAssign C x.2 x.1 = y)).card ≤ 4 * (nodes C).card + 1 := by
    by_cases hy : y.1 ∈ aggSet C
    · have hyN : y.1 ∈ nodes C := hA.top.1 hy
      have hsub : (allPorts C ×ˢ aggSet C).filter (fun x => dstAssign C x.2 x.1 = y) ⊆
          ((allPorts C).filter (fun p => dstAssign C y.1 p = y)) ×ˢ {y.1} := by
        intro x hx
        rw [mem_filter, mem_product] at hx
        obtain ⟨⟨hp, ha⟩, heq⟩ := hx
        have hmem := (dstAssign_spec (portsAt_nonempty (hA.top.1 ha))).1 x.1 hp
        have h1 : x.2 = y.1 := by rw [← heq]; exact (mem_portsAt.1 hmem).1.symm
        rw [mem_product, mem_filter, mem_singleton, ← h1]; exact ⟨⟨hp, heq⟩, rfl⟩
      refine (card_le_card hsub).trans ?_
      rw [card_product, card_singleton, mul_one]
      refine ((dstAssign_spec (portsAt_nonempty hyN)).2 y).trans ?_
      rw [card_allPorts hC, card_portsAt]
      apply Nat.add_le_add_right
      apply Nat.div_le_of_le_mul
      have := aggSet_deg_ge hA (fun v hv => ⟨degIn_pos hv, degIn_succ_le hC hv⟩) (sum_degIn hC)
        y.1 hy
      nlinarith
    · have : (allPorts C ×ˢ aggSet C).filter (fun x => dstAssign C x.2 x.1 = y) = ∅ := by
        rw [filter_eq_empty_iff]
        intro x hx heq
        rw [mem_product] at hx
        have hmem := (dstAssign_spec (portsAt_nonempty (hA.top.1 hx.2))).1 x.1 hx.1
        rw [heq] at hmem
        exact hy ((mem_portsAt.1 hmem).1 ▸ hx.2)
      rw [this, card_empty]; omega
  exact (Nat.add_le_add hsrc hdst).trans (by omega)

lemma topoP_card_le (hC : NoLoops C) (hne : C.Nonempty) :
    (topoP C).card ≤ 7 * (nodes C).card := by
  have hA := aggSet_spec hC hne
  have hm : 0 < C.card := card_pos.2 hne
  have h1 := (card_portsA_bounds hC hne).2
  have h2 : ((nodes C).biUnion (srcSet C)).card ≤ ∑ v ∈ nodes C, kPorts C v := by
    refine card_biUnion_le.trans (le_of_eq ?_)
    exact sum_congr rfl (fun v _ => srcSet_card C v)
  have hk : ∀ v ∈ nodes C, kPorts C v ≤
      (if v ∈ aggSet C then degIn C v else 0) + cdiv (degIn C v * (nodes C).card) C.card := by
    intro v _; unfold kPorts; split_ifs <;> simp
  have h3 : ∑ v ∈ nodes C, kPorts C v ≤ ∑ v ∈ aggSet C, degIn C v +
      ∑ v ∈ nodes C, cdiv (degIn C v * (nodes C).card) C.card := by
    refine (sum_le_sum hk).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hA.top.1]
  have h4 : (∑ v ∈ nodes C, cdiv (degIn C v * (nodes C).card) C.card) * C.card ≤
      3 * (nodes C).card * C.card := by
    rw [sum_mul]
    calc ∑ v ∈ nodes C, cdiv (degIn C v * (nodes C).card) C.card * C.card
        ≤ ∑ v ∈ nodes C, (degIn C v * (nodes C).card + C.card) :=
          sum_le_sum (fun v _ => (cdiv_mul_lt _ _ hm).le)
      _ = 2 * C.card * (nodes C).card + (nodes C).card * C.card := by
          rw [sum_add_distrib, ← sum_mul, sum_degIn hC, sum_const, smul_eq_mul]
      _ = 3 * (nodes C).card * C.card := by ring
  have h5 := Nat.le_of_mul_le_mul_right h4 hm
  have h6 : ∑ v ∈ aggSet C, degIn C v < 2 * (nodes C).card :=
    aggSet_sum_lt hA (fun v hv => degIn_succ_le hC hv)
  have h7 := card_union_le (portsA C) ((nodes C).biUnion (srcSet C))
  unfold topoP; omega

lemma portsA_subset_topoP : portsA C ⊆ topoP C := subset_union_left

end Lemma38

end APSP
