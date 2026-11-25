import ApspStoc.Congest.EmbConstructPar
import ApspStoc.Congest.EmbConstructLocal

/-!
# The final output of `embedConstruct`

At the end, a node `v` holds, for each of its clusters `C` (slice `s`), the output of the
pipeline in `C`: the setup output (`portsA C`), the topology packets received at its ports, and
the recorded routes through it (`r C`). From these and the global dilation and overlap it computes
(`ekL`) its embedding knowledge for `E = construct cl r`:
* `viewL_eq`: it hosts the aggregator of `C` in overlay `j < n` iff `(portAssign C j).1 = v`
  (the common endpoint of the dummy routes, `aggHost_construct`); then `v ∈ A(C)`, so it received
  a topology packet for every port of `C` (`topoL_eq`), whose payload carries the edge and its
  weight (`wL_eq`);
* `embL_eq`: the paths through it, in the key-edge model (`ioEmb`): its own paths (it is the
  source of its own dummy packets) and the non-empty paths through it of other sources, keyed by
  their source ports (`srcPort` of the source, whose second component is the key edge);
* its slices, and the public dilation and overlap.
`valE_eq` computes the local values (maximum own path length over the overlays `j < n`, number of
clusters), whose maxima over all nodes are `E.dil` and `E.ov` (`dil_construct`).
-/

namespace APSP.Stoc.Congest

namespace EmbC

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the pipeline output of `v` in cluster `C` after a successful run (setup output with leader
`ℓ` and parent `pr`, topology knowledge for routes `r₂`, dummy-route knowledge for routes `r`) -/
noncomputable def oOf (N : WNet V) (wexp : ℕ) (C : Finset (Sym2 V)) (ℓ : V) (pr : Option V)
    (r₂ r : Routes V) (v : V) : PipeOut V :=
  ((((), (ℓ, pr, tabOf C, portsA C)), rkAt r₂ (topoDemand C) (pl2 N wexp C) (.inl v)),
    rkAt r (portsDemand C) (pl3 C) (.inl v))

/-- hypotheses on the clusters and the dummy routes -/
structure OutH (N : WNet V) (wexp Lb : ℕ) (cl : Finset (Finset (Sym2 V)))
    (r : Finset (Sym2 V) → Routes V) : Prop where
  hcl : ClH N cl
  w : ∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp
  walk : ∀ C ∈ cl, ∀ v ∈ nodes C, ∀ q ∈ portsA C, IsEdgeWalk (r C (srcPort C v, q)) v q.1 ∧
    (∀ e ∈ r C (srcPort C v, q), e ∈ C) ∧ (r C (srcPort C v, q)).length ≤ Fintype.card V ^ Lb

/-- the hypotheses on the final state of a node -/
structure OutH.NodeH (N : WNet V) (wexp : ℕ) (cl : Finset (Finset (Sym2 V)))
    (r : Finset (Sym2 V) → Routes V) (P : Proto V) (v : V) (inp : Agent V → Option Mem)
    (cp : Finset (Sym2 V) → P.S) (o : Finset (Sym2 V) → PipeOut V) : Prop where
  sl : mSl inp v = clLoc cl v
  cp : ∀ C ∈ cl, v ∈ nodes C → cOut P v (cp (C.filter (fun e => v ∈ e))) = some (o C)
  o : ∀ C ∈ cl, v ∈ nodes C → ∃ ℓ pr r₂, o C = oOf N wexp C ℓ pr r₂ (r C) v

lemma OutH.NodeH.clOf {N : WNet V} {wexp : ℕ} {cl : Finset (Finset (Sym2 V))}
    {r : Finset (Sym2 V) → Routes V} {P : Proto V} {v : V} {inp : Agent V → Option Mem}
    {cp : Finset (Sym2 V) → P.S} {o : Finset (Sym2 V) → PipeOut V}
    (hN : OutH.NodeH N wexp cl r P v inp cp o) (hcl : ClH N cl) {s : Finset (Sym2 V)}
    (hs : s ∈ clLoc cl v) : cOut P v (cp s) = some (o (clOf cl v s)) := by
  have h := clOf_spec hcl hs
  have hv := mem_nodes_clOf hcl hs
  have := hN.cp _ h.1 hv
  rw [h.2] at this
  exact this

section Walks

lemma isEdgeWalk_unique : ∀ {l : List (Sym2 V)} {a b b' : V}, IsEdgeWalk l a b →
    IsEdgeWalk l a b' → b = b'
  | [], _, _, _, h, h' => h.symm.trans h'
  | e :: l, a, b, b', ⟨x, hx, h⟩, ⟨x', hx', h'⟩ => by
    have : x = x' := by
      rw [hx] at hx'
      rcases Sym2.eq_iff.1 hx' with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · rw [h1] at h2; exact h2
    subst this
    exact isEdgeWalk_unique h h'

end Walks

namespace OutH

variable {N : WNet V} {wexp Lb : ℕ} {cl : Finset (Finset (Sym2 V))}
  {r : Finset (Sym2 V) → Routes V} (H : OutH N wexp Lb cl r)
include H

lemma noLoops {C : Finset (Sym2 V)} (hC : C ∈ cl) : NoLoops C := ecNoLoops (H.hcl.sub C hC)

lemma portsA_ne {C : Finset (Sym2 V)} (hC : C ∈ cl) : (portsA C).Nonempty := by
  have hb := card_portsA_bounds (H.noLoops hC) (H.hcl.ne C hC)
  have := two_le_card_nodes (H.noLoops hC) (H.hcl.ne C hC)
  exact card_pos.1 (by omega)

lemma path_eq {C : Finset (Sym2 V)} (hC : C ∈ cl) {v : V} (hv : v ∈ nodes C) {j : ℕ}
    (hj : j < Fintype.card V) :
    (construct cl r).path j v C = r C (srcPort C v, portAssign C (H.portsA_ne hC) j) := by
  show (if h : (portsA C).Nonempty then (if v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V then
    r C (srcPort C v, portAssign C h j) else []) else []) = _
  rw [dif_pos (H.portsA_ne hC), if_pos ⟨hv, hC, hj⟩]

omit H in
lemma path_nil {C : Finset (Sym2 V)} {v : V} {j : ℕ}
    (h : ¬ (v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V)) : (construct cl r).path j v C = [] := by
  show (if h : (portsA C).Nonempty then (if v ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V then
    r C (srcPort C v, portAssign C h j) else []) else []) = _
  split_ifs <;> rfl

omit H in
lemma portAssign_mem {C : Finset (Sym2 V)} (h : (portsA C).Nonempty) {j : ℕ}
    (hj : j < Fintype.card V) : portAssign C h j ∈ portsA C :=
  (portAssign_spec C h).1 j (mem_range.2 hj)

omit H in
lemma mem_aggSet_of_portsA {C : Finset (Sym2 V)} {p : Port V} (hp : p ∈ portsA C) :
    p.1 ∈ aggSet C := (mem_portsA.1 hp).1

lemma aggSet_sub {C : Finset (Sym2 V)} (hC : C ∈ cl) : aggSet C ⊆ nodes C :=
  (aggSet_spec (H.noLoops hC) (H.hcl.ne C hC)).top.1

/-- the host of the aggregator of `C` in overlay `j` -/
lemma aggHost_construct (C : Finset (Sym2 V)) (j : ℕ) :
    aggHost (construct cl r) j C = if h : C ∈ cl ∧ j < Fintype.card V then
      some (portAssign C (H.portsA_ne h.1) j).1 else none := by
  classical
  unfold aggHost
  by_cases h : C ∈ cl ∧ j < Fintype.card V
  · rw [dif_pos h]
    have hwalk : ∀ v ∈ nodes C, IsEdgeWalk ((construct cl r).path j v C) v
        (portAssign C (H.portsA_ne h.1) j).1 := by
      intro v hv
      rw [H.path_eq h.1 hv h.2]
      exact (H.walk C h.1 v hv _ (portAssign_mem _ h.2)).1
    obtain ⟨u, hu⟩ : (nodes C).Nonempty := by
      obtain ⟨e, he⟩ := H.hcl.ne C h.1
      induction e using Sym2.ind with
      | _ a b => exact ⟨a, mem_nodes.2 ⟨_, he, Sym2.mem_mk_left a b⟩⟩
    have hc : (construct cl r).cl = cl := rfl
    have hex : C ∈ (construct cl r).cl ∧ (nodes C).Nonempty ∧ ∃ hv : V, ∀ v ∈ nodes C,
        IsEdgeWalk ((construct cl r).path j v C) v hv := ⟨h.1, ⟨u, hu⟩, _, hwalk⟩
    rw [dif_pos hex]
    congr 1
    exact isEdgeWalk_unique (hex.2.2.choose_spec u hu) (hwalk u hu)
  · rw [dif_neg h, dif_neg]
    rintro ⟨hC, ⟨u, hu⟩, hv, hw⟩
    have hj : ¬ j < Fintype.card V := fun hj => h ⟨hC, hj⟩
    -- all paths are empty, so all nodes of `C` would coincide
    have h2 := two_le_card_nodes (H.noLoops hC) (H.hcl.ne C hC)
    have hall : ∀ v ∈ nodes C, v = hv := by
      intro v hv'
      have := hw v hv'
      rw [path_nil (fun h' => hj h'.2.2)] at this
      exact this
    have : (nodes C).card ≤ 1 := card_le_one.2 (fun a ha b hb => (hall a ha).trans (hall b hb).symm)
    omega

/-! ### The local values -/

lemma clLoc_eq_image (v : V) :
    clLoc cl v = (clustersOf cl v).image (fun C => C.filter (fun e => v ∈ e)) := by
  ext s
  rw [mem_clLoc, mem_image]
  constructor
  · rintro ⟨C, hC, rfl, ⟨e, he⟩⟩
    exact ⟨C, mem_filter.2 ⟨hC, mem_nodes.2 ⟨e, (mem_filter.1 he).1, (mem_filter.1 he).2⟩⟩, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hC, hv⟩ := mem_filter.1 hC
    exact ⟨C, hC, rfl, slice_nonempty hv⟩

lemma slice_injOn (v : V) :
    Set.InjOn (fun C => C.filter (fun e => v ∈ e)) (clustersOf cl v : Set (Finset (Sym2 V))) := by
  intro C hC C' hC' heq
  simp only [clustersOf, coe_filter, Set.mem_ofPred_eq] at hC hC'
  obtain ⟨e, he⟩ := slice_nonempty hC.2
  have he' := he
  simp only at heq
  rw [heq] at he'
  exact eq_of_slice H.hcl hC.1 hC'.1 (mem_filter.1 he).1 (mem_filter.1 he').1

lemma card_clLoc (v : V) : (clLoc cl v).card = (clustersOf cl v).card := by
  rw [H.clLoc_eq_image v, card_image_of_injOn (H.slice_injOn v)]

/-- the route knowledge on the own dummy packets -/
lemma rk_own {C : Finset (Sym2 V)} (_hC : C ∈ cl) {v : V} (hv : v ∈ nodes C) {q : Port V}
    (hq : q ∈ portsA C) (r₂ : Routes V) (ℓ : V) (pr : Option V) :
    oRt (oOf N wexp C ℓ pr r₂ (r C) v) (srcPort C v, q) = r C (srcPort C v, q) := by
  classical
  show (if (srcPort C v, q) ∈ portsDemand C ∧ OnWalk (r C (srcPort C v, q)) (srcPort C v, q).1.1 v
    then r C (srcPort C v, q) else []) = _
  rw [if_pos]
  refine ⟨?_, Or.inl (srcPort_fst C v).symm⟩
  unfold portsDemand
  exact Multiset.mem_map.2 ⟨(v, q), mem_val.mpr (mem_product.2 ⟨hv, hq⟩), rfl⟩

variable {P : Proto V} {v : V} {inp : Agent V → Option Mem} {cp : Finset (Sym2 V) → P.S}
  {o : Finset (Sym2 V) → PipeOut V}


lemma pathLen_eq (hN : NodeH N wexp cl r P v inp cp o) {C : Finset (Sym2 V)} (hC : C ∈ cl)
    (hv : v ∈ nodes C) {j : ℕ} (hj : j < Fintype.card V) :
    pathLenL v (C.filter (fun e => v ∈ e)) (cOut P v (cp (C.filter (fun e => v ∈ e)))) j =
      ((construct cl r).path j v C).length := by
  rw [hN.cp C hC hv]
  obtain ⟨ℓ, pr, r₂, ho⟩ := hN.o C hC hv
  simp only [pathLenL]
  rw [ho, ← srcPort_local]
  have hpa : oPa (oOf N wexp C ℓ pr r₂ (r C) v) = portsA C := rfl
  rw [hpa, ← portAssign_local (H.portsA_ne hC), H.rk_own hC hv (portAssign_mem _ hj),
    H.path_eq hC hv hj]

/-- **The local values** of a node. -/
lemma valE_eq (hN : NodeH N wexp cl r P v inp cp o) :
    valE P ((baseInst N).ctx v) inp cp =
      ((range (Fintype.card V)).sup (fun j => cl.sup (fun C => ((construct cl r).path j v C).length)),
        (clustersOf cl v).card) := by
  unfold valE
  have hme : ((baseInst N).ctx v).me = v := rfl
  rw [hme, hN.sl, H.card_clLoc]
  congr 1
  refine Finset.sup_congr rfl (fun j hj => ?_)
  rw [H.clLoc_eq_image, sup_image]
  apply le_antisymm
  · refine Finset.sup_le (fun C hC => ?_)
    obtain ⟨hC, hv⟩ := mem_filter.1 hC
    simp only [Function.comp_apply]
    rw [H.pathLen_eq hN hC hv (mem_range.1 hj)]
    exact le_sup (f := fun C => ((construct cl r).path j v C).length) hC
  · refine Finset.sup_le (fun C hC => ?_)
    by_cases hv : v ∈ nodes C
    · have hC' : C ∈ clustersOf cl v := mem_filter.2 ⟨hC, hv⟩
      refine le_trans (le_of_eq ?_) (le_sup (f := (fun s => pathLenL v s (cOut P v (cp s)) j) ∘
        (fun C => C.filter (fun e => v ∈ e))) hC')
      simp only [Function.comp_apply]
      rw [H.pathLen_eq hN hC hv (mem_range.1 hj)]
    · rw [path_nil (fun h' => hv h'.1)]; exact Nat.zero_le _

lemma valE_bound (hN : NodeH N wexp cl r P v inp cp o) :
    (valE P ((baseInst N).ctx v) inp cp).1 ≤ Fintype.card V ^ Lb ∧
      (valE P ((baseInst N).ctx v) inp cp).2 ≤ Fintype.card V := by
  rw [H.valE_eq hN]
  dsimp only
  refine ⟨Finset.sup_le (fun j hj => Finset.sup_le (fun C hC => ?_)), ?_⟩
  · by_cases hv : v ∈ nodes C
    · rw [H.path_eq hC hv (mem_range.1 hj)]
      exact (H.walk C hC v hv _ (portAssign_mem _ (mem_range.1 hj))).2.2
    · rw [path_nil (fun h' => hv h'.1)]; exact Nat.zero_le _
  · rw [← H.card_clLoc]; exact card_clLoc_le H.hcl v

omit H in
/-- the global maximum of the local path lengths is the dilation -/
lemma dil_construct :
    univ.sup (fun v => (range (Fintype.card V)).sup
      (fun j => cl.sup (fun C => ((construct cl r).path j v C).length))) = (construct cl r).dil := by
  unfold Overlays.dil
  exact Finset.sup_comm _ _ _

/-! ### The views of the hosted aggregators -/

lemma topoL_eq (hN : NodeH N wexp cl r P v inp cp o) {C : Finset (Sym2 V)} (hC : C ∈ cl)
    (hv : v ∈ nodes C) (ha : v ∈ aggSet C) : topoL (o C) = C := by
  classical
  obtain ⟨ℓ, pr, r₂, ho⟩ := hN.o C hC hv
  rw [ho]
  have hrcv : oRcv (oOf N wexp C ℓ pr r₂ (r C) v) = (pl2 N wexp C).filter (fun x => x.1.2.1 = v) :=
    rfl
  unfold topoL
  rw [hrcv]
  ext e
  rw [Multiset.mem_toFinset, Multiset.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxe⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_filter hx)
    simp only [topoPay, hdE, Option.some.injEq] at hxe
    rw [← hxe]
    exact (mem_portsAt.1 (mem_allPorts.1 (mem_product.1 (mem_val.mp hy)).1).2).2.1
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
    have hp : (a, s(a, b)) ∈ allPorts C :=
      mem_allPorts.2 ⟨mem_nodes.2 ⟨_, he, Sym2.mem_mk_left a b⟩,
        mem_portsAt.2 ⟨rfl, he, Sym2.mem_mk_left a b⟩⟩
    have hd := (dstAssign_spec (portsAt_nonempty hv)).1 _ hp
    refine ⟨((srcAssign C a ((a, s(a, b)), v), dstAssign C v (a, s(a, b))),
      topoPay (Fintype.card V) wexp (N.w s(a, b)) s(a, b)), ?_, rfl⟩
    refine Multiset.mem_filter.2 ⟨Multiset.mem_map.2 ⟨((a, s(a, b)), v),
      mem_val.mpr (mem_product.2 ⟨hp, ha⟩), rfl⟩, ?_⟩
    exact (mem_portsAt.1 hd).1

lemma wL_eq (hN : NodeH N wexp cl r P v inp cp o) {C : Finset (Sym2 V)} (hC : C ∈ cl)
    (hv : v ∈ nodes C) (ha : v ∈ aggSet C) {e : Sym2 V} (he : e ∈ C) :
    wL wexp (o C) e = N.w e := by
  classical
  have hex : ∃ x ∈ oRcv (o C), hdE x.2 = some e := by
    have := H.topoL_eq hN hC hv ha
    rw [← this] at he
    unfold topoL at he
    rw [Multiset.mem_toFinset, Multiset.mem_filterMap] at he
    exact he
  unfold wL
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  generalize hex.choose = x at hspec ⊢
  obtain ⟨hx, hxe⟩ := hspec
  obtain ⟨ℓ, pr, r₂, ho⟩ := hN.o C hC hv
  rw [ho] at hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_filter hx)
  simp only [topoPay, hdE, Option.some.injEq] at hxe
  show decD (Fintype.card V + 4) (wexp + 1)
    (fun i => (topoPay (Fintype.card V) wexp (N.w y.1.2) y.1.2).getD i (.num 0)) 1 = N.w e
  rw [hxe]
  have hw : N.w e ≤ Fintype.card V ^ wexp := H.w e (by simpa using H.hcl.sub C hC he)
  refine decD_digits _ _ _ _ _ (fun j hj => ?_) (lt_pow_of_le_pow hw)
  show (Word.edge e :: digW (Fintype.card V + 4) (wexp + 1) (N.w e)).getD (1 + j) (.num 0) = _
  rw [Nat.add_comm 1 j, List.getD_cons_succ, getD_digW _ _ _ hj]

lemma hosts_choose (hN : NodeH N wexp cl r P v inp cp o) {s : Finset (Sym2 V)}
    (hs : s ∈ clLoc cl v) {o' : PipeOut V} (ho' : cOut P v (cp s) = some o') {j : ℕ}
    (hh : hostsL v o' j) :
    o' = o (clOf cl v s) ∧ clOf cl v s ∈ cl ∧ v ∈ aggSet (clOf cl v s) ∧
      topoL o' = clOf cl v s ∧
      (portAssign (clOf cl v s) (H.portsA_ne (clOf_spec H.hcl hs).1) j).1 = v ∧
      j < Fintype.card V := by
  rw [hN.clOf H.hcl hs, Option.some.injEq] at ho'
  subst ho'
  obtain ⟨hC, -⟩ := clOf_spec H.hcl hs
  have hv := mem_nodes_clOf H.hcl hs
  obtain ⟨ℓ, pr, r₂, ho⟩ := hN.o _ hC hv
  obtain ⟨hj, -, hpa⟩ := hh
  have hpa' : (portAssign (clOf cl v s) (H.portsA_ne (clOf_spec H.hcl hs).1) j).1 = v := by
    rw [portAssign_local _ v]
    rw [ho, show oPa (oOf N wexp (clOf cl v s) ℓ pr r₂ (r (clOf cl v s)) v) =
      portsA (clOf cl v s) from rfl] at hpa
    exact hpa
  have ha : v ∈ aggSet (clOf cl v s) := by
    have := mem_aggSet_of_portsA (portAssign_mem (H.portsA_ne (clOf_spec H.hcl hs).1) hj)
    rwa [hpa'] at this
  refine ⟨rfl, hC, ha, ?_, hpa', hj⟩
  exact H.topoL_eq hN hC hv ha

lemma hosts_iff (hN : NodeH N wexp cl r P v inp cp o) (j : ℕ) (C' : Finset (Sym2 V)) :
    (∃ s ∈ mSl inp v, ∃ o', cOut P v (cp s) = some o' ∧ hostsL v o' j ∧ topoL o' = C') ↔
      ∃ h : C' ∈ cl ∧ j < Fintype.card V, (portAssign C' (H.portsA_ne h.1) j).1 = v := by
  rw [hN.sl]
  constructor
  · rintro ⟨s, hs, o', ho', hh, htop⟩
    obtain ⟨-, hC, -, h4, h5, hj⟩ := H.hosts_choose hN hs ho' hh
    rw [h4] at htop
    subst htop
    exact ⟨⟨hC, hj⟩, h5⟩
  · rintro ⟨⟨hC, hj⟩, hpa⟩
    have ha : v ∈ aggSet C' := by rw [← hpa]; exact mem_aggSet_of_portsA (portAssign_mem _ hj)
    have hv : v ∈ nodes C' := H.aggSet_sub hC ha
    obtain ⟨ℓ, pr, r₂, ho⟩ := hN.o C' hC hv
    refine ⟨_, slice_mem_clLoc hC hv, o C', hN.cp C' hC hv, ⟨hj, ?_, ?_⟩, H.topoL_eq hN hC hv ha⟩
    · rw [ho]; exact H.portsA_ne hC
    · rw [ho]; show (portAssignL v (portsA C') j).1 = v
      rw [← portAssign_local (H.portsA_ne hC)]; exact hpa

lemma viewL_eq (hN : NodeH N wexp cl r P v inp cp o) (j : ℕ) :
    viewL wexp P ((baseInst N).ctx v) inp cp j = ioView N (construct cl r) j univ v := by
  classical
  have hme : ((baseInst N).ctx v).me = v := rfl
  funext g
  cases g with
  | inl u =>
    simp only [viewL, ioView, ioHost, mem_univ, ↓reduceIte, Option.some.injEq, hme]
    by_cases hu : u = v
    · subst hu
      rw [if_pos rfl, if_pos rfl]
      simp [ownVw, baseInst]
    · rw [if_neg hu, if_neg hu]
  | inr C' =>
    simp only [viewL, hme]
    have hio : ioView N (construct cl r) j univ v (.inr C') =
        if h : C' ∈ cl ∧ j < Fintype.card V then
          (if (portAssign C' (H.portsA_ne h.1) j).1 = v then some (lview N (.inr C')) else none)
        else none := by
      by_cases h : C' ∈ cl ∧ j < Fintype.card V
      · have ha : aggHost (construct cl r) j C' = some (portAssign C' (H.portsA_ne h.1) j).1 := by
          rw [H.aggHost_construct, dif_pos h]
        simp only [ioView, ioHost, ha, mem_univ, ↓reduceIte, dif_pos h, Option.some.injEq]
      · have ha : aggHost (construct cl r) j C' = none := by
          rw [H.aggHost_construct, dif_neg h]
        simp only [ioView, ioHost, ha, dif_neg h]
        simp
    rw [hio]
    by_cases hex : ∃ s ∈ mSl inp v, ∃ o', cOut P v (cp s) = some o' ∧ hostsL v o' j ∧
        topoL o' = C'
    · rw [dif_pos hex]
      obtain ⟨⟨hC, hj⟩, hpa⟩ := (H.hosts_iff hN j C').1 hex
      rw [dif_pos ⟨hC, hj⟩, if_pos hpa]
      have hspec := hex.choose_spec
      generalize hex.choose = s0 at hspec ⊢
      obtain ⟨hs, o', ho', hh, htop⟩ := hspec
      rw [hN.sl] at hs
      obtain ⟨h1, h2, h3, h4, -, -⟩ := H.hosts_choose hN hs ho' hh
      rw [h4] at htop
      congr 1
      funext e
      simp only [lview]
      split_ifs with he
      · rw [ho']
        simp only
        rw [h1]
        rw [← htop] at he
        exact H.wL_eq hN h2 (H.aggSet_sub h2 h3) h3 he
      · rfl
    · rw [dif_neg hex]
      by_cases h : C' ∈ cl ∧ j < Fintype.card V
      · rw [dif_pos h, if_neg (fun hpa => hex ((H.hosts_iff hN j C').2 ⟨h, hpa⟩))]
      · rw [dif_neg h]

/-! ### The embedded paths -/

omit H in
lemma onWalk_ne {l : List (Sym2 V)} {u v : V} (huv : u ≠ v) : OnWalk l u v ↔ ∃ e ∈ l, v ∈ e := by
  unfold OnWalk
  constructor
  · rintro (h | h)
    · exact absurd h.symm huv
    · exact h
  · exact Or.inr

lemma key_eq {C C' : Finset (Sym2 V)} (hC : C ∈ cl) (hC' : C' ∈ cl) {u : V} (hu : u ∈ nodes C)
    (hu' : u ∈ nodes C') (h : (srcPort C u).2 = (srcPort C' u).2) : C = C' :=
  eq_of_slice H.hcl hC hC' (srcPort_snd_mem hu).1 (h ▸ (srcPort_snd_mem hu').1)

lemma path_local {C : Finset (Sym2 V)} {u : V} {j : ℕ} {e : Sym2 V}
    (he : e ∈ (construct cl r).path j u C) : e ∈ C := by
  by_cases h : u ∈ nodes C ∧ C ∈ cl ∧ j < Fintype.card V
  · rw [H.path_eq h.2.1 h.1 h.2.2] at he
    exact (H.walk C h.2.1 u h.1 _ (portAssign_mem _ h.2.2)).2.1 e he
  · rw [path_nil h] at he; exact absurd he (List.not_mem_nil)

open Classical in
/-- the recorded route of the packet of `u` (key `k`) to the host of overlay `j` -/
lemma oRt_eq (hN : NodeH N wexp cl r P v inp cp o) {C : Finset (Sym2 V)} (hC : C ∈ cl)
    (hv : v ∈ nodes C) (u : V) (k : Sym2 V) {j : ℕ} (hj : j < Fintype.card V) :
    oRt (o C) ((u, k), portAssignL v (oPa (o C)) j) =
      if u ∈ nodes C ∧ (srcPort C u).2 = k ∧ OnWalk ((construct cl r).path j u C) u v then
        (construct cl r).path j u C else [] := by
  classical
  obtain ⟨ℓ, pr, r₂, ho⟩ := hN.o C hC hv
  rw [ho]
  have hpa : oPa (oOf N wexp C ℓ pr r₂ (r C) v) = portsA C := rfl
  rw [hpa, ← portAssign_local (H.portsA_ne hC)]
  show (if ((u, k), portAssign C (H.portsA_ne hC) j) ∈ portsDemand C ∧
    OnWalk (r C ((u, k), portAssign C (H.portsA_ne hC) j)) u v then
      r C ((u, k), portAssign C (H.portsA_ne hC) j) else []) = _
  by_cases hc : u ∈ nodes C ∧ (srcPort C u).2 = k
  · have hsp : srcPort C u = (u, k) := Prod.ext (srcPort_fst C u) hc.2
    have hD : (srcPort C u, portAssign C (H.portsA_ne hC) j) ∈ portsDemand C :=
      Multiset.mem_map.2 ⟨(u, portAssign C (H.portsA_ne hC) j),
        mem_val.mpr (mem_product.2 ⟨hc.1, portAssign_mem (H.portsA_ne hC) hj⟩), rfl⟩
    rw [← hsp, ← H.path_eq hC hc.1 hj]
    by_cases hw : OnWalk ((construct cl r).path j u C) u v
    · rw [if_pos ⟨hD, hw⟩, if_pos ⟨hc.1, hc.2, hw⟩]
    · rw [if_neg (fun h => hw h.2), if_neg (fun h => hw h.2.2)]
  · rw [if_neg, if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
    rintro ⟨hD, -⟩
    obtain ⟨x, hx, hxe⟩ := Multiset.mem_map.1 hD
    obtain ⟨hx1, -⟩ := mem_product.1 (mem_val.mp hx)
    have h1 : srcPort C x.1 = (u, k) := (Prod.ext_iff.1 hxe).1
    have h2 : x.1 = u := by rw [← srcPort_fst C x.1, h1]
    rw [h2] at h1 hx1
    exact hc ⟨hx1, by rw [h1]⟩

lemma embL_eq (hN : NodeH N wexp cl r P v inp cp o) :
    embL P ((baseInst N).ctx v) inp cp = ioEmb (construct cl r) v := by
  classical
  have hme : ((baseInst N).ctx v).me = v := rfl
  funext j u k
  unfold embL ioEmb
  rw [hme]
  have hcl : (construct cl r).cl = cl := rfl
  by_cases hj : j < Fintype.card V
  · rw [if_pos hj]
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      have hiff : (∃ s ∈ mSl inp u, (srcPortL u s).2 = k) ↔
          ∃ C ∈ (construct cl r).cl, u ∈ nodes C ∧ (srcPort C u).2 = k ∧
            OnWalk ((construct cl r).path j u C) u u := by
        rw [hN.sl, hcl]
        constructor
        · rintro ⟨s, hs, hk⟩
          obtain ⟨hC, hsl⟩ := clOf_spec H.hcl hs
          refine ⟨_, hC, mem_nodes_clOf H.hcl hs, ?_, Or.inl rfl⟩
          rw [srcPort_local, hsl]; exact hk
        · rintro ⟨C, hC, hu, hk, -⟩
          exact ⟨_, slice_mem_clLoc hC hu, by rw [← srcPort_local]; exact hk⟩
      by_cases hex : ∃ s ∈ mSl inp u, (srcPortL u s).2 = k
      · rw [dif_pos hex, dif_pos (hiff.1 hex)]
        have hspec := hex.choose_spec
        have hspec' := (hiff.1 hex).choose_spec
        generalize hex.choose = s0 at hspec ⊢
        generalize (hiff.1 hex).choose = C' at hspec' ⊢
        obtain ⟨hs, hk⟩ := hspec
        rw [hN.sl] at hs
        obtain ⟨hC, hsl⟩ := clOf_spec H.hcl hs
        have hu := mem_nodes_clOf H.hcl hs
        rw [hN.clOf H.hcl hs]
        simp only
        obtain ⟨hC', hu', hk', -⟩ := hspec'
        have hsp : srcPortL u s0 = srcPort (clOf cl u s0) u := by
          rw [srcPort_local, hsl]
        have heq : clOf cl u s0 = C' :=
          H.key_eq hC hC' hu hu' (by rw [hk', ← hsp, hk])
        rw [hsp]
        have := H.oRt_eq hN hC hu u (srcPort (clOf cl u s0) u).2 hj
        have hsp2 : ((u, (srcPort (clOf cl u s0) u).2) : Port V) =
            srcPort (clOf cl u s0) u := Prod.ext (srcPort_fst _ u).symm rfl
        rw [hsp2] at this
        rw [this, if_pos ⟨hu, rfl, Or.inl rfl⟩, heq]
      · rw [dif_neg hex, dif_neg (fun h => hex (hiff.2 h))]
    · rw [if_neg huv]
      have hiff : (∃ s ∈ mSl inp v, ∃ o', cOut P v (cp s) = some o' ∧
          oRt o' ((u, k), portAssignL v (oPa o') j) ≠ []) ↔
          ∃ C ∈ (construct cl r).cl, u ∈ nodes C ∧ (srcPort C u).2 = k ∧
            OnWalk ((construct cl r).path j u C) u v := by
        rw [hN.sl, hcl]
        constructor
        · rintro ⟨s, hs, o', ho', hne⟩
          rw [hN.clOf H.hcl hs, Option.some.injEq] at ho'
          subst ho'
          obtain ⟨hC, -⟩ := clOf_spec H.hcl hs
          rw [H.oRt_eq hN hC (mem_nodes_clOf H.hcl hs) u k hj] at hne
          split_ifs at hne with hc
          · exact ⟨_, hC, hc⟩
          · exact absurd rfl hne
        · rintro ⟨C, hC, hu, hk, hw⟩
          obtain ⟨e, he, hve⟩ := (onWalk_ne huv).1 hw
          have hv : v ∈ nodes C := mem_nodes.2 ⟨e, H.path_local he, hve⟩
          refine ⟨_, slice_mem_clLoc hC hv, o C, hN.cp C hC hv, ?_⟩
          rw [H.oRt_eq hN hC hv u k hj, if_pos ⟨hu, hk, hw⟩]
          exact List.ne_nil_of_mem he
      by_cases hex : ∃ s ∈ mSl inp v, ∃ o', cOut P v (cp s) = some o' ∧
          oRt o' ((u, k), portAssignL v (oPa o') j) ≠ []
      · rw [dif_pos hex, dif_pos (hiff.1 hex)]
        have hspec := hex.choose_spec
        have hspec' := (hiff.1 hex).choose_spec
        generalize hex.choose = s0 at hspec ⊢
        generalize (hiff.1 hex).choose = C' at hspec' ⊢
        obtain ⟨hs, o', ho', hne⟩ := hspec
        rw [hN.sl] at hs
        rw [ho']
        simp only
        rw [hN.clOf H.hcl hs, Option.some.injEq] at ho'
        subst ho'
        obtain ⟨hC, -⟩ := clOf_spec H.hcl hs
        rw [H.oRt_eq hN hC (mem_nodes_clOf H.hcl hs) u k hj] at hne ⊢
        split_ifs at hne ⊢ with hc
        · obtain ⟨hC', hu', hk', -⟩ := hspec'
          rw [H.key_eq hC hC' hc.1 hu' (by rw [hc.2.1, hk'])]
        · exact absurd rfl hne
      · rw [dif_neg hex, dif_neg (fun h => hex (hiff.2 h))]
  · rw [if_neg hj]
    have hnil : ∀ C, (construct cl r).path j u C = [] := fun C => path_nil (fun h => hj h.2.2)
    have hiff : (u = v ∧ ∃ s ∈ mSl inp v, (srcPortL v s).2 = k) ↔
        ∃ C ∈ (construct cl r).cl, u ∈ nodes C ∧ (srcPort C u).2 = k ∧
          OnWalk ((construct cl r).path j u C) u v := by
      rw [hN.sl, hcl]
      constructor
      · rintro ⟨rfl, s, hs, hk⟩
        obtain ⟨hC, hsl⟩ := clOf_spec H.hcl hs
        exact ⟨_, hC, mem_nodes_clOf H.hcl hs, by rw [srcPort_local, hsl]; exact hk, Or.inl rfl⟩
      · rintro ⟨C, hC, hu, hk, hw⟩
        rw [hnil, OnWalk] at hw
        have huv : v = u := by
          rcases hw with h | ⟨e, he, -⟩
          · exact h
          · exact absurd he (List.not_mem_nil)
        subst huv
        exact ⟨rfl, _, slice_mem_clLoc hC hu, by rw [← srcPort_local]; exact hk⟩
    by_cases hex : u = v ∧ ∃ s ∈ mSl inp v, (srcPortL v s).2 = k
    · rw [if_pos hex, dif_pos (hiff.1 hex), hnil]
    · rw [if_neg hex, dif_neg (fun h => hex (hiff.2 h))]

/-- **The final output** of a node is its embedding knowledge for `construct cl r`. -/
theorem ekL_eq (hN : NodeH N wexp cl r P v inp cp o) :
    ekL wexp P ((baseInst N).ctx v) inp cp ((construct cl r).dil, (construct cl r).ov) =
      ekAt N (construct cl r) (.inl v) := by
  unfold ekL
  have hme : ((baseInst N).ctx v).me = v := rfl
  rw [funext (H.viewL_eq hN), H.embL_eq hN, hme, hN.sl]
  rfl

end OutH

end EmbC

end APSP.Stoc.Congest
