import ApspStoc.Sec5bAux1

/-!
# Realizability of three auxiliary specifications

* aggregates (`AggOf`) exist for every non-empty multiset;
* rooted spanning forests (`SpanForest`) exist for every loop-free edge set inside `S`;
* exact distances with a shortest-path parent satisfy the `3/2`-approximate SSSP specification
  (`ApproxSpec`).
-/

namespace APSP.Stoc

open APSP Finset

/-- aggregates exist for every non-empty multiset -/
theorem aggOf_exists {M : Type} (op : M → M → M) (s : Multiset M) (hs : s ≠ 0) :
    ∃ a, AggOf op s a := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    by_cases h0 : s = 0
    · subst h0
      exact ⟨a, by simpa using AggOf.single (op := op) a⟩
    · obtain ⟨b, hb⟩ := ih h0
      refine ⟨op a b, ?_⟩
      rw [← Multiset.singleton_add]
      exact AggOf.comb (AggOf.single a) hb

section Forest

lemma EReach.of_edge {V : Type} {F : Finset (Sym2 V)} {a b : V} (h : s(a, b) ∈ F) :
    EReach F a b :=
  Relation.ReflTransGen.single h

/-- `EReach F` implies reachability in the simple graph spanned by `F`. -/
lemma reachable_of_eReach {V : Type} [DecidableEq V] {F : Finset (Sym2 V)} {a b : V}
    (h : EReach F a b) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable a b := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    by_cases hne : b = c
    · subst hne; exact ih
    · refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by simpa using hbc, hne⟩

-- `hloop` is part of the intended interface but not needed for the construction
set_option linter.unusedVariables false in
/-- rooted spanning forests exist -/
theorem spanForest_exists {V : Type} [Fintype V] [DecidableEq V] (S : Finset V)
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ∀ v ∈ e, v ∈ S) (hloop : ∀ e ∈ F, ¬ e.IsDiag) :
    ∃ (par : V → Option V) (root : V → V), SpanForest S F par root := by
  classical
  set H : SimpleGraph V := SimpleGraph.fromEdgeSet (F : Set (Sym2 V)) with hH
  -- canonical representatives: the `equivFin`-minimal element of the class
  have hex : ∀ v, ∃ r, EReach F r v ∧ ∀ r', EReach F r' v →
      Fintype.equivFin V r ≤ Fintype.equivFin V r' := by
    intro v
    obtain ⟨r, hr, hmin⟩ := (univ.filter (fun u => EReach F u v)).exists_min_image
      (Fintype.equivFin V) ⟨v, mem_filter.2 ⟨mem_univ _, Relation.ReflTransGen.refl⟩⟩
    refine ⟨r, (mem_filter.1 hr).2, fun r' hr' => hmin r' (mem_filter.2 ⟨mem_univ _, hr'⟩)⟩
  choose root hroot using hex
  have root_eq : ∀ u v, EReach F u v → root u = root v := by
    intro u v huv
    have h1 : EReach F (root u) v := (hroot u).1.trans huv
    have h2 : EReach F (root v) u := (hroot v).1.trans (EReach.symm huv)
    have a1 := (hroot v).2 _ h1
    have a2 := (hroot u).2 _ h2
    exact (Fintype.equivFin V).injective (le_antisymm a2 a1)
  -- a neighbour closer to the root
  have hpar : ∀ v, ∃ u, v ≠ root v → s(v, u) ∈ F ∧ H.dist u (root v) < H.dist v (root v) := by
    intro v
    by_cases hv : v = root v
    · exact ⟨v, fun h => absurd hv h⟩
    · have hreach : H.Reachable v (root v) :=
        reachable_of_eReach (EReach.symm (hroot v).1)
      obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      generalize root v = r at p hp hv
      cases p with
      | nil => exact absurd rfl hv
      | @cons _ u _ hadj p' =>
        refine ⟨u, fun _ => ⟨?_, ?_⟩⟩
        · rw [hH, SimpleGraph.fromEdgeSet_adj] at hadj
          simpa using hadj.1
        · have := H.dist_le p'
          rw [SimpleGraph.Walk.length_cons] at hp
          omega
  choose pf hpf using hpar
  refine ⟨fun v => if v ∈ S ∧ v ≠ root v then some (pf v) else none, root, ?_⟩
  have hsome : ∀ v u, (if v ∈ S ∧ v ≠ root v then some (pf v) else none) = some u →
      v ∈ S ∧ v ≠ root v ∧ u = pf v := by
    intro v u h
    split_ifs at h with hc
    · exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  have hedge : ∀ v u, (if v ∈ S ∧ v ≠ root v then some (pf v) else none) = some u →
      s(v, u) ∈ F := by
    intro v u h
    obtain ⟨_, hne, rfl⟩ := hsome v u h
    exact (hpf v hne).1
  refine ⟨fun v _ u h => hedge v u h, fun v _ u h => ?_, fun v _ u h => ?_, fun v hv h => ?_,
    ⟨fun v => H.dist v (root v), fun v _ u h => ?_⟩, fun u _ v _ => ?_⟩
  · exact hF _ (hedge v u h) u (Sym2.mem_mk_right v u)
  · exact (root_eq v u (EReach.of_edge (hedge v u h))).symm
  · split_ifs at h with hc
    · by_contra hne; exact hc ⟨hv, Ne.symm hne⟩
  · obtain ⟨_, hne, rfl⟩ := hsome v u h
    have hr := root_eq v (pf v) (EReach.of_edge (hpf v hne).1)
    simp only
    rw [← hr]
    exact (hpf v hne).2
  · constructor
    · intro h
      have h1 : EReach F u (root u) := EReach.symm (hroot u).1
      rw [h] at h1
      exact h1.trans (hroot v).1
    · exact root_eq u v

end Forest

section SSSP

/-- exact distances with a shortest-path parent satisfy the 3/2-approximate SSSP specification -/
theorem approxSpec_realizable {V : Type} [Fintype V] [DecidableEq V] (N : WNet V)
    (S : Finset V) (w0 : V → Option (ℕ × V)) : ∃ y : V → Option (ℕ × V), ApproxSpec N S w0 y := by
  classical
  have key : ∀ v, ∃ p : V, v ∈ S → subDist N S w0 v ≠ ⊤ →
      w0 v = some ((subDist N S w0 v).toNat, p) ∨
      (p ∈ S ∧ N.G.Adj v p ∧ subDist N S w0 v = subDist N S w0 p + N.w s(p, v)) := by
    intro v
    by_cases hv : v ∈ S
    · by_cases hD : subDist N S w0 v = ⊤
      · exact ⟨v, fun _ h => absurd hD h⟩
      · rcases subDist_bellman N hv hD with ⟨c, p, hw, hc⟩ | ⟨p, hp, hadj, hpe⟩
        · refine ⟨p, fun _ _ => Or.inl ?_⟩
          rw [hc, ENat.toNat_natCast]; exact hw
        · exact ⟨p, fun _ _ => Or.inr ⟨hp, hadj.symm, hpe⟩⟩
    · exact ⟨v, fun h => absurd h hv⟩
  choose par hpar using key
  refine ⟨fun v => if v ∈ S ∧ subDist N S w0 v ≠ ⊤ then
    some ((subDist N S w0 v).toNat, par v) else none, ?_⟩
  intro v hv
  refine ⟨?_, ?_⟩
  · simp only
    split_ifs with hc
    · simp only [false_iff]
      exact hc.2
    · simp only [true_iff]
      by_contra hne; exact hc ⟨hv, hne⟩
  · intro d p h
    simp only at h
    split_ifs at h with hc
    obtain ⟨hd, hp⟩ := Prod.mk.inj (Option.some.inj h)
    subst hd hp
    have hcoe : ((subDist N S w0 v).toNat : ℕ∞) = subDist N S w0 v := ENat.natCast_toNat hc.2
    refine ⟨hcoe.ge, ?_, ?_⟩
    · rw [hcoe]
      calc 2 * subDist N S w0 v ≤ 2 * subDist N S w0 v + subDist N S w0 v := le_self_add
        _ = 3 * subDist N S w0 v := by ring
    · rcases hpar v hv hc.2 with hw | ⟨hpS, hadj, hpe⟩
      · exact Or.inr hw
      · left
        have hpD : subDist N S w0 (par v) ≠ ⊤ := by
          intro htop; rw [htop, top_add] at hpe; exact hc.2 hpe
        refine ⟨hpS, hadj, (subDist N S w0 (par v)).toNat, par (par v), ?_, ?_⟩
        · simp only [hpS, ne_eq, hpD, not_false_eq_true, and_self, ite_true]
        · have hpcoe : ((subDist N S w0 (par v)).toNat : ℕ∞) = subDist N S w0 (par v) :=
            ENat.natCast_toNat hpD
          rw [← hcoe, ← hpcoe] at hpe
          exact_mod_cast hpe.symm

end SSSP

end APSP.Stoc
