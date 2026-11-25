import ApspStoc.Congest.Tasks

/-!
# The KT1 model: nodes do not know the set of IDs

In the model of `thm_5_6_congest` (`Model.lean`) a protocol is a `Proto V`, so every node knows the
node set `V`, i.e. the set of all IDs. This file sets up the model without that assumption.

* IDs come from a known universe `U` (a `Fintype`); the node set is an unknown `S : Finset U`, and
  the network is `N : WNet S` (connected, positive weights, on the subtype `↥S`).
* A protocol is a `Proto U`: every node knows the universe `U` and its own ID. The algorithm is
  indexed by `n = |S|`, so `n` is known as well. Nothing else is known about `S`.
* The instance `ktInst S N` (on `U`): the participants are the nodes of `S`, the communication
  graph is the image of the network on `U` (the other IDs are isolated and do not take part), only
  the physical agents of `S` are simulated, and a node knows only its ID and the weights of its
  incident edges (`ktView`), hence the IDs of its neighbours (KT1).
* `ktOut` translates outputs over `U` back to the node set `S`.

The basic facts: adjacency in the instance (`ktInst_adj`), a node's view is the view `lview` of the
model on `↥S` (`ktView_map`), and a node recognises its neighbours from its view
(`ktView_ne_zero_iff`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {U : Type} [Fintype U] [DecidableEq U]

/-- the weight view of `v` in the KT1 instance: the weights of the edges of `N` at `v` -/
noncomputable def ktView (S : Finset U) (N : WNet S) (v : U) : Sym2 U → ℕ :=
  fun e => ∑ e' ∈ N.G.edgeFinset.filter (fun e' => Sym2.map Subtype.val e' = e ∧ v ∈ e), N.w e'

/-- The KT1 instance on the ID universe `U`: participants `S`, the edges of `N`, physical agents
only, and every node of `S` knows only its ID and its incident edges with their weights. -/
noncomputable def ktInst (S : Finset U) (N : WNet S) : Inst U where
  G := N.G.map (Function.Embedding.subtype (· ∈ S))
  dec := Classical.decRel _
  part v := v ∈ S
  host g := match g with
    | .inl v => if v ∈ S then some v else none
    | .inr _ => none
  ctx v := ⟨v, fun g => if g = .inl v then some (ktView S N v) else none, [], fun _ _ _ => none, ∅⟩
  adj_part u v h := by
    obtain ⟨u', v', -, hu, -⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
    rw [← hu]; exact u'.2
  host_part g v h := by
    cases g with
    | inl u =>
      simp only at h
      split_ifs at h with hu
      cases h; exact hu
    | inr _ => cases h

/-- outputs translated back to the node set `S` -/
def ktOut (S : Finset U) (z : Agent U → (U → ℕ × U)) : S → S → ℕ × S := fun v u =>
  ((z (.inl v.1) u.1).1, if h : (z (.inl v.1) u.1).2 ∈ S then ⟨_, h⟩ else v)

/-! ## Basic facts -/

section Basic

variable {S : Finset U} {N : WNet S}

lemma ktInst_adj {u v : U} :
    (ktInst S N).G.Adj u v ↔ ∃ (hu : u ∈ S) (hv : v ∈ S), N.G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  show (N.G.map (Function.Embedding.subtype (· ∈ S))).Adj u v ↔ _
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u', v', h, rfl, rfl⟩
    exact ⟨u'.2, v'.2, h⟩
  · rintro ⟨hu, hv, h⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, h, rfl, rfl⟩

lemma ktInst_adj_sub {u v : S} : (ktInst S N).G.Adj u.1 v.1 ↔ N.G.Adj u v := by
  rw [ktInst_adj]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨u.2, v.2, h⟩⟩

lemma ktInst_mem_left {u v : U} (h : (ktInst S N).G.Adj u v) : u ∈ S :=
  (ktInst_adj.1 h).1

lemma ktInst_mem_right {u v : U} (h : (ktInst S N).G.Adj u v) : v ∈ S :=
  (ktInst_adj.1 h).2.1

@[simp] lemma ktInst_part (v : U) : (ktInst S N).part v ↔ v ∈ S := Iff.rfl

lemma ktInst_ctx (v : U) : (ktInst S N).ctx v =
    ⟨v, fun g => if g = .inl v then some (ktView S N v) else none, [], fun _ _ _ => none, ∅⟩ := rfl

lemma ktInst_host_inl (v : U) : (ktInst S N).host (.inl v) = if v ∈ S then some v else none := rfl

lemma ktInst_host_inr (C : Finset (Sym2 U)) : (ktInst S N).host (.inr C) = none := rfl

lemma ktInst_host_eq {g : Agent U} {v : U} : (ktInst S N).host g = some v ↔ g = .inl v ∧ v ∈ S := by
  cases g with
  | inl u =>
    rw [ktInst_host_inl]
    split_ifs with hu
    · simp only [Option.some.injEq, Sum.inl.injEq]
      exact ⟨fun h => ⟨h, h ▸ hu⟩, fun h => h.1⟩
    · simp only [Sum.inl.injEq, false_iff, not_and]
      rintro rfl; exact hu
  | inr C => simp [ktInst_host_inr]

/-- The view of a node of `S` is the view `lview` of the model on `↥S`. -/
lemma ktView_map (v : S) (e : Sym2 S) :
    ktView S N v.1 (Sym2.map Subtype.val e) = lview N (.inl v) e := by
  classical
  have hinj : Function.Injective (Sym2.map (Subtype.val : S → U)) :=
    Sym2.map.injective Subtype.val_injective
  have hmem : v.1 ∈ Sym2.map Subtype.val e ↔ v ∈ e := by
    rw [Sym2.mem_map]
    exact ⟨fun ⟨a, ha, hav⟩ => (Subtype.val_injective hav) ▸ ha, fun h => ⟨v, h, rfl⟩⟩
  unfold ktView
  simp only [lview]
  by_cases h : e ∈ N.G.edgeFinset ∧ v ∈ e
  · rw [ite_eq_left h]
    have : N.G.edgeFinset.filter (fun e' => Sym2.map Subtype.val e' = Sym2.map Subtype.val e ∧
        v.1 ∈ Sym2.map Subtype.val e) = {e} := by
      ext e'
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨-, h1, -⟩; exact hinj h1
      · rintro rfl; exact ⟨h.1, rfl, hmem.2 h.2⟩
    rw [this, sum_singleton]
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro e' he'
    simp only [mem_filter] at he'
    exact absurd ⟨hinj he'.2.1 ▸ he'.1, hmem.1 he'.2.2⟩ h

/-- A node recognises its neighbours from its view (weights are positive). -/
lemma ktView_ne_zero_iff (u v : U) : ktView S N u s(u, v) ≠ 0 ↔ (ktInst S N).G.Adj u v := by
  classical
  rw [ktInst_adj]
  constructor
  · intro h
    obtain ⟨e', he', -⟩ := exists_ne_zero_of_sum_ne_zero h
    simp only [mem_filter] at he'
    obtain ⟨he1, he2, -⟩ := he'
    induction e' using Sym2.ind with
    | _ a b =>
      rw [Sym2.map_mk, Sym2.eq_iff] at he2
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he1
      rcases he2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.2, b.2, he1⟩
      · exact ⟨b.2, a.2, he1.symm⟩
  · rintro ⟨hu, hv, h⟩
    have := ktView_map (N := N) ⟨u, hu⟩ s(⟨u, hu⟩, ⟨v, hv⟩)
    rw [Sym2.map_mk] at this
    rw [this]
    simp only [lview]
    rw [ite_eq_left ⟨by simpa using h, Sym2.mem_mk_left _ _⟩]
    have := N.wpos _ ((SimpleGraph.mem_edgeSet N.G).2 h)
    omega

end Basic

end APSP.Stoc.Congest
