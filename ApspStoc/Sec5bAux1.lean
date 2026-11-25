import ApspStoc.Statements

/-!
# Theorem 5.5, auxiliary file 1: graph and arithmetic lemmas

Distances from a virtual source (`subDist`): attainment, triangle inequality, the Bellman
equation, a potential (lower-bound) lemma and strong induction on the distance; connected
components of an induced subgraph; the bound `dist ≤ (n-1)·W`; the window counting of the
participation argument; the per-node decomposition of `ρ^S`; minimum selection.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Walk lengths -/

section Walks
variable (N : WNet V)

@[simp] lemma wlen_nil (u : V) : N.wlen (SimpleGraph.Walk.nil : N.G.Walk u u) = 0 := by
  simp [WNet.wlen]

@[simp] lemma wlen_cons {u u' v : V} (h : N.G.Adj u u') (p : N.G.Walk u' v) :
    N.wlen (SimpleGraph.Walk.cons h p) = N.w s(u, u') + N.wlen p := by
  simp [WNet.wlen]

lemma wlen_concat {u v x : V} (p : N.G.Walk u v) (h : N.G.Adj v x) :
    N.wlen (p.concat h) = N.wlen p + N.w s(v, x) := by
  simp [WNet.wlen, SimpleGraph.Walk.edges_concat]

/-- The last edge of a walk (or the walk is closed at its start). -/
lemma walk_last {u v : V} (q : N.G.Walk u v) :
    u = v ∨ ∃ y, N.G.Adj y v ∧ ∃ q' : N.G.Walk u y, (∀ x ∈ q'.support, x ∈ q.support) ∧
      N.wlen q' + N.w s(y, v) ≤ N.wlen q := by
  induction q with
  | nil => exact Or.inl rfl
  | @cons a b c h p ih =>
    right
    rcases ih with hbc | ⟨y, hy, q', hsup, hlen⟩
    · subst hbc
      refine ⟨a, h, SimpleGraph.Walk.nil, fun x hx => ?_, ?_⟩
      · simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
        simp [hx]
      · simp
    · refine ⟨y, hy, SimpleGraph.Walk.cons h q', fun x hx => ?_, ?_⟩
      · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (hsup x hx)
      · simp only [wlen_cons]; omega

lemma wdist_le_adj (s : V) {y x : V} (h : N.G.Adj y x) :
    N.wdist s x ≤ N.wdist s y + N.w s(y, x) := by
  obtain ⟨q, hq⟩ := N.exists_walk_wdist s y
  have := N.wdist_le (q.concat h)
  rw [wlen_concat, hq] at this; exact this

lemma wdist_self (s : V) : N.wdist s s = 0 := by
  have := N.wdist_le (SimpleGraph.Walk.nil : N.G.Walk s s)
  simp at this; exact this

/-- Shortest-path distances are at most `(n-1)·W`. -/
lemma wdist_add_le (s v : V) {W : ℕ} (hW : ∀ e ∈ N.G.edgeSet, N.w e ≤ W) :
    N.wdist s v + W ≤ Fintype.card V * W := by
  obtain ⟨q⟩ := N.conn.preconnected s v
  have hp := q.bypass_isPath
  have hlt := hp.length_lt
  have h1 : N.wlen q.bypass ≤ q.bypass.length * W := by
    unfold WNet.wlen
    rw [← SimpleGraph.Walk.length_edges]
    have := List.sum_le_card_nsmul (q.bypass.edges.map N.w) W
      (fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx; exact hW e (q.bypass.edges_subset_edgeSet he))
    simpa using this
  have h2 := N.wdist_le q.bypass
  have h3 : (q.bypass.length + 1) * W ≤ Fintype.card V * W := Nat.mul_le_mul_right _ hlt
  nlinarith

end Walks

/-! ## Distances from a virtual source -/

section SubDist
variable (N : WNet V)

lemma subDist_le_walk {S : Finset V} {w0 : V → Option (ℕ × V)} {u v : V} (hu : u ∈ S) {c : ℕ}
    {p : V} (hw : w0 u = some (c, p)) (q : N.G.Walk u v) (hq : ∀ x ∈ q.support, x ∈ S) :
    subDist N S w0 v ≤ ((c + N.wlen q : ℕ) : ℕ∞) :=
  sInf_le ⟨u, hu, c, p, hw, q, hq, rfl⟩

lemma subDist_le_virt {S : Finset V} {w0 : V → Option (ℕ × V)} {v : V} (hv : v ∈ S) {c : ℕ}
    {p : V} (hw : w0 v = some (c, p)) : subDist N S w0 v ≤ c := by
  have := subDist_le_walk N hv hw SimpleGraph.Walk.nil (by simp [hv])
  simpa using this

lemma subDist_attained {S : Finset V} {w0 : V → Option (ℕ × V)} {v : V}
    (hD : subDist N S w0 v ≠ ⊤) : ∃ u ∈ S, ∃ c p, w0 u = some (c, p) ∧
      ∃ q : N.G.Walk u v, (∀ x ∈ q.support, x ∈ S) ∧ subDist N S w0 v = ((c + N.wlen q : ℕ) : ℕ∞) := by
  have hne : {d : ℕ∞ | ∃ u ∈ S, ∃ c p, w0 u = some (c, p) ∧
      ∃ q : N.G.Walk u v, (∀ x ∈ q.support, x ∈ S) ∧ d = ((c + N.wlen q : ℕ) : ℕ∞)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hD; unfold subDist; rw [h, sInf_empty]
  exact csInf_mem hne

/-- Triangle inequality along an edge of `G[S]`. -/
lemma subDist_le_adj {S : Finset V} {w0 : V → Option (ℕ × V)} {u v : V} (hv : v ∈ S)
    (h : N.G.Adj u v) : subDist N S w0 v ≤ subDist N S w0 u + N.w s(u, v) := by
  by_cases hD : subDist N S w0 u = ⊤
  · rw [hD]; simp
  obtain ⟨u0, hu0, c, p, hw, q, hq, hDe⟩ := subDist_attained N hD
  have := subDist_le_walk N hu0 hw (q.concat h) (by
    intro x hx
    rw [SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hq x hx
    · exact hv)
  rw [wlen_concat] at this
  rw [hDe]; push_cast at this ⊢
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The Bellman equation: a reachable node is reached by its virtual edge or through a
neighbour. -/
lemma subDist_bellman {S : Finset V} {w0 : V → Option (ℕ × V)} {v : V} (hv : v ∈ S)
    (hD : subDist N S w0 v ≠ ⊤) :
    (∃ c p, w0 v = some (c, p) ∧ subDist N S w0 v = c) ∨
    ∃ y ∈ S, N.G.Adj y v ∧ subDist N S w0 v = subDist N S w0 y + N.w s(y, v) := by
  obtain ⟨u, hu, c, p, hw, q, hq, hDe⟩ := subDist_attained N hD
  rcases walk_last N q with huv | ⟨y, hy, q', hsup, hlen⟩
  · subst huv
    left
    refine ⟨c, p, hw, le_antisymm (subDist_le_virt N hu hw) ?_⟩
    rw [hDe]; exact_mod_cast Nat.le_add_right _ _
  · right
    have hyS : y ∈ S := hq y (hsup y (SimpleGraph.Walk.end_mem_support q'))
    refine ⟨y, hyS, hy, le_antisymm (subDist_le_adj N hv hy) ?_⟩
    have h1 := subDist_le_walk N hu hw q' (fun x hx => hq x (hsup x hx))
    rw [hDe]
    calc subDist N S w0 y + (N.w s(y, v) : ℕ∞) ≤ ((c + N.wlen q' : ℕ) : ℕ∞) + N.w s(y, v) :=
          add_le_add h1 le_rfl
      _ ≤ ((c + N.wlen q : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add]; exact_mod_cast (by omega)

/-- Potential lemma: a function that is a lower bound at the virtual edges (up to `b`) and
satisfies the triangle inequality along edges of `G[K]` is a lower bound for the distances. -/
lemma le_subDist_of_pot {K : Finset V} {w0 : V → Option (ℕ × V)} (φ : V → ℕ∞) (b : ℕ)
    (hv : ∀ u ∈ K, ∀ c p, w0 u = some (c, p) → φ u ≤ c + b)
    (he : ∀ y ∈ K, ∀ x ∈ K, N.G.Adj y x → φ x ≤ φ y + N.w s(y, x)) :
    ∀ x ∈ K, φ x ≤ subDist N K w0 x + b := by
  intro x hx
  by_cases hD : subDist N K w0 x = ⊤
  · rw [hD]; simp
  obtain ⟨u, hu, c, p, hw, q, hq, hDe⟩ := subDist_attained N hD
  have hwalk : ∀ {a z : V} (r : N.G.Walk a z), (∀ x ∈ r.support, x ∈ K) →
      φ z ≤ φ a + N.wlen r := by
    intro a z r
    induction r with
    | nil => intro _; simp
    | @cons a b c h p ih =>
      intro hr
      have ha : a ∈ K := hr a (by simp)
      have hb : b ∈ K := hr b (by simp)
      have h1 := ih (fun x hx => hr x (by simp [hx]))
      have h2 := he a ha b hb h
      rw [wlen_cons]; push_cast
      calc φ c ≤ φ b + N.wlen p := h1
        _ ≤ φ a + N.w s(a, b) + N.wlen p := add_le_add h2 le_rfl
        _ = _ := by ring
  have h1 := hwalk q hq
  have h2 := hv u hu c p hw
  rw [hDe]; push_cast
  calc φ x ≤ φ u + N.wlen q := h1
    _ ≤ c + b + N.wlen q := add_le_add h2 le_rfl
    _ = _ := by ring

/-- Distances in a subset are at least the distances in the superset. -/
lemma subDist_mono {S K : Finset V} (hKS : K ⊆ S) (w0 : V → Option (ℕ × V)) :
    ∀ x ∈ K, subDist N S w0 x ≤ subDist N K w0 x := by
  have := le_subDist_of_pot N (K := K) (w0 := w0) (subDist N S w0) 0
    (fun u hu c p hw => by simpa using subDist_le_virt N (hKS hu) hw)
    (fun y _ x hx h => subDist_le_adj N (hKS hx) h)
  intro x hx; simpa using this x hx

/-- Strong induction on the (finite) distance. -/
lemma subDist_induction {S : Finset V} {w0 : V → Option (ℕ × V)} (P : V → Prop)
    (h : ∀ v ∈ S, subDist N S w0 v ≠ ⊤ → (∀ y ∈ S, subDist N S w0 y < subDist N S w0 v → P y) →
      P v) : ∀ v ∈ S, subDist N S w0 v ≠ ⊤ → P v := by
  suffices H : ∀ d : ℕ∞, ∀ v ∈ S, subDist N S w0 v = d → d ≠ ⊤ → P v by
    intro v hv hfin; exact H _ v hv rfl hfin
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro v hv hd hfin
    subst hd
    exact h v hv hfin (fun y hy hlt => ih _ hlt y hy rfl (ne_top_of_lt hlt))

/-- At the top level (`S = V`, one virtual edge of weight `0` at `s`), `subDist` is the
distance from `s`. -/
lemma subDist_top (s v : V) :
    subDist N univ (fun u => if u = s then some (0, s) else none) v = N.wdist s v := by
  apply le_antisymm
  · obtain ⟨q, hq⟩ := N.exists_walk_wdist s v
    have := subDist_le_walk N (S := univ) (w0 := fun u => if u = s then some (0, s) else none)
      (mem_univ s) (c := 0) (p := s) (by simp) q (fun x _ => mem_univ x)
    rw [hq] at this; simpa using this
  · have := le_subDist_of_pot N (K := univ) (w0 := fun u => if u = s then some (0, s) else none)
      (fun x => (N.wdist s x : ℕ∞)) 0
      (fun u _ c p hw => by
        by_cases hus : u = s
        · subst hus; simp [wdist_self]
        · simp [hus] at hw)
      (fun y _ x _ h => by exact_mod_cast wdist_le_adj N s h)
    simpa using this v (mem_univ v)

end SubDist

/-! ## Connected components of an induced subgraph -/

section Comps
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma mem_inducedEdges {T : Finset V} {a b : V} :
    s(a, b) ∈ inducedEdges G T ↔ G.Adj a b ∧ a ∈ T ∧ b ∈ T := by
  unfold inducedEdges
  rw [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨h, h2⟩; exact ⟨h, h2 a (Sym2.mem_mk_left a b), h2 b (Sym2.mem_mk_right a b)⟩
  · rintro ⟨h, ha, hb⟩
    refine ⟨h, fun x hx => ?_⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> assumption

lemma EReach.symm {F : Finset (Sym2 V)} {a b : V} (h : EReach F a b) : EReach F b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine Relation.ReflTransGen.head ?_ ih
    rw [Sym2.eq_swap]; exact hbc

/-- the component of `v` in `G[T]` -/
noncomputable def compOf (T : Finset V) (v : V) : Finset V := by
  classical exact T.filter (fun u => EReach (inducedEdges G T) u v)

lemma mem_compOf {T : Finset V} {v u : V} :
    u ∈ compOf G T v ↔ u ∈ T ∧ EReach (inducedEdges G T) u v := by
  classical
  simp only [compOf, mem_filter]

lemma mem_comps {T K : Finset V} : K ∈ comps G T ↔ ∃ v ∈ T, compOf G T v = K := by
  unfold comps compOf; rw [mem_image]

lemma comps_sub {T K : Finset V} (hK : K ∈ comps G T) : K ⊆ T := by
  obtain ⟨v, _, rfl⟩ := (mem_comps G).1 hK
  intro u hu; exact ((mem_compOf G).1 hu).1

lemma self_mem_compOf {T : Finset V} {v : V} (hv : v ∈ T) : v ∈ compOf G T v :=
  (mem_compOf G).2 ⟨hv, Relation.ReflTransGen.refl⟩

lemma compOf_mem_comps {T : Finset V} {v : V} (hv : v ∈ T) : compOf G T v ∈ comps G T :=
  (mem_comps G).2 ⟨v, hv, rfl⟩

lemma comps_adj {T K : Finset V} (hK : K ∈ comps G T) {v y : V} (hv : v ∈ K) (hy : y ∈ T)
    (h : G.Adj y v) : y ∈ K := by
  obtain ⟨u, _, rfl⟩ := (mem_comps G).1 hK
  obtain ⟨hvT, hvu⟩ := (mem_compOf G).1 hv
  refine (mem_compOf G).2 ⟨hy, Relation.ReflTransGen.head ?_ hvu⟩
  exact (mem_inducedEdges G).2 ⟨h, hy, hvT⟩

lemma compOf_eq {T : Finset V} {u v : V} (hu : u ∈ compOf G T v) : compOf G T u = compOf G T v := by
  have huv := ((mem_compOf G).1 hu).2
  ext x; rw [mem_compOf, mem_compOf]
  constructor
  · rintro ⟨hx, h⟩; exact ⟨hx, h.trans huv⟩
  · rintro ⟨hx, h⟩; exact ⟨hx, h.trans (EReach.symm huv)⟩

lemma comps_eq_of_mem {T K : Finset V} (hK : K ∈ comps G T) {v : V} (hv : v ∈ K) :
    compOf G T v = K := by
  obtain ⟨u, _, rfl⟩ := (mem_comps G).1 hK
  exact compOf_eq G hv

lemma comps_disj {T K K' : Finset V} (hK : K ∈ comps G T) (hK' : K' ∈ comps G T) (hne : K ≠ K') :
    Disjoint K K' := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact hne ((comps_eq_of_mem G hK hv).symm.trans (comps_eq_of_mem G hK' hv'))

/-- the components partition `T` -/
lemma sum_comps {β : Type*} [AddCommMonoid β] (T : Finset V) (f : V → β) :
    ∑ K ∈ comps G T, ∑ v ∈ K, f v = ∑ v ∈ T, f v := by
  rw [← sum_biUnion (fun K hK K' hK' hne => comps_disj G hK hK' hne)]
  congr 1
  ext v; rw [mem_biUnion]
  constructor
  · rintro ⟨K, hK, hv⟩; exact comps_sub G hK hv
  · intro hv; exact ⟨_, compOf_mem_comps G hv, self_mem_compOf G hv⟩

lemma ereach_compOf {T : Finset V} {a v : V} (ha : a ∈ T) (h : EReach (inducedEdges G T) a v) :
    EReach (inducedEdges G (compOf G T v)) a v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a c hac hcv ih =>
    have hac' := (mem_inducedEdges G).1 hac
    refine Relation.ReflTransGen.head ?_ (ih hac'.2.2)
    refine (mem_inducedEdges G).2 ⟨hac'.1, ?_, ?_⟩
    · exact (mem_compOf G).2 ⟨ha, Relation.ReflTransGen.head hac hcv⟩
    · exact (mem_compOf G).2 ⟨hac'.2.2, hcv⟩

lemma comps_conn {T K : Finset V} (hK : K ∈ comps G T) : ConnSet G K := by
  obtain ⟨v, hv, rfl⟩ := (mem_comps G).1 hK
  refine ⟨⟨v, self_mem_compOf G hv⟩, fun a ha b hb => ?_⟩
  have ha' := (mem_compOf G).1 ha
  have hb' := (mem_compOf G).1 hb
  exact (ereach_compOf G ha'.1 ha'.2).trans (EReach.symm (ereach_compOf G hb'.1 hb'.2))

lemma comps_nonempty {T K : Finset V} (hK : K ∈ comps G T) : K.Nonempty :=
  (comps_conn G hK).1

end Comps

/-! ## Window counting (participation argument) -/

/-- At most four multiples `a` of `δ` satisfy `a ≤ x ≤ a + 3δ`. -/
lemma card_offsets_le (δ x : ℕ) (hδ : 0 < δ) :
    ((range (x + 1)).filter (fun a => δ ∣ a ∧ x ≤ a + 3 * δ)).card ≤ 4 := by
  have hmaps : ∀ a ∈ (range (x + 1)).filter (fun a => δ ∣ a ∧ x ≤ a + 3 * δ),
      a / δ ∈ Icc (x / δ - 3) (x / δ) := by
    intro a ha
    rw [mem_filter, mem_range] at ha
    rw [mem_Icc]
    constructor
    · have h1 : x / δ ≤ a / δ + 3 := by
        have h0 : x / δ ≤ (a + δ * 3) / δ := Nat.div_le_div_right (by linarith [ha.2.2])
        rwa [Nat.add_mul_div_left _ _ hδ] at h0
      generalize a / δ = t at h1 ⊢
      generalize x / δ = u at h1 ⊢
      omega
    · exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun a => a / δ)
      ((range (x + 1)).filter (fun a => δ ∣ a ∧ x ≤ a + 3 * δ)) := by
    intro a ha a' ha' h
    simp only [coe_filter, Set.mem_ofPred_eq] at ha ha'
    simp only at h
    rw [← Nat.div_mul_cancel ha.2.1, ← Nat.div_mul_cancel ha'.2.1, h]
  refine (card_le_card_of_injOn _ hmaps hinj).trans ?_
  rw [Nat.card_Icc]; omega

/-- `Nw x k a`: the number of pairs (height `k' ≤ k`, offset `a'` in `[a, a + 2^k)`, multiple of
`2^k'`) whose window `[a', a' + 3·2^k']` contains `x`. -/
def Nw (x k a : ℕ) : ℕ :=
  ∑ k' ∈ range (k + 1), ((Ico a (a + 2 ^ k)).filter
    (fun a' => 2 ^ k' ∣ a' ∧ a' ≤ x ∧ x ≤ a' + 3 * 2 ^ k')).card

lemma one_le_window {k a x : ℕ} (hd : 2 ^ k ∣ a) (h1 : a ≤ x) (h2 : x ≤ a + 3 * 2 ^ k) :
    1 ≤ ((Ico a (a + 2 ^ k)).filter
      (fun a' => 2 ^ k ∣ a' ∧ a' ≤ x ∧ x ≤ a' + 3 * 2 ^ k)).card := by
  apply card_pos.2
  refine ⟨a, mem_filter.2 ⟨mem_Ico.2 ⟨le_rfl, ?_⟩, hd, h1, h2⟩⟩
  have := Nat.one_le_two_pow (n := k); omega

lemma one_le_Nw {k a x : ℕ} (hd : 2 ^ k ∣ a) (h1 : a ≤ x) (h2 : x ≤ a + 3 * 2 ^ k) :
    1 ≤ Nw x k a := by
  unfold Nw
  rw [sum_range_succ]
  have := one_le_window hd h1 h2
  omega

lemma Nw_succ {k a x : ℕ} (hd : 2 ^ (k + 1) ∣ a) (h1 : a ≤ x) (h2 : x ≤ a + 3 * 2 ^ (k + 1)) :
    1 + Nw x k a + Nw x k (a + 2 ^ k) ≤ Nw x (k + 1) a := by
  unfold Nw
  rw [sum_range_succ (n := k + 1)]
  have hlast := one_le_window hd h1 h2
  have hsplit : ∀ k' ∈ range (k + 1),
      ((Ico a (a + 2 ^ (k + 1))).filter
        (fun a' => 2 ^ k' ∣ a' ∧ a' ≤ x ∧ x ≤ a' + 3 * 2 ^ k')).card =
      ((Ico a (a + 2 ^ k)).filter
        (fun a' => 2 ^ k' ∣ a' ∧ a' ≤ x ∧ x ≤ a' + 3 * 2 ^ k')).card +
      ((Ico (a + 2 ^ k) (a + 2 ^ k + 2 ^ k)).filter
        (fun a' => 2 ^ k' ∣ a' ∧ a' ≤ x ∧ x ≤ a' + 3 * 2 ^ k')).card := by
    intro k' _
    rw [← card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)),
      ← filter_union, Ico_union_Ico_eq_Ico (by omega) (by omega)]
    congr 2; rw [pow_succ]; ring
  rw [sum_congr rfl hsplit, sum_add_distrib]
  omega

lemma Nw_le (x k a : ℕ) : Nw x k a ≤ 4 * (k + 1) := by
  unfold Nw
  calc _ ≤ ∑ k' ∈ range (k + 1), 4 := by
        apply sum_le_sum; intro k' _
        refine le_trans (card_le_card ?_) (card_offsets_le (2 ^ k') x (by positivity))
        intro a' ha'
        rw [mem_filter] at ha' ⊢
        exact ⟨mem_range.2 (by omega), ha'.2.1, ha'.2.2.2⟩
    _ = 4 * (k + 1) := by rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-! ## Per-node decomposition of the edge usage -/

section HG
variable (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)

/-- the usage of edge `e` attributed to node `v`: its incident edge and its aggregator paths -/
def hg (v : V) (e : Sym2 V) : ℕ :=
  (if e ∈ G.edgeFinset ∧ v ∈ e then 1 else 0) + ∑ C ∈ clustersOf E.cl v, (E.path j v C).count e

lemma rho_le_sum_hg (S : Finset V) (e : Sym2 V) : E.rho G j S e ≤ ∑ v ∈ S, hg G E j v e := by
  unfold Overlays.rho Overlays.rhoAgg hg
  rw [sum_add_distrib]
  apply Nat.add_le_add_right
  split_ifs with hc
  · obtain ⟨he, v, hv, hve⟩ := hc
    exact single_le_sum (f := fun v => if e ∈ G.edgeFinset ∧ v ∈ e then 1 else 0)
      (fun _ _ => Nat.zero_le _) hv |>.trans' (by simp [he, hve])
  · exact Nat.zero_le _

lemma sum_hg_le (e : Sym2 V) : ∑ v, hg G E j v e ≤ 2 * E.rho G j univ e := by
  unfold hg
  rw [sum_add_distrib]
  have hh : ∑ v, (if e ∈ G.edgeFinset ∧ v ∈ e then 1 else 0) ≤
      2 * (if e ∈ G.edgeFinset ∧ ∃ v ∈ (univ : Finset V), v ∈ e then 1 else 0) := by
    by_cases he : e ∈ G.edgeFinset
    · have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet (by simpa using he)
      have : ∑ v, (if e ∈ G.edgeFinset ∧ v ∈ e then 1 else 0) = 2 := by
        simp only [he, true_and]
        rw [sum_boole]; exact_mod_cast card_filter_mem_of_not_diag hnd
      rw [this]
      induction e using Sym2.ind with
      | _ a b => rw [if_pos ⟨he, a, mem_univ _, Sym2.mem_mk_left a b⟩]
    · simp [he]
  have hrho : E.rho G j univ e =
      (if e ∈ G.edgeFinset ∧ ∃ v ∈ (univ : Finset V), v ∈ e then 1 else 0) +
        ∑ v, ∑ C ∈ clustersOf E.cl v, (E.path j v C).count e := rfl
  rw [hrho]; omega

end HG

/-! ## Minimum selection -/

/-- An element with minimal first component (`none` for the empty set). -/
noncomputable def bestOf {α : Type} (s : Finset (ℕ × α)) : Option (ℕ × α) :=
  if h : s.Nonempty then some (Classical.choose (s.exists_min_image Prod.fst h)) else none

lemma bestOf_some {α : Type} {s : Finset (ℕ × α)} {q : ℕ × α} (h : bestOf s = some q) :
    q ∈ s ∧ ∀ q' ∈ s, q.1 ≤ q'.1 := by
  unfold bestOf at h
  split_ifs at h with hne
  · cases h
    exact Classical.choose_spec (s.exists_min_image Prod.fst hne)

lemma bestOf_exists {α : Type} {s : Finset (ℕ × α)} {q : ℕ × α} (hq : q ∈ s) :
    ∃ q', bestOf s = some q' := by
  unfold bestOf
  rw [dif_pos ⟨q, hq⟩]; exact ⟨_, rfl⟩

lemma bestOf_none {α : Type} {s : Finset (ℕ × α)} (h : bestOf s = none) : s = ∅ := by
  unfold bestOf at h
  split_ifs at h with hne
  exact not_nonempty_iff_eq_empty.1 hne

end APSP.Stoc
