import ApspStoc.Congest.Tasks

/-!
# Announcements along the embedded aggregator paths (for `perCompR`)

A *hop-synchronised announcement* from a set `Q` of sources: every source `x ∈ Q` sends a packet
along its path `E.path j x C` in every cluster `C` of `x`; in sub-phase `h` every packet crosses
the `h`-th edge of its path. `pk Q h u w` is the set of sources whose packet crosses the directed
edge `(u, w)` in sub-phase `h`: the packets on a directed edge are sent one after another, in the
order of `(pk Q h u w).toList`.

* `vtx l a i`: the `i`-th vertex of the walk `l` from `a`; `walk_getElem`: the `i`-th edge of a
  walk joins its `i`-th and `(i+1)`-th vertices.
* `pk_relay`: a relay `v` computes the packets it forwards in sub-phase `h ≥ 1` from the packets it
  received in sub-phase `h - 1` and the paths through it that it knows (`ioEmb`, keyed by source
  and key edge): the edge over which a packet arrived determines its cluster (clusters are
  edge-disjoint), hence the path, hence the next edge. `pk_zero`: a source knows its own paths.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the other endpoint of an edge -/
noncomputable def pcOth (e : Sym2 V) (a : V) : V := if h : a ∈ e then Sym2.Mem.other h else a

lemma pcOth_mk (a b : V) : pcOth s(a, b) a = b := by
  unfold pcOth
  rw [dif_pos (Sym2.mem_mk_left a b)]
  exact Sym2.congr_right.1 (Sym2.other_spec _)

/-- the `i`-th vertex of the walk `l` starting at `a` -/
noncomputable def vtx : List (Sym2 V) → V → ℕ → V
  | [], a, _ => a
  | _ :: _, a, 0 => a
  | e :: l, a, i + 1 => vtx l (pcOth e a) i

lemma vtx_zero (l : List (Sym2 V)) (a : V) : vtx l a 0 = a := by cases l <;> rfl

lemma vtx_cons_succ (e : Sym2 V) (l : List (Sym2 V)) (a : V) (i : ℕ) :
    vtx (e :: l) a (i + 1) = vtx l (pcOth e a) i := rfl

lemma walk_getElem : ∀ (l : List (Sym2 V)) (a b : V), IsEdgeWalk l a b →
    ∀ i (hi : i < l.length), l[i] = s(vtx l a i, vtx l a (i + 1))
  | [], _, _, _, i, hi => absurd hi (by simp)
  | e :: l, a, b, h, i, hi => by
    obtain ⟨x, he, hw⟩ := h
    cases i with
    | zero =>
      rw [List.getElem_cons_zero, vtx_zero, vtx_cons_succ, vtx_zero, he, pcOth_mk]
    | succ i =>
      rw [List.getElem_cons_succ, vtx_cons_succ, vtx_cons_succ, he, pcOth_mk]
      exact walk_getElem l x b hw i (by simpa using hi)

lemma walk_vtx_mem (l : List (Sym2 V)) (a b : V) (hw : IsEdgeWalk l a b) {i : ℕ}
    (hi : i < l.length) {w : V} : w ∈ l[i] ↔ w = vtx l a i ∨ w = vtx l a (i + 1) := by
  rw [walk_getElem l a b hw i hi, Sym2.mem_iff]

section Emb

variable (E : Overlays V) (j : ℕ)

/-- the sources whose packet crosses the directed edge `(u, w)` in sub-phase `h` -/
noncomputable def pk (Q : Finset V) (h : ℕ) (u w : V) : Finset V := by
  classical exact Q.filter (fun x => ∃ C ∈ clustersOf E.cl x, h < (E.path j x C).length ∧
    vtx (E.path j x C) x h = u ∧ vtx (E.path j x C) x (h + 1) = w)

variable {E j}

lemma mem_pk {Q : Finset V} {h : ℕ} {u w x : V} : x ∈ pk E j Q h u w ↔ x ∈ Q ∧
    ∃ C ∈ clustersOf E.cl x, h < (E.path j x C).length ∧
      vtx (E.path j x C) x h = u ∧ vtx (E.path j x C) x (h + 1) = w := by
  classical
  unfold pk
  simp only [mem_filter]

variable {G : SimpleGraph V} [DecidableRel G.Adj] (hE : EmbValid G E) (hj : j < Fintype.card V)
include hE hj

lemma pc_path_walk {x : V} {C : Finset (Sym2 V)} (hC : C ∈ clustersOf E.cl x) :
    ∃ hv, IsEdgeWalk (E.path j x C) x hv := by
  rw [clustersOf, mem_filter] at hC
  obtain ⟨h, -, hh⟩ := hE.walk j hj C hC.1
  exact ⟨h, hh x hC.2⟩

lemma path_edge {x : V} {C : Finset (Sym2 V)} (hC : C ∈ clustersOf E.cl x) {i : ℕ}
    (hi : i < (E.path j x C).length) :
    (E.path j x C)[i] = s(vtx (E.path j x C) x i, vtx (E.path j x C) x (i + 1)) := by
  obtain ⟨hv, hw⟩ := pc_path_walk hE hj hC
  exact walk_getElem _ _ _ hw i hi

omit hj in
lemma path_edge_mem {x : V} {C : Finset (Sym2 V)} (hC : C ∈ clustersOf E.cl x) {i : ℕ}
    (hi : i < (E.path j x C).length) : (E.path j x C)[i] ∈ C :=
  hE.local_ j x C _ (List.getElem_mem hi)

/-- The edges crossed by packets are edges of `G`. -/
lemma pk_adj {Q : Finset V} {h : ℕ} {u w x : V} (hx : x ∈ pk E j Q h u w) : G.Adj u w := by
  obtain ⟨-, C, hC, hh, hu, hw⟩ := mem_pk.1 hx
  have he := path_edge_mem hE hC hh
  rw [path_edge hE hj hC hh, hu, hw] at he
  have := hE.sub C (mem_filter.1 hC).1 he
  rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this

/-- The endpoints of the edges crossed by packets are in the footprint. -/
lemma pk_fp {Q : Finset V} {h : ℕ} {u w x : V} (hx : x ∈ pk E j Q h u w) :
    u ∈ footprint E j Q ∧ w ∈ footprint E j Q := by
  obtain ⟨hxQ, C, hC, hh, hu, hw⟩ := mem_pk.1 hx
  have he := path_edge hE hj hC hh
  refine ⟨mem_footprint.2 (Or.inr ⟨x, hxQ, C, hC, _, List.getElem_mem hh, ?_⟩),
    mem_footprint.2 (Or.inr ⟨x, hxQ, C, hC, _, List.getElem_mem hh, ?_⟩)⟩
  · rw [he, hu]; exact Sym2.mem_mk_left _ _
  · rw [he, hw]; exact Sym2.mem_mk_right _ _

/-- The packets of distinct clusters of a source cross distinct edges. -/
lemma cluster_unique {x : V} {C C' : Finset (Sym2 V)} (hC : C ∈ clustersOf E.cl x)
    (hC' : C' ∈ clustersOf E.cl x) {i i' : ℕ} (hi : i < (E.path j x C).length)
    (hi' : i' < (E.path j x C').length) (he : (E.path j x C)[i] = (E.path j x C')[i']) :
    C = C' := by
  by_contra hne
  have h1 := path_edge_mem hE hC hi
  have h2 := path_edge_mem hE hC' hi'
  rw [he] at h1
  exact Finset.disjoint_left.1 (hE.disj C (mem_filter.1 hC).1 C' (mem_filter.1 hC').1 hne) h1 h2

/-- A node lies on the paths through it. -/
lemma onWalk_vtx {x : V} {C : Finset (Sym2 V)} (hC : C ∈ clustersOf E.cl x) {i : ℕ}
    (hi : i ≤ (E.path j x C).length) : OnWalk (E.path j x C) x (vtx (E.path j x C) x i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · left; exact vtx_zero _ _
  · right
    refine ⟨_, List.getElem_mem (show i - 1 < (E.path j x C).length by omega), ?_⟩
    rw [path_edge hE hj hC (by omega), show i - 1 + 1 = i by omega]
    exact Sym2.mem_mk_right _ _

lemma emb_path {x v : V} {C : Finset (Sym2 V)} (hC : C ∈ clustersOf E.cl x)
    (hv : OnWalk (E.path j x C) x v) :
    ioEmb E v j x (srcPort C x).2 = some (E.path j x C) :=
  ioEmb_eq_some hE.disj (mem_filter.1 hC).1 (mem_filter.1 hC).2 hv

/-- **Sources** know their own packets. -/
lemma pk_zero (Q : Finset V) (v w : V) (x : V) : x ∈ pk E j Q 0 v w ↔ x = v ∧ v ∈ Q ∧
    ∃ k l e, ioEmb E v j v k = some l ∧ l[0]? = some e ∧ pcOth e v = w := by
  rw [mem_pk]
  constructor
  · rintro ⟨hxQ, C, hC, hh, hu, hw⟩
    rw [vtx_zero] at hu
    subst hu
    refine ⟨rfl, hxQ, (srcPort C x).2, E.path j x C, (E.path j x C)[0], ?_, ?_, ?_⟩
    · exact emb_path hE hj hC (Or.inl rfl)
    · exact List.getElem?_eq_getElem hh
    · rw [path_edge hE hj hC hh, vtx_zero, zero_add, hw, pcOth_mk]
  · rintro ⟨rfl, hxQ, k, l, e, hk, he, hw⟩
    obtain ⟨C, hCl, hxC, -, -, rfl⟩ := ioEmb_spec hk
    have hC : C ∈ clustersOf E.cl x := mem_filter.2 ⟨hCl, hxC⟩
    have hh : 0 < (E.path j x C).length := by
      rcases hl : E.path j x C with _ | ⟨a, l⟩
      · rw [hl] at he; simp at he
      · simp
    refine ⟨hxQ, C, hC, hh, vtx_zero _ _, ?_⟩
    rw [List.getElem?_eq_getElem hh, Option.some.injEq] at he
    rw [← hw, ← he, path_edge hE hj hC hh, vtx_zero, pcOth_mk]

/-- **Relays** compute the packets they forward in sub-phase `h ≥ 1` from those they received in
sub-phase `h - 1`. -/
lemma pk_relay (Q : Finset V) (h : ℕ) (hh : 1 ≤ h) (v w x : V) : x ∈ pk E j Q h v w ↔
    ∃ y, x ∈ pk E j Q (h - 1) y v ∧ ∃ k l e, ioEmb E v j x k = some l ∧
      l[h - 1]? = some s(y, v) ∧ l[h]? = some e ∧ pcOth e v = w := by
  constructor
  · rintro hx
    obtain ⟨hxQ, C, hC, hlen, hu, hw⟩ := mem_pk.1 hx
    refine ⟨vtx (E.path j x C) x (h - 1), mem_pk.2 ⟨hxQ, C, hC, by omega, rfl, ?_⟩,
      (srcPort C x).2, E.path j x C, (E.path j x C)[h], ?_, ?_, ?_, ?_⟩
    · rw [show h - 1 + 1 = h by omega, hu]
    · exact emb_path hE hj hC (hu ▸ onWalk_vtx hE hj hC hlen.le)
    · rw [List.getElem?_eq_getElem (by omega), path_edge hE hj hC (by omega),
        show h - 1 + 1 = h by omega, hu]
    · exact List.getElem?_eq_getElem hlen
    · rw [path_edge hE hj hC hlen, hu, hw, pcOth_mk]
  · rintro ⟨y, hy, k, l, e, hk, hl1, hl2, hw⟩
    obtain ⟨hxQ, C', hC', hlen', hu', hw'⟩ := mem_pk.1 hy
    obtain ⟨C, hCl, hxC, -, -, rfl⟩ := ioEmb_spec hk
    have hC : C ∈ clustersOf E.cl x := mem_filter.2 ⟨hCl, hxC⟩
    have hlen : h < (E.path j x C).length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hl2
      exact absurd hl2 (by simp)
    have h1 : (E.path j x C)[h - 1] = (E.path j x C')[h - 1] := by
      rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hl1
      rw [hl1, path_edge hE hj hC' hlen', hu', hw']
    have hCC := cluster_unique hE hj hC hC' (by omega) hlen' h1
    subst hCC
    refine mem_pk.2 ⟨hxQ, C, hC, hlen, by rw [← hw', show h - 1 + 1 = h by omega], ?_⟩
    rw [List.getElem?_eq_getElem hlen, Option.some.injEq] at hl2
    rw [← hw, ← hl2, path_edge hE hj hC hlen, ← hw', show h - 1 + 1 = h by omega, pcOth_mk]

/-! ### Counting -/

omit hE hj in
/-- At most `|Q|` packets cross a directed edge in a sub-phase (one per source: the edge
determines the cluster). -/
lemma card_pk_le (Q : Finset V) (h : ℕ) (u w : V) : (pk E j Q h u w).card ≤ Q.card :=
  card_filter_le _ _

end Emb

end APSP.Stoc.Congest
