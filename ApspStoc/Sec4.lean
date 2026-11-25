import ApspStoc.Statements

/-!
# Lemma 4.2: Minor-Aggregation on a subset (aggregator-based simulation)

One round of Minor-Aggregation on `(S, F_I)` is simulated as in the proofs of Theorem 4.1 and
Lemma 4.2:

1. every node of `S` tells its aggregators that it belongs to `S` (`aggUp`);
2. the aggregator of every cluster `C` computes a spanning forest of the contracted edges of the
   round inside `C` and sends every node its parent (`aggDown`);
3. every node notifies its parents (`notify`), so it knows its neighbours in the union `F` of the
   per-cluster forests;
4. GHS on `(S, F)` yields a rooted spanning forest whose trees span the supernodes (`ghs`);
5. a convergecast/broadcast computes the consensus values (`treeCast` with `⊕`);
6. every node sends its root and consensus value to its aggregators (`aggUp`);
7. the aggregators compute the values `z_{e,u}` of the crossing edges and their partial
   `⊗`-aggregates per node, and send them to the nodes (`aggDown`);
8. every node combines its partial aggregates, and a convergecast/broadcast with the lifted
   operator (absent values allowed) computes the supernode aggregates (`treeCast`).
-/

namespace APSP.Stoc

open APSP Finset

/-! ## Generic facts about aggregates -/

section Agg
variable {M : Type}

lemma AggOf.ne_zero {op : M → M → M} {s : Multiset M} {a : M} (h : AggOf op s a) : s ≠ 0 := by
  induction h with
  | single a => simp
  | comb _ _ ih1 _ => intro h; exact ih1 (add_eq_zero.1 h).1

lemma AggOf.pred {op : M → M → M} {P : M → Prop} (hop : ∀ a b, P a → P b → P (op a b))
    {s : Multiset M} {a : M} (h : AggOf op s a) (hs : ∀ m ∈ s, P m) : P a := by
  induction h with
  | single a => exact hs a (Multiset.mem_singleton_self a)
  | comb _ _ ih1 ih2 =>
    exact hop _ _ (ih1 fun m hm => hs m (Multiset.mem_add.2 (Or.inl hm)))
      (ih2 fun m hm => hs m (Multiset.mem_add.2 (Or.inr hm)))

/-- right fold of a non-empty list `a :: l` -/
def aggList (op : M → M → M) : M → List M → M
  | a, [] => a
  | a, b :: l => op a (aggList op b l)

/-- aggregate of a list (`none` for the empty list) -/
def aggOpt (op : M → M → M) : List M → Option M
  | [] => none
  | a :: l => some (aggList op a l)

lemma aggOf_aggList (op : M → M → M) (a : M) (l : List M) :
    AggOf op ((a :: l : List M) : Multiset M) (aggList op a l) := by
  induction l generalizing a with
  | nil => simpa [aggList] using AggOf.single (op := op) a
  | cons b l ih =>
    have := AggOf.comb (AggOf.single (op := op) a) (ih b)
    rw [Multiset.singleton_add] at this
    simpa [aggList] using this

lemma aggOpt_eq_none {op : M → M → M} {l : List M} : aggOpt op l = none ↔ l = [] := by
  cases l <;> simp [aggOpt]

lemma aggOf_aggOpt {op : M → M → M} {l : List M} {w : M} (h : aggOpt op l = some w) :
    AggOf op (l : Multiset M) w := by
  cases l with
  | nil => simp [aggOpt] at h
  | cons a l =>
    simp only [aggOpt, Option.some.injEq] at h
    subst h
    exact aggOf_aggList op a l

lemma Multiset.map_eq_add_split {α β : Type*} (f : α → β) (P : Multiset α) :
    ∀ s t : Multiset β, P.map f = s + t → ∃ P1 P2, P = P1 + P2 ∧ P1.map f = s ∧ P2.map f = t := by
  classical
  induction P using Multiset.induction_on with
  | empty =>
    intro s t h
    rw [Multiset.map_zero, eq_comm, add_eq_zero] at h
    exact ⟨0, 0, by simp, by simp [h.1], by simp [h.2]⟩
  | cons a P ih =>
    intro s t h
    rw [Multiset.map_cons] at h
    have hmem : f a ∈ s + t := h ▸ Multiset.mem_cons_self _ _
    rcases Multiset.mem_add.1 hmem with hs | ht
    · rw [← Multiset.cons_erase hs, Multiset.cons_add] at h
      obtain ⟨P1, P2, h1, h2, h3⟩ := ih _ _ (Multiset.cons_inj_right _ |>.1 h)
      refine ⟨a ::ₘ P1, P2, by rw [h1, Multiset.cons_add], ?_, h3⟩
      rw [Multiset.map_cons, h2, Multiset.cons_erase hs]
    · rw [← Multiset.cons_erase ht, Multiset.add_cons] at h
      obtain ⟨P1, P2, h1, h2, h3⟩ := ih _ _ (Multiset.cons_inj_right _ |>.1 h)
      refine ⟨P1, a ::ₘ P2, by rw [h1, Multiset.add_cons], h2, ?_⟩
      rw [Multiset.map_cons, h3, Multiset.cons_erase ht]

/-- Hierarchical aggregation: an aggregate of aggregates of parts is an aggregate of the union. -/
lemma aggOf_bind_pairs {op : M → M → M} {t : Multiset M} {a : M} (h : AggOf op t a) :
    ∀ P : Multiset (M × Multiset M), P.map Prod.fst = t → (∀ x ∈ P, AggOf op x.2 x.1) →
      AggOf op (P.bind Prod.snd) a := by
  induction h with
  | single a =>
    intro P hP hall
    obtain ⟨x, rfl, hx⟩ := Multiset.map_eq_singleton.1 hP
    rw [Multiset.singleton_bind, ← hx]
    exact hall x (Multiset.mem_singleton_self x)
  | comb _ _ ih1 ih2 =>
    intro P hP hall
    obtain ⟨P1, P2, rfl, hP1, hP2⟩ := Multiset.map_eq_add_split _ P _ _ hP
    rw [Multiset.add_bind]
    exact AggOf.comb (ih1 P1 hP1 (fun x hx => hall x (Multiset.mem_add.2 (Or.inl hx))))
      (ih2 P2 hP2 (fun x hx => hall x (Multiset.mem_add.2 (Or.inr hx))))

/-- Hierarchical aggregation with absent parts. -/
lemma aggOf_bind_opt {ι : Type*} {op : M → M → M} (s : Multiset ι) (o : ι → Option M)
    (f : ι → Multiset M)
    (h : ∀ i ∈ s, (o i = none → f i = 0) ∧ ∀ w, o i = some w → AggOf op (f i) w) :
    (s.filterMap o = 0 ↔ s.bind f = 0) ∧
      ∀ a, AggOf op (s.filterMap o) a → AggOf op (s.bind f) a := by
  let P := s.filterMap (fun i => (o i).map (fun w => (w, f i)))
  have key : (s.filterMap o = 0 ↔ s.bind f = 0) ∧ P.map Prod.fst = s.filterMap o ∧
      P.bind Prod.snd = s.bind f ∧ ∀ x ∈ P, AggOf op x.2 x.1 := by
    simp only [P]
    induction s using Multiset.induction_on with
    | empty => simp
    | cons i s ih =>
      have hi := h i (Multiset.mem_cons_self _ _)
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih (fun i' hi' => h i' (Multiset.mem_cons_of_mem hi'))
      cases hoi : o i with
      | none =>
        have hf : f i = 0 := hi.1 hoi
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Multiset.filterMap_cons_none _ _ hoi, Multiset.cons_bind, hf, zero_add]; exact ih1
        · rw [Multiset.filterMap_cons_none _ _ (by simp [hoi]),
            Multiset.filterMap_cons_none _ _ hoi]; exact ih2
        · rw [Multiset.filterMap_cons_none _ _ (by simp [hoi]), Multiset.cons_bind, hf, zero_add]
          exact ih3
        · rw [Multiset.filterMap_cons_none _ _ (by simp [hoi])]; exact ih4
      | some w =>
        have hw := hi.2 w hoi
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Multiset.filterMap_cons_some _ _ _ hoi, Multiset.cons_bind]
          simp only [Multiset.cons_ne_zero, false_iff]
          intro h0
          exact hw.ne_zero (add_eq_zero.1 h0).1
        · rw [Multiset.filterMap_cons_some _ _ _ (b := (w, f i)) (by simp [hoi]),
            Multiset.filterMap_cons_some _ _ _ hoi, Multiset.map_cons, ih2]
        · rw [Multiset.filterMap_cons_some _ _ _ (b := (w, f i)) (by simp [hoi]), Multiset.cons_bind,
            Multiset.cons_bind, ih3]
        · rw [Multiset.filterMap_cons_some _ _ _ (b := (w, f i)) (by simp [hoi])]
          intro x hx
          rcases Multiset.mem_cons.1 hx with rfl | hx
          · exact hw
          · exact ih4 x hx
  refine ⟨key.1, fun a ha => ?_⟩
  rw [← key.2.2.1]
  exact aggOf_bind_pairs ha P key.2.1 key.2.2.2

end Agg

/-! ## Messages: a lifted operator for possibly absent values -/

section Lift
variable {V : Type}

/-- encoding of an optional message (`none` = the empty message) -/
def encO : Option (Msg V) → Msg V
  | none => []
  | some m => Word.num 0 :: m

/-- decoding of `encO` -/
def decO : Msg V → Option (Msg V)
  | [] => none
  | _ :: m => some m

@[simp] lemma decO_encO (o : Option (Msg V)) : decO (encO o) = o := by cases o <;> rfl

/-- the operator `op` lifted to optional values (absent values are neutral) -/
def liftOp (op : Msg V → Msg V → Msg V) (m m' : Msg V) : Msg V :=
  match decO m, decO m' with
  | none, _ => m'
  | some _, none => m
  | some x, some y => encO (some (op x y))

lemma aggOf_liftOp (op : Msg V → Msg V → Msg V) {s : Multiset (Msg V)} {a : Msg V}
    (h : AggOf (liftOp op) s a) :
    (s.filterMap decO = 0 ∧ decO a = none) ∨ ∃ z, decO a = some z ∧ AggOf op (s.filterMap decO) z := by
  induction h with
  | single a =>
    cases ha : decO a with
    | none =>
      left
      rw [← Multiset.cons_zero, Multiset.filterMap_cons_none _ _ ha, Multiset.filterMap_zero]
      exact ⟨rfl, rfl⟩
    | some z =>
      right
      refine ⟨z, rfl, ?_⟩
      rw [← Multiset.cons_zero, Multiset.filterMap_cons_some _ _ _ ha, Multiset.filterMap_zero,
        Multiset.cons_zero]
      exact AggOf.single z
  | @comb s t a b _ _ ih1 ih2 =>
    rw [Multiset.filterMap_add]
    rcases ih1 with ⟨hs, ha⟩ | ⟨x, ha, hx⟩ <;> rcases ih2 with ⟨ht, hb⟩ | ⟨y, hb, hy⟩
    · left; refine ⟨by rw [hs, ht, add_zero], ?_⟩
      simp only [liftOp, ha]; exact hb
    · right; refine ⟨y, ?_, by rw [hs, zero_add]; exact hy⟩
      simp only [liftOp, ha]; exact hb
    · right; refine ⟨x, ?_, by rw [ht, add_zero]; exact hx⟩
      simp only [liftOp, ha, hb]
    · right; refine ⟨op x y, ?_, AggOf.comb hx hy⟩
      simp only [liftOp, ha, hb, decO_encO]

lemma Msg.small_cons {b B : ℕ} {m : Msg V} {w : Word V} (hm : m.Small b B)
    (hw : ∀ k, w = Word.num k → k ≤ B) : Msg.Small (b + 1) B (w :: m) := by
  refine ⟨by simp [hm.1], fun k hk => ?_⟩
  rcases List.mem_cons.1 hk with h | h
  · exact hw k h.symm
  · exact hm.2 k h

lemma Msg.small_tail {b B : ℕ} {m : Msg V} (hm : m.Small (b + 1) B) : Msg.Small b B m.tail :=
  ⟨by have := hm.1; simp; omega, fun k hk => hm.2 k (List.mem_of_mem_tail hk)⟩

lemma Msg.small_mono {b b' B : ℕ} {m : Msg V} (hm : m.Small b B) (h : b ≤ b') : m.Small b' B :=
  ⟨hm.1.trans h, hm.2⟩

lemma small_encO {b B : ℕ} {o : Option (Msg V)} (h : ∀ m, o = some m → m.Small b B) :
    (encO o).Small (b + 1) B := by
  cases o with
  | none => exact ⟨by simp [encO], fun k hk => by simp [encO] at hk⟩
  | some m => exact Msg.small_cons (h m rfl) (fun k hk => by have := Word.num.inj hk; omega)

lemma small_decO {b B : ℕ} {m x : Msg V} (hm : m.Small (b + 1) B) (h : decO m = some x) :
    x.Small b B := by
  cases m with
  | nil => simp [decO] at h
  | cons w m =>
    simp only [decO, Option.some.injEq] at h
    subst h
    exact Msg.small_tail hm

lemma small_liftOp {b B : ℕ} {op : Msg V → Msg V → Msg V}
    (hop : ∀ m m', m.Small b B → m'.Small b B → (op m m').Small b B) {m m' : Msg V}
    (hm : m.Small (b + 1) B) (hm' : m'.Small (b + 1) B) : (liftOp op m m').Small (b + 1) B := by
  unfold liftOp
  cases hx : decO m with
  | none => exact hm'
  | some x =>
    cases hy : decO m' with
    | none => exact hm
    | some y =>
      exact small_encO (fun z hz => by
        cases hz; exact hop _ _ (small_decO hm hx) (small_decO hm' hy))

end Lift

/-! ## Connectivity and forests -/

section Forest
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma EReach.symm' {F : Finset (Sym2 V)} {a b : V} (h : EReach F a b) : EReach F b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih => exact Relation.ReflTransGen.head (by rwa [Sym2.eq_swap]) ih

omit [Fintype V] [DecidableEq V] in
lemma EReach.mono' {F F' : Finset (Sym2 V)} (hF : F ⊆ F') {a b : V} (h : EReach F a b) :
    EReach F' a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih => exact Relation.ReflTransGen.tail ih (hF hcd)

omit [Fintype V] [DecidableEq V] in
lemma EReach.single' {F : Finset (Sym2 V)} {a b : V} (h : s(a, b) ∈ F) : EReach F a b :=
  Relation.ReflTransGen.single h

omit [Fintype V] [DecidableEq V] in
/-- If `F ⊆ F'` and the endpoints of every edge of `F'` are connected in `F`, then `F` and `F'`
have the same connectivity. -/
lemma EReach_iff_of {F F' : Finset (Sym2 V)} (hF : F ⊆ F')
    (h : ∀ a b, s(a, b) ∈ F' → EReach F a b) (a b : V) : EReach F' a b ↔ EReach F a b := by
  refine ⟨fun hab => ?_, EReach.mono' hF⟩
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih => exact ih.trans (h _ _ hcd)

/-- the graph with edge set `K` -/
abbrev gOf (K : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet (K : Set (Sym2 V))

/-- a representative ("root") of the component of `v` in `gOf K` -/
noncomputable def frt (K : Finset (Sym2 V)) (v : V) : V := ((gOf K).connectedComponentMk v).out

omit [Fintype V] [DecidableEq V] in
lemma frt_reach (K : Finset (Sym2 V)) (v : V) : (gOf K).Reachable (frt K v) v :=
  SimpleGraph.ConnectedComponent.exact (Quot.out_eq _)

omit [Fintype V] [DecidableEq V] in
lemma frt_eq {K : Finset (Sym2 V)} {u v : V} (h : (gOf K).Reachable u v) : frt K u = frt K v := by
  unfold frt; rw [SimpleGraph.ConnectedComponent.sound h]

open Classical in
/-- parent pointers of a BFS forest of `gOf K` (towards the roots `frt K`) -/
noncomputable def fpar (K : Finset (Sym2 V)) (v : V) : Option V :=
  if h : ∃ u, (gOf K).Adj v u ∧ (gOf K).dist (frt K v) u < (gOf K).dist (frt K v) v then
    some (Classical.choose h) else none

lemma fpar_spec {K : Finset (Sym2 V)} {v u : V} (h : fpar K v = some u) :
    (gOf K).Adj v u ∧ (gOf K).dist (frt K v) u < (gOf K).dist (frt K v) v := by
  unfold fpar at h
  split_ifs at h with hex
  · cases h; exact Classical.choose_spec hex

lemma fpar_mem {K : Finset (Sym2 V)} {v u : V} (h : fpar K v = some u) : s(v, u) ∈ K := by
  have := (fpar_spec h).1
  rw [SimpleGraph.fromEdgeSet_adj] at this
  exact this.1

lemma fpar_exists {K : Finset (Sym2 V)} {v : V} (h : 0 < (gOf K).dist (frt K v) v) :
    ∃ u, fpar K v = some u ∧ (gOf K).Adj v u ∧
      (gOf K).dist (frt K v) u < (gOf K).dist (frt K v) v := by
  have key : ∀ r : V, ∀ p : (gOf K).Walk v r, 0 < p.length →
      ∃ u, (gOf K).Adj v u ∧ (gOf K).dist u r < p.length := by
    intro r p hp
    cases p with
    | nil => simp at hp
    | cons hadj q =>
      exact ⟨_, hadj, lt_of_le_of_lt (SimpleGraph.dist_le q) (by simp)⟩
  have hex : ∃ u, (gOf K).Adj v u ∧ (gOf K).dist (frt K v) u < (gOf K).dist (frt K v) v := by
    obtain ⟨p, hp⟩ := (frt_reach K v).symm.exists_walk_length_eq_dist
    rw [SimpleGraph.dist_comm] at h
    obtain ⟨u, hadj, hlt⟩ := key _ p (hp ▸ h)
    refine ⟨u, hadj, ?_⟩
    rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := frt K v) (v := v)]
    omega
  refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
  unfold fpar; rw [dite_eq_left hex]

/-- the edges `s(v, par v)` of parent pointers -/
def pedges (par : V → Option V) : Finset (Sym2 V) :=
  univ.biUnion (fun v => ((par v).map (fun u => s(v, u))).toFinset)

lemma mem_pedges {par : V → Option V} {e : Sym2 V} :
    e ∈ pedges par ↔ ∃ v u, par v = some u ∧ e = s(v, u) := by
  simp only [pedges, mem_biUnion, mem_univ, true_and, Option.mem_toFinset, Option.mem_def,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, u, h1, h2⟩; exact ⟨v, u, h1, h2.symm⟩
  · rintro ⟨v, u, h1, h2⟩; exact ⟨v, u, h1, h2.symm⟩

lemma pedges_card_le (par : V → Option V) (A : Finset V) (h : ∀ v u, par v = some u → v ∈ A) :
    (pedges par).card ≤ A.card := by
  have hsub : pedges par ⊆ A.biUnion (fun v => ((par v).map (fun u => s(v, u))).toFinset) := by
    intro e he
    obtain ⟨v, u, h1, rfl⟩ := mem_pedges.1 he
    exact mem_biUnion.2 ⟨v, h v u h1, by simp [h1]⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [card_eq_sum_ones]
  apply sum_le_sum
  intro v _
  cases par v <;> simp

lemma fpar_reach_root (K : Finset (Sym2 V)) (v : V) : EReach (pedges (fpar K)) v (frt K v) := by
  induction hn : (gOf K).dist (frt K v) v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [(frt_reach K v).dist_eq_zero_iff] at hn
      rw [hn]; exact Relation.ReflTransGen.refl
    · obtain ⟨u, hu, hadj, hlt⟩ := fpar_exists (K := K) (v := v) (hn ▸ hpos)
      have hr : frt K u = frt K v := (frt_eq hadj.reachable).symm
      have := ih _ (hn ▸ hlt) u (by rw [hr])
      rw [hr] at this
      exact Relation.ReflTransGen.head (mem_pedges.2 ⟨v, u, hu, rfl⟩) this

/-- the endpoints of every edge of `K` are connected along the parent pointers -/
lemma fpar_conn (K : Finset (Sym2 V)) {a b : V} (h : s(a, b) ∈ K) :
    EReach (pedges (fpar K)) a b := by
  by_cases hab : a = b
  · subst hab; exact Relation.ReflTransGen.refl
  · have hadj : (gOf K).Adj a b := by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨h, hab⟩
    have hr := frt_eq (K := K) hadj.reachable
    have h1 := fpar_reach_root K a
    have h2 := (fpar_reach_root K b).symm'
    rw [hr] at h1
    exact h1.trans h2

end Forest

/-! ## The data of a round -/

section Round
variable {V : Type} [Fintype V] [DecidableEq V]

lemma ma_mem_inducedEdges {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {e : Sym2 V} :
    e ∈ inducedEdges G S ↔ e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ S := by
  unfold inducedEdges; simp only [mem_filter]

lemma MAInst.mem_edges {G : SimpleGraph V} [DecidableRel G.Adj] {I : MAInst V} {e : Sym2 V} :
    e ∈ I.edges G ↔ e ∈ G.edgeFinset ∧ (∀ v ∈ e, v ∈ I.S) ∧ I.pres e = true := by
  unfold MAInst.edges; simp only [mem_filter, ma_mem_inducedEdges, and_assoc]

lemma MAInst.mem_cedges {G : SimpleGraph V} [DecidableRel G.Adj] {I : MAInst V} {e : Sym2 V} :
    e ∈ I.cedges G ↔ e ∈ I.edges G ∧ I.con e = true := by
  unfold MAInst.cedges; simp only [mem_filter]

/-- the contracted edges of the round inside cluster `C` -/
noncomputable def ccl (G : SimpleGraph V) [DecidableRel G.Adj] (I : MAInst V) (C : Finset (Sym2 V)) :
    Finset (Sym2 V) := C.filter (fun e => e ∈ I.cedges G)

/-- the union of the per-cluster spanning forests -/
noncomputable def forestF (G : SimpleGraph V) [DecidableRel G.Adj] (cl : Finset (Finset (Sym2 V)))
    (I : MAInst V) : Finset (Sym2 V) :=
  cl.biUnion (fun C => pedges (fpar (ccl G I C)))

variable {G : SimpleGraph V} [DecidableRel G.Adj] {I : MAInst V}

lemma fpar_ccl {C : Finset (Sym2 V)} {v u : V} (h : fpar (ccl G I C) v = some u) :
    s(v, u) ∈ C ∧ s(v, u) ∈ I.cedges G := by
  have := fpar_mem h; unfold ccl at this; exact mem_filter.1 this

lemma mem_forestF {cl : Finset (Finset (Sym2 V))} {e : Sym2 V} :
    e ∈ forestF G cl I ↔ ∃ C ∈ cl, ∃ v u, fpar (ccl G I C) v = some u ∧ e = s(v, u) := by
  unfold forestF; simp only [mem_biUnion, mem_pedges]

lemma forestF_sub_cedges (cl : Finset (Finset (Sym2 V))) : forestF G cl I ⊆ I.cedges G := by
  intro e he
  obtain ⟨C, _, v, u, h, rfl⟩ := mem_forestF.1 he
  exact (fpar_ccl h).2

lemma cedges_sub_edges : I.cedges G ⊆ I.edges G := fun _ he => (MAInst.mem_cedges.1 he).1

lemma forestF_sub (cl : Finset (Finset (Sym2 V))) : forestF G cl I ⊆ G.edgeFinset :=
  fun _ he => (MAInst.mem_edges.1 (cedges_sub_edges (forestF_sub_cedges cl he))).1

lemma forestF_S (cl : Finset (Finset (Sym2 V))) : ∀ e ∈ forestF G cl I, ∀ v ∈ e, v ∈ I.S :=
  fun _ he => (MAInst.mem_edges.1 (cedges_sub_edges (forestF_sub_cedges cl he))).2.1

/-- the forest has the connectivity of the contracted edges -/
lemma EReach_forestF {cl : Finset (Finset (Sym2 V))} (hcov : ∀ e ∈ G.edgeFinset, ∃ C ∈ cl, e ∈ C)
    (a b : V) : EReach (I.cedges G) a b ↔ EReach (forestF G cl I) a b := by
  refine EReach_iff_of (forestF_sub_cedges cl) (fun x y hxy => ?_) a b
  have hG := (MAInst.mem_edges.1 (cedges_sub_edges hxy)).1
  obtain ⟨C, hC, hxyC⟩ := hcov _ hG
  have h1 : s(x, y) ∈ ccl G I C := mem_filter.2 ⟨hxyC, hxy⟩
  refine EReach.mono' (fun e he => ?_) (fpar_conn _ h1)
  obtain ⟨v, u, h, rfl⟩ := mem_pedges.1 he
  exact mem_forestF.2 ⟨C, hC, v, u, h, rfl⟩

lemma forestF_card {cl : Finset (Finset (Sym2 V))} {ov : ℕ}
    (hov : ∀ v, (clustersOf cl v).card ≤ ov) : (forestF G cl I).card ≤ ov * I.S.card := by
  unfold forestF
  refine card_biUnion_le.trans ?_
  have h1 : ∀ C ∈ cl, (pedges (fpar (ccl G I C))).card ≤ ((nodes C).filter (· ∈ I.S)).card := by
    intro C _
    apply pedges_card_le
    intro v u h
    have := fpar_ccl h
    refine mem_filter.2 ⟨mem_nodes.2 ⟨_, this.1, Sym2.mem_mk_left v u⟩, ?_⟩
    exact (MAInst.mem_edges.1 (cedges_sub_edges this.2)).2.1 v (Sym2.mem_mk_left v u)
  refine (sum_le_sum h1).trans ?_
  have h2 : ∑ C ∈ cl, ((nodes C).filter (· ∈ I.S)).card = ∑ v ∈ I.S, (clustersOf cl v).card := by
    have e1 : ∀ C, (nodes C).filter (· ∈ I.S) = I.S.filter (· ∈ nodes C) := by
      intro C; ext v; simp only [mem_filter]; tauto
    simp only [e1, card_filter, clustersOf]
    exact sum_comm
  rw [h2]
  have := sum_le_card_nsmul I.S (fun v => (clustersOf cl v).card) ov (fun v _ => hov v)
  simpa [mul_comm] using this

end Round

/-! ## The algorithm -/

section Alg

/-- contraction bit of an edge datum -/
def conBit {V : Type} (o : Option (Bool × (V → Msg V → Msg V → Msg V))) : Bool :=
  match o with
  | some (c, _) => c
  | none => false

/-- aggregation function of an edge datum -/
def zfun {V : Type} (o : Option (Bool × (V → Msg V → Msg V → Msg V))) :
    V → Msg V → Msg V → Msg V :=
  match o with
  | some (_, z) => z
  | none => fun _ _ _ => []

/-- the tail of an optional message -/
def tl {V : Type} (o : Option (Msg V)) : Msg V := (o.map List.tail).getD []

variable {V : Type} [Fintype V] [DecidableEq V]

/-- (aggregator of `C`) the contracted edges of the round in `C`, computed from the edge data and
the membership messages -/
def aggCon (C : Finset (Sym2 V)) (ed : Sym2 V → Option (Bool × (V → Msg V → Msg V → Msg V)))
    (y : V → Option (Msg V)) : Finset (Sym2 V) :=
  C.filter (fun e => conBit (ed e) = true ∧ ∀ v ∈ e, (y v).isSome = true)

/-- (node) the parents announced by the aggregators -/
def parentsOf (m : Multiset (Msg V)) : Finset V := univ.filter (fun u => [Word.id u] ∈ m)

/-- (aggregator of `C`) the crossing edges of the round in `C` at `u` -/
def maCrossP (C : Finset (Sym2 V)) (ed : Sym2 V → Option (Bool × (V → Msg V → Msg V → Msg V)))
    (y : V → Option (Msg V)) (u : V) : Finset V :=
  univ.filter (fun u' => s(u, u') ∈ C ∧ (ed s(u, u')).isSome = true ∧ (y u).isSome = true ∧
    (y u').isSome = true ∧ (y u).map List.head? ≠ (y u').map List.head?)

/-- (aggregator of `C`) the partial `⊗`-aggregate for node `u` -/
noncomputable def msg7 (C : Finset (Sym2 V))
    (ed : Sym2 V → Option (Bool × (V → Msg V → Msg V → Msg V))) (op : Msg V → Msg V → Msg V)
    (y : V → Option (Msg V)) (u : V) : Option (Msg V) :=
  aggOpt op ((maCrossP C ed y u).toList.map
    (fun u' => zfun (ed s(u, u')) u (tl (y u)) (tl (y u'))))

end Alg

/-- states of the agents between the steps -/
abbrev St1 (V : Type) := MAIn V × (V → Option (Msg V))
abbrev St2 (V : Type) := St1 V × Multiset (Msg V)
abbrev St3 (V : Type) := St2 V × Finset V
abbrev St4 (V : Type) := St3 V × (Option V × V)
abbrev St5 (V : Type) := St4 V × Option (Msg V)
abbrev St6 (V : Type) := St5 V × (V → Option (Msg V))
abbrev St7 (V : Type) := St6 V × Multiset (Msg V)
abbrev St8 (V : Type) := St7 V × Option (Msg V)
/-- input of a tree convergecast/broadcast -/
abbrev TcIn (V : Type) := Option (Option V × V × Msg V × (Msg V → Msg V → Msg V))

/-- step 1: membership messages -/
def L1 : LocFn where
  α := MAIn
  β := fun V => Option (Msg V)
  f := fun _ _ _ g _ s => match g with
    | .inl _ => if s.inS then some [] else none
    | .inr _ => none

/-- step 2: per-cluster forests, parent messages -/
noncomputable def L2 : LocFn where
  α := St1
  β := fun V => V → Option (Msg V)
  f := fun _ _ _ g _ s => match g with
    | .inl _ => fun _ => none
    | .inr C => fun v => (fpar (aggCon C s.1.edata s.2) v).map (fun u => [Word.id u])

/-- step 3: notify the parents -/
def L3 : LocFn where
  α := St2
  β := fun V => Finset V
  f := fun _ _ _ g _ s => match g with
    | .inl _ => parentsOf s.2
    | .inr _ => ∅

/-- step 4: GHS input (neighbours in the forest) -/
def L4 : LocFn where
  α := St3
  β := fun V => Option (Finset V)
  f := fun _ _ _ g _ s => match g with
    | .inl _ => if s.1.1.1.inS then some (parentsOf s.1.2 ∪ s.2) else none
    | .inr _ => none

/-- step 5: convergecast/broadcast of the inputs with `⊕` -/
def L5 : LocFn where
  α := St4
  β := TcIn
  f := fun _ _ _ g _ s => match g with
    | .inl _ => if s.1.1.1.1.inS then some (s.2.1, s.2.2, s.1.1.1.1.x, s.1.1.1.1.op₁) else none
    | .inr _ => none

/-- step 6: root and consensus value to the aggregators -/
def L6 : LocFn where
  α := St5
  β := fun V => Option (Msg V)
  f := fun _ _ _ g _ s => match g with
    | .inl _ => if s.1.1.1.1.1.inS then some (Word.id s.1.2.2 :: s.2.getD []) else none
    | .inr _ => none

/-- step 7: partial aggregates at the aggregators -/
noncomputable def L7 : LocFn where
  α := St6
  β := fun V => V → Option (Msg V)
  f := fun _ _ _ g _ s => match g with
    | .inl _ => fun _ => none
    | .inr C => fun u => msg7 C s.1.1.1.1.1.1.edata s.1.1.1.1.1.1.op₂ s.2 u

/-- step 8: convergecast/broadcast of the nodes' partial aggregates with the lifted `⊗` -/
noncomputable def L8 : LocFn where
  α := St7
  β := TcIn
  f := fun _ _ _ g _ s => match g with
    | .inl _ => if s.1.1.1.1.1.1.1.inS then
        some (s.1.1.1.2.1, s.1.1.1.2.2, encO (aggOpt s.1.1.1.1.1.1.1.op₂ s.2.toList),
          liftOp s.1.1.1.1.1.1.1.op₂) else none
    | .inr _ => none

/-- output -/
def Lfin : LocFn where
  α := St8
  β := MAOut
  f := fun _ _ _ g _ s => match g with
    | .inl _ => ⟨s.1.1.1.2, s.2.bind decO, fun _ _ => none⟩
    | .inr _ => ⟨none, none, fun _ u => (s.1.1.2 u).map List.tail⟩

/-- The simulation of one Minor-Aggregation round with `b`-word values. The tree
convergecast/broadcast `Atc` is indexed by its public value size: `b` for the consensus values
(step 5), `b + 1` for the encoded partial aggregates (step 8). Likewise the aggregator exchanges
`Aup`, `Adn` are indexed by their public message size: `0` for the membership messages (step 1),
`1` for the parents (step 2), `b + 1` for the roots and consensus values (step 6), `b` for the
partial aggregates (step 7). -/
noncomputable def maAlg (T : Toolkit) (Aup Adn : ℕ → T.Alg) (Anot Agh : T.Alg) (Atc : ℕ → T.Alg)
    (b : ℕ) : T.Alg :=
  T.seq (T.call L1 (Aup 0)) <| T.seq (T.call L2 (Adn 1)) <|
  T.seq (T.call L3 Anot) <| T.seq (T.call L4 Agh) <|
  T.seq (T.call L5 (Atc b)) <| T.seq (T.call L6 (Aup (b + 1))) <|
  T.seq (T.call L7 (Adn b)) <| T.seq (T.call L8 (Atc (b + 1))) (T.loc Lfin)

/-- A local computation followed by an algorithm working on its result (a local call). -/
lemma stage (T : Toolkit) (F : LocFn) {P : T.Alg} {V : Type} [Fintype V] [DecidableEq V]
    {N : WNet V} {E : Overlays V} {j sz : ℕ} {Pt : Finset V} {β : Type} {s : Agent V → F.α V}
    {R : (Agent V → β) → Prop} {p : Prof V} {δ : ℝ}
    (h : T.Impl P N (.io E j sz Pt (F.β V) β (fun g => F.f V g (lview N g) (s g)) R) p δ) :
    T.Impl (T.call F P) N (.io E j sz Pt (F.α V) β s R) p δ :=
  T.callR F s h

/-! ## The aggregation step: combinatorics -/

section Comb
variable {V : Type} [Fintype V] [DecidableEq V]

lemma val_map_eq_sum {α β : Type*} (A : Finset α) (h : α → β) :
    A.val.map h = ∑ x ∈ A, ({h x} : Multiset β) := by
  rw [Finset.sum_eq_multiset_sum]
  generalize A.val = s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, Multiset.singleton_add]

lemma val_bind_eq_sum {α β : Type*} (A : Finset α) (f : α → Multiset β) :
    A.val.bind f = ∑ x ∈ A, f x := by
  rw [Finset.sum_eq_multiset_sum]; rfl

/-- the crossing edges of the round in `C` at `u` (mathematical version) -/
noncomputable def mcross (G : SimpleGraph V) [DecidableRel G.Adj] (I : MAInst V) (root : V → V)
    (C : Finset (Sym2 V)) (u : V) : Finset V :=
  univ.filter (fun u' => s(u, u') ∈ C ∧ s(u, u') ∈ I.edges G ∧ root u ≠ root u')

variable {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V} {ov d X : ℕ}

/-- every edge of `G` lies in exactly one cluster -/
lemma sum_clusters_unique (hE : OverlayProps G E ov d X) {u : V} {e : Sym2 V} (hu : u ∈ e)
    (Q : Prop) [Decidable Q] (hQ : Q → e ∈ G.edgeFinset) {β : Type*} [AddCommMonoid β] (m : β) :
    ∑ C ∈ clustersOf E.cl u, (if e ∈ C ∧ Q then m else 0) = if Q then m else 0 := by
  by_cases hq : Q
  · simp only [hq, and_true, ↓reduceIte]
    obtain ⟨C0, hC0, he0⟩ := hE.valid.cover e (hQ hq)
    have hC0' : C0 ∈ clustersOf E.cl u := mem_filter.2 ⟨hC0, mem_nodes.2 ⟨e, he0, hu⟩⟩
    rw [sum_eq_single C0]
    · simp [he0]
    · intro C hC hne
      have hdis := hE.disj C (mem_filter.1 hC).1 C0 hC0 hne
      rw [ite_eq_right]
      intro heC
      exact disjoint_left.1 hdis heC he0
    · intro h; exact absurd hC0' h
  · simp [hq]

/-- The multiset of the values `z_{e,s}` of the edges leaving the supernode of `v` is the union,
over the nodes `u` of the supernode and the clusters `C` of `u`, of the values of the crossing
edges of the round in `C` at `u`. -/
lemma zcomb (hE : OverlayProps G E ov d X) (I : MAInst V) (root : V → V)
    (hroot : ∀ u ∈ I.S, ∀ w ∈ I.S, (root u = root w ↔ EReach (I.cedges G) u w))
    (g : V → V → Msg V) {v : V} (hv : v ∈ I.S) (P : V × V → Prop) [DecidablePred P]
    (hP : ∀ p, P p ↔ (s(p.1, p.2) ∈ I.edges G ∧ EReach (I.cedges G) p.1 v ∧
      ¬ EReach (I.cedges G) p.1 p.2)) :
    ((I.S ×ˢ I.S).filter P).val.map (fun p => g p.1 p.2) =
      (I.S.filter (fun u => root u = root v)).val.bind
        (fun u => (clustersOf E.cl u).val.bind (fun C => (mcross G I root C u).val.map (g u))) := by
  rw [val_map_eq_sum, val_bind_eq_sum, sum_filter, sum_filter, sum_product]
  refine sum_congr rfl (fun u hu => ?_)
  split_ifs with hr
  · have huv : EReach (I.cedges G) u v := (hroot u hu v hv).1 hr
    rw [val_bind_eq_sum]
    simp only [val_map_eq_sum, mcross, sum_filter]
    rw [sum_comm]
    have h1 : ∀ u' ∈ (univ : Finset V), ∑ C ∈ clustersOf E.cl u,
        (if s(u, u') ∈ C ∧ s(u, u') ∈ I.edges G ∧ root u ≠ root u' then
          ({g u u'} : Multiset (Msg V)) else 0) =
        if s(u, u') ∈ I.edges G ∧ root u ≠ root u' then {g u u'} else 0 :=
      fun u' _ => sum_clusters_unique hE (Sym2.mem_mk_left u u') _
        (fun h => (MAInst.mem_edges.1 h.1).1) _
    rw [sum_congr rfl h1]
    symm
    rw [← sum_subset (subset_univ I.S)]
    · refine sum_congr rfl (fun u' hu' => ?_)
      have : (s(u, u') ∈ I.edges G ∧ root u ≠ root u') ↔ P (u, u') := by
        rw [hP]
        simp only [huv, true_and]
        rw [← hroot u hu u' hu']
      simp only [this]
    · intro u' _ hu'
      rw [ite_eq_right]
      intro h
      exact hu' ((MAInst.mem_edges.1 h.1).2.1 u' (Sym2.mem_mk_right u u'))
  · apply sum_eq_zero
    intro u' _
    rw [ite_eq_right]
    intro h
    exact hr ((hroot u hu v hv).2 ((hP _).1 h).2.1)

end Comb

/-! ## The output specification -/

section Final
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {E : Overlays V} {ov d X : ℕ}

/-- the multiset of the values `z_{e,u}` of the crossing edges of the round at `u` -/
noncomputable def zU (G : SimpleGraph V) [DecidableRel G.Adj] (cl : Finset (Finset (Sym2 V)))
    (I : MAInst V) (root : V → V) (g : V → V → Msg V) (u : V) : Multiset (Msg V) :=
  (clustersOf cl u).val.bind (fun C => (mcross G I root C u).val.map (g u))

open Classical in
lemma final_spec (hE : OverlayProps G E ov d X) (I : MAInst V) (root : V → V)
    (hroot : ∀ u ∈ I.S, ∀ w ∈ I.S, (root u = root w ↔ EReach (I.cedges G) u w))
    (Y : V → Msg V) (zopt : V → Option (Msg V)) (o : Agent V → MAOut V)
    (hy : ∀ v ∈ I.S, (o (.inl v)).y = some (Y v))
    (hYagg : ∀ v ∈ I.S, AggOf I.op₁ ((I.S.filter (fun u => root u = root v)).val.map I.x) (Y v))
    (hYc : ∀ u ∈ I.S, ∀ v ∈ I.S, root u = root v → Y u = Y v)
    (hey : ∀ C ∈ E.cl, ∀ e ∈ I.edges G, e ∈ C → ∀ u ∈ e, (o (.inr C)).ey e u = some (Y u))
    (hzopt : ∀ u ∈ I.S,
      (zopt u = none → zU G E.cl I root (fun a b => I.zf s(a, b) a (Y a) (Y b)) u = 0) ∧
      ∀ w, zopt u = some w → AggOf I.op₂ (zU G E.cl I root (fun a b => I.zf s(a, b) a (Y a) (Y b)) u) w)
    (hz : ∀ v ∈ I.S, ∃ a, (o (.inl v)).z = decO a ∧
      AggOf (liftOp I.op₂) ((I.S.filter (fun u => root u = root v)).val.map
        (fun u => encO (zopt u))) a ∧
      ∀ u ∈ I.S, root u = root v → (o (.inl u)).z = decO a) :
    MASpec G E.cl I o := by
  refine ⟨Y, hy, fun u hu v hv h => hYc u hu v hv ((hroot u hu v hv).2 h), fun v hv => ?_,
    fun v hv => ?_, ?_, hey⟩
  · have : I.S.filter (fun u => EReach (I.cedges G) u v) = I.S.filter (fun u => root u = root v) :=
      Finset.filter_congr (fun u hu => (hroot u hu v hv).symm)
    rw [this]; exact hYagg v hv
  · intro Z
    have hZ : Z = (I.S.filter (fun u => root u = root v)).val.bind
        (zU G E.cl I root (fun a b => I.zf s(a, b) a (Y a) (Y b))) :=
      zcomb hE I root hroot (fun a b => I.zf s(a, b) a (Y a) (Y b)) hv _ (fun p => Iff.rfl)
    obtain ⟨a, ha, hagg, -⟩ := hz v hv
    have hl := aggOf_liftOp I.op₂ hagg
    have hD : ((I.S.filter (fun u => root u = root v)).val.map (fun u => encO (zopt u))).filterMap
        decO = (I.S.filter (fun u => root u = root v)).val.filterMap zopt := by
      rw [Multiset.filterMap_map]
      congr 1
      funext u
      simp
    have hb := aggOf_bind_opt (op := I.op₂) (I.S.filter (fun u => root u = root v)).val zopt
      (zU G E.cl I root (fun a b => I.zf s(a, b) a (Y a) (Y b)))
      (fun u hu => hzopt u (mem_filter.1 hu).1)
    rw [hD] at hl
    constructor
    · intro hZ0
      rw [ha]
      rcases hl with ⟨_, h⟩ | ⟨z, _, hz'⟩
      · exact h
      · exact absurd (hb.1.2 (hZ ▸ hZ0)) hz'.ne_zero
    · intro hZ0
      rcases hl with ⟨h0, _⟩ | ⟨z, hz1, hz2⟩
      · exact absurd (hZ ▸ hb.1.1 h0) hZ0
      · exact ⟨z, by rw [ha, hz1], by rw [hZ]; exact hb.2 z hz2⟩
  · intro u hu v hv h
    obtain ⟨a, ha, -, hc⟩ := hz v hv
    rw [ha, hc u hu ((hroot u hu v hv).2 h)]

end Final

/-! ## What the agents compute -/

section Local
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {I : MAInst V}

lemma coe_toList_map {α β : Type*} (A : Finset α) (h : α → β) :
    ((A.toList.map h : List β) : Multiset β) = A.val.map h := by
  rw [← Multiset.map_coe, Finset.coe_toList]

/-- levels 1 and 2 of the aggregation: the aggregators' partial aggregates and their
combination at the node -/
lemma zopt_spec (cl : Finset (Finset (Sym2 V))) (root : V → V) (g : V → V → Msg V) (u : V)
    (op : Msg V → Msg V → Msg V) (m7 : Finset (Sym2 V) → Option (Msg V))
    (hm7 : ∀ C ∈ clustersOf cl u, m7 C = aggOpt op ((mcross G I root C u).toList.map (g u))) :
    (aggOpt op ((clustersOf cl u).val.filterMap m7).toList = none → zU G cl I root g u = 0) ∧
    ∀ w, aggOpt op ((clustersOf cl u).val.filterMap m7).toList = some w →
      AggOf op (zU G cl I root g u) w := by
  have hb := aggOf_bind_opt (op := op) (clustersOf cl u).val m7
    (fun C => (mcross G I root C u).val.map (g u)) (fun C hC => by
      refine ⟨fun h => ?_, fun w h => ?_⟩
      · rw [hm7 C hC, aggOpt_eq_none] at h
        rw [← coe_toList_map, h]; rfl
      · rw [hm7 C hC] at h
        rw [← coe_toList_map]; exact aggOf_aggOpt h)
  refine ⟨fun h => ?_, fun w h => ?_⟩
  · rw [aggOpt_eq_none, Multiset.toList_eq_nil] at h
    exact hb.1.1 h
  · have := aggOf_aggOpt h
    rw [Multiset.coe_toList] at this
    exact hb.2 w this

omit [Fintype V] in
lemma maInput_edata (C : Finset (Sym2 V)) (e : Sym2 V) :
    (maInput I (.inr C)).edata e =
      if e ∈ C ∧ I.pres e = true then some (I.con e, I.zf e) else none := rfl

lemma aggCon_eq {C : Finset (Sym2 V)} (hC : C ⊆ G.edgeFinset) {y : V → Option (Msg V)}
    (hy : ∀ v, y v = if v ∈ nodes C ∧ v ∈ I.S then some [] else none) :
    aggCon C (maInput I (.inr C)).edata y = ccl G I C := by
  ext e
  simp only [aggCon, ccl]
  rw [mem_filter, mem_filter]
  simp only [MAInst.mem_cedges, MAInst.mem_edges, maInput_edata]
  by_cases he : e ∈ C
  · have hv : ∀ v ∈ e, (y v).isSome = true ↔ v ∈ I.S := by
      intro v hve
      rw [hy v]
      have : v ∈ nodes C := mem_nodes.2 ⟨e, he, hve⟩
      by_cases hvS : v ∈ I.S <;> simp [this, hvS]
    have hv' : (∀ v ∈ e, (y v).isSome = true) ↔ ∀ v ∈ e, v ∈ I.S :=
      ⟨fun h v hve => (hv v hve).1 (h v hve), fun h v hve => (hv v hve).2 (h v hve)⟩
    rw [hv']
    by_cases hp : I.pres e = true
    · simp [he, hp, conBit, hC he]; tauto
    · simp [he, hp, conBit, hC he]
  · simp [he]

lemma maCrossP_eq {C : Finset (Sym2 V)} (hC : C ⊆ G.edgeFinset) {y : V → Option (Msg V)}
    (root : V → V) (Y : V → Msg V)
    (hy : ∀ v, y v = if v ∈ nodes C ∧ v ∈ I.S then some (Word.id (root v) :: Y v) else none)
    (u : V) : maCrossP C (maInput I (.inr C)).edata y u = mcross G I root C u := by
  ext u'
  simp only [maCrossP, mcross]
  rw [mem_filter, mem_filter]
  simp only [mem_univ, true_and, MAInst.mem_edges, maInput_edata]
  by_cases he : s(u, u') ∈ C
  · have hu : u ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_left u u'⟩
    have hu' : u' ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_right u u'⟩
    rw [hy u, hy u']
    by_cases huS : u ∈ I.S <;> by_cases hu'S : u' ∈ I.S <;>
      by_cases hp : I.pres s(u, u') = true <;> simp [he, hu, hu', huS, hu'S, hp, hC he]
  · simp [he]

lemma msg7_eq {C : Finset (Sym2 V)} (hC : C ⊆ G.edgeFinset) {y : V → Option (Msg V)}
    (root : V → V) (Y : V → Msg V)
    (hy : ∀ v, y v = if v ∈ nodes C ∧ v ∈ I.S then some (Word.id (root v) :: Y v) else none)
    (u : V) : msg7 C (maInput I (.inr C)).edata I.op₂ y u =
      aggOpt I.op₂ ((mcross G I root C u).toList.map (fun u' => I.zf s(u, u') u (Y u) (Y u'))) := by
  unfold msg7
  rw [maCrossP_eq hC root Y hy u]
  congr 1
  apply List.map_congr_left
  intro u' hu'
  rw [Finset.mem_toList] at hu'
  simp only [mcross, mem_filter, MAInst.mem_edges] at hu'
  obtain ⟨-, he, ⟨-, hS, hp⟩, -⟩ := hu'
  have hu : u ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_left u u'⟩
  have hu' : u' ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_right u u'⟩
  have huS := hS u (Sym2.mem_mk_left u u')
  have hu'S := hS u' (Sym2.mem_mk_right u u')
  simp [maInput_edata, he, hp, zfun, tl, hy u, hy u', hu, hu', huS, hu'S]

end Local

lemma mcross_agg_small {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {I : MAInst V} {b B : ℕ} (hI : I.Small b B) (root : V → V)
    (Y : V → Msg V) (hY : ∀ v ∈ I.S, (Y v).Small b B) (C : Finset (Sym2 V)) (u : V) (m : Msg V)
    (h : aggOpt I.op₂ ((mcross G I root C u).toList.map
      (fun u' => I.zf s(u, u') u (Y u) (Y u'))) = some m) :
    m.Small b B ∧ u ∈ I.S ∧ u ∈ nodes C := by
  have hmem : ∀ u' ∈ mcross G I root C u, s(u, u') ∈ C ∧ u ∈ I.S ∧ u' ∈ I.S := by
    intro u' hu'
    simp only [mcross, mem_filter, mem_univ, true_and, MAInst.mem_edges] at hu'
    exact ⟨hu'.1, hu'.2.1.2.1 u (Sym2.mem_mk_left u u'), hu'.2.1.2.1 u' (Sym2.mem_mk_right u u')⟩
  have hne : (mcross G I root C u).toList.map (fun u' => I.zf s(u, u') u (Y u) (Y u')) ≠ [] := by
    intro h0; rw [h0] at h; simp [aggOpt] at h
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨u0, hu0, -⟩ := List.mem_map.1 hz
  have h0 := hmem u0 (Finset.mem_toList.1 hu0)
  refine ⟨AggOf.pred (fun a b ha hb => (hI.2.1 a b ha hb).2) (aggOf_aggOpt h) (fun m hm => ?_),
    h0.2.1, mem_nodes.2 ⟨_, h0.1, Sym2.mem_mk_left u u0⟩⟩
  rw [Multiset.mem_coe] at hm
  obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hm
  have h1 := hmem u' (Finset.mem_toList.1 hu')
  exact hI.2.2 _ _ _ _ (hY u h1.2.1) (hY u' h1.2.2)

/-! ## Correctness of the simulation -/

/-- The simulation `maAlg` solves the Minor-Aggregation round `I`, given the specifications of
the building blocks (instantiated for the network at hand). The cost is the sum of the costs of the
building blocks. -/
theorem ma_correct (T : Toolkit) {Aup Adn : ℕ → T.Alg} {Anot Agh : T.Alg} {Atc : ℕ → T.Alg}
    {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (E : Overlays V) (j sz : ℕ)
    (Pt : Finset V) (I : MAInst V) (b B ov d X : ℕ)
    (hE : OverlayProps N.G E ov d X) (hI : I.Small b B)
    (pUp pDn pTc : ℕ → Prof V) (pNot pGh : Prof V) (δu δd : ℝ) (hδu : 0 ≤ δu) (hδd : 0 ≤ δd)
    (hUp : ∀ (μ : ℕ) (x : Agent V → Option (Msg V)), (∀ v, x (.inl v) ≠ none → v ∈ I.S) →
      (∀ v m, x (.inl v) = some m → m.Small μ B) →
      T.Impl (Aup μ) N (.io E j sz Pt (Option (Msg V)) (V → Option (Msg V)) x
        (fun y => ∀ C ∈ E.cl, ∀ v, y (.inr C) v = if v ∈ nodes C then x (.inl v) else none))
        (pUp μ) δu)
    (hDn : ∀ (μ : ℕ) (x : Agent V → V → Option (Msg V)),
      (∀ C ∈ E.cl, ∀ v, x (.inr C) v ≠ none → v ∈ I.S ∧ v ∈ nodes C) →
      (∀ C ∈ E.cl, ∀ v m, x (.inr C) v = some m → m.Small μ B) →
      T.Impl (Adn μ) N (.io E j sz Pt (V → Option (Msg V)) (Multiset (Msg V)) x
        (fun y => ∀ v, y (.inl v) = (clustersOf E.cl v).val.filterMap (fun C => x (.inr C) v)))
        (pDn μ) δd)
    (hNot : ∀ (x : Agent V → Finset V),
      (∀ v, ∀ u ∈ x (.inl v), v ∈ I.S ∧ N.G.Adj v u ∧ s(v, u) ∈ forestF N.G E.cl I) →
      T.Impl Anot N (.io E j sz Pt (Finset V) (Finset V) x
        (fun y => ∀ v, y (.inl v) = univ.filter (fun u => v ∈ x (.inl u)))) pNot 0)
    (hGh : ∀ (x : Agent V → Option (Finset V)),
      (∀ v, x (.inl v) = if v ∈ I.S then some (nbrsIn (forestF N.G E.cl I) v) else none) →
      T.Impl Agh N (.io E j sz Pt (Option (Finset V)) (Option V × V) x
        (fun y => SpanForest I.S (forestF N.G E.cl I) (fun v => (y (.inl v)).1)
          (fun v => (y (.inl v)).2))) pGh 0)
    (hTc : ∀ (b' : ℕ) (par : V → Option V) (root : V → V) (val : V → Msg V)
      (op : Msg V → Msg V → Msg V) (x : Agent V → TcIn V),
      (∀ v, x (.inl v) = if v ∈ I.S then some (par v, root v, val v, op) else none) →
      (∀ v ∈ I.S, ∀ u, par v = some u → u ∈ I.S ∧ s(v, u) ∈ forestF N.G E.cl I) →
      (∀ v ∈ I.S, ∀ u, par v = some u → root u = root v) →
      (∀ v ∈ I.S, par v = none → root v = v) →
      (∃ r : V → ℕ, ∀ v ∈ I.S, ∀ u, par v = some u → r u < r v) →
      (∀ v ∈ I.S, (val v).Small b' B) →
      (∀ m m', m.Small b' B → m'.Small b' B → (op m m').Small b' B) →
      T.Impl (Atc b') N (.io E j sz Pt (TcIn V) (Option (Msg V)) x
        (fun y => ∀ v ∈ I.S, ∃ Y, y (.inl v) = some Y ∧
          AggOf op ((I.S.filter (fun u => root u = root v)).val.map val) Y ∧
          ∀ u ∈ I.S, root u = root v → y (.inl u) = some Y)) (pTc b') 0) :
    T.Impl (maAlg T Aup Adn Anot Agh Atc b) N (maTask N.G E j sz Pt I)
      (pUp 0 + (pDn 1 + (pNot + (pGh + (pTc b + (pUp (b + 1) + (pDn b + (pTc (b + 1) + 0))))))))
      (δu + (δd + (0 + (0 + (0 + (δu + (δd + (0 + 0)))))))) := by
  unfold maAlg
  -- step 1: membership messages to the aggregators
  refine T.bind (stage T L1 (s := maInput I) (hUp 0 _ ?_ ?_)) ?_ (by linarith)
  · intro v hv
    simpa [L1, maInput] using hv
  · intro v m hm
    simp only [L1, maInput, decide_eq_true_eq] at hm
    split_ifs at hm
    cases hm
    exact ⟨by simp, fun k hk => by simp at hk⟩
  intro y1 hy1
  have hy1' : ∀ C ∈ E.cl, ∀ v, y1 (.inr C) v = if v ∈ nodes C ∧ v ∈ I.S then some [] else none := by
    intro C hC v
    rw [hy1 C hC v]
    simp [L1, maInput, ite_and]
  clear hy1
  -- step 2: per-cluster forests, parents to the nodes
  have hx2 : ∀ C ∈ E.cl, ∀ v, L2.f V (.inr C) (lview N (.inr C)) (maInput I (.inr C), y1 (.inr C)) v
      = (fpar (ccl N.G I C) v).map (fun u => [Word.id u]) := by
    intro C hC v
    show (fpar (aggCon C _ (y1 (.inr C))) v).map _ = _
    rw [aggCon_eq (hE.sub C hC) (hy1' C hC)]
  refine T.bind (stage T L2 (s := fun g => (maInput I g, y1 g)) (hDn 1 _ ?_ ?_)) ?_
    (by linarith)
  · intro C hC v h
    rw [hx2 C hC v] at h
    cases hf : fpar (ccl N.G I C) v with
    | none => simp [hf] at h
    | some u =>
      have := fpar_ccl hf
      exact ⟨(MAInst.mem_edges.1 (cedges_sub_edges this.2)).2.1 v (Sym2.mem_mk_left v u),
        mem_nodes.2 ⟨_, this.1, Sym2.mem_mk_left v u⟩⟩
  · intro C hC v m h
    rw [hx2 C hC v] at h
    cases hf : fpar (ccl N.G I C) v with
    | none => simp [hf] at h
    | some u =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨by simp, fun k hk => by simp at hk⟩
  intro y2 hy2
  have hpar : ∀ v u, u ∈ parentsOf (y2 (.inl v)) ↔ ∃ C ∈ E.cl, fpar (ccl N.G I C) v = some u := by
    intro v u
    simp only [parentsOf, mem_filter, mem_univ, true_and]
    rw [hy2 v, Multiset.mem_filterMap]
    constructor
    · rintro ⟨C, hC, h⟩
      have hC' := (mem_filter.1 hC).1
      rw [hx2 C hC' v] at h
      cases hf : fpar (ccl N.G I C) v with
      | none => simp [hf] at h
      | some u' =>
        simp only [hf, Option.map_some, Option.some.injEq, List.cons.injEq, Word.id.injEq,
          and_true] at h
        exact ⟨C, hC', h ▸ hf⟩
    · rintro ⟨C, hC, hf⟩
      have := fpar_ccl hf
      refine ⟨C, mem_filter.2 ⟨hC, mem_nodes.2 ⟨_, this.1, Sym2.mem_mk_left v u⟩⟩, ?_⟩
      rw [hx2 C hC v, hf]; rfl
  -- step 3: notify the parents
  refine T.bind (stage T L3 (s := fun g => ((maInput I g, y1 g), y2 g)) (hNot _ ?_)) ?_
    (by linarith)
  · intro v u hu
    change u ∈ parentsOf (y2 (.inl v)) at hu
    obtain ⟨C, hC, hf⟩ := (hpar v u).1 hu
    have := fpar_ccl hf
    have hE' := MAInst.mem_edges.1 (cedges_sub_edges this.2)
    exact ⟨hE'.2.1 v (Sym2.mem_mk_left v u), SimpleGraph.mem_edgeFinset.1 hE'.1,
      mem_forestF.2 ⟨C, hC, v, u, hf, rfl⟩⟩
  intro y3 hy3
  have hy3' : ∀ v, y3 (.inl v) = univ.filter (fun u => v ∈ parentsOf (y2 (.inl u))) := hy3
  have hch : ∀ v u, u ∈ y3 (.inl v) ↔ ∃ C ∈ E.cl, fpar (ccl N.G I C) u = some v := by
    intro v u
    rw [hy3' v, mem_filter]
    simp only [mem_univ, true_and]
    exact hpar u v
  have hnb : ∀ v, parentsOf (y2 (.inl v)) ∪ y3 (.inl v) = nbrsIn (forestF N.G E.cl I) v := by
    intro v; ext u
    rw [mem_union, hpar, hch]
    simp only [nbrsIn, mem_filter, mem_univ, true_and, mem_forestF]
    constructor
    · rintro (⟨C, hC, hf⟩ | ⟨C, hC, hf⟩)
      · exact ⟨C, hC, v, u, hf, rfl⟩
      · exact ⟨C, hC, u, v, hf, Sym2.eq_swap⟩
    · rintro ⟨C, hC, a, c, hf, he⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨C, hC, hf⟩
      · exact Or.inr ⟨C, hC, hf⟩
  -- step 4: GHS on the union of the forests
  refine T.bind (stage T L4 (s := fun g => (((maInput I g, y1 g), y2 g), y3 g)) (hGh _ ?_))
    ?_ (by linarith)
  · intro v
    show (if decide (v ∈ I.S) = true then some (parentsOf (y2 (.inl v)) ∪ y3 (.inl v))
      else none) = _
    rw [hnb v]; simp
  intro y4 hy4
  set par : V → Option V := fun v => (y4 (.inl v)).1 with hpar_def
  set root : V → V := fun v => (y4 (.inl v)).2 with hroot_def
  have hroot : ∀ u ∈ I.S, ∀ w ∈ I.S, (root u = root w ↔ EReach (I.cedges N.G) u w) := by
    intro u hu w hw
    rw [hy4.conn u hu w hw, EReach_forestF hE.valid.cover]
  -- step 5: consensus values
  refine T.bind (stage T L5 (s := fun g => ((((maInput I g, y1 g), y2 g), y3 g), y4 g))
    (hTc b par root I.x I.op₁ _ ?_ (fun v hv u h => ⟨hy4.mem v hv u h, hy4.edge v hv u h⟩)
      hy4.root_par hy4.root_self hy4.rank (fun v _ => hI.1 v)
      (fun m m' hm hm' => (hI.2.1 m m' hm hm').1))) ?_ (by linarith)
  · intro v
    show (if decide (v ∈ I.S) = true then some ((y4 (.inl v)).1, (y4 (.inl v)).2, I.x v, I.op₁)
      else none) = _
    simp only [decide_eq_true_eq]; rfl
  intro y5 hy5
  set Y : V → Msg V := fun v => (y5 (.inl v)).getD [] with hY_def
  have hY5 : ∀ v ∈ I.S, y5 (.inl v) = some (Y v) := by
    intro v hv; obtain ⟨Yv, h, -⟩ := hy5 v hv; simp [hY_def, h]
  have hYagg : ∀ v ∈ I.S,
      AggOf I.op₁ ((I.S.filter (fun u => root u = root v)).val.map I.x) (Y v) := by
    intro v hv
    obtain ⟨Yv, h, ha, -⟩ := hy5 v hv
    have : Yv = Y v := Option.some.inj (h.symm.trans (hY5 v hv))
    rw [← this]; exact ha
  have hYc : ∀ u ∈ I.S, ∀ v ∈ I.S, root u = root v → Y u = Y v := by
    intro u hu v hv hr
    obtain ⟨Yv, h, -, hc⟩ := hy5 v hv
    have h1 := Option.some.inj ((hY5 u hu).symm.trans (hc u hu hr))
    have h2 := Option.some.inj ((hY5 v hv).symm.trans h)
    rw [h1, h2]
  have hYs : ∀ v ∈ I.S, (Y v).Small b B := by
    intro v hv
    refine AggOf.pred (fun a c ha hc => (hI.2.1 a c ha hc).1) (hYagg v hv) (fun m hm => ?_)
    obtain ⟨u, -, rfl⟩ := Multiset.mem_map.1 hm
    exact hI.1 u
  -- step 6: roots and consensus values to the aggregators
  refine T.bind (stage T L6 (s := fun g => (((((maInput I g, y1 g), y2 g), y3 g), y4 g), y5 g))
    (hUp (b + 1) _ ?_ ?_)) ?_ (by linarith)
  · intro v hv
    simpa [L6, maInput] using hv
  · intro v m hm
    simp only [L6, maInput, decide_eq_true_eq] at hm
    split_ifs at hm with hv
    cases hm
    exact Msg.small_cons (hYs v hv) (fun k hk => by cases hk)
  intro y6 hy6
  have hy6' : ∀ C ∈ E.cl, ∀ v, y6 (.inr C) v =
      if v ∈ nodes C ∧ v ∈ I.S then some (Word.id (root v) :: Y v) else none := by
    intro C hC v
    rw [hy6 C hC v]
    simp [L6, maInput, ite_and, hroot_def, hY_def]
  clear hy6
  -- step 7: partial aggregates at the aggregators
  have hx7 : ∀ C ∈ E.cl, ∀ u, L7.f V (.inr C) (lview N (.inr C))
      ((((((maInput I (.inr C), y1 (.inr C)), y2 (.inr C)), y3 (.inr C)), y4 (.inr C)),
        y5 (.inr C)), y6 (.inr C)) u =
      aggOpt I.op₂ ((mcross N.G I root C u).toList.map
        (fun u' => I.zf s(u, u') u (Y u) (Y u'))) := by
    intro C hC u
    exact msg7_eq (hE.sub C hC) root Y (hy6' C hC) u
  refine T.bind (stage T L7
    (s := fun g => ((((((maInput I g, y1 g), y2 g), y3 g), y4 g), y5 g), y6 g))
    (hDn b _ ?_ ?_)) ?_ (by linarith)
  · intro C hC u h
    rw [hx7 C hC u] at h
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 h
    exact (mcross_agg_small hI root Y hYs C u m hm).2
  · intro C hC u m h
    rw [hx7 C hC u] at h
    exact (mcross_agg_small hI root Y hYs C u m h).1
  intro y7 hy7
  set zopt : V → Option (Msg V) := fun v => aggOpt I.op₂ (y7 (.inl v)).toList with hzopt_def
  have hzopt : ∀ u ∈ I.S,
      (zopt u = none → zU N.G E.cl I root (fun a c => I.zf s(a, c) a (Y a) (Y c)) u = 0) ∧
      ∀ w, zopt u = some w →
        AggOf I.op₂ (zU N.G E.cl I root (fun a c => I.zf s(a, c) a (Y a) (Y c)) u) w := by
    intro u _
    simp only [hzopt_def]
    rw [hy7 u]
    exact zopt_spec E.cl root (fun a c => I.zf s(a, c) a (Y a) (Y c)) u I.op₂ _
      (fun C hC => hx7 C (mem_filter.1 hC).1 u)
  have hzs : ∀ v w, zopt v = some w → w.Small b B := by
    intro v w h
    simp only [hzopt_def] at h
    have ha := aggOf_aggOpt h
    rw [Multiset.coe_toList] at ha
    refine AggOf.pred (fun a c ha hc => (hI.2.1 a c ha hc).2) ha (fun m hm => ?_)
    rw [hy7 v, Multiset.mem_filterMap] at hm
    obtain ⟨C, hC, hm⟩ := hm
    rw [hx7 C (mem_filter.1 hC).1 v] at hm
    exact (mcross_agg_small hI root Y hYs C v m hm).1
  -- step 8: supernode aggregates with the lifted operator
  refine T.bind (stage T L8
    (s := fun g => (((((((maInput I g, y1 g), y2 g), y3 g), y4 g), y5 g), y6 g), y7 g))
    (hTc (b + 1) par root (fun v => encO (zopt v)) (liftOp I.op₂) _ ?_
      (fun v hv u h => ⟨hy4.mem v hv u h, hy4.edge v hv u h⟩) hy4.root_par hy4.root_self hy4.rank
      (fun v _ => small_encO (hzs v))
      (fun m m' hm hm' => small_liftOp (fun a c ha hc => (hI.2.1 a c ha hc).2) hm hm')))
    ?_ (by linarith)
  · intro v
    show (if decide (v ∈ I.S) = true then some ((y4 (.inl v)).1, (y4 (.inl v)).2,
      encO (aggOpt I.op₂ (y7 (.inl v)).toList), liftOp I.op₂) else none) = _
    simp only [decide_eq_true_eq]; rfl
  intro y8 hy8
  -- output
  refine T.weakenIO (fun o ho => ?_) (T.locR Lfin N E j sz Pt _)
  refine final_spec hE I root hroot Y zopt o ?_ hYagg hYc ?_ hzopt ?_
  · intro v hv; rw [ho]; exact hY5 v hv
  · intro C hC e he heC u hu
    rw [ho]
    show (y6 (.inr C) u).map List.tail = _
    have hun : u ∈ nodes C := mem_nodes.2 ⟨e, heC, hu⟩
    have huS : u ∈ I.S := (MAInst.mem_edges.1 he).2.1 u hu
    rw [hy6' C hC u, ite_eq_left ⟨hun, huS⟩]; rfl
  · intro v hv
    obtain ⟨a, ha, hagg, hc⟩ := hy8 v hv
    refine ⟨a, ?_, hagg, fun u hu hr => ?_⟩
    · rw [ho]; show (y8 (.inl v)).bind decO = _; rw [ha]; rfl
    · rw [ho]; show (y8 (.inl u)).bind decO = _; rw [hc u hu hr]; rfl

/-! ## Costs -/

section Cost
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {E : Overlays V} {ov d X : ℕ}

/-- Cost of one node-to-aggregator or aggregator-to-node exchange of `μ`-word messages on the
aggregator edges of `S` (Lemma 2.2 with the subset congestion of Theorem 3.10), with the public
round budget `K·(μ+1)·(dil+1)·(sz+1)` and `K'·(μ+1)` words per message and path edge (`K' ≤ K`). -/
lemma aggCost_le (hE : OverlayProps G E ov d X) (j sz : ℕ) (S : Finset V) (K K' μ : ℕ)
    (hK : K' ≤ K) :
    Prof.mk (K * (μ + 1) * (E.dil + 1) * (sz + 1)) ((K' * (μ + 1)) • E.rhoAgg j S)
        (K' * (μ + 1) * E.aggLen j S) ≤
      szProf G E j sz S ((μ + 1) * (K * (d + 1 + ov * d) + 1)) := by
  unfold szProf
  have hdil := dil_le_of_props hE
  have hKd : K ≤ K * (d + 1 + ov * d) := Nat.le_mul_of_pos_right K (by omega)
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
  · simp only [Prof.rounds_mk]
    have h : K * (μ + 1) * (E.dil + 1) * (sz + 1) = (μ + 1) * (K * (E.dil + 1)) * (sz + 1) := by
      ring
    rw [h]
    refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
    have : K * (E.dil + 1) ≤ K * (d + 1 + ov * d) := Nat.mul_le_mul_left _ (by omega)
    omega
  · simp only [Prof.load_mk, Pi.smul_apply, smul_eq_mul]
    have h1 := rhoAgg_le_rho (G := G) E j S e
    calc K' * (μ + 1) * E.rhoAgg j S e ≤ K * (μ + 1) * E.rho G j S e :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hK) h1
      _ ≤ (μ + 1) * (K * (d + 1 + ov * d) + 1) * E.rho G j S e := by
          apply Nat.mul_le_mul_right
          rw [mul_comm K]
          exact Nat.mul_le_mul_left _ (by omega)
  · simp only [Prof.msgs_mk]
    have h1 := aggLen_le hE j S
    have h2 : K * (ov * d) ≤ K * (d + 1 + ov * d) := Nat.mul_le_mul_left _ (by omega)
    calc K' * (μ + 1) * E.aggLen j S ≤ K * (μ + 1) * (ov * d * S.card) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hK) h1
      _ = (μ + 1) * (K * (ov * d)) * S.card := by ring
      _ ≤ (μ + 1) * (K * (d + 1 + ov * d) + 1) * (S.card + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

/-- Cost of an algorithm sending at most `x` messages over every edge of a subgraph `F` of
`G[S]` with `|F| ≤ ov·|S|` (notify, GHS, tree convergecast/broadcast). -/
lemma forestCost_le (j sz : ℕ) {S : Finset V} {F : Finset (Sym2 V)} (hF : F ⊆ G.edgeFinset)
    (hFS : ∀ e ∈ F, ∀ v ∈ e, v ∈ S) (hFc : F.card ≤ ov * S.card) (x r m Q : ℕ)
    (hr : r ≤ x * (sz + 1)) (hm : m ≤ x * (F.card + S.card + 1)) (hQ : x * (ov + 1) ≤ Q) :
    Prof.mk r (onEdges F x) m ≤ szProf G E j sz S Q := by
  unfold szProf
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
  · simp only [Prof.rounds_mk]
    refine hr.trans (Nat.mul_le_mul_right _ ((Nat.le_mul_of_pos_right x (by omega)).trans hQ))
  · simp only [Prof.load_mk]
    refine (onEdges_le_rho E j hF hFS x e).trans (Nat.mul_le_mul_right _ ?_)
    exact (Nat.le_mul_of_pos_right x (by omega)).trans hQ
  · simp only [Prof.msgs_mk]
    refine hm.trans ?_
    calc x * (F.card + S.card + 1) ≤ x * ((ov + 1) * (S.card + 1)) :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = x * (ov + 1) * (S.card + 1) := by ring
      _ ≤ Q * (S.card + 1) := Nat.mul_le_mul_right _ hQ

end Cost

/-- **Lemma 4.2**. -/
theorem lemma_4_2 (T : Toolkit) : Lemma_4_2 T := by
  intro c Bw fov fd hov hd
  obtain ⟨Ka, ka, Kδa, Aa, hA⟩ := T.aggUp c Bw
  obtain ⟨Kd, kd, Kδd, Ad, hD⟩ := T.aggDown c Bw
  obtain ⟨An, hN⟩ := T.notify
  obtain ⟨Kg, Ag, hG⟩ := T.ghs
  obtain ⟨Kt, At, hT⟩ := T.treeCast Bw
  have hd1 : IsPL (fun ν => fd ν + 1) := hd.add (IsPL.const 1)
  have hXa : IsPL (fun ν => Ka * lg ν ^ ka * (fd ν + 1 + fov ν * fd ν) + 1) :=
    (((IsPL.const Ka).mul (IsPL.lgpow ka)).mul (hd1.add (hov.mul hd))).add (IsPL.const 1)
  have hXd : IsPL (fun ν => Kd * lg ν ^ kd * (fd ν + 1 + fov ν * fd ν) + 1) :=
    (((IsPL.const Kd).mul (IsPL.lgpow kd)).mul (hd1.add (hov.mul hd))).add (IsPL.const 1)
  have ho1 : IsPL (fun ν => fov ν + 1) := hov.add (IsPL.const 1)
  refine ⟨fun ν => 3 * (Ka * lg ν ^ ka * (fd ν + 1 + fov ν * fd ν) + 1) +
      3 * (Kd * lg ν ^ kd * (fd ν + 1 + fov ν * fd ν) + 1) + 2 * (fov ν + 1) +
      Kg * lg ν * (fov ν + 1) + 3 * (Kt * (fov ν + 1)),
    ((((hXa.smul 3).add (hXd.smul 3)).add (ho1.smul 2)).add
      (((IsPL.const Kg).mul IsPL.lg').mul ho1)).add (((IsPL.const Kt).mul ho1).smul 3),
    2 * Kδa + 2 * Kδd, fun ν b => maAlg T (Aa ν) (Ad ν) An (Ag ν) (At ν) b, ?_⟩
  intro V _ _ N ν hν hνn E X hE j sz I b hj hsz hI Pt hPt
  have hFsub := forestF_sub (G := N.G) (I := I) E.cl
  have hFS := forestF_S (G := N.G) (I := I) E.cl
  have hFc : (forestF N.G E.cl I).card ≤ fov ν * I.S.card := forestF_card hE.overlap
  have hSPt : I.S ⊆ Pt := (subset_footprint E j I.S).trans hPt
  have hKa : Ka ≤ Ka * lg ν ^ ka := Nat.le_mul_of_pos_right Ka (Nat.one_le_pow _ _ (lg_pos ν))
  have hKd : Kd ≤ Kd * lg ν ^ kd := Nat.le_mul_of_pos_right Kd (Nat.one_le_pow _ _ (lg_pos ν))
  have hM := ma_correct T N E j sz Pt I b (ν ^ Bw) (fov ν) (fd ν) X hE hI
    (fun μ => szProf N.G E j sz I.S
      ((μ + 1) * (Ka * lg ν ^ ka * (fd ν + 1 + fov ν * fd ν) + 1)))
    (fun μ => szProf N.G E j sz I.S
      ((μ + 1) * (Kd * lg ν ^ kd * (fd ν + 1 + fov ν * fd ν) + 1)))
    (fun b' => szProf N.G E j sz I.S (Kt * (fov ν + 1) * (b' + 1)))
    (szProf N.G E j sz I.S (2 * (fov ν + 1)))
    (szProf N.G E j sz I.S (Kg * lg ν * (fov ν + 1)))
    (whp Kδa c ν) (whp Kδd c ν) (whp_nonneg _ _ _) (whp_nonneg _ _ _)
    (fun μ x h1 h2 => T.mono (hA N ν hν hνn E j sz Pt I.S μ x hE.valid hj hsz hPt h1 h2)
      (aggCost_le hE j sz I.S _ _ μ hKa) le_rfl)
    (fun μ x h1 h2 => T.mono (hD N ν hν hνn E j sz Pt I.S μ x hE.valid hj hsz hPt h1 h2)
      (aggCost_le hE j sz I.S _ _ μ hKd) le_rfl)
    (fun x hx => T.mono (hN N E j sz Pt I.S _ x hx
        (fun v u hu => hSPt (hFS _ (hx v u hu).2.2 u (Sym2.mem_mk_right v u))) hSPt)
      (forestCost_le j sz hFsub hFS hFc 2 1 _ _ (by nlinarith) (by nlinarith) le_rfl) le_rfl)
    (fun x hx => T.mono (hG N ν hν hνn E j sz Pt I.S _ x hFsub hFS hsz hSPt hx)
      (forestCost_le j sz hFsub hFS hFc _ _ _ _ le_rfl (Nat.mul_le_mul_left _ (by omega)) le_rfl)
      le_rfl)
    (fun b' par root val op x hx hpar hrp hrs hrk hval hop =>
      T.mono (hT N ν hνn E j sz Pt I.S b' par root val op _ x hx hsz hSPt hFsub hpar hrp hrs hrk
        hval hop)
        (forestCost_le j sz hFsub hFS hFc _ _ _ _ le_rfl (Nat.mul_le_mul_left _ (by omega))
          (le_of_eq (by ring))) le_rfl)
  refine T.mono hM ?_ ?_
  · simp only [add_zero, szProf_add]
    apply szProf_mono_Q
    generalize Ka * lg ν ^ ka * (fd ν + 1 + fov ν * fd ν) + 1 = A
    generalize Kd * lg ν ^ kd * (fd ν + 1 + fov ν * fd ν) + 1 = D
    generalize Kg * lg ν * (fov ν + 1) = G'
    generalize Kt * (fov ν + 1) = H
    generalize fov ν = o
    nlinarith [Nat.zero_le (A * b), Nat.zero_le (D * b), Nat.zero_le (o * b), Nat.zero_le (G' * b),
      Nat.zero_le (H * b)]
  · have : whp (2 * Kδa + 2 * Kδd) c ν = 2 * whp Kδa c ν + 2 * whp Kδd c ν := by
      unfold whp; push_cast; ring
    rw [this]
    simp only [add_zero, zero_add]
    linarith

end APSP.Stoc
