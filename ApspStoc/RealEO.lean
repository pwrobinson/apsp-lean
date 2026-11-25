import ApspStoc.Sec5EOAux

/-!
# Realizability of the Eulerian-orientation specification

`eoSpec_realizable`: every well-formed Eulerian-orientation instance (with virtual nodes) has an
orientation satisfying `EOSpec`.

Proof: darts (edge–endpoint incidences) of all physical, physical–virtual and virtual–virtual
edges; the edge involution `eps` swaps the two darts of an edge, and at every vertex (physical or
virtual) the darts are paired by a fixed-point-free involution (the degrees are even). By
`dart_orient` there is a colouring of the darts that differs along both involutions
(`true` = the edge leaves the vertex); the pairing at a vertex matches its out-darts with its
in-darts, which gives the balance equations.
-/

namespace APSP.Stoc

open APSP Finset

namespace RealEO

/-! ## List and sum facts -/

lemma len_filter_zip_range {α β : Type*} (l : List α) (x0 : α) (g : ℕ → β) (p : α × β → Bool) :
    ((l.zip ((List.range l.length).map g)).filter p).length =
      ∑ t ∈ range l.length, if p (l.getD t x0, g t) then 1 else 0 := by
  induction l generalizing g with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.zip_cons_cons,
      List.filter_cons, Finset.sum_range_succ']
    have := ih (g ∘ Nat.succ)
    simp only [List.getD_cons_succ, List.getD_cons_zero, Function.comp_apply] at this ⊢
    split_ifs with h
    · simp [this]
    · simp [this]

lemma sum_range_getD {α M : Type*} [AddCommMonoid M] (l : List α) (x0 : α) (f : α → M) :
    ∑ t ∈ range l.length, f (l.getD t x0) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    exact add_comm _ _

lemma sum_range_getD_count (l : List ℕ) (i : ℕ) :
    ∑ t ∈ range l.length, (if l.getD t 0 = i then 1 else 0) = l.count i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.count_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, beq_iff_eq]

lemma count_map_range (n : ℕ) (g : ℕ → Bool) (b : Bool) :
    ((List.range n).map g).count b = ∑ k ∈ range n, if g k = b then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, Finset.sum_range_succ, ih]
    simp [List.count_cons]


lemma bool_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

section Darts

variable {V : Type} [Fintype V] [DecidableEq V]

/-- darts: physical `(e, v)`; virtual links `⟨v, k, b⟩` (`b = false`: at `v`, `true`: at the
virtual node `(vv v)[k]`); virtual–virtual `(t, b)` (`false`: at `uu[t].1`, `true`: at `uu[t].2`) -/
abbrev Dart (V : Type) := (Sym2 V × V) ⊕ (Σ _ : V, ℕ × Bool) ⊕ (ℕ × Bool)

/-- the vertex of a dart -/
noncomputable def vx (H : EOInst V) : Dart V → V ⊕ ℕ
  | .inl p => .inl p.2
  | .inr (.inl ⟨v, k, b⟩) => if b then .inr ((H.vv v).getD k 0) else .inl v
  | .inr (.inr (t, b)) => .inr (if b then (H.uu.getD t (0, 0)).2 else (H.uu.getD t (0, 0)).1)

/-- the other dart of the same edge -/
noncomputable def eps : Dart V → Dart V
  | .inl p => .inl (p.1, oth p.2 p.1)
  | .inr (.inl ⟨v, k, b⟩) => .inr (.inl ⟨v, k, !b⟩)
  | .inr (.inr (t, b)) => .inr (.inr (t, !b))

/-- all darts of the instance -/
noncomputable def DD (H : EOInst V) : Finset (Dart V) :=
  ((H.Hp ×ˢ univ).filter (fun p : Sym2 V × V => p.2 ∈ p.1)).disjSum
    ((H.S.sigma (fun v => range (H.vv v).length ×ˢ (univ : Finset Bool))).disjSum
      (range H.uu.length ×ˢ univ))

lemma sum_DD (H : EOInst V) (f : Dart V → ℕ) : ∑ d ∈ DD H, f d =
    (∑ e ∈ H.Hp, ∑ u ∈ univ.filter (fun u => u ∈ e), f (.inl (e, u))) +
    ((∑ v ∈ H.S, ∑ k ∈ range (H.vv v).length,
        (f (.inr (.inl ⟨v, k, false⟩)) + f (.inr (.inl ⟨v, k, true⟩)))) +
      ∑ t ∈ range H.uu.length, (f (.inr (.inr (t, false))) + f (.inr (.inr (t, true))))) := by
  rw [DD, sum_disjSum, sum_disjSum, sum_sigma, sum_filter, sum_product]
  simp only [sum_filter, sum_product, Fintype.sum_bool]
  congr 1
  congr 1
  · refine sum_congr rfl (fun v _ => sum_congr rfl (fun k _ => add_comm _ _))
  · refine sum_congr rfl (fun k _ => add_comm _ _)

@[simp] lemma mem_DD_inl (H : EOInst V) (e : Sym2 V) (u : V) :
    (.inl (e, u) : Dart V) ∈ DD H ↔ e ∈ H.Hp ∧ u ∈ e := by simp [DD]

@[simp] lemma mem_DD_vv (H : EOInst V) (v : V) (k : ℕ) (b : Bool) :
    (.inr (.inl ⟨v, k, b⟩) : Dart V) ∈ DD H ↔ v ∈ H.S ∧ k < (H.vv v).length := by simp [DD]

@[simp] lemma mem_DD_uu (H : EOInst V) (t : ℕ) (b : Bool) :
    (.inr (.inr (t, b)) : Dart V) ∈ DD H ↔ t < H.uu.length := by simp [DD]

lemma card_filter_eq_and {α : Type*} [DecidableEq α] (s : Finset α) (v : α) (Q : α → Prop)
    [DecidablePred Q] : (s.filter (fun u => u = v ∧ Q u)).card = if v ∈ s ∧ Q v then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨v, Finset.eq_singleton_iff_unique_mem.2 ⟨by simp [h.1, h.2], fun u hu => ?_⟩⟩
    exact (Finset.mem_filter.1 hu).2.1
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u hu ⟨rfl, hq⟩
    exact h ⟨hu, hq⟩

lemma cnt_inl (H : EOInst V) (v : V) (P : Dart V → Prop) [DecidablePred P] :
    ((DD H).filter (fun d => vx H d = .inl v ∧ P d)).card =
      (H.Hp.filter (fun e => v ∈ e ∧ P (.inl (e, v)))).card +
      (if v ∈ H.S then ∑ k ∈ range (H.vv v).length,
        (if P (.inr (.inl ⟨v, k, false⟩)) then 1 else 0) else 0) := by
  rw [card_filter, sum_DD]
  simp only [vx]
  simp
  congr 1
  · conv_rhs => rw [Finset.card_filter]
    refine sum_congr rfl (fun e _ => ?_)
    rw [card_filter_eq_and]
    simp
  · have : ∀ x ∈ H.S, ((range (H.vv x).length).filter
        (fun k => x = v ∧ P (.inr (.inl ⟨x, (k, false)⟩)))).card = if x = v then
        ((range (H.vv x).length).filter (fun k => P (.inr (.inl ⟨x, (k, false)⟩)))).card
        else 0 := by
      intro x _
      by_cases hx : x = v
      · subst hx; simp
      · simp [hx]
    rw [sum_congr rfl this, sum_ite_eq']

lemma cnt_inr (H : EOInst V) (i : ℕ) (P : Dart V → Prop) [DecidablePred P] :
    ((DD H).filter (fun d => vx H d = .inr i ∧ P d)).card =
      (∑ v ∈ H.S, ∑ k ∈ range (H.vv v).length,
        if (H.vv v).getD k 0 = i ∧ P (.inr (.inl ⟨v, k, true⟩)) then 1 else 0) +
      ∑ t ∈ range H.uu.length,
        ((if (H.uu.getD t (0, 0)).1 = i ∧ P (.inr (.inr (t, false))) then 1 else 0) +
          (if (H.uu.getD t (0, 0)).2 = i ∧ P (.inr (.inr (t, true))) then 1 else 0)) := by
  rw [card_filter, sum_DD]
  simp [vx]

lemma hp_facts {G : SimpleGraph V} [DecidableRel G.Adj] {H : EOInst V} (hwf : H.WF G)
    {e : Sym2 V} (he : e ∈ H.Hp) : ¬ e.IsDiag ∧ ∀ u ∈ e, u ∈ H.S := by
  have h := hwf.sub he
  simp only [inducedEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at h
  exact ⟨G.not_isDiag_of_mem_edgeSet h.1, h.2⟩

lemma eps_props {G : SimpleGraph V} [DecidableRel G.Adj] {H : EOInst V} (hwf : H.WF G) :
    ∀ d ∈ DD H, eps d ∈ DD H ∧ eps (eps d) = d ∧ eps d ≠ d := by
  rintro (⟨e, u⟩ | ⟨v, k, b⟩ | ⟨t, b⟩) hd
  · rw [mem_DD_inl] at hd
    have hnd := (hp_facts hwf hd.1).1
    simp [eps, oth_mem hd.2, oth_oth hd.2, oth_ne hd.2 hnd, hd.1]
  · rw [mem_DD_vv] at hd; simp [eps, hd]
  · rw [mem_DD_uu] at hd; simp [eps, hd]

lemma even_at {G : SimpleGraph V} [DecidableRel G.Adj] {H : EOInst V} (hwf : H.WF G)
    (w : V ⊕ ℕ) : Even ((DD H).filter (fun d => vx H d = w)).card := by
  rcases w with v | i
  · have h := cnt_inl H v (fun _ => True)
    simp only [and_true, ite_true] at h
    rw [h]
    by_cases hv : v ∈ H.S
    · have := hwf.even_p v hv
      simp only [hv, ite_true]
      have hp : (H.Hp.filter (fun e => v ∈ e)).card = H.pdeg v := by
        unfold EOInst.pdeg; rfl
      rw [hp]; simpa using this
    · have h1 : H.Hp.filter (fun e => v ∈ e) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hve
        exact hv ((hp_facts hwf he).2 v hve)
      simp [hv, h1]
  · have h := cnt_inr H i (fun _ => True)
    simp only [and_true] at h
    rw [h]
    simp only [sum_range_getD_count]
    rw [sum_range_getD H.uu (0, 0) (fun p => (if p.1 = i then 1 else 0) + (if p.2 = i then 1 else 0))]
    change Even (H.vdeg i)
    by_cases hi : i < H.k
    · exact hwf.even_v i hi
    · have : H.vdeg i = 0 := by
        unfold EOInst.vdeg
        rw [Nat.add_eq_zero_iff]
        constructor
        · refine Finset.sum_eq_zero (fun v _ => List.count_eq_zero.2 (fun hm => hi ?_))
          exact hwf.vv_lt v i hm
        · refine List.sum_eq_zero (fun x hx => ?_)
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
          have := hwf.uu_lt p hp
          have h1 : p.1 ≠ i := by omega
          have h2 : p.2 ≠ i := by omega
          simp [h1, h2]
      rw [this]; exact ⟨0, rfl⟩

end Darts

end RealEO

open RealEO in
theorem eoSpec_realizable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (cl : Finset (Finset (Sym2 V))) (H : EOInst V) (hwf : H.WF G) :
    ∃ o : Agent V → EOOut V, EOSpec cl H o := by
  -- a fixed-point-free pairing of the darts at every vertex
  have hpair : ∀ w : V ⊕ ℕ, ∃ σ : Dart V → Dart V,
      (∀ a ∈ (DD H).filter (fun d => vx H d = w),
        σ a ∈ (DD H).filter (fun d => vx H d = w) ∧ σ (σ a) = a) ∧
      (∀ a ∈ (DD H).filter (fun d => vx H d = w), σ a ≠ a) := by
    intro w
    obtain ⟨σ, h1, -, h3⟩ := exists_pairing ((DD H).filter (fun d => vx H d = w))
    exact ⟨σ, h1, h3.1 (even_at hwf w)⟩
  choose σ hσ using hpair
  obtain ⟨π, hπ⟩ : ∃ π : Dart V → Dart V,
      ∀ d ∈ DD H, π d ∈ DD H ∧ π (π d) = d ∧ π d ≠ d ∧ vx H (π d) = vx H d := by
    refine ⟨fun d => σ (vx H d) d, fun d hd => ?_⟩
    have hd' : d ∈ (DD H).filter (fun x => vx H x = vx H d) := Finset.mem_filter.2 ⟨hd, rfl⟩
    obtain ⟨h1, h2⟩ := (hσ (vx H d)).1 d hd'
    have h1' := Finset.mem_filter.1 h1
    refine ⟨h1'.1, ?_, (hσ (vx H d)).2 d hd', h1'.2⟩
    simp only [h1'.2, h2]
  obtain ⟨_, -, hc⟩ := dart_orient π (DD H) eps (eps_props hwf)
    (fun d hd => ⟨(hπ d hd).1, (hπ d hd).2.1⟩)
  obtain ⟨c, hcε, hcπ, -⟩ := hc (fun _ => false) (fun d hd hfix => absurd hfix (hπ d hd).2.2.1)
  -- in-degree = out-degree at every vertex
  have hbal : ∀ w, ((DD H).filter (fun d => vx H d = w ∧ c d = true)).card =
      ((DD H).filter (fun d => vx H d = w ∧ c d = false)).card := by
    intro w
    have := card_filter_invol ((DD H).filter (fun d => vx H d = w)) (fun d => c d = true) π (by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨h1, h2, h3, h4⟩ := hπ a ha.1
      refine ⟨Finset.mem_filter.2 ⟨h1, h4.trans ha.2⟩, h2, ?_⟩
      have := hcπ a ha.1 h3
      cases hca : c a <;> cases hcpa : c (π a) <;> simp [hca, hcpa] at this ⊢)
    simpa [Finset.filter_filter] using this
  -- heads of physical edges: the endpoint whose dart is coloured `false`
  have hhead : ∀ e : Sym2 V, ∃ u, u ∈ e ∧ (e ∈ H.Hp → c (.inl (e, u)) = false) := by
    intro e
    obtain ⟨u, hu⟩ := exists_mem_sym2 e
    by_cases hcu : c (.inl (e, u)) = false
    · exact ⟨u, hu, fun _ => hcu⟩
    · refine ⟨oth u e, oth_mem hu, fun he => ?_⟩
      have := hcε (.inl (e, u)) ((mem_DD_inl H e u).2 ⟨he, hu⟩)
      simp only [eps] at this
      rw [bool_ne this]
      simpa using hcu
  choose head hhead1 hhead2 using hhead
  have hkey : ∀ e ∈ H.Hp, ∀ v ∈ e, (c (.inl (e, v)) = false ↔ head e = v) := by
    intro e he v hv
    constructor
    · intro hcv
      by_contra hne
      rcases eq_or_eq_oth (hhead1 e) hv with h | h
      · exact hne h.symm
      · have := hcε (.inl (e, head e)) ((mem_DD_inl H e _).2 ⟨he, hhead1 e⟩)
        simp only [eps] at this
        rw [← h, hcv, hhead2 e he] at this
        exact this rfl
    · rintro rfl; exact hhead2 e he
  have hvt : ∀ v ∈ H.S, ∀ k < (H.vv v).length,
      c (.inr (.inl ⟨v, (k, true)⟩)) = !c (.inr (.inl ⟨v, (k, false)⟩)) := by
    intro v hv k hk
    have := hcε (.inr (.inl ⟨v, (k, false)⟩)) ((mem_DD_vv H v k false).2 ⟨hv, hk⟩)
    simp only [eps, Bool.not_false] at this
    exact bool_ne this
  have hut : ∀ t < H.uu.length, c (.inr (.inr (t, true))) = !c (.inr (.inr (t, false))) := by
    intro t ht
    have := hcε (.inr (.inr (t, false))) ((mem_DD_uu H t false).2 ht)
    simp only [eps, Bool.not_false] at this
    exact bool_ne this
  -- the outputs
  let vd : V → List Bool := fun v =>
    (List.range (H.vv v).length).map (fun k => c (.inr (.inl ⟨v, (k, false)⟩)))
  let ud : List Bool := (List.range H.uu.length).map (fun t => c (.inr (.inr (t, false))))
  let o : Agent V → EOOut V := fun a => match a with
    | .inl v => ⟨vd v, ud, fun _ => none⟩
    | .inr _ => ⟨[], [], fun e => some (head e)⟩
  refine ⟨o, head, vd, ud, fun e _ => hhead1 e, fun C _ e _ _ => rfl,
    fun v _ => ⟨rfl, by simp [vd], rfl⟩, by simp [ud], ?_, ?_⟩
  · intro v hv
    have h1 := hbal (.inl v)
    rw [cnt_inl H v (fun d => c d = true), cnt_inl H v (fun d => c d = false)] at h1
    simp only [hv, ↓reduceIte] at h1
    have e1 : H.Hp.filter (fun e => v ∈ e ∧ head e = v) =
        H.Hp.filter (fun e => v ∈ e ∧ c (.inl (e, v)) = false) :=
      Finset.filter_congr (fun e he => ⟨fun h => ⟨h.1, (hkey e he v h.1).2 h.2⟩,
        fun h => ⟨h.1, (hkey e he v h.1).1 h.2⟩⟩)
    have e2 : H.Hp.filter (fun e => v ∈ e ∧ head e ≠ v) =
        H.Hp.filter (fun e => v ∈ e ∧ c (.inl (e, v)) = true) := by
      refine Finset.filter_congr (fun e he => ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩)
      · have := mt (hkey e he v h.1).1 h.2
        simpa using this
      · intro hh
        have := (hkey e he v h.1).2 hh
        rw [h.2] at this
        exact Bool.noConfusion this
    rw [e1, e2]
    simp only [vd, count_map_range]
    omega
  · intro i hi
    have h2 := hbal (.inr i)
    rw [cnt_inr H i (fun d => c d = true), cnt_inr H i (fun d => c d = false)] at h2
    have ev : ∀ v ∈ H.S, ∀ b : Bool, List.count (i, b) ((H.vv v).zip (vd v)) =
        ∑ k ∈ range (H.vv v).length,
          if (H.vv v).getD k 0 = i ∧ c (.inr (.inl ⟨v, (k, true)⟩)) = !b then 1 else 0 := by
      intro v hv b
      rw [List.count_eq_countP, List.countP_eq_length_filter]
      simp only [vd]
      rw [len_filter_zip_range (H.vv v) 0]
      refine sum_congr rfl (fun k hk => ?_)
      rw [hvt v hv k (mem_range.1 hk)]
      cases b <;> cases c (.inr (.inl ⟨v, (k, false)⟩)) <;> simp
    have eu1 : ((H.uu.zip ud).filter
          (fun t => decide (t.1.2 = i ∧ t.2 = true ∨ t.1.1 = i ∧ t.2 = false))).length =
        ∑ t ∈ range H.uu.length,
          ((if (H.uu.getD t (0, 0)).1 = i ∧ c (.inr (.inr (t, false))) = false then 1 else 0) +
            (if (H.uu.getD t (0, 0)).2 = i ∧ c (.inr (.inr (t, true))) = false then 1 else 0)) := by
      simp only [ud]
      rw [len_filter_zip_range H.uu (0, 0)]
      refine sum_congr rfl (fun t ht => ?_)
      rw [hut t (mem_range.1 ht)]
      cases c (.inr (.inr (t, false))) <;> simp
    have eu2 : ((H.uu.zip ud).filter
          (fun t => decide (t.1.1 = i ∧ t.2 = true ∨ t.1.2 = i ∧ t.2 = false))).length =
        ∑ t ∈ range H.uu.length,
          ((if (H.uu.getD t (0, 0)).1 = i ∧ c (.inr (.inr (t, false))) = true then 1 else 0) +
            (if (H.uu.getD t (0, 0)).2 = i ∧ c (.inr (.inr (t, true))) = true then 1 else 0)) := by
      simp only [ud]
      rw [len_filter_zip_range H.uu (0, 0)]
      refine sum_congr rfl (fun t ht => ?_)
      rw [hut t (mem_range.1 ht)]
      cases c (.inr (.inr (t, false))) <;> simp
    rw [sum_congr rfl (fun v hv => ev v hv true), sum_congr rfl (fun v hv => ev v hv false), eu1,
      eu2]
    simp only [Bool.not_true, Bool.not_false]
    omega

end APSP.Stoc
