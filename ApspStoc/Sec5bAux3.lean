import ApspStoc.Sec5bAux2

/-!
# Theorem 5.5, auxiliary file 3: correctness of one call of the recursion

Pure (algorithm-free) lemmas: given outputs of the building blocks satisfying their
specifications, the output of a call satisfies `ThreshSpec`, the subproblems satisfy `Valid`, and
the messages of the Bellman–Ford step are small.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Arithmetic helpers -/

lemma enat_lt_of_eq_add {a b : ℕ∞} {w : ℕ} (hw : 1 ≤ w) (h : b = a + w) (hb : b ≠ ⊤) : a < b := by
  have ha : a ≠ ⊤ := by intro ha; rw [ha] at h; exact hb (by rw [h]; simp)
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
  subst h
  exact_mod_cast (show m < m + w by omega)

lemma adj_wpos (N : WNet V) {u v : V} (h : N.G.Adj u v) : 1 ≤ N.w s(u, v) :=
  N.wpos _ ((SimpleGraph.mem_edgeSet N.G).2 h)

/-! ## The sets of one call -/

/-- `S₁ = {v ∈ S : d̃(v) ≤ 3δ}` (Step 3) -/
def s1Set (S : Finset V) (δ : ℕ) (ya : V → Option (ℕ × V)) : Finset V :=
  S.filter (fun v => leB (3 * δ) (ya v) = true)

/-- `S₂`: the nodes of `S₁` reached by the first recursive call (Step 4) -/
def s2Set (S1 : Finset V) (o1 : V → Option (ℕ × V)) : Finset V :=
  S1.filter (fun v => (o1 v).isSome = true)

/-- `S₁ \ S₂` -/
def tSet (S1 : Finset V) (o1 : V → Option (ℕ × V)) : Finset V :=
  S1.filter (fun v => (o1 v).isSome = false)

/-- the message of node `v` to its aggregators -/
def msgOf (S1 : Finset V) (o1 : V → Option (ℕ × V)) (v : V) : Option (Msg V) :=
  if v ∈ S1 then some (upOf (o1 v)) else none

/-- the answers received by `x` from its aggregators -/
noncomputable def recvOf (N : WNet V) (E : Overlays V) (up : Finset (Sym2 V) → V → Option (Msg V))
    (x : V) : Multiset (Msg V) :=
  (clustersOf E.cl x).val.filterMap (fun C => dnMsg C (lview N (.inr C)) (up C) x)

/-- the minimum of the old virtual edge and the received candidates -/
noncomputable def w1Of (w0 : V → Option (ℕ × V)) (recv : V → Multiset (Msg V)) (x : V) :
    Option (ℕ × V) :=
  bestOf (nodeCands (w0 x) (recv x))

/-- the virtual edges of the second recursive call -/
noncomputable def w2Of (T : Finset V) (δ : ℕ) (w0 : V → Option (ℕ × V))
    (recv : V → Multiset (Msg V)) (x : V) : Option (ℕ × V) :=
  if x ∈ T then (w1Of w0 recv x).map (fun q => (q.1 - δ, q.2)) else none

/-- the output of a call -/
def outOf (S2 T : Finset V) (δ : ℕ) (o1 o2 : V → Option (ℕ × V)) (v : V) : Option (ℕ × V) :=
  if v ∈ S2 then o1 v else if v ∈ T then (o2 v).map (fun q => (q.1 + δ, q.2)) else none

/-! ## Base case -/

section Base
variable (N : WNet V) {S : Finset V} {w0 : V → Option (ℕ × V)}

theorem base_correct {ya : V → Option (ℕ × V)} (hA : ApproxSpec N S w0 ya) :
    ThreshSpec N S w0 1 (fun v => baseOut (ya v)) := by
  intro v hv
  obtain ⟨hnone, hsome⟩ := hA v hv
  refine ⟨fun hle => ?_, fun hle => ?_⟩
  · have hfin : subDist N S w0 v ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
    obtain ⟨⟨d, p⟩, hy⟩ := Option.ne_none_iff_exists'.1 (fun h => hfin (hnone.1 h))
    obtain ⟨h1, h2, h3⟩ := hsome d p hy
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
    rw [← hm] at h1 h2 hle
    have h1' : m ≤ d := by exact_mod_cast h1
    have h2' : 2 * d ≤ 3 * m := by exact_mod_cast h2
    have hle' : m ≤ 1 := by exact_mod_cast hle
    have hdm : d = m := by omega
    refine ⟨d, p, by simp [hy, baseOut, show d ≤ 1 by omega], by rw [← hm, hdm], ?_⟩
    rcases h3 with ⟨hpS, hadj, dp, p', hyp, hdp⟩ | hw
    · left
      have hw1 := adj_wpos N hadj.symm
      have hp1 := ((hA p hpS).2 dp p' hyp).1
      have hdp0 : dp = 0 := by omega
      refine ⟨hpS, hadj.symm, ?_⟩
      have hDp : subDist N S w0 p = 0 := le_antisymm (by rw [hdp0] at hp1; exact_mod_cast hp1)
        bot_le
      rw [hDp, ← hm]
      have : N.w s(p, v) = m := by omega
      rw [this]; simp
    · right; exact ⟨d, hw, by rw [← hm, hdm]⟩
  · cases hy : ya v with
    | none => simp [hy, baseOut]
    | some q =>
      obtain ⟨d, p⟩ := q
      have h1 := ((hsome d p hy).1)
      simp only [hy, baseOut]
      rw [if_neg]
      intro hd
      exact hle (h1.trans (by exact_mod_cast hd))

end Base

/-! ## First recursive call -/

section First
variable (N : WNet V) {S : Finset V} {w0 : V → Option (ℕ × V)} {δ : ℕ}
  {ya : V → Option (ℕ × V)}

lemma mem_s1Set {v : V} : v ∈ s1Set S δ ya ↔ v ∈ S ∧ leB (3 * δ) (ya v) = true := by
  unfold s1Set; rw [mem_filter]

lemma s1_of_le (hA : ApproxSpec N S w0 ya) {v : V} (hv : v ∈ S)
    (hle : subDist N S w0 v ≤ (2 * δ : ℕ)) : v ∈ s1Set S δ ya := by
  obtain ⟨hnone, hsome⟩ := hA v hv
  have hfin : subDist N S w0 v ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  obtain ⟨⟨d, p⟩, hy⟩ := Option.ne_none_iff_exists'.1 (fun h => hfin (hnone.1 h))
  obtain ⟨_, h2, _⟩ := hsome d p hy
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hm] at h2 hle
  have h2' : 2 * d ≤ 3 * m := by exact_mod_cast h2
  have hle' : m ≤ 2 * δ := by exact_mod_cast hle
  refine (mem_s1Set).2 ⟨hv, ?_⟩
  rw [hy]; simp only [leB, decide_eq_true_eq]; omega

lemma le_of_s1 (hA : ApproxSpec N S w0 ya) {v : V} (hv : v ∈ s1Set S δ ya) :
    v ∈ S ∧ subDist N S w0 v ≤ (3 * δ : ℕ) := by
  obtain ⟨hvS, hle⟩ := (mem_s1Set).1 hv
  refine ⟨hvS, ?_⟩
  cases hy : ya v with
  | none => rw [hy] at hle; simp [leB] at hle
  | some q =>
    obtain ⟨d, p⟩ := q
    rw [hy] at hle; simp only [leB, decide_eq_true_eq] at hle
    exact ((hA v hvS).2 d p hy).1.trans (by exact_mod_cast hle)

lemma s1_sub : s1Set S δ ya ⊆ S := fun _ hv => ((mem_s1Set).1 hv).1

/-- Claim A: inside the component `K` of `S₁`, distances up to `2δ` are the distances in `S`. -/
lemma claimA (hA : ApproxSpec N S w0 ya) {K : Finset V} (hK : K ∈ comps N.G (s1Set S δ ya)) :
    ∀ v ∈ K, subDist N S w0 v ≤ (2 * δ : ℕ) → subDist N K w0 v = subDist N S w0 v := by
  have hKS : K ⊆ S := (comps_sub N.G hK).trans s1_sub
  intro v hv hle
  refine le_antisymm ?_ (subDist_mono N hKS w0 v hv)
  have hfin : subDist N S w0 v ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  refine subDist_induction N (S := S) (w0 := w0)
    (fun v => v ∈ K → subDist N S w0 v ≤ (2 * δ : ℕ) → subDist N K w0 v ≤ subDist N S w0 v)
    ?_ v (hKS hv) hfin hv hle
  intro v hvS hfin ih hvK hle
  rcases subDist_bellman N hvS hfin with ⟨c, p, hw, hD⟩ | ⟨y, hyS, hadj, hD⟩
  · rw [hD]; exact subDist_le_virt N hvK hw
  · have hlt := enat_lt_of_eq_add (adj_wpos N hadj) hD hfin
    have hyle : subDist N S w0 y ≤ (2 * δ : ℕ) := hlt.le.trans hle
    have hyK : y ∈ K := comps_adj N.G hK hvK (s1_of_le N hA hyS hyle) hadj
    have h1 := ih y hyS hlt hyK hyle
    calc subDist N K w0 v ≤ subDist N K w0 y + N.w s(y, v) := subDist_le_adj N hvK hadj
      _ ≤ subDist N S w0 y + N.w s(y, v) := add_le_add h1 le_rfl
      _ = _ := hD.symm

variable {o1 : V → Option (ℕ × V)}

/-- the first recursive call, on the component of `v` in `S₁` -/
lemma first_some (hA : ApproxSpec N S w0 ya)
    (h1 : ∀ K ∈ comps N.G (s1Set S δ ya), ThreshSpec N K w0 δ o1) {v : V}
    (hv : v ∈ s1Set S δ ya) (hle : subDist N S w0 v ≤ δ) :
    ∃ d p, o1 v = some (d, p) ∧ (d : ℕ∞) = subDist N S w0 v ∧ ParOK N S w0 v p := by
  set K := compOf N.G (s1Set S δ ya) v
  have hK : K ∈ comps N.G (s1Set S δ ya) := compOf_mem_comps N.G hv
  have hvK : v ∈ K := self_mem_compOf N.G hv
  have hKS : K ⊆ S := (comps_sub N.G hK).trans s1_sub
  have hEq := claimA N hA hK v hvK (hle.trans (by exact_mod_cast (show δ ≤ 2 * δ by omega)))
  obtain ⟨d, p, ho, hd, hpar⟩ := (h1 K hK v hvK).1 (hEq ▸ hle)
  refine ⟨d, p, ho, hd.trans hEq, ?_⟩
  rcases hpar with ⟨hpK, hadj, hsum⟩ | ⟨c, hw, hc⟩
  · left
    refine ⟨hKS hpK, hadj, le_antisymm ?_ (subDist_le_adj N (hKS hvK) hadj)⟩
    calc subDist N S w0 p + N.w s(p, v) ≤ subDist N K w0 p + N.w s(p, v) :=
          add_le_add (subDist_mono N hKS w0 p hpK) le_rfl
      _ = subDist N K w0 v := hsum
      _ = _ := hEq
  · right; exact ⟨c, hw, hc.trans hEq⟩

lemma first_none (h1 : ∀ K ∈ comps N.G (s1Set S δ ya), ThreshSpec N K w0 δ o1) {v : V}
    (hv : v ∈ s1Set S δ ya) (hle : ¬ subDist N S w0 v ≤ δ) : o1 v = none := by
  set K := compOf N.G (s1Set S δ ya) v
  have hK : K ∈ comps N.G (s1Set S δ ya) := compOf_mem_comps N.G hv
  have hvK : v ∈ K := self_mem_compOf N.G hv
  have hKS : K ⊆ S := (comps_sub N.G hK).trans s1_sub
  exact (h1 K hK v hvK).2 (fun h => hle ((subDist_mono N hKS w0 v hvK).trans h))

lemma first_isSome (hA : ApproxSpec N S w0 ya)
    (h1 : ∀ K ∈ comps N.G (s1Set S δ ya), ThreshSpec N K w0 δ o1) {v : V}
    (hv : v ∈ s1Set S δ ya) : (o1 v).isSome = true ↔ subDist N S w0 v ≤ δ := by
  constructor
  · intro hs
    by_contra hle
    rw [first_none N h1 hv hle] at hs; simp at hs
  · intro hle
    obtain ⟨d, p, ho, _⟩ := first_some N hA h1 hv hle
    rw [ho]; rfl

/-- the value of a node of `S₂` is its distance -/
lemma first_val (hA : ApproxSpec N S w0 ya)
    (h1 : ∀ K ∈ comps N.G (s1Set S δ ya), ThreshSpec N K w0 δ o1) {v : V}
    (hv : v ∈ s1Set S δ ya) {d : ℕ} {p : V} (ho : o1 v = some (d, p)) :
    (d : ℕ∞) = subDist N S w0 v ∧ d ≤ δ := by
  have hle : subDist N S w0 v ≤ δ := (first_isSome N hA h1 hv).1 (by rw [ho]; rfl)
  obtain ⟨d', p', ho', hd', _⟩ := first_some N hA h1 hv hle
  rw [ho] at ho'
  cases ho'
  refine ⟨hd', ?_⟩
  rw [← hd'] at hle; exact_mod_cast hle

end First

/-! ## The Bellman–Ford step (Step 5) -/

section BF
variable (N : WNet V) (E : Overlays V) {S : Finset V} {w0 : V → Option (ℕ × V)} {δ : ℕ}
  {ya o1 : V → Option (ℕ × V)} {up : Finset (Sym2 V) → V → Option (Msg V)}

lemma mem_tSet {S1 : Finset V} {v : V} : v ∈ tSet S1 o1 ↔ v ∈ S1 ∧ (o1 v).isSome = false := by
  unfold tSet; rw [mem_filter]

lemma mem_s2Set {S1 : Finset V} {v : V} : v ∈ s2Set S1 o1 ↔ v ∈ S1 ∧ (o1 v).isSome = true := by
  unfold s2Set; rw [mem_filter]

lemma s2val_msg {S1 : Finset V} {u : V} {d : ℕ} :
    s2val (msgOf S1 o1 u) = some d ↔ u ∈ S1 ∧ ∃ p, o1 u = some (d, p) := by
  unfold msgOf
  split_ifs with hu
  · cases ho : o1 u with
    | none => simp [upOf, s2val]
    | some q => obtain ⟨d', p⟩ := q; simp [upOf, s2val, hu, eq_comm]
  · simp [s2val, hu]

lemma msg_one {S1 : Finset V} {u : V} :
    msgOf S1 o1 u = some [Word.num 1] ↔ u ∈ tSet S1 o1 := by
  rw [mem_tSet]
  unfold msgOf
  split_ifs with hu
  · cases ho : o1 u with
    | none => simp [upOf, hu]
    | some q => obtain ⟨d', p⟩ := q; simp [upOf]
  · simp [hu]

lemma mem_recvOf {x : V} {m : Msg V} : m ∈ recvOf N E up x ↔
    ∃ C ∈ clustersOf E.cl x, dnMsg C (lview N (.inr C)) (up C) x = some m := by
  unfold recvOf; rw [Multiset.mem_filterMap]; simp only [Finset.mem_val]

lemma mem_aggCands {C : Finset (Sym2 V)} {wt : Sym2 V → ℕ} {upC : V → Option (Msg V)} {x : V}
    {q : ℕ × V} : q ∈ aggCands C wt upC x ↔
      ∃ u, (s(u, x) ∈ C ∧ (s2val (upC u)).isSome = true) ∧
        ((s2val (upC u)).getD 0 + wt s(u, x), u) = q := by
  unfold aggCands; simp only [mem_image, mem_filter, mem_univ, true_and]

lemma lview_inr {C : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ C) : lview N (.inr C) e = N.w e := by
  simp [lview, he]

lemma mem_nodeCands {o : Option (ℕ × V)} {r : Multiset (Msg V)} {q : ℕ × V} :
    q ∈ nodeCands o r ↔ o = some q ∨ ∃ m ∈ r, parseDn m = some q := by
  unfold nodeCands
  rw [mem_union, Option.mem_toFinset, Option.mem_def, Multiset.mem_toFinset,
    Multiset.mem_filterMap]

variable {N E}

/-- soundness of the Bellman–Ford answers -/
lemma recv_sound (hsub : ∀ C ∈ E.cl, C ⊆ N.G.edgeFinset) {S1 : Finset V}
    (hup : ∀ C ∈ E.cl, ∀ v, up C v = if v ∈ nodes C then msgOf S1 o1 v else none)
    {x u : V} {m : Msg V} {c : ℕ} (hm : m ∈ recvOf N E up x) (hp : parseDn m = some (c, u)) :
    u ∈ S1 ∧ N.G.Adj u x ∧ ∃ d p, o1 u = some (d, p) ∧ c = d + N.w s(u, x) := by
  obtain ⟨C, hC, hdn⟩ := (mem_recvOf N E).1 hm
  have hCcl : C ∈ E.cl := (mem_filter.1 hC).1
  unfold dnMsg at hdn
  split_ifs at hdn with hx
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hdn
  simp only [parseDn, Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨u', ⟨huC, hs⟩, hqe⟩ := mem_aggCands.1 (bestOf_some hq).1
  subst hqe
  have hupu := hup C hCcl u'
  by_cases hun : u' ∈ nodes C
  · rw [if_pos hun] at hupu
    rw [hupu] at hs ⊢
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨hu1, p, hop⟩ := (s2val_msg).1 hd
    have hadj : N.G.Adj u' x := by
      have := hsub C hCcl huC
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    refine ⟨hu1, hadj, d, p, hop, ?_⟩
    simp only [hd, Option.getD_some, lview_inr N huC]
  · rw [if_neg hun] at hupu; rw [hupu] at hs; simp [s2val] at hs

/-- completeness of the Bellman–Ford answers: every neighbour in `S₂` is reported (through the
aggregator of a cluster containing the edge) -/
lemma recv_complete (hcover : ∀ e ∈ N.G.edgeFinset, ∃ C ∈ E.cl, e ∈ C) {S1 : Finset V}
    (hup : ∀ C ∈ E.cl, ∀ v, up C v = if v ∈ nodes C then msgOf S1 o1 v else none)
    {x y : V} {d : ℕ} {p : V} (hx : x ∈ tSet S1 o1) (hy : y ∈ S1) (hoy : o1 y = some (d, p))
    (hadj : N.G.Adj y x) :
    ∃ m ∈ recvOf N E up x, ∃ c u, parseDn m = some (c, u) ∧ c ≤ d + N.w s(y, x) := by
  obtain ⟨C, hC, hyxC⟩ := hcover s(y, x) (by rw [SimpleGraph.mem_edgeFinset]; exact hadj)
  have hxC : x ∈ nodes C := mem_nodes.2 ⟨_, hyxC, Sym2.mem_mk_right y x⟩
  have hyC : y ∈ nodes C := mem_nodes.2 ⟨_, hyxC, Sym2.mem_mk_left y x⟩
  have hC' : C ∈ clustersOf E.cl x := mem_filter.2 ⟨hC, hxC⟩
  have hupx : up C x = some [Word.num 1] := by
    rw [hup C hC x, if_pos hxC]; exact msg_one.2 hx
  have hs2 : s2val (up C y) = some d := by
    rw [hup C hC y, if_pos hyC]; exact s2val_msg.2 ⟨hy, p, hoy⟩
  have hq0 : (d + N.w s(y, x), y) ∈ aggCands C (lview N (.inr C)) (up C) x :=
    mem_aggCands.2 ⟨y, ⟨hyxC, by rw [hs2]; rfl⟩, by rw [hs2, Option.getD_some, lview_inr N hyxC]⟩
  obtain ⟨q, hq⟩ := bestOf_exists hq0
  have hqle := (bestOf_some hq).2 _ hq0
  refine ⟨[Word.num q.1, Word.id q.2], (mem_recvOf N E).2 ⟨C, hC', ?_⟩, q.1, q.2, rfl, hqle⟩
  unfold dnMsg; rw [if_pos hupx, hq]; rfl

/-- the candidates of a node -/
lemma w1_sound (hsub : ∀ C ∈ E.cl, C ⊆ N.G.edgeFinset) {S1 : Finset V}
    (hup : ∀ C ∈ E.cl, ∀ v, up C v = if v ∈ nodes C then msgOf S1 o1 v else none)
    {x p : V} {c : ℕ} (h : w1Of w0 (recvOf N E up) x = some (c, p)) :
    w0 x = some (c, p) ∨ (p ∈ S1 ∧ N.G.Adj p x ∧ ∃ d q, o1 p = some (d, q) ∧ c = d + N.w s(p, x)) := by
  have hmem := (bestOf_some h).1
  rcases (mem_nodeCands).1 hmem with hw | ⟨m, hm, hp⟩
  · exact Or.inl hw
  · exact Or.inr (recv_sound hsub hup hm hp)

lemma w1_le_of_mem {x : V} {q : ℕ × V} (hq : q ∈ nodeCands (w0 x) (recvOf N E up x)) :
    ∃ c' p', w1Of w0 (recvOf N E up) x = some (c', p') ∧ c' ≤ q.1 := by
  obtain ⟨⟨c', p'⟩, h⟩ := bestOf_exists hq
  exact ⟨c', p', h, (bestOf_some h).2 q hq⟩

lemma w1_le_virt {x p : V} {c : ℕ} (hw : w0 x = some (c, p)) :
    ∃ c' p', w1Of w0 (recvOf N E up) x = some (c', p') ∧ c' ≤ c :=
  w1_le_of_mem ((mem_nodeCands).2 (Or.inl hw))

lemma w1_le_nb (hcover : ∀ e ∈ N.G.edgeFinset, ∃ C ∈ E.cl, e ∈ C) {S1 : Finset V}
    (hup : ∀ C ∈ E.cl, ∀ v, up C v = if v ∈ nodes C then msgOf S1 o1 v else none)
    {x y : V} {d : ℕ} {p : V} (hx : x ∈ tSet S1 o1) (hy : y ∈ S1) (hoy : o1 y = some (d, p))
    (hadj : N.G.Adj y x) :
    ∃ c' p', w1Of w0 (recvOf N E up) x = some (c', p') ∧ c' ≤ d + N.w s(y, x) := by
  obtain ⟨m, hm, c, u, hp, hc⟩ := recv_complete hcover hup hx hy hoy hadj
  obtain ⟨c', p', h, hle⟩ := w1_le_of_mem (w0 := w0) (q := (c, u))
    ((mem_nodeCands).2 (Or.inr ⟨m, hm, hp⟩))
  exact ⟨c', p', h, hle.trans hc⟩

end BF

/-! ## The second recursive call and the output -/

/-- The hypotheses on the outputs of Steps 1–5. -/
structure StepHyp (N : WNet V) (E : Overlays V) (S : Finset V) (w0 : V → Option (ℕ × V)) (δ : ℕ)
    (ya o1 : V → Option (ℕ × V)) (up : Finset (Sym2 V) → V → Option (Msg V)) : Prop where
  hA : ApproxSpec N S w0 ya
  h1 : ∀ K ∈ comps N.G (s1Set S δ ya), ThreshSpec N K w0 δ o1
  sub : ∀ C ∈ E.cl, C ⊆ N.G.edgeFinset
  cover : ∀ e ∈ N.G.edgeFinset, ∃ C ∈ E.cl, e ∈ C
  up : ∀ C ∈ E.cl, ∀ v, up C v = if v ∈ nodes C then msgOf (s1Set S δ ya) o1 v else none

section Second
variable {N : WNet V} {E : Overlays V} {S : Finset V} {w0 : V → Option (ℕ × V)} {δ : ℕ}
  {ya o1 : V → Option (ℕ × V)} {up : Finset (Sym2 V) → V → Option (Msg V)}

lemma tSet_sub {S1 : Finset V} : tSet S1 o1 ⊆ S1 := fun _ hv => (mem_tSet.1 hv).1

lemma tSet_sub_S : tSet (s1Set S δ ya) o1 ⊆ S := tSet_sub.trans s1_sub

lemma T_not_le (H : StepHyp N E S w0 δ ya o1 up) {x : V} (hx : x ∈ tSet (s1Set S δ ya) o1) :
    ¬ subDist N S w0 x ≤ δ := by
  obtain ⟨hx1, hxn⟩ := mem_tSet.1 hx
  intro hle
  have := (first_isSome N H.hA H.h1 hx1).2 hle
  rw [hxn] at this; exact Bool.false_ne_true this

lemma w1_lower (H : StepHyp N E S w0 δ ya o1 up) {x p : V} {c : ℕ} (hxS : x ∈ S)
    (h : w1Of w0 (recvOf N E up) x = some (c, p)) : subDist N S w0 x ≤ c := by
  rcases w1_sound H.sub H.up h with hw | ⟨hp1, hadj, d, q, hop, hc⟩
  · exact subDist_le_virt N hxS hw
  · have hd := (first_val N H.hA H.h1 hp1 hop).1
    rw [hc]; push_cast; rw [hd]
    exact subDist_le_adj N hxS hadj

lemma w1_gt (H : StepHyp N E S w0 δ ya o1 up) {x p : V} {c : ℕ}
    (hx : x ∈ tSet (s1Set S δ ya) o1) (h : w1Of w0 (recvOf N E up) x = some (c, p)) : δ < c := by
  have h1 := w1_lower H (tSet_sub_S hx) h
  by_contra hc
  exact T_not_le H hx (h1.trans (by exact_mod_cast (not_lt.1 hc)))

lemma w2_eq {T : Finset V} {recv : V → Multiset (Msg V)} {x p : V} {c : ℕ}
    (h : w2Of T δ w0 recv x = some (c, p)) :
    x ∈ T ∧ ∃ c1, w1Of w0 recv x = some (c1, p) ∧ c = c1 - δ := by
  unfold w2Of at h
  split_ifs at h with hx
  obtain ⟨⟨c1, p1⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hx, c1, h1, rfl⟩

lemma w2_of_w1 {T : Finset V} {recv : V → Multiset (Msg V)} {x p : V} {c : ℕ} (hx : x ∈ T)
    (h : w1Of w0 recv x = some (c, p)) : w2Of T δ w0 recv x = some (c - δ, p) := by
  unfold w2Of; rw [if_pos hx, h]; rfl

/-- Claim C: the second call never undercuts the distances in `S` (minus `δ`). -/
lemma claimC (H : StepHyp N E S w0 δ ya o1 up) {K : Finset V}
    (hK : K ∈ comps N.G (tSet (s1Set S δ ya) o1)) :
    ∀ x ∈ K, subDist N S w0 x ≤
      subDist N K (w2Of (tSet (s1Set S δ ya) o1) δ w0 (recvOf N E up)) x + δ := by
  have hKS : K ⊆ S := (comps_sub N.G hK).trans tSet_sub_S
  refine le_subDist_of_pot N (subDist N S w0) δ (fun u hu c p hw => ?_)
    (fun y _ x hx h => subDist_le_adj N (hKS hx) h)
  obtain ⟨huT, c1, h1, rfl⟩ := w2_eq hw
  exact (w1_lower H (hKS hu) h1).trans (by exact_mod_cast (show c1 ≤ c1 - δ + δ by omega))

/-- Claim D: up to distance `2δ`, the second call finds the distances in `S` (minus `δ`), thanks
to the Bellman–Ford entries and the old virtual edges. -/
lemma claimD (H : StepHyp N E S w0 δ ya o1 up) {K : Finset V}
    (hK : K ∈ comps N.G (tSet (s1Set S δ ya) o1)) :
    ∀ x ∈ K, subDist N S w0 x ≤ (2 * δ : ℕ) →
      subDist N K (w2Of (tSet (s1Set S δ ya) o1) δ w0 (recvOf N E up)) x + δ ≤
        subDist N S w0 x := by
  set T := tSet (s1Set S δ ya) o1
  set w2 := w2Of T δ w0 (recvOf N E up)
  have hKT : K ⊆ T := comps_sub N.G hK
  have hKS : K ⊆ S := hKT.trans tSet_sub_S
  -- the entry of `x` bounds its distance
  have key : ∀ x ∈ K, ∀ c' p', w1Of w0 (recvOf N E up) x = some (c', p') →
      subDist N K w2 x + δ ≤ c' := by
    intro x hx c' p' h
    have hgt := w1_gt H (hKT hx) h
    have hv := subDist_le_virt N (S := K) (w0 := w2) hx (w2_of_w1 (hKT hx) h)
    calc subDist N K w2 x + δ ≤ ((c' - δ : ℕ) : ℕ∞) + δ := add_le_add hv le_rfl
      _ = c' := by rw [← Nat.cast_add, Nat.sub_add_cancel hgt.le]
  intro x hx hle
  have hfin : subDist N S w0 x ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  refine subDist_induction N (S := S) (w0 := w0)
    (fun x => x ∈ K → subDist N S w0 x ≤ (2 * δ : ℕ) → subDist N K w2 x + δ ≤ subDist N S w0 x)
    ?_ x (hKS hx) hfin hx hle
  intro x hxS hfin ih hxK hle
  rcases subDist_bellman N hxS hfin with ⟨c, p, hw, hD⟩ | ⟨y, hyS, hadj, hD⟩
  · obtain ⟨c', p', h, hc'⟩ := w1_le_virt (N := N) (E := E) (up := up) hw
    rw [hD]; exact (key x hxK c' p' h).trans (by exact_mod_cast hc')
  · have hlt := enat_lt_of_eq_add (adj_wpos N hadj) hD hfin
    have hyle : subDist N S w0 y ≤ (2 * δ : ℕ) := hlt.le.trans hle
    have hy1 : y ∈ s1Set S δ ya := s1_of_le N H.hA hyS hyle
    cases hoy : o1 y with
    | some q =>
      obtain ⟨d, p⟩ := q
      have hd := (first_val N H.hA H.h1 hy1 hoy).1
      obtain ⟨c', p', h, hc'⟩ := w1_le_nb H.cover H.up (hKT hxK) hy1 hoy hadj
      refine (key x hxK c' p' h).trans ?_
      rw [hD, ← hd]; exact_mod_cast hc'
    | none =>
      have hyT : y ∈ T := mem_tSet.2 ⟨hy1, by rw [hoy]; rfl⟩
      have hyK : y ∈ K := comps_adj N.G hK hxK hyT hadj
      have h1 := ih y hyS hlt hyK hyle
      calc subDist N K w2 x + δ ≤ subDist N K w2 y + N.w s(y, x) + δ :=
            add_le_add (subDist_le_adj N hxK hadj) le_rfl
        _ = subDist N K w2 y + δ + N.w s(y, x) := by ring
        _ ≤ subDist N S w0 y + N.w s(y, x) := add_le_add h1 le_rfl
        _ = _ := hD.symm

lemma second_some (H : StepHyp N E S w0 δ ya o1 up) {o2 : V → Option (ℕ × V)}
    (h2 : ∀ K ∈ comps N.G (tSet (s1Set S δ ya) o1),
      ThreshSpec N K (w2Of (tSet (s1Set S δ ya) o1) δ w0 (recvOf N E up)) δ o2)
    {x : V} (hx : x ∈ tSet (s1Set S δ ya) o1) (hle : subDist N S w0 x ≤ (2 * δ : ℕ)) :
    ∃ d p, o2 x = some (d, p) ∧ ((d + δ : ℕ) : ℕ∞) = subDist N S w0 x ∧ ParOK N S w0 x p := by
  set T := tSet (s1Set S δ ya) o1
  set w2 := w2Of T δ w0 (recvOf N E up)
  set K := compOf N.G T x
  have hK : K ∈ comps N.G T := compOf_mem_comps N.G hx
  have hxK : x ∈ K := self_mem_compOf N.G hx
  have hKT : K ⊆ T := comps_sub N.G hK
  have hKS : K ⊆ S := hKT.trans tSet_sub_S
  have hC := claimC H hK
  have hEq : subDist N K w2 x + δ = subDist N S w0 x :=
    le_antisymm (claimD H hK x hxK hle) (hC x hxK)
  have hle' : subDist N K w2 x ≤ δ := by
    have hfin : subDist N K w2 x ≠ ⊤ := by
      intro h; rw [h] at hEq
      exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle (by rw [← hEq]; simp)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
    rw [← hm] at hEq ⊢
    rw [← hEq] at hle
    have : m + δ ≤ 2 * δ := by exact_mod_cast hle
    exact_mod_cast (show m ≤ δ by omega)
  obtain ⟨d, p, ho, hd, hpar⟩ := (h2 K hK x hxK).1 hle'
  have hdδ : ((d + δ : ℕ) : ℕ∞) = subDist N S w0 x := by push_cast; rw [hd]; exact hEq
  refine ⟨d, p, ho, hdδ, ?_⟩
  rcases hpar with ⟨hpK, hadj, hsum⟩ | ⟨c, hw, hc⟩
  · left
    refine ⟨hKS hpK, hadj, le_antisymm ?_ (subDist_le_adj N (hKS hxK) hadj)⟩
    calc subDist N S w0 p + N.w s(p, x) ≤ subDist N K w2 p + δ + N.w s(p, x) :=
          add_le_add (hC p hpK) le_rfl
      _ = subDist N K w2 p + N.w s(p, x) + δ := by ring
      _ = _ := by rw [hsum, hEq]
  · obtain ⟨_, c1, h1, rfl⟩ := w2_eq hw
    have hgt := w1_gt H hx h1
    have hc1 : (c1 : ℕ∞) = subDist N S w0 x := by
      rw [← hEq, ← hc]; push_cast [Nat.cast_sub hgt.le]
      rw [tsub_add_cancel_of_le (by exact_mod_cast hgt.le)]
    rcases w1_sound H.sub H.up h1 with hw0 | ⟨hp1, hadj, d', q, hop, hcd⟩
    · right; exact ⟨c1, hw0, hc1⟩
    · left
      have hd' := (first_val N H.hA H.h1 hp1 hop).1
      refine ⟨s1_sub hp1, hadj, ?_⟩
      rw [← hc1, ← hd', hcd]; push_cast; rfl

lemma second_none (H : StepHyp N E S w0 δ ya o1 up) {o2 : V → Option (ℕ × V)}
    (h2 : ∀ K ∈ comps N.G (tSet (s1Set S δ ya) o1),
      ThreshSpec N K (w2Of (tSet (s1Set S δ ya) o1) δ w0 (recvOf N E up)) δ o2)
    {x : V} (hx : x ∈ tSet (s1Set S δ ya) o1) (hle : ¬ subDist N S w0 x ≤ (2 * δ : ℕ)) :
    o2 x = none := by
  set T := tSet (s1Set S δ ya) o1
  set K := compOf N.G T x
  have hK : K ∈ comps N.G T := compOf_mem_comps N.G hx
  have hxK : x ∈ K := self_mem_compOf N.G hx
  refine (h2 K hK x hxK).2 (fun h => hle ?_)
  calc subDist N S w0 x ≤ _ + δ := claimC H hK x hxK
    _ ≤ (δ : ℕ∞) + δ := add_le_add h le_rfl
    _ = ((2 * δ : ℕ) : ℕ∞) := by push_cast; ring

/-- Correctness of one call of the recursion. -/
theorem out_correct (H : StepHyp N E S w0 δ ya o1 up) {o2 : V → Option (ℕ × V)}
    (h2 : ∀ K ∈ comps N.G (tSet (s1Set S δ ya) o1),
      ThreshSpec N K (w2Of (tSet (s1Set S δ ya) o1) δ w0 (recvOf N E up)) δ o2) :
    ThreshSpec N S w0 (2 * δ)
      (outOf (s2Set (s1Set S δ ya) o1) (tSet (s1Set S δ ya) o1) δ o1 o2) := by
  intro v hv
  refine ⟨fun hle => ?_, fun hle => ?_⟩
  · have hv1 := s1_of_le N H.hA hv (by exact_mod_cast hle)
    by_cases hs : (o1 v).isSome = true
    · have hv2 : v ∈ s2Set (s1Set S δ ya) o1 := mem_s2Set.2 ⟨hv1, hs⟩
      have hleδ := (first_isSome N H.hA H.h1 hv1).1 hs
      obtain ⟨d, p, ho, hd, hpar⟩ := first_some N H.hA H.h1 hv1 hleδ
      exact ⟨d, p, by simp [outOf, hv2, ho], hd, hpar⟩
    · have hvT : v ∈ tSet (s1Set S δ ya) o1 := mem_tSet.2 ⟨hv1, by simpa using hs⟩
      have hv2 : v ∉ s2Set (s1Set S δ ya) o1 := fun h => hs (mem_s2Set.1 h).2
      obtain ⟨d, p, ho, hd, hpar⟩ := second_some H h2 hvT (by exact_mod_cast hle)
      exact ⟨d + δ, p, by simp [outOf, hv2, hvT, ho], hd, hpar⟩
  · unfold outOf
    split_ifs with hv2 hvT
    · have h := (mem_s2Set.1 hv2)
      exact first_none N H.h1 h.1 (fun h' => hle (h'.trans (by exact_mod_cast (by omega))))
        |> fun h0 => by rw [h0] at h; simp at h
    · rw [second_none H h2 hvT (by exact_mod_cast hle)]; rfl
    · rfl

end Second

/-! ## The invariant of the subproblems and the message sizes -/

section Valid
variable {N : WNet V} {E : Overlays V} {S : Finset V} {w0 : V → Option (ℕ × V)} {k a W : ℕ}
  {s : V} {ya o1 : V → Option (ℕ × V)} {up : Finset (Sym2 V) → V → Option (Msg V)}

/-- true distances are at most `subDist + a` -/
lemma valid_lb (hV : Valid N s W k S w0 a) :
    ∀ v ∈ S, (N.wdist s v : ℕ∞) ≤ subDist N S w0 v + a :=
  le_subDist_of_pot N (fun v => (N.wdist s v : ℕ∞)) a
    (fun u hu c p hw => by exact_mod_cast hV.low u hu c p hw)
    (fun y _ x _ h => by exact_mod_cast wdist_le_adj N s h)

/-- a node with `subDist ≤ 2^(k+1)` has `subDist = dist - a` -/
lemma valid_ex' (hV : Valid N s W (k + 1) S w0 a) {v : V} (hv : v ∈ S) {d : ℕ}
    (hd : (d : ℕ∞) = subDist N S w0 v) (hle : d ≤ 2 ^ (k + 1)) : d + a = N.wdist s v := by
  have h1 := valid_lb hV v hv
  rw [← hd] at h1
  have h1' : N.wdist s v ≤ d + a := by exact_mod_cast h1
  have h2 := hV.ex v hv (by omega)
  rw [← hd] at h2
  exact_mod_cast h2

lemma valid_first (hA : ApproxSpec N S w0 ya) (hV : Valid N s W (k + 1) S w0 a) {K : Finset V}
    (hK : K ∈ comps N.G (s1Set S (2 ^ k) ya)) : Valid N s W k K w0 a := by
  have hKS : K ⊆ S := (comps_sub N.G hK).trans s1_sub
  refine ⟨hV.bnd, fun u hu => hV.low u (hKS hu), fun v hv => ⟨(hV.win v (hKS hv)).1, ?_⟩,
    fun v hv hle => ?_, (pow_dvd_pow 2 (Nat.le_succ k)).trans hV.dvd⟩
  · have h1 := valid_lb hV v (hKS hv)
    have h2 := (le_of_s1 N hA (comps_sub N.G hK hv)).2
    have : (N.wdist s v : ℕ∞) ≤ ((3 * 2 ^ k + a : ℕ) : ℕ∞) := by
      push_cast; exact h1.trans (add_le_add (by exact_mod_cast h2) le_rfl)
    have := (by exact_mod_cast this : N.wdist s v ≤ 3 * 2 ^ k + a)
    omega
  · have h2 := hV.ex v (hKS hv) (by rw [pow_succ]; omega)
    have hfin : subDist N S w0 v ≠ ⊤ := fun h => by rw [h] at h2; simp at h2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
    rw [← hm] at h2
    have h2' : m + a = N.wdist s v := by exact_mod_cast h2
    have hEq := claimA N hA hK v hv (by rw [← hm]; exact_mod_cast (show m ≤ 2 * 2 ^ k by omega))
    rw [hEq, ← hm]; exact_mod_cast h2'

lemma valid_second (H : StepHyp N E S w0 (2 ^ k) ya o1 up) (hV : Valid N s W (k + 1) S w0 a)
    (hW : ∀ e ∈ N.G.edgeSet, N.w e ≤ W) {K : Finset V} (hK : K ∈ comps N.G (tSet (s1Set S (2 ^ k) ya) o1)) :
    Valid N s W k K (w2Of (tSet (s1Set S (2 ^ k) ya) o1) (2 ^ k) w0 (recvOf N E up))
      (a + 2 ^ k) := by
  have hKT : K ⊆ tSet (s1Set S (2 ^ k) ya) o1 := comps_sub N.G hK
  have hKS : K ⊆ S := hKT.trans tSet_sub_S
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
  refine ⟨fun v c p hw => ?_, fun u hu c p hw => ?_, fun v hv => ⟨?_, ?_⟩, fun v hv hle => ?_,
    dvd_add ((pow_dvd_pow 2 (Nat.le_succ k)).trans hV.dvd) dvd_rfl⟩
  · obtain ⟨_, c1, h1, rfl⟩ := w2_eq hw
    rcases w1_sound H.sub H.up h1 with hw0 | ⟨hp1, hpadj, d, q, hop, hc⟩
    · have := hV.bnd v c1 p hw0; exact (Nat.sub_le _ _).trans this
    · have hd := (first_val N H.hA H.h1 hp1 hop).2
      have := hW s(p, v) ((N.G.mem_edgeSet).2 hpadj)
      rw [hc]; generalize 2 ^ k = δ at hd ⊢; omega
  · obtain ⟨huT, c1, h1, rfl⟩ := w2_eq hw
    have hgt := w1_gt H huT h1
    suffices N.wdist s u ≤ c1 + a by omega
    rcases w1_sound H.sub H.up h1 with hw0 | ⟨hp1, hadj, d, q, hop, hc⟩
    · exact hV.low u (hKS hu) c1 p hw0
    · obtain ⟨hd, hdδ⟩ := first_val N H.hA H.h1 hp1 hop
      have h1 := valid_ex' hV (s1_sub hp1) hd (by rw [hpow]; omega)
      have h2 := wdist_le_adj N s hadj
      omega
  · by_contra hlt
    have h2 := hV.ex v (hKS hv) (by rw [hpow]; generalize 2 ^ k = δ at hlt ⊢; omega)
    apply T_not_le H (hKT hv)
    have hfin : subDist N S w0 v ≠ ⊤ := fun h => by rw [h] at h2; simp at h2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
    rw [← hm] at h2 ⊢
    have h2' : m + a = N.wdist s v := by exact_mod_cast h2
    exact_mod_cast (show m ≤ 2 ^ k by omega)
  · have h1 := valid_lb hV v (hKS hv)
    have h2 := (le_of_s1 N H.hA (tSet_sub (hKT hv))).2
    have : (N.wdist s v : ℕ∞) ≤ ((3 * 2 ^ k + a : ℕ) : ℕ∞) := by
      push_cast; exact h1.trans (add_le_add (by exact_mod_cast h2) le_rfl)
    have := (by exact_mod_cast this : N.wdist s v ≤ 3 * 2 ^ k + a)
    generalize 2 ^ k = δ at this ⊢; omega
  · have h2 := hV.ex v (hKS hv) (by rw [hpow]; omega)
    have hfin : subDist N S w0 v ≠ ⊤ := fun h => by rw [h] at h2; simp at h2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
    have h2' : m + a = N.wdist s v := by rw [← hm] at h2; exact_mod_cast h2
    have hle2 : subDist N S w0 v ≤ ((2 * 2 ^ k : ℕ) : ℕ∞) := by
      rw [← hm]; exact_mod_cast (show m ≤ 2 * 2 ^ k by omega)
    have hEq : subDist N K (w2Of (tSet (s1Set S (2 ^ k) ya) o1) (2 ^ k) w0 (recvOf N E up)) v +
        2 ^ k = subDist N S w0 v :=
      le_antisymm (claimD H hK v hv hle2) (by exact_mod_cast claimC H hK v hv)
    calc subDist N K (w2Of (tSet (s1Set S (2 ^ k) ya) o1) (2 ^ k) w0 (recvOf N E up)) v +
          ((a + 2 ^ k : ℕ) : ℕ∞) =
        (subDist N K (w2Of (tSet (s1Set S (2 ^ k) ya) o1) (2 ^ k) w0 (recvOf N E up)) v +
          2 ^ k) + a := by push_cast; ring
      _ = subDist N S w0 v + a := by rw [hEq]
      _ = _ := h2

/-- the distance announced by a node of `S₂` -/
lemma s2_dist (H : StepHyp N E S w0 (2 ^ k) ya o1 up) (hV : Valid N s W (k + 1) S w0 a)
    {v p : V} {d : ℕ} (hv : v ∈ s1Set S (2 ^ k) ya) (ho : o1 v = some (d, p)) :
    d + a = N.wdist s v := by
  obtain ⟨hd, hdδ⟩ := first_val N H.hA H.h1 hv ho
  exact valid_ex' hV (s1_sub hv) hd (by rw [pow_succ]; omega)

lemma msg_mem {S1 : Finset V} (hS1 : S1 ⊆ S) {v : V} (h : msgOf S1 o1 v ≠ none) : v ∈ S := by
  unfold msgOf at h; split_ifs at h with hv
  · exact hS1 hv
  · exact absurd rfl h

lemma msg_small (H : StepHyp N E S w0 (2 ^ k) ya o1 up) (hV : Valid N s W (k + 1) S w0 a)
    {B : ℕ} (hB1 : 1 ≤ B) (hBx : ∀ v, N.wdist s v + W ≤ B) :
    ∀ v m, msgOf (s1Set S (2 ^ k) ya) o1 v = some m → m.Small 2 B := by
  intro v m hm
  unfold msgOf at hm
  split_ifs at hm with hv
  cases hm
  cases ho : o1 v with
  | none => simp [upOf, Msg.Small, Msg.Bnd, hB1]
  | some q =>
    obtain ⟨d, p⟩ := q
    have h1 := s2_dist H hV hv ho
    have h2 := hBx v
    simp only [upOf, Msg.Small, Msg.Bnd, List.length_cons, List.length_nil, List.mem_cons,
      Word.num.injEq, List.not_mem_nil, or_false]
    refine ⟨le_rfl, fun k hk => ?_⟩
    rcases hk with rfl | rfl <;> omega

lemma dn_mem (H : StepHyp N E S w0 (2 ^ k) ya o1 up) :
    ∀ C ∈ E.cl, ∀ v, dnMsg C (lview N (.inr C)) (up C) v ≠ none → v ∈ S ∧ v ∈ nodes C := by
  intro C hC v h
  unfold dnMsg at h
  split_ifs at h with hx
  · rw [H.up C hC v] at hx
    split_ifs at hx with hvC
    · exact ⟨tSet_sub_S (msg_one.1 hx), hvC⟩
  · exact absurd rfl h

lemma dn_small (H : StepHyp N E S w0 (2 ^ k) ya o1 up) (hV : Valid N s W (k + 1) S w0 a)
    (hW : ∀ e ∈ N.G.edgeSet, N.w e ≤ W) {B : ℕ} (hBx : ∀ v, N.wdist s v + W ≤ B) :
    ∀ C ∈ E.cl, ∀ v m, dnMsg C (lview N (.inr C)) (up C) v = some m → m.Small 2 B := by
  intro C hC v m hm
  unfold dnMsg at hm
  split_ifs at hm with hx
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hm
  obtain ⟨u, ⟨huC, hs⟩, hqe⟩ := mem_aggCands.1 (bestOf_some hq).1
  subst hqe
  have hupu := H.up C hC u
  by_cases hun : u ∈ nodes C
  · rw [if_pos hun] at hupu
    rw [hupu] at hs ⊢
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨hu1, p, hop⟩ := (s2val_msg).1 hd
    have h1 := s2_dist H hV hu1 hop
    have h2 := hBx u
    have h3 := hW s(u, v) (N.G.mem_edgeFinset.1 (H.sub C hC huC))
    simp only [Msg.Small, Msg.Bnd, List.length_cons, List.length_nil, List.mem_cons,
      List.not_mem_nil, or_false, hd, Option.getD_some, lview_inr N huC]
    refine ⟨le_rfl, fun k hk => ?_⟩
    simp only [Word.num.injEq, reduceCtorEq, or_false] at hk
    omega
  · rw [if_neg hun] at hupu; rw [hupu] at hs; simp [s2val] at hs

end Valid

/-! ## The top level -/

section Top
variable (N : WNet V) (s : V)

lemma subDist_topW0 (v : V) : subDist N univ (topW0 s) v = N.wdist s v := subDist_top N s v

lemma valid_top (W L : ℕ) (hlt : ∀ v, N.wdist s v < 2 ^ L) :
    Valid N s W L univ (topW0 s) 0 := by
  refine ⟨fun v c p hw => ?_, fun u _ c p hw => ?_, fun v _ => ⟨Nat.zero_le _, ?_⟩,
    fun v _ _ => by rw [subDist_topW0]; simp, dvd_zero _⟩
  · unfold topW0 at hw; split_ifs at hw; cases hw; exact Nat.zero_le _
  · unfold topW0 at hw; split_ifs at hw with hus
    cases hw; subst hus; rw [wdist_self]
  · have := hlt v; omega

lemma top_out (L : ℕ) (hlt : ∀ v, N.wdist s v < 2 ^ L) (o : V → Option (ℕ × V))
    (h : ThreshSpec N univ (topW0 s) (2 ^ L) o) : SSSPSpec N s (fun v => (o v).getD (0, s)) := by
  intro v
  have hle : subDist N univ (topW0 s) v ≤ (2 ^ L : ℕ) := by
    rw [subDist_topW0]; exact_mod_cast (hlt v).le
  obtain ⟨d, p, ho, hd, hpar⟩ := (h v (mem_univ v)).1 hle
  rw [subDist_topW0] at hd
  have hd' : d = N.wdist s v := by exact_mod_cast hd
  simp only [ho, Option.getD_some]
  refine ⟨hd', fun hvs => ?_⟩
  rcases hpar with ⟨_, hadj, hsum⟩ | ⟨c, hw, _⟩
  · rw [subDist_topW0, subDist_topW0] at hsum
    have hsum' : N.wdist s p + N.w s(p, v) = N.wdist s v := by exact_mod_cast hsum
    refine ⟨hadj.symm, ?_⟩
    rw [Sym2.eq_swap]; omega
  · unfold topW0 at hw; rw [if_neg hvs] at hw; cases hw

end Top

end APSP.Stoc
