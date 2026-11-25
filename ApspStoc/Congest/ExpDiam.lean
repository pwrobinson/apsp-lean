import ApspStoc.Defs

/-!
# Diameter of expander clusters

The graph `clGraph C` of a cluster `C` (two nodes are adjacent iff they span an edge of `C`) has
diameter `O(φinv · log |C|)` on `nodes C` when `C` is a `1/φinv`-expander: BFS balls grow in volume
by a factor `(φinv + 1) / φinv` per step as long as they hold at most half of the volume, and two
balls holding more than half of the volume intersect.
-/

namespace APSP.Stoc

open APSP Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The graph of a cluster -/

/-- The graph of a cluster: nodes adjacent iff they span an edge of `C`. -/
def clGraph (C : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ s(u, v) ∈ C
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance clGraph.instDecidableRelAdj (C : Finset (Sym2 V)) : DecidableRel (clGraph C).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ s(u, v) ∈ C))

/-- diameter bound for a `1/φinv`-expander with `m` edges -/
def diamBound (φinv m : ℕ) : ℕ := 4 * (φinv + 1) * (Nat.log 2 (2 * m) + 1) + 2

section
variable {C : Finset (Sym2 V)}

omit [Fintype V] [DecidableEq V] in
@[simp] lemma clGraph_adj {u v : V} : (clGraph C).Adj u v ↔ u ≠ v ∧ s(u, v) ∈ C := Iff.rfl

omit [Fintype V] [DecidableEq V] in
lemma clGraph_adj_of_mem (hC : NoLoops C) {u v : V} (h : s(u, v) ∈ C) : (clGraph C).Adj u v :=
  ⟨fun huv => hC _ h (Sym2.mk_isDiag_iff.2 huv), h⟩

lemma mem_nodes_of_adj {u v : V} (h : (clGraph C).Adj u v) : u ∈ nodes C :=
  mem_nodes.2 ⟨_, h.2, Sym2.mem_mk_left u v⟩

lemma mem_nodes_of_reachable {u v : V} (hu : u ∈ nodes C) (h : (clGraph C).Reachable u v) :
    v ∈ nodes C := by
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => exact hu
  | cons hadj _ => exact mem_nodes_of_adj hadj

lemma mem_nodes_of_reachable_of_ne {u v : V} (h : (clGraph C).Reachable u v) (huv : u ≠ v) :
    u ∈ nodes C := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl huv
  | cons hadj _ => exact mem_nodes_of_adj hadj

lemma card_pos_of_mem_nodes {u : V} (hu : u ∈ nodes C) : 0 < C.card := by
  obtain ⟨e, he, _⟩ := mem_nodes.1 hu
  exact card_pos.2 ⟨e, he⟩

lemma nodes_nonempty_iff : (nodes C).Nonempty ↔ C.Nonempty := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨e, he, _⟩ := mem_nodes.1 hu
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, mem_nodes.2 ⟨_, he, Sym2.mem_mk_left a b⟩⟩

lemma nodes_nonempty (hne : C.Nonempty) : (nodes C).Nonempty := nodes_nonempty_iff.2 hne

omit [Fintype V] [DecidableEq V] in
/-- A walk of `clGraph C` gives an edge walk (`IsEdgeWalk`) along edges of `C`, of the same
length. -/
lemma isEdgeWalk_edges {u v : V} (p : (clGraph C).Walk u v) :
    IsEdgeWalk p.edges u v ∧ ∀ e ∈ p.edges, e ∈ C := by
  induction p with
  | nil => exact ⟨rfl, by simp⟩
  | cons h p ih =>
    refine ⟨⟨_, rfl, ih.1⟩, ?_⟩
    intro e he
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.2
    · exact ih.2 e he

/-! ## Volumes -/

omit [Fintype V] in
lemma vol_mono {S T : Finset V} (h : S ⊆ T) : vol C S ≤ vol C T :=
  sum_le_sum_of_subset h

omit [Fintype V] in
lemma vol_union {S T : Finset V} (h : Disjoint S T) : vol C (S ∪ T) = vol C S + vol C T :=
  sum_union h

omit [Fintype V] in
lemma vol_sdiff_add {S T : Finset V} (h : S ⊆ T) : vol C (T \ S) + vol C S = vol C T :=
  sum_sdiff h

lemma vol_nodes (hC : NoLoops C) : vol C (nodes C) = 2 * C.card := sum_degIn hC

lemma vol_add_vol_nodes_sdiff (hC : NoLoops C) {S : Finset V} (hS : S ⊆ nodes C) :
    vol C S + vol C (nodes C \ S) = 2 * C.card := by
  rw [← vol_nodes hC, add_comm]; exact vol_sdiff_add hS

omit [Fintype V] in
/-- A set of edges of `C`, each with an endpoint in `T`, has at most `vol C T` elements. -/
lemma card_le_vol {D : Finset (Sym2 V)} {T : Finset V} (hD : D ⊆ C)
    (h : ∀ e ∈ D, ∃ v ∈ T, v ∈ e) : D.card ≤ vol C T :=
  calc D.card ≤ (T.biUnion (fun v => C.filter (fun e => v ∈ e))).card := by
        apply card_le_card
        intro e he
        obtain ⟨v, hv, hve⟩ := h e he
        exact mem_biUnion.2 ⟨v, hv, mem_filter.2 ⟨hD he, hve⟩⟩
    _ ≤ ∑ v ∈ T, (C.filter (fun e => v ∈ e)).card := card_biUnion_le
    _ = vol C T := rfl

private lemma mem_cutEdges' {S : Finset V} {e : Sym2 V} :
    e ∈ cutEdges C S ↔ e ∈ C ∧ (∃ u ∈ e, u ∈ S) ∧ (∃ u ∈ e, u ∉ S) := by
  unfold cutEdges; exact mem_filter

/-! ## BFS balls -/

/-- The ball of radius `r` around `u` in `clGraph C`. -/
noncomputable def clBall (C : Finset (Sym2 V)) (u : V) (r : ℕ) : Finset V := by
  classical exact univ.filter (fun x => ∃ p : (clGraph C).Walk u x, p.length ≤ r)

omit [DecidableEq V] in
lemma mem_clBall {u x : V} {r : ℕ} :
    x ∈ clBall C u r ↔ ∃ p : (clGraph C).Walk u x, p.length ≤ r := by
  unfold clBall; simp

omit [DecidableEq V] in
lemma self_mem_clBall {u : V} {r : ℕ} : u ∈ clBall C u r :=
  mem_clBall.2 ⟨.nil, by simp⟩

omit [DecidableEq V] in
lemma clBall_mono {u : V} {r s : ℕ} (h : r ≤ s) : clBall C u r ⊆ clBall C u s := fun _ hx =>
  let ⟨p, hp⟩ := mem_clBall.1 hx
  mem_clBall.2 ⟨p, hp.trans h⟩

lemma clBall_subset_nodes {u : V} (hu : u ∈ nodes C) (r : ℕ) : clBall C u r ⊆ nodes C :=
  fun _ hx =>
  let ⟨p, _⟩ := mem_clBall.1 hx
  mem_nodes_of_reachable hu ⟨p⟩

omit [DecidableEq V] in
lemma mem_clBall_succ {u x y : V} {r : ℕ} (hx : x ∈ clBall C u r) (hadj : (clGraph C).Adj x y) :
    y ∈ clBall C u (r + 1) := by
  obtain ⟨p, hp⟩ := mem_clBall.1 hx
  exact mem_clBall.2 ⟨p.concat hadj, by rw [Walk.length_concat]; omega⟩

/-- Every cut edge of a ball leads to a node of the next layer, so the next ball gains at least
the number of cut edges in volume. -/
lemma vol_clBall_succ (u : V) (r : ℕ) :
    vol C (clBall C u r) + (cutEdges C (clBall C u r)).card ≤ vol C (clBall C u (r + 1)) := by
  have hsub : clBall C u r ⊆ clBall C u (r + 1) := clBall_mono (Nat.le_succ r)
  rw [← vol_sdiff_add hsub, add_comm]
  apply Nat.add_le_add_right
  apply card_le_vol (fun e he => (mem_cutEdges'.1 he).1)
  intro e he
  obtain ⟨heC, ⟨a, hae, ha⟩, ⟨b, hbe, hb⟩⟩ := mem_cutEdges'.1 he
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have he' : e = s(a, b) := (Sym2.mem_and_mem_iff hab).1 ⟨hae, hbe⟩
  subst he'
  exact ⟨b, mem_sdiff.2 ⟨mem_clBall_succ ha ⟨hab, heC⟩, hb⟩, hbe⟩

/-- Growth of BFS balls in an expander: a ball holds more than half the volume, or
`φinv ^ r · vol(B_r) ≥ (φinv + 1) ^ r`. -/
lemma clBall_growth {φinv : ℕ} (hC : NoLoops C) (hexp : IsExpander C φinv) {u : V}
    (hu : u ∈ nodes C) (r : ℕ) :
    C.card < vol C (clBall C u r) ∨ (φinv + 1) ^ r ≤ φinv ^ r * vol C (clBall C u r) := by
  induction r with
  | zero =>
    right
    simp only [pow_zero, one_mul]
    calc 1 ≤ degIn C u := degIn_pos hu
      _ ≤ vol C (clBall C u 0) := single_le_sum (fun _ _ => Nat.zero_le _) self_mem_clBall
  | succ r ih =>
    have hgrow := vol_clBall_succ (C := C) u r
    by_cases hbig : C.card < vol C (clBall C u r)
    · left; omega
    right
    replace hbig := not_lt.1 hbig
    rcases ih with ih | ih
    · omega
    have hsub := clBall_subset_nodes hu r
    have htot := vol_add_vol_nodes_sdiff hC hsub
    have hmin := hexp _ hsub
    rw [min_eq_left (by omega)] at hmin
    have h2 : (φinv + 1) * vol C (clBall C u r) ≤ φinv * vol C (clBall C u (r + 1)) :=
      calc (φinv + 1) * vol C (clBall C u r)
          = φinv * vol C (clBall C u r) + vol C (clBall C u r) := by ring
        _ ≤ φinv * vol C (clBall C u r) + φinv * (cutEdges C (clBall C u r)).card := by omega
        _ = φinv * (vol C (clBall C u r) + (cutEdges C (clBall C u r)).card) := by ring
        _ ≤ φinv * vol C (clBall C u (r + 1)) := Nat.mul_le_mul_left _ hgrow
    calc (φinv + 1) ^ (r + 1) = (φinv + 1) * (φinv + 1) ^ r := pow_succ' _ _
      _ ≤ (φinv + 1) * (φinv ^ r * vol C (clBall C u r)) := Nat.mul_le_mul_left _ ih
      _ = φinv ^ r * ((φinv + 1) * vol C (clBall C u r)) := by ring
      _ ≤ φinv ^ r * (φinv * vol C (clBall C u (r + 1))) := Nat.mul_le_mul_left _ h2
      _ = φinv ^ (r + 1) * vol C (clBall C u (r + 1)) := by ring

end

/-! ## Arithmetic -/

private lemma bernoulli_aux (φ n : ℕ) : φ ^ (n + 1) + (n + 1) * φ ^ n ≤ (φ + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (φ + 1) * (φ ^ (n + 1) + (n + 1) * φ ^ n) =
        φ ^ (n + 1 + 1) + (n + 1 + 1) * φ ^ (n + 1) + (n + 1) * φ ^ n := by ring
    calc φ ^ (n + 1 + 1) + (n + 1 + 1) * φ ^ (n + 1)
        ≤ (φ + 1) * (φ ^ (n + 1) + (n + 1) * φ ^ n) := by rw [e]; exact Nat.le_add_right _ _
      _ ≤ (φ + 1) * (φ + 1) ^ (n + 1) := Nat.mul_le_mul_left _ ih
      _ = (φ + 1) ^ (n + 1 + 1) := (pow_succ' _ _).symm

/-- `(1 + 1/φ) ^ (φ + 1) ≥ 2`, in integers. -/
private lemma two_mul_pow_le (φ : ℕ) : 2 * φ ^ (φ + 1) ≤ (φ + 1) ^ (φ + 1) := by
  have h := bernoulli_aux φ φ
  have : φ ^ (φ + 1) ≤ (φ + 1) * φ ^ φ := by
    rw [pow_succ']; exact Nat.mul_le_mul_right _ (Nat.le_succ φ)
  omega

private lemma two_pow_mul_pow_le (φ k : ℕ) :
    2 ^ k * φ ^ ((φ + 1) * k) ≤ (φ + 1) ^ ((φ + 1) * k) := by
  rw [pow_mul, pow_mul, ← mul_pow]
  exact Nat.pow_le_pow_left (two_mul_pow_le φ) k

/-! ## Diameter -/

section
variable {C : Finset (Sym2 V)}

/-- After `(φinv + 1) · log₂ (2|C|)` BFS steps a ball holds more than half of the volume. -/
lemma card_lt_vol_clBall {φinv : ℕ} (hC : NoLoops C) (hexp : IsExpander C φinv) {u : V}
    (hu : u ∈ nodes C) :
    C.card < vol C (clBall C u ((φinv + 1) * Nat.log 2 (2 * C.card))) := by
  set k := Nat.log 2 (2 * C.card)
  set R := (φinv + 1) * k
  rcases clBall_growth hC hexp hu R with h | h
  · exact h
  by_contra hle
  replace hle := not_lt.1 hle
  have hk : C.card < 2 ^ k := by
    have : 2 * C.card < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) _
    rw [pow_succ] at this; omega
  have hpow := two_pow_mul_pow_le φinv k
  have hpos : 0 < (φinv + 1) ^ R := by positivity
  have h3 : (φinv + 1) ^ R ≤ φinv ^ R * C.card := h.trans (Nat.mul_le_mul_left _ hle)
  rcases Nat.eq_zero_or_pos (φinv ^ R) with h0 | h0
  · rw [h0, zero_mul] at h3; omega
  · have h4 : 2 ^ k * φinv ^ R ≤ C.card * φinv ^ R := by
      rw [mul_comm C.card]; exact hpow.trans h3
    have := Nat.le_of_mul_le_mul_right h4 h0
    omega

/-- **Diameter of expanders.** Any two nodes of a `1/φinv`-expander cluster are connected in
`clGraph C`, at distance at most `diamBound φinv |C|`. -/
theorem expander_dist_le {φinv : ℕ} (hC : NoLoops C) (hexp : IsExpander C φinv)
    {u v : V} (hu : u ∈ nodes C) (hv : v ∈ nodes C) :
    (clGraph C).Reachable u v ∧ (clGraph C).dist u v ≤ diamBound φinv C.card := by
  set k := Nat.log 2 (2 * C.card)
  set R := (φinv + 1) * k
  have h1 : C.card < vol C (clBall C u R) := card_lt_vol_clBall hC hexp hu
  have h2 : C.card < vol C (clBall C v R) := card_lt_vol_clBall hC hexp hv
  have hnd : ¬ Disjoint (clBall C u R) (clBall C v R) := by
    intro hd
    have := vol_mono (C := C) (union_subset (clBall_subset_nodes hu R) (clBall_subset_nodes hv R))
    rw [vol_union hd, vol_nodes hC] at this
    omega
  obtain ⟨x, hxu, hxv⟩ := not_disjoint_iff.1 hnd
  obtain ⟨p, hp⟩ := mem_clBall.1 hxu
  obtain ⟨q, hq⟩ := mem_clBall.1 hxv
  have hw : (p.append q.reverse).length ≤ 2 * R := by
    rw [Walk.length_append, Walk.length_reverse]; omega
  refine ⟨⟨p.append q.reverse⟩, (dist_le _).trans (hw.trans ?_)⟩
  show _ ≤ 4 * (φinv + 1) * (k + 1) + 2
  have : 2 * R ≤ 4 * (φinv + 1) * (k + 1) := by
    calc 2 * R = 2 * (φinv + 1) * k := by ring
      _ ≤ 4 * (φinv + 1) * (k + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) (Nat.le_succ k)
  omega

/-- In a `1/φinv`-expander cluster, every distance of `clGraph C` is at most
`diamBound φinv |C|` (pairs outside `nodes C` are isolated or equal, with distance `0`). -/
theorem clGraph_dist_le_diamBound {φinv : ℕ} (hC : NoLoops C) (hexp : IsExpander C φinv)
    (u v : V) : (clGraph C).dist u v ≤ diamBound φinv C.card := by
  by_cases h : (clGraph C).Reachable u v
  · by_cases huv : u = v
    · subst huv; simp
    · exact (expander_dist_le hC hexp (mem_nodes_of_reachable_of_ne h huv)
        (mem_nodes_of_reachable_of_ne h.symm (Ne.symm huv))).2
  · rw [dist_eq_zero_of_not_reachable h]; exact Nat.zero_le _

/-- An expander cluster is connected: any two nodes of `C` are reachable in `clGraph C`. -/
theorem expander_reachable {φinv : ℕ} (hC : NoLoops C) (hexp : IsExpander C φinv)
    {u v : V} (hu : u ∈ nodes C) (hv : v ∈ nodes C) : (clGraph C).Reachable u v :=
  (expander_dist_le hC hexp hu hv).1

/-- Any two nodes of a `1/φinv`-expander cluster are joined by an edge walk along edges of `C` of
length at most `diamBound φinv |C|`. -/
theorem expander_exists_edgeWalk {φinv : ℕ} (hC : NoLoops C) (hexp : IsExpander C φinv)
    {u v : V} (hu : u ∈ nodes C) (hv : v ∈ nodes C) :
    ∃ l : List (Sym2 V), IsEdgeWalk l u v ∧ (∀ e ∈ l, e ∈ C) ∧
      l.length ≤ diamBound φinv C.card := by
  obtain ⟨hr, hd⟩ := expander_dist_le hC hexp hu hv
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨h1, h2⟩ := isEdgeWalk_edges p
  exact ⟨p.edges, h1, h2, by rw [Walk.length_edges, hp]; exact hd⟩

end

end APSP.Stoc
