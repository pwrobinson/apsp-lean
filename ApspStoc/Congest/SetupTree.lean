import ApspStoc.Congest.SetupProto

/-!
# Cluster setup in CONGEST: graph facts

The combinatorics behind the run of `setupProto` on a cluster `C` whose graph `clGraph C` has
diameter at most `D` on `nodes C`:

* `ballSup C y j v`: the maximum of `y` over the ball of radius `j` around `v` (the value of a
  max-flood after `j` rounds);
* `parOf C M v`: the parent of `v` in the BFS tree rooted at `M` (a neighbour one step closer);
* `ccz C ℓ j v`: the value sent by `v` in the `j`-th counting round; it stabilizes after `D + 1`
  rounds, and then the root's value is `n_C` (a telescoping sum);
* `gos C ℓ I k v`: the items known to `v` after `k` gossip windows on the BFS tree when every node
  `u` starts with `I u`; after `2D` windows it is the set of all items (`gos_full`). Instances:
  `Sg` (phase G: the (ID, degree) pairs; finally the true table) and `Pg` (phase H: the ports of
  `A(C)`, initially known to their nodes only; finally `portsA C`).
-/

namespace APSP.Stoc.Congest

open APSP Finset SimpleGraph

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

section Balls

variable (C : Finset (Sym2 V))

/-- the maximum of `y` over the ball of radius `j` around `v` -/
noncomputable def ballSup (y : V → ℕ) (j : ℕ) (v : V) : ℕ := (clBall C v j).sup y

variable {C}

lemma mem_clBall_iff_dist {v x : V} {j : ℕ} :
    x ∈ clBall C v j ↔ (clGraph C).Reachable v x ∧ (clGraph C).dist v x ≤ j := by
  rw [mem_clBall]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨⟨p⟩, (dist_le p).trans hp⟩
  · rintro ⟨hr, hd⟩
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    exact ⟨p, hp ▸ hd⟩

lemma mem_clBall_succ_iff {v x : V} {j : ℕ} :
    x ∈ clBall C v (j + 1) ↔ x ∈ clBall C v j ∨ ∃ u, (clGraph C).Adj u v ∧ x ∈ clBall C u j := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := mem_clBall.1 h
    cases p with
    | nil => exact Or.inl self_mem_clBall
    | cons hadj q =>
      rw [Walk.length_cons] at hp
      exact Or.inr ⟨_, hadj.symm, mem_clBall.2 ⟨q, by omega⟩⟩
  · rintro (h | ⟨u, hadj, h⟩)
    · exact clBall_mono (Nat.le_succ j) h
    · obtain ⟨q, hq⟩ := mem_clBall.1 h
      exact mem_clBall.2 ⟨.cons hadj.symm q, by rw [Walk.length_cons]; omega⟩

lemma clBall_succ_eq (v : V) (j : ℕ) :
    clBall C v (j + 1) =
      clBall C v j ∪ (univ.filter (fun u => (clGraph C).Adj u v)).biUnion (fun u => clBall C u j) := by
  ext x
  rw [mem_clBall_succ_iff, mem_union, mem_biUnion]
  simp only [mem_filter, mem_univ, true_and]

lemma clBall_zero (v : V) : clBall C v 0 = {v} := by
  ext x
  rw [mem_clBall, mem_singleton]
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | nil => rfl
    | cons _ q => rw [Walk.length_cons] at hp; omega
  · rintro rfl; exact ⟨.nil, le_rfl⟩

lemma ballSup_zero (y : V → ℕ) (v : V) : ballSup C y 0 v = y v := by
  simp [ballSup, clBall_zero]

lemma ballSup_succ (y : V → ℕ) (j : ℕ) (v : V) :
    ballSup C y (j + 1) v = max (ballSup C y j v)
      ((univ.filter (fun u => (clGraph C).Adj u v)).sup (fun u => ballSup C y j u)) := by
  unfold ballSup
  rw [clBall_succ_eq, sup_union, sup_biUnion]

lemma le_ballSup (y : V → ℕ) {j : ℕ} {v x : V} (hx : x ∈ clBall C v j) : y x ≤ ballSup C y j v :=
  le_sup hx

lemma ballSup_le {y : V → ℕ} {j : ℕ} {v : V} {b : ℕ} (h : ∀ x ∈ clBall C v j, y x ≤ b) :
    ballSup C y j v ≤ b := Finset.sup_le h

lemma exists_ballSup (y : V → ℕ) (j : ℕ) (v : V) : ∃ x ∈ clBall C v j, ballSup C y j v = y x :=
  exists_mem_eq_sup _ ⟨v, self_mem_clBall⟩ y

lemma ballSup_mono_ball (y : V → ℕ) {j : ℕ} {u v : V} (hadj : (clGraph C).Adj u v) :
    ballSup C y j u ≤ ballSup C y (j + 1) v :=
  Finset.sup_le (fun _ hx => le_ballSup y (mem_clBall_succ_iff.2 (Or.inr ⟨u, hadj, hx⟩)))

/-- the maximum of the numbers received from the neighbours -/
lemma sup_numOf_adj (f : V → ℕ) (v : V) :
    univ.sup (fun u => numOf (if (clGraph C).Adj u v then some (Word.num (V := V) (f u)) else none)) =
      (univ.filter (fun u => (clGraph C).Adj u v)).sup f := by
  have : (fun u => numOf (if (clGraph C).Adj u v then some (Word.num (V := V) (f u)) else none)) =
      fun u => if (clGraph C).Adj u v then f u else 0 := by
    funext u; split_ifs <;> rfl
  rw [this, sup_ite]
  simp

/-- the flood step -/
lemma ballSup_succ_numOf (y : V → ℕ) (j : ℕ) (v : V) :
    max (ballSup C y j v) (univ.sup (fun u => numOf (if (clGraph C).Adj u v then
      some (Word.num (V := V) (ballSup C y j u)) else none))) = ballSup C y (j + 1) v := by
  rw [sup_numOf_adj, ballSup_succ]

end Balls

/-! ## Distances and BFS parents -/

section Parents

variable (C : Finset (Sym2 V))

/-- the parent of `v` in the BFS tree rooted at `M`: a neighbour one step closer to `M` -/
noncomputable def parOf (M v : V) : Option V :=
  if v = M then none else
    suPick (univ.filter (fun u => (clGraph C).Adj v u ∧
      (clGraph C).dist M u + 1 = (clGraph C).dist M v))

variable {C}

lemma parOf_self (M : V) : parOf C M M = none := by simp [parOf]

lemma parOf_spec {M v p : V} (h : parOf C M v = some p) :
    (clGraph C).Adj v p ∧ (clGraph C).dist M p + 1 = (clGraph C).dist M v := by
  unfold parOf at h
  split_ifs at h
  have := suPick_mem h
  simpa using this

lemma parOf_ne_self {M v p : V} (h : parOf C M v = some p) : v ≠ M := by
  intro hv; subst hv; rw [parOf_self] at h; cases h

lemma dist_le_of_adj {u v M : V} (hadj : (clGraph C).Adj v u) (hr : (clGraph C).Reachable u M) :
    (clGraph C).dist v M ≤ (clGraph C).dist u M + 1 := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  calc (clGraph C).dist v M ≤ (Walk.cons hadj p).length := dist_le _
    _ = _ := by rw [Walk.length_cons, hp]

lemma exists_adj_dist_pred {M v : V} (hr : (clGraph C).Reachable M v) (hv : v ≠ M) :
    ∃ u, (clGraph C).Adj v u ∧ (clGraph C).dist M u + 1 = (clGraph C).dist M v := by
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  cases p with
  | nil => exact absurd rfl hv
  | cons hadj q =>
    rename_i u
    refine ⟨u, hadj, ?_⟩
    rw [Walk.length_cons] at hp
    have hr' : (clGraph C).Reachable u M := ⟨q⟩
    have h1 := dist_le q
    have h2 := dist_le_of_adj hadj hr'
    rw [dist_comm (u := M) (v := u), dist_comm (u := M) (v := v)]
    omega

lemma parOf_isSome {M v : V} (hr : (clGraph C).Reachable M v) (hv : v ≠ M) :
    (parOf C M v).isSome := by
  unfold parOf
  rw [ite_eq_right hv]
  obtain ⟨u, hu⟩ := exists_adj_dist_pred hr hv
  exact suPick_isSome ⟨u, by simpa using hu⟩

/-- the key fact for the parent pointers of the max-flood: if `M` enters the ball of `v` at
radius `t + 1`, a neighbour `u` has `M` in its ball of radius `t` iff `u` is one step closer to
`M` -/
lemma mem_clBall_iff_dist_pred {M v u : V} {t : ℕ} (h1 : M ∈ clBall C v (t + 1))
    (h2 : M ∉ clBall C v t) (hadj : (clGraph C).Adj u v) :
    M ∈ clBall C u t ↔ (clGraph C).dist M u + 1 = (clGraph C).dist M v := by
  rw [mem_clBall_iff_dist] at h1 h2 ⊢
  have hvM : (clGraph C).dist v M = t + 1 := by
    have := h1.2
    by_contra hne
    exact h2 ⟨h1.1, by omega⟩
  rw [dist_comm (u := M) (v := u), dist_comm (u := M) (v := v), hvM]
  constructor
  · rintro ⟨hr, hd⟩
    have := dist_le_of_adj hadj.symm hr
    omega
  · intro hd
    exact ⟨hadj.reachable.trans h1.1, by omega⟩

end Parents

/-! ## The BFS tree of a cluster of diameter `≤ D` -/

section Tree

variable {C : Finset (Sym2 V)} {D : ℕ} {ℓ : V}

/-- the cluster is connected with diameter at most `D` -/
def DiamLe (C : Finset (Sym2 V)) (D : ℕ) : Prop :=
  ∀ u ∈ nodes C, ∀ v ∈ nodes C, (clGraph C).Reachable u v ∧ (clGraph C).dist u v ≤ D

lemma clBall_eq_nodes (hd : DiamLe C D) {v : V} (hv : v ∈ nodes C) : clBall C v D = nodes C := by
  apply Subset.antisymm (clBall_subset_nodes hv D)
  intro u hu
  exact mem_clBall_iff_dist.2 (hd v hv u hu)

variable (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C)
include hd hℓ

lemma parOf_eq_none_iff {v : V} (hv : v ∈ nodes C) : parOf C ℓ v = none ↔ v = ℓ := by
  constructor
  · intro h
    by_contra hne
    have := parOf_isSome (hd ℓ hℓ v hv).1 hne
    rw [h] at this; cases this
  · rintro rfl; exact parOf_self _

lemma parOf_mem {v p : V} (_hv : v ∈ nodes C) (h : parOf C ℓ v = some p) :
    p ∈ nodes C ∧ (clGraph C).dist ℓ p + 1 = (clGraph C).dist ℓ v := by
  obtain ⟨hadj, hdist⟩ := parOf_spec h
  exact ⟨mem_nodes_of_adj hadj.symm, hdist⟩

lemma dist_eq_zero_iff' {v : V} (hv : v ∈ nodes C) : (clGraph C).dist ℓ v = 0 ↔ v = ℓ := by
  rw [(hd ℓ hℓ v hv).1.dist_eq_zero_iff]
  exact eq_comm

/-- induction along parent pointers -/
lemma parOf_induction (P : V → Prop) (h0 : P ℓ)
    (hs : ∀ v ∈ nodes C, ∀ p, parOf C ℓ v = some p → P p → P v) :
    ∀ v ∈ nodes C, P v := by
  suffices ∀ d, ∀ v ∈ nodes C, (clGraph C).dist ℓ v = d → P v from
    fun v hv => this _ v hv rfl
  intro d
  induction d with
  | zero =>
    intro v hv h
    rw [(dist_eq_zero_iff' hd hℓ hv).1 h]; exact h0
  | succ d ih =>
    intro v hv h
    have hne : v ≠ ℓ := fun h' => by
      rw [h', dist_self] at h; omega
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (parOf_isSome (hd ℓ hℓ v hv).1 hne)
    obtain ⟨hpC, hpd⟩ := parOf_mem hd hℓ hv hp
    exact hs v hv p hp (ih p hpC (by omega))

end Tree

/-! ## Counting -/

section Count

variable (C : Finset (Sym2 V)) (ℓ : V)

/-- the value sent by `v` in counting round `j` is `ccz (j + 1) v` -/
noncomputable def ccz : ℕ → V → ℕ
  | 0, _ => 0
  | j + 1, v => 1 + ∑ u ∈ (nodes C).filter (fun u => parOf C ℓ u = some v), ccz j u

/-- the latest counts received from the children -/
noncomputable def latC (j : ℕ) (v : V) : V → ℕ := fun u =>
  if u ∈ nodes C ∧ parOf C ℓ u = some v then ccz C ℓ j u else 0

variable {C ℓ}

lemma ccz_succ (j : ℕ) (v : V) :
    ccz C ℓ (j + 1) v = 1 + ∑ u ∈ (nodes C).filter (fun u => parOf C ℓ u = some v), ccz C ℓ j u :=
  rfl

lemma one_le_ccz_succ (j : ℕ) (v : V) : 1 ≤ ccz C ℓ (j + 1) v := by
  rw [ccz_succ]; omega

lemma sum_latC (j : ℕ) (v : V) :
    ∑ u, latC C ℓ j v u = ∑ u ∈ (nodes C).filter (fun u => parOf C ℓ u = some v), ccz C ℓ j u := by
  unfold latC
  rw [← sum_filter]
  congr 1
  ext u; simp

lemma latC_zero (v : V) : latC C ℓ 0 v = fun _ => 0 := by
  funext u; simp [latC, ccz]

lemma ccz_mono (j : ℕ) : ∀ v, ccz C ℓ j v ≤ ccz C ℓ (j + 1) v := by
  induction j with
  | zero => intro v; exact Nat.zero_le _
  | succ j ih =>
    intro v
    rw [ccz_succ, ccz_succ (j + 1)]
    exact Nat.add_le_add_left (sum_le_sum (fun u _ => ih u)) 1

lemma latC_ne_zero_iff {j : ℕ} {v u : V} :
    latC C ℓ (j + 1) v u ≠ 0 ↔ u ∈ nodes C ∧ parOf C ℓ u = some v := by
  unfold latC
  split_ifs with h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have := one_le_ccz_succ (C := C) (ℓ := ℓ) j u
    omega
  · exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩

variable {D : ℕ} (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C)
include hd hℓ

/-- every non-root node of `C` has exactly one parent in `C` -/
lemma sum_children (f : V → ℕ) :
    ∑ v ∈ nodes C, ∑ u ∈ (nodes C).filter (fun u => parOf C ℓ u = some v), f u =
      ∑ u ∈ (nodes C).erase ℓ, f u := by
  have hmaps : ∀ u ∈ (nodes C).erase ℓ, (parOf C ℓ u).getD ℓ ∈ nodes C := by
    intro u hu
    obtain ⟨hne, hu⟩ := mem_erase.1 hu
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (parOf_isSome (hd ℓ hℓ u hu).1 hne)
    rw [hp]; exact (parOf_mem hd hℓ hu hp).1
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl (fun v hv => ?_)
  congr 1
  ext u
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hu, hp⟩
    exact ⟨⟨parOf_ne_self hp, hu⟩, by rw [hp]; rfl⟩
  · rintro ⟨⟨hne, hu⟩, hp⟩
    obtain ⟨p, hp'⟩ := Option.isSome_iff_exists.1 (parOf_isSome (hd ℓ hℓ u hu).1 hne)
    rw [hp'] at hp ⊢
    exact ⟨hu, by rw [← hp]; rfl⟩

/-- the counts are stable after `D + 1 - dist(ℓ, v)` rounds -/
lemma ccz_stable : ∀ j, ∀ v ∈ nodes C, D + 1 ≤ j + (clGraph C).dist ℓ v →
    ccz C ℓ (j + 1) v = ccz C ℓ j v := by
  intro j
  induction j with
  | zero =>
    intro v hv h
    have := (hd ℓ hℓ v hv).2
    omega
  | succ j ih =>
    intro v hv h
    rw [ccz_succ, ccz_succ j]
    congr 1
    refine sum_congr rfl (fun u hu => ?_)
    obtain ⟨huC, hp⟩ := mem_filter.1 hu
    have := (parOf_mem hd hℓ huC hp).2
    exact ih u huC (by omega)

lemma sum_ccz_succ (j : ℕ) :
    ∑ v ∈ nodes C, ccz C ℓ (j + 1) v = (nodes C).card + ∑ u ∈ (nodes C).erase ℓ, ccz C ℓ j u := by
  simp only [ccz_succ]
  rw [sum_add_distrib, sum_children hd hℓ]
  simp

/-- **The root counts the nodes.** -/
lemma ccz_root : ccz C ℓ (D + 2) ℓ = (nodes C).card := by
  have hst : ∀ v ∈ nodes C, ccz C ℓ (D + 2) v = ccz C ℓ (D + 1) v :=
    fun v hv => ccz_stable hd hℓ (D + 1) v hv (by omega)
  have h1 := sum_ccz_succ hd hℓ (D + 1)
  rw [sum_congr rfl hst, ← add_sum_erase _ _ hℓ] at h1
  rw [hst ℓ hℓ]
  omega

lemma ccz_root_le (j : ℕ) : ccz C ℓ j ℓ ≤ (nodes C).card := by
  cases j with
  | zero => exact Nat.zero_le _
  | succ j =>
    have h1 := sum_ccz_succ hd hℓ j
    rw [← add_sum_erase _ _ hℓ] at h1
    have h2 : ∑ u ∈ (nodes C).erase ℓ, ccz C ℓ j u ≤ ∑ u ∈ (nodes C).erase ℓ, ccz C ℓ (j + 1) u :=
      sum_le_sum (fun u _ => ccz_mono j u)
    omega

lemma ccz_le_root : ∀ v ∈ nodes C, ∀ j, ccz C ℓ j v ≤ ccz C ℓ (j + (clGraph C).dist ℓ v) ℓ := by
  apply parOf_induction hd hℓ
  · intro j; simp
  · intro v hv p hp ih j
    obtain ⟨hpC, hpd⟩ := parOf_mem hd hℓ hv hp
    calc ccz C ℓ j v ≤ ccz C ℓ (j + 1) p := by
          rw [ccz_succ]
          have : ccz C ℓ j v ≤ ∑ u ∈ (nodes C).filter (fun u => parOf C ℓ u = some p), ccz C ℓ j u :=
            single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hv, hp⟩)
          omega
      _ ≤ ccz C ℓ (j + 1 + (clGraph C).dist ℓ p) ℓ := ih (j + 1)
      _ = _ := by congr 1; omega

lemma ccz_le_card (j : ℕ) {v : V} (hv : v ∈ nodes C) : ccz C ℓ j v ≤ (nodes C).card :=
  (ccz_le_root hd hℓ v hv j).trans (ccz_root_le hd hℓ _)

end Count

/-! ## Gossip on the tree -/

section Gossip

variable (C : Finset (Sym2 V)) (ℓ : V)

/-- `u` sends to `v` in the gossip phases: `v` is the parent or a child of `u` -/
def tnb (u v : V) : Prop := parOf C ℓ u = some v ∨ (v ∈ nodes C ∧ parOf C ℓ v = some u)

noncomputable instance (u v : V) : Decidable (tnb C ℓ u v) := by unfold tnb; infer_instance

/-- **Gossip on the tree**: the items known to `v` after `k` windows, when every node `u` starts
with the items `I u` and, in every window, adds the items its parent and its children knew at the
start of the window -/
noncomputable def gos {α : Type} [DecidableEq α] (I : V → Finset α) : ℕ → V → Finset α
  | 0, v => I v
  | k + 1, v => gos I k v ∪ ((nodes C).filter (fun u => tnb C ℓ u v)).biUnion (fun u => gos I k u)

/-- the true (ID, degree) pairs -/
def truePairs : Finset (V × ℕ) := (nodes C).image (fun u => (u, degIn C u))

/-- the pairs known to `v` after `k` windows of phase G -/
noncomputable def Sg (k : ℕ) (v : V) : Finset (V × ℕ) := gos C ℓ (fun u => {(u, degIn C u)}) k v

/-- the initial port sets of phase H: a node of `A(C)` starts with its ports, the others with
none -/
noncomputable def initP (v : V) : Finset (Port V) := if v ∈ aggSet C then portsAt C v else ∅

/-- the ports of `A(C)` known to `v` after `k` windows of phase H -/
noncomputable def Pg (k : ℕ) (v : V) : Finset (Port V) := gos C ℓ (initP C) k v

variable {C ℓ} {α : Type} [DecidableEq α] {I : V → Finset α}

lemma gos_succ (k : ℕ) (v : V) :
    gos C ℓ I (k + 1) v = gos C ℓ I k v ∪
      ((nodes C).filter (fun u => tnb C ℓ u v)).biUnion (fun u => gos C ℓ I k u) :=
  rfl

lemma gos_sub : ∀ k, ∀ v ∈ nodes C, gos C ℓ I k v ⊆ (nodes C).biUnion I := by
  intro k
  induction k with
  | zero =>
    intro v hv
    exact subset_biUnion_of_mem I hv
  | succ k ih =>
    intro v hv
    rw [gos_succ]
    exact union_subset (ih v hv) (biUnion_subset.2 (fun u hu => ih u (mem_filter.1 hu).1))

lemma gos_mono_succ (k : ℕ) (v : V) : gos C ℓ I k v ⊆ gos C ℓ I (k + 1) v := by
  rw [gos_succ]; exact subset_union_left

lemma gos_mono {k k' : ℕ} (h : k ≤ k') (v : V) : gos C ℓ I k v ⊆ gos C ℓ I k' v := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans (gos_mono_succ _ v)

lemma gos_up {k : ℕ} {u p : V} (hu : u ∈ nodes C) (h : parOf C ℓ u = some p) :
    gos C ℓ I k u ⊆ gos C ℓ I (k + 1) p := by
  rw [gos_succ]
  refine Subset.trans ?_ subset_union_right
  exact subset_biUnion_of_mem (fun u => gos C ℓ I k u) (mem_filter.2 ⟨hu, Or.inl h⟩)

section Full

variable {D : ℕ} (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C)
include hd hℓ

lemma gos_down {k : ℕ} {u p : V} (hu : u ∈ nodes C) (h : parOf C ℓ u = some p) :
    gos C ℓ I k p ⊆ gos C ℓ I (k + 1) u := by
  rw [gos_succ]
  refine Subset.trans ?_ subset_union_right
  exact subset_biUnion_of_mem (fun u => gos C ℓ I k u)
    (mem_filter.2 ⟨(parOf_mem hd hℓ hu h).1, Or.inr ⟨hu, h⟩⟩)

lemma gos_to_root : ∀ v ∈ nodes C, ∀ k,
    gos C ℓ I k v ⊆ gos C ℓ I (k + (clGraph C).dist ℓ v) ℓ := by
  apply parOf_induction hd hℓ
  · intro k; simp
  · intro v hv p hp ih k
    have hpd := (parOf_mem hd hℓ hv hp).2
    refine (gos_up hv hp).trans ((ih (k + 1)).trans (gos_mono (by omega) ℓ))

lemma gos_from_root : ∀ v ∈ nodes C, ∀ k,
    gos C ℓ I k ℓ ⊆ gos C ℓ I (k + (clGraph C).dist ℓ v) v := by
  apply parOf_induction hd hℓ
  · intro k; simp
  · intro v hv p hp ih k
    have hpd := (parOf_mem hd hℓ hv hp).2
    refine (ih k).trans ((gos_down hd hℓ hv hp).trans (gos_mono (by omega) v))

/-- **After `2D` windows every node knows all items.** -/
lemma gos_full {v : V} (hv : v ∈ nodes C) : gos C ℓ I (2 * D) v = (nodes C).biUnion I := by
  apply Subset.antisymm (gos_sub _ v hv)
  intro q hq
  obtain ⟨u, hu, hqu⟩ := mem_biUnion.1 hq
  have h1 : q ∈ gos C ℓ I 0 u := hqu
  have h2 := gos_to_root hd hℓ u hu 0 h1
  have h3 : gos C ℓ I (0 + (clGraph C).dist ℓ u) ℓ ⊆ gos C ℓ I D ℓ :=
    gos_mono (by have := (hd ℓ hℓ u hu).2; omega) ℓ
  have h4 := gos_from_root hd hℓ v hv D (h3 h2)
  exact gos_mono (by have := (hd ℓ hℓ v hv).2; omega) v h4

end Full

/-! ### Phase G: the degree table -/

lemma Sg_succ (k : ℕ) (v : V) :
    Sg C ℓ (k + 1) v = Sg C ℓ k v ∪ ((nodes C).filter (fun u => tnb C ℓ u v)).biUnion (fun u => Sg C ℓ k u) :=
  rfl

lemma truePairs_eq_biUnion :
    truePairs C = (nodes C).biUnion (fun u => ({(u, degIn C u)} : Finset (V × ℕ))) := by
  ext q
  simp only [truePairs, mem_image, mem_biUnion, mem_singleton]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

lemma Sg_sub : ∀ k, ∀ v ∈ nodes C, Sg C ℓ k v ⊆ truePairs C := by
  intro k v hv
  rw [truePairs_eq_biUnion]
  exact gos_sub k v hv

lemma card_truePairs_le : (truePairs C).card ≤ (nodes C).card := card_image_le

/-- **After `2D` windows every node knows all pairs.** -/
lemma Sg_full {D : ℕ} (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C) {v : V} (hv : v ∈ nodes C) :
    Sg C ℓ (2 * D) v = truePairs C := by
  rw [truePairs_eq_biUnion]
  exact gos_full hd hℓ hv

/-- The aggregator set computed from the true table is `A(C)`. -/
lemma aggT_truePairs : aggT (truePairs C) = aggSet C := (aggSet_eq_aggT C).symm

/-! ### Phase H: the ports of `A(C)` -/

lemma Pg_succ (k : ℕ) (v : V) :
    Pg C ℓ (k + 1) v = Pg C ℓ k v ∪ ((nodes C).filter (fun u => tnb C ℓ u v)).biUnion (fun u => Pg C ℓ k u) :=
  rfl

lemma biUnion_initP : (nodes C).biUnion (initP C) = portsA C := by
  ext p
  simp only [mem_biUnion, initP, portsA, portsOf]
  constructor
  · rintro ⟨v, _, hp⟩
    split_ifs at hp with hA
    · exact ⟨v, hA, hp⟩
    · simp at hp
  · rintro ⟨v, hA, hp⟩
    have hv : v ∈ nodes C := by
      obtain ⟨-, he, hve⟩ := mem_portsAt.1 hp
      exact mem_nodes.2 ⟨_, he, hve⟩
    exact ⟨v, hv, by rw [ite_eq_left hA]; exact hp⟩

lemma Pg_sub : ∀ k, ∀ v ∈ nodes C, Pg C ℓ k v ⊆ portsA C := by
  intro k v hv
  rw [← biUnion_initP]
  exact gos_sub k v hv

/-- **After `2D` windows of phase H every node knows the ports of `A(C)`.** -/
lemma Pg_full {D : ℕ} (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C) {v : V} (hv : v ∈ nodes C) :
    Pg C ℓ (2 * D) v = portsA C := by
  rw [← biUnion_initP]
  exact gos_full hd hℓ hv

end Gossip

end APSP.Stoc.Congest
