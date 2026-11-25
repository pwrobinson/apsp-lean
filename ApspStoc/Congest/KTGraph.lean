import ApspStoc.Congest.KTSim
import ApspStoc.Congest.TreeCastAux

/-!
# The global objects of the gather phase

The gather phase (`KTGather.lean`) lets every node of `S` learn `S`. Its schedule is described by
global objects, defined here from `S` and the network `N`:

* `idx u < |U|`: the index of an ID in the universe (`Fintype.equivFin`), known to every node.
  `argminIdx s`: the element of least index of a finite set.
* **Flooding from a set** `A ⊆ S`: the distance `dA A w` of `w` to `A`, and the flood parent
  `parA A w` of `w ∉ A`: its neighbour of least index one step closer to `A`.
* **Binary search for the least index** `mstar` of a node of `S`: after `b` windows the search
  interval is `[gLo b, gLo b + 2^(B - b))` with `B = nB U = lg |U|`, and window `b` floods from the
  nodes `srcB b` of `S` with index in the lower half. After `B` windows, `gLo B = mstar`, so
  `srcB B` is the single node of least index, the leader.
* **The BFS tree** from the leader: parent `kpar`, depth `kdep` (the flood of window `B`), subtree
  sizes `ksz`, and preorder numbers `kpre` (children in increasing index order). `kpre` is
  injective on `S` with values `< |S|` (`kpre_inj`, `kpre_lt`).
-/

namespace APSP.Stoc.Congest

namespace KT

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {U : Type} [Fintype U] [DecidableEq U]

/-! ## Indices -/

/-- the index of an ID in the universe -/
noncomputable def idx (u : U) : ℕ := (Fintype.equivFin U u : ℕ)

lemma idx_lt (u : U) : idx u < Fintype.card U := (Fintype.equivFin U u).2

lemma idx_inj : Function.Injective (idx : U → ℕ) := fun _ _ h =>
  (Fintype.equivFin U).injective (Fin.ext h)

/-- the element of least index of a finite set (`none` if it is empty) -/
noncomputable def argminIdx (s : Finset U) : Option U :=
  if h : s.Nonempty then some (s.exists_min_image idx h).choose else none

lemma argminIdx_mem {s : Finset U} {x : U} (h : argminIdx s = some x) : x ∈ s := by
  unfold argminIdx at h
  split_ifs at h with hs
  cases h
  exact (s.exists_min_image idx hs).choose_spec.1

lemma argminIdx_eq_none {s : Finset U} : argminIdx s = none ↔ s = ∅ := by
  unfold argminIdx
  split_ifs with hs
  · simp [hs.ne_empty]
  · simp [not_nonempty_iff_eq_empty.1 hs]

lemma argminIdx_of_sub {s : Finset U} {x : U} (hx : x ∈ s) (h : ∀ y ∈ s, y = x) :
    argminIdx s = some x := by
  have hs : s.Nonempty := ⟨x, hx⟩
  unfold argminIdx
  rw [dite_eq_left hs]
  exact congrArg some (h _ (s.exists_min_image idx hs).choose_spec.1)

lemma argminIdx_isSome {s : Finset U} : (argminIdx s).isSome ↔ s.Nonempty := by
  rw [← not_iff_not, Option.not_isSome_iff_eq_none, argminIdx_eq_none, not_nonempty_iff_eq_empty]

/-! ## Distances and flooding from a set -/

section Dist

variable (S : Finset U) (N : WNet S)

/-- the distance in the network between two IDs (`0` if one of them is not in `S`) -/
noncomputable def dU (a w : U) : ℕ :=
  if h : a ∈ S ∧ w ∈ S then N.G.dist ⟨a, h.1⟩ ⟨w, h.2⟩ else 0

/-- the distance of `w` to the set `A` -/
noncomputable def dA (A : Finset U) (w : U) : ℕ :=
  if h : A.Nonempty then A.inf' h (fun a => dU S N a w) else 0

open Classical in
/-- the flood parent of `w ∉ A`: its neighbour of least index one step closer to `A` -/
noncomputable def parA (A : Finset U) (w : U) : Option U :=
  if w ∈ S ∧ w ∉ A then
    argminIdx (univ.filter (fun v => (ktInst S N).G.Adj v w ∧ dA S N A v + 1 = dA S N A w))
  else none

variable {S N}

lemma dist_adj_le' {ρ u w : S} (h : N.G.Adj u w) : N.G.dist ρ u ≤ N.G.dist ρ w + 1 := by
  obtain ⟨p, hp⟩ := N.conn.exists_walk_length_eq_dist ρ w
  have := SimpleGraph.dist_le (p.concat h.symm)
  rw [SimpleGraph.Walk.length_concat, hp] at this
  exact this

lemma exists_closer' {ρ v : S} (hv : v ≠ ρ) :
    ∃ w, N.G.Adj w v ∧ N.G.dist ρ w + 1 = N.G.dist ρ v := by
  obtain ⟨p, hp⟩ := N.conn.exists_walk_length_eq_dist v ρ
  obtain ⟨w, hadj, q, rfl⟩ := p.exists_eq_cons_of_ne hv
  have h1 := SimpleGraph.dist_le q.reverse
  rw [SimpleGraph.Walk.length_reverse] at h1
  have h2 := dist_adj_le' (N := N) (ρ := ρ) hadj
  simp only [SimpleGraph.Walk.length_cons] at hp
  rw [SimpleGraph.dist_comm] at hp
  refine ⟨w, hadj.symm, by omega⟩

lemma dist_lt_card' (ρ v : S) : N.G.dist ρ v < S.card := by
  obtain ⟨p, hp, hl⟩ := N.conn.exists_path_of_dist ρ v
  rw [← hl, ← Fintype.card_coe]; exact hp.length_lt

lemma dU_sub (a w : S) : dU S N a.1 w.1 = N.G.dist a w := by
  unfold dU; rw [dite_eq_left ⟨a.2, w.2⟩]

lemma dU_mk {a w : U} (ha : a ∈ S) (hw : w ∈ S) : dU S N a w = N.G.dist ⟨a, ha⟩ ⟨w, hw⟩ :=
  dU_sub ⟨a, ha⟩ ⟨w, hw⟩

variable {A : Finset U}

lemma dA_exists (hne : A.Nonempty) (w : U) : ∃ a ∈ A, dA S N A w = dU S N a w := by
  unfold dA; rw [dite_eq_left hne]; exact exists_mem_eq_inf' hne _

lemma dA_le {a w : U} (ha : a ∈ A) : dA S N A w ≤ dU S N a w := by
  unfold dA; rw [dite_eq_left ⟨a, ha⟩]; exact inf'_le _ ha

lemma dA_zero (hA : A ⊆ S) (hne : A.Nonempty) {w : U} (hw : w ∈ S) :
    dA S N A w = 0 ↔ w ∈ A := by
  constructor
  · intro h
    obtain ⟨a, ha, hd⟩ := dA_exists hne w
    rw [h] at hd
    have haS := hA ha
    rw [dU_mk haS hw] at hd
    have := (N.conn.dist_eq_zero_iff).1 hd.symm
    have : a = w := congrArg Subtype.val this
    rw [← this]; exact ha
  · intro h
    have := dA_le (S := S) (N := N) h (w := w)
    rw [show dU S N w w = 0 by rw [dU_mk hw hw]; simp] at this
    omega

lemma dA_adj (hne : A.Nonempty) {v w : U} (h : (ktInst S N).G.Adj v w) :
    dA S N A v ≤ dA S N A w + 1 := by
  obtain ⟨hv, hw, hadj⟩ := ktInst_adj.1 h
  obtain ⟨a, ha, hd⟩ := dA_exists (S := S) (N := N) hne w
  have h1 := dA_le (S := S) (N := N) ha (w := v)
  by_cases haS : a ∈ S
  · rw [dU_mk haS hv] at h1
    rw [dU_mk haS hw] at hd
    have := dist_adj_le' (N := N) (ρ := ⟨a, haS⟩) hadj
    omega
  · have : dU S N a v = 0 := by unfold dU; rw [dite_eq_right (fun h => haS h.1)]
    omega

lemma dA_closer (hA : A ⊆ S) (hne : A.Nonempty) {w : U} (hw : w ∈ S) (hwA : w ∉ A) :
    ∃ v, (ktInst S N).G.Adj v w ∧ dA S N A v + 1 = dA S N A w := by
  obtain ⟨a, ha, hd⟩ := dA_exists (S := S) (N := N) hne w
  have haS := hA ha
  have hne' : (⟨w, hw⟩ : S) ≠ ⟨a, haS⟩ := fun h => hwA (by
    have : w = a := congrArg Subtype.val h
    rw [this]; exact ha)
  obtain ⟨v, hadj, hdv⟩ := exists_closer' (N := N) hne'
  refine ⟨v.1, ktInst_adj_sub.2 hadj, ?_⟩
  have h1 : dA S N A v.1 ≤ N.G.dist ⟨a, haS⟩ v := by
    have := dA_le (S := S) (N := N) ha (w := v.1); rwa [dU_mk haS v.2] at this
  have h2 : dA S N A w ≤ dA S N A v.1 + 1 :=
    dA_adj (S := S) (N := N) hne (ktInst_adj_sub.2 hadj.symm)
  rw [dU_mk haS hw] at hd
  omega

lemma dA_lt (hne : A.Nonempty) (hA : A ⊆ S) {w : U} (hw : w ∈ S) : dA S N A w < S.card := by
  obtain ⟨a, ha⟩ := hne
  have h1 := dA_le (S := S) (N := N) ha (w := w)
  rw [dU_mk (hA ha) hw] at h1
  exact lt_of_le_of_lt h1 (dist_lt_card' _ _)

lemma parA_spec {w p : U} (h : parA S N A w = some p) :
    w ∈ S ∧ w ∉ A ∧ (ktInst S N).G.Adj p w ∧ dA S N A p + 1 = dA S N A w := by
  classical
  unfold parA at h
  split_ifs at h with hw
  have := argminIdx_mem h
  simp only [mem_filter, mem_univ, true_and] at this
  exact ⟨hw.1, hw.2, this⟩

lemma parA_eq_none (hA : A ⊆ S) (hne : A.Nonempty) {w : U} (hw : w ∈ S) :
    parA S N A w = none ↔ w ∈ A := by
  classical
  unfold parA
  by_cases hwA : w ∈ A
  · rw [ite_eq_right (fun h => h.2 hwA)]; simp [hwA]
  · rw [ite_eq_left ⟨hw, hwA⟩, argminIdx_eq_none]
    simp only [hwA, iff_false]
    obtain ⟨v, hv⟩ := dA_closer (N := N) hA hne hw hwA
    exact Finset.ne_empty_of_mem (a := v) (by simpa using hv)

lemma parA_eq (hw : w ∈ S) (hwA : w ∉ A) : parA S N A w = argminIdx (univ.filter
    (fun v => (ktInst S N).G.Adj v w ∧ dA S N A v + 1 = dA S N A w)) := by
  classical
  unfold parA
  rw [ite_eq_left ⟨hw, hwA⟩]

end Dist

/-! ## Binary search for the least index -/

section Search

variable (S : Finset U)

/-- the least index of a node of `S` -/
noncomputable def mstar : ℕ := if h : S.Nonempty then S.inf' h idx else 0

/-- the number of windows of the binary search: `2 ^ nB U > |U|` -/
def nB (U : Type) [Fintype U] : ℕ := lg (Fintype.card U)

/-- the lower end of the search interval after `b` windows -/
noncomputable def gLo : ℕ → ℕ
  | 0 => 0
  | b + 1 => if mstar S < gLo b + 2 ^ (nB U - b - 1) then gLo b else gLo b + 2 ^ (nB U - b - 1)

/-- the sources of window `b`: the nodes with index in the lower half of the search interval -/
noncomputable def srcB (b : ℕ) : Finset U :=
  S.filter (fun w => idx w < gLo S b + 2 ^ (nB U - b - 1))

variable {S}

lemma mstar_le {u : U} (hu : u ∈ S) : mstar S ≤ idx u := by
  unfold mstar; rw [dite_eq_left ⟨u, hu⟩]; exact inf'_le _ hu

lemma exists_mstar (hS : S.Nonempty) : ∃ u ∈ S, idx u = mstar S := by
  unfold mstar; rw [dite_eq_left hS]
  obtain ⟨u, hu, h⟩ := exists_mem_eq_inf' hS idx
  exact ⟨u, hu, h.symm⟩

lemma lt_pow_nB (u : U) : idx u < 2 ^ nB U := by
  have h1 := idx_lt u
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Fintype.card U)
  unfold nB lg
  omega

lemma gLo_inv (hS : S.Nonempty) : ∀ b ≤ nB U, gLo S b ≤ mstar S ∧ mstar S < gLo S b + 2 ^ (nB U - b) := by
  intro b
  induction b with
  | zero =>
    intro _
    obtain ⟨u, hu, h⟩ := exists_mstar hS
    have := lt_pow_nB u
    simp only [gLo, Nat.sub_zero]
    omega
  | succ b ih =>
    intro hb
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hp : 2 ^ (nB U - b) = 2 * 2 ^ (nB U - b - 1) := by
      rw [← pow_succ']; congr 1; omega
    have he : nB U - (b + 1) = nB U - b - 1 := by omega
    simp only [gLo, he]
    split_ifs with h
    · omega
    · omega

lemma gLo_last (hS : S.Nonempty) : gLo S (nB U) = mstar S := by
  have := gLo_inv hS (nB U) le_rfl
  simp only [Nat.sub_self, pow_zero] at this
  omega

lemma srcB_sub (b : ℕ) : srcB S b ⊆ S := filter_subset _ _

lemma mem_srcB {b : ℕ} {w : U} : w ∈ srcB S b ↔ w ∈ S ∧ idx w < gLo S b + 2 ^ (nB U - b - 1) := by
  unfold srcB; rw [mem_filter]

lemma srcB_nonempty_iff (hS : S.Nonempty) (b : ℕ) :
    (srcB S b).Nonempty ↔ mstar S < gLo S b + 2 ^ (nB U - b - 1) := by
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_srcB] at hw
    have := mstar_le hw.1
    omega
  · intro h
    obtain ⟨u, hu, hm⟩ := exists_mstar hS
    exact ⟨u, mem_srcB.2 ⟨hu, by omega⟩⟩

/-- the leader: the node of least index -/
lemma srcB_last (hS : S.Nonempty) : ∃ ℓ ∈ S, srcB S (nB U) = {ℓ} := by
  obtain ⟨ℓ, hℓ, hm⟩ := exists_mstar hS
  refine ⟨ℓ, hℓ, ?_⟩
  ext w
  rw [mem_srcB, mem_singleton, gLo_last hS, Nat.sub_self, Nat.zero_sub, pow_zero]
  constructor
  · rintro ⟨hw, h⟩
    have := mstar_le hw
    exact idx_inj (by omega)
  · rintro rfl; exact ⟨hℓ, by omega⟩

lemma srcB_last_nonempty (hS : S.Nonempty) : (srcB S (nB U)).Nonempty := by
  obtain ⟨ℓ, -, h⟩ := srcB_last hS
  rw [h]; exact singleton_nonempty ℓ

end Search

/-! ## The BFS tree from the leader -/

section Tree

variable (S : Finset U) (N : WNet S)

/-- the parent in the BFS tree from the leader (the flood of window `nB U`) -/
noncomputable def kpar (w : U) : Option U := parA S N (srcB S (nB U)) w

/-- the depth in the BFS tree -/
noncomputable def kdep (w : U) : ℕ := dA S N (srcB S (nB U)) w

/-- the size of the subtree of `u` -/
noncomputable def ksz (u : U) : ℕ := (desc S (kpar S N) u).card

/-- the preorder number of `u` (the children of a node in increasing index order) -/
noncomputable def kpre (u : U) : ℕ :=
  match kpar S N u with
  | none => 0
  | some p => if h : kdep S N p < kdep S N u then
      kpre p + 1 + ∑ c ∈ (kidsOf S (kpar S N) p).filter (fun c => idx c < idx u), ksz S N c
    else 0
termination_by kdep S N u

variable {S N} (hS : S.Nonempty)

lemma kpar_spec {w p : U} (h : kpar S N w = some p) :
    w ∈ S ∧ p ∈ S ∧ (ktInst S N).G.Adj p w ∧ kdep S N p + 1 = kdep S N w := by
  obtain ⟨hw, -, hadj, hd⟩ := parA_spec h
  exact ⟨hw, ktInst_mem_left hadj, hadj, hd⟩

lemma kpar_mem : ∀ v ∈ S, ∀ u, kpar S N v = some u → u ∈ S :=
  fun _ _ _ h => (kpar_spec h).2.1

lemma kpar_rk : ∀ v ∈ S, ∀ u, kpar S N v = some u → kdep S N u < kdep S N v := fun _ _ _ h => by
  have := (kpar_spec h).2.2.2; omega

lemma kpar_adj {v u : U} (h : kpar S N v = some u) : (ktInst S N).G.Adj v u :=
  (kpar_spec h).2.2.1.symm

include hS

lemma kpar_none {w : U} (hw : w ∈ S) : kpar S N w = none ↔ w ∈ srcB S (nB U) :=
  parA_eq_none (srcB_sub _) (srcB_last_nonempty hS) hw

lemma kdep_lt {w : U} (hw : w ∈ S) : kdep S N w < S.card :=
  dA_lt (srcB_last_nonempty hS) (srcB_sub _) hw

lemma desc_root {ℓ : U} (hℓ : srcB S (nB U) = {ℓ}) : desc S (kpar S N) ℓ = S := by
  ext w
  rw [mem_desc]
  refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
  obtain ⟨t, ht, htn⟩ := exists_top kpar_mem kpar_rk w hw
  have htS := anc_mem kpar_mem hw ht
  have := (kpar_none hS htS).1 htn
  rw [hℓ, mem_singleton] at this
  rw [← this]; exact ht

lemma ksz_eq {u : U} (hu : u ∈ S) : ksz S N u = 1 + ∑ c ∈ kidsOf S (kpar S N) u, ksz S N c := by
  have hnot : u ∉ (kidsOf S (kpar S N) u).biUnion (desc S (kpar S N)) := fun h => by
    obtain ⟨c, hc, hu'⟩ := mem_biUnion.1 h
    exact not_mem_desc_kid kpar_mem kpar_rk hc hu'
  unfold ksz
  rw [desc_eq kpar_mem kpar_rk hu, card_insert_of_notMem hnot,
    card_biUnion (desc_disj kpar_mem kpar_rk u)]
  ring

omit hS in
lemma kpre_none {u : U} (h : kpar S N u = none) : kpre S N u = 0 := by
  rw [kpre]; split <;> simp_all

omit hS in
lemma kpre_some {u p : U} (h : kpar S N u = some p) : kpre S N u =
    kpre S N p + 1 + ∑ c ∈ (kidsOf S (kpar S N) p).filter (fun c => idx c < idx u), ksz S N c := by
  have hlt := kpar_rk u (kpar_spec h).1 p h
  rw [kpre]
  split
  · simp_all
  · rename_i p' hp'
    rw [h] at hp'; cases hp'
    exact dite_eq_left hlt

omit hS in
lemma sum_lt_add_le {K : Finset U} {f : U → ℕ} {c : U} (hc : c ∈ K) (a : ℕ) (ha : idx c < a) :
    ∑ c' ∈ K.filter (fun c' => idx c' < idx c), f c' + f c ≤
      ∑ c' ∈ K.filter (fun c' => idx c' < a), f c' := by
  have hnot : c ∉ K.filter (fun c' => idx c' < idx c) := by simp
  rw [add_comm, ← sum_insert hnot]
  refine sum_le_sum_of_subset (fun x hx => ?_)
  rw [mem_insert, mem_filter] at hx
  rw [mem_filter]
  rcases hx with rfl | ⟨h1, h2⟩
  · exact ⟨hc, ha⟩
  · exact ⟨h1, by omega⟩

omit hS in
lemma sum_lt_add_le_all {K : Finset U} {f : U → ℕ} {c : U} (hc : c ∈ K) :
    ∑ c' ∈ K.filter (fun c' => idx c' < idx c), f c' + f c ≤ ∑ c' ∈ K, f c' := by
  have hnot : c ∉ K.filter (fun c' => idx c' < idx c) := by simp
  rw [add_comm, ← sum_insert hnot]
  refine sum_le_sum_of_subset (fun x hx => ?_)
  rw [mem_insert, mem_filter] at hx
  rcases hx with rfl | ⟨h1, _⟩
  · exact hc
  · exact h1

omit hS in
/-- **Preorder numbers**: the subtree of `u` gets the numbers in `[kpre u, kpre u + ksz u)`,
injectively. -/
lemma kpre_main (u : U) : u ∈ S →
    (∀ w ∈ desc S (kpar S N) u, kpre S N u ≤ kpre S N w ∧ kpre S N w < kpre S N u + ksz S N u) ∧
      Set.InjOn (kpre S N) ↑(desc S (kpar S N) u) := by
  induction u using kid_induction (S := S) (par := kpar S N) (rk := kdep S N) kpar_rk with
  | _ u ih =>
    intro hu
    have hsz : ksz S N u = 1 + ∑ c ∈ kidsOf S (kpar S N) u, ksz S N c := by
      have hnot : u ∉ (kidsOf S (kpar S N) u).biUnion (desc S (kpar S N)) := fun h => by
        obtain ⟨c, hc, hu'⟩ := mem_biUnion.1 h
        exact not_mem_desc_kid kpar_mem kpar_rk hc hu'
      unfold ksz
      rw [desc_eq kpar_mem kpar_rk hu, card_insert_of_notMem hnot,
        card_biUnion (desc_disj kpar_mem kpar_rk u)]
      ring
    have hkid : ∀ c ∈ kidsOf S (kpar S N) u, kpre S N c = kpre S N u + 1 +
        ∑ c' ∈ (kidsOf S (kpar S N) u).filter (fun c' => idx c' < idx c), ksz S N c' :=
      fun c hc => kpre_some (mem_kidsOf.1 hc).2
    have hcS : ∀ c ∈ kidsOf S (kpar S N) u, c ∈ S := fun c hc => (mem_kidsOf.1 hc).1
    -- the range of a child's subtree
    have hrange : ∀ c ∈ kidsOf S (kpar S N) u, ∀ w ∈ desc S (kpar S N) c,
        kpre S N u < kpre S N w ∧ kpre S N w < kpre S N u + ksz S N u := by
      intro c hc w hw
      obtain ⟨h1, h2⟩ := (ih c hc (hcS c hc)).1 w hw
      have h3 := sum_lt_add_le_all (f := ksz S N) hc
      rw [hkid c hc] at h1 h2
      constructor <;> omega
    -- ordered children have ordered ranges
    have hord : ∀ c ∈ kidsOf S (kpar S N) u, ∀ c' ∈ kidsOf S (kpar S N) u, idx c < idx c' →
        ∀ w ∈ desc S (kpar S N) c, ∀ w' ∈ desc S (kpar S N) c', kpre S N w < kpre S N w' := by
      intro c hc c' hc' hlt w hw w' hw'
      have h1 := ((ih c hc (hcS c hc)).1 w hw).2
      have h2 := ((ih c' hc' (hcS c' hc')).1 w' hw').1
      have h3 := sum_lt_add_le (f := ksz S N) hc (idx c') hlt
      rw [hkid c hc] at h1
      rw [hkid c' hc'] at h2
      omega
    have hdesc := desc_eq (kpar_mem (N := N)) kpar_rk hu
    refine ⟨fun w hw => ?_, fun w hw w' hw' heq => ?_⟩
    · rw [hdesc, mem_insert, mem_biUnion] at hw
      rcases hw with rfl | ⟨c, hc, hw⟩
      · constructor <;> omega
      · have := hrange c hc w hw
        constructor <;> omega
    · rw [mem_coe, hdesc, mem_insert, mem_biUnion] at hw hw'
      rcases hw with rfl | ⟨c, hc, hw⟩ <;> rcases hw' with rfl | ⟨c', hc', hw'⟩
      · rfl
      · have := hrange c' hc' w' hw'; omega
      · have := hrange c hc w hw; omega
      · by_cases hcc : c = c'
        · subst hcc
          exact (ih c hc (hcS c hc)).2 (mem_coe.2 hw) (mem_coe.2 hw') heq
        · have hne : idx c ≠ idx c' := fun h => hcc (idx_inj h)
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · have := hord c hc c' hc' hlt w hw w' hw'; omega
          · have := hord c' hc' c hc hlt w' hw' w hw; omega

lemma kpre_lt {ℓ : U} (hℓ : srcB S (nB U) = {ℓ}) {w : U} (hw : w ∈ S) : kpre S N w < S.card := by
  have hℓS : ℓ ∈ S := srcB_sub _ (by rw [hℓ]; exact mem_singleton_self ℓ)
  have hroot : kpar S N ℓ = none := (kpar_none hS hℓS).2 (by rw [hℓ]; exact mem_singleton_self ℓ)
  have h := ((kpre_main (N := N) ℓ hℓS).1 w (by rw [desc_root hS hℓ]; exact hw)).2
  rw [kpre_none hroot] at h
  unfold ksz at h
  rw [desc_root hS hℓ] at h
  omega

lemma kpre_inj {ℓ : U} (hℓ : srcB S (nB U) = {ℓ}) : Set.InjOn (kpre S N) ↑S := by
  have hℓS : ℓ ∈ S := srcB_sub _ (by rw [hℓ]; exact mem_singleton_self ℓ)
  have h := (kpre_main (N := N) ℓ hℓS).2
  rwa [desc_root hS hℓ] at h

end Tree

end KT

end APSP.Stoc.Congest
