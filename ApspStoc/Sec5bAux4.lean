import ApspStoc.Sec5bAux3

/-!
# Theorem 5.5, auxiliary file 4: cost accounting of the recursion

The cost bound `costB` of a subproblem is `Q` times its weighted participation count; one call
costs `Õ(|S|)` itself (approximate SSSP, two MSTs and component traversals, two aggregator
exchanges), and its subproblems are disjoint subsets of `S` with the windows of the next level.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V] {N : WNet V} {E : Overlays V} {j : ℕ} {s : V}

lemma sum_costB_le {Q k a : ℕ} {T' S : Finset V} (h : T' ⊆ S) :
    ∑ K ∈ comps N.G T', costB N E j s Q k K a ≤ costB N E j s Q k S a := by
  unfold costB
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
  · rw [Prof.rounds_sum]; simp only [Prof.rounds_mk]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_comps]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sum_le_sum_of_subset h))
  · rw [Prof.load_sum]; simp only [Prof.load_mk]
    rw [← Finset.mul_sum, sum_comps N.G T' (fun v => Nw (N.wdist s v) k a * hg N.G E j v e)]
    exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset h)
  · rw [Prof.msgs_sum]; simp only [Prof.msgs_mk]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_comps]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sum_le_sum_of_subset h))

lemma sum_δB_le {η : ℝ} (hη : 0 ≤ η) {k a : ℕ} {T' S : Finset V} (h : T' ⊆ S) :
    ∑ K ∈ comps N.G T', δB N s η k K a ≤ δB N s η k S a := by
  unfold δB
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_comps]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast sum_le_sum_of_subset h

lemma card_le_sum_Nw {k a : ℕ} {S : Finset V} (h1 : ∀ v ∈ S, 1 ≤ Nw (N.wdist s v) k a) :
    S.card ≤ ∑ v ∈ S, Nw (N.wdist s v) k a := by
  rw [card_eq_sum_ones]; exact sum_le_sum h1

lemma own_le {Q q k a : ℕ} {S : Finset V} (hne : S.Nonempty)
    (h1 : ∀ v ∈ S, 1 ≤ Nw (N.wdist s v) k a) (hq : q ≤ Q) :
    subsetProf N.G E j S q ≤ costB N E j s Q k S a := by
  have hc := card_le_sum_Nw (N := N) (s := s) h1
  have hpos : 1 ≤ S.card := card_pos.2 hne
  have hr : q * (S.card + 1) ≤ Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) k a) :=
    Nat.mul_le_mul hq (by omega)
  unfold subsetProf costB
  refine Prof.le_mk _ _ _ _ hr (fun e => ?_) hr
  simp only [Prof.load_mk]
  refine Nat.mul_le_mul hq ((rho_le_sum_hg N.G E j S e).trans (sum_le_sum (fun v hv => ?_)))
  exact Nat.le_mul_of_pos_left _ (h1 v hv)

lemma ownδ_le {η : ℝ} (hη : 0 ≤ η) {k a : ℕ} {S : Finset V} (hne : S.Nonempty)
    (h1 : ∀ v ∈ S, 1 ≤ Nw (N.wdist s v) k a) : 7 * η ≤ δB N s η k S a := by
  unfold δB
  have hc := card_le_sum_Nw (N := N) (s := s) h1
  have hpos : 1 ≤ S.card := card_pos.2 hne
  have : (1 : ℝ) ≤ ((∑ v ∈ S, Nw (N.wdist s v) k a : ℕ) : ℝ) := by exact_mod_cast hpos.trans hc
  nlinarith

lemma step_cost {Q q k a : ℕ} {S : Finset V} (hne : S.Nonempty)
    (hNw : ∀ v ∈ S, 1 + Nw (N.wdist s v) k a + Nw (N.wdist s v) k (a + 2 ^ k) ≤
      Nw (N.wdist s v) (k + 1) a) (hq : q ≤ Q) :
    subsetProf N.G E j S q + (costB N E j s Q k S a + costB N E j s Q k S (a + 2 ^ k)) ≤
      costB N E j s Q (k + 1) S a := by
  have hsum : S.card + ∑ v ∈ S, Nw (N.wdist s v) k a + ∑ v ∈ S, Nw (N.wdist s v) k (a + 2 ^ k)
      ≤ ∑ v ∈ S, Nw (N.wdist s v) (k + 1) a := by
    rw [card_eq_sum_ones, ← sum_add_distrib, ← sum_add_distrib]; exact sum_le_sum hNw
  have hpos : 1 ≤ S.card := card_pos.2 hne
  have hr : q * (S.card + 1) + (Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) k a) +
      Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) k (a + 2 ^ k))) ≤
      Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) (k + 1) a) := by
    have h1 : q * (S.card + 1) ≤ Q * (2 * S.card) := Nat.mul_le_mul hq (by omega)
    have h2 : Q * (2 * S.card) + (Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) k a) +
        Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) k (a + 2 ^ k))) =
        Q * (2 * (S.card + ∑ v ∈ S, Nw (N.wdist s v) k a +
          ∑ v ∈ S, Nw (N.wdist s v) k (a + 2 ^ k))) := by ring
    have h3 := Nat.mul_le_mul_left Q (Nat.mul_le_mul_left 2 hsum)
    omega
  unfold subsetProf costB
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
  · simpa only [Prof.rounds_add, Prof.rounds_mk] using hr
  · simp only [Prof.load_add, Prof.load_mk, Pi.add_apply]
    have h1 : q * E.rho N.G j S e ≤ Q * ∑ v ∈ S, hg N.G E j v e :=
      Nat.mul_le_mul hq (rho_le_sum_hg N.G E j S e)
    have h2 : ∑ v ∈ S, hg N.G E j v e + ∑ v ∈ S, Nw (N.wdist s v) k a * hg N.G E j v e +
        ∑ v ∈ S, Nw (N.wdist s v) k (a + 2 ^ k) * hg N.G E j v e ≤
        ∑ v ∈ S, Nw (N.wdist s v) (k + 1) a * hg N.G E j v e := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      refine sum_le_sum (fun v hv => ?_)
      have := Nat.mul_le_mul_right (hg N.G E j v e) (hNw v hv)
      nlinarith
    have h3 := Nat.mul_le_mul_left Q h2
    rw [mul_add, mul_add] at h3
    omega
  · simpa only [Prof.msgs_add, Prof.msgs_mk] using hr

lemma step_δ {η : ℝ} (hη : 0 ≤ η) {k a : ℕ} {S : Finset V} (hne : S.Nonempty)
    (hNw : ∀ v ∈ S, 1 + Nw (N.wdist s v) k a + Nw (N.wdist s v) k (a + 2 ^ k) ≤
      Nw (N.wdist s v) (k + 1) a) :
    7 * η + (δB N s η k S a + δB N s η k S (a + 2 ^ k)) ≤ δB N s η (k + 1) S a := by
  have hsum : S.card + ∑ v ∈ S, Nw (N.wdist s v) k a + ∑ v ∈ S, Nw (N.wdist s v) k (a + 2 ^ k)
      ≤ ∑ v ∈ S, Nw (N.wdist s v) (k + 1) a := by
    rw [card_eq_sum_ones, ← sum_add_distrib, ← sum_add_distrib]; exact sum_le_sum hNw
  have hpos : 1 ≤ S.card := card_pos.2 hne
  unfold δB
  have hsum' : (S.card : ℝ) + ((∑ v ∈ S, Nw (N.wdist s v) k a : ℕ) : ℝ) +
      ((∑ v ∈ S, Nw (N.wdist s v) k (a + 2 ^ k) : ℕ) : ℝ) ≤
      ((∑ v ∈ S, Nw (N.wdist s v) (k + 1) a : ℕ) : ℝ) := by exact_mod_cast hsum
  have hpos' : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
  nlinarith

end APSP.Stoc
