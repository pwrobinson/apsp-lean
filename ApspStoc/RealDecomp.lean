import ApspStoc.Defs

/-!
# Existence of expander decompositions

The classical sparse-cut recursion: repeatedly split along a cut of conductance `< 1/φinv`.
With the potential `Φ(W) = W * ⌈log₂ W⌉` (on twice the number of edges) one shows that at most
`2|F| ⌈log₂ (2|F|)⌉ / φinv` edges are left uncovered by the expander clusters.
-/

namespace APSP.Stoc

open APSP Finset

section RealDecomp

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The edges of `F` with both endpoints in `X`. -/
noncomputable def insE (F : Finset (Sym2 V)) (X : Finset V) : Finset (Sym2 V) := by
  classical exact F.filter (fun e => ∀ v ∈ e, v ∈ X)

lemma mem_insE {F : Finset (Sym2 V)} {X : Finset V} {e : Sym2 V} :
    e ∈ insE F X ↔ e ∈ F ∧ ∀ v ∈ e, v ∈ X := by
  unfold insE; exact mem_filter

lemma mem_cutEdges_iff {C : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} :
    e ∈ cutEdges C S ↔ e ∈ C ∧ (∃ u ∈ e, u ∈ S) ∧ (∃ u ∈ e, u ∉ S) := by
  unfold cutEdges; exact mem_filter

lemma insE_univ (F : Finset (Sym2 V)) : insE F univ = F := by
  ext e; simp [mem_insE]

lemma insE_mono (F : Finset (Sym2 V)) {X Y : Finset V} (h : X ⊆ Y) : insE F X ⊆ insE F Y := by
  intro e he
  rw [mem_insE] at he ⊢
  exact ⟨he.1, fun v hv => h (he.2 v hv)⟩

lemma insE_subset (F : Finset (Sym2 V)) (X : Finset V) : insE F X ⊆ F :=
  fun _ he => (mem_insE.1 he).1

omit [Fintype V] [DecidableEq V] in
lemma noLoops_of_subset {C D : Finset (Sym2 V)} (h : D ⊆ C) (hC : NoLoops C) : NoLoops D :=
  fun e he => hC e (h he)

lemma nodes_insE_subset (F : Finset (Sym2 V)) (X : Finset V) : nodes (insE F X) ⊆ X := by
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_nodes.1 hv
  exact (mem_insE.1 he).2 v hve

lemma vol_add_vol_compl {C : Finset (Sym2 V)} (hC : NoLoops C) {S : Finset V}
    (hS : S ⊆ nodes C) : vol C S + vol C (nodes C \ S) = 2 * C.card := by
  unfold vol
  rw [← sum_degIn hC, add_comm]
  exact sum_sdiff hS

lemma two_mul_card_le_vol {C D : Finset (Sym2 V)} (hDC : D ⊆ C) (hD : NoLoops D)
    {T : Finset V} (hT : ∀ e ∈ D, ∀ v ∈ e, v ∈ T) : 2 * D.card ≤ vol C T := by
  rw [← sum_degIn hD]
  unfold vol
  calc ∑ v ∈ nodes D, degIn D v ≤ ∑ v ∈ T, degIn D v := by
        apply sum_le_sum_of_subset
        intro v hv
        obtain ⟨e, he, hve⟩ := mem_nodes.1 hv
        exact hT e he v hve
    _ ≤ ∑ v ∈ T, degIn C v := by
        apply sum_le_sum
        intro v _
        unfold degIn
        exact card_le_card (filter_subset_filter _ hDC)

/-! ## The potential `Φ(W) = W * ⌈log₂ W⌉` -/

lemma clog_succ_le_of_two_mul_le {a W : ℕ} (ha : 1 ≤ a) (h : 2 * a ≤ W) :
    Nat.clog 2 a + 1 ≤ Nat.clog 2 W := by
  have h1 : 2 ^ Nat.clog 2 a < 2 * a := by
    rcases Nat.eq_zero_or_pos (Nat.clog 2 a) with h0 | h0
    · rw [h0]; omega
    · have h2 : 2 ^ (Nat.clog 2 a - 1) < a :=
        (Nat.lt_clog_iff_pow_lt (by norm_num)).1 (by omega)
      have e : 2 ^ Nat.clog 2 a = 2 * 2 ^ (Nat.clog 2 a - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
  have : Nat.clog 2 a < Nat.clog 2 W := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by omega)
  omega

lemma pot_mono {W W' : ℕ} (h : W ≤ W') : W * Nat.clog 2 W ≤ W' * Nat.clog 2 W' :=
  Nat.mul_le_mul h (Nat.clog_mono_right 2 h)

lemma pot_split (a b : ℕ) :
    a * Nat.clog 2 a + b * Nat.clog 2 b + min a b ≤ (a + b) * Nat.clog 2 (a + b) := by
  wlog hab : a ≤ b generalizing a b
  · have := this b a (by omega)
    rw [min_comm, add_comm a b]
    omega
  rcases Nat.eq_zero_or_pos a with h0 | ha
  · subst h0; simp
  · rw [min_eq_left hab]
    have h1 := clog_succ_le_of_two_mul_le ha (show 2 * a ≤ a + b by omega)
    have h2 : Nat.clog 2 b ≤ Nat.clog 2 (a + b) := Nat.clog_mono_right 2 (by omega)
    have h3 : a * (Nat.clog 2 a + 1) ≤ a * Nat.clog 2 (a + b) := Nat.mul_le_mul_left a h1
    have h4 : b * Nat.clog 2 b ≤ b * Nat.clog 2 (a + b) := Nat.mul_le_mul_left b h2
    rw [mul_add, mul_one] at h3
    rw [add_mul]
    omega

/-! ## The recursion -/

theorem expDecomp_aux (F : Finset (Sym2 V)) (hF : NoLoops F) (φinv : ℕ) (X : Finset V) :
    ∃ P : Finset (Finset (Sym2 V)),
      (∀ C ∈ P, C ⊆ insE F X ∧ C.Nonempty ∧ IsExpander C φinv ∧ nodes C ⊆ X) ∧
      (∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint (nodes C) (nodes C')) ∧
      φinv * (insE F X \ P.biUnion id).card ≤
        2 * (insE F X).card * Nat.clog 2 (2 * (insE F X).card) := by
  obtain ⟨n, hn⟩ : ∃ n, X.card = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  by_cases hC0 : insE F X = ∅
  · refine ⟨∅, by simp, by simp, ?_⟩
    rw [hC0]; simp
  by_cases hexp : IsExpander (insE F X) φinv
  · refine ⟨{insE F X}, ?_, ?_, ?_⟩
    · intro D hD
      rw [mem_singleton] at hD
      subst hD
      exact ⟨subset_refl _, nonempty_iff_ne_empty.2 hC0, hexp, nodes_insE_subset F X⟩
    · intro D hD D' hD' hne
      rw [mem_singleton] at hD hD'
      exact absurd (hD.trans hD'.symm) hne
    · simp
  -- a sparse cut exists
  unfold IsExpander at hexp
  push Not at hexp
  obtain ⟨S, hSn, hcut⟩ := hexp
  have hCnl : NoLoops (insE F X) := noLoops_of_subset (insE_subset F X) hF
  have hnX : nodes (insE F X) ⊆ X := nodes_insE_subset F X
  have hSX : S ⊆ X := hSn.trans hnX
  have hab := vol_add_vol_compl hCnl hSn
  have hmin1 := min_le_left (vol (insE F X) S) (vol (insE F X) (nodes (insE F X) \ S))
  have hmin2 := min_le_right (vol (insE F X) S) (vol (insE F X) (nodes (insE F X) \ S))
  have ha : 1 ≤ vol (insE F X) S := by omega
  have hb : 1 ≤ vol (insE F X) (nodes (insE F X) \ S) := by omega
  have hSne : S.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    simp [vol] at ha
  have hTne : (nodes (insE F X) \ S).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    rw [h] at hb
    simp [vol] at hb
  have hlt1 : S.card < n := by
    rw [← hn]
    apply card_lt_card
    rw [ssubset_iff_of_subset hSX]
    obtain ⟨v, hv⟩ := hTne
    rw [mem_sdiff] at hv
    exact ⟨v, hnX hv.1, hv.2⟩
  have hlt2 : (X \ S).card < n := by
    rw [← hn]
    exact card_lt_card (sdiff_ssubset hSX hSne)
  obtain ⟨P₁, h1a, h1b, h1c⟩ := ih S.card hlt1 S rfl
  obtain ⟨P₂, h2a, h2b, h2c⟩ := ih (X \ S).card hlt2 (X \ S) rfl
  refine ⟨P₁ ∪ P₂, ?_, ?_, ?_⟩
  · intro D hD
    rcases mem_union.1 hD with hD | hD
    · obtain ⟨h1, h2, h3, h4⟩ := h1a D hD
      exact ⟨h1.trans (insE_mono F hSX), h2, h3, h4.trans hSX⟩
    · obtain ⟨h1, h2, h3, h4⟩ := h2a D hD
      exact ⟨h1.trans (insE_mono F sdiff_subset), h2, h3, h4.trans sdiff_subset⟩
  · intro D hD D' hD' hne
    rcases mem_union.1 hD with hD | hD <;> rcases mem_union.1 hD' with hD' | hD'
    · exact h1b D hD D' hD' hne
    · exact disjoint_of_subset_left (h1a D hD).2.2.2
        (disjoint_of_subset_right (h2a D' hD').2.2.2 disjoint_sdiff)
    · exact disjoint_of_subset_left (h2a D hD).2.2.2
        (disjoint_of_subset_right (h1a D' hD').2.2.2 sdiff_disjoint)
    · exact h2b D hD D' hD' hne
  · -- edge accounting
    have hcover : insE F X \ (P₁ ∪ P₂).biUnion id ⊆
        ((insE F S \ P₁.biUnion id) ∪ (insE F (X \ S) \ P₂.biUnion id)) ∪
          cutEdges (insE F X) S := by
      intro e he
      rw [mem_sdiff, union_biUnion, mem_union, not_or] at he
      obtain ⟨heC, hn1, hn2⟩ := he
      have heC' := mem_insE.1 heC
      by_cases hall : ∀ v ∈ e, v ∈ S
      · exact mem_union_left _ (mem_union_left _ (mem_sdiff.2 ⟨mem_insE.2 ⟨heC'.1, hall⟩, hn1⟩))
      · by_cases hnone : ∀ v ∈ e, v ∉ S
        · refine mem_union_left _ (mem_union_right _ (mem_sdiff.2 ⟨mem_insE.2 ⟨heC'.1, ?_⟩, hn2⟩))
          exact fun v hv => mem_sdiff.2 ⟨heC'.2 v hv, hnone v hv⟩
        · push Not at hall hnone
          exact mem_union_right _ (mem_cutEdges_iff.2 ⟨heC, hnone, hall⟩)
    have hc1 := card_le_card hcover
    have hc2 := card_union_le ((insE F S \ P₁.biUnion id) ∪ (insE F (X \ S) \ P₂.biUnion id))
      (cutEdges (insE F X) S)
    have hc3 := card_union_le (insE F S \ P₁.biUnion id) (insE F (X \ S) \ P₂.biUnion id)
    have hmul : φinv * (insE F X \ (P₁ ∪ P₂).biUnion id).card ≤
        φinv * (insE F S \ P₁.biUnion id).card + φinv * (insE F (X \ S) \ P₂.biUnion id).card +
          φinv * (cutEdges (insE F X) S).card := by
      rw [← mul_add, ← mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    -- volumes of the two sides
    have hv1 : 2 * (insE F S).card ≤ vol (insE F X) S :=
      two_mul_card_le_vol (insE_mono F hSX) (noLoops_of_subset (insE_subset F S) hF)
        (fun e he v hv => (mem_insE.1 he).2 v hv)
    have hv2 : 2 * (insE F (X \ S)).card ≤ vol (insE F X) (nodes (insE F X) \ S) := by
      refine two_mul_card_le_vol (insE_mono F sdiff_subset)
        (noLoops_of_subset (insE_subset F _) hF) ?_
      intro e he v hv
      refine mem_sdiff.2 ⟨mem_nodes.2 ⟨e, insE_mono F sdiff_subset he, hv⟩, ?_⟩
      exact (mem_sdiff.1 ((mem_insE.1 he).2 v hv)).2
    have hp1 := pot_mono hv1
    have hp2 := pot_mono hv2
    have hps := pot_split (vol (insE F X) S) (vol (insE F X) (nodes (insE F X) \ S))
    rw [← hab]
    omega

/-! ## Main statements -/

theorem expDecomp_exists {V : Type} [Fintype V] [DecidableEq V] (F : Finset (Sym2 V))
    (hF : NoLoops F) (φinv : ℕ) :
    ∃ P : Finset (Finset (Sym2 V)),
      (∀ C ∈ P, C ⊆ F ∧ C.Nonempty ∧ IsExpander C φinv) ∧
      (∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint (nodes C) (nodes C')) ∧
      φinv * (F \ P.biUnion id).card ≤ 2 * F.card * Nat.clog 2 (2 * F.card) := by
  obtain ⟨P, h1, h2, h3⟩ := expDecomp_aux F hF φinv univ
  rw [insE_univ] at h1 h3
  exact ⟨P, fun C hC => ⟨(h1 C hC).1, (h1 C hC).2.1, (h1 C hC).2.2.1⟩, h2, h3⟩

lemma clog_two_mul_le_three_lg {m ν : ℕ} (hm : m ≤ ν ^ 2) :
    Nat.clog 2 (2 * m) ≤ 3 * lg ν := by
  apply Nat.clog_le_of_le_pow
  have h1 : ν < 2 ^ (Nat.log 2 ν + 1) := Nat.lt_pow_succ_log_self (by norm_num) ν
  have h2 : ν ^ 2 ≤ 2 ^ (2 * (Nat.log 2 ν + 1)) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left h1.le 2
  have h3 : 2 ^ (2 * (Nat.log 2 ν + 1) + 1) ≤ 2 ^ (3 * lg ν) :=
    Nat.pow_le_pow_right (by norm_num) (by unfold lg; omega)
  rw [pow_succ] at h3
  omega

theorem expDecomp_exists_lg {V : Type} [Fintype V] [DecidableEq V] (F : Finset (Sym2 V))
    (hF : NoLoops F) (φinv ν : ℕ) (hν : F.card ≤ ν ^ 2) :
    ∃ P : Finset (Finset (Sym2 V)),
      (∀ C ∈ P, C ⊆ F ∧ C.Nonempty ∧ IsExpander C φinv) ∧
      (∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint (nodes C) (nodes C')) ∧
      φinv * (F \ P.biUnion id).card ≤ 6 * lg ν * F.card := by
  obtain ⟨P, h1, h2, h3⟩ := expDecomp_exists F hF φinv
  refine ⟨P, h1, h2, h3.trans ?_⟩
  have h := Nat.mul_le_mul_left (2 * F.card) (clog_two_mul_le_three_lg hν)
  calc 2 * F.card * Nat.clog 2 (2 * F.card) ≤ 2 * F.card * (3 * lg ν) := h
    _ = 6 * lg ν * F.card := by ring

end RealDecomp

end APSP.Stoc
