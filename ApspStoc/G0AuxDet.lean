import ApspStoc.G0AuxWalk

/-!
# The deterministic part of Claims 3.4/3.5

If the walks behave as expected (every port starts and receives at most `hi` surviving walks,
every set `A` with `|A| ≤ |P|/2` sends at least `|A| L` surviving walks out of `A`, and in every
step at most `hc` surviving walks cross each edge), then the constructed multigraph has the
claimed parameters.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable instance rwSurv.instDecidable (C : Finset (Sym2 V)) (P : Finset (Port V)) (p : Port V) {ℓ : ℕ}
    (σ : Fin (2 * ℓ) → Fin (seedRange C)) : Decidable (rwSurv C P p σ) := by
  unfold rwSurv; infer_instance

lemma count_filterMap_snd (s : List (V × Option (Sym2 V))) (e : Sym2 V) :
    (s.filterMap Prod.snd).count e =
      ∑ j ∈ range s.length, if ∃ y, s[j]? = some (y, some e) then 1 else 0 := by
  induction s with
  | nil => simp
  | cons x s ih =>
    obtain ⟨y, o⟩ := x
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq]
    cases o with
    | none =>
      simp only [List.filterMap_cons, reduceCtorEq, and_false, exists_false, if_false,
        add_zero]
      exact ih
    | some e' =>
      simp only [List.filterMap_cons, List.count_cons, ih, Option.some.injEq, beq_iff_eq]
      congr 1
      by_cases h : e' = e
      · simp [h]
      · simp [h]

/-- Counting by fibres. -/
lemma card_le_of_fiber {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (h : ∀ x ∈ s, f x ∈ t) (b : ℕ) (hb : ∀ y ∈ t, (s.filter (fun x => f x = y)).card ≤ b) :
    s.card ≤ t.card * b := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := t) (fun x hx => h x hx)]
  calc ∑ y ∈ t, (s.filter (fun x => f x = y)).card ≤ ∑ _y ∈ t, b := Finset.sum_le_sum hb
    _ = t.card * b := by rw [Finset.sum_const, smul_eq_mul]

section Det

variable (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ) (ω : RWSeeds C P R ℓ)

/-- The node of `G₀` at which walk `w` ends. -/
noncomputable def endOf (w : RWIdx P R) : Port V := (rwEnd C w.1.1 (ω w)).getD w.1.1

variable {C P R ℓ ω}

lemma mem_rwSurvivors {w : RWIdx P R} :
    w ∈ rwSurvivors C P R ℓ ω ↔ rwSurv C P w.1.1 (ω w) := by
  unfold rwSurvivors; simp

lemma endOf_of_surv {w : RWIdx P R} (h : rwSurv C P w.1.1 (ω w)) :
    endOf C P R ℓ ω w ∈ P ∧ rwEnd C w.1.1 (ω w) = some (endOf C P R ℓ ω w) := by
  obtain ⟨q, hq, he⟩ := h
  unfold endOf; rw [he]; exact ⟨hq, rfl⟩

lemma volMG_rwG0 (A : Finset (Port V)) :
    volMG (rwG0 C P R ℓ ω) A = ∑ w ∈ rwSurvivors C P R ℓ ω,
      ((if w.1.1 ∈ A then 1 else 0) + (if endOf C P R ℓ ω w ∈ A then 1 else 0)) := by
  unfold volMG rwG0; rw [Multiset.map_map]; rfl

lemma cutMG_rwG0 (A : Finset (Port V)) :
    cutMG (rwG0 C P R ℓ ω) A = ((rwSurvivors C P R ℓ ω).filter (fun w =>
      (w.1.1 ∈ A ∧ endOf C P R ℓ ω w ∉ A) ∨ (w.1.1 ∉ A ∧ endOf C P R ℓ ω w ∈ A))).card := by
  unfold cutMG rwG0; rw [Multiset.filter_map, Multiset.card_map]; rfl

lemma rwPath_count (p : Port V) (σ : Fin (2 * ℓ) → Fin (seedRange C)) (e : Sym2 V) :
    (rwPath C p σ).count e = (if p.2 = e then 1 else 0) +
      ∑ j ∈ range (2 * ℓ), if ∃ y, (rwTraj C p σ)[j + 1]? = some (y, some e) then 1 else 0 := by
  unfold rwPath
  rw [count_filterMap_snd]
  have hlen : (rwTraj C p σ).length = 2 * ℓ + 1 := by
    unfold rwTraj; simp [walkSteps_length]
  rw [hlen, Finset.sum_range_succ', add_comm]
  congr 1
  unfold rwTraj
  simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, exists_and_left,
    exists_eq']
  by_cases h : p.2 = e <;> simp [h]

variable (hP : P ⊆ allPorts C)
include hP

lemma card_filter_snd_le (e : Sym2 V) : (P.filter (fun p => p.2 = e)).card ≤ 2 := by
  calc (P.filter (fun p => p.2 = e)).card ≤ (univ.filter (fun z : V => z ∈ e)).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1)
        · intro p hp
          rw [mem_coe, mem_filter] at hp
          have := (mem_allPorts'.1 (hP hp.1)).2
          rw [hp.2] at this
          simp [this]
        · intro p hp p' hp' h
          rw [mem_coe, mem_filter] at hp hp'
          exact Prod.ext h (hp.2.trans hp'.2.symm)
    _ ≤ 2 := card_filter_mem_sym2_le e

/-- **Claims 3.4/3.5, deterministic part.** -/
theorem trueParams_of_good (h2P : 2 ≤ P.card) (hi hc L φ : ℕ) (hL : 1 ≤ L)
    (hφ : 2 * hi ≤ φ * L)
    (hfrom : ∀ p ∈ P,
      (univ.filter (fun w : RWIdx P R => w.1.1 = p ∧ rwSurv C P w.1.1 (ω w))).card ≤ hi)
    (hto : ∀ q ∈ P,
      (univ.filter (fun w : RWIdx P R => rwEnd C w.1.1 (ω w) = some q)).card ≤ hi)
    (hcut : ∀ A ⊆ P, A.Nonempty → 2 * A.card ≤ P.card → A.card * L ≤
      (univ.filter (fun w : RWIdx P R => w.1.1 ∈ A ∧
        ∃ q ∈ P \ A, rwEnd C w.1.1 (ω w) = some q)).card)
    (hcong : ∀ e, ∀ j < 2 * ℓ, (univ.filter (fun w : RWIdx P R =>
      (∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e)) ∧
        rwSurv C P w.1.1 (ω w))).card ≤ hc) :
    TrueParams C P R ℓ ω ⟨P.card, hi * P.card, φ, 2 * hi + 2 * ℓ * hc, 2 * ℓ + 1⟩ := by
  set S := rwSurvivors C P R ℓ ω with hS
  have hSP : ∀ w ∈ S, w.1.1 ∈ P := fun w _ => w.1.2
  have hSend : ∀ w ∈ S, endOf C P R ℓ ω w ∈ P :=
    fun w hw => (endOf_of_surv (mem_rwSurvivors.1 hw)).1
  -- surviving walks from a port
  have hfib : ∀ p ∈ P, (S.filter (fun w => w.1.1 = p)).card ≤ hi := by
    intro p hp
    refine le_trans (Finset.card_le_card ?_) (hfrom p hp)
    intro w hw
    rw [mem_filter] at hw ⊢
    exact ⟨mem_univ _, hw.2, mem_rwSurvivors.1 hw.1⟩
  have hfibE : ∀ q ∈ P, (S.filter (fun w => endOf C P R ℓ ω w = q)).card ≤ hi := by
    intro q hq
    refine le_trans (Finset.card_le_card ?_) (hto q hq)
    intro w hw
    rw [mem_filter] at hw ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [(endOf_of_surv (mem_rwSurvivors.1 hw.1)).2, hw.2]
  -- volumes
  have hvol : ∀ A ⊆ P, volMG (rwG0 C P R ℓ ω) A ≤ 2 * hi * A.card := by
    intro A hA
    rw [volMG_rwG0, Finset.sum_add_distrib, ← card_filter, ← card_filter]
    have h1 : (S.filter (fun w => w.1.1 ∈ A)).card ≤ A.card * hi := by
      apply card_le_of_fiber _ A (fun w : RWIdx P R => w.1.1) (fun w hw => (mem_filter.1 hw).2)
      intro p hp
      refine le_trans (Finset.card_le_card ?_) (hfib p (hA hp))
      intro w hw
      rw [mem_filter, mem_filter] at hw
      rw [mem_filter]; exact ⟨hw.1.1, hw.2⟩
    have h2 : (S.filter (fun w => endOf C P R ℓ ω w ∈ A)).card ≤ A.card * hi := by
      apply card_le_of_fiber _ A (fun w : RWIdx P R => endOf C P R ℓ ω w)
        (fun w hw => (mem_filter.1 hw).2)
      intro p hp
      refine le_trans (Finset.card_le_card ?_) (hfibE p (hA hp))
      intro w hw
      rw [mem_filter, mem_filter] at hw
      rw [mem_filter]; exact ⟨hw.1.1, hw.2⟩
    nlinarith
  -- cuts
  have hcutS : ∀ A ⊆ P, A.Nonempty → 2 * A.card ≤ P.card →
      A.card * L ≤ cutMG (rwG0 C P R ℓ ω) A := by
    intro A hA hne h2
    refine le_trans (hcut A hA hne h2) ?_
    rw [cutMG_rwG0]
    apply Finset.card_le_card
    intro w hw
    rw [mem_filter] at hw ⊢
    obtain ⟨-, hwA, q, hq, hend⟩ := hw
    have hsurv : rwSurv C P w.1.1 (ω w) := ⟨q, (mem_sdiff.1 hq).1, hend⟩
    refine ⟨mem_rwSurvivors.2 hsurv, Or.inl ⟨hwA, ?_⟩⟩
    have : endOf C P R ℓ ω w = q := by unfold endOf; rw [hend]; rfl
    rw [this]; exact (mem_sdiff.1 hq).2
  have hcut_le_vol : ∀ A, cutMG (rwG0 C P R ℓ ω) A ≤ volMG (rwG0 C P R ℓ ω) A := by
    intro A
    rw [cutMG_rwG0, volMG_rwG0, card_filter]
    refine Finset.sum_le_sum (fun w _ => ?_)
    split_ifs <;> simp_all
  have hcut_symm : ∀ A ⊆ P, cutMG (rwG0 C P R ℓ ω) (P \ A) = cutMG (rwG0 C P R ℓ ω) A := by
    intro A _
    rw [cutMG_rwG0, cutMG_rwG0]
    congr 1
    apply Finset.filter_congr
    intro w hw
    have h1 := hSP w hw
    have h2 := hSend w hw
    simp only [mem_sdiff, h1, h2, true_and, not_not]
    tauto
  have hside : ∀ B ⊆ P, 2 * B.card ≤ P.card →
      volMG (rwG0 C P R ℓ ω) B ≤ φ * cutMG (rwG0 C P R ℓ ω) B := by
    intro B hB h2
    refine le_trans (hvol B hB) ?_
    rcases B.eq_empty_or_nonempty with h | h
    · rw [h]; simp
    · have := hcutS B hB h h2
      calc 2 * hi * B.card ≤ φ * L * B.card := Nat.mul_le_mul_right _ hφ
        _ = φ * (B.card * L) := by ring
        _ ≤ φ * cutMG (rwG0 C P R ℓ ω) B := Nat.mul_le_mul_left _ this
  refine ⟨le_refl _, ?_, ⟨?_, ?_⟩, ?_, le_refl _⟩
  · -- number of edges
    show S.card ≤ hi * P.card
    rw [mul_comm]
    exact card_le_of_fiber S P (fun w : RWIdx P R => w.1.1) hSP hi hfib
  · -- no isolated node
    intro p hp
    have h1 := hcutS {p} (singleton_subset_iff.2 hp) (singleton_nonempty p)
      (by rw [card_singleton]; omega)
    have h2 := hcut_le_vol {p}
    rw [card_singleton, one_mul] at h1
    omega
  · -- conductance
    intro A hA
    by_cases h : 2 * A.card ≤ P.card
    · exact le_trans (min_le_left _ _) (hside A hA h)
    · have hB : P \ A ⊆ P := sdiff_subset
      have hcB : 2 * (P \ A).card ≤ P.card := by
        rw [card_sdiff_of_subset hA]; omega
      refine le_trans (min_le_right _ _) ?_
      rw [← hcut_symm A hA]
      exact hside _ hB hcB
  · -- congestion
    show C.sup _ ≤ _
    apply Finset.sup_le
    intro e _
    simp only [rwPath_count]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have hA1 : ∑ w ∈ S, (if w.1.1.2 = e then 1 else 0) ≤ 2 * hi := by
      rw [← card_filter]
      have := card_le_of_fiber (S.filter (fun w => w.1.1.2 = e)) (P.filter (fun p => p.2 = e))
        (fun w : RWIdx P R => w.1.1)
        (fun w hw => by rw [mem_filter] at hw ⊢; exact ⟨hSP w hw.1, hw.2⟩) hi
        (fun p hp => by
          refine le_trans (Finset.card_le_card ?_) (hfib p (mem_filter.1 hp).1)
          intro w hw
          rw [mem_filter, mem_filter] at hw
          rw [mem_filter]; exact ⟨hw.1.1, hw.2⟩)
      exact this.trans (Nat.mul_le_mul_right _ (card_filter_snd_le hP e))
    have hA2 : ∀ j ∈ range (2 * ℓ), ∑ w ∈ S,
        (if ∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e) then 1 else 0) ≤ hc := by
      intro j hj
      rw [← card_filter]
      refine le_trans (Finset.card_le_card ?_) (hcong e j (mem_range.1 hj))
      intro w hw; rw [mem_filter] at hw ⊢
      exact ⟨mem_univ _, hw.2, mem_rwSurvivors.1 hw.1⟩
    calc ∑ x ∈ S, (if x.1.1.2 = e then 1 else 0) + ∑ j ∈ range (2 * ℓ), ∑ w ∈ S,
          (if ∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e) then 1 else 0)
        ≤ 2 * hi + ∑ j ∈ range (2 * ℓ), hc := Nat.add_le_add hA1 (Finset.sum_le_sum hA2)
      _ = 2 * hi + 2 * ℓ * hc := by rw [Finset.sum_const, card_range, smul_eq_mul]

end Det

end APSP.Stoc
