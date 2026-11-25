import ApspStoc.Base.Basic

/-!
# Lemma 3.7: properties of the aggregator set

For a cluster `C` with node set `s` (`n_C = |s|`), degree function `d` (degrees inside `C`) and
`m_C` edges, the aggregator set `A(C)` is a minimal set of highest-degree nodes whose total
degree is at least `n_C` (Definition 3.6). We prove existence and the three items of Lemma 3.7:

1. `∑_{a∈A} d a < 2 n_C`,
2. `|A| · m_C < n_C²`          (i.e. `q_C < n_C² / m_C`),
3. `m_C ≤ 2 n_C · d a` for all `a ∈ A` (i.e. `d a ≥ m_C / 2n_C`).

The hypotheses are exactly what holds for a cluster of an expander *edge* decomposition: every
node of the cluster has degree `≥ 1` (it is an endpoint of a cluster edge) and `≤ n_C - 1`
(simple graph). (The paper states the lemma for connected clusters; connectivity is only used to
get `d ≥ 1`.)

Theorem numbers refer to the STOC submission of the paper.
-/

namespace APSP

open Finset

variable {α : Type*} [DecidableEq α]

/-- `A ⊆ s` consists of highest-degree nodes: every node of `A` has degree at least that of every
node of `s \ A`. -/
def IsTop (s A : Finset α) (d : α → ℕ) : Prop := A ⊆ s ∧ ∀ a ∈ A, ∀ b ∈ s \ A, d b ≤ d a

/-- `A` is an aggregator set of `s` (Definition 3.6): a top-degree set with total degree
`≥ |s|`, which is minimal: removing its minimum-degree element drops the total below `|s|`. -/
structure IsAggSet (s A : Finset α) (d : α → ℕ) : Prop where
  top : IsTop s A d
  enough : s.card ≤ ∑ a ∈ A, d a
  minimal : ∃ a₀ ∈ A, (∀ a ∈ A, d a₀ ≤ d a) ∧ ∑ a ∈ A.erase a₀, d a < s.card

lemma isTop_erase_min {s A : Finset α} {d : α → ℕ} (h : IsTop s A d) {a₀ : α} (ha₀ : a₀ ∈ A)
    (hmin : ∀ a ∈ A, d a₀ ≤ d a) : IsTop s (A.erase a₀) d := by
  refine ⟨(erase_subset _ _).trans h.1, fun a ha b hb => ?_⟩
  rw [mem_sdiff] at hb
  by_cases hba : b = a₀
  · subst hba; exact hmin a (mem_of_mem_erase ha)
  · have : b ∉ A := fun hbA => hb.2 (mem_erase.2 ⟨hba, hbA⟩)
    exact h.2 a (mem_of_mem_erase ha) b (mem_sdiff.2 ⟨hb.1, this⟩)

/-- Existence of an aggregator set (as soon as the total degree is at least `|s| ≥ 1`). -/
lemma exists_aggSet (s : Finset α) (d : α → ℕ) (hs : 1 ≤ s.card)
    (hsum : s.card ≤ ∑ v ∈ s, d v) : ∃ A, IsAggSet s A d := by
  classical
  let P : ℕ → Prop := fun k => ∃ A, IsTop s A d ∧ A.card = k ∧ s.card ≤ ∑ a ∈ A, d a
  have hP : ∃ k, P k := ⟨s.card, s, ⟨subset_refl _, by simp⟩, rfl, hsum⟩
  obtain ⟨A, hAtop, hAcard, hAsum⟩ := Nat.find_spec hP
  have hAne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hAsum
    omega
  obtain ⟨a₀, ha₀, hmin⟩ := exists_min_image A d hAne
  refine ⟨A, hAtop, hAsum, a₀, ha₀, hmin, ?_⟩
  by_contra hcon
  push Not at hcon
  have hlt : (A.erase a₀).card < Nat.find hP := by
    rw [card_erase_of_mem ha₀, hAcard]
    have : 0 < A.card := card_pos.2 hAne
    omega
  exact Nat.find_min hP hlt ⟨A.erase a₀, isTop_erase_min hAtop ha₀ hmin, rfl, hcon⟩

/-- Top-degree sets have average degree at least the overall average. -/
lemma card_mul_sum_le_of_top {s A : Finset α} {d : α → ℕ} (hA : A ⊆ s) (μ : ℕ)
    (hμA : ∀ a ∈ A, μ ≤ d a) (hμB : ∀ b ∈ s \ A, d b ≤ μ) :
    A.card * ∑ v ∈ s, d v ≤ s.card * ∑ a ∈ A, d a := by
  have hsplit : ∑ v ∈ s, d v = ∑ a ∈ A, d a + ∑ b ∈ s \ A, d b := by
    rw [add_comm, sum_sdiff hA]
  have hcard : s.card = A.card + (s \ A).card := by
    rw [card_sdiff_of_subset hA]; have := card_le_card hA; omega
  have h1 : A.card * μ ≤ ∑ a ∈ A, d a := by
    have := card_nsmul_le_sum A d μ hμA; simpa using this
  have h2 : ∑ b ∈ s \ A, d b ≤ (s \ A).card * μ := by
    have := sum_le_card_nsmul (s \ A) d μ hμB; simpa using this
  rw [hsplit, hcard]
  nlinarith

section Lemma37

variable {s A : Finset α} {d : α → ℕ} {m : ℕ}

/-- Lemma 3.7 (1): the total degree of `A(C)` is less than `2 n_C`. -/
theorem aggSet_sum_lt (hA : IsAggSet s A d) (hdeg : ∀ v ∈ s, d v + 1 ≤ s.card) :
    ∑ a ∈ A, d a < 2 * s.card := by
  obtain ⟨a₀, ha₀, -, hlt⟩ := hA.minimal
  have h := sum_erase_add A d ha₀
  have := hdeg a₀ (hA.top.1 ha₀)
  omega

/-- Lemma 3.7 (2): `q_C · m_C < n_C²`, i.e. `|A(C)| < n_C² / m_C`. -/
theorem aggSet_card_mul_lt (hA : IsAggSet s A d) (hdeg : ∀ v ∈ s, d v + 1 ≤ s.card)
    (hm : ∑ v ∈ s, d v = 2 * m) : A.card * m < s.card ^ 2 := by
  obtain ⟨a₀, ha₀, hmin, -⟩ := hA.minimal
  have havg := card_mul_sum_le_of_top hA.top.1 (d a₀) hmin
    (fun b hb => hA.top.2 a₀ ha₀ b hb)
  have h1 := aggSet_sum_lt hA hdeg
  have hspos : 0 < s.card := card_pos.2 ⟨a₀, hA.top.1 ha₀⟩
  rw [hm] at havg
  nlinarith

/-- Lemma 3.7 (3): every aggregator has degree at least `m_C / 2 n_C`. -/
theorem aggSet_deg_ge (hA : IsAggSet s A d) (hdeg : ∀ v ∈ s, 1 ≤ d v ∧ d v + 1 ≤ s.card)
    (hm : ∑ v ∈ s, d v = 2 * m) : ∀ a ∈ A, m ≤ 2 * s.card * d a := by
  intro a ha
  obtain ⟨a₀, ha₀, hmin, -⟩ := hA.minimal
  have hda : 1 ≤ d a := (hdeg a (hA.top.1 ha)).1
  by_cases hsmall : m ≤ 2 * s.card
  · calc m ≤ 2 * s.card := hsmall
      _ = 2 * s.card * 1 := by ring
      _ ≤ 2 * s.card * d a := Nat.mul_le_mul_left _ hda
  · push Not at hsmall
    have h1 := aggSet_sum_lt hA (fun v hv => (hdeg v hv).2)
    have hsplit : ∑ v ∈ s, d v = ∑ a ∈ A, d a + ∑ b ∈ s \ A, d b := by
      rw [add_comm, sum_sdiff hA.top.1]
    have h2 : ∑ b ∈ s \ A, d b ≤ (s \ A).card * d a₀ := by
      have := sum_le_card_nsmul (s \ A) d (d a₀) (fun b hb => hA.top.2 a₀ ha₀ b hb)
      simpa using this
    have h3 : (s \ A).card ≤ s.card := card_le_card sdiff_subset
    have h4 : d a₀ ≤ d a := hmin a ha
    have h5 : (s \ A).card * d a₀ ≤ s.card * d a := Nat.mul_le_mul h3 h4
    nlinarith

end Lemma37

end APSP
