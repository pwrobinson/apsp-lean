import ApspStoc.Base.Basic

/-!
# Chernoff bounds on finite uniform product spaces

Pure probability used by the proof of Claims 3.4/3.5: for a uniform `ω : ι → S` and events
`E i` on the coordinates, the number `X ω` of indices `i` with `E i (ω i)` satisfies
`P(X ≥ t) ≤ exp(2μ - t)` if `E[X] ≤ μ`, and `P(X ≤ s) ≤ exp(s - μ/2)` if `E[X] ≥ μ`.
-/

namespace APSP.Stoc

open Finset

section Chernoff

variable {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq ι]

/-- The exponential moment of a sum over independent coordinates factorises. -/
lemma sum_exp_sum_eq_prod (b : ι → S → ℝ) :
    ∑ ω : ι → S, Real.exp (∑ i, b i (ω i)) = ∏ i, ∑ s, Real.exp (b i s) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Real.exp_sum]

lemma sum_exp_sum_le (b : ι → S → ℝ) (β : ι → ℝ)
    (hb : ∀ i, ∑ s, Real.exp (b i s) ≤ (Fintype.card S : ℝ) * Real.exp (β i)) :
    ∑ ω : ι → S, Real.exp (∑ i, b i (ω i)) ≤
      (Fintype.card (ι → S) : ℝ) * Real.exp (∑ i, β i) := by
  rw [sum_exp_sum_eq_prod]
  calc ∏ i, ∑ s, Real.exp (b i s) ≤ ∏ i, ((Fintype.card S : ℝ) * Real.exp (β i)) := by
        gcongr with i; exact hb i
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
          Nat.cast_pow, Real.exp_sum]

open Classical in
/-- Chernoff upper tail (with `λ = 1`): `P(X ≥ t) ≤ exp(2μ - t)` when `E[X] ≤ μ`. -/
theorem chernoff_upper (E : ι → S → Prop) (μ t : ℝ)
    (hμ : ∑ i, ((univ.filter (E i)).card : ℝ) / Fintype.card S ≤ μ)
    (ev : (ι → S) → Prop) [DecidablePred ev]
    (hev : ∀ ω, ev ω → t ≤ ((univ.filter (fun i => E i (ω i))).card : ℝ)) :
    ((univ.filter ev).card : ℝ) / Fintype.card (ι → S) ≤ Real.exp (2 * μ - t) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · rcases isEmpty_or_nonempty ι with hι | hι
    · -- a single point `ω`, with `X ω = 0`
      have h0 : ∀ ω : ι → S, ((univ.filter (fun i => E i (ω i))).card : ℝ) = 0 := by
        intro ω; simp
      have hμ0 : 0 ≤ μ := by simpa using hμ
      have hcard : Fintype.card (ι → S) = 1 := by simp
      rw [hcard, Nat.cast_one, div_one]
      by_cases hne : (univ.filter ev).Nonempty
      · obtain ⟨ω, hω⟩ := hne
        have ht := hev ω (mem_filter.1 hω).2
        rw [h0] at ht
        have : ((univ.filter ev).card : ℝ) ≤ 1 := by
          have := card_le_univ (univ.filter ev); rw [hcard] at this; exact_mod_cast this
        calc ((univ.filter ev).card : ℝ) ≤ 1 := this
          _ ≤ Real.exp (2 * μ - t) := Real.one_le_exp (by linarith)
      · rw [not_nonempty_iff_eq_empty.1 hne]; simp; exact (Real.exp_pos _).le
    · have : Fintype.card (ι → S) = 0 := by
        rw [Fintype.card_eq_zero_iff]; exact ⟨fun ω => hS.elim (ω (Classical.arbitrary ι))⟩
      rw [this, Nat.cast_zero, div_zero]; exact (Real.exp_pos _).le
  have hN : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hNf : (0 : ℝ) < Fintype.card (ι → S) := by exact_mod_cast Fintype.card_pos
  set a : ι → S → ℝ := fun i s => if E i s then 1 else 0 with ha
  have hX : ∀ ω : ι → S, ((univ.filter (fun i => E i (ω i))).card : ℝ) = ∑ i, a i (ω i) := by
    intro ω; rw [card_filter]; push_cast; rfl
  -- pointwise: indicator ≤ exp(X - t)
  have hpt : ∀ ω : ι → S, (if ev ω then (1 : ℝ) else 0) ≤
      Real.exp (-t) * Real.exp (∑ i, a i (ω i)) := by
    intro ω
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp; have := hev ω h; rw [hX] at this; linarith
    · exact (Real.exp_pos _).le
  have hsum : ((univ.filter ev).card : ℝ) ≤
      Real.exp (-t) * ((Fintype.card (ι → S) : ℝ) * Real.exp (∑ i, 2 *
        (((univ.filter (E i)).card : ℝ) / Fintype.card S))) := by
    rw [card_filter]; push_cast
    calc ∑ ω, (if ev ω then (1 : ℝ) else 0) ≤ ∑ ω, Real.exp (-t) * Real.exp (∑ i, a i (ω i)) :=
          Finset.sum_le_sum (fun ω _ => hpt ω)
      _ = Real.exp (-t) * ∑ ω : ι → S, Real.exp (∑ i, a i (ω i)) := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          apply sum_exp_sum_le
          intro i
          have he : ∀ s, Real.exp (a i s) = 1 + (Real.exp 1 - 1) * a i s := by
            intro s; simp only [ha]; split_ifs <;> simp
          simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum]
          have hc : ∑ s, a i s = ((univ.filter (E i)).card : ℝ) := by
            simp only [ha]; rw [card_filter]; push_cast; rfl
          rw [hc]
          simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
          have he1 : Real.exp 1 - 1 ≤ 2 := by
            have := Real.exp_one_lt_d9; linarith
          have hc0 : (0 : ℝ) ≤ ((univ.filter (E i)).card : ℝ) := Nat.cast_nonneg _
          calc (Fintype.card S : ℝ) + (Real.exp 1 - 1) * ((univ.filter (E i)).card : ℝ)
              ≤ (Fintype.card S : ℝ) * (1 + 2 * (((univ.filter (E i)).card : ℝ) /
                  Fintype.card S)) := by
                rw [mul_add, mul_one, show (Fintype.card S : ℝ) * (2 *
                  (((univ.filter (E i)).card : ℝ) / Fintype.card S)) =
                    2 * ((univ.filter (E i)).card : ℝ) by field_simp]
                nlinarith
            _ ≤ _ := by
                gcongr
                have := Real.add_one_le_exp (2 * (((univ.filter (E i)).card : ℝ) /
                  Fintype.card S))
                linarith
  rw [div_le_iff₀ hNf]
  calc ((univ.filter ev).card : ℝ) ≤ _ := hsum
    _ ≤ Real.exp (-t) * ((Fintype.card (ι → S) : ℝ) * Real.exp (2 * μ)) := by
        gcongr; rw [← Finset.mul_sum]; linarith
    _ = Real.exp (2 * μ - t) * Fintype.card (ι → S) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring

open Classical in
/-- Chernoff lower tail (with `λ = 1`): `P(X ≤ s) ≤ exp(s - μ/2)` when `E[X] ≥ μ`. -/
theorem chernoff_lower (E : ι → S → Prop) (μ s : ℝ)
    (hμ : μ ≤ ∑ i, ((univ.filter (E i)).card : ℝ) / Fintype.card S)
    (ev : (ι → S) → Prop) [DecidablePred ev]
    (hev : ∀ ω, ev ω → ((univ.filter (fun i => E i (ω i))).card : ℝ) ≤ s) :
    ((univ.filter ev).card : ℝ) / Fintype.card (ι → S) ≤ Real.exp (s - μ / 2) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · rcases isEmpty_or_nonempty ι with hι | hι
    · have h0 : ∀ ω : ι → S, ((univ.filter (fun i => E i (ω i))).card : ℝ) = 0 := by
        intro ω; simp
      have hμ0 : μ ≤ 0 := by simpa using hμ
      have hcard : Fintype.card (ι → S) = 1 := by simp
      rw [hcard, Nat.cast_one, div_one]
      by_cases hne : (univ.filter ev).Nonempty
      · obtain ⟨ω, hω⟩ := hne
        have ht := hev ω (mem_filter.1 hω).2
        rw [h0] at ht
        have : ((univ.filter ev).card : ℝ) ≤ 1 := by
          have := card_le_univ (univ.filter ev); rw [hcard] at this; exact_mod_cast this
        calc ((univ.filter ev).card : ℝ) ≤ 1 := this
          _ ≤ Real.exp (s - μ / 2) := Real.one_le_exp (by linarith)
      · rw [not_nonempty_iff_eq_empty.1 hne]; simp; exact (Real.exp_pos _).le
    · have : Fintype.card (ι → S) = 0 := by
        rw [Fintype.card_eq_zero_iff]; exact ⟨fun ω => hS.elim (ω (Classical.arbitrary ι))⟩
      rw [this, Nat.cast_zero, div_zero]; exact (Real.exp_pos _).le
  have hN : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hNf : (0 : ℝ) < Fintype.card (ι → S) := by exact_mod_cast Fintype.card_pos
  set a : ι → S → ℝ := fun i s => if E i s then -1 else 0 with ha
  have hX : ∀ ω : ι → S, -((univ.filter (fun i => E i (ω i))).card : ℝ) = ∑ i, a i (ω i) := by
    intro ω; rw [card_filter]; push_cast; rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); simp only [ha]; split_ifs <;> simp
  have hpt : ∀ ω : ι → S, (if ev ω then (1 : ℝ) else 0) ≤
      Real.exp s * Real.exp (∑ i, a i (ω i)) := by
    intro ω
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp; have := hev ω h; rw [← hX]; linarith
    · exact (Real.exp_pos _).le
  have hsum : ((univ.filter ev).card : ℝ) ≤
      Real.exp s * ((Fintype.card (ι → S) : ℝ) * Real.exp (∑ i, -(1 / 2) *
        (((univ.filter (E i)).card : ℝ) / Fintype.card S))) := by
    rw [card_filter]; push_cast
    calc ∑ ω, (if ev ω then (1 : ℝ) else 0) ≤ ∑ ω, Real.exp s * Real.exp (∑ i, a i (ω i)) :=
          Finset.sum_le_sum (fun ω _ => hpt ω)
      _ = Real.exp s * ∑ ω : ι → S, Real.exp (∑ i, a i (ω i)) := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          apply sum_exp_sum_le
          intro i
          have he : ∀ s, Real.exp (a i s) = 1 - (1 - Real.exp (-1)) *
              (if E i s then (1 : ℝ) else 0) := by
            intro s; simp only [ha]; split_ifs <;> simp
          simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
          have hc : ∑ s, (if E i s then (1 : ℝ) else 0) = ((univ.filter (E i)).card : ℝ) := by
            rw [card_filter]; push_cast; rfl
          rw [hc]
          simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
          have he1 : (1 / 2 : ℝ) ≤ 1 - Real.exp (-1) := by
            have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
            have : Real.exp (-1) ≤ 1 / 2 := by
              rw [Real.exp_neg]; rw [inv_eq_one_div]
              exact one_div_le_one_div_of_le (by norm_num) h2
            linarith
          have hc0 : (0 : ℝ) ≤ ((univ.filter (E i)).card : ℝ) := Nat.cast_nonneg _
          calc (Fintype.card S : ℝ) - (1 - Real.exp (-1)) * ((univ.filter (E i)).card : ℝ)
              ≤ (Fintype.card S : ℝ) * (1 + -(1 / 2) * (((univ.filter (E i)).card : ℝ) /
                  Fintype.card S)) := by
                rw [mul_add, mul_one, show (Fintype.card S : ℝ) * (-(1 / 2) *
                  (((univ.filter (E i)).card : ℝ) / Fintype.card S)) =
                    -(1 / 2) * ((univ.filter (E i)).card : ℝ) by field_simp]
                nlinarith
            _ ≤ _ := by
                gcongr
                have := Real.add_one_le_exp (-(1 / 2) * (((univ.filter (E i)).card : ℝ) /
                  Fintype.card S))
                linarith
  rw [div_le_iff₀ hNf]
  calc ((univ.filter ev).card : ℝ) ≤ _ := hsum
    _ ≤ Real.exp s * ((Fintype.card (ι → S) : ℝ) * Real.exp (-(1 / 2) * μ)) := by
        gcongr; rw [← Finset.mul_sum]; linarith
    _ = Real.exp (s - μ / 2) * Fintype.card (ι → S) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring_nf

end Chernoff

/-- `exp(-K lg ν) ≤ ν^{-K}`. -/
lemma exp_neg_lg_le (K ν : ℕ) (hν : 1 ≤ ν) :
    Real.exp (-((K : ℝ) * (lg ν : ℝ))) ≤ 1 / (ν : ℝ) ^ K := by
  have hν' : (0 : ℝ) < ν := by exact_mod_cast hν
  have h1 : (ν : ℝ) ≤ Real.exp (lg ν) := by
    have h2 : (ν : ℝ) ≤ (2 : ℝ) ^ lg ν := by exact_mod_cast (lt_two_pow_lg ν).le
    calc (ν : ℝ) ≤ (2 : ℝ) ^ lg ν := h2
      _ ≤ Real.exp 1 ^ lg ν := by
          gcongr; have := Real.exp_one_gt_d9; linarith
      _ = Real.exp (lg ν) := by rw [← Real.exp_nat_mul, mul_one]
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  calc (ν : ℝ) ^ K ≤ Real.exp (lg ν) ^ K := by gcongr
    _ = Real.exp (K * lg ν) := by rw [← Real.exp_nat_mul]

end APSP.Stoc
