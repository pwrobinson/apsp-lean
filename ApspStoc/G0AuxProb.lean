import ApspStoc.G0AuxDet
import ApspStoc.G0AuxChernoff

/-!
# The probabilistic part of Claims 3.4/3.5

Expected values of the relevant counts of walks (from the one-walk facts of `G0AuxWalk.lean`)
and the Chernoff bounds for them; the union bound over all failure events.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The start node of the lazy walk of the tokens of port `p`. -/
noncomputable def startOf (p : Port V) : V := otherEnd p.2 p.1

lemma startOf_mem {C : Finset (Sym2 V)} {p : Port V} (hp : p ∈ allPorts C) :
    startOf p ∈ nodes C :=
  mem_nodes_of (mem_allPorts'.1 hp).1 (otherEnd_mem (mem_allPorts'.1 hp).2)

lemma rwEnd_eq_lastPort (C : Finset (Sym2 V)) (p : Port V) {ℓ : ℕ}
    (σ : Fin (2 * ℓ) → Fin (seedRange C)) : rwEnd C p σ = lastPort (rwTraj C p σ) := by
  unfold rwEnd lastPort
  rcases (rwTraj C p σ).getLast? with _ | ⟨x, _ | e⟩ <;> rfl

lemma card_filter_iff {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (h : ∀ a, p a ↔ q a) : (univ.filter p).card = (univ.filter q).card := by
  congr 1; ext a; simp [h]

/-- Some port starts more than `hi` surviving walks. -/
abbrev evFrom (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ hi : ℕ) (ω : RWSeeds C P R ℓ) :
    Prop :=
  ∃ p ∈ P, hi < (univ.filter (fun w : RWIdx P R => w.1.1 = p ∧ rwSurv C P w.1.1 (ω w))).card

/-- Some port receives more than `hi` surviving walks. -/
abbrev evTo (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ hi : ℕ) (ω : RWSeeds C P R ℓ) :
    Prop :=
  ∃ q ∈ P, hi < (univ.filter (fun w : RWIdx P R => rwEnd C w.1.1 (ω w) = some q)).card

/-- Some small set `A` sends fewer than `|A| L` surviving walks out of `A`. -/
abbrev evCut (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ L : ℕ) (ω : RWSeeds C P R ℓ) :
    Prop :=
  ∃ A ∈ P.powerset.filter (fun A => A.Nonempty ∧ 2 * A.card ≤ P.card),
    (univ.filter (fun w : RWIdx P R => w.1.1 ∈ A ∧
      ∃ q ∈ P \ A, rwEnd C w.1.1 (ω w) = some q)).card < A.card * L

/-- In some step more than `hc` surviving walks cross some edge. -/
abbrev evCong (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ hc : ℕ) (ω : RWSeeds C P R ℓ) :
    Prop :=
  ∃ e ∈ (univ : Finset (Sym2 V)), ∃ j ∈ range (2 * ℓ), hc < (univ.filter (fun w : RWIdx P R =>
    (∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e)) ∧ rwSurv C P w.1.1 (ω w))).card

/-- `mem_filter` for an arbitrary decidability instance (unified, not synthesized). -/
lemma mem_filter' {α : Type*} {p : α → Prop} {inst : DecidablePred p} {s : Finset α} {a : α} :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

section Model

variable (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ)

/-! ## Union bounds -/

lemma rwProb_nonneg (ev : RWSeeds C P R ℓ → Prop) : 0 ≤ rwProb C P R ℓ ev := by
  unfold rwProb; positivity

lemma rwProb_mono {ev ev' : RWSeeds C P R ℓ → Prop} (h : ∀ ω, ev ω → ev' ω) :
    rwProb C P R ℓ ev ≤ rwProb C P R ℓ ev' := by
  unfold rwProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun ω hω => by
    rw [mem_filter'] at hω ⊢; exact ⟨hω.1, h ω hω.2⟩)

lemma rwProb_or (ev ev' : RWSeeds C P R ℓ → Prop) :
    rwProb C P R ℓ (fun ω => ev ω ∨ ev' ω) ≤ rwProb C P R ℓ ev + rwProb C P R ℓ ev' := by
  unfold rwProb
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_cast
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro ω hω
  rw [mem_filter'] at hω
  rw [mem_union, mem_filter', mem_filter']
  rcases hω.2 with h | h
  · exact Or.inl ⟨mem_univ _, h⟩
  · exact Or.inr ⟨mem_univ _, h⟩

lemma rwProb_or5 (a b c d e : RWSeeds C P R ℓ → Prop) :
    rwProb C P R ℓ (fun ω => a ω ∨ b ω ∨ c ω ∨ d ω ∨ e ω) ≤ rwProb C P R ℓ a +
      rwProb C P R ℓ b + rwProb C P R ℓ c + rwProb C P R ℓ d + rwProb C P R ℓ e := by
  have h1 := rwProb_or C P R ℓ a (fun ω => b ω ∨ c ω ∨ d ω ∨ e ω)
  have h2 := rwProb_or C P R ℓ b (fun ω => c ω ∨ d ω ∨ e ω)
  have h3 := rwProb_or C P R ℓ c (fun ω => d ω ∨ e ω)
  have h4 := rwProb_or C P R ℓ d e
  linarith

lemma rwProb_exists {ι : Type*} (I : Finset ι) (ev : ι → RWSeeds C P R ℓ → Prop) :
    rwProb C P R ℓ (fun ω => ∃ i ∈ I, ev i ω) ≤ ∑ i ∈ I, rwProb C P R ℓ (ev i) := by
  classical
  unfold rwProb
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_cast
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro ω hω
  rw [mem_filter'] at hω
  obtain ⟨i, hi, h⟩ := hω.2
  exact mem_biUnion.2 ⟨i, hi, by rw [mem_filter']; exact ⟨mem_univ _, h⟩⟩

/-! ## Chernoff bounds for the walks -/

open Classical in
lemma rwProb_upper (E : RWIdx P R → (Fin (2 * ℓ) → Fin (seedRange C)) → Prop)
    (pw : RWIdx P R → ℝ)
    (hpw : ∀ w, ((univ.filter (E w)).card : ℝ) /
      Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)) ≤ pw w)
    (μ t : ℝ) (hμ : ∑ w, pw w ≤ μ)
    (ev : RWSeeds C P R ℓ → Prop)
    (hev : ∀ ω, ev ω → t ≤ ((univ.filter (fun w => E w (ω w))).card : ℝ)) :
    rwProb C P R ℓ ev ≤ Real.exp (2 * μ - t) := by
  unfold rwProb
  exact chernoff_upper E μ t ((Finset.sum_le_sum (fun w _ => hpw w)).trans hμ) ev hev

open Classical in
lemma rwProb_lower (E : RWIdx P R → (Fin (2 * ℓ) → Fin (seedRange C)) → Prop)
    (pw : RWIdx P R → ℝ)
    (hpw : ∀ w, pw w ≤ ((univ.filter (E w)).card : ℝ) /
      Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)))
    (μ s : ℝ) (hμ : μ ≤ ∑ w, pw w)
    (ev : RWSeeds C P R ℓ → Prop)
    (hev : ∀ ω, ev ω → ((univ.filter (fun w => E w (ω w))).card : ℝ) ≤ s) :
    rwProb C P R ℓ ev ≤ Real.exp (s - μ / 2) := by
  unfold rwProb
  exact chernoff_lower E μ s (hμ.trans (Finset.sum_le_sum (fun w _ => hpw w))) ev hev

/-- Probability of an event of a single walk. -/
lemma prob_walk_eq (p : Port V) (E : (Fin (2 * ℓ) → Fin (seedRange C)) → Prop)
    {inst : DecidablePred E} (Ψ : List (V × Option (Sym2 V)) → Prop) [DecidablePred Ψ]
    (hE : ∀ σ, E σ ↔ Ψ (rwTraj C p σ)) :
    ((univ.filter E).card : ℝ) / Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)) =
      wexp C (2 * ℓ) (startOf p) (fun s => if Ψ ((startOf p, some p.2) :: s) then 1 else 0) := by
  unfold wexp lexp
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, card_filter]
  push_cast
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have key : E σ ↔ Ψ ((startOf p, some p.2) ::
      walkSteps C (startOf p) (List.ofFn (fun i => (σ i : ℕ)))) := hE σ
  by_cases h : E σ
  · simp only [if_pos h, if_pos (key.1 h)]
  · simp only [if_neg h, if_neg (fun h' => h (key.2 h'))]

lemma prob_walk_zero (E : (Fin (2 * ℓ) → Fin (seedRange C)) → Prop) {inst : DecidablePred E}
    (hE : ∀ σ, ¬ E σ) :
    ((univ.filter E).card : ℝ) / Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)) = 0 := by
  rw [Finset.filter_false_of_mem (fun σ _ => hE σ)]; simp

lemma sum_rwIdx (f : Port V → ℝ) : ∑ w : RWIdx P R, f w.1.1 = R * ∑ p ∈ P, f p := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_coe_sort P f]

/-- Probability that the walk of port `p` ends through a port of `Q`. -/
lemma prob_end (hℓ : 1 ≤ ℓ) (p : Port V) (Q : Finset (Port V))
    (E : (Fin (2 * ℓ) → Fin (seedRange C)) → Prop) {inst : DecidablePred E}
    (hE : ∀ σ, E σ ↔ ∃ q ∈ Q, rwEnd C p σ = some q) :
    ((univ.filter E).card : ℝ) / Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)) =
      ∑ z, walkProb C (2 * ℓ - 1) (startOf p) z * survP C Q z := by
  rw [prob_walk_eq C ℓ p E (fun s => ∃ q ∈ Q, lastPort s = some q)
    (fun σ => by rw [hE, rwEnd_eq_lastPort])]
  rw [← wexp_surv C (2 * ℓ) (by omega) (startOf p) Q]
  apply wexp_congr
  intro s hs
  rw [lastPort_cons _ _ (by intro h; subst h; simp at hs <;> omega)]

/-- Probability that the walk of port `p` crosses `e` in lazy step `j`. -/
lemma prob_cross_le (p : Port V) (j : ℕ) (hj : j < 2 * ℓ) (e : Sym2 V)
    (E : (Fin (2 * ℓ) → Fin (seedRange C)) → Prop) {inst : DecidablePred E}
    (hE : ∀ σ, E σ → ∃ y, (rwTraj C p σ)[j + 1]? = some (y, some e)) :
    ((univ.filter E).card : ℝ) / Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)) ≤
      ∑ z, walkProb C j (startOf p) z * crossP C z e := by
  calc ((univ.filter E).card : ℝ) / Fintype.card (Fin (2 * ℓ) → Fin (seedRange C))
      ≤ ((univ.filter (fun σ : Fin (2 * ℓ) → Fin (seedRange C) =>
          ∃ y, (rwTraj C p σ)[j + 1]? = some (y, some e))).card : ℝ) /
          Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (fun σ hσ => by
          rw [mem_filter'] at hσ ⊢; exact ⟨hσ.1, hE σ hσ.2⟩)
    _ = _ := by
        rw [prob_walk_eq C ℓ p _ (fun s => ∃ y, s[j + 1]? = some (y, some e)) (fun σ => Iff.rfl)]
        rw [← wexp_cross C (2 * ℓ) j hj (startOf p) e]
        apply wexp_congr
        intro s _
        simp only [List.getElem?_cons_succ]

variable {C P}
variable (hC : C.Nonempty) (hP : P ⊆ allPorts C) {T : ℕ} (hmix : MixAt C T) (hℓ : T + 1 ≤ ℓ)
include hC hP hmix hℓ

/-- Crossing `e` in step `j` and surviving. -/
lemma prob_cross_surv_le (p : Port V) (hp : p ∈ P) (j : ℕ) (hj : j < 2 * ℓ) (e : Sym2 V)
    (E : (Fin (2 * ℓ) → Fin (seedRange C)) → Prop) {inst : DecidablePred E}
    (hE : ∀ σ, E σ ↔ (∃ y, (rwTraj C p σ)[j + 1]? = some (y, some e)) ∧ rwSurv C P p σ) :
    ((univ.filter E).card : ℝ) / Fintype.card (Fin (2 * ℓ) → Fin (seedRange C)) ≤
      if T ≤ j then (3 : ℝ) / (4 * (C.card : ℝ))
      else (∑ z, walkProb C j (startOf p) z * crossP C z e) * (3 * P.card / (8 * C.card)) := by
  have hpA := hP hp
  split_ifs with hTj
  · exact (prob_cross_le C ℓ p j hj e E (fun σ h => ((hE σ).1 h).1)).trans
      (mix_cross_le hmix hC hTj (startOf_mem hpA) e)
  · obtain ⟨b, hb⟩ : ∃ b, 2 * ℓ = j + (b + 1) := ⟨2 * ℓ - j - 1, by omega⟩
    rw [prob_walk_eq C ℓ p E (fun s => (∃ y, s[j + 1]? = some (y, some e)) ∧
      ∃ q ∈ P, lastPort s = some q) (fun σ => by rw [hE, rwSurv, rwEnd_eq_lastPort])]
    rw [hb]
    have hb1 : 1 ≤ b := by omega
    calc wexp C (j + (b + 1)) (startOf p) (fun s => if (∃ y, ((startOf p, some p.2) :: s)[j + 1]? =
          some (y, some e)) ∧ ∃ q ∈ P, lastPort ((startOf p, some p.2) :: s) = some q then 1 else 0)
        = wexp C (j + (b + 1)) (startOf p) (fun s =>
            (if ∃ y, s[j]? = some (y, some e) then 1 else 0) *
            (if ∃ q ∈ P, lastPort s = some q then 1 else 0)) := by
          apply wexp_congr
          intro s hs
          rw [lastPort_cons _ _ (by intro h; subst h; simp at hs <;> omega)]
          simp only [List.getElem?_cons_succ]
          rw [ite_zero_mul_ite_zero, one_mul]
      _ ≤ _ := by
          apply wexp_cross_surv_le C j b hb1 (startOf p) e P
          intro y hy
          rw [wexp_surv C b hb1 y P]
          exact mix_surv_le hmix hC (by omega) hy P

/-! ## The failure events -/

/-- Bound on the expected number of walks per edge, step and direction (overflow). -/
lemma ovf_le (j : ℕ) (hj : j < 2 * ℓ) (y : V) (e : Sym2 V) (t : ℕ) :
    rwProb C P R ℓ (fun ω => t < (univ.filter (fun w : RWIdx P R =>
      (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e))).card) ≤
      Real.exp (2 * R - (t + 1)) := by
  refine rwProb_upper C P R ℓ (fun w σ => (rwTraj C w.1.1 σ)[j + 1]? = some (y, some e))
    (fun w => ∑ z, walkProb C j (startOf w.1.1) z * crossP C z e)
    (fun w => prob_cross_le C ℓ w.1.1 j hj e _ (fun σ h => ⟨y, h⟩)) _ _ ?_ _ ?_
  · rw [sum_rwIdx P R (fun p => ∑ z, walkProb C j (startOf p) z * crossP C z e)]
    calc (R : ℝ) * ∑ p ∈ P, ∑ z, walkProb C j (startOf p) z * crossP C z e ≤ R * 1 :=
          mul_le_mul_of_nonneg_left (sum_ports_cross_le C P hP j e) (Nat.cast_nonneg R)
      _ = R := mul_one _
  · intro ω hω
    have h' : ((t + 1 : ℕ) : ℝ) ≤ ((univ.filter (fun w : RWIdx P R =>
        (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e))).card : ℝ) := by exact_mod_cast hω
    push_cast at h'
    refine h'.trans ?_
    exact_mod_cast Finset.card_le_card (fun w hw => by rw [mem_filter'] at hw ⊢; exact hw)

/-- The expected number of surviving walks from a port is at most `3R|P|/(8m)`. -/
lemma from_le (p₀ : Port V) (hp₀ : p₀ ∈ P) (hi : ℕ) :
    rwProb C P R ℓ (fun ω => hi < (univ.filter (fun w : RWIdx P R =>
      w.1.1 = p₀ ∧ rwSurv C P w.1.1 (ω w))).card) ≤
      Real.exp (2 * (3 * R * P.card / (4 * C.card)) - (hi + 1)) := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  refine rwProb_upper C P R ℓ (fun w σ => w.1.1 = p₀ ∧ rwSurv C P w.1.1 σ)
    (fun w => if w.1.1 = p₀ then 3 * (P.card : ℝ) / (8 * C.card) else 0) ?_ _ _ ?_ _ ?_
  · intro w
    split_ifs with h
    · rw [prob_end C ℓ (by omega) w.1.1 P (fun σ => w.1.1 = p₀ ∧ rwSurv C P w.1.1 σ)
        (fun σ => by rw [rwSurv]; simp [h])]
      exact mix_surv_le (t := 2 * ℓ - 1) hmix hC (by omega) (startOf_mem (hP w.1.2)) P
    · rw [prob_walk_zero C ℓ (fun σ => w.1.1 = p₀ ∧ rwSurv C P w.1.1 σ) (fun σ hσ => h hσ.1)]
  · rw [sum_rwIdx P R (fun p => if p = p₀ then 3 * (P.card : ℝ) / (8 * C.card) else 0),
      Finset.sum_ite_eq' P p₀, if_pos hp₀]
    have : (0 : ℝ) ≤ R * P.card := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · intro ω hω
    have h' : ((hi + 1 : ℕ) : ℝ) ≤ ((univ.filter (fun w : RWIdx P R =>
        w.1.1 = p₀ ∧ rwSurv C P w.1.1 (ω w))).card : ℝ) := by exact_mod_cast hω
    push_cast at h'
    refine h'.trans ?_
    exact_mod_cast Finset.card_le_card (fun w hw => by rw [mem_filter'] at hw ⊢; exact hw)

/-- The expected number of surviving walks ending at a port is at most `3R|P|/(8m)`. -/
lemma to_le (q₀ : Port V) (hi : ℕ) :
    rwProb C P R ℓ (fun ω => hi < (univ.filter (fun w : RWIdx P R =>
      rwEnd C w.1.1 (ω w) = some q₀)).card) ≤
      Real.exp (2 * (3 * R * P.card / (4 * C.card)) - (hi + 1)) := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  refine rwProb_upper C P R ℓ (fun w σ => rwEnd C w.1.1 σ = some q₀)
    (fun _ => 3 * 1 / (8 * (C.card : ℝ))) ?_ _ _ ?_ _ ?_
  · intro w
    rw [prob_end C ℓ (by omega) w.1.1 {q₀} (fun σ => rwEnd C w.1.1 σ = some q₀)
      (fun σ => by simp)]
    have := mix_surv_le (t := 2 * ℓ - 1) hmix hC (by omega) (startOf_mem (hP w.1.2)) {q₀}
    rwa [card_singleton, Nat.cast_one] at this
  · rw [Finset.sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      nsmul_eq_mul]
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ R * P.card * C.card := by positivity
    nlinarith
  · intro ω hω
    have h' : ((hi + 1 : ℕ) : ℝ) ≤ ((univ.filter (fun w : RWIdx P R =>
        rwEnd C w.1.1 (ω w) = some q₀)).card : ℝ) := by exact_mod_cast hω
    push_cast at h'
    refine h'.trans ?_
    exact_mod_cast Finset.card_le_card (fun w hw => by rw [mem_filter'] at hw ⊢; exact hw)

/-- Every set `A` with `|A| ≤ |P|/2` sends out of `A` surviving walks in expected number at
least `R|A||P|/(16m)`. -/
lemma cut_le (A : Finset (Port V)) (hA : A ⊆ P) (h2 : 2 * A.card ≤ P.card) (L : ℕ) :
    rwProb C P R ℓ (fun ω => (univ.filter (fun w : RWIdx P R => w.1.1 ∈ A ∧
      ∃ q ∈ P \ A, rwEnd C w.1.1 (ω w) = some q)).card < A.card * L) ≤
      Real.exp (A.card * L - (R * A.card * P.card / (16 * C.card)) / 2) := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  refine rwProb_lower C P R ℓ (fun w σ => w.1.1 ∈ A ∧ ∃ q ∈ P \ A, rwEnd C w.1.1 σ = some q)
    (fun w => if w.1.1 ∈ A then (P.card : ℝ) / (16 * C.card) else 0) ?_ _ _ ?_ _ ?_
  · intro w
    split_ifs with h
    · rw [prob_end C ℓ (by omega) w.1.1 (P \ A)
        (fun σ => w.1.1 ∈ A ∧ ∃ q ∈ P \ A, rwEnd C w.1.1 σ = some q) (fun σ => by simp [h])]
      refine le_trans ?_ (mix_surv_ge (t := 2 * ℓ - 1) hmix hC (by omega) (startOf_mem (hP w.1.2)) (P \ A)
        (sdiff_subset.trans hP))
      rw [card_sdiff_of_subset hA]
      have hAP : A.card ≤ P.card := card_le_card hA
      have : (P.card : ℝ) ≤ 2 * ((P.card - A.card : ℕ) : ℝ) := by
        push_cast [hAP]; linarith [show (2 * A.card : ℝ) ≤ P.card by exact_mod_cast h2]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [prob_walk_zero C ℓ (fun σ => w.1.1 ∈ A ∧ ∃ q ∈ P \ A, rwEnd C w.1.1 σ = some q)
        (fun σ hσ => h hσ.1)]
  · rw [sum_rwIdx P R (fun p => if p ∈ A then (P.card : ℝ) / (16 * C.card) else 0),
      Finset.sum_ite_mem, Finset.inter_eq_right.2 hA, Finset.sum_const, nsmul_eq_mul]
    apply le_of_eq; ring
  · intro ω hω
    have h' : ((univ.filter (fun w : RWIdx P R => w.1.1 ∈ A ∧
        ∃ q ∈ P \ A, rwEnd C w.1.1 (ω w) = some q)).card : ℝ) ≤ ((A.card * L : ℕ) : ℝ) := by
      exact_mod_cast hω.le
    push_cast at h'
    refine le_trans ?_ h'
    exact_mod_cast Finset.card_le_card (fun w hw => by rw [mem_filter'] at hw ⊢; exact hw)

/-- The expected number of surviving walks crossing an edge in a given step is at most
`3R|P|/(4m)`. -/
lemma cong_le (e : Sym2 V) (j : ℕ) (hj : j < 2 * ℓ) (hc : ℕ) :
    rwProb C P R ℓ (fun ω => hc < (univ.filter (fun w : RWIdx P R =>
      (∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e)) ∧
        rwSurv C P w.1.1 (ω w))).card) ≤
      Real.exp (2 * (3 * R * P.card / (4 * C.card)) - (hc + 1)) := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  refine rwProb_upper C P R ℓ (fun w σ => (∃ y, (rwTraj C w.1.1 σ)[j + 1]? = some (y, some e)) ∧
    rwSurv C P w.1.1 σ)
    (fun w => if T ≤ j then 3 / (4 * (C.card : ℝ))
      else (∑ z, walkProb C j (startOf w.1.1) z * crossP C z e) * (3 * P.card / (8 * C.card)))
    (fun w => prob_cross_surv_le ℓ hC hP hmix hℓ w.1.1 w.1.2 j hj e _ (fun σ => Iff.rfl))
    _ _ ?_ _ ?_
  · rw [sum_rwIdx P R (fun p => if T ≤ j then 3 / (4 * (C.card : ℝ))
      else (∑ z, walkProb C j (startOf p) z * crossP C z e) * (3 * P.card / (8 * C.card)))]
    by_cases hTj : T ≤ j
    · simp only [if_pos hTj]
      rw [Finset.sum_const, nsmul_eq_mul]
      apply le_of_eq; ring
    · simp only [if_neg hTj]
      rw [← Finset.sum_mul]
      have h1 := sum_ports_cross_le C P hP j e
      have h0 : (0 : ℝ) ≤ 3 * P.card / (8 * C.card) := by positivity
      calc (R : ℝ) * ((∑ p ∈ P, ∑ z, walkProb C j (startOf p) z * crossP C z e) *
            (3 * P.card / (8 * C.card)))
          ≤ R * (1 * (3 * P.card / (8 * C.card))) := by gcongr <;> exact h1
        _ ≤ 3 * R * P.card / (4 * C.card) := by
            rw [one_mul, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            have : (0 : ℝ) ≤ R * P.card * C.card := by positivity
            nlinarith
  · intro ω hω
    have h' : ((hc + 1 : ℕ) : ℝ) ≤ ((univ.filter (fun w : RWIdx P R =>
        (∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e)) ∧
        rwSurv C P w.1.1 (ω w))).card : ℝ) := by exact_mod_cast hω
    push_cast at h'
    refine h'.trans ?_
    exact_mod_cast Finset.card_le_card (fun w hw => by rw [mem_filter'] at hw ⊢; exact hw)

/-- **Claims 3.4/3.5, probabilistic part**: the failure probability of the construction is at
most the sum of the Chernoff bounds of all failure events. -/
theorem rw_fail_le (h2P : 2 ≤ P.card) (t hi hc L φ : ℕ) (hL : 1 ≤ L) (hφ : 2 * hi ≤ φ * L)
    (Good : G0Data → Prop)
    (hGood : Good ⟨P.card, hi * P.card, φ, 2 * hi + 2 * ℓ * hc, 2 * ℓ + 1⟩)
    (y : ℝ) (hy : 0 ≤ y)
    (h1 : Real.exp (2 * R - (t + 1)) ≤ y)
    (h2 : Real.exp (2 * (3 * R * P.card / (4 * C.card)) - (hi + 1)) ≤ y)
    (h3 : Real.exp (2 * (3 * R * P.card / (4 * C.card)) - (hc + 1)) ≤ y)
    (h4 : ∀ A ⊆ P, A.Nonempty →
      Real.exp (A.card * L - (R * A.card * P.card / (16 * C.card)) / 2) ≤ y ^ A.card) :
    rwProb C P R ℓ (fun ω => rwOverflow C P R ℓ t ω ∨ ¬ ∃ g, TrueParams C P R ℓ ω g ∧ Good g) ≤
      ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
        Fintype.card (Sym2 V) * (2 * ℓ) : ℕ) : ℝ) * y +
      ∑ A ∈ P.powerset.filter (fun A => A.Nonempty), y ^ A.card := by
  have hsub : ∀ ω, (rwOverflow C P R ℓ t ω ∨ ¬ ∃ g, TrueParams C P R ℓ ω g ∧ Good g) →
      rwOverflow C P R ℓ t ω ∨ evFrom C P R ℓ hi ω ∨ evTo C P R ℓ hi ω ∨ evCut C P R ℓ L ω ∨
        evCong C P R ℓ hc ω := by
    intro ω h
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨hov, hf, ht, hcu, hg⟩ := hn
    rcases h with h | h
    · exact hov h
    apply h
    refine ⟨_, trueParams_of_good hP h2P hi hc L φ hL hφ ?_ ?_ ?_ ?_, hGood⟩
    · intro p hp; by_contra hc'; exact hf ⟨p, hp, not_le.1 hc'⟩
    · intro q hq; by_contra hc'; exact ht ⟨q, hq, not_le.1 hc'⟩
    · intro A hA hne h2; by_contra hc'
      exact hcu ⟨A, mem_filter.2 ⟨mem_powerset.2 hA, hne, h2⟩, not_le.1 hc'⟩
    · intro e j hj; by_contra hc'
      exact hg ⟨e, mem_univ _, j, mem_range.2 hj, not_le.1 hc'⟩
  refine (rwProb_mono C P R ℓ hsub).trans ((rwProb_or5 C P R ℓ _ _ _ _ _).trans ?_)
  -- overflow
  have hov : rwProb C P R ℓ (rwOverflow C P R ℓ t) ≤
      ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) : ℕ) : ℝ) * y := by
    calc rwProb C P R ℓ (rwOverflow C P R ℓ t)
        ≤ rwProb C P R ℓ (fun ω => ∃ j ∈ range (2 * ℓ), ∃ y' ∈ (univ : Finset V),
            ∃ e ∈ (univ : Finset (Sym2 V)), t < (univ.filter (fun w : RWIdx P R =>
              (rwTraj C w.1.1 (ω w))[j + 1]? = some (y', some e))).card) := by
          apply rwProb_mono
          intro ω h
          unfold rwOverflow at h
          obtain ⟨j, hj, y', e, h⟩ := h
          refine ⟨j, mem_range.2 hj, y', mem_univ _, e, mem_univ _, lt_of_lt_of_le h ?_⟩
          exact Finset.card_le_card (fun w hw => by rw [mem_filter'] at hw ⊢; exact hw)
      _ ≤ ∑ j ∈ range (2 * ℓ), ∑ y' ∈ (univ : Finset V), ∑ e ∈ (univ : Finset (Sym2 V)),
            rwProb C P R ℓ (fun ω => t < (univ.filter (fun w : RWIdx P R =>
              (rwTraj C w.1.1 (ω w))[j + 1]? = some (y', some e))).card) := by
          refine (rwProb_exists C P R ℓ _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
          refine (rwProb_exists C P R ℓ _ _).trans (Finset.sum_le_sum (fun y' _ => ?_))
          exact rwProb_exists C P R ℓ _ _
      _ ≤ ∑ j ∈ range (2 * ℓ), ∑ y' ∈ (univ : Finset V), ∑ e ∈ (univ : Finset (Sym2 V)), y := by
          refine Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun y' _ =>
            Finset.sum_le_sum (fun e _ => ?_)))
          exact (ovf_le R ℓ hC hP hmix hℓ j (mem_range.1 hj) y' e t).trans h1
      _ = _ := by
          simp only [Finset.sum_const, card_range, card_univ, nsmul_eq_mul]
          push_cast; ring
  have hf : rwProb C P R ℓ (evFrom C P R ℓ hi) ≤ (P.card : ℝ) * y := by
    calc rwProb C P R ℓ (evFrom C P R ℓ hi) ≤ ∑ p ∈ P, rwProb C P R ℓ (fun ω => hi <
          (univ.filter (fun w : RWIdx P R => w.1.1 = p ∧ rwSurv C P w.1.1 (ω w))).card) :=
          rwProb_exists C P R ℓ P (fun p ω => hi <
            (univ.filter (fun w : RWIdx P R => w.1.1 = p ∧ rwSurv C P w.1.1 (ω w))).card)
      _ ≤ ∑ p ∈ P, y := Finset.sum_le_sum (fun p hp =>
          (from_le R ℓ hC hP hmix hℓ p hp hi).trans h2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have ht : rwProb C P R ℓ (evTo C P R ℓ hi) ≤ (P.card : ℝ) * y := by
    calc rwProb C P R ℓ (evTo C P R ℓ hi) ≤ ∑ q ∈ P, rwProb C P R ℓ (fun ω => hi < (univ.filter
          (fun w : RWIdx P R => rwEnd C w.1.1 (ω w) = some q)).card) :=
          rwProb_exists C P R ℓ P (fun q ω => hi < (univ.filter
            (fun w : RWIdx P R => rwEnd C w.1.1 (ω w) = some q)).card)
      _ ≤ ∑ q ∈ P, y := Finset.sum_le_sum (fun q _ =>
          (to_le R ℓ hC hP hmix hℓ q hi).trans h2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcu : rwProb C P R ℓ (evCut C P R ℓ L) ≤
      ∑ A ∈ P.powerset.filter (fun A => A.Nonempty), y ^ A.card := by
    calc rwProb C P R ℓ (evCut C P R ℓ L)
        ≤ ∑ A ∈ P.powerset.filter (fun A => A.Nonempty ∧ 2 * A.card ≤ P.card),
          rwProb C P R ℓ (fun ω => (univ.filter (fun w : RWIdx P R => w.1.1 ∈ A ∧
            ∃ q ∈ P \ A, rwEnd C w.1.1 (ω w) = some q)).card < A.card * L) :=
          rwProb_exists C P R ℓ _ (fun A ω => (univ.filter (fun w : RWIdx P R => w.1.1 ∈ A ∧
            ∃ q ∈ P \ A, rwEnd C w.1.1 (ω w) = some q)).card < A.card * L)
      _ ≤ ∑ A ∈ P.powerset.filter (fun A => A.Nonempty ∧ 2 * A.card ≤ P.card), y ^ A.card := by
          refine Finset.sum_le_sum (fun A hA => ?_)
          rw [mem_filter, mem_powerset] at hA
          exact (cut_le R ℓ hC hP hmix hℓ A hA.1 hA.2.2 L).trans (h4 A hA.1 hA.2.1)
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro A hA; rw [mem_filter] at hA ⊢; exact ⟨hA.1, hA.2.1⟩
          · intro A _ _; positivity
  have hg : rwProb C P R ℓ (evCong C P R ℓ hc) ≤
      ((Fintype.card (Sym2 V) * (2 * ℓ) : ℕ) : ℝ) * y := by
    calc rwProb C P R ℓ (evCong C P R ℓ hc) ≤ ∑ e ∈ (univ : Finset (Sym2 V)),
          rwProb C P R ℓ (fun ω => ∃ j ∈ range (2 * ℓ), hc < (univ.filter (fun w : RWIdx P R =>
            (∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e)) ∧
              rwSurv C P w.1.1 (ω w))).card) :=
          rwProb_exists C P R ℓ _ (fun e ω => ∃ j ∈ range (2 * ℓ), hc < (univ.filter
            (fun w : RWIdx P R => (∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e)) ∧
              rwSurv C P w.1.1 (ω w))).card)
      _ ≤ ∑ e ∈ (univ : Finset (Sym2 V)), ∑ j ∈ range (2 * ℓ),
          rwProb C P R ℓ (fun ω => hc < (univ.filter (fun w : RWIdx P R =>
            (∃ y, (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e)) ∧
              rwSurv C P w.1.1 (ω w))).card) :=
          Finset.sum_le_sum (fun e _ => rwProb_exists C P R ℓ _ _)
      _ ≤ ∑ e ∈ (univ : Finset (Sym2 V)), ∑ j ∈ range (2 * ℓ), y :=
          Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun j hj =>
            (cong_le R ℓ hC hP hmix hℓ e j (mem_range.1 hj) hc).trans h3))
      _ = _ := by
          simp only [Finset.sum_const, card_range, card_univ, nsmul_eq_mul]
          push_cast; ring
  have : ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
        Fintype.card (Sym2 V) * (2 * ℓ) : ℕ) : ℝ) * y =
      ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) : ℕ) : ℝ) * y + (P.card : ℝ) * y +
        (P.card : ℝ) * y + ((Fintype.card (Sym2 V) * (2 * ℓ) : ℕ) : ℝ) * y := by
    push_cast; ring
  rw [this]
  linarith

end Model

end APSP.Stoc
