import ApspStoc.G0Model

/-!
# Lazy random walks with seeds: one walk

Facts about a single lazy walk of the model of `G0Model.lean`: expectations over uniform seed lists,
the one-step distribution (the seed step is exactly the lazy random walk step), the Markov property,
stationarity of the degree distribution, and the consequences of the mixing bound for crossing and
survival probabilities.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Expectations over uniform seed lists -/

/-- Expectation of `f` over `k` independent uniform seeds in `[0, D)`. -/
noncomputable def lexp (D k : ℕ) (f : List ℕ → ℝ) : ℝ :=
  (∑ σ : Fin k → Fin D, f (List.ofFn (fun i => (σ i : ℕ)))) / (D : ℝ) ^ k

lemma lexp_zero (D : ℕ) (f : List ℕ → ℝ) : lexp D 0 f = f [] := by
  unfold lexp; simp

lemma lexp_succ (D k : ℕ) (f : List ℕ → ℝ) :
    lexp D (k + 1) f = (∑ r ∈ range D, lexp D k (fun l => f (r :: l))) / D := by
  unfold lexp
  have h1 : ∑ σ : Fin (k + 1) → Fin D, f (List.ofFn (fun i => (σ i : ℕ))) =
      ∑ r : Fin D, ∑ τ : Fin k → Fin D, f ((r : ℕ) :: List.ofFn (fun i => (τ i : ℕ))) := by
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin D)) _ _ (fun x => ?_)
    simp [Fin.consEquiv, List.ofFn_succ]
  rw [h1, pow_succ, ← div_div, Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun r => (∑ τ : Fin k → Fin D,
    f (r :: List.ofFn (fun i => (τ i : ℕ)))) / (D : ℝ) ^ k) D]

lemma lexp_congr {D k : ℕ} {f g : List ℕ → ℝ} (h : ∀ l, l.length = k → f l = g l) :
    lexp D k f = lexp D k g := by
  unfold lexp; congr 1
  exact Finset.sum_congr rfl (fun σ _ => h _ (by simp))

lemma lexp_mono {D k : ℕ} {f g : List ℕ → ℝ} (h : ∀ l, l.length = k → f l ≤ g l) :
    lexp D k f ≤ lexp D k g := by
  unfold lexp
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun σ _ => h _ (by simp))

lemma lexp_nonneg {D k : ℕ} {f : List ℕ → ℝ} (h : ∀ l, 0 ≤ f l) : 0 ≤ lexp D k f := by
  unfold lexp
  exact div_nonneg (Finset.sum_nonneg (fun σ _ => h _)) (by positivity)

lemma lexp_const_mul (D k : ℕ) (c : ℝ) (f : List ℕ → ℝ) :
    lexp D k (fun l => c * f l) = c * lexp D k f := by
  unfold lexp; rw [← Finset.mul_sum, mul_div_assoc]

lemma lexp_const {D : ℕ} (hD : 0 < D) (k : ℕ) (c : ℝ) : lexp D k (fun _ => c) = c := by
  unfold lexp
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  have : (0 : ℝ) < (D : ℝ) ^ k := by positivity
  push_cast; field_simp

/-- Probability of an event of `k` uniform seeds as an expectation. -/
lemma card_filter_div_eq_lexp (D k : ℕ) (Φ : List ℕ → Prop) [DecidablePred Φ] :
    ((univ.filter (fun σ : Fin k → Fin D => Φ (List.ofFn (fun i => (σ i : ℕ))))).card : ℝ) /
      Fintype.card (Fin k → Fin D) = lexp D k (fun l => if Φ l then 1 else 0) := by
  unfold lexp
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, card_filter]
  push_cast; rfl

/-! ## Walks -/

lemma seedRange_eq (C : Finset (Sym2 V)) : seedRange C = 2 * ∏ v, max 1 (degIn C v) := rfl

lemma prod_max_pos (C : Finset (Sym2 V)) : 0 < ∏ v, max 1 (degIn C v) :=
  Finset.prod_pos (fun v _ => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))

lemma seedRange_pos (C : Finset (Sym2 V)) : 0 < seedRange C := by
  rw [seedRange_eq]; have := prod_max_pos C; omega

lemma walkSteps_length (C : Finset (Sym2 V)) (u : V) (l : List ℕ) :
    (walkSteps C u l).length = l.length := by
  induction l generalizing u with
  | nil => rfl
  | cons r rs ih => simp [walkSteps, ih]

lemma walkSteps_cons (C : Finset (Sym2 V)) (u : V) (r : ℕ) (l : List ℕ) :
    walkSteps C u (r :: l) = lazyStep C u r :: walkSteps C (lazyStep C u r).1 l := rfl

lemma walkEnd_cons (C : Finset (Sym2 V)) (u : V) (r : ℕ) (l : List ℕ) :
    walkEnd C u (r :: l) = walkEnd C (lazyStep C u r).1 l := rfl

lemma walkEnd_nil (C : Finset (Sym2 V)) (u : V) : walkEnd C u [] = u := rfl

/-- Expectation of a function of the steps of a `k`-step walk from `u`. -/
noncomputable def wexp (C : Finset (Sym2 V)) (k : ℕ) (u : V)
    (F : List (V × Option (Sym2 V)) → ℝ) : ℝ :=
  lexp (seedRange C) k (fun l => F (walkSteps C u l))

/-- Expectation of a function of one lazy step from `z`. -/
noncomputable def step1 (C : Finset (Sym2 V)) (z : V) (f : V × Option (Sym2 V) → ℝ) : ℝ :=
  (∑ r ∈ range (seedRange C), f (lazyStep C z r)) / seedRange C

lemma wexp_zero (C : Finset (Sym2 V)) (u : V) (F : List (V × Option (Sym2 V)) → ℝ) :
    wexp C 0 u F = F [] := lexp_zero _ _

lemma wexp_succ (C : Finset (Sym2 V)) (k : ℕ) (u : V) (F : List (V × Option (Sym2 V)) → ℝ) :
    wexp C (k + 1) u F = step1 C u (fun st => wexp C k st.1 (fun s => F (st :: s))) := by
  unfold wexp step1; rw [lexp_succ]; rfl

lemma wexp_congr {C : Finset (Sym2 V)} {k : ℕ} {u : V} {F G : List (V × Option (Sym2 V)) → ℝ}
    (h : ∀ s, s.length = k → F s = G s) : wexp C k u F = wexp C k u G := by
  unfold wexp
  exact lexp_congr (fun l hl => h _ (by rw [walkSteps_length, hl]))

lemma wexp_mono {C : Finset (Sym2 V)} {k : ℕ} {u : V} {F G : List (V × Option (Sym2 V)) → ℝ}
    (h : ∀ s, s.length = k → F s ≤ G s) : wexp C k u F ≤ wexp C k u G := by
  unfold wexp
  exact lexp_mono (fun l hl => h _ (by rw [walkSteps_length, hl]))

lemma wexp_nonneg {C : Finset (Sym2 V)} {k : ℕ} {u : V} {F : List (V × Option (Sym2 V)) → ℝ}
    (h : ∀ s, 0 ≤ F s) : 0 ≤ wexp C k u F := lexp_nonneg (fun _ => h _)

lemma wexp_const_mul (C : Finset (Sym2 V)) (k : ℕ) (u : V) (c : ℝ)
    (F : List (V × Option (Sym2 V)) → ℝ) :
    wexp C k u (fun s => c * F s) = c * wexp C k u F := lexp_const_mul _ _ _ _

lemma wexp_const (C : Finset (Sym2 V)) (k : ℕ) (u : V) (c : ℝ) :
    wexp C k u (fun _ => c) = c := lexp_const (seedRange_pos C) _ _

lemma step1_sum_mul (C : Finset (Sym2 V)) (u : V) (g : V → V × Option (Sym2 V) → ℝ)
    (c : V → ℝ) :
    step1 C u (fun st => ∑ z, g z st * c z) = ∑ z, step1 C u (g z) * c z := by
  unfold step1
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.sum_mul, div_mul_eq_mul_div]

/-! ## The one-step distribution -/

lemma sum_range_mul_div (c n : ℕ) (hc : 0 < c) (g : ℕ → ℝ) :
    ∑ x ∈ range (c * n), g (x / c) = c * ∑ i ∈ range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    have : ∀ x ∈ range c, g ((c * n + x) / c) = g n := by
      intro x hx
      rw [Nat.mul_add_div hc, Nat.div_eq_of_lt (mem_range.1 hx), Nat.add_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma sum_range_length_elim {α : Type*} (L : List α) (a : ℝ) (g : α → ℝ) :
    ∑ i ∈ range L.length, (L[i]?).elim a g = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.elim_some]
    rw [ih]

lemma length_incList (C : Finset (Sym2 V)) (z : V) : (incList C z).length = degIn C z := by
  unfold incList degIn; rw [Finset.length_toList]

/-- **The seed step is the lazy random walk step**: from a node `z` of `C`, stay with probability
`1/2`, cross each incident edge with probability `1/(2 deg z)`. -/
lemma step1_formula (C : Finset (Sym2 V)) (z : V) (f : V × Option (Sym2 V) → ℝ)
    (hz : 1 ≤ degIn C z) :
    step1 C z f = f (z, none) / 2 +
      (∑ e ∈ C.filter (fun e => z ∈ e), f (otherEnd e z, some e)) / (2 * degIn C z) := by
  have hQpos : 0 < ∏ v, max 1 (degIn C v) := prod_max_pos C
  obtain ⟨c, hc⟩ : degIn C z ∣ ∏ v, max 1 (degIn C v) := by
    have := Finset.dvd_prod_of_mem (fun v => max 1 (degIn C v)) (Finset.mem_univ z)
    rwa [max_eq_right hz] at this
  have hD : seedRange C = (∏ v, max 1 (degIn C v)) + ∏ v, max 1 (degIn C v) := by
    rw [seedRange_eq]; ring
  have hD2 : seedRange C / 2 = ∏ v, max 1 (degIn C v) := by rw [seedRange_eq]; omega
  generalize hQ : ∏ v, max 1 (degIn C v) = Q at hc hQpos hD hD2
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hc; omega
    · exact h
  have hdiv : seedRange C / 2 / degIn C z = c := by
    rw [hD2, hc, Nat.mul_div_cancel_left c (by omega)]
  unfold step1
  rw [hD, Finset.sum_range_add]
  have h1 : ∀ r ∈ range Q, f (lazyStep C z r) = f (z, none) := by
    intro r hr
    unfold lazyStep
    rw [if_pos (Or.inl (by rw [hD2]; exact mem_range.1 hr))]
  have h2 : ∀ x ∈ range Q, f (lazyStep C z (Q + x)) =
      ((incList C z)[x / c]?).elim (f (z, none)) (fun e => f (otherEnd e z, some e)) := by
    intro x _
    unfold lazyStep
    rw [if_neg (by rw [hD2]; omega), hdiv, hD2, Nat.add_sub_cancel_left]
    cases (incList C z)[x / c]? <;> rfl
  have hsum : ∑ i ∈ range (degIn C z),
      ((incList C z)[i]?).elim (f (z, none)) (fun e => f (otherEnd e z, some e)) =
      ∑ e ∈ C.filter (fun e => z ∈ e), f (otherEnd e z, some e) := by
    have := sum_range_length_elim (incList C z) (f (z, none)) (fun e => f (otherEnd e z, some e))
    rw [length_incList] at this
    rw [this]; unfold incList; rw [Finset.sum_map_toList]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  rw [show Q = c * degIn C z by rw [hc, mul_comm]]
  rw [sum_range_mul_div c (degIn C z) hcpos
    (fun i => ((incList C z)[i]?).elim (f (z, none)) (fun e => f (otherEnd e z, some e))), hsum]
  have hdR : (0 : ℝ) < degIn C z := by exact_mod_cast hz
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  push_cast
  field_simp
  ring

lemma step1_deg0 (C : Finset (Sym2 V)) (z : V) (f : V × Option (Sym2 V) → ℝ)
    (hz : degIn C z = 0) : step1 C z f = f (z, none) := by
  unfold step1
  have : ∀ r ∈ range (seedRange C), f (lazyStep C z r) = f (z, none) := by
    intro r _; unfold lazyStep; rw [if_pos (Or.inr hz)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (0 : ℝ) < seedRange C := by exact_mod_cast seedRange_pos C
  field_simp

lemma filter_mem_eq_empty {C : Finset (Sym2 V)} {z : V} (hz : degIn C z = 0) :
    C.filter (fun e => z ∈ e) = ∅ := by
  unfold degIn at hz; exact Finset.card_eq_zero.1 hz

lemma otherEnd_mem {e : Sym2 V} {v : V} (h : v ∈ e) : otherEnd e v ∈ e := by
  unfold otherEnd; rw [dif_pos h]; exact Sym2.other_mem h

lemma otherEnd_otherEnd {e : Sym2 V} {v : V} (h : v ∈ e) : otherEnd e (otherEnd e v) = v := by
  have h' := otherEnd_mem h
  unfold otherEnd at h' ⊢
  rw [dif_pos h] at h' ⊢
  rw [dif_pos h']
  exact Sym2.other_invol h h'

lemma mem_nodes_of {C : Finset (Sym2 V)} {e : Sym2 V} {v : V} (he : e ∈ C) (hv : v ∈ e) :
    v ∈ nodes C := mem_nodes.2 ⟨e, he, hv⟩

/-- Monotonicity of the one-step expectation, comparing only the reachable outcomes. -/
lemma step1_mono {C : Finset (Sym2 V)} {z : V} {f g : V × Option (Sym2 V) → ℝ}
    (hn : f (z, none) ≤ g (z, none))
    (hs : ∀ e ∈ C, z ∈ e → f (otherEnd e z, some e) ≤ g (otherEnd e z, some e)) :
    step1 C z f ≤ step1 C z g := by
  rcases Nat.eq_zero_or_pos (degIn C z) with h0 | hpos
  · rw [step1_deg0 C z f h0, step1_deg0 C z g h0]; exact hn
  · rw [step1_formula C z f hpos, step1_formula C z g hpos]
    have hdR : (0 : ℝ) < 2 * degIn C z := by
      have : (0 : ℝ) < degIn C z := by exact_mod_cast hpos
      linarith
    gcongr with e he
    rw [mem_filter] at he
    exact hs e he.1 he.2

/-! ## Transition probabilities -/

lemma walkProb_eq (C : Finset (Sym2 V)) (t : ℕ) (u x : V) :
    walkProb C t u x = lexp (seedRange C) t (fun l => if walkEnd C u l = x then 1 else 0) := by
  unfold walkProb lexp
  rw [card_filter]; push_cast; rfl

lemma walkProb_zero (C : Finset (Sym2 V)) (u x : V) :
    walkProb C 0 u x = if u = x then 1 else 0 := by
  rw [walkProb_eq, lexp_zero, walkEnd_nil]

lemma walkProb_succ (C : Finset (Sym2 V)) (t : ℕ) (u x : V) :
    walkProb C (t + 1) u x = step1 C u (fun st => walkProb C t st.1 x) := by
  rw [walkProb_eq, lexp_succ]
  unfold step1
  congr 1
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [walkProb_eq]; rfl

lemma walkProb_nonneg (C : Finset (Sym2 V)) (t : ℕ) (u x : V) : 0 ≤ walkProb C t u x := by
  rw [walkProb_eq]; exact lexp_nonneg (fun l => by split_ifs <;> norm_num)

/-- **Markov property**: if `F` only depends on the steps after step `a`, the walk restarts
from its position after `a` steps. -/
lemma wexp_markov (C : Finset (Sym2 V)) (a b : ℕ) (u : V) (F G : List (V × Option (Sym2 V)) → ℝ)
    (h : ∀ s₁ s₂, s₁.length = a → s₂.length = b → F (s₁ ++ s₂) = G s₂) :
    wexp C (a + b) u F = ∑ z, walkProb C a u z * wexp C b z G := by
  induction a generalizing u F with
  | zero =>
    rw [Nat.zero_add]
    have : wexp C b u F = wexp C b u G := wexp_congr (fun s hs => h [] s rfl hs)
    rw [this]
    simp only [walkProb_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring, wexp_succ]
    have : ∀ st : V × Option (Sym2 V), wexp C (a + b) st.1 (fun s => F (st :: s)) =
        ∑ z, walkProb C a st.1 z * wexp C b z G := by
      intro st
      exact ih st.1 _ (fun s₁ s₂ h1 h2 => by
        rw [← List.cons_append]; exact h (st :: s₁) s₂ (by simp [h1]) h2)
    simp_rw [this]
    rw [step1_sum_mul]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [walkProb_succ]

/-! ## Crossing and survival probabilities -/

/-- Probability that a lazy step from `z` crosses `e`. -/
noncomputable def crossP (C : Finset (Sym2 V)) (z : V) (e : Sym2 V) : ℝ :=
  if e ∈ C ∧ z ∈ e then 1 / (2 * degIn C z) else 0

/-- Probability that a lazy step from `z` enters its new node through a port of `Q`. -/
noncomputable def survP (C : Finset (Sym2 V)) (Q : Finset (Port V)) (z : V) : ℝ :=
  (∑ e ∈ C.filter (fun e => z ∈ e), if (otherEnd e z, e) ∈ Q then (1 : ℝ) else 0) /
    (2 * degIn C z)

lemma crossP_nonneg (C : Finset (Sym2 V)) (z : V) (e : Sym2 V) : 0 ≤ crossP C z e := by
  unfold crossP; split_ifs <;> positivity

lemma survP_nonneg (C : Finset (Sym2 V)) (Q : Finset (Port V)) (z : V) : 0 ≤ survP C Q z := by
  unfold survP
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (by positivity)

lemma step1_cross (C : Finset (Sym2 V)) (z : V) (e : Sym2 V) :
    step1 C z (fun st => if st.2 = some e then 1 else 0) = crossP C z e := by
  rcases Nat.eq_zero_or_pos (degIn C z) with h0 | hpos
  · rw [step1_deg0 C z _ h0]
    unfold crossP
    rw [if_neg (by simp), if_neg]
    rintro ⟨he, hz⟩
    have := degIn_pos (mem_nodes_of he hz); omega
  · rw [step1_formula C z _ hpos]
    simp only [reduceCtorEq, if_false, zero_div, zero_add, Option.some.injEq]
    rw [Finset.sum_ite_eq' (C.filter (fun e => z ∈ e)) e (fun _ => (1 : ℝ))]
    unfold crossP
    simp only [mem_filter]
    split_ifs <;> simp

/-- the port through which a step entered its node (if it moved) -/
def stPort : V × Option (Sym2 V) → Option (Port V)
  | (x, some e) => some (x, e)
  | (_, none) => none

/-- the port through which a list of steps ended (if the last step moved) -/
def lastPort (s : List (V × Option (Sym2 V))) : Option (Port V) := s.getLast?.bind stPort

lemma lastPort_append (s₁ s₂ : List (V × Option (Sym2 V))) (h : s₂ ≠ []) :
    lastPort (s₁ ++ s₂) = lastPort s₂ := by
  unfold lastPort; rw [List.getLast?_append_of_ne_nil _ h]

lemma lastPort_cons (st : V × Option (Sym2 V)) (s : List (V × Option (Sym2 V))) (h : s ≠ []) :
    lastPort (st :: s) = lastPort s := by
  rw [← List.singleton_append, lastPort_append _ _ h]

lemma step1_surv (C : Finset (Sym2 V)) (Q : Finset (Port V)) (z : V) :
    step1 C z (fun st => if ∃ q ∈ Q, stPort st = some q then 1 else 0) = survP C Q z := by
  rcases Nat.eq_zero_or_pos (degIn C z) with h0 | hpos
  · rw [step1_deg0 C z _ h0]
    unfold survP
    rw [filter_mem_eq_empty h0]
    simp [stPort]
  · rw [step1_formula C z _ hpos]
    unfold survP
    simp only [stPort, reduceCtorEq, and_false, exists_false, if_false, zero_div, zero_add,
      Option.some.injEq, exists_eq_right, exists_eq_right']

/-- Probability that step `j < k` of a `k`-step walk from `u` crosses `e`. -/
lemma wexp_cross (C : Finset (Sym2 V)) (k j : ℕ) (hj : j < k) (u : V) (e : Sym2 V) :
    wexp C k u (fun s => if ∃ y, s[j]? = some (y, some e) then 1 else 0) =
      ∑ z, walkProb C j u z * crossP C z e := by
  obtain ⟨b, rfl⟩ : ∃ b, k = j + (b + 1) := ⟨k - j - 1, by omega⟩
  rw [wexp_markov C j (b + 1) u _ (fun s => if ∃ y, s[0]? = some (y, some e) then 1 else 0)]
  · refine Finset.sum_congr rfl (fun z _ => ?_)
    congr 1
    rw [wexp_succ]
    simp only [List.getElem?_cons_zero, Option.some.injEq, wexp_const]
    rw [← step1_cross]
    congr 1; funext st
    congr 1
    apply propext
    constructor
    · rintro ⟨y, rfl⟩; rfl
    · intro h; exact ⟨st.1, by rw [← h]⟩
  · intro s₁ s₂ h1 _
    rw [List.getElem?_append_right (by omega), h1, Nat.sub_self]

/-- Probability that a `k`-step walk (`k ≥ 1`) from `u` ends through a port of `Q`. -/
lemma wexp_surv (C : Finset (Sym2 V)) (k : ℕ) (hk : 1 ≤ k) (u : V) (Q : Finset (Port V)) :
    wexp C k u (fun s => if ∃ q ∈ Q, lastPort s = some q then 1 else 0) =
      ∑ z, walkProb C (k - 1) u z * survP C Q z := by
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  rw [wexp_markov C b 1 u _ (fun s => if ∃ q ∈ Q, lastPort s = some q then 1 else 0)]
  · simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    congr 1
    rw [wexp_succ, ← step1_surv]
    congr 1; funext st
    rw [wexp_zero]
    rfl
  · intro s₁ s₂ _ h2
    rw [lastPort_append _ _ (by intro h; rw [h] at h2; simp at h2)]

/-- Crossing `e` at step `j` and surviving afterwards (the remaining `b ≥ 1` steps). -/
lemma wexp_cross_surv_le (C : Finset (Sym2 V)) (j b : ℕ) (hb : 1 ≤ b) (u : V) (e : Sym2 V)
    (Q : Finset (Port V)) (B : ℝ)
    (hB : ∀ y ∈ nodes C, wexp C b y (fun s => if ∃ q ∈ Q, lastPort s = some q then 1 else 0) ≤ B) :
    wexp C (j + (b + 1)) u (fun s => (if ∃ y, s[j]? = some (y, some e) then 1 else 0) *
        (if ∃ q ∈ Q, lastPort s = some q then 1 else 0)) ≤
      (∑ z, walkProb C j u z * crossP C z e) * B := by
  rw [wexp_markov C j (b + 1) u _ (fun s => (if ∃ y, s[0]? = some (y, some e) then 1 else 0) *
        (if ∃ q ∈ Q, lastPort s = some q then 1 else 0))]
  · rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun z _ => ?_)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (walkProb_nonneg _ _ _ _)
    rw [wexp_succ, ← step1_cross]
    have hrw : ∀ st : V × Option (Sym2 V), wexp C b st.1 (fun s =>
        (if ∃ y, (st :: s)[0]? = some (y, some e) then (1 : ℝ) else 0) *
        (if ∃ q ∈ Q, lastPort (st :: s) = some q then 1 else 0)) =
        (if st.2 = some e then 1 else 0) *
          wexp C b st.1 (fun s => if ∃ q ∈ Q, lastPort s = some q then 1 else 0) := by
      intro st
      rw [← wexp_const_mul]
      apply wexp_congr
      intro s hs
      have hne : s ≠ [] := by intro h; rw [h] at hs; simp at hs; omega
      rw [lastPort_cons _ _ hne]
      congr 2
      simp only [List.getElem?_cons_zero, Option.some.injEq]
      apply propext
      constructor
      · rintro ⟨y, rfl⟩; rfl
      · intro h; exact ⟨st.1, by rw [← h]⟩
    simp_rw [hrw]
    rw [show (step1 C z fun st => if st.2 = some e then (1 : ℝ) else 0) * B =
      step1 C z (fun st => (if st.2 = some e then (1 : ℝ) else 0) * B) by
        unfold step1; rw [Finset.sum_div, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r _ => ?_); ring]
    apply step1_mono
    · simp
    · intro e' he' hz
      apply mul_le_mul_of_nonneg_left _ (by split_ifs <;> norm_num)
      exact hB _ (mem_nodes_of he' (otherEnd_mem hz))
  · intro s₁ s₂ h1 h2
    rw [List.getElem?_append_right (by omega), h1, Nat.sub_self,
      lastPort_append _ _ (by intro h; rw [h] at h2; simp at h2)]

/-! ## Sums over ports -/

lemma sum_allPorts (C : Finset (Sym2 V)) (f : Port V → ℝ) :
    ∑ p ∈ allPorts C, f p = ∑ z ∈ nodes C, ∑ e ∈ C.filter (fun e => z ∈ e), f (z, e) := by
  unfold allPorts portsOf
  rw [Finset.sum_biUnion (fun u _ v _ h => portsAt_disjoint C h)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  unfold portsAt
  rw [Finset.sum_image (fun e _ e' _ h => (Prod.ext_iff.1 h).2)]

lemma sum_allPorts_fst (C : Finset (Sym2 V)) (g : V → ℝ) :
    ∑ p ∈ allPorts C, g p.1 = ∑ z ∈ nodes C, (degIn C z : ℝ) * g z := by
  rw [sum_allPorts]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul]; rfl

lemma mem_allPorts' {C : Finset (Sym2 V)} {p : Port V} :
    p ∈ allPorts C ↔ p.2 ∈ C ∧ p.1 ∈ p.2 := by
  rw [mem_allPorts]
  constructor
  · rintro ⟨_, h⟩; exact ⟨(mem_portsAt.1 h).2.1, (mem_portsAt.1 h).2.2⟩
  · rintro ⟨h1, h2⟩; exact ⟨mem_nodes_of h1 h2, mem_portsAt.2 ⟨rfl, h1, h2⟩⟩

/-- The start map `(v, e) ↦ (other end of e, e)` is an involution of `allPorts C`. -/
lemma sum_allPorts_swap (C : Finset (Sym2 V)) (f : Port V → ℝ) :
    ∑ p ∈ allPorts C, f (otherEnd p.2 p.1, p.2) = ∑ p ∈ allPorts C, f p := by
  apply Finset.sum_nbij' (fun p => (otherEnd p.2 p.1, p.2)) (fun p => (otherEnd p.2 p.1, p.2))
  · intro p hp
    rw [mem_allPorts'] at hp ⊢
    exact ⟨hp.1, otherEnd_mem hp.2⟩
  · intro p hp
    rw [mem_allPorts'] at hp ⊢
    exact ⟨hp.1, otherEnd_mem hp.2⟩
  · intro p hp
    rw [mem_allPorts'] at hp
    simp only [otherEnd_otherEnd hp.2]
  · intro p hp
    rw [mem_allPorts'] at hp
    simp only [otherEnd_otherEnd hp.2]
  · intro p _; rfl

lemma sum_allPorts_indicator (C : Finset (Sym2 V)) (Q : Finset (Port V)) :
    ∑ p ∈ allPorts C, (if p ∈ Q then (1 : ℝ) else 0) ≤ Q.card := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card (fun p hp => (mem_filter.1 hp).2)

lemma sum_allPorts_indicator_eq (C : Finset (Sym2 V)) (Q : Finset (Port V))
    (hQ : Q ⊆ allPorts C) :
    ∑ p ∈ allPorts C, (if p ∈ Q then (1 : ℝ) else 0) = Q.card := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext p; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hQ h, h⟩⟩

/-- `∑_z deg(z) survP(z) = |Q ∩ allPorts|/2`, written for a weight `w z` with
`deg z · c ≤ w z` etc. -/
lemma sum_deg_survP (C : Finset (Sym2 V)) (Q : Finset (Port V)) :
    ∑ z ∈ nodes C, (degIn C z : ℝ) * survP C Q z =
      (∑ p ∈ allPorts C, (if p ∈ Q then (1 : ℝ) else 0)) / 2 := by
  rw [← sum_allPorts_swap, sum_allPorts, Finset.sum_div]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  unfold survP
  have : (0 : ℝ) < degIn C z := by exact_mod_cast degIn_pos hz
  field_simp

lemma card_filter_mem_sym2_le (e : Sym2 V) : (univ.filter (fun z : V => z ∈ e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    calc (univ.filter (fun z : V => z ∈ s(a, b))).card ≤ ({a, b} : Finset V).card := by
          apply Finset.card_le_card
          intro z hz; simp only [mem_filter, Sym2.mem_iff] at hz
          rcases hz.2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two

/-! ## Stationarity -/

/-- **Stationarity**: starting from the degree distribution, the walk stays in it. -/
lemma sum_allPorts_walkProb (C : Finset (Sym2 V)) (j : ℕ) (z : V) :
    ∑ p ∈ allPorts C, walkProb C j p.1 z = degIn C z := by
  induction j generalizing z with
  | zero =>
    have h0 : ∀ p ∈ allPorts C, walkProb C 0 p.1 z = if p.1 = z then 1 else 0 :=
      fun p _ => walkProb_zero C p.1 z
    rw [Finset.sum_congr rfl h0, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← card_portsAt C z]
    congr 2
    ext p
    rw [mem_filter, mem_allPorts', mem_portsAt]
    constructor
    · rintro ⟨⟨h1, h2⟩, rfl⟩; exact ⟨rfl, h1, h2⟩
    · rintro ⟨rfl, h1, h2⟩; exact ⟨⟨h1, h2⟩, rfl⟩
  | succ j ih =>
    have h1 : ∀ p ∈ allPorts C, walkProb C (j + 1) p.1 z = walkProb C j p.1 z / 2 +
        (∑ e ∈ C.filter (fun e => p.1 ∈ e), walkProb C j (otherEnd e p.1) z) /
          (2 * degIn C p.1) := by
      intro p hp
      rw [walkProb_succ, step1_formula C p.1 _ (degIn_pos (mem_allPorts.1 hp).1)]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_div, ih]
    have h2 : ∑ p ∈ allPorts C, (∑ e ∈ C.filter (fun e => p.1 ∈ e),
        walkProb C j (otherEnd e p.1) z) / (2 * degIn C p.1) =
        (∑ p ∈ allPorts C, walkProb C j (otherEnd p.2 p.1) z) / 2 := by
      rw [sum_allPorts_fst C (fun x => (∑ e ∈ C.filter (fun e => x ∈ e),
        walkProb C j (otherEnd e x) z) / (2 * degIn C x)), sum_allPorts, Finset.sum_div]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      dsimp only
      have : (0 : ℝ) < degIn C x := by exact_mod_cast degIn_pos hx
      field_simp
    rw [h2, sum_allPorts_swap C (fun p => walkProb C j p.1 z), ih]
    ring

/-- The expected number of walks (one per port of `P ⊆ allPorts C`) crossing `e` in step `j` is
at most `1`. -/
lemma sum_ports_cross_le (C : Finset (Sym2 V)) (P : Finset (Port V)) (hP : P ⊆ allPorts C)
    (j : ℕ) (e : Sym2 V) :
    ∑ p ∈ P, ∑ z, walkProb C j (otherEnd p.2 p.1) z * crossP C z e ≤ 1 := by
  have hnn : ∀ p : Port V, 0 ≤ ∑ z, walkProb C j (otherEnd p.2 p.1) z * crossP C z e :=
    fun p => Finset.sum_nonneg (fun z _ => mul_nonneg (walkProb_nonneg _ _ _ _)
      (crossP_nonneg _ _ _))
  calc ∑ p ∈ P, ∑ z, walkProb C j (otherEnd p.2 p.1) z * crossP C z e
      ≤ ∑ p ∈ allPorts C, ∑ z, walkProb C j (otherEnd p.2 p.1) z * crossP C z e :=
        Finset.sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => hnn p)
    _ = ∑ z, (degIn C z : ℝ) * crossP C z e := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [← Finset.sum_mul, sum_allPorts_swap C (fun p => walkProb C j p.1 z),
          sum_allPorts_walkProb]
    _ ≤ ∑ z, (if z ∈ e then (1 / 2 : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        unfold crossP
        split_ifs with h1 h2
        · have : (0 : ℝ) < degIn C z := by exact_mod_cast degIn_pos (mem_nodes_of h1.1 h1.2)
          field_simp; rfl
        · exact absurd h1.2 h2
        · simp
        · simp
    _ ≤ 1 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have : ((univ.filter (fun z : V => z ∈ e)).card : ℝ) ≤ 2 := by
          exact_mod_cast card_filter_mem_sym2_le e
        linarith

/-! ## Consequences of mixing -/

/-- The mixing bound at all times `≥ T`. -/
def MixAt (C : Finset (Sym2 V)) (T : ℕ) : Prop :=
  ∀ t, T ≤ t → ∀ u ∈ nodes C, ∀ x ∈ nodes C,
    |walkProb C t u x - (degIn C x : ℝ) / (2 * C.card)| ≤ (degIn C x : ℝ) / (4 * C.card)

lemma MixAt.upper {C : Finset (Sym2 V)} {T : ℕ} (h : MixAt C T) (hC : C.Nonempty) {t : ℕ}
    (ht : T ≤ t) {u x : V} (hu : u ∈ nodes C) (hx : x ∈ nodes C) :
    walkProb C t u x ≤ 3 * (degIn C x : ℝ) / (4 * C.card) := by
  have := (abs_le.1 (h t ht u hu x hx)).2
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have e1 : (degIn C x : ℝ) / (2 * C.card) = 2 * ((degIn C x : ℝ) / (4 * C.card)) := by
    field_simp; ring
  have e2 : 3 * (degIn C x : ℝ) / (4 * C.card) = 3 * ((degIn C x : ℝ) / (4 * C.card)) := by
    ring
  rw [e2]; linarith

lemma MixAt.lower {C : Finset (Sym2 V)} {T : ℕ} (h : MixAt C T) (hC : C.Nonempty) {t : ℕ}
    (ht : T ≤ t) {u x : V} (hu : u ∈ nodes C) (hx : x ∈ nodes C) :
    (degIn C x : ℝ) / (4 * C.card) ≤ walkProb C t u x := by
  have := (abs_le.1 (h t ht u hu x hx)).1
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have e1 : (degIn C x : ℝ) / (2 * C.card) = 2 * ((degIn C x : ℝ) / (4 * C.card)) := by
    field_simp; ring
  linarith

lemma survP_eq_zero {C : Finset (Sym2 V)} (Q : Finset (Port V)) {z : V} (hz : z ∉ nodes C) :
    survP C Q z = 0 := by
  unfold survP; rw [filter_mem_eq_empty (degIn_eq_zero hz)]; simp

lemma crossP_eq_zero {C : Finset (Sym2 V)} {z : V} (e : Sym2 V) (hz : z ∉ nodes C) :
    crossP C z e = 0 := by
  unfold crossP; rw [if_neg]; rintro ⟨h1, h2⟩; exact hz (mem_nodes_of h1 h2)

/-- After mixing, the probability of ending through a port of `Q` is at most `3|Q|/(8m)`. -/
lemma mix_surv_le {C : Finset (Sym2 V)} {T : ℕ} (h : MixAt C T) (hC : C.Nonempty) {t : ℕ}
    (ht : T ≤ t) {u : V} (hu : u ∈ nodes C) (Q : Finset (Port V)) :
    ∑ z, walkProb C t u z * survP C Q z ≤ 3 * (Q.card : ℝ) / (8 * C.card) := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  rw [← Finset.sum_subset (subset_univ (nodes C)) (fun z _ hz => by
    rw [survP_eq_zero Q hz, mul_zero])]
  calc ∑ z ∈ nodes C, walkProb C t u z * survP C Q z
      ≤ ∑ z ∈ nodes C, (3 / (4 * C.card)) * ((degIn C z : ℝ) * survP C Q z) := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (survP_nonneg _ _ _)
        have := h.upper hC ht hu hz
        have e : (3 / (4 * (C.card : ℝ))) * (degIn C z : ℝ) = 3 * (degIn C z : ℝ) / (4 * C.card) :=
          by ring
        rw [e]; exact this
    _ = (3 / (4 * C.card)) * ((∑ p ∈ allPorts C, (if p ∈ Q then (1 : ℝ) else 0)) / 2) := by
        rw [← Finset.mul_sum, sum_deg_survP]
    _ ≤ (3 / (4 * C.card)) * ((Q.card : ℝ) / 2) := by
        gcongr; exact sum_allPorts_indicator C Q
    _ = 3 * (Q.card : ℝ) / (8 * C.card) := by field_simp; ring

/-- After mixing, the probability of ending through a port of `Q ⊆ allPorts C` is at least
`|Q|/(8m)`. -/
lemma mix_surv_ge {C : Finset (Sym2 V)} {T : ℕ} (h : MixAt C T) (hC : C.Nonempty) {t : ℕ}
    (ht : T ≤ t) {u : V} (hu : u ∈ nodes C) (Q : Finset (Port V)) (hQ : Q ⊆ allPorts C) :
    (Q.card : ℝ) / (8 * C.card) ≤ ∑ z, walkProb C t u z * survP C Q z := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  rw [← Finset.sum_subset (subset_univ (nodes C)) (fun z _ hz => by
    rw [survP_eq_zero Q hz, mul_zero])]
  calc (Q.card : ℝ) / (8 * C.card)
      = (1 / (4 * C.card)) * ((∑ p ∈ allPorts C, (if p ∈ Q then (1 : ℝ) else 0)) / 2) := by
        rw [sum_allPorts_indicator_eq C Q hQ]; field_simp; ring
    _ = ∑ z ∈ nodes C, (1 / (4 * C.card)) * ((degIn C z : ℝ) * survP C Q z) := by
        rw [← Finset.mul_sum, sum_deg_survP]
    _ ≤ ∑ z ∈ nodes C, walkProb C t u z * survP C Q z := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (survP_nonneg _ _ _)
        have := h.lower hC ht hu hz
        have e : (1 / (4 * (C.card : ℝ))) * (degIn C z : ℝ) = (degIn C z : ℝ) / (4 * C.card) :=
          by ring
        rw [e]; exact this

/-- After mixing, the probability of crossing `e` in a step is at most `3/(4m)`. -/
lemma mix_cross_le {C : Finset (Sym2 V)} {T : ℕ} (h : MixAt C T) (hC : C.Nonempty) {t : ℕ}
    (ht : T ≤ t) {u : V} (hu : u ∈ nodes C) (e : Sym2 V) :
    ∑ z, walkProb C t u z * crossP C z e ≤ 3 / (4 * C.card) := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  calc ∑ z, walkProb C t u z * crossP C z e
      ≤ ∑ z, (if z ∈ e then (3 : ℝ) / (8 * (C.card : ℝ)) else 0) := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        unfold crossP
        split_ifs with h1 h2
        · have hz := mem_nodes_of h1.1 h1.2
          have hd : (0 : ℝ) < degIn C z := by exact_mod_cast degIn_pos hz
          have := h.upper hC ht hu hz
          calc walkProb C t u z * (1 / (2 * degIn C z))
              ≤ 3 * (degIn C z : ℝ) / (4 * C.card) * (1 / (2 * degIn C z)) := by
                gcongr
            _ = 3 / (8 * C.card) := by field_simp; ring
        · exact absurd h1.2 h2
        · rw [mul_zero]; positivity
        · simp
    _ ≤ 3 / (4 * C.card) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have : ((univ.filter (fun z : V => z ∈ e)).card : ℝ) ≤ 2 := by
          exact_mod_cast card_filter_mem_sym2_le e
        calc ((univ.filter (fun z : V => z ∈ e)).card : ℝ) * (3 / (8 * C.card))
            ≤ 2 * (3 / (8 * C.card)) := by gcongr
          _ = 3 / (4 * C.card) := by field_simp; ring

end APSP.Stoc
