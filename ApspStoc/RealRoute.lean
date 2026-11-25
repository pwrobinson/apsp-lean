import ApspStoc.G0AuxProb

/-!
# Routing in an expander cluster along random-walk bridges

**Theorem (`route_exists`).** Assuming the mixing bound for lazy random walks (`Mixing`), in a
cluster `C` with conductance `≥ 1/φinv` every demand `D` on ports of `C` whose port loads are at
most `lam` can be routed along walks in `C` of length `≤ K (φinv+1)^k lg^k ν` with edge congestion
`≤ K (φinv+1)^k lg^k ν · lam` (`K, k` absolute constants; all copies of a packet share a route).

Proof (the probabilistic method with random-walk bridges):
* Let `T = Km (φinv+1)² lg ν + 1` (so the lazy walk is mixed after `T` steps, `MixAt C T`) and
  `L = 2T`. A *bridge* from `u` to `x` is a seed vector of an `L`-step lazy walk from `u` that ends
  at `x`; bridges exist since `P^L(u,x) ≥ deg x / 4m > 0`. The route of a bridge is the list of
  edges it crosses: a walk in `C` from `u` to `x` of length `≤ L`.
* For a uniform bridge from `u` to `x`, the probability of crossing `e` in step `j` is
  `∑_z P^j(u,z) crossP(z,e) P^{L-j-1}(z',x) / P^L(u,x)` (Markov property). If `j ≥ T` this is
  `≤ (3/2) ∑_{z∈e} P^{L-j-1}(z',x)/deg x` (mixing at step `j`); if `j < T` it is
  `≤ 3 ∑_z P^j(u,z) crossP(z,e)` (mixing of the rest of the walk).
* Summing over the packets (`count ≤ lam`, at most `lam·deg` packets start/end at a node),
  stationarity `∑_p P^j(p.1, z) = deg z` and `∑_x P^t(y,x) = 1` give an expected weighted number
  `≤ 3 lam` of crossings of `e` in step `j`.
* Choose one independent uniform bridge per packet type. The normalized congestion
  `Y_e = ∑_π (count π / lam) · (crossings of e by the bridge of π) / L` is a sum of independent
  `[0,1]`-valued terms with mean `≤ 3`, so `E[exp Y_e] ≤ e^6`; averaging `∑_e exp(Y_e)` over the
  product space gives a choice with `Y_e ≤ 2 lg ν + 6` for every `e` (as `|Sym2 V| ≤ ν² ≤ e^{2 lg ν}`),
  i.e. congestion `≤ lam · L · (2 lg ν + 6)`. Hence `K = 16 (Km + 1)` and `k = 2` work.
-/

namespace APSP.Stoc

open APSP Finset

namespace RouteAux

set_option linter.unusedSectionVars false
set_option linter.deprecated false

section Walks

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The route of a walk -/

lemma lazyStep_cases (C : Finset (Sym2 V)) (v : V) (r : ℕ) :
    lazyStep C v r = (v, none) ∨ ∃ e ∈ C, v ∈ e ∧ lazyStep C v r = (otherEnd e v, some e) := by
  unfold lazyStep
  split_ifs with h
  · left; rfl
  · split
    · rename_i e he
      right
      have hmem : e ∈ incList C v := List.mem_of_getElem? he
      unfold incList at hmem
      rw [Finset.mem_toList, mem_filter] at hmem
      exact ⟨e, hmem.1, hmem.2, rfl⟩
    · left; rfl

lemma otherEnd_spec {e : Sym2 V} {v : V} (h : v ∈ e) : e = s(v, otherEnd e v) := by
  unfold otherEnd; rw [dif_pos h]; exact (Sym2.other_spec h).symm

lemma isEdgeWalk_walkSteps (C : Finset (Sym2 V)) (u : V) (l : List ℕ) :
    IsEdgeWalk ((walkSteps C u l).filterMap Prod.snd) u (walkEnd C u l) := by
  induction l generalizing u with
  | nil => rfl
  | cons r rs ih =>
    rw [walkSteps_cons, walkEnd_cons]
    rcases lazyStep_cases C u r with h | ⟨e, _, hue, h⟩
    · rw [List.filterMap_cons, h]
      exact ih u
    · rw [List.filterMap_cons, h]
      exact ⟨otherEnd e u, otherEnd_spec hue, ih _⟩

lemma walkSteps_edges_mem (C : Finset (Sym2 V)) (u : V) (l : List ℕ) :
    ∀ e ∈ (walkSteps C u l).filterMap Prod.snd, e ∈ C := by
  induction l generalizing u with
  | nil => simp [walkSteps]
  | cons r rs ih =>
    rw [walkSteps_cons]
    rcases lazyStep_cases C u r with h | ⟨e, he, _, h⟩
    · rw [List.filterMap_cons, h]
      exact ih u
    · rw [List.filterMap_cons, h]
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | h'
      · exact he
      · exact ih _ e' h'

lemma length_filterMap_walkSteps_le (C : Finset (Sym2 V)) (u : V) (l : List ℕ) :
    ((walkSteps C u l).filterMap Prod.snd).length ≤ l.length :=
  (List.length_filterMap_le _ _).trans (walkSteps_length C u l).le

/-! ## The end of a list of steps -/

/-- The node reached after a list of steps, starting from `y`. -/
def stepsEnd : V → List (V × Option (Sym2 V)) → V
  | y, [] => y
  | _, a :: s => stepsEnd a.1 s

lemma stepsEnd_walkSteps (C : Finset (Sym2 V)) (u : V) (l : List ℕ) :
    stepsEnd u (walkSteps C u l) = walkEnd C u l := by
  induction l generalizing u with
  | nil => rfl
  | cons r rs ih => rw [walkSteps_cons, walkEnd_cons]; exact ih _

lemma stepsEnd_append (y : V) (s₁ s₂ : List (V × Option (Sym2 V))) :
    stepsEnd y (s₁ ++ s₂) = stepsEnd (stepsEnd y s₁) s₂ := by
  induction s₁ generalizing y with
  | nil => rfl
  | cons a s ih => exact ih a.1

lemma stepsEnd_append_ne_nil (y y' : V) (s₁ s₂ : List (V × Option (Sym2 V))) (h : s₂ ≠ []) :
    stepsEnd y (s₁ ++ s₂) = stepsEnd y' s₂ := by
  rw [stepsEnd_append]
  obtain ⟨a, s, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

lemma wexp_end (C : Finset (Sym2 V)) (b : ℕ) (y x : V) :
    wexp C b y (fun s => if stepsEnd y s = x then 1 else 0) = walkProb C b y x := by
  rw [walkProb_eq]; unfold wexp
  simp only [stepsEnd_walkSteps]

lemma sum_walkProb (C : Finset (Sym2 V)) (t : ℕ) (y : V) : ∑ x, walkProb C t y x = 1 := by
  simp only [walkProb_eq]
  unfold lexp
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (0 : ℝ) < (seedRange C : ℝ) ^ t := by
    have := seedRange_pos C; positivity
  push_cast
  field_simp

/-! ## Crossing an edge and ending at a node -/

lemma step1_cross_mul (C : Finset (Sym2 V)) (z : V) (e : Sym2 V) (g : V → ℝ) :
    step1 C z (fun st => (if st.2 = some e then 1 else 0) * g st.1) =
      crossP C z e * g (otherEnd e z) := by
  rcases Nat.eq_zero_or_pos (degIn C z) with h0 | hpos
  · rw [step1_deg0 C z _ h0]
    unfold crossP
    have : ¬ (e ∈ C ∧ z ∈ e) := by
      rintro ⟨he, hz⟩; have := degIn_pos (mem_nodes_of he hz); omega
    simp [this]
  · rw [step1_formula C z _ hpos]
    simp only [reduceCtorEq, if_false, zero_mul, zero_div, zero_add, Option.some.injEq,
      ite_mul, one_mul]
    rw [Finset.sum_ite_eq' (C.filter (fun e => z ∈ e)) e (fun e' => g (otherEnd e' z))]
    unfold crossP
    simp only [mem_filter]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- Probability that step `j` of a walk of length `j + b + 1` from `u` crosses `e` and the walk
ends at `x`. -/
lemma wexp_cross_end (C : Finset (Sym2 V)) (j b : ℕ) (u x : V) (e : Sym2 V) :
    wexp C (j + (b + 1)) u (fun s => (if ∃ y, s[j]? = some (y, some e) then 1 else 0) *
        (if stepsEnd u s = x then 1 else 0)) =
      ∑ z, walkProb C j u z * (crossP C z e * walkProb C b (otherEnd e z) x) := by
  rw [wexp_markov C j (b + 1) u _ (fun s => (if ∃ y, s[0]? = some (y, some e) then 1 else 0) *
    (if stepsEnd u s = x then 1 else 0))]
  · refine Finset.sum_congr rfl (fun z _ => ?_)
    congr 1
    rw [wexp_succ]
    have : ∀ st : V × Option (Sym2 V), wexp C b st.1 (fun s =>
        (if ∃ y, (st :: s)[0]? = some (y, some e) then (1 : ℝ) else 0) *
          (if stepsEnd u (st :: s) = x then 1 else 0)) =
        (if st.2 = some e then 1 else 0) * walkProb C b st.1 x := by
      intro st
      rw [← wexp_end, ← wexp_const_mul]
      apply wexp_congr
      intro s _
      congr 2
      simp only [List.getElem?_cons_zero, Option.some.injEq]
      apply propext
      constructor
      · rintro ⟨y, rfl⟩; rfl
      · intro h; exact ⟨st.1, by rw [← h]⟩
    simp_rw [this]
    exact step1_cross_mul C z e (fun y => walkProb C b y x)
  · intro s₁ s₂ h1 h2
    rw [List.getElem?_append_right (by omega), h1, Nat.sub_self,
      stepsEnd_append_ne_nil u u s₁ s₂ (by intro h; rw [h] at h2; simp at h2)]

/-- The route of a walk from `u` with seeds `s`: the edges it crosses. -/
noncomputable def wpath (C : Finset (Sym2 V)) (u : V) {L : ℕ} (s : Fin L → Fin (seedRange C)) :
    List (Sym2 V) :=
  (walkSteps C u (List.ofFn (fun i => (s i : ℕ)))).filterMap Prod.snd

/-- The bridges from `u` to `x`: seed vectors of walks of length `L` from `u` ending at `x`. -/
noncomputable def bridge (C : Finset (Sym2 V)) (L : ℕ) (u x : V) :
    Finset (Fin L → Fin (seedRange C)) :=
  univ.filter (fun s => walkEnd C u (List.ofFn (fun i => (s i : ℕ))) = x)

/-- Indicator that step `j` crosses `e` and the walk from `u` ends at `x`. -/
noncomputable def crossEnd (j : ℕ) (e : Sym2 V) (u x : V) (s : List (V × Option (Sym2 V))) : ℝ :=
  (if ∃ y, s[j]? = some (y, some e) then 1 else 0) * (if stepsEnd u s = x then 1 else 0)

lemma wpath_walk (C : Finset (Sym2 V)) (L : ℕ) (u x : V) {s : Fin L → Fin (seedRange C)}
    (hs : s ∈ bridge C L u x) : IsEdgeWalk (wpath C u s) u x := by
  unfold bridge at hs
  rw [mem_filter] at hs
  rw [← hs.2]
  exact isEdgeWalk_walkSteps C u _

lemma wpath_mem (C : Finset (Sym2 V)) (u : V) {L : ℕ} (s : Fin L → Fin (seedRange C)) :
    ∀ e ∈ wpath C u s, e ∈ C := walkSteps_edges_mem C u _

lemma wpath_length (C : Finset (Sym2 V)) (u : V) {L : ℕ} (s : Fin L → Fin (seedRange C)) :
    (wpath C u s).length ≤ L := by
  have := length_filterMap_walkSteps_le C u (List.ofFn (fun i => (s i : ℕ)))
  rwa [List.length_ofFn] at this

lemma card_bridge (C : Finset (Sym2 V)) (L : ℕ) (u x : V) :
    ((bridge C L u x).card : ℝ) = (seedRange C : ℝ) ^ L * walkProb C L u x := by
  rw [walkProb_eq]
  unfold lexp bridge
  rw [card_filter]
  have : (0 : ℝ) < (seedRange C : ℝ) ^ L := by have := seedRange_pos C; positivity
  push_cast
  field_simp

lemma sum_bridge_count (C : Finset (Sym2 V)) (L : ℕ) (u x : V) (e : Sym2 V) :
    ∑ s ∈ bridge C L u x, ((wpath C u s).count e : ℝ) =
      (seedRange C : ℝ) ^ L * ∑ j ∈ range L, wexp C L u (crossEnd j e u x) := by
  have hpos : (0 : ℝ) < (seedRange C : ℝ) ^ L := by have := seedRange_pos C; positivity
  unfold bridge wexp lexp
  rw [Finset.sum_filter, ← Finset.sum_div, Finset.sum_comm, mul_div_cancel₀ _ hpos.ne']
  refine Finset.sum_congr rfl (fun s _ => ?_)
  unfold wpath
  rw [count_filterMap_snd, walkSteps_length, List.length_ofFn]
  unfold crossEnd
  simp only [stepsEnd_walkSteps]
  split_ifs with h
  · push_cast; simp
  · simp

/-! ## The bound on the crossing fractions -/

/-- The bound for the fraction of bridges from `u` to `x` (of length `2T`) crossing `e` in step
`j`. -/
noncomputable def crossBnd (C : Finset (Sym2 V)) (T j : ℕ) (e : Sym2 V) (u x : V) : ℝ :=
  if T ≤ j then ∑ z, (if z ∈ e then 3 / 2 * walkProb C (2 * T - j - 1) (otherEnd e z) x /
    degIn C x else 0)
  else 3 * ∑ z, walkProb C j u z * crossP C z e

lemma crossBnd_nonneg (C : Finset (Sym2 V)) (T j : ℕ) (e : Sym2 V) (u x : V) :
    0 ≤ crossBnd C T j e u x := by
  unfold crossBnd
  split_ifs
  · refine Finset.sum_nonneg (fun z _ => ?_)
    split_ifs
    · have := walkProb_nonneg C (2 * T - j - 1) (otherEnd e z) x; positivity
    · exact le_rfl
  · have : 0 ≤ ∑ z, walkProb C j u z * crossP C z e :=
      Finset.sum_nonneg (fun z _ => mul_nonneg (walkProb_nonneg _ _ _ _) (crossP_nonneg _ _ _))
    linarith

lemma crossP_pos_mem {C : Finset (Sym2 V)} {z : V} {e : Sym2 V} (h : crossP C z e ≠ 0) :
    e ∈ C ∧ z ∈ e := by
  unfold crossP at h
  by_contra h'
  exact h (if_neg h')

lemma crossP_eq {C : Finset (Sym2 V)} {z : V} {e : Sym2 V} (h : e ∈ C ∧ z ∈ e) :
    crossP C z e = 1 / (2 * degIn C z) := by
  unfold crossP; rw [if_pos h]

lemma alg_route1 (a m : ℝ) (ha : 0 < a) (hm : 0 < m) :
    3 * a / (4 * m) * (1 / (2 * a)) = 3 / (8 * m) := by
  field_simp; ring

lemma alg_route2 (P a m : ℝ) (ha : 0 < a) (hm : 0 < m) :
    3 / (8 * m) * P = 3 / 2 * P / a * (a / (4 * m)) := by
  field_simp; ring

lemma alg_route3 (w c a m : ℝ) :
    w * (c * (3 * a / (4 * m))) = 3 * (w * c) * (a / (4 * m)) := by
  ring

section Mix

variable {C : Finset (Sym2 V)} {T : ℕ} (hC : C.Nonempty) (hmix : MixAt C T)
include hC hmix

lemma cross_end_le {u x : V} (hu : u ∈ nodes C) (hx : x ∈ nodes C) (j : ℕ) (hj : j < 2 * T)
    (e : Sym2 V) :
    wexp C (2 * T) u (crossEnd j e u x) ≤ crossBnd C T j e u x * walkProb C (2 * T) u x := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hdx : (0 : ℝ) < degIn C x := by exact_mod_cast degIn_pos hx
  have hW : (degIn C x : ℝ) / (4 * C.card) ≤ walkProb C (2 * T) u x :=
    hmix.lower hC (by omega) hu hx
  obtain ⟨b, hb⟩ : ∃ b, 2 * T = j + (b + 1) := ⟨2 * T - j - 1, by omega⟩
  have hb' : 2 * T - j - 1 = b := by omega
  have hw : wexp C (2 * T) u (crossEnd j e u x) =
      ∑ z, walkProb C j u z * (crossP C z e * walkProb C b (otherEnd e z) x) := by
    rw [hb]; exact wexp_cross_end C j b u x e
  rw [hw]
  have hbnn := crossBnd_nonneg C T j e u x
  unfold crossBnd
  rw [hb']
  split_ifs with hTj
  · -- the walk is mixed at step `j`
    calc ∑ z, walkProb C j u z * (crossP C z e * walkProb C b (otherEnd e z) x)
        ≤ ∑ z, (if z ∈ e then 3 / (8 * (C.card : ℝ)) * walkProb C b (otherEnd e z) x else 0) := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          by_cases hc : crossP C z e = 0
          · rw [hc, zero_mul, mul_zero]
            split_ifs
            · exact mul_nonneg (div_pos (by norm_num) (mul_pos (by norm_num) hm)).le
                (walkProb_nonneg C b (otherEnd e z) x)
            · exact le_rfl
          · have hez := crossP_pos_mem hc
            have hz := mem_nodes_of hez.1 hez.2
            have hdz : (0 : ℝ) < degIn C z := by exact_mod_cast degIn_pos hz
            rw [if_pos hez.2, crossP_eq hez, ← mul_assoc]
            apply mul_le_mul_of_nonneg_right _ (walkProb_nonneg _ _ _ _)
            have := hmix.upper hC hTj hu hz
            calc walkProb C j u z * (1 / (2 * degIn C z))
                ≤ 3 * (degIn C z : ℝ) / (4 * C.card) * (1 / (2 * degIn C z)) := by gcongr
              _ = 3 / (8 * C.card) := alg_route1 _ _ hdz hm
      _ = (∑ z, (if z ∈ e then 3 / 2 * walkProb C b (otherEnd e z) x / degIn C x else 0)) *
            ((degIn C x : ℝ) / (4 * C.card)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          split_ifs
          · exact alg_route2 _ _ _ hdx hm
          · simp
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left hW
          refine Finset.sum_nonneg (fun z _ => ?_)
          split_ifs
          · have := walkProb_nonneg C b (otherEnd e z) x
            exact div_nonneg (mul_nonneg (by norm_num) this) hdx.le
          · exact le_rfl
  · -- the rest of the walk mixes
    have hTb : T ≤ b := by omega
    calc ∑ z, walkProb C j u z * (crossP C z e * walkProb C b (otherEnd e z) x)
        ≤ ∑ z, walkProb C j u z * (crossP C z e * (3 * (degIn C x : ℝ) / (4 * C.card))) := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          apply mul_le_mul_of_nonneg_left _ (walkProb_nonneg _ _ _ _)
          by_cases hc : crossP C z e = 0
          · rw [hc, zero_mul, zero_mul]
          · have hez := crossP_pos_mem hc
            apply mul_le_mul_of_nonneg_left _ (crossP_nonneg _ _ _)
            exact hmix.upper hC hTb (mem_nodes_of hez.1 (otherEnd_mem hez.2)) hx
      _ = (3 * ∑ z, walkProb C j u z * crossP C z e) * ((degIn C x : ℝ) / (4 * C.card)) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          exact alg_route3 _ _ _ _
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left hW
          have : 0 ≤ ∑ z, walkProb C j u z * crossP C z e :=
            Finset.sum_nonneg (fun z _ => mul_nonneg (walkProb_nonneg _ _ _ _)
              (crossP_nonneg _ _ _))
          linarith

end Mix

/-! ## Sums over the packets of a demand -/

lemma count_le_load (D : Demand V) (π : Port V × Port V) : D.count π ≤ D.load π.1 := by
  unfold Demand.load
  rw [Multiset.count_eq_card_filter_eq]
  calc (D.filter (fun x => π = x)).card ≤ (D.filter (fun pq => pq.1 = π.1)).card :=
        Multiset.card_le_card (Multiset.monotone_filter_right D (fun pq h => by rw [← h]))
    _ ≤ _ := Nat.le_add_right _ _

lemma sum_count_fst_le (D : Demand V) (A : Finset (Port V)) (lam : ℕ)
    (hA : ∀ pq ∈ D, pq.1 ∈ A) (hl : ∀ p, D.load p ≤ lam) (g : Port V → ℝ)
    (hg : ∀ p, 0 ≤ g p) :
    ∑ π ∈ D.toFinset, (D.count π : ℝ) * g π.1 ≤ lam * ∑ p ∈ A, g p := by
  have h1 : ∑ π ∈ D.toFinset, (D.count π : ℝ) * g π.1 = ((D.map Prod.fst).map g).sum := by
    rw [Multiset.map_map, Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul, Function.comp]
  rw [h1, Finset.sum_multiset_map_count]
  calc ∑ p ∈ (D.map Prod.fst).toFinset, (D.map Prod.fst).count p • g p
      ≤ ∑ p ∈ (D.map Prod.fst).toFinset, (lam : ℝ) * g p := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (hg p)
        have : (D.map Prod.fst).count p ≤ lam := by
          rw [Multiset.count_map]
          refine le_trans ?_ (hl p)
          unfold Demand.load
          refine le_trans (le_of_eq ?_) (Nat.le_add_right _ _)
          congr 1
          exact Multiset.filter_congr (fun pq _ => eq_comm)
        exact_mod_cast this
    _ ≤ ∑ p ∈ A, (lam : ℝ) * g p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Multiset.mem_toFinset, Multiset.mem_map] at hp
          obtain ⟨pq, hpq, rfl⟩ := hp
          exact hA pq hpq
        · intro p _ _; have := hg p; positivity
    _ = lam * ∑ p ∈ A, g p := by rw [Finset.mul_sum]

lemma sum_count_snd_le (D : Demand V) (A : Finset (Port V)) (lam : ℕ)
    (hA : ∀ pq ∈ D, pq.2 ∈ A) (hl : ∀ p, D.load p ≤ lam) (g : Port V → ℝ)
    (hg : ∀ p, 0 ≤ g p) :
    ∑ π ∈ D.toFinset, (D.count π : ℝ) * g π.2 ≤ lam * ∑ p ∈ A, g p := by
  have h1 : ∑ π ∈ D.toFinset, (D.count π : ℝ) * g π.2 = ((D.map Prod.snd).map g).sum := by
    rw [Multiset.map_map, Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul, Function.comp]
  rw [h1, Finset.sum_multiset_map_count]
  calc ∑ p ∈ (D.map Prod.snd).toFinset, (D.map Prod.snd).count p • g p
      ≤ ∑ p ∈ (D.map Prod.snd).toFinset, (lam : ℝ) * g p := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (hg p)
        have : (D.map Prod.snd).count p ≤ lam := by
          rw [Multiset.count_map]
          refine le_trans ?_ (hl p)
          unfold Demand.load
          refine le_trans (le_of_eq ?_) (Nat.le_add_left _ _)
          congr 1
          exact Multiset.filter_congr (fun pq _ => eq_comm)
        exact_mod_cast this
    _ ≤ ∑ p ∈ A, (lam : ℝ) * g p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Multiset.mem_toFinset, Multiset.mem_map] at hp
          obtain ⟨pq, hpq, rfl⟩ := hp
          exact hA pq hpq
        · intro p _ _; have := hg p; positivity
    _ = lam * ∑ p ∈ A, g p := by rw [Finset.mul_sum]

/-- The packets of a demand with port loads `≤ lam` cross every edge in every step with
expected (weighted) number at most `3 lam`. -/
lemma sum_count_crossBnd_le (C : Finset (Sym2 V)) (D : Demand V) (lam T j : ℕ) (e : Sym2 V)
    (hD : ∀ pq ∈ D, pq.1 ∈ allPorts C ∧ pq.2 ∈ allPorts C) (hl : ∀ p, D.load p ≤ lam) :
    ∑ π ∈ D.toFinset, (D.count π : ℝ) * crossBnd C T j e π.1.1 π.2.1 ≤ 3 * lam := by
  unfold crossBnd
  split_ifs with hTj
  · set b := 2 * T - j - 1
    have h1 : ∑ π ∈ D.toFinset, (D.count π : ℝ) * ∑ z, (if z ∈ e then 3 / 2 *
          walkProb C b (otherEnd e z) π.2.1 / degIn C π.2.1 else 0) =
        ∑ z, (if z ∈ e then (3 / 2) * ∑ π ∈ D.toFinset, (D.count π : ℝ) *
          (walkProb C b (otherEnd e z) π.2.1 / degIn C π.2.1) else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      split_ifs
      · refine Finset.sum_congr rfl (fun π _ => ?_)
        ring
      · simp
    rw [h1]
    calc ∑ z, (if z ∈ e then (3 / 2) * ∑ π ∈ D.toFinset, (D.count π : ℝ) *
          (walkProb C b (otherEnd e z) π.2.1 / degIn C π.2.1) else 0)
        ≤ ∑ z, (if z ∈ e then (3 / 2) * (lam : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          split_ifs
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have hg : ∀ q : Port V, 0 ≤ walkProb C b (otherEnd e z) q.1 / degIn C q.1 := by
              intro q; have := walkProb_nonneg C b (otherEnd e z) q.1; positivity
            refine (sum_count_snd_le D (allPorts C) lam (fun pq h => (hD pq h).2) hl _ hg).trans ?_
            rw [sum_allPorts_fst C (fun x => walkProb C b (otherEnd e z) x / degIn C x)]
            have h2 : ∑ x ∈ nodes C, (degIn C x : ℝ) * (walkProb C b (otherEnd e z) x /
                degIn C x) = ∑ x ∈ nodes C, walkProb C b (otherEnd e z) x := by
              refine Finset.sum_congr rfl (fun x hx => ?_)
              have : (0 : ℝ) < degIn C x := by exact_mod_cast degIn_pos hx
              exact mul_div_cancel₀ _ this.ne'
            rw [h2]
            have h3 : ∑ x ∈ nodes C, walkProb C b (otherEnd e z) x ≤ 1 := by
              rw [← sum_walkProb C b (otherEnd e z)]
              exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
                (fun x _ _ => walkProb_nonneg _ _ _ _)
            have : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
            nlinarith
          · exact le_rfl
      _ ≤ 3 * lam := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have : ((univ.filter (fun z : V => z ∈ e)).card : ℝ) ≤ 2 := by
            exact_mod_cast card_filter_mem_sym2_le e
          have : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
          nlinarith
  · have hg : ∀ p : Port V, 0 ≤ 3 * ∑ z, walkProb C j p.1 z * crossP C z e := by
      intro p
      have : 0 ≤ ∑ z, walkProb C j p.1 z * crossP C z e :=
        Finset.sum_nonneg (fun z _ => mul_nonneg (walkProb_nonneg _ _ _ _) (crossP_nonneg _ _ _))
      linarith
    refine (sum_count_fst_le D (allPorts C) lam (fun pq h => (hD pq h).1) hl
      (fun p => 3 * ∑ z, walkProb C j p.1 z * crossP C z e) hg).trans ?_
    rw [← Finset.mul_sum]
    have h1 := sum_ports_cross_le C (allPorts C) subset_rfl j e
    rw [sum_allPorts_swap C (fun p => ∑ z, walkProb C j p.1 z * crossP C z e)] at h1
    have : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
    nlinarith

end Walks

section Exp

/-! ## Exponential moments on product spaces -/

lemma exp_le_one_add_two_mul {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : Real.exp a ≤ 1 + 2 * a := by
  have := Real.abs_exp_sub_one_sub_id_le (x := a) (by rw [abs_of_nonneg h0]; exact h1)
  have h2 := (abs_le.1 this).2
  nlinarith

lemma sum_exp_le_card_mul {κ : Type*} (t : Finset κ) (a : κ → ℝ)
    (ha : ∀ s ∈ t, 0 ≤ a s ∧ a s ≤ 1) :
    ∑ s ∈ t, Real.exp (a s) ≤ t.card * Real.exp (2 * (∑ s ∈ t, a s) / t.card) := by
  rcases t.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < t.card := by exact_mod_cast hne.card_pos
  calc ∑ s ∈ t, Real.exp (a s) ≤ ∑ s ∈ t, (1 + 2 * a s) :=
        Finset.sum_le_sum (fun s hs => exp_le_one_add_two_mul (ha s hs).1 (ha s hs).2)
    _ = t.card * (1 + 2 * (∑ s ∈ t, a s) / t.card) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
        field_simp
    _ ≤ t.card * Real.exp (2 * (∑ s ∈ t, a s) / t.card) := by
        gcongr; linarith [Real.add_one_le_exp (2 * (∑ s ∈ t, a s) / t.card)]

/-- **Exponential moment bound** for a sum of independent `[0,1]`-valued variables, each uniform
on a finite set: `E[exp(∑ Xᵢ)] ≤ exp(2 ∑ E[Xᵢ])`. -/
lemma sum_piFinset_exp_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] (t : ι → Finset κ)
    (a : ι → κ → ℝ) (ha : ∀ i, ∀ s ∈ t i, 0 ≤ a i s ∧ a i s ≤ 1) :
    ∑ ω ∈ Fintype.piFinset t, Real.exp (∑ i, a i (ω i)) ≤
      (Fintype.piFinset t).card * Real.exp (∑ i, 2 * (∑ s ∈ t i, a i s) / (t i).card) := by
  simp_rw [Real.exp_sum]
  rw [← Finset.prod_univ_sum (fun i => t i) (fun i s => Real.exp (a i s)), Fintype.card_piFinset]
  push_cast
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun s _ => (Real.exp_pos _).le))
    (fun i _ => sum_exp_le_card_mul (t i) (a i) (ha i))


end Exp

section Core

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Choosing the bridges -/


/-- The fraction of bridges of a packet crossing an edge, summed over the steps, is at most the
sum of the bounds `crossBnd`. -/
lemma bridge_avg_le {C : Finset (Sym2 V)} {T : ℕ} (hC : C.Nonempty) (hmix : MixAt C T)
    {u x : V} (hu : u ∈ nodes C) (hx : x ∈ nodes C) (e : Sym2 V) :
    (∑ s ∈ bridge C (2 * T) u x, ((wpath C u s).count e : ℝ)) / (bridge C (2 * T) u x).card ≤
      ∑ j ∈ range (2 * T), crossBnd C T j e u x := by
  have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hdx : (0 : ℝ) < degIn C x := by exact_mod_cast degIn_pos hx
  have hW : (degIn C x : ℝ) / (4 * C.card) ≤ walkProb C (2 * T) u x :=
    hmix.lower hC (by omega) hu hx
  have hWpos : 0 < walkProb C (2 * T) u x := lt_of_lt_of_le (by positivity) hW
  have hS : (0 : ℝ) < (seedRange C : ℝ) ^ (2 * T) := by have := seedRange_pos C; positivity
  rw [sum_bridge_count, card_bridge, mul_div_mul_left _ _ hS.ne', div_le_iff₀ hWpos,
    Finset.sum_mul]
  exact Finset.sum_le_sum (fun j hj => cross_end_le hC hmix hu hx j (mem_range.1 hj) e)

/-- **Core of the routing theorem**: with a mixing time `T ≥ 1` and `|Sym2 V| ≤ e^Λ`, every demand
with port loads `≤ lam` between ports of `C` has routes along walks of length `≤ 2T` in `C` with
congestion `≤ lam · 2T · (Λ + 6)`. -/
theorem route_core (C : Finset (Sym2 V)) (D : Demand V) (lam T : ℕ) (hC : C.Nonempty)
    (hmix : MixAt C T) (hD : ∀ pq ∈ D, pq.1 ∈ allPorts C ∧ pq.2 ∈ allPorts C)
    (hl : ∀ p, D.load p ≤ lam) (hlam : 1 ≤ lam) (hT : 1 ≤ T) (Λ : ℝ)
    (hΛ : (Fintype.card (Sym2 V) : ℝ) ≤ Real.exp Λ) :
    ∃ r : Routes V, (∀ pq ∈ D, IsEdgeWalk (r pq) pq.1.1 pq.2.1) ∧
      (∀ pq ∈ D, ∀ e ∈ r pq, e ∈ C) ∧ (∀ pq ∈ D, (r pq).length ≤ 2 * T) ∧
      ∀ e, (((D.map (fun pq => (r pq).count e)).sum : ℕ) : ℝ) ≤ lam * (2 * T) * (Λ + 6) := by
  classical
  set L := 2 * T with hL
  have hLpos : (0 : ℝ) < L := by rw [hL]; push_cast; have : (1 : ℝ) ≤ T := by exact_mod_cast hT
                                 linarith
  have hlamR : (0 : ℝ) < lam := by exact_mod_cast hlam
  -- the index set: the packet types
  let ι := {π // π ∈ D.toFinset}
  have hmemD : ∀ i : ι, i.1 ∈ D := fun i => Multiset.mem_toFinset.1 i.2
  have hu : ∀ i : ι, i.1.1.1 ∈ nodes C := fun i => (mem_allPorts.1 (hD _ (hmemD i)).1).1
  have hx : ∀ i : ι, i.1.2.1 ∈ nodes C := fun i => (mem_allPorts.1 (hD _ (hmemD i)).2).1
  let t : ι → Finset (Fin L → Fin (seedRange C)) := fun i => bridge C L i.1.1.1 i.1.2.1
  have ht : ∀ i, (t i).Nonempty := by
    intro i
    rw [← Finset.card_pos]
    have hm : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
    have hdx : (0 : ℝ) < degIn C i.1.2.1 := by exact_mod_cast degIn_pos (hx i)
    have hW : (degIn C i.1.2.1 : ℝ) / (4 * C.card) ≤ walkProb C L i.1.1.1 i.1.2.1 :=
      hmix.lower hC (by omega) (hu i) (hx i)
    have hS : (0 : ℝ) < (seedRange C : ℝ) ^ L := by have := seedRange_pos C; positivity
    have : (0 : ℝ) < (t i).card := by
      show (0 : ℝ) < ((bridge C L i.1.1.1 i.1.2.1).card : ℝ)
      rw [card_bridge]
      exact mul_pos hS (lt_of_lt_of_le (by positivity) hW)
    exact_mod_cast this
  -- the normalized crossing counts
  let a : Sym2 V → ι → (Fin L → Fin (seedRange C)) → ℝ := fun e i s =>
    ((D.count i.1 : ℝ) / lam) * (((wpath C i.1.1.1 s).count e : ℝ) / L)
  have ha : ∀ e i, ∀ s ∈ t i, 0 ≤ a e i s ∧ a e i s ≤ 1 := by
    intro e i s _
    have h1 : (D.count i.1 : ℝ) ≤ lam := by
      exact_mod_cast (count_le_load D i.1).trans (hl _)
    have h2 : ((wpath C i.1.1.1 s).count e : ℝ) ≤ L := by
      exact_mod_cast (List.count_le_length).trans (wpath_length C i.1.1.1 s)
    have h1' : (D.count i.1 : ℝ) / lam ≤ 1 := (div_le_one hlamR).2 h1
    have h2' : ((wpath C i.1.1.1 s).count e : ℝ) / L ≤ 1 := (div_le_one hLpos).2 h2
    refine ⟨by positivity, ?_⟩
    exact mul_le_one₀ h1' (by positivity) h2'
  -- the expectation bound
  have hexp : ∀ e, ∑ i, 2 * (∑ s ∈ t i, a e i s) / (t i).card ≤ 6 := by
    intro e
    have h1 : ∀ i : ι, 2 * (∑ s ∈ t i, a e i s) / (t i).card ≤
        2 / (lam * L) * ((D.count i.1 : ℝ) * ∑ j ∈ range L, crossBnd C T j e i.1.1.1 i.1.2.1) := by
      intro i
      have hsum : ∑ s ∈ t i, a e i s = (D.count i.1 : ℝ) / lam / L *
          ∑ s ∈ t i, ((wpath C i.1.1.1 s).count e : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [a]; ring
      have hav := bridge_avg_le hC hmix (hu i) (hx i) e
      have hc0 : (0 : ℝ) ≤ (D.count i.1 : ℝ) / lam / L := by positivity
      calc 2 * (∑ s ∈ t i, a e i s) / (t i).card
          = 2 * ((D.count i.1 : ℝ) / lam / L) * ((∑ s ∈ t i, ((wpath C i.1.1.1 s).count e : ℝ)) /
              (t i).card) := by rw [hsum]; ring
        _ ≤ 2 * ((D.count i.1 : ℝ) / lam / L) * ∑ j ∈ range L, crossBnd C T j e i.1.1.1 i.1.2.1 :=
            mul_le_mul_of_nonneg_left hav (by positivity)
        _ = _ := by field_simp
    refine (Finset.sum_le_sum (fun i _ => h1 i)).trans ?_
    rw [← Finset.mul_sum]
    have h2 : ∑ i : ι, (D.count i.1 : ℝ) * ∑ j ∈ range L, crossBnd C T j e i.1.1.1 i.1.2.1 =
        ∑ j ∈ range L, ∑ π ∈ D.toFinset, (D.count π : ℝ) * crossBnd C T j e π.1.1 π.2.1 := by
      rw [Finset.sum_coe_sort D.toFinset (fun π => (D.count π : ℝ) *
        ∑ j ∈ range L, crossBnd C T j e π.1.1 π.2.1)]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [h2]
    have h3 : ∑ j ∈ range L, ∑ π ∈ D.toFinset, (D.count π : ℝ) * crossBnd C T j e π.1.1 π.2.1 ≤
        L * (3 * lam) := by
      calc _ ≤ ∑ j ∈ range L, 3 * (lam : ℝ) :=
            Finset.sum_le_sum (fun j _ => sum_count_crossBnd_le C D lam T j e hD hl)
        _ = L * (3 * lam) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    calc 2 / (lam * L) * ∑ j ∈ range L, ∑ π ∈ D.toFinset, (D.count π : ℝ) *
          crossBnd C T j e π.1.1 π.2.1 ≤ 2 / (lam * L) * (L * (3 * lam)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 6 := by field_simp; ring
  -- averaging over the product space
  have hprod : ∀ e, ∑ ω ∈ Fintype.piFinset t, Real.exp (∑ i, a e i (ω i)) ≤
      (Fintype.piFinset t).card * Real.exp 6 := by
    intro e
    refine (sum_piFinset_exp_le t (a e) (ha e)).trans ?_
    gcongr
    exact hexp e
  have hne : (Fintype.piFinset t).Nonempty := Fintype.piFinset_nonempty.2 ht
  have hall : ∑ ω ∈ Fintype.piFinset t, ∑ e : Sym2 V, Real.exp (∑ i, a e i (ω i)) ≤
      ∑ ω ∈ Fintype.piFinset t, (Fintype.card (Sym2 V) : ℝ) * Real.exp 6 := by
    rw [Finset.sum_comm, Finset.sum_const, nsmul_eq_mul]
    calc ∑ e : Sym2 V, ∑ ω ∈ Fintype.piFinset t, Real.exp (∑ i, a e i (ω i))
        ≤ ∑ e : Sym2 V, (Fintype.piFinset t).card * Real.exp 6 :=
          Finset.sum_le_sum (fun e _ => hprod e)
      _ = _ := by rw [Finset.sum_const, card_univ, nsmul_eq_mul]; ring
  obtain ⟨ω, hω, hωle⟩ := Finset.exists_le_of_sum_le hne hall
  have hωt : ∀ i, ω i ∈ t i := Fintype.mem_piFinset.1 hω
  have hY : ∀ e, ∑ i, a e i (ω i) ≤ Λ + 6 := by
    intro e
    have h1 : Real.exp (∑ i, a e i (ω i)) ≤ (Fintype.card (Sym2 V) : ℝ) * Real.exp 6 :=
      le_trans (Finset.single_le_sum (f := fun e => Real.exp (∑ i, a e i (ω i)))
        (fun e _ => (Real.exp_pos _).le) (mem_univ e)) hωle
    have h2 : (Fintype.card (Sym2 V) : ℝ) * Real.exp 6 ≤ Real.exp (Λ + 6) := by
      rw [Real.exp_add]; gcongr
    exact Real.exp_le_exp.1 (h1.trans h2)
  -- the routes
  let r : Routes V := fun π => if h : π ∈ D.toFinset then wpath C π.1.1 (ω ⟨π, h⟩) else []
  have hr : ∀ i : ι, r i.1 = wpath C i.1.1.1 (ω i) := by
    intro i
    simp only [r, dif_pos i.2]
    rfl
  have hr' : ∀ π (hπ : π ∈ D), r π = wpath C π.1.1 (ω ⟨π, Multiset.mem_toFinset.2 hπ⟩) :=
    fun π hπ => hr ⟨π, Multiset.mem_toFinset.2 hπ⟩
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro π hπ
    rw [hr' π hπ]
    exact wpath_walk C L π.1.1 π.2.1 (hωt ⟨π, Multiset.mem_toFinset.2 hπ⟩)
  · intro π hπ
    rw [hr' π hπ]
    exact wpath_mem C π.1.1 _
  · intro π hπ
    rw [hr' π hπ]
    exact wpath_length C π.1.1 _
  · intro e
    rw [Finset.sum_multiset_map_count]
    simp only [smul_eq_mul]
    push_cast
    rw [← Finset.sum_coe_sort D.toFinset]
    have h1 : ∑ i : ι, (D.count i.1 : ℝ) * ((r i.1).count e : ℝ) =
        lam * L * ∑ i, a e i (ω i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hr i]
      simp only [a]
      field_simp
    rw [h1]
    have hL' : (L : ℝ) = 2 * T := by rw [hL]; push_cast; ring
    rw [hL'] at hLpos ⊢
    exact mul_le_mul_of_nonneg_left (hY e) (mul_pos hlamR hLpos).le

end Core

lemma rr_card_sym2_le (V : Type) [Fintype V] [DecidableEq V] :
    Fintype.card (Sym2 V) ≤ Fintype.card V ^ 2 := by
  have := Fintype.card_le_of_surjective _ (Sym2.mk_surjective (α := V))
  rwa [Fintype.card_prod, ← pow_two] at this

lemma rr_card_sym2_le_exp (V : Type) [Fintype V] [DecidableEq V] (ν : ℕ)
    (hV : Fintype.card V ≤ ν) :
    (Fintype.card (Sym2 V) : ℝ) ≤ Real.exp (2 * (lg ν : ℝ)) := by
  have h1 : Fintype.card (Sym2 V) ≤ ν ^ 2 :=
    (rr_card_sym2_le V).trans (Nat.pow_le_pow_left hV 2)
  have h2 : (ν : ℝ) ≤ Real.exp (lg ν) := by
    have h3 : (ν : ℝ) ≤ (2 : ℝ) ^ lg ν := by exact_mod_cast (lt_two_pow_lg ν).le
    calc (ν : ℝ) ≤ (2 : ℝ) ^ lg ν := h3
      _ ≤ Real.exp 1 ^ lg ν := by gcongr; have := Real.exp_one_gt_d9; linarith
      _ = Real.exp (lg ν) := by rw [← Real.exp_nat_mul, mul_one]
  calc (Fintype.card (Sym2 V) : ℝ) ≤ (ν : ℝ) ^ 2 := by exact_mod_cast h1
    _ ≤ Real.exp (lg ν) ^ 2 := by gcongr
    _ = Real.exp (2 * (lg ν : ℝ)) := by rw [← Real.exp_nat_mul]; norm_num


end RouteAux

open RouteAux in
/-- **Routing on expanders**: in a cluster with conductance `≥ 1/φinv` (and the mixing bound for
lazy random walks), every demand on ports of the cluster with port loads `≤ lam` can be routed along
walks in the cluster of length `≤ K (φinv+1)^k lg^k ν` with edge congestion
`≤ K (φinv+1)^k lg^k ν · lam`, where all copies of a packet use the same route. -/
theorem route_exists (hmix : Mixing) : ∃ K k : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (C : Finset (Sym2 V)) (P : Finset (Port V)) (φinv ν : ℕ) (D : Demand V) (lam : ℕ),
    NoLoops C → IsExpander C φinv → Fintype.card V ≤ ν → P ⊆ allPorts C →
    D.SupportedOn P → (∀ x, D.load x ≤ lam) →
    ∃ r : Routes V, RoutesOK C D r (K * (φinv + 1) ^ k * lg ν ^ k)
      (K * (φinv + 1) ^ k * lg ν ^ k * lam) := by
  obtain ⟨Km, hmix⟩ := hmix
  refine ⟨16 * (Km + 1), 2, ?_⟩
  intro V _ _ C P φinv ν D lam hCL hexp hV hPA hDP hl
  rcases Multiset.empty_or_exists_mem D with hD0 | ⟨π₀, hπ₀⟩
  · subst hD0
    exact ⟨fun _ => [], ⟨by simp, by simp, by simp, by simp⟩⟩
  have hD : ∀ pq ∈ D, pq.1 ∈ allPorts C ∧ pq.2 ∈ allPorts C :=
    fun pq h => ⟨hPA (hDP pq h).1, hPA (hDP pq h).2⟩
  have hC : C.Nonempty := ⟨π₀.1.2, (mem_allPorts'.1 (hD π₀ hπ₀).1).1⟩
  have hlam : 1 ≤ lam := by
    refine le_trans ?_ (hl π₀.1)
    unfold Demand.load
    have : 0 < (D.filter (fun pq => pq.1 = π₀.1)).card :=
      Multiset.card_pos_iff_exists_mem.2 ⟨π₀, Multiset.mem_filter.2 ⟨hπ₀, rfl⟩⟩
    omega
  -- the mixing time
  set T := Km * (φinv + 1) ^ 2 * lg ν + 1 with hT
  have hM : MixAt C T := fun t ht => hmix C φinv ν hCL hC hexp hV t (by omega)
  obtain ⟨r, hw, hloc, hlen, hcong⟩ := route_core C D lam T hC hM hD hl hlam (by omega)
    (2 * (lg ν : ℝ)) (rr_card_sym2_le_exp V ν hV)
  -- arithmetic
  have hX : 1 ≤ (φinv + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hY : 1 ≤ lg ν := one_le_lg ν
  have hZ : 1 ≤ (φinv + 1) ^ 2 * lg ν := Nat.mul_le_mul hX hY
  have h2T : 2 * T ≤ 2 * (Km + 1) * ((φinv + 1) ^ 2 * lg ν) := by
    rw [hT, show Km * (φinv + 1) ^ 2 * lg ν = Km * ((φinv + 1) ^ 2 * lg ν) by ring]
    nlinarith
  refine ⟨r, hw, hloc, ?_, ?_⟩
  · intro pq hpq
    calc (r pq).length ≤ 2 * T := hlen pq hpq
      _ ≤ 2 * (Km + 1) * ((φinv + 1) ^ 2 * lg ν) := h2T
      _ = 2 * (Km + 1) * (φinv + 1) ^ 2 * lg ν * 1 := by ring
      _ ≤ 2 * (Km + 1) * (φinv + 1) ^ 2 * lg ν * (8 * lg ν) := by gcongr; omega
      _ = 16 * (Km + 1) * (φinv + 1) ^ 2 * lg ν ^ 2 := by ring
  · intro e
    have hN : (D.map (fun pq => (r pq).count e)).sum ≤ lam * (2 * T) * (2 * lg ν + 6) := by
      have h := hcong e
      have e1 : ((lam * (2 * T) * (2 * lg ν + 6) : ℕ) : ℝ) =
          (lam : ℝ) * (2 * (T : ℝ)) * (2 * (lg ν : ℝ) + 6) := by push_cast; ring
      have : (((D.map (fun pq => (r pq).count e)).sum : ℕ) : ℝ) ≤
          ((lam * (2 * T) * (2 * lg ν + 6) : ℕ) : ℝ) := by
        rw [e1]; exact h
      exact_mod_cast this
    calc (D.map (fun pq => (r pq).count e)).sum ≤ lam * (2 * T) * (2 * lg ν + 6) := hN
      _ ≤ lam * (2 * (Km + 1) * ((φinv + 1) ^ 2 * lg ν)) * (8 * lg ν) := by gcongr; omega
      _ = 16 * (Km + 1) * (φinv + 1) ^ 2 * lg ν ^ 2 * lam := by ring

end APSP.Stoc
