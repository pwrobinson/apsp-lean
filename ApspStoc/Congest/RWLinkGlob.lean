import ApspStoc.Congest.RWLinkProto

/-!
# The random-walk construction: the global schedule and the walks

For fixed seed tables `τ`, the *global schedule* `schedG` is defined by well-founded recursion
on the macro-round: node `u` sends to `v` in macro-round `s` what its local send function
`sendL` computes from the packets it received before (`schedG` at earlier macro-rounds). The local
computations read only earlier macro-rounds (`sendL_congr`), so the protocol follows `schedG`.

We then relate the local knowledge in this schedule to the abstract walks under the seeds
`rwSeedMap C P hR τ` (`RWCouple.lean`): unless the walks overflow, the tokens held by `y` before
step `j` are exactly the walks at `y` (`held_eq`), and the reports known by `y` after the reversed
steps down to `j` are the surviving walks visiting `y` at a step `≥ j` (`known_eq`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Local computations read only earlier macro-rounds -/

section Congr

variable (en : LEnv V) {H H' : ℕ → V → Option (Msg V)}

lemma rcvA_congr (h : ∀ s < en.R, H s = H' s) : rcvA en H = rcvA en H' := by
  unfold rcvA
  refine biUnion_congr rfl (fun s hs => ?_)
  rw [h s (mem_range.1 hs)]

lemma rcvB_congr (j : ℕ) (h : ∀ s < en.R + (j + 1) * en.t, H s = H' s) :
    rcvB en H j = rcvB en H' j := by
  unfold rcvB
  refine biUnion_congr rfl (fun k hk => ?_)
  have hk := mem_range.1 hk
  rw [h (bAt en.R en.t j k) (by unfold bAt; nlinarith)]

lemma held_congr : ∀ j, (∀ s < en.R + j * en.t, H s = H' s) → held en H j = held en H' j := by
  intro j
  induction j with
  | zero => intro h; exact rcvA_congr en (fun s hs => h s (by simpa using hs))
  | succ j ih =>
    intro h
    simp only [held]
    rw [ih (fun s hs => h s (by nlinarith)), rcvB_congr en j h]

lemma rcvC_congr (j : ℕ) (h : ∀ s < cAt en.R en.t en.ℓ j 0 + en.t, H s = H' s) :
    rcvC en H j = rcvC en H' j := by
  unfold rcvC
  refine biUnion_congr rfl (fun k hk => ?_)
  have hk := mem_range.1 hk
  rw [h (cAt en.R en.t en.ℓ j k) (by unfold cAt at *; omega)]

lemma known_congr : ∀ r ≤ 2 * en.ℓ,
    (∀ s < en.R + 2 * en.ℓ * en.t + r * en.t, H s = H' s) → known en H r = known en H' r := by
  intro r
  induction r with
  | zero =>
    intro _ h
    simp only [known]
    rw [held_congr en (2 * en.ℓ) (fun s hs => h s (by simpa using hs))]
  | succ r ih =>
    intro hr h
    simp only [known]
    rw [ih (by omega) (fun s hs => h s (by nlinarith)),
      rcvC_congr en (2 * en.ℓ - 1 - r) (fun s hs => h s ?_)]
    unfold cAt at hs
    have e : 2 * en.ℓ - 1 - (2 * en.ℓ - 1 - r) = r := by omega
    rw [e] at hs
    nlinarith

lemma rcvD_congr (h : ∀ s < en.R + 4 * en.ℓ * en.t + en.R, H s = H' s) :
    rcvD en H = rcvD en H' := by
  unfold rcvD
  refine biUnion_congr rfl (fun i hi => ?_)
  have hi := mem_range.1 hi
  rw [h (dRnd en.R en.t en.ℓ i) (by unfold dRnd; omega)]

lemma knownF_congr (h : ∀ s < tEndRW en.R en.t en.ℓ, H s = H' s) :
    knownF en H = knownF en H' := by
  unfold knownF
  have e : 4 * en.ℓ * en.t = 2 * en.ℓ * en.t + 2 * en.ℓ * en.t := by ring
  rw [known_congr en (2 * en.ℓ) le_rfl (fun s hs => h s (by unfold tEndRW; nlinarith)),
    rcvD_congr en (fun s hs => h s (by unfold tEndRW; omega))]

lemma recs_congr (h : ∀ s < en.R + 2 * en.ℓ * en.t, H s = H' s) : recs en H = recs en H' := by
  have hh : ∀ j ≤ 2 * en.ℓ, held en H j = held en H' j := fun j hj =>
    held_congr en j (fun s hs => h s (by nlinarith))
  unfold recs
  congr 1
  · congr 1
    · refine biUnion_congr rfl (fun j hj => ?_)
      rw [hh j (by have := mem_range.1 hj; omega)]
    · refine biUnion_congr rfl (fun j hj => ?_)
      rw [hh j (by have := mem_range.1 hj; omega)]

lemma outMS_congr (h : ∀ s < tEndRW en.R en.t en.ℓ, H s = H' s) : outMS en H = outMS en H' := by
  have e : 4 * en.ℓ * en.t = 2 * en.ℓ * en.t + 2 * en.ℓ * en.t := by ring
  unfold outMS hopsL
  rw [knownF_congr en h, recs_congr en (fun s hs => h s (by unfold tEndRW; omega))]

lemma sendL_congr (s : ℕ) (h : ∀ s' < s, H s' = H' s') (u : V) :
    sendL en H s u = sendL en H' s u := by
  unfold sendL
  have e4 : 4 * en.ℓ * en.t = 2 * en.ℓ * en.t + 2 * en.ℓ * en.t := by ring
  by_cases h1 : s < en.R
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : s < en.R + 2 * en.ℓ * en.t
  · rw [if_pos h2, if_pos h2]
    unfold bSend
    have := Nat.div_mul_le_self (s - en.R) en.t
    rw [held_congr en ((s - en.R) / en.t) (fun s' hs' => h s' (by omega))]
  rw [if_neg h2, if_neg h2]
  by_cases h3 : s < en.R + 4 * en.ℓ * en.t
  · rw [if_pos h3, if_pos h3]
    unfold cSend
    have ht : 0 < en.t := by
      rcases Nat.eq_zero_or_pos en.t with h0 | h0
      · simp only [h0, mul_zero, add_zero] at h2 h3; omega
      · exact h0
    obtain ⟨q, hq⟩ : ∃ q, s - en.R - 2 * en.ℓ * en.t = q := ⟨_, rfl⟩
    rw [hq]
    have hq2 : q < 2 * en.ℓ * en.t := by omega
    have hr : q / en.t < 2 * en.ℓ := by
      rw [Nat.div_lt_iff_lt_mul ht]; exact hq2
    have hdm := Nat.div_mul_le_self q en.t
    have hmod := Nat.mod_lt q ht
    obtain ⟨r, hr0⟩ : ∃ r, q / en.t = r := ⟨_, rfl⟩
    rw [hr0] at hr hdm ⊢
    have e : 2 * en.ℓ - 1 - (2 * en.ℓ - 1 - r) = r := by omega
    rw [e]
    have hb : bAt en.R en.t (2 * en.ℓ - 1 - r) (q % en.t) < s := by
      unfold bAt
      have h5 := Nat.mul_le_mul_right en.t (show 2 * en.ℓ - 1 - r + 1 ≤ 2 * en.ℓ by omega)
      rw [add_mul, one_mul] at h5
      omega
    rw [known_congr en r (by omega) (fun s' hs' => h s' (by omega)), h _ hb]
  rw [if_neg h3, if_neg h3]
  by_cases h4 : s < tEndRW en.R en.t en.ℓ
  · rw [if_pos h4, if_pos h4]
    have h4' : s < 2 * en.R + 4 * en.ℓ * en.t := h4
    unfold dSend
    rw [known_congr en (2 * en.ℓ) le_rfl (fun s' hs' => h s' (by omega)),
      h (s - en.R - 4 * en.ℓ * en.t) (by omega)]
  rw [if_neg h4, if_neg h4]

/-! ### The phases of the local send function -/

lemma sendL_A {s : ℕ} (hs : s < en.R) (u : V) : sendL en H s u = aSend en u s := by
  unfold sendL; rw [if_pos hs]

lemma sendL_B {j k : ℕ} (hj : j < 2 * en.ℓ) (hk : k < en.t) (u : V) :
    sendL en H (bAt en.R en.t j k) u = bSend en H j k u := by
  have ht : 0 < en.t := by omega
  have h1 : (j + 1) * en.t ≤ 2 * en.ℓ * en.t := Nat.mul_le_mul_right _ (by omega)
  rw [add_mul, one_mul] at h1
  have h2 : bAt en.R en.t j k - en.R = k + j * en.t := by unfold bAt; omega
  unfold sendL
  rw [if_neg (by unfold bAt; omega), if_pos (by unfold bAt; omega), h2,
    Nat.add_mul_div_right _ _ ht, Nat.div_eq_of_lt hk, zero_add, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hk]

lemma sendL_C {j k : ℕ} (hj : j < 2 * en.ℓ) (hk : k < en.t) (u : V) :
    sendL en H (cAt en.R en.t en.ℓ j k) u = cSend en H j k u := by
  have ht : 0 < en.t := by omega
  have h1 : (2 * en.ℓ - 1 - j + 1) * en.t ≤ 2 * en.ℓ * en.t :=
    Nat.mul_le_mul_right _ (by omega)
  rw [add_mul, one_mul] at h1
  have e4 : 4 * en.ℓ * en.t = 2 * en.ℓ * en.t + 2 * en.ℓ * en.t := by ring
  have h2 : cAt en.R en.t en.ℓ j k - en.R - 2 * en.ℓ * en.t = k + (2 * en.ℓ - 1 - j) * en.t := by
    unfold cAt; omega
  unfold sendL
  rw [if_neg (by unfold cAt; omega), if_neg (by unfold cAt; omega),
    if_pos (by unfold cAt; omega), h2,
    Nat.add_mul_div_right _ _ ht, Nat.div_eq_of_lt hk, zero_add, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hk, show 2 * en.ℓ - 1 - (2 * en.ℓ - 1 - j) = j by omega]

lemma sendL_D {i : ℕ} (hi : i < en.R) (u : V) :
    sendL en H (dRnd en.R en.t en.ℓ i) u = dSend en H i u := by
  have e4 : 4 * en.ℓ * en.t = 2 * en.ℓ * en.t + 2 * en.ℓ * en.t := by ring
  unfold sendL
  rw [if_neg (by unfold dRnd; omega), if_neg (by unfold dRnd; omega),
    if_neg (by unfold dRnd; omega), if_pos (by unfold dRnd tEndRW; omega),
    show dRnd en.R en.t en.ℓ i - en.R - 4 * en.ℓ * en.t = i by unfold dRnd; omega]

lemma sendL_end {s : ℕ} (hs : tEndRW en.R en.t en.ℓ ≤ s) (u : V) : sendL en H s u = none := by
  have e4 : 4 * en.ℓ * en.t = 2 * en.ℓ * en.t + 2 * en.ℓ * en.t := by ring
  have hs' : 2 * en.R + 4 * en.ℓ * en.t ≤ s := hs
  unfold sendL
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end Congr

/-! ## The global schedule -/

/-- The local environment of node `y` in the run on cluster `C` with port set `P`, `R` tokens per
port, `t` slots per step and seed tables `τ`. -/
def envG (C : Finset (Sym2 V)) (P : Finset (Port V)) (R t : ℕ) {ℓ Rmax Dmax : ℕ}
    (τ : V → RWTable V Rmax ℓ Dmax) (y : V) : LEnv V :=
  ⟨y, C.filter (fun e => y ∈ e), P.filter (fun p => p.1 = y), R, t, ℓ, Dmax,
    fun p i j => seedL (τ y) p i j⟩

/-- **The global packet schedule**: `schedG … s u v` is the packet from `u` to `v` in macro-round
`s`, computed by `u`'s local send function from the packets it received before. -/
noncomputable def schedG (C : Finset (Sym2 V)) (P : Finset (Port V)) (R t : ℕ) {ℓ Rmax Dmax : ℕ}
    (τ : V → RWTable V Rmax ℓ Dmax) (s : ℕ) (u v : V) : Option (Msg V) :=
  sendL (envG C P R t τ u) (fun s' w => if h : s' < s then schedG C P R t τ s' w u else none) s v
termination_by s

/-- The packets received by `y` in the global schedule (all macro-rounds). -/
noncomputable def fullO (C : Finset (Sym2 V)) (P : Finset (Port V)) (R t : ℕ) {ℓ Rmax Dmax : ℕ}
    (τ : V → RWTable V Rmax ℓ Dmax) (y : V) : ℕ → V → Option (Msg V) :=
  fun s w => schedG C P R t τ s w y

section Sched

variable (C : Finset (Sym2 V)) (P : Finset (Port V)) (R t : ℕ) {ℓ Rmax Dmax : ℕ}
  (τ : V → RWTable V Rmax ℓ Dmax)

lemma schedG_eq_trunc (s : ℕ) (u v : V) : schedG C P R t τ s u v =
    sendL (envG C P R t τ u) (fun s' w => if s' < s then schedG C P R t τ s' w u else none) s v := by
  rw [schedG]
  apply sendL_congr
  intro s' hs'
  funext w
  simp [hs']

lemma schedG_full (s : ℕ) (u v : V) :
    schedG C P R t τ s u v = sendL (envG C P R t τ u) (fullO C P R t τ u) s v := by
  rw [schedG_eq_trunc]
  apply sendL_congr
  intro s' hs'
  funext w
  simp [fullO, hs']

@[simp] lemma envG_R (y : V) : (envG C P R t τ y).R = R := rfl
@[simp] lemma envG_t (y : V) : (envG C P R t τ y).t = t := rfl
@[simp] lemma envG_ℓ (y : V) : (envG C P R t τ y).ℓ = ℓ := rfl
@[simp] lemma envG_me (y : V) : (envG C P R t τ y).me = y := rfl
@[simp] lemma envG_E (y : V) : (envG C P R t τ y).E = C.filter (fun e => y ∈ e) := rfl
@[simp] lemma envG_ports (y : V) : (envG C P R t τ y).ports = P.filter (fun p => p.1 = y) := rfl
@[simp] lemma envG_Dmax (y : V) : (envG C P R t τ y).Dmax = Dmax := rfl

lemma schedG_A {s : ℕ} (hs : s < R) (u v : V) :
    schedG C P R t τ s u v = aSend (envG C P R t τ u) v s := by
  rw [schedG_full]; exact sendL_A _ hs v

lemma schedG_B {j k : ℕ} (hj : j < 2 * ℓ) (hk : k < t) (u v : V) :
    schedG C P R t τ (bAt R t j k) u v = bSend (envG C P R t τ u) (fullO C P R t τ u) j k v := by
  rw [schedG_full]; exact sendL_B _ hj hk v

lemma schedG_C {j k : ℕ} (hj : j < 2 * ℓ) (hk : k < t) (u v : V) :
    schedG C P R t τ (cAt R t ℓ j k) u v = cSend (envG C P R t τ u) (fullO C P R t τ u) j k v := by
  rw [schedG_full]; exact sendL_C _ hj hk v

lemma schedG_D {i : ℕ} (hi : i < R) (u v : V) :
    schedG C P R t τ (dRnd R t ℓ i) u v = dSend (envG C P R t τ u) (fullO C P R t τ u) i v := by
  rw [schedG_full]; exact sendL_D _ hi v

lemma schedG_end {s : ℕ} (hs : tEndRW R t ℓ ≤ s) (u v : V) : schedG C P R t τ s u v = none := by
  rw [schedG_full]; exact sendL_end _ hs v

/-- The macro-rounds are covered by the four phases. -/
lemma phase_cases (s : ℕ) (hs : s < tEndRW R t ℓ) :
    s < R ∨ (∃ j k, j < 2 * ℓ ∧ k < t ∧ s = bAt R t j k) ∨
      (∃ j k, j < 2 * ℓ ∧ k < t ∧ s = cAt R t ℓ j k) ∨ (∃ i, i < R ∧ s = dRnd R t ℓ i) := by
  have e4 : 4 * ℓ * t = 2 * ℓ * t + 2 * ℓ * t := by ring
  unfold tEndRW at hs
  by_cases h1 : s < R
  · exact Or.inl h1
  by_cases h2 : s < R + 2 * ℓ * t
  · have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · simp only [h0, mul_zero, add_zero] at h2; omega
      · exact h0
    refine Or.inr (Or.inl ⟨(s - R) / t, (s - R) % t, ?_, Nat.mod_lt _ ht, ?_⟩)
    · rw [Nat.div_lt_iff_lt_mul ht]; omega
    · unfold bAt
      have := Nat.div_add_mod (s - R) t
      rw [mul_comm] at this
      omega
  by_cases h3 : s < R + 4 * ℓ * t
  · have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · simp only [h0, mul_zero, add_zero] at h2 h3; omega
      · exact h0
    obtain ⟨q, hq⟩ : ∃ q, s - R - 2 * ℓ * t = q := ⟨_, rfl⟩
    have hr : q / t < 2 * ℓ := by rw [Nat.div_lt_iff_lt_mul ht]; omega
    have hdm := Nat.div_add_mod q t
    obtain ⟨r, hr0⟩ : ∃ r, q / t = r := ⟨_, rfl⟩
    rw [hr0] at hr hdm
    refine Or.inr (Or.inr (Or.inl ⟨2 * ℓ - 1 - r, q % t, by omega, Nat.mod_lt _ ht, ?_⟩))
    unfold cAt
    rw [show 2 * ℓ - 1 - (2 * ℓ - 1 - r) = r by omega]
    rw [mul_comm] at hdm
    omega
  · exact Or.inr (Or.inr (Or.inr ⟨s - R - 4 * ℓ * t, by omega, by unfold dRnd; omega⟩))

end Sched

/-! ## Facts about lazy steps and edges -/

lemma lazyStepD_filter (Dmax : ℕ) (C : Finset (Sym2 V)) (y : V) (t : ℕ) :
    lazyStepD Dmax (C.filter (fun e => y ∈ e)) y t = lazyStepD Dmax C y t := by
  unfold lazyStepD degIn incList
  simp only [filter_filter, and_self]

lemma lazyStepD_cases (Dmax : ℕ) (S : Finset (Sym2 V)) (y : V) (t : ℕ) :
    lazyStepD Dmax S y t = (y, none) ∨ ∃ e, lazyStepD Dmax S y t = (otherEnd e y, some e) ∧
      e ∈ S ∧ y ∈ e := by
  unfold lazyStepD
  by_cases hc : t < Dmax / 2 ∨ degIn S y = 0
  · left; rw [if_pos hc]
  · rw [if_neg hc]
    rcases h : (incList S y)[(t - Dmax / 2) / (Dmax / 2 / degIn S y)]? with _ | e
    · left; rfl
    · right
      have hm := List.mem_of_getElem? h
      rw [incList, mem_toList, mem_filter] at hm
      exact ⟨e, rfl, hm.1, hm.2⟩

lemma lazyStepD_some {Dmax : ℕ} {S : Finset (Sym2 V)} {y u : V} {t : ℕ} {e : Sym2 V}
    (h : lazyStepD Dmax S y t = (u, some e)) : e ∈ S ∧ y ∈ e ∧ u = otherEnd e y := by
  rcases lazyStepD_cases Dmax S y t with h' | ⟨e', h', he', hy'⟩
  · rw [h'] at h; simp at h
  · rw [h'] at h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨he', hy', h1.symm⟩

lemma lazyStepD_none {Dmax : ℕ} {S : Finset (Sym2 V)} {y : V} {t : ℕ}
    (h : (lazyStepD Dmax S y t).2 = none) : (lazyStepD Dmax S y t).1 = y := by
  rcases lazyStepD_cases Dmax S y t with h' | ⟨e', h', -⟩
  · rw [h']
  · rw [h'] at h; simp at h

section Edges

variable {C : Finset (Sym2 V)}

lemma rwOtherEnd_spec {e : Sym2 V} {y : V} (hy : y ∈ e) : s(y, otherEnd e y) = e := by
  unfold otherEnd; rw [dif_pos hy]; exact Sym2.other_spec hy

lemma rwOtherEnd_mem {e : Sym2 V} {y : V} (hy : y ∈ e) : otherEnd e y ∈ e := by
  unfold otherEnd; rw [dif_pos hy]; exact Sym2.other_mem hy

lemma rwOtherEnd_ne (hC : NoLoops C) {e : Sym2 V} (he : e ∈ C) {y : V} (hy : y ∈ e) :
    otherEnd e y ≠ y := by
  intro h
  apply hC e he
  rw [← rwOtherEnd_spec hy, h]
  exact Sym2.mk_isDiag_iff.2 rfl

lemma mem_iff_otherEnd {e : Sym2 V} {y : V} (hy : y ∈ e) (v : V) :
    v ∈ e ↔ v = y ∨ v = otherEnd e y := by
  conv_lhs => rw [← rwOtherEnd_spec hy]
  exact Sym2.mem_iff

lemma eq_of_otherEnd {e e' : Sym2 V} {y : V} (hy : y ∈ e) (hy' : y ∈ e')
    (h : otherEnd e y = otherEnd e' y) : e = e' := by
  rw [← rwOtherEnd_spec hy, ← rwOtherEnd_spec hy', h]

/-- An edge of `C` at `y` is an edge of the communication graph of the cluster instance. -/
lemma clG_adj_of {N : WNet V} (hCN : C ⊆ N.G.edgeFinset) {e : Sym2 V} (he : e ∈ C) {y : V}
    (hy : y ∈ e) : (clG N C).Adj y (otherEnd e y) := by
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  have hs : s(y, otherEnd e y) = e := rwOtherEnd_spec hy
  have h1 : (clGraph C).Adj y (otherEnd e y) :=
    (show y ≠ otherEnd e y ∧ s(y, otherEnd e y) ∈ C from
      ⟨(rwOtherEnd_ne hC he hy).symm, by rw [hs]; exact he⟩)
  have h2 : N.G.Adj y (otherEnd e y) := by
    have := hCN he
    rw [SimpleGraph.mem_edgeFinset, ← hs] at this
    exact this
  show (clGraph C ⊓ N.G).Adj y (otherEnd e y)
  rw [SimpleGraph.inf_adj]
  exact ⟨h1, h2⟩

end Edges

end APSP.Stoc.Congest
