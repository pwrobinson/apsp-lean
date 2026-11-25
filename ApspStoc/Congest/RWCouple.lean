import ApspStoc.G0Model

/-!
# Coupling the distributed random walks with the abstract model `G0Model`

In the distributed random-walk construction (`rwLink`), a walk's lazy step is taken at the node
`y` where the walk currently is, with a seed from `y`'s *private* seed table. Concretely, every node
`y` draws a table `τ y : RWTable V Rmax ℓ Dmax = Port V → Fin Rmax → Fin (2ℓ) → Fin Dmax`, uniformly
and independently; walk `w = (p, i)` (port `p ∈ P`, token index `i < R ≤ Rmax`) uses the seed
`τ y p i j` for its step `j`, at the node `y` it occupies before that step. The lazy choice is made
by `lazyStepD Dmax`, i.e. by the rule of `lazyStep` with `Dmax` in place of `seedRange C`.

This file shows that this concrete process is exactly the abstract model of `G0Model.lean`:

* `lazyStepD_eq`: if `seedRange C ∣ Dmax`, then `lazyStepD Dmax C y t = lazyStep C y (t / m)` with
  `m = Dmax / seedRange C` (the reduction `t ↦ t / m` preserves the block structure).
* `rwSeedMap C P hR τ : RWSeeds C P R ℓ` reduces, for every walk `w` and step `j`, the seed that `w`
  actually uses in step `j` (the one at its current node `y_j`) by `t ↦ t / m`.
  `rwSeedMap_traj`: the concrete trajectory of `w` is `rwTraj C w.1.1 (rwSeedMap C P hR τ w)`.
* `rwSeedMap_prob`: `rwSeedMap` is measure preserving: for every event `Ev` on the abstract seeds,
  the probability over uniform tables `τ` of `Ev (rwSeedMap C P hR τ)` is `rwProb C P R ℓ Ev`.
  (Every fibre has the same size: the coordinates `(y_j(w), p, i, j)` constrained by an abstract
  seed vector `σ` are pairwise distinct and each constraint allows exactly `m` values.)
* `seedRange_dvd_rwDmax`: for loop-free clusters, `seedRange C ∣ rwDmax n = 2 · (n!)ⁿ`.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The seed range -/

lemma seedRange_half (C : Finset (Sym2 V)) : seedRange C / 2 = ∏ v, max 1 (degIn C v) := by
  unfold seedRange; omega

lemma seedRange_pos (C : Finset (Sym2 V)) : 0 < seedRange C := by
  have : 0 < ∏ v, max 1 (degIn C v) :=
    Finset.prod_pos (fun v _ => lt_of_lt_of_le one_pos (le_max_left _ _))
  unfold seedRange; omega

/-- A node's (positive) degree divides `seedRange C / 2`. -/
lemma degIn_dvd_seedRange_half (C : Finset (Sym2 V)) {y : V} (hy : 0 < degIn C y) :
    degIn C y ∣ seedRange C / 2 := by
  rw [seedRange_half]
  have h := Finset.dvd_prod_of_mem (fun v => max 1 (degIn C v)) (mem_univ y)
  rwa [max_eq_right hy] at h

/-- `2 · deg_C(y) ∣ seedRange C` for every node of positive degree. -/
lemma two_mul_degIn_dvd_seedRange (C : Finset (Sym2 V)) {y : V} (hy : 0 < degIn C y) :
    2 * degIn C y ∣ seedRange C := by
  have h := Nat.mul_dvd_mul_left 2 (degIn_dvd_seedRange_half C hy)
  have h2 : 2 * (seedRange C / 2) = seedRange C := by unfold seedRange; omega
  rwa [h2] at h

/-- The seed range divides `2 · (n!)ⁿ` (`n = |V|`) when all degrees are at most `n`. -/
theorem seedRange_dvd (C : Finset (Sym2 V)) (hdeg : ∀ v, degIn C v ≤ Fintype.card V) :
    seedRange C ∣ 2 * (Fintype.card V).factorial ^ Fintype.card V := by
  unfold seedRange
  apply Nat.mul_dvd_mul_left
  rw [← Finset.card_univ (α := V), ← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro v _
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  exact Nat.dvd_factorial (lt_of_lt_of_le one_pos (le_max_left _ _)) (max_le hn (hdeg v))

/-- In a loop-free cluster every degree is at most `n = |V|`. -/
lemma degIn_le_card (C : Finset (Sym2 V)) (hC : NoLoops C) (v : V) :
    degIn C v ≤ Fintype.card V := by
  by_cases hv : v ∈ nodes C
  · have := degIn_succ_le hC hv
    have := Finset.card_le_univ (nodes C)
    omega
  · rw [degIn_eq_zero hv]; exact Nat.zero_le _

/-- The seed range of the protocol: `Dmax = 2 · (n!)ⁿ`, a multiple of `seedRange C` for every
loop-free cluster `C` on `n` nodes, and known to every node. -/
def rwDmax (n : ℕ) : ℕ := 2 * n.factorial ^ n

lemma rwDmax_pos (n : ℕ) : 0 < rwDmax n := by
  unfold rwDmax; have := Nat.factorial_pos n; positivity

theorem seedRange_dvd_rwDmax (C : Finset (Sym2 V)) (hC : NoLoops C) :
    seedRange C ∣ rwDmax (Fintype.card V) :=
  seedRange_dvd C (degIn_le_card C hC)

/-- The token-index range of the protocol: `Rmax = max_{a ≤ n, b ≤ n²} Rf a b`. -/
def rwRmax (Rf : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  (range (n + 1)).sup (fun a => (range (n ^ 2 + 1)).sup (Rf a))

lemma le_rwRmax (Rf : ℕ → ℕ → ℕ) {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n ^ 2) :
    Rf a b ≤ rwRmax Rf n := by
  unfold rwRmax
  refine le_trans ?_ (Finset.le_sup (f := fun a => (range (n ^ 2 + 1)).sup (Rf a))
    (mem_range.2 (Nat.lt_succ_of_le ha)))
  exact Finset.le_sup (f := Rf a) (mem_range.2 (Nat.lt_succ_of_le hb))

/-! ## Lazy steps with seeds in `[0, Dmax)` -/

/-- One lazy step from `y` with seed `t < Dmax`: the rule of `lazyStep` with `Dmax` in place of
`seedRange C` — stay iff `t < Dmax/2` (or `y` is isolated), else cross the incident edge of index
`⌊(t - Dmax/2) / (Dmax/(2 deg y))⌋`. Returns the new node and the crossed edge (if any). -/
noncomputable def lazyStepD (Dmax : ℕ) (C : Finset (Sym2 V)) (y : V) (t : ℕ) :
    V × Option (Sym2 V) :=
  if t < Dmax / 2 ∨ degIn C y = 0 then (y, none)
  else
    match (incList C y)[(t - Dmax / 2) / (Dmax / 2 / degIn C y)]? with
    | some e => (otherEnd e y, some e)
    | none => (y, none)

/-- **Block-preserving reduction.** If `seedRange C ∣ Dmax` (and `Dmax > 0`), a lazy step with seed
`t` in range `Dmax` is the lazy step with seed `t / m` in range `seedRange C`, `m = Dmax / seedRange C`. -/
theorem lazyStepD_eq {Dmax : ℕ} (C : Finset (Sym2 V)) (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax)
    (y : V) (t : ℕ) : lazyStepD Dmax C y t = lazyStep C y (t / (Dmax / seedRange C)) := by
  have hDpos := seedRange_pos C
  have hmpos : 0 < Dmax / seedRange C := Nat.div_pos (Nat.le_of_dvd hpos hD) hDpos
  have hDm : Dmax = seedRange C * (Dmax / seedRange C) := (Nat.mul_div_cancel' hD).symm
  have hD2 : seedRange C = 2 * (seedRange C / 2) := by unfold seedRange; omega
  generalize Dmax / seedRange C = m at hmpos hDm ⊢
  have hDm2 : Dmax / 2 = seedRange C / 2 * m := by
    rw [hDm, hD2, mul_assoc]; simp
  unfold lazyStepD lazyStep
  rw [hDm2]
  by_cases hd : degIn C y = 0
  · simp [hd]
  · have hdpos : 0 < degIn C y := Nat.pos_of_ne_zero hd
    obtain ⟨k, hk⟩ := degIn_dvd_seedRange_half C hdpos
    have hlt : t < seedRange C / 2 * m ↔ t / m < seedRange C / 2 :=
      (Nat.div_lt_iff_lt_mul hmpos).symm
    have hidx : (t - seedRange C / 2 * m) / (seedRange C / 2 * m / degIn C y) =
        (t / m - seedRange C / 2) / (seedRange C / 2 / degIn C y) := by
      rw [hk]
      generalize degIn C y = d at hdpos ⊢
      have e1 : d * k * m / d = k * m := by rw [mul_assoc, Nat.mul_div_cancel_left _ hdpos]
      have e2 : d * k / d = k := Nat.mul_div_cancel_left _ hdpos
      rw [e1, e2, show d * k * m = m * (d * k) by ring, mul_comm k m,
        ← Nat.div_div_eq_div_mul, Nat.sub_mul_div]
    simp only [hd, or_false, hlt, hidx]
    rfl

/-! ## Positions and trajectories -/

/-- The node of the abstract walk from port `p` with seeds `σ` before its lazy step `j` (after
`j` steps; the walk stays put after its `2ℓ` steps). -/
noncomputable def rwPos (C : Finset (Sym2 V)) (p : Port V) {ℓ : ℕ}
    (σ : Fin (2 * ℓ) → Fin (seedRange C)) : ℕ → V
  | 0 => otherEnd p.2 p.1
  | j + 1 => if h : j < 2 * ℓ then (lazyStep C (rwPos C p σ j) (σ ⟨j, h⟩)).1 else rwPos C p σ j

/-- A seed table of a node: one seed in `[0, Dmax)` for each (port, token index, step). -/
abbrev RWTable (V : Type) (Rmax ℓ Dmax : ℕ) := Port V → Fin Rmax → Fin (2 * ℓ) → Fin Dmax

/-- The seeds available to walk `w = (p, i)` (with `i < R ≤ Rmax`): at node `y`, step `j`, the entry
`τ y p i j` of `y`'s table. -/
def walkTab {P : Finset (Port V)} {R Rmax ℓ Dmax : ℕ} (hR : R ≤ Rmax)
    (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) : V → Fin (2 * ℓ) → Fin Dmax :=
  fun y => τ y w.1.1 (Fin.castLE hR w.2)

/-- The node of the concrete walk from port `p` before its step `j`, when the step at node `y`
uses the seed `κ y j` (`κ = walkTab hR τ w` for walk `w`): first the crossing of `p.2`, then lazy
steps by `lazyStepD` at the current node. -/
noncomputable def rwPosD (C : Finset (Sym2 V)) (p : Port V) {ℓ Dmax : ℕ}
    (κ : V → Fin (2 * ℓ) → Fin Dmax) : ℕ → V
  | 0 => otherEnd p.2 p.1
  | j + 1 => if h : j < 2 * ℓ then
      (lazyStepD Dmax C (rwPosD C p κ j) (κ (rwPosD C p κ j) ⟨j, h⟩)).1
    else rwPosD C p κ j

/-- The concrete trajectory of the walk from port `p` with node-local seeds `κ`: first the
crossing of `p.2`, then the `2ℓ` steps, step `j` taken at the current node `y` by `lazyStepD` with
seed `κ y j`; each entry is (node after the step, crossed edge). -/
noncomputable def rwTrajD (C : Finset (Sym2 V)) (p : Port V) {ℓ Dmax : ℕ}
    (κ : V → Fin (2 * ℓ) → Fin Dmax) : List (V × Option (Sym2 V)) :=
  (otherEnd p.2 p.1, some p.2) ::
    List.ofFn (fun j : Fin (2 * ℓ) => lazyStepD Dmax C (rwPosD C p κ j) (κ (rwPosD C p κ j) j))

/-- The reduced seeds of the concrete walk from `p`: step `j` gets `κ y_j j / m` (`y_j` its node
before step `j`, `m = Dmax / seedRange C`; the `% seedRange C` is vacuous when
`seedRange C ∣ Dmax`, see `rwRed_val`). -/
noncomputable def rwRed (C : Finset (Sym2 V)) (p : Port V) {ℓ Dmax : ℕ}
    (κ : V → Fin (2 * ℓ) → Fin Dmax) : Fin (2 * ℓ) → Fin (seedRange C) :=
  fun j => ⟨(κ (rwPosD C p κ j) j : ℕ) / (Dmax / seedRange C) % seedRange C,
    Nat.mod_lt _ (seedRange_pos C)⟩

/-- **The coupling map** `Φ`: node tables `τ` ↦ abstract seeds, `Φ τ w j = τ y_j p i j / m` where
`w = (p, i)`, `y_j` is the node of the concrete walk `w` before step `j` and
`m = Dmax / seedRange C`. -/
noncomputable def rwSeedMap (C : Finset (Sym2 V)) (P : Finset (Port V)) {R Rmax ℓ Dmax : ℕ}
    (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) : RWSeeds C P R ℓ :=
  fun w => rwRed C w.1.1 (walkTab hR τ w)

/-- The node of walk `w` before its step `j` in the distributed process with node tables `τ`. -/
noncomputable def rwWalkPos (C : Finset (Sym2 V)) {P : Finset (Port V)} {R Rmax ℓ Dmax : ℕ}
    (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) : ℕ → V :=
  rwPosD C w.1.1 (walkTab hR τ w)

/-- The trajectory of walk `w` in the distributed process with node tables `τ`. -/
noncomputable def rwWalkTraj (C : Finset (Sym2 V)) {P : Finset (Port V)} {R Rmax ℓ Dmax : ℕ}
    (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) : List (V × Option (Sym2 V)) :=
  rwTrajD C w.1.1 (walkTab hR τ w)

section Traj

variable (C : Finset (Sym2 V))

@[simp] lemma rwPos_zero (p : Port V) {ℓ : ℕ} (σ : Fin (2 * ℓ) → Fin (seedRange C)) :
    rwPos C p σ 0 = otherEnd p.2 p.1 := rfl

lemma rwPos_succ (p : Port V) {ℓ : ℕ} (σ : Fin (2 * ℓ) → Fin (seedRange C)) {j : ℕ}
    (hj : j < 2 * ℓ) : rwPos C p σ (j + 1) = (lazyStep C (rwPos C p σ j) (σ ⟨j, hj⟩)).1 := by
  simp [rwPos, hj]

omit [Fintype V] in
@[simp] lemma rwPosD_zero (p : Port V) {ℓ Dmax : ℕ} (κ : V → Fin (2 * ℓ) → Fin Dmax) :
    rwPosD C p κ 0 = otherEnd p.2 p.1 := rfl

omit [Fintype V] in
lemma rwPosD_succ (p : Port V) {ℓ Dmax : ℕ} (κ : V → Fin (2 * ℓ) → Fin Dmax) {j : ℕ}
    (hj : j < 2 * ℓ) :
    rwPosD C p κ (j + 1) = (lazyStepD Dmax C (rwPosD C p κ j) (κ (rwPosD C p κ j) ⟨j, hj⟩)).1 := by
  simp [rwPosD, hj]

/-- A lazy walk with seeds `g`, described through its positions. -/
lemma walkSteps_ofFn {n : ℕ} (g : Fin n → ℕ) (pos : ℕ → V)
    (hpos : ∀ j : Fin n, pos (j + 1) = (lazyStep C (pos j) (g j)).1) :
    walkSteps C (pos 0) (List.ofFn g) = List.ofFn (fun j => lazyStep C (pos j) (g j)) := by
  induction n generalizing pos with
  | zero => simp [walkSteps]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, walkSteps]
    have h1 : (lazyStep C (pos 0) (g 0)).1 = pos (0 + 1) := (hpos 0).symm
    rw [h1]
    have := ih (fun j => g j.succ) (fun j => pos (j + 1)) (fun j => by
      have := hpos j.succ
      simpa using this)
    simpa using this

/-- The abstract trajectory through the positions `rwPos`. -/
theorem rwTraj_eq_ofFn (p : Port V) {ℓ : ℕ} (σ : Fin (2 * ℓ) → Fin (seedRange C)) :
    rwTraj C p σ = (otherEnd p.2 p.1, some p.2) ::
      List.ofFn (fun j : Fin (2 * ℓ) => lazyStep C (rwPos C p σ j) (σ j)) := by
  unfold rwTraj
  congr 1
  exact walkSteps_ofFn C (fun j => (σ j : ℕ)) (rwPos C p σ) (fun j => rwPos_succ C p σ j.2)

lemma rwTraj_length (p : Port V) {ℓ : ℕ} (σ : Fin (2 * ℓ) → Fin (seedRange C)) :
    (rwTraj C p σ).length = 2 * ℓ + 1 := by
  simp [rwTraj_eq_ofFn]

lemma rwTraj_getElem?_zero (p : Port V) {ℓ : ℕ} (σ : Fin (2 * ℓ) → Fin (seedRange C)) :
    (rwTraj C p σ)[0]? = some (otherEnd p.2 p.1, some p.2) := by
  simp [rwTraj_eq_ofFn]

lemma rwTraj_getElem?_succ (p : Port V) {ℓ : ℕ} (σ : Fin (2 * ℓ) → Fin (seedRange C)) {j : ℕ}
    (hj : j < 2 * ℓ) :
    (rwTraj C p σ)[j + 1]? = some (lazyStep C (rwPos C p σ j) (σ ⟨j, hj⟩)) := by
  simp [rwTraj_eq_ofFn, hj]

variable {C}

lemma rwRed_lt {Dmax : ℕ} (hD : seedRange C ∣ Dmax) (t : Fin Dmax) :
    (t : ℕ) / (Dmax / seedRange C) < seedRange C := by
  rcases Nat.eq_zero_or_pos Dmax with h0 | hpos
  · exact absurd t.2 (by omega)
  have hmpos : 0 < Dmax / seedRange C := Nat.div_pos (Nat.le_of_dvd hpos hD) (seedRange_pos C)
  rw [Nat.div_lt_iff_lt_mul hmpos, Nat.mul_div_cancel' hD]
  exact t.2

lemma rwRed_val (p : Port V) {ℓ Dmax : ℕ} (hD : seedRange C ∣ Dmax)
    (κ : V → Fin (2 * ℓ) → Fin Dmax) (j : Fin (2 * ℓ)) :
    (rwRed C p κ j : ℕ) = (κ (rwPosD C p κ j) j : ℕ) / (Dmax / seedRange C) :=
  Nat.mod_eq_of_lt (rwRed_lt hD _)

/-- The concrete positions are the abstract positions under the reduced seeds. -/
theorem rwPosD_eq (p : Port V) {ℓ Dmax : ℕ} (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax)
    (κ : V → Fin (2 * ℓ) → Fin Dmax) (j : ℕ) : rwPosD C p κ j = rwPos C p (rwRed C p κ) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases hj : j < 2 * ℓ
    · rw [rwPosD_succ C p κ hj, rwPos_succ C p _ hj, lazyStepD_eq C hD hpos, ← ih]
      congr 3
      exact (rwRed_val p hD κ ⟨j, hj⟩).symm
    · simp [rwPosD, rwPos, hj, ih]

/-- **Trajectories are preserved** (per walk): the concrete trajectory is the abstract trajectory
under the reduced seeds. -/
theorem rwTrajD_eq (p : Port V) {ℓ Dmax : ℕ} (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax)
    (κ : V → Fin (2 * ℓ) → Fin Dmax) : rwTrajD C p κ = rwTraj C p (rwRed C p κ) := by
  rw [rwTraj_eq_ofFn, rwTrajD]
  congr 1
  apply List.ofFn_inj.2
  funext j
  rw [lazyStepD_eq C hD hpos, rwPosD_eq p hD hpos, rwRed_val p hD κ j, rwPosD_eq p hD hpos]

end Traj

section Coupling

variable {C : Finset (Sym2 V)} {P : Finset (Port V)} {R Rmax ℓ Dmax : ℕ}

lemma rwSeedMap_val (hD : seedRange C ∣ Dmax) (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax)
    (w : RWIdx P R) (j : Fin (2 * ℓ)) :
    (rwSeedMap C P hR τ w j : ℕ) =
      (τ (rwWalkPos C hR τ w j) w.1.1 (Fin.castLE hR w.2) j : ℕ) / (Dmax / seedRange C) :=
  rwRed_val _ hD _ j

/-- The positions of the distributed walk `w` are those of the abstract walk under `rwSeedMap`. -/
theorem rwPos_rwSeedMap (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (hR : R ≤ Rmax)
    (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) (j : ℕ) :
    rwPos C w.1.1 (rwSeedMap C P hR τ w) j = rwWalkPos C hR τ w j :=
  (rwPosD_eq _ hD hpos _ j).symm

/-- **Trajectories are preserved**: the trajectory of walk `w` in the distributed process with
node tables `τ` is the abstract trajectory `rwTraj` under the seeds `rwSeedMap C P hR τ`. -/
theorem rwSeedMap_traj (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (hR : R ≤ Rmax)
    (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) :
    rwTraj C w.1.1 (rwSeedMap C P hR τ w) = rwWalkTraj C hR τ w :=
  (rwTrajD_eq _ hD hpos _).symm

/-- Step `j` of the abstract walk `w` under `rwSeedMap` is the lazy step taken by the distributed
walk at its current node `y`, with `y`'s seed `τ y p i j`. -/
theorem rwTraj_rwSeedMap_getElem?_succ (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax)
    (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) {j : ℕ} (hj : j < 2 * ℓ) :
    (rwTraj C w.1.1 (rwSeedMap C P hR τ w))[j + 1]? =
      some (lazyStepD Dmax C (rwWalkPos C hR τ w j)
        (τ (rwWalkPos C hR τ w j) w.1.1 (Fin.castLE hR w.2) ⟨j, hj⟩)) := by
  rw [rwSeedMap_traj hD hpos hR τ w, rwWalkTraj, rwTrajD]
  simp [hj, rwWalkPos, walkTab]

omit [Fintype V] in
/-- The position of the distributed walk after step `j` (by the definition of `rwPosD`). -/
lemma rwWalkPos_succ (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) {j : ℕ}
    (hj : j < 2 * ℓ) :
    rwWalkPos C hR τ w (j + 1) = (lazyStepD Dmax C (rwWalkPos C hR τ w j)
      (τ (rwWalkPos C hR τ w j) w.1.1 (Fin.castLE hR w.2) ⟨j, hj⟩)).1 :=
  rwPosD_succ C _ _ hj

omit [Fintype V] in
@[simp] lemma rwWalkPos_zero (hR : R ≤ Rmax) (τ : V → RWTable V Rmax ℓ Dmax) (w : RWIdx P R) :
    rwWalkPos C hR τ w 0 = otherEnd w.1.1.2 w.1.1.1 := rfl

/-- The fibre of `rwSeedMap` over `σ`: `τ` reproduces `σ` iff at every coordinate
`(y_j^σ(w), p, i, j)` (with `y_j^σ(w)` the node of the abstract walk) the seed reduces to
`σ w j`. -/
theorem rwSeedMap_eq_iff (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (hR : R ≤ Rmax)
    (τ : V → RWTable V Rmax ℓ Dmax) (σ : RWSeeds C P R ℓ) :
    rwSeedMap C P hR τ = σ ↔ ∀ (w : RWIdx P R) (j : Fin (2 * ℓ)),
      (τ (rwPos C w.1.1 (σ w) j) w.1.1 (Fin.castLE hR w.2) j : ℕ) / (Dmax / seedRange C) =
        σ w j := by
  constructor
  · rintro rfl w j
    rw [rwPos_rwSeedMap hD hpos, rwSeedMap_val hD]
  · intro h
    funext w
    have hp : ∀ j, rwWalkPos C hR τ w j = rwPos C w.1.1 (σ w) j := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        by_cases hj : j < 2 * ℓ
        · rw [rwWalkPos_succ hR τ w hj, rwPos_succ C _ _ hj, lazyStepD_eq C hD hpos, ih,
            h w ⟨j, hj⟩]
        · simp [rwWalkPos, rwPosD, rwPos, hj] at ih ⊢; exact ih
    funext j
    apply Fin.ext
    rw [rwSeedMap_val hD, hp]
    exact h w j

/-- Seeds in `[0, D·m)` with quotient `k < D` by `m`: exactly `m` of them. -/
lemma card_filter_div_eq {Dmax D m k : ℕ} (hDm : Dmax = D * m) (hm : 0 < m) (hk : k < D) :
    (univ.filter (fun t : Fin Dmax => (t : ℕ) / m = k)).card = m := by
  have hkm : (k + 1) * m ≤ D * m := Nat.mul_le_mul_right _ hk
  suffices h : (univ.filter (fun t : Fin Dmax => (t : ℕ) / m = k)).card =
      (Finset.Ico (k * m) (k * m + m)).card by simpa using h
  refine Finset.card_bij (fun t _ => (t : ℕ)) ?_ ?_ ?_
  · intro t ht
    rw [mem_filter, Nat.div_eq_iff hm] at ht
    rw [mem_Ico]; omega
  · intro a _ b _ h; exact Fin.ext h
  · intro b hb
    rw [mem_Ico] at hb
    have hb2 : b < Dmax := by rw [hDm]; nlinarith
    refine ⟨⟨b, hb2⟩, ?_, rfl⟩
    rw [mem_filter, Nat.div_eq_iff hm]
    exact ⟨mem_univ _, by simp only; omega⟩

/-- Currying the seed coordinates. -/
def rwTableEquiv (V : Type) (Rmax ℓ Dmax : ℕ) :
    (V × Port V × Fin Rmax × Fin (2 * ℓ) → Fin Dmax) ≃ (V → RWTable V Rmax ℓ Dmax) where
  toFun f := fun y q i j => f (y, q, i, j)
  invFun τ := fun c => τ c.1 c.2.1 c.2.2.1 c.2.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The common size of the fibres of `rwSeedMap`: `m^K · Dmax^(N - K)` with `K` the number of
(walk, step) pairs and `N` the number of seed coordinates. -/
def rwFibre (P : Finset (Port V)) (R Rmax ℓ Dmax m : ℕ) : ℕ :=
  m ^ Fintype.card (RWIdx P R × Fin (2 * ℓ)) *
    Dmax ^ (Fintype.card (V × Port V × Fin Rmax × Fin (2 * ℓ)) -
      Fintype.card (RWIdx P R × Fin (2 * ℓ)))

/-- **Uniform fibres**: every fibre of `rwSeedMap` has size `rwFibre`. -/
theorem card_rwSeedMap_fibre (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (hR : R ≤ Rmax)
    (σ : RWSeeds C P R ℓ) :
    (univ.filter (fun τ : V → RWTable V Rmax ℓ Dmax => rwSeedMap C P hR τ = σ)).card =
      rwFibre P R Rmax ℓ Dmax (Dmax / seedRange C) := by
  classical
  set m := Dmax / seedRange C with hm
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hpos hD) (seedRange_pos C)
  have hDm : Dmax = seedRange C * m := (Nat.mul_div_cancel' hD).symm
  -- the constrained coordinates
  let c : RWIdx P R × Fin (2 * ℓ) → V × Port V × Fin Rmax × Fin (2 * ℓ) := fun wj =>
    (rwPos C wj.1.1.1 (σ wj.1) wj.2, wj.1.1.1, Fin.castLE hR wj.1.2, wj.2)
  have hinj : Function.Injective c := by
    rintro ⟨⟨⟨p, hp⟩, i⟩, j⟩ ⟨⟨⟨p', hp'⟩, i'⟩, j'⟩ h
    simp only [c, Prod.mk.injEq] at h
    obtain ⟨-, rfl, hi, rfl⟩ := h
    have : i = i' := Fin.castLE_injective hR hi
    subst this; rfl
  let A : V × Port V × Fin Rmax × Fin (2 * ℓ) → Finset (Fin Dmax) := fun x =>
    univ.filter (fun t => ∀ wj, c wj = x → (t : ℕ) / m = σ wj.1 wj.2)
  have h1 : (univ.filter (fun τ : V → RWTable V Rmax ℓ Dmax => rwSeedMap C P hR τ = σ)).card =
      (Fintype.piFinset A).card := by
    refine (Finset.card_equiv (rwTableEquiv V Rmax ℓ Dmax).symm ?_)
    intro τ
    rw [mem_filter, Fintype.mem_piFinset, rwSeedMap_eq_iff hD hpos hR]
    simp only [mem_univ, true_and, A, mem_filter]
    constructor
    · rintro h x wj rfl; exact h wj.1 wj.2
    · intro h w j; exact h (c (w, j)) (w, j) rfl
  have h2 : ∀ x, (A x).card = if x ∈ univ.image c then m else Dmax := by
    intro x
    split_ifs with hx
    · obtain ⟨wj, -, rfl⟩ := mem_image.1 hx
      have : A (c wj) = univ.filter (fun t : Fin Dmax => (t : ℕ) / m = σ wj.1 wj.2) := by
        ext t
        simp only [A, mem_filter, mem_univ, true_and]
        constructor
        · intro h; exact h wj rfl
        · intro h wj' hwj'; rw [hinj hwj']; exact h
      rw [this]
      exact card_filter_div_eq hDm hmpos (σ wj.1 wj.2).2
    · have : A x = univ := by
        ext t
        simp only [A, mem_filter, mem_univ, true_and, iff_true]
        intro wj hwj
        exact absurd (mem_image.2 ⟨wj, mem_univ _, hwj⟩) hx
      rw [this, card_univ, Fintype.card_fin]
  rw [h1, Fintype.card_piFinset, Finset.prod_congr rfl (fun x _ => h2 x), Finset.prod_ite,
    prod_const, prod_const, filter_mem_eq_inter, univ_inter,
    card_image_of_injective _ hinj, card_univ]
  unfold rwFibre
  congr 2
  have := card_filter_add_card_filter_not (s := (univ : Finset (V × Port V × Fin Rmax ×
    Fin (2 * ℓ)))) (fun x => x ∈ univ.image c)
  rw [filter_mem_eq_inter, univ_inter, card_image_of_injective _ hinj, card_univ, card_univ]
    at this
  omega

/-- Counting form of measure preservation: the number of tables `τ` with `Ev (rwSeedMap τ)` is
the number of abstract seed vectors satisfying `Ev` times the common fibre size. -/
theorem card_filter_rwSeedMap (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (hR : R ≤ Rmax)
    (Ev : RWSeeds C P R ℓ → Prop) [DecidablePred Ev]
    [DecidablePred (fun τ : V → RWTable V Rmax ℓ Dmax => Ev (rwSeedMap C P hR τ))] :
    (univ.filter (fun τ : V → RWTable V Rmax ℓ Dmax => Ev (rwSeedMap C P hR τ))).card =
      (univ.filter Ev).card * rwFibre P R Rmax ℓ Dmax (Dmax / seedRange C) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := rwSeedMap C P hR) (t := univ.filter Ev)
    (fun τ hτ => by simpa using hτ)]
  rw [Finset.sum_congr rfl (g := fun _ => rwFibre P R Rmax ℓ Dmax (Dmax / seedRange C)),
    sum_const, smul_eq_mul]
  intro σ hσ
  rw [← card_rwSeedMap_fibre hD hpos hR σ, filter_filter]
  congr 1
  apply filter_congr
  intro τ _
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨?_, h⟩; rw [h]; simpa using hσ

/-- **Measure preservation.** Under uniform node tables `τ`, the probability of `Ev (rwSeedMap τ)`
equals the probability `rwProb C P R ℓ Ev` of `Ev` under uniform abstract seeds. -/
theorem rwSeedMap_prob (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax) (hR : R ≤ Rmax)
    (Ev : RWSeeds C P R ℓ → Prop)
    [DecidablePred (fun τ : V → RWTable V Rmax ℓ Dmax => Ev (rwSeedMap C P hR τ))] :
    ((univ.filter (fun τ : V → RWTable V Rmax ℓ Dmax => Ev (rwSeedMap C P hR τ))).card : ℝ) /
      (Fintype.card (V → RWTable V Rmax ℓ Dmax) : ℝ) = rwProb C P R ℓ Ev := by
  classical
  have hmpos : 0 < Dmax / seedRange C := Nat.div_pos (Nat.le_of_dvd hpos hD) (seedRange_pos C)
  have hF : (rwFibre P R Rmax ℓ Dmax (Dmax / seedRange C) : ℝ) ≠ 0 := by
    unfold rwFibre; positivity
  have htot : Fintype.card (V → RWTable V Rmax ℓ Dmax) =
      Fintype.card (RWSeeds C P R ℓ) * rwFibre P R Rmax ℓ Dmax (Dmax / seedRange C) := by
    have := card_filter_rwSeedMap hD hpos hR (fun _ : RWSeeds C P R ℓ => True)
    simpa using this
  rw [card_filter_rwSeedMap hD hpos hR Ev, htot, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ hF]
  unfold rwProb
  congr 2

end Coupling

end APSP.Stoc
