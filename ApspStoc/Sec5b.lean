import ApspStoc.Sec5bAux5

/-!
# Theorem 5.5: exact SSSP by the thresholded recursion of Ghaffari–Trygub

The algorithm (`topAlg`, built in `Sec5bAux2`) runs the paper's thresholded recursion (Steps 1–7
of the proof of Theorem 5.5) on `V` from the virtual source `σ` with one edge `(σ, s)` of weight
`0`, at height `L = lg(ν^(wexp+1))` (threshold `2^L > n·W ≥` every distance), and outputs the
distances and parents.

* correctness (`ThreshSpec`, including the shortest-path tree) is proved in `Sec5bAux3`;
* the invariant `Valid` of the subproblems (in particular the paper's claim that every node of a
  subproblem with offset `a` has distance in `[a, a + 3δ]`) is proved in `Sec5bAux3`;
* the participation argument (each node is in `≤ 4` windows per level) is `Nw_le`/`Nw_succ`
  (`Sec5bAux1`), the cost recursion is in `Sec5bAux4`/`Sec5bAux5`.
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

lemma ereach_univ_of_walk (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (q : G.Walk u v) :
    EReach (inducedEdges G univ) u v := by
  induction q with
  | nil => exact Relation.ReflTransGen.refl
  | cons h p ih =>
    exact Relation.ReflTransGen.head ((mem_inducedEdges G).2 ⟨h, mem_univ _, mem_univ _⟩) ih

lemma connSet_univ (N : WNet V) (s : V) : ConnSet N.G univ :=
  ⟨⟨s, mem_univ s⟩, fun u _ v _ => ereach_univ_of_walk N.G (N.conn.preconnected u v).some⟩

/-- The cost of an aggregator exchange (Lemma 2.2) with `2`-word messages and public size bound
`|S|` (`3K` words per message and path edge), as a subset profile. -/
lemma agg_cost {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V} {ov d X : ℕ}
    (hE : OverlayProps G E ov d X) (K k ν j : ℕ) (S : Finset V) :
    Prof.mk (K * lg ν ^ k * (2 + 1) * (E.dil + 1) * (S.card + 1)) ((K * (2 + 1)) • E.rhoAgg j S)
        (K * (2 + 1) * E.aggLen j S) ≤
      subsetProf G E j S (3 * K * lg ν ^ k * (d + 1) + 3 * K * ov * d + 3) := by
  unfold subsetProf
  have hL : 1 ≤ lg ν ^ k := Nat.one_le_pow _ _ (lg_pos ν)
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
  · simp only [Prof.rounds_mk]
    have hdil := dil_le_of_props hE
    have : K * lg ν ^ k * (2 + 1) * (E.dil + 1) * (S.card + 1) =
        3 * K * lg ν ^ k * (E.dil + 1) * (S.card + 1) := by ring
    rw [this]
    refine Nat.mul_le_mul_right _ ?_
    calc 3 * K * lg ν ^ k * (E.dil + 1) ≤ 3 * K * lg ν ^ k * (d + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := by omega
  · simp only [Prof.load_mk, Pi.smul_apply, smul_eq_mul]
    have h3 : 3 * K ≤ 3 * K * lg ν ^ k * (d + 1) := by
      calc 3 * K = 3 * K * 1 * 1 := by ring
        _ ≤ 3 * K * lg ν ^ k * (d + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hL) (by omega)
    exact Nat.mul_le_mul (by omega) (rhoAgg_le_rho E j S e)
  · simp only [Prof.msgs_mk]
    have h1 := aggLen_le hE j S
    calc K * (2 + 1) * E.aggLen j S ≤ K * 3 * (ov * d * S.card) := Nat.mul_le_mul_left _ h1
      _ = (3 * K * ov * d) * S.card := by ring
      _ ≤ (3 * K * lg ν ^ k * (d + 1) + 3 * K * ov * d + 3) * (S.card + 1) :=
          Nat.mul_le_mul (by omega) (by omega)

/-- The overhead of the component traversal (`perCompR`) on `P = S`, as a subset profile. -/
lemma ovh_cost {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V} {ov d X : ℕ}
    (hE : OverlayProps G E ov d X) (K₀ j : ℕ) (S : Finset V) :
    Prof.mk (K₀ * (E.dil + 1) ^ 2 * (S.card + 1)) (fun e => K₀ * E.rho G j S e)
        (K₀ * (S.card + 1) + K₀ * E.aggLen j S) ≤
      subsetProf G E j S (K₀ * (d + 1) ^ 2 + K₀ * (ov * d)) := by
  have hdil := dil_le_of_props hE
  have hsq : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hK : K₀ ≤ K₀ * (d + 1) ^ 2 + K₀ * (ov * d) :=
    (Nat.le_mul_of_pos_right K₀ hsq).trans (Nat.le_add_right _ _)
  unfold subsetProf
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
  · simp only [Prof.rounds_mk]
    refine Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left K₀
      (Nat.pow_le_pow_left (by omega : E.dil + 1 ≤ d + 1) 2)).trans (Nat.le_add_right _ _))
  · simp only [Prof.load_mk]
    exact Nat.mul_le_mul_right _ hK
  · simp only [Prof.msgs_mk]
    have h1 := aggLen_le hE j S
    have h2 : K₀ * (S.card + 1) ≤ K₀ * (d + 1) ^ 2 * (S.card + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right K₀ hsq)
    have h3 : ov * d * S.card ≤ ov * d * (S.card + 1) := Nat.mul_le_mul_left _ (by omega)
    have h4 : K₀ * E.aggLen j S ≤ K₀ * (ov * d * (S.card + 1)) :=
      Nat.mul_le_mul_left _ (h1.trans h3)
    calc K₀ * (S.card + 1) + K₀ * E.aggLen j S ≤
          K₀ * (d + 1) ^ 2 * (S.card + 1) + K₀ * (ov * d * (S.card + 1)) := by omega
      _ = (K₀ * (d + 1) ^ 2 + K₀ * (ov * d)) * (S.card + 1) := by ring

/-- **Theorem 5.5**, from Lemma 5.4 and the MST/leader-election lemma. -/
theorem thm_5_5_of (T : Toolkit) (h54 : Lemma_5_4 T) (hmst : LemmaMST T) : Thm_5_5 T := by
  intro wexp
  obtain ⟨qδa, hqδa, h54'⟩ := h54 wexp
  obtain ⟨qδs, hqδs, hmst'⟩ := hmst
  have hL : IsPL (fun ν => lg (ν ^ (wexp + 1))) := IsPL.lg_pow_succ wexp
  refine ⟨fun ν => 28 * (qδa ν + qδs ν + 1) * (lg (ν ^ (wexp + 1)) + 1),
    ((IsPL.const 28).mul ((hqδa.add hqδs).add (IsPL.const 1))).mul (hL.add (IsPL.const 1)),
    fun c fov fd hov hd => ?_⟩
  obtain ⟨qa, hqa, Kδa, Aa, hA⟩ := h54' c hov hd
  obtain ⟨qs, hqs, Kδs, As, hS⟩ := hmst' c hov hd
  obtain ⟨Ku, ku, Kδu, Au, hU⟩ := T.aggUp c (wexp + 1)
  obtain ⟨Kd, kd, Kδd, Ad, hD⟩ := T.aggDown c (wexp + 1)
  have hqu : IsPL (fun ν => 3 * Ku * lg ν ^ ku * (fd ν + 1) + 3 * Ku * fov ν * fd ν + 3) :=
    ((((IsPL.const (3 * Ku)).mul (IsPL.lgpow ku)).mul (hd.add (IsPL.const 1))).add
      (((IsPL.const (3 * Ku)).mul hov).mul hd)).add (IsPL.const 3)
  have hqd : IsPL (fun ν => 3 * Kd * lg ν ^ kd * (fd ν + 1) + 3 * Kd * fov ν * fd ν + 3) :=
    ((((IsPL.const (3 * Kd)).mul (IsPL.lgpow kd)).mul (hd.add (IsPL.const 1))).add
      (((IsPL.const (3 * Kd)).mul hov).mul hd)).add (IsPL.const 3)
  have hqo : IsPL (fun ν => K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν)) :=
    ((IsPL.const (K0of T)).mul ((hd.add (IsPL.const 1)).pow 2)).add ((IsPL.const (K0of T)).mul (hov.mul hd))
  have hQ : IsPL (fun ν => qa ν + qs ν + qs ν + (K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν)) +
      (3 * Ku * lg ν ^ ku * (fd ν + 1) + 3 * Ku * fov ν * fd ν + 3) +
      (3 * Kd * lg ν ^ kd * (fd ν + 1) + 3 * Kd * fov ν * fd ν + 3) + qs ν + qs ν +
      (K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν))) :=
    (((((((hqa.add hqs).add hqs).add hqo).add hqu).add hqd).add hqs).add hqs).add hqo
  refine ⟨fun ν => 8 * (qa ν + qs ν + qs ν + (K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν)) +
      (3 * Ku * lg ν ^ ku * (fd ν + 1) + 3 * Ku * fov ν * fd ν + 3) +
      (3 * Kd * lg ν ^ kd * (fd ν + 1) + 3 * Kd * fov ν * fd ν + 3) + qs ν + qs ν +
      (K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν))) *
      (lg (ν ^ (wexp + 1)) + 1),
    ((IsPL.const 8).mul hQ).mul (hL.add (IsPL.const 1)), Kδa + Kδs + Kδu + Kδd,
    fun ν => topAlg T (lg (ν ^ (wexp + 1))) (Aa ν) (As ν) (Au ν 2) (Ad ν 2), ?_⟩
  intro V _ _ N ν hν hνn hw E X hE s
  have hj : (Fintype.equivFin V s : ℕ) < Fintype.card V := (Fintype.equivFin V s).isLt
  have hν1 : 1 ≤ ν := le_trans (Fintype.card_pos_iff.2 ⟨s⟩) hν
  -- failure probabilities
  set Kδ := Kδa + Kδs + Kδu + Kδd with hKδ
  set η : ℝ := ((qδa ν + qδs ν + 1 : ℕ) : ℝ) * whp Kδ c ν with hη
  have hw0 := whp_nonneg Kδ c ν
  have hη0 : 0 ≤ η := by positivity
  have hle1 : ∀ K' ≤ Kδ, ∀ x : ℕ, x ≤ qδa ν + qδs ν + 1 → (x : ℝ) * whp K' c ν ≤ η := by
    intro K' hK' x hx
    exact mul_le_mul (by exact_mod_cast hx) (whp_mono_K hK' c ν) (whp_nonneg _ _ _)
      (Nat.cast_nonneg _)
  have hδa : (qδa ν : ℝ) * whp Kδa c ν ≤ η := hle1 _ (by omega) _ (by omega)
  have hδs : (qδs ν : ℝ) * whp Kδs c ν ≤ η := hle1 _ (by omega) _ (by omega)
  have hδu : whp Kδu c ν ≤ η := by simpa using hle1 Kδu (by omega) 1 (by omega)
  have hδd : whp Kδd c ν ≤ η := by simpa using hle1 Kδd (by omega) 1 (by omega)
  -- the message bound `ν^(wexp+1)`
  have hBx : ∀ v, N.wdist s v + ν ^ wexp ≤ ν ^ (wexp + 1) := by
    intro v
    have h1 := wdist_add_le N s v hw
    have h2 : Fintype.card V * ν ^ wexp ≤ ν ^ (wexp + 1) :=
      calc Fintype.card V * ν ^ wexp ≤ ν * ν ^ wexp := Nat.mul_le_mul_right _ hν
        _ = ν ^ (wexp + 1) := by ring
    omega
  have P : Prims T N E (Fintype.equivFin V s : ℕ) s (ν ^ wexp) (ν ^ (wexp + 1)) (Aa ν) (As ν)
      (Au ν 2) (Ad ν 2) (qa ν) (qs ν) (3 * Ku * lg ν ^ ku * (fd ν + 1) + 3 * Ku * fov ν * fd ν + 3)
      (3 * Kd * lg ν ^ kd * (fd ν + 1) + 3 * Kd * fov ν * fd ν + 3)
      (K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν)) η :=
    { hAa := fun S w0 hconn hbnd =>
        T.mono (hA N ν hν hνn (fun e he => hw e (N.G.mem_edgeFinset.1 he)) E X hE _ S.card S w0 hj le_rfl hconn hbnd _
          subset_rfl) le_rfl hδa
      hAm := fun sz Pt S hsz hPt => T.mono (hS N ν hν hνn E X hE _ sz S hj hsz Pt hPt) le_rfl hδs
      ovh := fun S => ovh_cost hE (K0of T) _ S
      hAu := fun S x hx1 hx2 =>
        T.mono (hU N ν hν hνn E _ S.card _ S 2 x hE.valid hj le_rfl subset_rfl hx1 hx2)
          (agg_cost hE Ku ku ν _ S) hδu
      hAd := fun S x hx1 hx2 =>
        T.mono (hD N ν hν hνn E _ S.card _ S 2 x hE.valid hj le_rfl subset_rfl hx1 hx2)
          (agg_cost hE Kd kd ν _ S) hδd
      valid := hE.valid
      hj := hj
      sub := hE.sub
      cover := hE.valid.cover
      hW := hw
      hB1 := Nat.one_le_pow _ _ hν1
      hBx := hBx
      η0 := hη0 }
  set L := lg (ν ^ (wexp + 1)) with hLdef
  have hlt : ∀ v, N.wdist s v < 2 ^ L := fun v =>
    lt_of_le_of_lt (by have := hBx v; omega) (lt_two_pow_lg _)
  have main := gt_impl P le_rfl L univ (topW0 s) 0 (connSet_univ N s)
    (valid_top N s (ν ^ wexp) L hlt)
  rw [Finset.card_univ, footprint_univ] at main
  set Q := qa ν + qs ν + qs ν + (K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν)) +
      (3 * Ku * lg ν ^ ku * (fd ν + 1) + 3 * Ku * fov ν * fd ν + 3) +
      (3 * Kd * lg ν ^ kd * (fd ν + 1) + 3 * Kd * fov ν * fd ν + 3) + qs ν + qs ν +
      (K0of T * (fd ν + 1) ^ 2 + K0of T * (fov ν * fd ν)) with hQdef
  set j := (Fintype.equivFin V s : ℕ) with hjdef
  -- participation: every node is in at most `4(L+1)` windows
  have hsumN : ∑ v, Nw (N.wdist s v) L 0 ≤ 4 * (L + 1) * ν := by
    calc ∑ v, Nw (N.wdist s v) L 0 ≤ ∑ _v : V, 4 * (L + 1) := sum_le_sum (fun v _ => Nw_le _ _ _)
      _ = Fintype.card V * (4 * (L + 1)) := by rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ 4 * (L + 1) * ν := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hν
  have hcost : (0 : Prof V) + (costB N E j s Q L univ 0 + 0) ≤
      Prof.mk (8 * Q * (L + 1) * ν) (fun e => 8 * Q * (L + 1) * E.rho N.G j univ e)
        (8 * Q * (L + 1) * ν) := by
    rw [zero_add, add_zero]
    unfold costB
    have hr : Q * (2 * ∑ v, Nw (N.wdist s v) L 0) ≤ 8 * Q * (L + 1) * ν := by
      calc Q * (2 * ∑ v, Nw (N.wdist s v) L 0) ≤ Q * (2 * (4 * (L + 1) * ν)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsumN)
        _ = 8 * Q * (L + 1) * ν := by ring
    refine Prof.le_mk _ _ _ _ hr (fun e => ?_) hr
    simp only [Prof.load_mk]
    calc Q * ∑ v, Nw (N.wdist s v) L 0 * hg N.G E j v e ≤ Q * ∑ v, 4 * (L + 1) * hg N.G E j v e :=
          Nat.mul_le_mul_left _ (sum_le_sum (fun v _ => Nat.mul_le_mul_right _ (Nw_le _ _ _)))
      _ = Q * (4 * (L + 1)) * ∑ v, hg N.G E j v e := by rw [← Finset.mul_sum]; ring
      _ ≤ Q * (4 * (L + 1)) * (2 * E.rho N.G j univ e) :=
          Nat.mul_le_mul_left _ (sum_hg_le N.G E j e)
      _ = 8 * Q * (L + 1) * E.rho N.G j univ e := by ring
  have hδ : (0 : ℝ) + (δB N s η L univ 0 + 0) ≤
      ((28 * (qδa ν + qδs ν + 1) * (L + 1) * ν : ℕ) : ℝ) * whp Kδ c ν := by
    rw [zero_add, add_zero]
    unfold δB
    have h1 : ((∑ v, Nw (N.wdist s v) L 0 : ℕ) : ℝ) ≤ ((4 * (L + 1) * ν : ℕ) : ℝ) := by
      exact_mod_cast hsumN
    calc ((∑ v, Nw (N.wdist s v) L 0 : ℕ) : ℝ) * (7 * η) ≤ ((4 * (L + 1) * ν : ℕ) : ℝ) * (7 * η) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by rw [hη]; push_cast; ring
  refine T.mono (T.bind (q := costB N E j s Q L univ 0 + 0) (δ' := δB N s η L univ 0 + 0)
    (T.locR topInF N E j (Fintype.card V) univ (fun _ => s)) (fun y hy => ?_)
    (by rw [add_zero]; exact δB_nonneg hη0 _ _ _)) hcost hδ
  have hy' : y = subInput univ (topW0 s) := funext (fun g => by
    rw [hy g]; cases g <;> simp [topInF, subInput])
  subst hy'
  refine T.bind (T.frameCall (Γ := fun V => V) (fun _ => s) main) (fun o ho => ?_) le_rfl
  refine T.weakenIO (fun out hout => ?_) (T.locR topOutF N E j (Fintype.card V) univ _)
  have hfun : (fun v => out (.inl v)) = fun v => (o (.inl v)).getD (0, s) :=
    funext (fun v => hout (.inl v))
  rw [hfun]
  exact top_out N s L hlt (fun v => o (.inl v)) ho

end APSP.Stoc
