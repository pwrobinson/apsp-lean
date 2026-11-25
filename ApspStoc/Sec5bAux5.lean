import ApspStoc.Sec5bAux4

/-!
# Theorem 5.5, auxiliary file 5: the recursion as a toolkit judgement

By induction on the height `k`, the call `recAlg k` on a connected set `S` with virtual edges
`w0` satisfying `Valid` (offset `a`) solves `ThreshSpec` with threshold `2^k`, within the cost
`costB` and failure probability `δB`. The building blocks are given abstractly (`Prims`).

A call on `S` has the public size bound `|S|` and the participants `footprint E j S` (the nodes
of `S`, the relays on their aggregator paths and the hosts of their aggregators). All its blocks
run on these participants (blocks on subsets `S₁ ⊆ S` included, since
`footprint E j S₁ ⊆ footprint E j S`); the component traversal (`perCompR`) is called with
`P = S`, and the recursive call on a component `K` runs on `footprint E j K`, which is exactly
the induction hypothesis.
-/

namespace APSP.Stoc

open APSP Finset

/-- the constant of `perCompR` -/
noncomputable def K0of (T : Toolkit) : ℕ := Classical.choose T.perCompR

/-- The building blocks used by the recursion, with their specifications on a fixed network:
approximate SSSP (Lemma 5.4), MST (for the component traversals), and the two directions of the
aggregator exchange (Lemma 2.2), with message bound `B`. A block on `S` runs on the participants
`footprint E j S` (MST: on any participant set containing it); `ovh` bounds the overhead of the
component traversal (`perCompR`) on `P = S`. -/
structure Prims (T : Toolkit) {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (E : Overlays V)
    (j : ℕ) (s : V) (W B : ℕ) (Aa Am Au Ad : T.Alg) (qa qm qu qd qo : ℕ) (η : ℝ) : Prop where
  hAa : ∀ (S : Finset V) (w0 : V → Option (ℕ × V)), ConnSet N.G S →
    (∀ v c p, w0 v = some (c, p) → c ≤ W) →
    T.Impl Aa N (.io E j S.card (footprint E j S) (SubIn V) (Option (ℕ × V)) (subInput S w0)
      (fun y => ApproxSpec N S w0 (fun v => y (.inl v)))) (subsetProf N.G E j S qa) η
  hAm : ∀ (sz : ℕ) (Pt S : Finset V), S.card ≤ sz → footprint E j S ⊆ Pt →
    T.Impl Am N (.mst E j sz Pt S) (szProf N.G E j sz S qm) η
  ovh : ∀ S : Finset V,
    Prof.mk (K0of T * (E.dil + 1) ^ 2 * (S.card + 1)) (fun e => K0of T * E.rho N.G j S e)
      (K0of T * (S.card + 1) + K0of T * E.aggLen j S) ≤ subsetProf N.G E j S qo
  hAu : ∀ (S : Finset V) (x : Agent V → Option (Msg V)), (∀ v, x (.inl v) ≠ none → v ∈ S) →
    (∀ v m, x (.inl v) = some m → m.Small 2 B) →
    T.Impl Au N (.io E j S.card (footprint E j S) (Option (Msg V)) (V → Option (Msg V)) x
      (fun y => ∀ C ∈ E.cl, ∀ v, y (.inr C) v = if v ∈ nodes C then x (.inl v) else none))
      (subsetProf N.G E j S qu) η
  hAd : ∀ (S : Finset V) (x : Agent V → V → Option (Msg V)),
    (∀ C ∈ E.cl, ∀ v, x (.inr C) v ≠ none → v ∈ S ∧ v ∈ nodes C) →
    (∀ C ∈ E.cl, ∀ v m, x (.inr C) v = some m → m.Small 2 B) →
    T.Impl Ad N (.io E j S.card (footprint E j S) (V → Option (Msg V)) (Multiset (Msg V)) x
      (fun y => ∀ v, y (.inl v) = (clustersOf E.cl v).val.filterMap (fun C => x (.inr C) v)))
      (subsetProf N.G E j S qd) η
  valid : EmbValid N.G E
  hj : j < Fintype.card V
  sub : ∀ C ∈ E.cl, C ⊆ N.G.edgeFinset
  cover : ∀ e ∈ N.G.edgeFinset, ∃ C ∈ E.cl, e ∈ C
  hW : ∀ e ∈ N.G.edgeSet, N.w e ≤ W
  hB1 : 1 ≤ B
  hBx : ∀ v, N.wdist s v + W ≤ B
  η0 : 0 ≤ η

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The states after the stages -/

def stA (S : Finset V) (w0 : V → Option (ℕ × V)) (ya : Agent V → Option (ℕ × V)) :
    Agent V → GS V := fun g => initGS (subInput S w0 g) (ya g)

def stB (st : Agent V → GS V) (o1 : Agent V → Option (ℕ × V)) : Agent V → GS V :=
  fun g => { st g with o1 := o1 g }

def stC (st : Agent V → GS V) (yup : Agent V → V → Option (Msg V)) : Agent V → GS V :=
  fun g => { st g with up := yup g }

def stD (st : Agent V → GS V) (yr : Agent V → Multiset (Msg V)) : Agent V → GS V :=
  fun g => { st g with recv := yr g }

section Glue
variable (N : WNet V) (S : Finset V) (w0 : V → Option (ℕ × V)) (δ : ℕ)
  (ya o1 o2 : Agent V → Option (ℕ × V)) (yup : Agent V → V → Option (Msg V))
  (yr : Agent V → Multiset (Msg V))

lemma in2_stA (g : Agent V) :
    in2F δ V g (lview N g) (stA S w0 ya g) =
      ((memAg S g, memAg (s1Set S δ (fun v => ya (.inl v))) g), (subInput S w0 g).2) := by
  cases g with
  | inl v => simp [in2F, stA, initGS, GS.in1, subInput, memAg, mem_s1Set]
  | inr C => rfl

lemma in3_inl (v : V) :
    in3F δ V (.inl v) (lview N (.inl v)) (stB (stA S w0 ya) o1 (.inl v)) =
      msgOf (s1Set S δ (fun v => ya (.inl v))) (fun v => o1 (.inl v)) v := by
  simp only [in3F, GS.upMsg, msgOf, stB, stA, initGS, GS.in1, subInput, mem_s1Set]
  by_cases hv : v ∈ S <;> simp [hv]

lemma in5_stD (E : Overlays V)
    (hyr : ∀ v, yr (.inl v) = recvOf N E (fun C => yup (.inr C)) v) (g : Agent V) :
    in5F δ V g (lview N g) (stD (stC (stB (stA S w0 ya) o1) yup) yr g) =
      ((memAg S g, memAg (tSet (s1Set S δ (fun v => ya (.inl v))) (fun v => o1 (.inl v))) g),
        (subInput S (w2Of (tSet (s1Set S δ (fun v => ya (.inl v))) (fun v => o1 (.inl v))) δ w0
          (recvOf N E (fun C => yup (.inr C)))) g).2) := by
  cases g with
  | inl v =>
    simp only [in5F, GS.z2, GS.inT, GS.in1, stD, stC, stB, stA, initGS, subInput, memAg,
      w2Of, w1Of, mem_tSet, mem_s1Set, hyr]
    by_cases hv : v ∈ S <;> by_cases hl : leB (3 * δ) (ya (.inl v)) = true <;>
      cases ho : (o1 (.inl v)).isSome <;> simp [hv, hl, ho]
  | inr C => rfl

lemma out_stD (E : Overlays V) (v : V) :
    upd5F δ V (.inl v) (lview N (.inl v)) (stD (stC (stB (stA S w0 ya) o1) yup) yr (.inl v))
      (o2 (.inl v)) =
      outOf (s2Set (s1Set S δ (fun v => ya (.inl v))) (fun v => o1 (.inl v)))
        (tSet (s1Set S δ (fun v => ya (.inl v))) (fun v => o1 (.inl v))) δ
        (fun v => o1 (.inl v)) (fun v => o2 (.inl v)) v := by
  simp only [upd5F, finalOut, GS.in2, GS.inT, GS.in1, stD, stC, stB, stA, initGS, subInput,
    outOf, mem_s2Set, mem_tSet, mem_s1Set]
  by_cases hv : v ∈ S <;> by_cases hl : leB (3 * δ) (ya (.inl v)) = true <;>
    by_cases ho : (o1 (.inl v)).isSome = true <;> simp [hv, hl, ho]

end Glue

lemma threshSpec_congr {N : WNet V} {S : Finset V} {w0 : V → Option (ℕ × V)} {Δ : ℕ}
    {o o' : V → Option (ℕ × V)} (h : ∀ v ∈ S, o v = o' v) (ho : ThreshSpec N S w0 Δ o) :
    ThreshSpec N S w0 Δ o' := by
  intro v hv
  rw [← h v hv]; exact ho v hv

lemma threshSpec_local {N : WNet V} {w0 : V → Option (ℕ × V)} {Δ : ℕ} (K : Finset V)
    (y y' : Agent V → Option (ℕ × V)) (h : ∀ v ∈ K, y (.inl v) = y' (.inl v))
    (hy : ThreshSpec N K w0 Δ (fun v => y (.inl v))) :
    ThreshSpec N K w0 Δ (fun v => y' (.inl v)) :=
  threshSpec_congr (o := fun v => y (.inl v)) (o' := fun v => y' (.inl v)) h hy

lemma subInput_memAg (K S : Finset V) (w0 : V → Option (ℕ × V)) :
    (fun g => (memAg K g, (subInput S w0 g).2)) = subInput K w0 := by
  funext g; cases g <;> rfl

lemma δB_nonneg {N : WNet V} {s : V} {η : ℝ} (hη : 0 ≤ η) (k : ℕ) (S : Finset V) (a : ℕ) :
    0 ≤ δB N s η k S a :=
  mul_nonneg (Nat.cast_nonneg _) (by linarith)

/-! ## The induction -/

section Main
variable {T : Toolkit} {N : WNet V} {E : Overlays V} {j : ℕ} {s : V} {W B : ℕ}
  {Aa Am Au Ad : T.Alg} {qa qm qu qd qo : ℕ} {η : ℝ}

/-- Base case (Step 2, `Δ = 1`): the `3/2`-approximation is exact for distances `≤ 1`. -/
theorem base_impl (P : Prims T N E j s W B Aa Am Au Ad qa qm qu qd qo η) {Q : ℕ} (hQa : qa ≤ Q)
    {S : Finset V} {w0 : V → Option (ℕ × V)} {a : ℕ} (hS : ConnSet N.G S)
    (hV : Valid N s W 0 S w0 a) :
    T.Impl (recAlg T Aa Am Au Ad 0) N (.io E j S.card (footprint E j S) (SubIn V) (Option (ℕ × V)) (subInput S w0)
      (fun y => ThreshSpec N S w0 (2 ^ 0) (fun v => y (.inl v))))
      (costB N E j s Q 0 S a) (δB N s η 0 S a) := by
  have h1 : ∀ v ∈ S, 1 ≤ Nw (N.wdist s v) 0 a :=
    fun v hv => one_le_Nw hV.dvd (hV.win v hv).1 (hV.win v hv).2
  have hc : subsetProf N.G E j S qa + 0 ≤ costB N E j s Q 0 S a := by
    rw [add_zero]; exact own_le hS.1 h1 hQa
  have hδ : η + 0 ≤ δB N s η 0 S a := by
    have := ownδ_le (N := N) (s := s) P.η0 hS.1 h1
    have := P.η0
    linarith
  rw [recAlg]
  refine T.mono (T.bind (q := 0) (δ' := 0) (P.hAa S w0 hS hV.bnd) (fun y hy => ?_) le_rfl) hc hδ
  refine T.weakenIO (fun out hout => ?_) (T.locR baseF N E j S.card _ _)
  rw [pow_zero]
  exact threshSpec_congr (fun v _ => (hout (.inl v)).symm) (base_correct N hy)

/-- Induction step (Steps 1, 3–7). -/
theorem step_impl (P : Prims T N E j s W B Aa Am Au Ad qa qm qu qd qo η) {Q k : ℕ}
    (hQ : qa + qm + qm + qo + qu + qd + qm + qm + qo ≤ Q)
    (IH : ∀ (S : Finset V) (w0 : V → Option (ℕ × V)) (a : ℕ), ConnSet N.G S →
      Valid N s W k S w0 a →
      T.Impl (recAlg T Aa Am Au Ad k) N (.io E j S.card (footprint E j S) (SubIn V) (Option (ℕ × V)) (subInput S w0)
        (fun y => ThreshSpec N S w0 (2 ^ k) (fun v => y (.inl v))))
        (costB N E j s Q k S a) (δB N s η k S a))
    {S : Finset V} {w0 : V → Option (ℕ × V)} {a : ℕ} (hS : ConnSet N.G S)
    (hV : Valid N s W (k + 1) S w0 a) :
    T.Impl (recAlg T Aa Am Au Ad (k + 1)) N (.io E j S.card (footprint E j S) (SubIn V) (Option (ℕ × V)) (subInput S w0)
      (fun y => ThreshSpec N S w0 (2 ^ (k + 1)) (fun v => y (.inl v))))
      (costB N E j s Q (k + 1) S a) (δB N s η (k + 1) S a) := by
  have hK0 := Classical.choose_spec T.perCompR
  have hNw : ∀ v ∈ S, 1 + Nw (N.wdist s v) k a + Nw (N.wdist s v) k (a + 2 ^ k) ≤
      Nw (N.wdist s v) (k + 1) a := fun v hv => Nw_succ hV.dvd (hV.win v hv).1 (hV.win v hv).2
  have hcost : subsetProf N.G E j S qa + 0 +
      ((subsetProf N.G E j S qm + subsetProf N.G E j S qm + costB N E j s Q k S a +
          subsetProf N.G E j S qo) +
        (subsetProf N.G E j S qu + (subsetProf N.G E j S qd +
          (subsetProf N.G E j S qm + subsetProf N.G E j S qm + costB N E j s Q k S (a + 2 ^ k) +
            subsetProf N.G E j S qo)))) ≤ costB N E j s Q (k + 1) S a := by
    have heq : subsetProf N.G E j S qa + 0 +
        ((subsetProf N.G E j S qm + subsetProf N.G E j S qm + costB N E j s Q k S a +
          subsetProf N.G E j S qo) +
          (subsetProf N.G E j S qu + (subsetProf N.G E j S qd +
            (subsetProf N.G E j S qm + subsetProf N.G E j S qm + costB N E j s Q k S (a + 2 ^ k) +
              subsetProf N.G E j S qo)))) =
        subsetProf N.G E j S (qa + qm + qm + qo + qu + qd + qm + qm + qo) +
          (costB N E j s Q k S a + costB N E j s Q k S (a + 2 ^ k)) := by
      simp only [← subsetProf_add]; abel
    rw [heq]; exact step_cost hS.1 hNw hQ
  have hδ : η + 0 + ((η + η + δB N s η k S a) + (η + (η + (η + η + δB N s η k S (a + 2 ^ k))))) ≤
      δB N s η (k + 1) S a := by
    have := step_δ (N := N) (s := s) P.η0 hS.1 hNw; linarith
  rw [recAlg]; unfold stepAlg
  -- Step 1: approximate SSSP from the virtual source
  have J1 : T.Impl (T.seq Aa (T.loc initF)) N (.io E j S.card (footprint E j S) (SubIn V) (GS V) (subInput S w0)
      (fun st => ∃ ya : Agent V → Option (ℕ × V), ApproxSpec N S w0 (fun v => ya (.inl v)) ∧
        st = stA S w0 ya)) (subsetProf N.G E j S qa + 0) (η + 0) :=
    T.bind (P.hAa S w0 hS hV.bnd) (fun ya hya =>
      T.weakenIO (fun st hst => ⟨ya, hya, funext hst⟩) (T.locR initF N E j S.card _ _)) le_rfl
  have hη := P.η0
  have hδ0 := δB_nonneg (N := N) (s := s) P.η0 k S
  refine T.mono (T.bind J1 (fun st1 h1 => ?_) (by linarith [hδ0 a, hδ0 (a + 2 ^ k)])) hcost hδ
  obtain ⟨ya, hya, rfl⟩ := h1
  -- Steps 3–4: leaders of the components of `S₁` and the first recursive calls
  have PC1 : T.Impl (T.perComp (fun V => Option (ℕ × V)) (fun V => Option (ℕ × V)) Am
      (recAlg T Aa Am Au Ad k)) N
      (.io E j S.card (footprint E j S) ((Bool × Bool) × Option (ℕ × V)) (Option (ℕ × V))
        (fun g => ((memAg S g, memAg (s1Set S (2 ^ k) (fun v => ya (.inl v))) g),
          (subInput S w0 g).2))
        (fun y => ∀ K ∈ comps N.G (s1Set S (2 ^ k) (fun v => ya (.inl v))),
          ThreshSpec N K w0 (2 ^ k) (fun v => y (.inl v))))
      (subsetProf N.G E j S qm + subsetProf N.G E j S qm + costB N E j s Q k S a +
          subsetProf N.G E j S qo)
      (η + η + δB N s η k S a) := by
    refine T.mono (hK0 (fun V => Option (ℕ × V)) (fun V => Option (ℕ × V)) Am
      (recAlg T Aa Am Au Ad k) N E j S.card S
      (s1Set S (2 ^ k) (fun v => ya (.inl v))) (fun g => (subInput S w0 g).2)
      (fun K y => ThreshSpec N K w0 (2 ^ k) (fun v => y (.inl v)))
      (szProf N.G E j S.card S qm)
      (szProf N.G E j S.card (s1Set S (2 ^ k) (fun v => ya (.inl v))) qm)
      η η (fun K => costB N E j s Q k K a) (fun K => δB N s η k K a)
      P.valid P.hj s1_sub hS le_rfl threshSpec_local (P.hAm S.card _ S le_rfl subset_rfl)
      (P.hAm S.card _ _ (card_le_card s1_sub) (footprint_mono E j s1_sub)) (fun K hK => ?_)) ?_ ?_
    · have h := IH K w0 a (comps_conn N.G hK) (valid_first hya hV hK)
      rw [← subInput_memAg K S w0] at h
      exact h
    · exact add_le_add (add_le_add (add_le_add le_rfl (szProf_mono N.G E j le_rfl s1_sub qm))
        (sum_costB_le s1_sub)) (P.ovh S)
    · exact add_le_add le_rfl (sum_δB_le P.η0 s1_sub)
  have J2 : T.Impl (stageAlg T SubIn (fun V => (Bool × Bool) × Option (ℕ × V))
      (fun V => Option (ℕ × V)) GS (in2F (2 ^ k))
      (T.perComp (fun V => Option (ℕ × V)) (fun V => Option (ℕ × V)) Am (recAlg T Aa Am Au Ad k))
      upd2F) N
      (.io E j S.card (footprint E j S) (SubIn V × GS V) (GS V) (fun g => (subInput S w0 g, stA S w0 ya g))
        (fun out => ∃ o1 : Agent V → Option (ℕ × V),
          (∀ K ∈ comps N.G (s1Set S (2 ^ k) (fun v => ya (.inl v))),
            ThreshSpec N K w0 (2 ^ k) (fun v => o1 (.inl v))) ∧
          out = stB (stA S w0 ya) o1))
      (subsetProf N.G E j S qm + subsetProf N.G E j S qm + costB N E j s Q k S a +
          subsetProf N.G E j S qo)
      (η + η + δB N s η k S a) :=
    T.weakenIO (fun out h => by
        obtain ⟨o, ho, hout⟩ := h
        exact ⟨o, ho, funext hout⟩)
      (stage_impl T (subInput S w0) (stA S w0 ya) _ (in2_stA N S w0 (2 ^ k) ya) PC1
        (by linarith [hδ0 a]))
  refine T.bind J2 (fun st2 h2 => ?_) (by linarith [hδ0 (a + 2 ^ k)])
  obtain ⟨o1, ho1, rfl⟩ := h2
  -- Step 5, first half: nodes of `S₁` report to their aggregators
  have H0 : StepHyp N E S w0 (2 ^ k) (fun v => ya (.inl v)) (fun v => o1 (.inl v))
      (fun C v => if v ∈ nodes C then
        msgOf (s1Set S (2 ^ k) (fun v => ya (.inl v))) (fun v => o1 (.inl v)) v else none) :=
    ⟨hya, ho1, P.sub, P.cover, fun C _ v => rfl⟩
  have PU := P.hAu S (fun g => in3F (2 ^ k) V g (lview N g) (stB (stA S w0 ya) o1 g))
    (fun v hv => msg_mem s1_sub (by simpa only [in3_inl] using hv))
    (fun v m hm => msg_small H0 hV P.hB1 P.hBx v m (by simpa only [in3_inl] using hm))
  have J3 : T.Impl (stageAlg T (fun V => SubIn V × GS V) (fun V => Option (Msg V))
      (fun V => V → Option (Msg V)) GS (in3F (2 ^ k)) Au upd3F) N
      (.io E j S.card (footprint E j S) ((SubIn V × GS V) × GS V) (GS V)
        (fun g => ((subInput S w0 g, stA S w0 ya g), stB (stA S w0 ya) o1 g))
        (fun out => ∃ yup : Agent V → V → Option (Msg V),
          (∀ C ∈ E.cl, ∀ v, yup (.inr C) v = if v ∈ nodes C then
            msgOf (s1Set S (2 ^ k) (fun v => ya (.inl v))) (fun v => o1 (.inl v)) v else none) ∧
          out = stC (stB (stA S w0 ya) o1) yup)) (subsetProf N.G E j S qu) η :=
    T.weakenIO (fun out h => by
        obtain ⟨o, ho, hout⟩ := h
        refine ⟨o, fun C hC v => ?_, funext hout⟩
        simp only [ho C hC v, in3_inl])
      (stage_impl T (Pre := fun V => SubIn V × GS V) (fun g => (subInput S w0 g, stA S w0 ya g))
        (stB (stA S w0 ya) o1) _ (fun g => rfl) PU hη)
  refine T.bind J3 (fun st3 h3 => ?_) (by linarith [hδ0 (a + 2 ^ k)])
  obtain ⟨yup, hyup, rfl⟩ := h3
  have H : StepHyp N E S w0 (2 ^ k) (fun v => ya (.inl v)) (fun v => o1 (.inl v))
      (fun C => yup (.inr C)) := ⟨hya, ho1, P.sub, P.cover, hyup⟩
  -- Step 5, second half: the aggregators answer with the best Bellman–Ford candidate
  have PD := P.hAd S (fun g => in4F V g (lview N g) (stC (stB (stA S w0 ya) o1) yup g))
    (dn_mem H) (dn_small H hV P.hW P.hBx)
  have J4 : T.Impl (stageAlg T (fun V => (SubIn V × GS V) × GS V) (fun V => V → Option (Msg V))
      (fun V => Multiset (Msg V)) GS in4F Ad upd4F) N
      (.io E j S.card (footprint E j S) (((SubIn V × GS V) × GS V) × GS V) (GS V)
        (fun g => (((subInput S w0 g, stA S w0 ya g), stB (stA S w0 ya) o1 g),
          stC (stB (stA S w0 ya) o1) yup g))
        (fun out => ∃ yr : Agent V → Multiset (Msg V),
          (∀ v, yr (.inl v) = recvOf N E (fun C => yup (.inr C)) v) ∧
          out = stD (stC (stB (stA S w0 ya) o1) yup) yr)) (subsetProf N.G E j S qd) η :=
    T.weakenIO (fun out h => by
        obtain ⟨o, ho, hout⟩ := h
        exact ⟨o, ho, funext hout⟩)
      (stage_impl T (Pre := fun V => (SubIn V × GS V) × GS V)
        (fun g => ((subInput S w0 g, stA S w0 ya g), stB (stA S w0 ya) o1 g))
        (stC (stB (stA S w0 ya) o1) yup) _ (fun g => rfl) PD hη)
  refine T.bind J4 (fun st4 h4 => ?_) (by linarith [hδ0 (a + 2 ^ k)])
  obtain ⟨yr, hyr, rfl⟩ := h4
  -- Steps 6–7: leaders of the components of `S₁ \ S₂` and the second recursive calls
  have PC2 : T.Impl (T.perComp (fun V => Option (ℕ × V)) (fun V => Option (ℕ × V)) Am
      (recAlg T Aa Am Au Ad k)) N
      (.io E j S.card (footprint E j S) ((Bool × Bool) × Option (ℕ × V)) (Option (ℕ × V))
        (fun g => ((memAg S g, memAg (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v)))
            (fun v => o1 (.inl v))) g),
          (subInput S (w2Of (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v))) (fun v => o1 (.inl v)))
            (2 ^ k) w0 (recvOf N E (fun C => yup (.inr C)))) g).2))
        (fun y => ∀ K ∈ comps N.G (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v)))
            (fun v => o1 (.inl v))),
          ThreshSpec N K (w2Of (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v)))
            (fun v => o1 (.inl v))) (2 ^ k) w0 (recvOf N E (fun C => yup (.inr C))))
            (2 ^ k) (fun v => y (.inl v))))
      (subsetProf N.G E j S qm + subsetProf N.G E j S qm + costB N E j s Q k S (a + 2 ^ k) +
        subsetProf N.G E j S qo)
      (η + η + δB N s η k S (a + 2 ^ k)) := by
    refine T.mono (hK0 (fun V => Option (ℕ × V)) (fun V => Option (ℕ × V)) Am
      (recAlg T Aa Am Au Ad k) N E j S.card S
      (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v))) (fun v => o1 (.inl v)))
      (fun g => (subInput S (w2Of (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v)))
        (fun v => o1 (.inl v))) (2 ^ k) w0 (recvOf N E (fun C => yup (.inr C)))) g).2)
      (fun K y => ThreshSpec N K (w2Of (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v)))
        (fun v => o1 (.inl v))) (2 ^ k) w0 (recvOf N E (fun C => yup (.inr C))))
        (2 ^ k) (fun v => y (.inl v)))
      (szProf N.G E j S.card S qm)
      (szProf N.G E j S.card
        (tSet (s1Set S (2 ^ k) (fun v => ya (.inl v))) (fun v => o1 (.inl v))) qm)
      η η (fun K => costB N E j s Q k K (a + 2 ^ k))
      (fun K => δB N s η k K (a + 2 ^ k))
      P.valid P.hj tSet_sub_S hS le_rfl threshSpec_local (P.hAm S.card _ S le_rfl subset_rfl)
      (P.hAm S.card _ _ (card_le_card tSet_sub_S) (footprint_mono E j tSet_sub_S))
      (fun K hK => ?_)) ?_ ?_
    · have h := IH K _ (a + 2 ^ k) (comps_conn N.G hK) (valid_second H hV P.hW hK)
      rw [← subInput_memAg K S] at h
      exact h
    · exact add_le_add (add_le_add (add_le_add le_rfl (szProf_mono N.G E j le_rfl tSet_sub_S qm))
        (sum_costB_le tSet_sub_S)) (P.ovh S)
    · exact add_le_add le_rfl (sum_δB_le P.η0 tSet_sub_S)
  exact T.weakenIO (fun out h => by
      obtain ⟨o2, ho2, hout⟩ := h
      rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring]
      exact threshSpec_congr (fun v _ =>
        ((hout (.inl v)).trans (out_stD N S w0 (2 ^ k) ya o1 o2 yup yr E v)).symm)
        (out_correct H ho2))
    (stage_impl T (Pre := fun V => ((SubIn V × GS V) × GS V) × GS V)
      (fun g => (((subInput S w0 g, stA S w0 ya g), stB (stA S w0 ya) o1 g),
        stC (stB (stA S w0 ya) o1) yup g)) (stD (stC (stB (stA S w0 ya) o1) yup) yr) _
      (in5_stD N S w0 (2 ^ k) ya o1 yup yr E hyr) PC2 (by linarith [hδ0 (a + 2 ^ k)]))

/-- The recursion is correct and within the participation-based cost bound. -/
theorem gt_impl (P : Prims T N E j s W B Aa Am Au Ad qa qm qu qd qo η) {Q : ℕ}
    (hQ : qa + qm + qm + qo + qu + qd + qm + qm + qo ≤ Q) :
    ∀ (k : ℕ) (S : Finset V) (w0 : V → Option (ℕ × V)) (a : ℕ), ConnSet N.G S →
      Valid N s W k S w0 a →
      T.Impl (recAlg T Aa Am Au Ad k) N (.io E j S.card (footprint E j S) (SubIn V) (Option (ℕ × V)) (subInput S w0)
        (fun y => ThreshSpec N S w0 (2 ^ k) (fun v => y (.inl v))))
        (costB N E j s Q k S a) (δB N s η k S a) := by
  intro k
  induction k with
  | zero => intro S w0 a hS hV; exact base_impl P (by omega) hS hV
  | succ k IH => intro S w0 a hS hV; exact step_impl P hQ IH hS hV

end Main

end APSP.Stoc
