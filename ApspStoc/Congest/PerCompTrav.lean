import ApspStoc.Congest.PerCompPlan

/-!
# The traversal phase (for `perCompR`)

`trav_implI`: after the preparation (the spanning tree of `P`, the spanning forest of `G[S]`, the
component sizes, the children in both), the traversal `travA A Bt B` solves the task within the
costs of the sub-runs plus `O((dil+1)(sz+1))` rounds, load `O(ρ)` and `O(|P|) + O(aggLen j P)`
messages, except with probability `Σ_K δ K`.

The proof: for seeds under which every standalone run of `B` on a component succeeds (union
bound), the global data (`PCG`) with the halting times of these runs is a consistent plan
(`LOK`); by `embOK_of_frames` and `succ_embP` the traversal follows it and succeeds.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The traversal** with sub-runs of `B`. -/
noncomputable def travA (A Bt : Type → Type) (B : CAlg) : CAlg :=
  fun V _ _ => embP (pcCtl A Bt V).toCtl (B V)

/-- the data of the agents for the traversal -/
def x5Of {A : Type → Type} (P S : Finset V) (z : Agent V → A V) (y1 y2 : Agent V → Option V × V)
    (y3 : Agent V → Option (Msg V)) (y4 y5 : Agent V → Finset V) : Agent V → X5 A V :=
  fun g => ((((((((memAg P g, memAg S g), z g), y1 g), y2 g), y3 g), y4 g), y5 g))

open Classical in
/-- **Union bound** over events implying success. -/
lemma failProb_le_sum {P : Proto V} {I : Inst V} {x : Agent V → Mem}
    {Q : (Agent V → Mem) → Prop} {p : Prof V} {ι : Type} (s : Finset ι)
    (Ev : ι → (V → P.Ω) → Prop) (h : ∀ ω, (∀ i ∈ s, Ev i ω) → Succ P I x Q p ω) :
    failProb P I x Q p ≤ ∑ i ∈ s, (((univ.filter (fun ω => ¬ Ev i ω)).card : ℕ) : ℝ) /
      (Fintype.card (V → P.Ω) : ℝ) := by
  classical
  unfold failProb
  rw [← sum_div]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt (card_pos_fun P))
  have : (univ.filter (fun ω => ¬ Succ P I x Q p ω)) ⊆
      s.biUnion (fun i => univ.filter (fun ω => ¬ Ev i ω)) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_contra hno
    apply hω (h ω (fun i hi => ?_))
    by_contra hE
    exact hno (mem_biUnion.2 ⟨i, hi, by simp [hE]⟩)
  exact_mod_cast (card_le_card this).trans card_biUnion_le

lemma ioHost_iff {E : Overlays V} {j : ℕ} {Pt Pt' : Finset V} (h : Pt ⊆ Pt') {v : V}
    (hv : v ∈ Pt) (g : Agent V) : ioHost E j Pt' g = some v ↔ ioHost E j Pt g = some v := by
  cases g with
  | inl u =>
    simp only [ioHost]
    constructor
    · intro h'; split_ifs at h' with hu; cases h'; simp [hv]
    · intro h'; split_ifs at h' with hu; cases h'; simp [h hu]
  | inr C =>
    simp only [ioHost]
    cases aggHost E j C with
    | none => simp
    | some w =>
      simp only
      constructor
      · intro h'; split_ifs at h' with hw; cases h'; simp [hv]
      · intro h'; split_ifs at h' with hw; cases h'; simp [h hw]

lemma ioView_eq (N : WNet V) {E : Overlays V} {j : ℕ} {Pt Pt' : Finset V} (h : Pt ⊆ Pt') {v : V}
    (hv : v ∈ Pt) : ioView N E j Pt' v = ioView N E j Pt v := by
  classical
  funext g
  unfold ioView
  by_cases h1 : ioHost E j Pt g = some v
  · rw [if_pos h1, if_pos ((ioHost_iff h hv g).2 h1)]
  · rw [if_neg h1, if_neg (fun h2 => h1 ((ioHost_iff h hv g).1 h2))]

lemma memIE {G : SimpleGraph V} [DecidableRel G.Adj] {T : Finset V} {a b : V} :
    s(a, b) ∈ inducedEdges G T ↔ G.Adj a b ∧ a ∈ T ∧ b ∈ T := by
  classical
  unfold inducedEdges
  rw [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨h, h2⟩; exact ⟨h, h2 a (Sym2.mem_mk_left a b), h2 b (Sym2.mem_mk_right a b)⟩
  · rintro ⟨h, ha, hb⟩
    refine ⟨h, fun x hx => ?_⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> assumption

section Trav

variable {A Bt : Type → Type} {B : CAlg} [Nonempty (Bt V)] {N : WNet V} {E : Overlays V}
  {j sz : ℕ} {P S : Finset V} {z : Agent V → A V} {R : Finset V → (Agent V → Bt V) → Prop}
  {p : Finset V → Prof V} {δ : Finset V → ℝ}
  {y1 y2 : Agent V → Option V × V} {y3 : Agent V → Option (Msg V)} {y4 y5 : Agent V → Finset V}

/-- the hypotheses of the traversal phase -/
structure TravH (A Bt : Type → Type) (B : CAlg) (N : WNet V) (E : Overlays V) (j sz : ℕ)
    (P S : Finset V) (z : Agent V → A V) (R : Finset V → (Agent V → Bt V) → Prop)
    (p : Finset V → Prof V) (δ : Finset V → ℝ) (y1 y2 : Agent V → Option V × V)
    (y3 : Agent V → Option (Msg V)) (y4 y5 : Agent V → Finset V) : Prop where
  hE : EmbValid N.G E
  hj : j < Fintype.card V
  SP : S ⊆ P
  conn : ConnSet N.G P
  Psz : P.card ≤ sz
  loc : ∀ K y y', (∀ v ∈ K, y (.inl v) = y' (.inl v)) → R K y → R K y'
  hB : ∀ K ∈ comps N.G S, CImplT B N (.io E j K.card (footprint E j K) (Bool × A V) (Bt V)
    (fun g => (memAg K g, z g)) (R K)) (p K) (δ K)
  h1 : SpanForest P (inducedEdges N.G P) (fun v => (y1 (.inl v)).1) (fun v => (y1 (.inl v)).2)
  h2 : SpanForest S (inducedEdges N.G S) (fun v => (y2 (.inl v)).1) (fun v => (y2 (.inl v)).2)
  h3 : ∀ v ∈ S, numW (y3 (.inl v)) =
    (S.filter (fun u => (y2 (.inl u)).2 = (y2 (.inl v)).2)).card
  h4 : ∀ v, y4 (.inl v) = kidsOf P (fun v => (y1 (.inl v)).1) v
  h5 : ∀ v, y5 (.inl v) = kidsOf S (fun v => (y2 (.inl v)).1) v

variable (H : TravH A Bt B N E j sz P S z R p δ y1 y2 y3 y4 y5)
include H

lemma travH_root : ∃ r ∈ P, (y1 (.inl r)).1 = none ∧ ∀ v ∈ P, (y1 (.inl v)).2 = r := by
  obtain ⟨p0, hp0⟩ := H.conn.1
  obtain ⟨rk, hrk⟩ := H.h1.rank
  obtain ⟨h1, h2, -⟩ := root_spec H.h1.mem hrk H.h1.root_par H.h1.root_self hp0
  refine ⟨(y1 (.inl p0)).2, h1, h2, fun v hv => ?_⟩
  exact (H.h1.conn v hv p0 hp0).2 (H.conn.2 v hv p0 hp0)

/-- the global data of the traversal (the durations of the sub-runs are filled in later) -/
noncomputable def PCG0 (y1 y2 : Agent V → Option V × V) (N : WNet V) (E : Overlays V)
    (j sz : ℕ) (P S : Finset V) (r : V) (rkP rkS : V → ℕ) (tB : V → ℕ) : PCG V :=
  ⟨N, E, j, sz, P, S, fun v => (y1 (.inl v)).1, rkP, r, fun v => (y2 (.inl v)).1, rkS,
    fun v => (y2 (.inl v)).2, tB⟩

lemma pcg_ok {r : V} (hr : r ∈ P) (hpr : (y1 (.inl r)).1 = none)
    (hroot : ∀ v ∈ P, (y1 (.inl v)).2 = r) {rkP rkS : V → ℕ}
    (hrkP : ∀ v ∈ P, ∀ u, (y1 (.inl v)).1 = some u → rkP u < rkP v)
    (hrkS : ∀ v ∈ S, ∀ u, (y2 (.inl v)).1 = some u → rkS u < rkS v) (tB : V → ℕ) :
    (PCG0 y1 y2 N E j sz P S r rkP rkS tB).OK where
  hE := H.hE
  hj := H.hj
  SP := H.SP
  Psz := H.Psz
  rP := hr
  parr := hpr
  Pmem := H.h1.mem
  Prk := hrkP
  Pdesc := by
    show desc P (fun v => (y1 (.inl v)).1) r = P
    have hr' : (y1 (.inl r)).2 = r := hroot r hr
    rw [← hr'] at hpr ⊢
    rw [desc_root H.h1.mem hrkP H.h1.root_par H.h1.root_self (hr'.symm ▸ hr) hpr]
    ext v
    simp only [mem_filter, and_iff_left_iff_imp]
    intro hv
    rw [hroot v hv, hr']
  Padj := fun v hv u hu => by
    have := H.h1.edge v hv u hu
    rw [memIE] at this
    exact this.1
  Smem := H.h2.mem
  Srk := hrkS
  Sroot := H.h2.root_par
  Sself := H.h2.root_self
  Sadj := fun v hv u hu => by
    have := H.h2.edge v hv u hu
    rw [memIE] at this
    exact this.1

lemma comps_eq {r : V} {rkP rkS tB : V → ℕ} :
    comps N.G S = (PCG0 y1 y2 N E j sz P S r rkP rkS tB).lds.image
      (PCG0 y1 y2 N E j sz P S r rkP rkS tB).comp := by
  classical
  set X := PCG0 y1 y2 N E j sz P S r rkP rkS tB
  obtain ⟨rk, hrk⟩ := H.h2.rank
  ext K
  unfold comps
  simp only [mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h1, h2, -⟩ := root_spec H.h2.mem hrk H.h2.root_par H.h2.root_self hv
    refine ⟨(y2 (.inl v)).2, PCG.mem_lds.2 ⟨h1, h2⟩, ?_⟩
    ext u
    rw [PCG.mem_comp, mem_filter]
    constructor
    · rintro ⟨hu, he⟩; exact ⟨hu, (H.h2.conn u hu v hv).1 he⟩
    · rintro ⟨hu, he⟩; exact ⟨hu, (H.h2.conn u hu v hv).2 he⟩
  · rintro ⟨ℓ, hℓ, rfl⟩
    obtain ⟨hℓS, hℓp⟩ := PCG.mem_lds.1 hℓ
    refine ⟨ℓ, hℓS, ?_⟩
    have hself : (y2 (.inl ℓ)).2 = ℓ := H.h2.root_self ℓ hℓS hℓp
    ext u
    rw [PCG.mem_comp, mem_filter]
    constructor
    · rintro ⟨hu, he⟩
      exact ⟨hu, by show (y2 (.inl u)).2 = ℓ; rw [(H.h2.conn u hu ℓ hℓS).2 he, hself]⟩
    · rintro ⟨hu, he⟩
      refine ⟨hu, (H.h2.conn u hu ℓ hℓS).1 ?_⟩
      show (y2 (.inl u)).2 = (y2 (.inl ℓ)).2
      rw [hself]; exact he

/-- **The traversal phase.** -/
theorem trav_implI :
    ImplI (travA A Bt B V) (ioInst N E j sz (footprint E j P)) (inOf (x5Of P S z y1 y2 y3 y4 y5))
      (postOf (ioInst N E j sz (footprint E j P))
        (fun y : Agent V → Bt V => ∀ K ∈ comps N.G S, R K y))
      (∑ K ∈ comps N.G S, p K + Prof.mk (30 * (E.dil + 1) * (sz + 1))
        (fun e => 18 * E.rho N.G j P e) (12 * P.card + 6 * E.aggLen j P))
      (∑ K ∈ comps N.G S, δ K) := by
  classical
  obtain ⟨r, hr, hpr, hroot⟩ := travH_root H
  obtain ⟨rkP, hrkP⟩ := H.h1.rank
  obtain ⟨rkS, hrkS⟩ := H.h2.rank
  set X0 := PCG0 y1 y2 N E j sz P S r rkP rkS (fun _ => 0) with hX0def
  have hX0 := pcg_ok H hr hpr hroot hrkP hrkS (fun _ => 0)
  set I := ioInst N E j sz (footprint E j P) with hIdef
  set x := inOf (x5Of P S z y1 y2 y3 y4 y5) with hxdef
  let xs : V → Agent V → Mem := fun ℓ => inOf (fun g => (memAg (X0.comp ℓ) g, z g))
  let Ev : V → (V → (B V).Ω) → Prop := fun ℓ ω =>
    Succ (B V) (X0.J ℓ) (xs ℓ) (postOf (X0.J ℓ) (R (X0.comp ℓ))) (p (X0.comp ℓ)) ω
  have hcomps : comps N.G S = X0.lds.image X0.comp := comps_eq H
  have hinj : Set.InjOn X0.comp X0.lds := by
    intro ℓ hℓ ℓ' hℓ' he
    by_contra hne
    have := PCG.comp_disj hX0 hne
    rw [he] at this
    exact Finset.disjoint_left.1 this (PCG.self_mem_comp hX0 hℓ') (PCG.self_mem_comp hX0 hℓ')
  have hsumK : ∀ f : Finset V → Prof V, ∑ K ∈ comps N.G S, f K = ∑ ℓ ∈ X0.lds, f (X0.comp ℓ) := by
    intro f; rw [hcomps, sum_image hinj]
  unfold ImplI
  refine le_trans (failProb_le_sum (P := travA A Bt B V) (I := I) (x := x) X0.lds Ev
    (fun ω hω => ?_)) ?_
  swap
  · rw [hcomps, sum_image hinj]
    refine sum_le_sum (fun ℓ hℓ => ?_)
    have hK : X0.comp ℓ ∈ comps N.G S := by rw [hcomps]; exact mem_image_of_mem _ hℓ
    exact H.hB _ hK
  -- the durations of the sub-runs
  let tB : V → ℕ := fun ℓ => if h : Ev ℓ ω then h.choose else 0
  set X := PCG0 y1 y2 N E j sz P S r rkP rkS tB with hXdef
  have hX : X.OK := pcg_ok H hr hpr hroot hrkP hrkS tB
  have hrun : ∀ ℓ ∈ X.lds, HaltsAt (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) ∧
      ProperUpTo (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) ∧ X.tB ℓ ≤ (p (X.comp ℓ)).rounds ∧
      msgsUpTo (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) ≤ (p (X.comp ℓ)).msgs ∧
      (∀ e, loadUpTo (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) e ≤ (p (X.comp ℓ)).load e) ∧
      ∃ yy : Agent V → Mem, (∀ g, ((X.J ℓ).host g).isSome →
        outAt (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) g = some (yy g)) ∧
        postOf (X.J ℓ) (R (X.comp ℓ)) yy := by
    intro ℓ hℓ
    have h := hω ℓ hℓ
    have ht : X.tB ℓ = h.choose := by
      show tB ℓ = _; simp only [tB, dif_pos h]
    rw [ht]
    exact h.choose_spec
  -- the local data and contexts
  have hd : ∀ v ∈ footprint E j P, X.LDOK (myD A (inpAt I x v) v) v := by
    intro v hv
    have hinp : inpAt I x v (.inl v) = some ⟨X5 A V, x5Of P S z y1 y2 y3 y4 y5 (.inl v)⟩ := by
      simp [inpAt, hIdef, ioInst, ioHost, hv, hxdef, inOf]
    have hmy : myD A (inpAt I x v) v = ldOf (x5Of P S z y1 y2 y3 y4 y5 (.inl v)) := by
      unfold myD; rw [hinp]; simp
    rw [hmy]
    exact {
      bP := rfl, bS := rfl, parP := rfl, parS := rfl, rtS := rfl,
      rtP := fun hvP => hroot v hvP,
      cnt := fun hvS => by
        show numW (y3 (.inl v)) = (X.comp (X.rtS v)).card
        rw [H.h3 v hvS]
        unfold PCG.comp
        congr 1
      kP := H.h4 v, kS := H.h5 v }
  have hc : ∀ v, X.CtxOK (I.ctx v) v := fun v =>
    ⟨rfl, by simp [dilC, hIdef, ioInst, PCG.dil, hXdef, PCG0],
      by simp [szC, hIdef, ioInst, hXdef, PCG0], by simp [jC, hIdef, ioInst, hXdef, PCG0], rfl⟩
  have hfpsub : ∀ ℓ, footprint E j (X.comp ℓ) ⊆ footprint E j P :=
    fun ℓ => footprint_mono E j (PCG.comp_sub_P hX ℓ)
  -- the plan
  have hLOK : LOK (pcCtl A Bt V) (B V) I x ω X.lds X.J xs X.bOf X.tB
      (fun ℓ v => decide (v ∈ X.comp ℓ)) X.ML X.TL := {
    part := fun ℓ _ v hv => hfpsub ℓ hv
    adj := fun ℓ _ u v h => ⟨h.1, hfpsub ℓ h.2.1, hfpsub ℓ h.2.2⟩
    sep := fun ℓ hℓ ℓ' hℓ' hne => PCG.sub_sep hX hℓ hℓ' hne
    ownU := fun v ℓ _ ℓ' _ _ ho _ ho' => by
      by_contra hne
      exact Finset.disjoint_left.1 (PCG.comp_disj hX hne) (of_decide_eq_true ho)
        (of_decide_eq_true ho')
    b1 := fun ℓ hℓ => PCG.bOf_pos hX hℓ
    bT := fun ℓ hℓ => by
      have := (PCG.bOf_lt_end hX hℓ).2; have := PCG.phEnd_le_TL hX hℓ; omega
    halts := fun ℓ hℓ => (hrun ℓ hℓ).1
    proper := fun ℓ hℓ => (hrun ℓ hℓ).2.1
    Madj := fun φ u v h => by
      obtain ⟨h1, h2, h3⟩ := PCG.ML_adj hX h
      exact ⟨h1, h2, h3⟩
    Mok := fun φ u v w h => PCG.ML_ok hX h
    MB := fun φ u v h => ⟨fun hB => by rw [PCG.ML_LB hX hB] at h; simp at h,
      fun hB => by rw [PCG.ML_LB hX hB] at h; simp at h⟩
    send := fun v hv φ _ hB => PCG.lsend_eq hX (hd v hv) (hc v) hB
    start := fun v hv φ _ _ => by
      refine ⟨fun ℓ hℓ hvℓ hb => ?_, fun hno => PCG.lstart_none hX (hd v hv) (hc v) A _ hno⟩
      subst hb
      show lstart A (I.ctx v) (inpAt I x v) (myD A (inpAt I x v) v) (X.lh v (X.bOf ℓ)) = _
      rw [PCG.lstart_some hX (hd v hv) (hc v) A _ hℓ hvℓ]
      refine congrArg some (Prod.ext ?_ (Prod.ext ?_ rfl))
      · -- the context of the sub-run
        show ctxK (I.ctx v) (X.comp ℓ).card = (X.J ℓ).ctx v
        simp only [ctxK, hIdef, ioInst, PCG.J, hXdef, PCG0]
        rw [ioView_eq N (hfpsub ℓ) hvℓ]
        rfl
      · -- the inputs of the sub-run
        funext g
        unfold inpK
        dsimp only
        by_cases hg : ioHost E j (footprint E j (X.comp ℓ)) g = some v
        · have h1 : inpAt I x v g = some (x g) := by
            unfold inpAt; exact if_pos ((ioHost_iff (hfpsub ℓ) hvℓ g).2 hg)
          have h2 : inpAt (X.J ℓ) (xs ℓ) v g = some (xs ℓ g) := by
            unfold inpAt; exact if_pos hg
          rw [h1, h2]
          simp only [Option.map_some, hxdef, inOf, dif_pos, cast_eq, Option.some.injEq]
          cases g with
          | inl u =>
            have : u = v := by
              simp only [ioHost] at hg; split_ifs at hg; exact Option.some.inj hg
            subst this
            rfl
          | inr C => rfl
        · have h1 : inpAt I x v g = none := by
            unfold inpAt; exact if_neg (fun h' => hg ((ioHost_iff (hfpsub ℓ) hvℓ g).1 h'))
          have h2 : inpAt (X.J ℓ) (xs ℓ) v g = none := by
            unfold inpAt; exact if_neg hg
          rw [h1, h2]
          rfl
    halt := fun v hv φ hφ => PCG.lhalt_iff hX (hd v hv) (hc v) hv hφ }
  have hEmb := embOK_of_frames hLOK
  -- the outputs of the sub-runs
  let d0 : Bt V := Classical.choice inferInstance
  let zOf : V → Agent V → Bt V := fun ℓ => if hℓ : ℓ ∈ X.lds then
    (((hrun ℓ hℓ).2.2.2.2.2.choose_spec).2).choose else fun _ => d0
  have hzOf : ∀ ℓ (hℓ : ℓ ∈ X.lds), (∀ g, ((X.J ℓ).host g).isSome →
      outAt (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) g = some ⟨Bt V, zOf ℓ g⟩) ∧ R (X.comp ℓ) (zOf ℓ) := by
    intro ℓ hℓ
    have h1 := (hrun ℓ hℓ).2.2.2.2.2.choose_spec
    have h2 := h1.2.choose_spec
    simp only [zOf, dif_pos hℓ]
    refine ⟨fun g hg => ?_, h2.2⟩
    rw [h1.1 g hg, h2.1 g hg]
  let zz : Agent V → Bt V := fun g => match g with
    | .inl v => if v ∈ S then zOf (X.rtS v) (.inl v) else d0
    | .inr _ => d0
  have hdflt : dfltM Bt V = ⟨Bt V, d0⟩ := by
    unfold dfltM; rw [dif_pos (show Nonempty (Bt V) from inferInstance)]
  refine succ_embP hEmb (Q := postOf I (fun y : Agent V → Bt V => ∀ K ∈ comps N.G S, R K y))
    ?_ ?_ (fun e => ?_) (fun g => ⟨Bt V, zz g⟩) (fun g w hgw => ?_) ⟨zz, fun _ _ => rfl, ?_⟩
  · -- rounds
    have hTL := PCG.TL_le hX
    have hsplit : ∑ ℓ ∈ X.lds, (3 * X.PiK ℓ + (X.tB ℓ + 2) / 3) =
        3 * (X.dil + 1) * X.S.card + ∑ ℓ ∈ X.lds, (X.tB ℓ + 2) / 3 := by
      rw [sum_add_distrib, ← PCG.sum_comp_card hX, mul_sum]
      congr 1
      refine sum_congr rfl (fun ℓ _ => ?_)
      unfold PCG.PiK PiL
      ring
    have h3 : 3 * ∑ ℓ ∈ X.lds, (X.tB ℓ + 2) / 3 ≤ ∑ ℓ ∈ X.lds, X.tB ℓ + 2 * X.lds.card := by
      rw [mul_sum, card_eq_sum_ones, mul_sum, ← sum_add_distrib]
      exact sum_le_sum (fun ℓ _ => by omega)
    have h4 : ∑ ℓ ∈ X.lds, X.tB ℓ ≤ ∑ K ∈ comps N.G S, (p K).rounds := by
      rw [hcomps, sum_image hinj]
      exact sum_le_sum (fun ℓ hℓ => (hrun ℓ hℓ).2.2.1)
    have h5 : X.lds.card ≤ X.S.card := card_filter_le _ _
    have h6 : X.S.card ≤ sz := (card_le_card H.SP).trans H.Psz
    have h7 : X.P.card ≤ sz := H.Psz
    simp only [Prof.rounds_add, Prof.rounds_sum, Prof.rounds_mk]
    rw [hsplit] at hTL
    have hdl : X.dil = E.dil := rfl
    have hPi : PiL X.dil X.sz = (E.dil + 1) * sz := rfl
    rw [hPi, hdl] at hTL
    have h8 : (E.dil + 1) * X.S.card ≤ (E.dil + 1) * sz := Nat.mul_le_mul_left _ h6
    have h9 : sz ≤ (E.dil + 1) * sz := Nat.le_mul_of_pos_left _ (by omega)
    have e1 : 30 * (E.dil + 1) * (sz + 1) = 30 * ((E.dil + 1) * sz) + 30 * (E.dil + 1) := by ring
    have e3 : 3 * (E.dil + 1) * X.S.card = 3 * ((E.dil + 1) * X.S.card) := by ring
    rw [e3] at hTL
    rw [e1]
    omega
  · -- messages
    rw [sum_card_frames]
    have h1 : ∑ φ ∈ range X.TL, (univ.filter (fun uw : V × V => (X.ML uw.1 uw.2 φ).isSome ∧
        True)).card ≤ 4 * P.card + 2 * E.aggLen j P := PCG.msgs_le hX X.TL
    have h1' : ∑ φ ∈ range X.TL, ((univ.filter (fun uv : V × V => (X.ML uv.1 uv.2 φ).isSome)).filter
        (fun _ => True)).card ≤ 4 * P.card + 2 * E.aggLen j P := by
      simpa only [filter_filter] using h1
    have h2 : ∑ ℓ ∈ X.lds, msgsUpTo (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) ≤
        ∑ K ∈ comps N.G S, (p K).msgs := by
      rw [hcomps, sum_image hinj]
      exact sum_le_sum (fun ℓ hℓ => (hrun ℓ hℓ).2.2.2.1)
    simp only [Prof.msgs_add, Prof.msgs_sum, Prof.msgs_mk]
    omega
  · -- loads
    rw [sum_card_frames]
    have h1 : ∑ φ ∈ range X.TL, (univ.filter (fun uw : V × V => (X.ML uw.1 uw.2 φ).isSome ∧
        s(uw.1, uw.2) = e)).card ≤ 6 * E.rho N.G j P e := PCG.load_le hX X.TL e
    have h1' : ∑ φ ∈ range X.TL, ((univ.filter (fun uv : V × V => (X.ML uv.1 uv.2 φ).isSome)).filter
        (fun uv => s(uv.1, uv.2) = e)).card ≤ 6 * E.rho N.G j P e := by
      simpa only [filter_filter] using h1
    have h2 : ∑ ℓ ∈ X.lds, loadUpTo (B V) (X.J ℓ) (xs ℓ) ω (X.tB ℓ) e ≤
        ∑ K ∈ comps N.G S, (p K).load e := by
      rw [hcomps, sum_image hinj]
      exact sum_le_sum (fun ℓ hℓ => (hrun ℓ hℓ).2.2.2.2.1 e)
    simp only [Prof.load_add, Prof.load_sum, Prof.load_mk, Pi.add_apply]
    omega
  · -- outputs
    have hw : w ∈ footprint E j P := I.host_part g w hgw
    have hmy : myD A (inpAt I x w) w = ldOf (x5Of P S z y1 y2 y3 y4 y5 (.inl w)) := by
      have hinp : inpAt I x w (.inl w) = some ⟨X5 A V, x5Of P S z y1 y2 y3 y4 y5 (.inl w)⟩ := by
        simp [inpAt, hIdef, ioInst, ioHost, hw, hxdef, inOf]
      unfold myD; rw [hinp]; simp
    show some (if g = .inl (I.ctx w).me ∧ (myD A (inpAt I x w) (I.ctx w).me).bS = true then _
      else dfltM Bt V) = _
    have hme : (I.ctx w).me = w := rfl
    rw [hme, hmy]
    by_cases hgw' : g = .inl w ∧ w ∈ S
    · obtain ⟨rfl, hwS⟩ := hgw'
      rw [if_pos ⟨rfl, by simp [ldOf, x5Of, memAg, hwS]⟩]
      obtain ⟨hℓ, hwℓ⟩ := PCG.rtS_lds hX hwS
      have hres := resX_of hEmb hℓ (subset_footprint _ _ _ hwℓ) (decide_eq_true hwℓ)
        (show 3 * X.bOf (X.rtS w) + X.tB (X.rtS w) ≤ 3 * X.TL by
          have := (PCG.bOf_lt_end hX hℓ).2; have := PCG.phEnd_le_TL hX hℓ; omega)
      rw [hres]
      have hout := (hzOf (X.rtS w) hℓ).1 (.inl w) (by
        simp [PCG.J, ioInst, ioHost, subset_footprint _ _ _ hwℓ])
      have hhost : (X.J (X.rtS w)).host (.inl w) = some w := by
        simp [PCG.J, ioInst, ioHost, subset_footprint _ _ _ hwℓ]
      unfold outAt at hout
      rw [hhost] at hout
      dsimp only at hout
      rw [hout]
      simp only [Option.getD_some, zz, if_pos hwS]
    · rw [if_neg (fun h' => hgw' ⟨h'.1, by
        have := h'.2; simp [ldOf, x5Of, memAg] at this; rw [h'.1] at *; exact this⟩), hdflt]
      cases g with
      | inl u =>
        have hu : u = w := by
          simp only [hIdef, ioInst, ioHost] at hgw; split_ifs at hgw; exact Option.some.inj hgw
        subst hu
        have hwS : u ∉ S := fun h' => hgw' ⟨rfl, h'⟩
        simp only [zz, if_neg hwS]
      | inr C => rfl
  · -- the specification
    intro K hK
    rw [hcomps] at hK
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hK
    refine H.loc _ (zOf ℓ) zz (fun v hv => ?_) (hzOf ℓ hℓ).2
    have hvS : v ∈ S := (PCG.mem_comp.1 hv).1
    have hrt : X.rtS v = ℓ := (PCG.mem_comp.1 hv).2
    simp only [zz, if_pos hvS, hrt]

end Trav

end APSP.Stoc.Congest
