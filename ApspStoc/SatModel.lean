import ApspStoc.Main
import ApspStoc.Realizability
import ApspStoc.Sec5bAux1
import ApspStoc.G0
import ApspStoc.RealDecomp
import ApspStoc.RealEO
import ApspStoc.RealMisc
import ApspStoc.RealRoute

/-!
# Realizability of every toolkit contract: a satisfiability model

Under the intended reading, `Impl A N t p δ` says that `A` reaches the postcondition of `t` except
with probability at most `δ`. Two consequences hold for every task whose precondition can be met:
the failure bound is a probability bound, `0 ≤ δ`, and if `δ < 1` then the postcondition is
*satisfiable* (with positive probability some admissible output is produced). A toolkit field
violating this — a contract demanding outputs that do not exist — would be false under the
intended reading, whatever the algorithm.

This file interprets the judgement as exactly these two consequences,

  `Impl A N t p δ  :=  0 ≤ δ ∧ (δ < 1 → Sat t)`,

where `Sat t` says that the postcondition of `t` is satisfiable (under the formal precondition of
the task, which matters only for `routeViaG0`: there, `G₀` is one actually produced by the
random-walk construction), and proves **every field of `Toolkit`** in this interpretation
(`satToolkit`). Hence:

* every contract is realizable: whenever its premises hold (with failure bounds `< 1`), its
  postcondition has a solution;
* the generic rules (sequencing, local calls, weakening, local computation) preserve
  realizability;
* consequently every judgement derivable from the toolkit — in particular every statement proved
  in this development, including the main theorem — has a satisfiable postcondition whenever its
  failure bound is below `1`.

The model ignores costs and participant sets (the participants `Pt` of an overlay task play no
role in `Sat`, so no fact about footprints is needed): realizability is a property of the
postconditions. The existence results
used are proved here or in the files `Real*.lean`:

| field | existence statement | proof |
|---|---|---|
| `expDecomp` | expander decompositions with `Õ(1/φ)·|F|` crossing edges | `expDecomp_exists_lg` (`RealDecomp.lean`) |
| `routeG0` | short low-congestion routes in a `1/polylog`-expander cluster (terminal routes of a hierarchy of depth `0`) | `route_exists` (`RealRoute.lean`), from `Mixing` |
| `rwLink` | some seeds give a `G₀` meeting the public parameters (which satisfy `Good`), unless the failure probability is `1` | `exists_not_of_rwProb_lt_one` |
| `ghs` | rooted spanning forests | `spanForest_exists` (`RealMisc.lean`) |
| `treeCast` | aggregates of non-empty multisets | `aggOf_exists` (`RealMisc.lean`) |
| `ringLE` | consistent ring orientations | `ringSpec_realizable` (`Realizability.lean`) |
| `approxRed` | exact distances with shortest-path parents | `approxSpec_realizable` (`RealMisc.lean`) |
| `eoVirt` | Eulerian orientations of even-degree instances with virtual nodes | `eoSpec_realizable` (`RealEO.lean`) |
| `perCompR` | outputs of the components combine (components are disjoint) | `comps_disj` |
| `schedule`, `embedConstruct` | outputs of the instances / clusters combine | choice |
| `aggUp`, `aggDown`, `notify`, `locR` | the outputs are explicit functions of the inputs | direct |

Building this model exposed three defects of earlier versions of the toolkit, now repaired:
the sequencing rules lacked the premise `0 ≤ δ'` (with an unsatisfiable intermediate
postcondition the continuation premise is vacuous, and a negative `δ'` certified anything);
`routeG0` lacked the hypotheses that `C` is a `1/polylog`-expander and `P ⊆ allPorts C` (without
them its route-length bound is unsatisfiable on some embedded `G₀`); and `perCompR` lacked
`[Nonempty β]` (with `S = ∅` and an empty output type no output exists).
-/

namespace APSP.Stoc

open APSP Finset

section Sat

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `g` describes a `G₀` actually produced by the random-walk construction on `P` in `C` (the
precondition of `routeViaG0`). -/
def G0Pre (C : Finset (Sym2 V)) (P : Finset (Port V)) (g : G0Data) : Prop :=
  ∃ (R ℓ : ℕ) (ω : RWSeeds C P R ℓ), TrueParams C P R ℓ ω g

/-- The postcondition of a task is satisfiable. (`mst` and `clusterSetup` carry no formal
postcondition.) -/
def Sat : Task V → Prop
  | .compute _ β spec => ∃ o : V → β, spec o
  | .io _ _ _ _ _ β _ spec => ∃ y : Agent V → β, spec y
  | .mst _ _ _ _ _ => True
  | .embedOverlays Good => ∃ E, Good E
  | .decompose Good => ∃ cl, Good cl
  | .decompRest _ _ Good => ∃ cl, Good cl
  | .expDecompOnce _ _ Good => ∃ P, Good P
  | .embedFrom _ Good => ∃ E, Good E
  | .clusterSetup _ => True
  | .buildG0 C P Good => ∃ g, G0Pre C P g ∧ Good g
  | .routeViaG0 C P g _ _ _ Good => G0Pre C P g → ∃ r, Good r
  | .route _ _ _ _ _ Good => ∃ r, Good r

end Sat

/-- The judgement of the satisfiability model. -/
abbrev SImpl : PUnit.{3} → ∀ {V : Type} [Fintype V] [DecidableEq V], WNet V → Task V → Prof V → ℝ →
    Prop :=
  fun _ _ _ _ _ t _ δ => 0 ≤ δ ∧ (δ < 1 → Sat t)

section Lemmas

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The sequencing pattern shared by `bind`, `embThen`, `decompThen`, `decompStep`. -/
lemma seq_sat {X : Type*} {Q : X → Prop} {S₂ : Prop} {δ δ' : ℝ}
    (h1 : 0 ≤ δ ∧ (δ < 1 → ∃ x, Q x)) (h2 : ∀ x, Q x → 0 ≤ δ' ∧ (δ' < 1 → S₂)) (hδ' : 0 ≤ δ') :
    0 ≤ δ + δ' ∧ (δ + δ' < 1 → S₂) := by
  refine ⟨add_nonneg h1.1 hδ', fun hlt => ?_⟩
  obtain ⟨x, hx⟩ := h1.2 (by linarith [h1.1])
  exact (h2 x hx).2 (by linarith [h1.1])

/-- If an event has probability `< 1` under uniform seeds, some seed avoids it. -/
lemma exists_not_of_rwProb_lt_one {C : Finset (Sym2 V)} {P : Finset (Port V)} {R ℓ : ℕ}
    {ev : RWSeeds C P R ℓ → Prop} (h : rwProb C P R ℓ ev < 1) : ∃ ω, ¬ ev ω := by
  classical
  by_contra hne
  push Not at hne
  apply absurd h
  have hpos : 0 < Fintype.card (RWSeeds C P R ℓ) :=
    Fintype.card_pos_iff.2 ⟨fun _ _ => ⟨0, seedRange_pos C⟩⟩
  unfold rwProb
  rw [Finset.filter_true_of_mem (fun ω _ => hne ω), Finset.card_univ,
    div_self (by exact_mod_cast hpos.ne')]
  exact lt_irrefl 1

/-- A trivial Minor-Aggregation instance (no nodes). -/
def trivMA : MAInst V :=
  ⟨∅, fun _ => false, fun _ => false, fun _ => [], fun _ _ => [], fun _ _ _ _ => [], fun _ _ => []⟩

omit [Fintype V] [DecidableEq V] in
lemma trivMA_small (b B : ℕ) : (trivMA : MAInst V).Small b B := by
  refine ⟨fun _ => ⟨by simp [trivMA], fun _ h => by simp [trivMA] at h⟩, fun _ _ _ _ =>
    ⟨⟨by simp [trivMA], fun _ h => by simp [trivMA] at h⟩, ⟨by simp [trivMA], fun _ h => by
      simp [trivMA] at h⟩⟩, fun _ _ _ _ _ _ => ⟨by simp [trivMA], fun _ h => by simp [trivMA] at h⟩⟩

/-- A trivial Eulerian-orientation instance on `S` (no edges, no virtual nodes). -/
noncomputable def trivEO (S : Finset V) : EOInst V := ⟨S, ∅, 0, fun _ => [], []⟩

lemma trivEO_wf (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (trivEO S).WF G := by
  refine ⟨by simp [trivEO], fun _ _ => rfl, fun _ i hi => by simp [trivEO] at hi,
    fun p hp => by simp [trivEO] at hp, fun v _ => ?_, fun i hi => by simp [trivEO] at hi⟩
  simp [trivEO, EOInst.pdeg]

omit [Fintype V] [DecidableEq V] in
lemma trivEO_physical (S : Finset V) : (trivEO S).Physical := ⟨rfl, fun _ => rfl, rfl⟩

lemma noLoops_of_sub {N : WNet V} {F : Finset (Sym2 V)} (hF : F ⊆ N.G.edgeFinset) :
    ∀ e ∈ F, ¬ e.IsDiag :=
  fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hF he)

lemma card_le_sq_of_le (F : Finset (Sym2 V)) {ν : ℕ} (hν : Fintype.card V ≤ ν) :
    F.card ≤ ν ^ 2 :=
  (Finset.card_le_univ F).trans ((card_sym2_le V).trans (Nat.pow_le_pow_left hν 2))

lemma lift_route_bounds {K k Kφ kφ φC ν d n0 lam cg : ℕ} (hφ : φC ≤ Kφ * lg ν ^ kφ)
    (hd : 1 ≤ d) :
    K * (φC + 1) ^ k * lg ν ^ k ≤ K * (Kφ + 1) ^ k * lg ν ^ (k + kφ * k) * d ∧
    K * (φC + 1) ^ k * lg ν ^ k * lam ≤
      2 * (K * (Kφ + 1) ^ k * lg ν ^ (k + kφ * k) * (n0 + lam) * (cg + d)) := by
  have hL : 1 ≤ lg ν ^ kφ := Nat.one_le_pow _ _ (by unfold lg; omega)
  have h1 : φC + 1 ≤ (Kφ + 1) * lg ν ^ kφ := by nlinarith
  have h2 : (φC + 1) ^ k ≤ (Kφ + 1) ^ k * lg ν ^ (kφ * k) := by
    calc (φC + 1) ^ k ≤ ((Kφ + 1) * lg ν ^ kφ) ^ k := Nat.pow_le_pow_left h1 k
      _ = (Kφ + 1) ^ k * lg ν ^ (kφ * k) := by rw [mul_pow, ← pow_mul]
  have h3 : K * (φC + 1) ^ k * lg ν ^ k ≤ K * (Kφ + 1) ^ k * lg ν ^ (k + kφ * k) := by
    calc K * (φC + 1) ^ k * lg ν ^ k ≤ K * ((Kφ + 1) ^ k * lg ν ^ (kφ * k)) * lg ν ^ k := by
          gcongr
      _ = K * (Kφ + 1) ^ k * lg ν ^ (k + kφ * k) := by rw [pow_add]; ring
  refine ⟨h3.trans (Nat.le_mul_of_pos_right _ hd), ?_⟩
  have h4 : lam ≤ (n0 + lam) * (cg + d) :=
    (Nat.le_add_left lam n0).trans (Nat.le_mul_of_pos_right _ (by omega))
  calc K * (φC + 1) ^ k * lg ν ^ k * lam
      ≤ K * (Kφ + 1) ^ k * lg ν ^ (k + kφ * k) * ((n0 + lam) * (cg + d)) := by gcongr
    _ ≤ 2 * (K * (Kφ + 1) ^ k * lg ν ^ (k + kφ * k) * (n0 + lam) * (cg + d)) := by
        rw [← mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)

end Lemmas

/-- **The satisfiability model of the toolkit**: every field holds when `Impl A N t p δ` is read
as "`0 ≤ δ`, and if `δ < 1` the postcondition of `t` is satisfiable". The only hypothesis is the
mixing bound `Mixing` (also a hypothesis of the main theorem), used for the routing contract. -/
noncomputable def satToolkit (hmix : Mixing) : Toolkit where
  Alg := PUnit.{3}
  Impl := SImpl
  seq := fun _ _ => PUnit.unit
  skip := PUnit.unit
  loc := fun _ => PUnit.unit
  call := fun _ _ => PUnit.unit
  dstart := fun _ => PUnit.unit
  dstep := fun _ _ => PUnit.unit
  sched := fun _ _ _ _ _ => PUnit.unit
  clusterPar := fun _ _ _ _ _ => PUnit.unit
  rwAlg := fun _ _ _ _ => PUnit.unit
  perComp := fun _ _ _ _ => PUnit.unit
  mstAlg := fun _ _ => PUnit.unit
  approxAlg := fun _ _ _ => PUnit.unit
  eoAlg := fun _ _ _ _ => PUnit.unit
  mono := fun h _ hδ => ⟨h.1.trans hδ, fun h1 => h.2 (lt_of_le_of_lt hδ h1)⟩
  weaken := by
    intro A V _ _ N ctx β spec spec' p δ hs h
    refine ⟨h.1, fun h1 => ?_⟩
    obtain ⟨o, ho⟩ := h.2 h1
    exact ⟨o, hs o ho⟩
  weakenIO := by
    intro A V _ _ N E j sz Pt α β x R R' p δ hs h
    refine ⟨h.1, fun h1 => ?_⟩
    obtain ⟨o, ho⟩ := h.2 h1
    exact ⟨o, hs o ho⟩
  bind := fun h1 h2 hδ' => seq_sat h1 h2 hδ'
  callR := by
    intro F B V _ _ N E j sz Pt β x R p δ h
    exact h
  locR := fun F V _ _ N E j sz Pt x =>
    ⟨le_rfl, fun _ => ⟨fun g => F.f V g (lview N g) (x g), fun _ => rfl⟩⟩
  embThen := fun h1 h2 hδ' => seq_sat h1 h2 hδ'
  embWeaken := by
    intro A V _ _ N Good Good' p δ hG h
    refine ⟨h.1, fun h1 => ?_⟩
    obtain ⟨E, hE⟩ := h.2 h1
    exact ⟨E, hG E hE⟩
  decompThen := fun h1 h2 hδ' => seq_sat h1 h2 hδ'
  decompStart := fun h => h
  decompBase := fun hG => ⟨le_rfl, fun _ => ⟨_, hG⟩⟩
  decompStep := fun h1 h2 hδ' => seq_sat h1 h2 hδ'
  expDecomp := fun c => ⟨6, 1, 0, fun _ _ => PUnit.unit, by
    intro V _ _ N ν hν _ F φinv hF _
    refine ⟨whp_nonneg _ _ _, fun _ => ?_⟩
    obtain ⟨P, h1, h2, h3⟩ := expDecomp_exists_lg F (noLoops_of_sub hF) φinv ν
      (card_le_sq_of_le F hν)
    exact ⟨P, h1, h2, by simpa using h3⟩⟩
  clusterSetup := fun _ _ => ⟨0, 0, fun _ => PUnit.unit, by
    intros; exact ⟨le_rfl, fun _ => trivial⟩⟩
  rwLink := fun _ => ⟨0, by
    intro Rf ℓ tf gf V _ _ N C P Good _ _ _ hG _
    refine ⟨rwProb_nonneg _ _ _ _ _, fun hlt => ?_⟩
    obtain ⟨ω, hω⟩ := exists_not_of_rwProb_lt_one hlt
    push Not at hω
    exact ⟨_, ⟨_, _, ω, hω.2⟩, hG⟩⟩
  routeG0 := fun c Kφ kφ _ => by
    obtain ⟨K, k, hr⟩ := route_exists hmix
    -- depth `h = 0`: every route is a terminal route of the trivial hierarchy (every level and
    -- `G₀` have the edges of the cluster, every embedding is a single edge), so `b` is the length
    -- bound of `route_exists` and `τ = 1`
    refine ⟨K * (Kφ + 1) ^ k, k + kφ * k, 0, 0, K * (Kφ + 1) ^ k + 1, k + kφ * k, 1,
      fun _ => PUnit.unit, ?_⟩
    intro V _ _ N ν hν _ C P φC g D lam hC hexp hφC hP _ _ _ _ hD hlam
    refine ⟨whp_nonneg _ _ _, fun _ hpre => ?_⟩
    obtain ⟨R, ℓ, ω, htp⟩ := hpre
    have hdil : 1 ≤ g.dil := le_trans (by omega) htp.2.2.2.2
    obtain ⟨r, hr'⟩ := hr C P φC ν D lam (noLoops_of_sub hC) hexp hν hP hD hlam
    obtain ⟨-, b2⟩ := lift_route_bounds (K := K) (k := k) (n0 := g.n0) (lam := lam)
      (cg := g.cong) hφC hdil
    -- the length bound without the factor `dil`
    obtain ⟨b1, -⟩ := lift_route_bounds (K := K) (k := k) (n0 := g.n0) (lam := lam)
      (cg := g.cong) (d := 1) hφC le_rfl
    have hlg : 1 ≤ lg ν := lg_pos ν
    have hb1 : 1 ≤ (K * (Kφ + 1) ^ k + 1) * lg ν ^ (k + kφ * k) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos hlg)
    let H : Hier V := ⟨fun _ => Sym2 V, fun _ e => [e], Sym2 V, fun e => [e], fun e => [e]⟩
    refine ⟨r, hr'.walk, hr'.local_, fun e => (hr'.cong e).trans b2, H,
      ⟨fun _ _ => hb1, fun _ => ?_, fun _ => hdil⟩, fun pq hpq => ⟨[], r pq, Nat.zero_le _,
        Hier.Gen.term _ ?_, by simp [H]⟩⟩
    · show 1 ≤ 1 * (g.φinv + 1) ^ 2 * lg ν
      exact Nat.mul_pos (Nat.mul_pos one_pos (Nat.pow_pos (Nat.succ_pos _))) hlg
    · calc (r pq).length ≤ K * (φC + 1) ^ k * lg ν ^ k := hr'.len pq hpq
        _ ≤ K * (Kφ + 1) ^ k * lg ν ^ (k + kφ * k) * 1 := b1
        _ ≤ (K * (Kφ + 1) ^ k + 1) * lg ν ^ (k + kφ * k) := by
            rw [mul_one]; exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  g0Then := by
    intro A B V _ _ N C P D lam pw GG GR p q δ δ' h1 h2 hδ'
    refine ⟨add_nonneg h1.1 hδ', fun hlt => ?_⟩
    obtain ⟨g, hpre, hg⟩ := h1.2 (by linarith [h1.1])
    exact (h2 g hg).2 (by linarith [h1.1]) hpre
  routeViaWeaken := by
    intro A V _ _ N C P g D lam pw GR GR' p δ hG h
    refine ⟨h.1, fun h1 hpre => ?_⟩
    obtain ⟨r, hr⟩ := h.2 h1 hpre
    exact ⟨r, hG r hr⟩
  routeWeaken := by
    intro A V _ _ N C P D lam pw GR GR' p δ hG h
    refine ⟨h.1, fun h1 => ?_⟩
    obtain ⟨r, hr⟩ := h.2 h1
    exact ⟨r, hG r hr⟩
  embedConstruct := fun _ _ => ⟨0, by
    intro A₁ A₂ A₃ V _ _ N cl p₁ p₂ p₃ δ₁ δ₂ δ₃ GR Good _ _ _ _ h1 h2 h3 _ _ hgood
    have hnn : ∀ C ∈ cl, 0 ≤ δ₁ C + δ₂ C + δ₃ C := fun C hC =>
      add_nonneg (add_nonneg (h1 C hC).1 (h2 C hC).1) (h3 C hC).1
    refine ⟨sum_nonneg hnn, fun hlt => ?_⟩
    have hex : ∀ C ∈ cl, ∃ r, GR C r := fun C hC => (h3 C hC).2 (by
      have := single_le_sum hnn hC
      linarith [(h1 C hC).1, (h2 C hC).1])
    choose! r hr using hex
    exact ⟨_, hgood r hr⟩⟩
  aggUp := fun _ _ => ⟨0, 0, 0, fun _ _ => PUnit.unit, by
    intro V _ _ N ν _ _ E j sz Pt S μ x _ _ _ _ _ _
    exact ⟨whp_nonneg _ _ _, fun _ => ⟨fun g => match g with
      | .inl _ => fun _ => none
      | .inr C => fun v => if v ∈ nodes C then x (.inl v) else none, fun _ _ _ => rfl⟩⟩⟩
  aggDown := fun _ _ => ⟨0, 0, 0, fun _ _ => PUnit.unit, by
    intro V _ _ N ν _ _ E j sz Pt S μ x _ _ _ _ _ _
    exact ⟨whp_nonneg _ _ _, fun _ => ⟨fun g => match g with
      | .inl v => (clustersOf E.cl v).val.filterMap (fun C => x (.inr C) v)
      | .inr _ => 0, fun _ => rfl⟩⟩⟩
  notify := ⟨PUnit.unit, by
    intro V _ _ N E j sz Pt S F x _ _ _
    exact ⟨le_rfl, fun _ => ⟨fun g => match g with
      | .inl v => univ.filter (fun u => v ∈ x (.inl u))
      | .inr _ => ∅, fun _ => rfl⟩⟩⟩
  ghs := ⟨0, fun _ => PUnit.unit, by
    intro V _ _ N ν _ _ E j sz Pt S F x hF hFS _ _ _
    refine ⟨le_rfl, fun _ => ?_⟩
    obtain ⟨par, root, hsf⟩ := spanForest_exists S F hFS (noLoops_of_sub hF)
    have : Nonempty V := N.conn.nonempty
    exact ⟨fun g => match g with
      | .inl v => (par v, root v)
      | .inr _ => (none, Classical.arbitrary V), hsf⟩⟩
  treeCast := fun _ => ⟨0, fun _ _ => PUnit.unit, by
    intro V _ _ N ν _ E j sz Pt S b par root val op Fp x _ _ _ _ _ _ _ _ _ _
    refine ⟨le_rfl, fun _ => ?_⟩
    let Ms : V → Multiset (Msg V) := fun r => (S.filter (fun u => root u = r)).val.map val
    let Ysel : V → Option (Msg V) := fun r =>
      if h : Ms r ≠ 0 then some (Classical.choose (aggOf_exists op (Ms r) h)) else none
    refine ⟨fun g => match g with
      | .inl v => Ysel (root v)
      | .inr _ => none, fun v hv => ?_⟩
    have hne : Ms (root v) ≠ 0 := by
      intro h0
      have hv' : val v ∈ Ms (root v) :=
        Multiset.mem_map_of_mem _ (Finset.mem_def.1 (mem_filter.2 ⟨hv, rfl⟩))
      rw [h0] at hv'
      exact Multiset.notMem_zero _ hv'
    refine ⟨Classical.choose (aggOf_exists op _ hne), ?_,
      Classical.choose_spec (aggOf_exists op _ hne), fun u _ hru => ?_⟩
    · show Ysel (root v) = _
      simp only [Ysel, ne_eq, hne, not_false_eq_true, dite_true]
    · show Ysel (root u) = _
      rw [hru]
      simp only [Ysel, ne_eq, hne, not_false_eq_true, dite_true]⟩
  ringLE := ⟨0, fun _ => PUnit.unit, by
    intro V _ _ N ν _ _ E j sz Pt S r x _ _ hr _ _ _
    refine ⟨le_rfl, fun _ => ?_⟩
    obtain ⟨d, hd⟩ := ringSpec_realizable hr
    exact ⟨fun g => match g with
      | .inl v => d v
      | .inr _ => [], hd⟩⟩
  perCompR := ⟨0, by
    intro A Bt Am B V _ _ _ N E j sz P S z R pm pm' δm δm' p δ _ _ _ _ _ hloc hm hm' hB
    have hnn : ∀ K ∈ comps N.G S, 0 ≤ δ K := fun K hK => (hB K hK).1
    refine ⟨add_nonneg (add_nonneg hm.1 hm'.1) (sum_nonneg hnn), fun hlt => ?_⟩
    have hex : ∀ K ∈ comps N.G S, ∃ y, R K y := fun K hK => (hB K hK).2 (by
      have := single_le_sum hnn hK
      linarith [hm.1, hm'.1])
    choose! yK hyK using hex
    obtain ⟨b0⟩ := ‹Nonempty (Bt V)›
    classical
    let y : Agent V → Bt V := fun g => match g with
      | .inl v => if h : ∃ K ∈ comps N.G S, v ∈ K then yK (Classical.choose h) (.inl v) else b0
      | .inr _ => b0
    refine ⟨y, fun K hK => hloc K (yK K) y (fun v hv => ?_) (hyK K hK)⟩
    have h : ∃ K ∈ comps N.G S, v ∈ K := ⟨K, hK, hv⟩
    have hspec := Classical.choose_spec h
    have hK' : Classical.choose h = K := by
      by_contra hne
      exact Finset.disjoint_left.1 (comps_disj N.G hspec.1 hK hne) hspec.2 hv
    show yK K (.inl v) = (if h : ∃ K ∈ comps N.G S, v ∈ K then yK (Classical.choose h) (.inl v)
      else b0)
    rw [dite_eq_left_of_eq_true (eq_true h), hK']⟩
  mstRed := ⟨0, by
    intro M V _ _ N ν _ _ E j sz Pt S p δ _ _ hI
    have h0 := hI trivMA (by simp [trivMA]) (trivMA_small _ _)
    exact ⟨mul_nonneg (Nat.cast_nonneg _) h0.1, fun _ => trivial⟩⟩
  approxRed := fun _ => ⟨0, 0, by
    intro M Eo V _ _ N ν _ _ E j sz Pt S w0 pM pE δM δE _ _ _ _ _ hM hE
    have h1 := hM trivMA (by simp [trivMA]) (trivMA_small _ _)
    have h2 := hE (trivEO S) rfl (trivEO_wf _ _) (by simp [trivEO])
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (add_nonneg h1.1 h2.1), fun _ => ?_⟩
    obtain ⟨y, hy⟩ := approxSpec_realizable N S w0
    exact ⟨fun g => match g with
      | .inl v => y v
      | .inr _ => none, hy⟩⟩
  eoVirt := ⟨0, 0, by
    intro M Pa V _ _ N ν _ _ E j sz Pt H kb pM pP δM δP _ hwf _ _ _ hM hP
    have h1 := hM trivMA (by simp [trivMA]) (fun _ _ => trivMA_small _ _)
    have h2 := hP (trivEO H.S) rfl (trivEO_physical _) (by simp [trivEO]) (trivEO_wf _ _)
    refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) h1.1) h2.1, fun _ => ?_⟩
    exact eoSpec_realizable N.G E.cl H hwf⟩
  schedule := fun c _ => ⟨0, 0, 0, by
    intro A V _ _ N ν _ _ E β R Cg spec p δ _ hs _ _
    have hnn : ∀ s, 0 ≤ δ s := fun s => (hs s).1
    refine ⟨add_nonneg (sum_nonneg fun s _ => hnn s) (whp_nonneg _ _ _), fun hlt => ?_⟩
    have hex : ∀ s, ∃ y : Agent V → β, spec s (fun v => y (.inl v)) := fun s => (hs s).2 (by
      have := single_le_sum (fun s _ => hnn s) (mem_univ s)
      linarith [whp_nonneg 0 c ν])
    choose y hy using hex
    exact ⟨fun v s => y s (.inl v), hy⟩⟩

/-- In the satisfiability model, a judgement with failure bound below `1` has a satisfiable
postcondition (by construction). -/
theorem satToolkit_sat (hmix : Mixing) {A : (satToolkit hmix).Alg} {V : Type} [Fintype V]
    [DecidableEq V] {N : WNet V} {t : Task V} {p : Prof V} {δ : ℝ}
    (h : (satToolkit hmix).Impl A N t p δ) (hδ : δ < 1) : Sat t :=
  h.2 hδ

/-- The main theorem instantiated in the satisfiability model (a sanity check: `satToolkit` is a
toolkit like any other). -/
example (hmix : Mixing) : ∃ (A : ℕ → (satToolkit hmix).Alg) (C k K : ℕ), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V), 1 ≤ Fintype.card V → (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ 0) →
    ∃ (p : Prof V) (δ : ℝ),
      (satToolkit hmix).Impl (A (Fintype.card V)) N (.compute none (V → ℕ × V) (APSPSpec N)) p δ ∧
      p.rounds ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ∧
      p.msgs ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ^ 2 ∧
      δ ≤ (K : ℝ) / (Fintype.card V : ℝ) ^ 1 :=
  thm_5_6 (satToolkit hmix) hmix 0 1

end APSP.Stoc
