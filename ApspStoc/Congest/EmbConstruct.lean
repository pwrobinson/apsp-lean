import ApspStoc.Congest.EmbConstructOut
import ApspStoc.Congest.EmbConstructBfs

/-!
# `embedConstruct` in the CONGEST semantics

`embedConstruct_congest` proves the toolkit field `embedConstruct` (`Congest/Assume.lean`) for the
concrete protocol `clusterParC Lb wexp A₁ A₂ A₃` (the field `clusterPar`), with
`K = 4 Lb + 6`.

## The protocol (`clusterParC`)
1. **BFS** (`bfsP`, `EmbConstructBfs.lean`): a BFS tree of `G` from the node of smallest index,
   by flooding, in `n` rounds, `2m ≤ n²` messages, two per edge.
2. **Main phase** (`mainP`, `EmbConstructDefs.lean`): in every cluster `C` in parallel, the
   pipeline `pipeP` (`A₁`; `A₂` on the topology packets with payloads `[edge e] ++ digits of
   w(e)`; `A₃` on the dummy packets; inputs computed locally, `EmbConstructLocal.lean`), as copies
   keyed by the slices `C ∩ inc(v)`; meanwhile a termination detection on the BFS tree: a node
   whose copies have all halted and whose children have reported streams to its parent the
   maxima (over its subtree) of the lengths of its own overlay paths (`Lb + 1` digits) and of its
   number of clusters; the root streams the global maxima `E.dil`, `E.ov` down the tree, and all
   nodes halt in the same round (`EmbConstructPar.lean`).
3. **Output** (`finE`, `EmbConstructOut.lean`): every node outputs `ekAt N E (.inl v)` for
   `E = construct cl r`, `r C` the dummy routes recorded in `C`.

## The proof
* `pipe_implI`: in every cluster the pipeline succeeds within `p₁ C + p₂ C + p₃ C` except with
  probability `δ₁ C + δ₂ C + δ₃ C` (sequential composition).
* `PD.Ok.par_run` (generic parallel composition): if the standalone runs of all clusters (with
  the seeds of the slices, `seedC`) succeed, the main phase succeeds: the copies reproduce the
  standalone runs, the costs add up (plus `O(Lb · n)` rounds, `O(Lb)` per edge and `O(Lb · n)`
  messages for the tree), and the outputs are computed from the copies' final states.
* union bound (`card_proj_filter`): the seeds of the copies of a cluster are uniform, so the
  failure probability is at most `∑_C (δ₁ C + δ₂ C + δ₃ C)`.
-/

namespace APSP.Stoc.Congest

open APSP Finset EmbC

set_option linter.unusedSectionVars false

/-- **The constructor** of the per-cluster preprocessing (`clusterPar Lb wexp A₁ A₂ A₃`): the BFS
phase, then the parallel pipelines with termination detection. -/
noncomputable def clusterParC (Lb wexp : ℕ) (A₁ A₂ A₃ : CAlg) : CAlg := fun V _ _ =>
  seqP (bfsP V) (mainP (pipeP wexp (A₁ V) (A₂ V) (A₃ V)) (Lb + 1) (valE _) (finE wexp _))

/-- the toolkit field `embedConstruct` for the CONGEST semantics (with `clusterPar := clusterParC`) -/
def EmbedConstructC : Prop :=
  ∀ Lb wexp : ℕ, ∃ K : ℕ, ∀ (A₁ A₂ A₃ : CAlg) {V : Type} [Fintype V]
    [DecidableEq V]
    {N : WNet V} (cl : Finset (Finset (Sym2 V))) (p₁ p₂ p₃ : Finset (Sym2 V) → Prof V)
    (δ₁ δ₂ δ₃ : Finset (Sym2 V) → ℝ) (GR : Finset (Sym2 V) → Routes V → Prop)
    (Good : Overlays V → Prop),
    (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp) →
    (∀ e ∈ N.G.edgeFinset, ∃ C ∈ cl, e ∈ C) →
    (∀ C ∈ cl, C ⊆ N.G.edgeFinset ∧ C.Nonempty) →
    (∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C') →
    (∀ C ∈ cl, CImplT A₁ N (.clusterSetup C) (p₁ C) (δ₁ C)) →
    (∀ C ∈ cl, CImplT A₂ N (.route C (topoP C) (topoDemand C) (6 * (nodes C).card) (wexp + 2)
      (fun _ => True)) (p₂ C) (δ₂ C)) →
    (∀ C ∈ cl, CImplT A₃ N (.route C (portsP C) (portsDemand C) (3 * (nodes C).card) 0 (GR C))
      (p₃ C) (δ₃ C)) →
    (∀ C ∈ cl, ∀ e ∉ C, (p₁ C + p₂ C + p₃ C).load e = 0) →
    (∀ C ∈ cl, ∀ r, GR C r → ∀ v ∈ nodes C, ∀ q ∈ portsA C,
      IsEdgeWalk (r (srcPort C v, q)) v q.1 ∧ (∀ e ∈ r (srcPort C v, q), e ∈ C) ∧
      (r (srcPort C v, q)).length ≤ Fintype.card V ^ Lb) →
    (∀ r : Finset (Sym2 V) → Routes V, (∀ C ∈ cl, GR C (r C)) → Good (construct cl r)) →
    CImplT (clusterParC Lb wexp A₁ A₂ A₃) N (.embedFrom cl Good)
      (Prof.mk (cl.sup (fun C => (p₁ C + p₂ C + p₃ C).rounds) + K * Fintype.card V)
        (∑ C ∈ cl, (p₁ C + p₂ C + p₃ C).load + fun _ => K * Fintype.card V)
        (∑ C ∈ cl, (p₁ C + p₂ C + p₃ C).msgs + K * Fintype.card V ^ 2))
      (∑ C ∈ cl, (δ₁ C + δ₂ C + δ₃ C))

namespace EmbC

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the input of the task `.embedFrom` -/
def xinE (r : V → Finset (Sym2 V)) (cl : Finset (Finset (Sym2 V))) : Agent V → Unit × DState V :=
  fun g => match g with
    | .inl v => ((), (r v, clLoc cl v))
    | .inr _ => ((), (∅, ∅))

/-! ## The main phase: union bound over the clusters -/

section Main

/-- the BFS output, as a function of the agents -/
noncomputable def bfsOutOf (N : WNet V) (ρ : V) : Agent V → BfsOut V
  | .inl v => (bfsDep N ρ v, bfsPar N ρ v, univ.filter (fun c => bfsPar N ρ c = some v))
  | .inr _ => (0, none, ∅)

lemma readers_main (N : WNet V) (cl : Finset (Finset (Sym2 V))) (r : V → Finset (Sym2 V))
    (ρ : V) (z : Agent V → BfsOut V) (hz : ∀ v, z (.inl v) = bfsOutOf N ρ (.inl v)) (v : V) :
    mSl (inpAt (baseInst N) (inOf (fun g => (xinE r cl g, z g))) v) v = clLoc cl v ∧
    mPar (inpAt (baseInst N) (inOf (fun g => (xinE r cl g, z g))) v) v = bfsPar N ρ v ∧
    mKids (inpAt (baseInst N) (inOf (fun g => (xinE r cl g, z g))) v) v =
      univ.filter (fun c => bfsPar N ρ c = some v) ∧
    mDep (inpAt (baseInst N) (inOf (fun g => (xinE r cl g, z g))) v) v = bfsDep N ρ v := by
  have h : rdIn (MIn V) (inpAt (baseInst N) (inOf (fun g => (xinE r cl g, z g))) v) v =
      some (((), (r v, clLoc cl v)), bfsOutOf N ρ (.inl v)) := by
    apply rdIn_of
    simp [inpAt, baseInst, physHost, inOf, xinE, hz v]
  simp [mSl, mPar, mKids, mDep, h, bfsOutOf]

/-- the cost of the main phase -/
def qMain (Lb : ℕ) (cl : Finset (Finset (Sym2 V))) (pc : Finset (Sym2 V) → Prof V) : Prof V :=
  Prof.mk (cl.sup (fun C => (pc C).rounds) + 2 * (2 * (Lb + 1)) * Fintype.card V)
    (∑ C ∈ cl, (pc C).load + fun _ => 2 * (2 * (Lb + 1)))
    (∑ C ∈ cl, (pc C).msgs + 2 * (2 * (Lb + 1)) * Fintype.card V)

/-- **The main phase succeeds whenever all clusters succeed.** -/
theorem main_succ {Lb wexp : ℕ} {P : Proto V} {N : WNet V} {cl : Finset (Finset (Sym2 V))}
    {GR : Finset (Sym2 V) → Routes V → Prop} {pc : Finset (Sym2 V) → Prof V}
    {Good : Overlays V → Prop} (hV : Nonempty V) (hcl : ClH N cl)
    (hw : ∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp)
    (hGR : ∀ C ∈ cl, ∀ r, GR C r → ∀ v ∈ nodes C, ∀ q ∈ portsA C,
      IsEdgeWalk (r (srcPort C v, q)) v q.1 ∧ (∀ e ∈ r (srcPort C v, q), e ∈ C) ∧
      (r (srcPort C v, q)).length ≤ Fintype.card V ^ Lb)
    (hGood : ∀ r : Finset (Sym2 V) → Routes V, (∀ C ∈ cl, GR C (r C)) → Good (construct cl r))
    (r : V → Finset (Sym2 V)) (ρ : V) (z : Agent V → BfsOut V)
    (hz : ∀ v, z (.inl v) = bfsOutOf N ρ (.inl v))
    (ω : V → Finset (Sym2 V) → P.Ω)
    (hall : ∀ C ∈ cl, Succ P (clInst0 N C) x0 (postOf (clInst0 N C) (PipeSpec N wexp C (GR C)))
      (pc C) (seedC ω C)) :
    Succ (mainP P (Lb + 1) (valE P) (finE wexp P)) (baseInst N)
      (inOf (fun g => (xinE r cl g, z g)))
      (postOf (baseInst N) (fun z : Agent V → EK V =>
        ∃ E, Good E ∧ ∀ v, z (.inl v) = ekAt N E (.inl v))) (qMain Lb cl pc) ω := by
  classical
  -- the halting rounds of the clusters
  let T : Finset (Sym2 V) → ℕ := fun C => if h : C ∈ cl then (hall C h).choose else 0
  have hT : ∀ C (hC : C ∈ cl), T C = (hall C hC).choose := fun C hC => dif_pos hC
  have hS : ∀ C (hC : C ∈ cl), HaltsAt P (clInst0 N C) x0 (seedC ω C) (T C) ∧
      T C ≤ (pc C).rounds ∧ msgsUpTo P (clInst0 N C) x0 (seedC ω C) (T C) ≤ (pc C).msgs ∧
      (∀ e, loadUpTo P (clInst0 N C) x0 (seedC ω C) (T C) e ≤ (pc C).load e) ∧
      ∃ y : Agent V → Mem, (∀ g, ((clInst0 N C).host g).isSome →
        outAt P (clInst0 N C) x0 (seedC ω C) (T C) g = some (y g)) ∧
        postOf (clInst0 N C) (PipeSpec N wexp C (GR C)) y := by
    intro C hC
    rw [hT C hC]
    obtain ⟨h1, -, h2, h3, h4, h5⟩ := (hall C hC).choose_spec
    exact ⟨h1, h2, h3, h4, h5⟩
  -- the recorded routes of the clusters
  have hR : ∀ C ∈ cl, ∃ r₃ : Routes V, GR C r₃ ∧ ∀ v ∈ nodes C, ∃ ℓ pr r₂,
      cOut P v (st P (clInst0 N C) x0 (seedC ω C) (T C) v) = some (oOf N wexp C ℓ pr r₂ r₃ v) := by
    intro C hC
    obtain ⟨-, -, -, -, y, hy, zc, hzc, ℓ, par, r₂, r₃, hr₃, hzv⟩ := hS C hC
    refine ⟨r₃, hr₃, fun v hv => ⟨ℓ, par v, r₂, ?_⟩⟩
    have hhost : (clInst0 N C).host (.inl v) = some v := by
      simp [clInst0, clInstP, clHost, hv]
    have h1 := hy (.inl v) (by rw [hhost]; rfl)
    rw [hzc (.inl v) (by rw [hhost]; rfl), hzv v hv] at h1
    unfold outAt at h1
    rw [hhost] at h1
    simp only at h1
    obtain ⟨m, hm, hmv⟩ := Option.bind_eq_some_iff.1 h1
    unfold cOut
    rw [hm, Option.getD_some]
    exact rdIn_of hmv
  let rC : Finset (Sym2 V) → Routes V := fun C => if h : C ∈ cl then (hR C h).choose else fun _ => []
  have hrC : ∀ C (hC : C ∈ cl), rC C = (hR C hC).choose := fun C hC => dif_pos hC
  -- the data of the run
  let d : PD V := ⟨P, Lb + 1, valE P, finE wexp P, N, cl, ρ, bfsPar N ρ, bfsDep N ρ,
    inOf (fun g => (xinE r cl g, z g)), ω, T⟩
  have hrd := readers_main N cl r ρ z hz
  have hOut : OutH N wexp Lb cl rC := ⟨hcl, hw, fun C hC v hv q hq =>
    hGR C hC (rC C) (by rw [hrC C hC]; exact (hR C hC).choose_spec.1) v hv q hq⟩
  have := hV
  let oV : V → Finset (Sym2 V) → PipeOut V := fun v C =>
    (cOut P v (d.cpF v (C.filter (fun e => v ∈ e)))).getD (Classical.arbitrary _)
  have hNode : ∀ v, OutH.NodeH N wexp cl rC P v (inpAt (baseInst N) d.x' v) (d.cpF v) (oV v) := by
    intro v
    refine ⟨(hrd v).1, fun C hC hv => ?_, fun C hC hv => ?_⟩
    · obtain ⟨ℓ, pr, r₂, h⟩ := (hR C hC).choose_spec.2 v hv
      have h' : cOut P v (d.cpF v (C.filter (fun e => v ∈ e))) =
          some (oOf N wexp C ℓ pr r₂ (hR C hC).choose v) := by
        rw [d.cpF_slice hcl hC hv]; exact h
      simp only [oV, h', Option.getD_some]
    · obtain ⟨ℓ, pr, r₂, h⟩ := (hR C hC).choose_spec.2 v hv
      have h' : cOut P v (d.cpF v (C.filter (fun e => v ∈ e))) =
          some (oOf N wexp C ℓ pr r₂ (hR C hC).choose v) := by
        rw [d.cpF_slice hcl hC hv]; exact h
      refine ⟨ℓ, pr, r₂, ?_⟩
      simp only [oV, h', Option.getD_some, hrC C hC]
  have hval : ∀ v, d.val v = ((range (Fintype.card V)).sup
      (fun j => cl.sup (fun C => ((construct cl rC).path j v C).length)), (clustersOf cl v).card) :=
    fun v => hOut.valE_eq (hNode v)
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hok : d.Ok := by
    refine ⟨hcl, bfs_tree ρ, fun v => (hrd v).1, fun v => (hrd v).2.1, fun v => (hrd v).2.2.1,
      fun v => (hrd v).2.2.2, fun C hC => (hS C hC).1, Nat.le_add_left 1 Lb, fun v => ?_⟩
    have hb := hOut.valE_bound (hNode v)
    refine ⟨lt_pow_of_le_pow hb.1, lt_of_le_of_lt hb.2 ?_⟩
    calc Fintype.card V < Fintype.card V + 4 := by omega
      _ ≤ (Fintype.card V + 4) ^ (Lb + 1) := Nat.le_self_pow (by omega) _
  obtain ⟨hH, hP, hRd, hM, hL, hO⟩ := hok.par_run
  have hsupT : d.cl.sup d.T ≤ cl.sup (fun C => (pc C).rounds) :=
    Finset.sup_mono_fun (fun C hC => (hS C hC).2.1)
  let E := construct cl rC
  have hdil : univ.sup (fun w => (d.val w).1) = E.dil := by
    simp only [hval]; exact OutH.dil_construct
  have hov : univ.sup (fun w => (d.val w).2) = E.ov := by
    simp only [hval]; rfl
  refine ⟨d.H, hH, hP, ?_, ?_, fun e => ?_, fun g => ⟨EK V, ekAt N E g⟩, fun g hg => ?_, ?_⟩
  · simp only [qMain, Prof.rounds_mk]
    have hRd' : d.H ≤ cl.sup T + 2 * (2 * (Lb + 1)) * Fintype.card V := hRd
    have hsupT' : cl.sup T ≤ cl.sup (fun C => (pc C).rounds) := hsupT
    exact le_trans hRd' (by omega)
  · simp only [qMain, Prof.msgs_mk]
    refine le_trans hM (Nat.add_le_add_right (sum_le_sum (fun C hC => ?_)) _)
    exact (hS C hC).2.2.1
  · simp only [qMain, Prof.load_mk, Pi.add_apply, Finset.sum_apply]
    refine le_trans (hL e) (Nat.add_le_add_right (sum_le_sum (fun C hC => ?_)) _)
    exact (hS C hC).2.2.2.1 e
  · obtain ⟨v, rfl⟩ := baseInst_host hg
    show outAt d.run (baseInst d.N) d.x' d.ω d.H (.inl v) = _
    rw [hO v, hdil, hov]
    show (if (Sum.inl v : Agent V) = Sum.inl ((baseInst N).ctx v).me then
      some (⟨EK V, ekL wexp P ((baseInst N).ctx v) (inpAt (baseInst N) d.x' v) (d.cpF v)
        (E.dil, E.ov)⟩ : Mem) else none) = _
    rw [if_pos (show (Sum.inl v : Agent V) = Sum.inl ((baseInst N).ctx v).me from rfl),
      hOut.ekL_eq (hNode v)]
  · refine ⟨fun g => ekAt N E g, fun g _ => rfl, E, hGood rC (fun C hC => ?_), fun v => rfl⟩
    rw [hrC C hC]; exact (hR C hC).choose_spec.1

/-- **The main phase**: failure probability at most the sum over the clusters (union bound; the
seeds of the copies of a cluster are uniform). -/
theorem main_implI {Lb wexp : ℕ} {P : Proto V} {N : WNet V} {cl : Finset (Finset (Sym2 V))}
    {GR : Finset (Sym2 V) → Routes V → Prop} {pc : Finset (Sym2 V) → Prof V}
    {δc : Finset (Sym2 V) → ℝ} {Good : Overlays V → Prop} (hV : Nonempty V) (hcl : ClH N cl)
    (hw : ∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp)
    (hGR : ∀ C ∈ cl, ∀ r, GR C r → ∀ v ∈ nodes C, ∀ q ∈ portsA C,
      IsEdgeWalk (r (srcPort C v, q)) v q.1 ∧ (∀ e ∈ r (srcPort C v, q), e ∈ C) ∧
      (r (srcPort C v, q)).length ≤ Fintype.card V ^ Lb)
    (hGood : ∀ r : Finset (Sym2 V) → Routes V, (∀ C ∈ cl, GR C (r C)) → Good (construct cl r))
    (hpipe : ∀ C ∈ cl, ImplI P (clInst0 N C) x0
      (postOf (clInst0 N C) (PipeSpec N wexp C (GR C))) (pc C) (δc C))
    (r : V → Finset (Sym2 V)) (ρ : V) (z : Agent V → BfsOut V)
    (hz : ∀ v, z (.inl v) = bfsOutOf N ρ (.inl v)) :
    ImplI (mainP P (Lb + 1) (valE P) (finE wexp P)) (baseInst N)
      (inOf (fun g => (xinE r cl g, z g)))
      (postOf (baseInst N) (fun z : Agent V → EK V =>
        ∃ E, Good E ∧ ∀ v, z (.inl v) = ekAt N E (.inl v))) (qMain Lb cl pc) (∑ C ∈ cl, δc C) := by
  classical
  set Qc := fun C => postOf (clInst0 N C) (PipeSpec N wexp C (GR C))
  have hδ : ∀ C ∈ cl, ((univ.filter (fun ω : V → Finset (Sym2 V) → P.Ω =>
      ¬ Succ P (clInst0 N C) x0 (Qc C) (pc C) (seedC ω C))).card : ℝ) /
        (Fintype.card (V → Finset (Sym2 V) → P.Ω) : ℝ) ≤ δc C := by
    intro C hC
    have h1 := card_proj_filter' (Ω₀ := P.Ω) (fun v => C.filter (fun e => v ∈ e))
      (fun σ => ¬ Succ P (clInst0 N C) x0 (Qc C) (pc C) σ)
      (fun ω => ¬ Succ P (clInst0 N C) x0 (Qc C) (pc C) (seedC ω C)) (fun ω => Iff.rfl)
    rw [h1]
    have h2 := hpipe C hC
    unfold ImplI failProb at h2
    convert h2 using 3
  have hsub : (univ.filter (fun ω : V → Finset (Sym2 V) → P.Ω =>
      ¬ Succ (mainP P (Lb + 1) (valE P) (finE wexp P)) (baseInst N)
        (inOf (fun g => (xinE r cl g, z g)))
        (postOf (baseInst N) (fun z : Agent V → EK V =>
          ∃ E, Good E ∧ ∀ v, z (.inl v) = ekAt N E (.inl v))) (qMain Lb cl pc) ω)) ⊆
      cl.biUnion (fun C => univ.filter (fun ω : V → Finset (Sym2 V) → P.Ω =>
        ¬ Succ P (clInst0 N C) x0 (Qc C) (pc C) (seedC ω C))) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_contra hn
    refine hω (main_succ hV hcl hw hGR hGood r ρ z hz ω (fun C hC => ?_))
    by_contra hs
    exact hn (mem_biUnion.2 ⟨C, hC, by simp only [mem_filter, mem_univ, true_and]; exact hs⟩)
  unfold ImplI failProb
  have hpos : (0 : ℝ) < (Fintype.card (V → Finset (Sym2 V) → P.Ω) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  calc _ ≤ ((cl.biUnion (fun C => univ.filter (fun ω : V → Finset (Sym2 V) → P.Ω =>
        ¬ Succ P (clInst0 N C) x0 (Qc C) (pc C) (seedC ω C)))).card : ℝ) /
          (Fintype.card (V → Finset (Sym2 V) → P.Ω) : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hpos.le
        exact_mod_cast card_le_card hsub
    _ ≤ (∑ C ∈ cl, ((univ.filter (fun ω : V → Finset (Sym2 V) → P.Ω =>
        ¬ Succ P (clInst0 N C) x0 (Qc C) (pc C) (seedC ω C))).card : ℝ)) /
          (Fintype.card (V → Finset (Sym2 V) → P.Ω) : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hpos.le
        exact_mod_cast card_biUnion_le
    _ = ∑ C ∈ cl, (((univ.filter (fun ω : V → Finset (Sym2 V) → P.Ω =>
        ¬ Succ P (clInst0 N C) x0 (Qc C) (pc C) (seedC ω C))).card : ℝ) /
          (Fintype.card (V → Finset (Sym2 V) → P.Ω) : ℝ)) := sum_div _ _ _
    _ ≤ ∑ C ∈ cl, δc C := sum_le_sum hδ

end Main

end EmbC

/-! ## The theorem -/

/-- **`embedConstruct` in the CONGEST semantics.** -/
theorem embedConstruct_congest : EmbedConstructC := by
  intro Lb wexp
  refine ⟨4 * Lb + 6, ?_⟩
  intro A₁ A₂ A₃ V _ _ N cl p₁ p₂ p₃ δ₁ δ₂ δ₃ GR Good hw hcov hsub hdisj h₁ h₂ h₃ _ hGR hGood r
  classical
  have hcl : ClH N cl := ⟨fun C hC => (hsub C hC).1, fun C hC => (hsub C hC).2, hcov, hdisj⟩
  have hpipe : ∀ C ∈ cl, ImplI (pipeP wexp (A₁ V) (A₂ V) (A₃ V)) (clInst0 N C) x0
      (postOf (clInst0 N C) (PipeSpec N wexp C (GR C))) (p₁ C + p₂ C + p₃ C)
      (δ₁ C + δ₂ C + δ₃ C) := fun C hC =>
    pipe_implI (hsub C hC).1 (hsub C hC).2 (h₁ C hC) (h₂ C hC) (h₃ C hC)
  have hδ0 : 0 ≤ ∑ C ∈ cl, (δ₁ C + δ₂ C + δ₃ C) :=
    sum_nonneg (fun C hC => ImplI.nonneg _ _ (hpipe C hC))
  show ImplI (seqP (bfsP V) (mainP (pipeP wexp (A₁ V) (A₂ V) (A₃ V)) (Lb + 1) (valE _)
    (finE wexp _))) (baseInst N) (inOf (xinE r cl)) _ _ _
  by_cases hV : Nonempty V
  · let ρ : V := rootOf (Classical.arbitrary V)
    have hbfs := bfs_implI N ρ (fun _ => rfl) (xinE r cl)
    have hn : 1 ≤ Fintype.card V := Fintype.card_pos
    refine ImplI.mono _ _ (bindT hbfs (fun z hz => main_implI hV hcl hw hGR hGood hpipe r ρ z
      (fun v => hz v)) hδ0) ?_ (by rw [zero_add]) (fun _ h => h)
    rw [Prof.le_iff]
    simp only [qMain, Prof.rounds_add, Prof.rounds_mk, Prof.load_add, Prof.load_mk,
      Prof.msgs_add, Prof.msgs_mk, Pi.add_apply]
    refine ⟨by nlinarith, fun e => by nlinarith, ?_⟩
    have : Fintype.card V ≤ Fintype.card V ^ 2 := Nat.le_self_pow (by norm_num) _
    nlinarith
  · -- no nodes: no clusters, and every run succeeds at once
    have hcl0 : cl = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro C hC
      obtain ⟨e, -⟩ := (hsub C hC).2
      exact hV ⟨e.out.1⟩
    refine ImplI.of_forall _ _ hδ0 (fun ω => ?_)
    refine ⟨0, ⟨fun v => absurd ⟨v⟩ hV, fun s hs => absurd hs (Nat.not_lt_zero s)⟩,
      properUpTo_zero _ _ _ _, Nat.zero_le _, by simp [msgsUpTo], fun e => by simp [loadUpTo],
      fun g => ⟨EK V, ekAt N (construct cl (fun _ _ => [])) g⟩, fun g hg => ?_, ?_⟩
    · obtain ⟨v, rfl⟩ := baseInst_host hg
      exact absurd ⟨v⟩ hV
    · exact ⟨fun g => ekAt N (construct cl (fun _ _ => [])) g, fun g _ => rfl, _,
        hGood _ (by simp [hcl0]), fun v => rfl⟩

end APSP.Stoc.Congest
