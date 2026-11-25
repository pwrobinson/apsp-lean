import ApspStoc.Main

/-!
# Consistency of the assumptions

The trivial interpretation (`Impl := True`) satisfies every field of `Toolkit`, so the hypotheses
of `thm_5_6` are not contradictory. It also makes explicit what kind of statement `thm_5_6` is: it
holds for *every* interpretation of the judgement satisfying the toolkit; its meaning as a
statement about CONGEST comes from the intended interpretation (uniform randomized CONGEST
protocols), under which each field must be true: a standard fact [STD], a theorem of prior work
[PRIOR], a strengthened prior theorem [PRIOR+], or an implementation assumption for the paper's own
steps [IMPL]. The trivial model shows only that the fields are not contradictory; it is not a
realization by actual protocols. (The second hypothesis of `thm_5_6`, `Mixing`, is a theorem of
mathematics and is not part of the toolkit.)
-/

namespace APSP.Stoc

/-- closes the goals of the trivial model -/
macro "triv_toolkit" : tactic => `(tactic| (repeat (first
  | exact trivial
  | intro _
  | refine ⟨0, ?_⟩
  | refine ⟨PUnit.unit, ?_⟩
  | refine ⟨fun _ => PUnit.unit, ?_⟩
  | refine ⟨fun _ _ => PUnit.unit, ?_⟩)))

/-- A model of the toolkit in which every judgement holds. -/
def trivialToolkit : Toolkit where
  Alg := PUnit.{3}
  Impl := fun _ _ _ _ _ _ _ _ => True
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
  mono := by triv_toolkit
  weaken := by triv_toolkit
  weakenIO := by triv_toolkit
  bind := by triv_toolkit
  callR := by triv_toolkit
  locR := by triv_toolkit
  embThen := by triv_toolkit
  embWeaken := by triv_toolkit
  decompThen := by triv_toolkit
  decompStart := by triv_toolkit
  decompBase := by triv_toolkit
  decompStep := by triv_toolkit
  expDecomp := by triv_toolkit
  clusterSetup := by triv_toolkit
  rwLink := by triv_toolkit
  routeG0 := by triv_toolkit
  g0Then := by triv_toolkit
  routeViaWeaken := by triv_toolkit
  routeWeaken := by triv_toolkit
  embedConstruct := by triv_toolkit
  aggUp := by triv_toolkit
  aggDown := by triv_toolkit
  notify := by triv_toolkit
  ghs := by triv_toolkit
  treeCast := by triv_toolkit
  ringLE := by triv_toolkit
  perCompR := by triv_toolkit
  mstRed := by triv_toolkit
  approxRed := by triv_toolkit
  eoVirt := by triv_toolkit
  schedule := by triv_toolkit

/-- The main theorem instantiated in the trivial model (sanity check of the statement's shape). -/
example (hmix : Mixing) : ∃ (A : ℕ → trivialToolkit.Alg) (C k K : ℕ), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V), 1 ≤ Fintype.card V → (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ 0) →
    ∃ (p : Prof V) (δ : ℝ),
      trivialToolkit.Impl (A (Fintype.card V)) N (.compute none (V → ℕ × V) (APSPSpec N)) p δ ∧
      p.rounds ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ∧
      p.msgs ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ^ 2 ∧
      δ ≤ (K : ℝ) / (Fintype.card V : ℝ) ^ 1 :=
  thm_5_6 trivialToolkit hmix 0 1

end APSP.Stoc
