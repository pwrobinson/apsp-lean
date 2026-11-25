import ApspStoc.Sec5EOAux

/-!
# Realizability of the ring-orientation contract

(The realizability of every other contract, and a model of the whole toolkit in which every
judgement with failure bound `< 1` has a satisfiable postcondition, is in `SatModel.lean`.)

The toolkit field `ringLE` promises, for every input satisfying `RingWF`, an output satisfying
`RingSpec`, with failure probability `0`. Such a promise is only meaningful if the postcondition
is satisfiable whenever the precondition holds. This file proves exactly that: for every well-formed
ring input there is an orientation satisfying `RingSpec`.

(An earlier version of `RingWF` lacked the field `ne`; then a segment end could be its own partner,
and `RingSpec` demanded `d ≠ d` — the contract was unsatisfiable on such inputs.)

The proof views the positions `(v, i)` as darts with two fixed-point-free involutions: the pairing
at the node (`i ↔ i xor 1`) and the segment partner; any 2-colouring that differs along both exists
by `dart_orient` (the components alternate between the two involutions, hence are even cycles).
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the position paired with position `i` at a node (`i xor 1`) -/
def pairIdx (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

lemma pairIdx_pairIdx (i : ℕ) : pairIdx (pairIdx i) = i := by
  unfold pairIdx; split_ifs <;> omega

lemma pairIdx_ne (i : ℕ) : pairIdx i ≠ i := by
  unfold pairIdx; split_ifs <;> omega

lemma pairIdx_lt {i n : ℕ} (hn : Even n) (hi : i < n) : pairIdx i < n := by
  obtain ⟨k, rfl⟩ := hn
  unfold pairIdx; split_ifs <;> omega

/-- the segment partner of the position `(v, i)`: the position of the reverse end at the partner -/
def segPartner (r : V → RingIn V) (d : V × ℕ) : V × ℕ :=
  match (r d.1)[d.2]? with
  | some (e, x, e') => (x, (r x).idxOf (e', d.1, e))
  | none => d

/-- all positions -/
noncomputable def ringDarts (r : V → RingIn V) : Finset (V × ℕ) :=
  univ.biUnion (fun v => (range (r v).length).image (fun i => (v, i)))

lemma mem_ringDarts {r : V → RingIn V} {d : V × ℕ} : d ∈ ringDarts r ↔ d.2 < (r d.1).length := by
  unfold ringDarts
  simp only [mem_biUnion, mem_univ, mem_image, mem_range, true_and]
  constructor
  · rintro ⟨v, i, hi, rfl⟩; exact hi
  · intro h; exact ⟨d.1, d.2, h, rfl⟩

omit [Fintype V] in
lemma segPartner_of {r : V → RingIn V} {v : V} {i : ℕ} {e x e'} (h : (r v)[i]? = some (e, x, e')) :
    segPartner r (v, i) = (x, (r x).idxOf (e', v, e)) := by
  unfold segPartner; simp only [h]

/-- **Realizability of `ringLE`'s contract**: every well-formed ring input has a consistent
orientation. -/
theorem ringSpec_realizable {cl : Finset (Finset (Sym2 V))} {S : Finset V} {r : V → RingIn V}
    (hr : RingWF cl S r) : ∃ d : V → List Bool, RingSpec r d := by
  classical
  -- entries of a position
  have hent : ∀ v i (hi : i < (r v).length), (r v)[i]? = some (r v)[i] :=
    fun v i hi => List.getElem?_eq_getElem hi
  have hε : ∀ d ∈ ringDarts r, segPartner r d ∈ ringDarts r ∧
      segPartner r (segPartner r d) = d ∧ segPartner r d ≠ d := by
    rintro ⟨v, i⟩ hd
    rw [mem_ringDarts] at hd
    rcases hrv : (r v)[i] with ⟨e, x, e'⟩
    have hget : (r v)[i]? = some (e, x, e') := by rw [List.getElem?_eq_getElem hd, hrv]
    have hmem : (e, x, e') ∈ r v := hrv ▸ List.getElem_mem hd
    have hsym := hr.symm v e x e' hmem
    have hlt : (r x).idxOf (e', v, e) < (r x).length := List.idxOf_lt_length_of_mem hsym
    have hgetx : (r x)[(r x).idxOf (e', v, e)] = (e', v, e) := List.getElem_idxOf hlt
    rw [segPartner_of hget]
    refine ⟨mem_ringDarts.2 hlt, ?_, ?_⟩
    · rw [segPartner_of (by rw [List.getElem?_eq_getElem hlt, hgetx])]
      have := List.Nodup.idxOf_getElem (hr.nodup v) i hd
      rw [hrv] at this
      rw [this]
    · intro heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hxv, hidx⟩ := heq
      subst hxv
      have h1 : (r x)[i] = (e', x, e) := by
        have : (r x)[(r x).idxOf (e', x, e)] = (e', x, e) := hgetx
        simpa [hidx] using this
      have h2 : (r x)[i] = (e, x, e') := hrv
      rw [h1] at h2
      simp only [Prod.mk.injEq] at h2
      exact hr.ne x e x e' hmem (by rw [h2.1])
  have hπ : ∀ d ∈ ringDarts r, (d.1, pairIdx d.2) ∈ ringDarts r ∧
      (fun d : V × ℕ => (d.1, pairIdx d.2)) ((d.1, pairIdx d.2)) = d := by
    rintro ⟨v, i⟩ hd
    rw [mem_ringDarts] at hd
    exact ⟨mem_ringDarts.2 (pairIdx_lt (hr.even v) hd), by simp [pairIdx_pairIdx]⟩
  obtain ⟨_, _, hc⟩ := dart_orient (fun d : V × ℕ => (d.1, pairIdx d.2)) (ringDarts r)
    (segPartner r) hε hπ
  obtain ⟨c, hcε, hcπ, _⟩ := hc (fun _ => false) (fun d _ hfix => by
    exact absurd (congrArg Prod.snd hfix) (pairIdx_ne _))
  refine ⟨fun v => (List.range (r v).length).map (fun i => c (v, i)), ?_, ?_, ?_⟩
  · intro v; simp
  · intro v i hi
    have hd : (v, 2 * i) ∈ ringDarts r := mem_ringDarts.2 (by simp only; omega)
    have hne : ((v, 2 * i).1, pairIdx (v, 2 * i).2) ≠ (v, 2 * i) := by
      simp only [ne_eq, Prod.mk.injEq, true_and]; exact pairIdx_ne _
    have := hcπ _ hd hne
    have hp : pairIdx (2 * i) = 2 * i + 1 := by unfold pairIdx; split_ifs <;> omega
    simp only [hp] at this
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    exact fun h => this h.symm
  · intro v x e e' i i' hv hx
    have hi : i < (r v).length := (List.getElem?_eq_some_iff.1 hv).1
    have hi' : i' < (r x).length := (List.getElem?_eq_some_iff.1 hx).1
    have hidx : (r x).idxOf (e', v, e) = i' := by
      obtain ⟨_, hxi⟩ := List.getElem?_eq_some_iff.1 hx
      rw [← hxi]; exact List.Nodup.idxOf_getElem (hr.nodup x) i' hi'
    have hs : segPartner r (v, i) = (x, i') := by rw [segPartner_of hv, hidx]
    have := hcε (v, i) (mem_ringDarts.2 hi)
    rw [hs] at this
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi')]
    simp only [List.getElem_map, List.getElem_range]
    exact fun h => this h.symm

/-! ## Regression tests: the two counterexamples of the independent audit -/

section Regression

/-- Audit counterexample 1: two segment ends at node `0`, each its own partner. -/
def badRing : Fin 3 → RingIn (Fin 3) := fun v =>
  if v = 0 then [(s(0, 1), 0, s(0, 1)), (s(0, 2), 0, s(0, 2))] else []

/-- On this input the postcondition of `ringLE` is unsatisfiable ... -/
example : ¬ ∃ d, RingSpec badRing d := by
  rintro ⟨d, -, -, h⟩
  exact h 0 0 s(0, 1) s(0, 1) 0 0 (by simp [badRing]) (by simp [badRing]) rfl

/-- ... and the repaired precondition `RingWF` rejects it. -/
example (cl : Finset (Finset (Sym2 (Fin 3)))) (S : Finset (Fin 3)) : ¬ RingWF cl S badRing :=
  fun h => h.ne 0 s(0, 1) 0 s(0, 1) (by simp [badRing]) rfl

/-- Audit counterexample 2: one edge `{0,1}` forming one cluster, all embedded aggregator paths
empty. With the earlier `EmbValid` (`∀ v, ∃ h`) every node could be "its own host", so a single
virtual aggregator would collect the inputs of both nodes without communication. The repaired
`EmbValid` (one host per overlay and cluster) rejects this embedding. -/
example : ¬ EmbValid (⊤ : SimpleGraph (Fin 2))
    (⟨{{s(0, 1)}}, fun _ _ _ => []⟩ : Overlays (Fin 2)) := by
  intro h
  obtain ⟨hh, _, hw⟩ := h.walk 0 (by simp) {s(0, 1)} (by simp)
  have h0 := hw 0 (mem_nodes.2 ⟨s(0, 1), by simp, by simp⟩)
  have h1 := hw 1 (mem_nodes.2 ⟨s(0, 1), by simp, by simp⟩)
  simp only [IsEdgeWalk] at h0 h1
  exact absurd (h0.trans h1.symm) (by decide)

end Regression

end APSP.Stoc
