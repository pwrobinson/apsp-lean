import ApspStoc.Congest.RingLEStep

/-!
# Ring orientation in CONGEST: the output (`ringLE_congest`, part 6)

At the end, every end records the crossing events of its probes (`lEv`), which are those of the
election (`RS.evG`, `RS.lEv_eq`), and outputs the direction induced by the largest probe
(`bestDir`). By `RingComb.max_probe_crosses`, `probe_le_ringMax` and `dir_of_max_probe`, this is
the orientation `RingComb.dir` (`RS.bestDir_evG`), so the outputs form `ringDir r`
(`RS.outL_eq`), which satisfies `RingSpec` (`ringDir_spec`).
-/

namespace APSP.Stoc.Congest
namespace RingLE

open APSP Finset APSP.Stoc.RingComb

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

namespace RS

variable {Z : RS V}

open Classical in
/-- the crossing events of the end `x` in the election: (origin, departure?) -/
noncomputable def evG (Z : RS V) (x : V × ℕ) : Finset ((V × ℕ) × Bool) :=
  (range (phiOf Z.B + 1)).biUnion (fun i => (range (2 ^ i)).biUnion (fun k =>
    ((flightA Z.r i k).filter (fun a => depEnd Z.r a k = x)).image (fun a => (a, true)) ∪
    ((flightA Z.r i k).filter (fun a => arrEnd Z.r a k = x)).image (fun a => (a, false))))

lemma hopStart_le_tEnd {i k h : ℕ} (hi : i ≤ phiOf Z.B) (hk : k < 2 ^ i) (hh : h ≤ 2 * Z.D) :
    hopStart Z.D Z.B i k h ≤ tEnd Z.D Z.B :=
  (hopStart_le_phStart Z.D Z.B hk hh).trans (phStart_mono Z.D Z.B (by omega))

/-- **The recorded events are those of the election.** -/
lemma lEv_eq (hZ : Z.OK) {u : V} {H : ℕ → V → Option (Word V)}
    (hH : ∀ t < tEnd Z.D Z.B, ∀ w, H t w = Z.M w u t) (ix : ℕ) :
    lEv (Z.I.ctx u) (Z.r u) H ix = Z.evG (u, ix) := by
  classical
  unfold lEv evG
  simp only [bnd_ctx]
  refine biUnion_congr rfl (fun i hi => biUnion_congr rfl (fun k hk => ?_))
  rw [mem_range] at hi hk
  have hdep : lDep (Z.I.ctx u) (Z.r u) H i k = Z.held i k 0 u :=
    (lHeld_eq hZ hH).2 i (by omega) k hk 0 (Nat.zero_le _) (hopStart_le_tEnd (by omega) hk
      (Nat.zero_le _))
  have harr : lPhase (Z.I.ctx u) (Z.r u) H i (lSt (Z.I.ctx u) (Z.r u) H i) k =
      Z.held i k (2 * Z.D) u := by
    rw [lPhase_eq, hD_ctx]
    exact (lHeld_eq hZ hH).2 i (by omega) k hk _ le_rfl (hopStart_le_tEnd (by omega) hk le_rfl)
  rw [hdep, harr]
  congr 1
  · ext p
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨π, ⟨hπ, hix⟩, rfl⟩
      obtain ⟨a, ha, hp, rfl⟩ := mem_held.1 hπ
      have hx := depEnd_mem' hZ ha
      have hp' : (depEnd Z.r a k).1 = u := by rw [← hp, pos_zero]
      have hd := depIdx_pk hZ hx a 0
      rw [hp'] at hd
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      rw [← hix, hd]; exact Prod.ext hp' rfl
    · rintro ⟨a, ⟨ha, hx⟩, rfl⟩
      have hxm := depEnd_mem' hZ ha
      refine ⟨Z.pk a (depEnd Z.r a k) 0, ⟨mem_held.2 ⟨a, ha, by rw [pos_zero, hx], rfl⟩, ?_⟩, rfl⟩
      have hd := depIdx_pk hZ hxm a 0
      rw [show (depEnd Z.r a k).1 = u by rw [hx], show (depEnd Z.r a k).2 = ix by rw [hx]] at hd
      exact hd
  · ext p
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨π, ⟨hπ, hix⟩, rfl⟩
      obtain ⟨a, ha, hu, rfl⟩ := (mem_held_end hZ).1 hπ
      have hx := depEnd_mem' hZ ha
      obtain ⟨-, hai⟩ := arrIdx_pk hZ hx a (2 * Z.D)
      have hu' : (segPartner Z.r (depEnd Z.r a k)).1 = u := hu
      rw [hu'] at hai
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      show segPartner Z.r (depEnd Z.r a k) = (u, ix)
      rw [← hix, hai]
      exact Prod.ext hu' rfl
    · rintro ⟨a, ⟨ha, hx⟩, rfl⟩
      have hxm := depEnd_mem' hZ ha
      have hu : (arrEnd Z.r a k).1 = u := by rw [hx]
      refine ⟨_, ⟨(mem_held_end hZ).2 ⟨a, ha, hu, rfl⟩, ?_⟩, rfl⟩
      obtain ⟨-, hai⟩ := arrIdx_pk hZ hxm a (2 * Z.D)
      have hu' : (segPartner Z.r (depEnd Z.r a k)).1 = u := hu
      rw [hu'] at hai
      rw [hai]
      exact congrArg Prod.snd hx

lemma mem_evG {x : V × ℕ} {p : (V × ℕ) × Bool} :
    p ∈ Z.evG x ↔ ∃ i ≤ phiOf Z.B, ∃ k < 2 ^ i, p.1 ∈ flightA Z.r i k ∧
      ((p.2 = true ∧ depEnd Z.r p.1 k = x) ∨ (p.2 = false ∧ arrEnd Z.r p.1 k = x)) := by
  classical
  unfold evG
  simp only [mem_biUnion, mem_range, mem_union, mem_image, mem_filter]
  constructor
  · rintro ⟨i, hi, k, hk, ⟨a, ⟨ha, hx⟩, rfl⟩ | ⟨a, ⟨ha, hx⟩, rfl⟩⟩
    · exact ⟨i, by omega, k, hk, ha, Or.inl ⟨rfl, hx⟩⟩
    · exact ⟨i, by omega, k, hk, ha, Or.inr ⟨rfl, hx⟩⟩
  · rintro ⟨i, hi, k, hk, ha, ⟨h1, hx⟩ | ⟨h1, hx⟩⟩
    · exact ⟨i, by omega, k, hk, Or.inl ⟨p.1, ⟨ha, hx⟩, by rw [← h1]⟩⟩
    · exact ⟨i, by omega, k, hk, Or.inr ⟨p.1, ⟨ha, hx⟩, by rw [← h1]⟩⟩

/-- **The largest probe crossing an end induces the orientation `dir`.** -/
lemma bestDir_evG (hZ : Z.OK) {x : V × ℕ} (hx : x ∈ ringDarts Z.r) :
    bestDir (Z.evG x) = dir Z.r x := by
  -- the maximum's even-end probe crosses `x`
  obtain ⟨i0, hi0, k0, hfl, hcross⟩ := max_probe_crosses hZ.wf hx
  have hi0' : i0 ≤ phiOf Z.B := hi0 _ (card_elems_lt hZ).le
  have hfl' : evE (ringMax Z.r (elemOf x)) ∈ flightA Z.r i0 k0 := hfl
  have hk0 : k0 < 2 ^ i0 := (mem_flightA'.1 hfl').2.2.1.trans_le (hops_le_pow i0 _)
  obtain ⟨b0, hb0⟩ : ∃ b, (evE (ringMax Z.r (elemOf x)), b) ∈ Z.evG x := by
    rcases hcross with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨true, mem_evG.2 ⟨i0, hi0', k0, hk0, hfl', Or.inl ⟨rfl, h1⟩⟩⟩
    · exact ⟨false, mem_evG.2 ⟨i0, hi0', k0, hk0, hfl', Or.inr ⟨rfl, h1⟩⟩⟩
  have hne : (Z.evG x).Nonempty := ⟨_, hb0⟩
  unfold bestDir
  rw [dite_eq_left hne]
  obtain ⟨hpm, hpmax⟩ :=
    Classical.choose_spec ((Z.evG x).exists_max_image (fun p => eid (elemOf p.1)) hne)
  set p := Classical.choose ((Z.evG x).exists_max_image (fun p => eid (elemOf p.1)) hne)
  obtain ⟨i, -, k, -, hpf, hpe⟩ := mem_evG.1 hpm
  have hpd : p.1 ∈ ringDarts Z.r := (mem_flightA'.1 hpf).1
  have hle : eid (elemOf p.1) ≤ eid (ringMax Z.r (elemOf x)) := by
    apply probe_le_ringMax hZ.wf hpd (k := k)
    rcases hpe with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hge : eid (ringMax Z.r (elemOf x)) ≤ eid (elemOf p.1) := by
    have := hpmax _ hb0
    simpa only [elemOf_evE] using this
  have hpM : elemOf p.1 = ringMax Z.r (elemOf x) := eid_injective (le_antisymm hle hge)
  obtain ⟨hdep, harr⟩ := dir_of_max_probe hZ.wf hx hpM k
  unfold evDir
  rcases hpe with ⟨h2, h⟩ | ⟨h2, h⟩
  · rw [ite_eq_left h2, Bool.eq_iff_iff, decide_eq_true_iff]
    exact (hdep h).symm
  · rw [ite_eq_right (by rw [h2]; simp), Bool.eq_iff_iff, decide_eq_true_iff]
    exact (harr h).symm

/-- **The output of a node is its part of `ringDir r`.** -/
lemma outL_eq (hZ : Z.OK) {u : V} {H : ℕ → V → Option (Word V)}
    (hH : ∀ t < tEnd Z.D Z.B, ∀ w, H t w = Z.M w u t) :
    outL (Z.I.ctx u) (Z.r u) H = ringDir Z.r u := by
  unfold outL ringDir
  apply List.map_congr_left
  intro ix hix
  rw [List.mem_range] at hix
  rw [lEv_eq hZ hH ix, bestDir_evG hZ (mem_ringDarts.2 hix)]

end RS

end RingLE
end APSP.Stoc.Congest
