import ApspStoc.Congest.RingLELocal

/-!
# Ring orientation in CONGEST: the run follows the schedule (`ringLE_congest`, part 4)

* Bounds: a node has at most `|clustersOf v| ≤ min(ov, n)` segment ends, so there are at most
  `B = ov · min(sz, n)` elements, and fewer probes in flight than slots (`flightA_lt_slots`).
* `RS.held_succ`: the global held sets evolve by the local rules.
* `RS.lRecv_eq`, `RS.lHeldFrom_eq`: fed with the schedule, a node decodes exactly the packets
  moving to it, hence holds exactly the scheduled packets.
* `RS.dep0_eq`, `RS.depF_eq`, `RS.stOK_succ`: the departures and the status (candidate, decided)
  computed locally are those of the election of `RingComb` (`cand`, `Active`, `flightA`).
* `RS.lHeld_eq`: the main induction (phases, link steps, hops); `RS.sendL_eq`: the protocol sends
  exactly the messages of the schedule.
-/

namespace APSP.Stoc.Congest
namespace RingLE

open APSP Finset APSP.Stoc.RingComb

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma oth_spec {v : V} {e : Sym2 V} (h : v ∈ e) : e = s(v, oth v e) := by
  have hex : ∃ y, e = s(v, y) := Sym2.mem_iff_exists.1 h
  unfold oth
  rw [dite_eq_left hex]
  exact hex.choose_spec

namespace RS

variable {Z : RS V}

/-! ## Bounds -/

/-- a node has at most one segment end per cluster -/
lemma len_le_clusters (hZ : Z.OK) (v : V) : (Z.r v).length ≤ (clustersOf Z.E.cl v).card := by
  classical
  rw [← List.toFinset_card_of_nodup (hZ.wf.nodup v)]
  refine card_le_card_of_injOn (fun t => Cof Z.E.cl t.1) (fun t ht => ?_)
    (fun t ht t' ht' h => ?_)
  · have ht1 : t ∈ Z.r v := by simpa using ht
    obtain ⟨e, y, e'⟩ := t
    obtain ⟨C, hC, heC, -, hvC, -⟩ := hZ.wf.clus _ _ _ _ ht1
    rw [mem_coe]
    show Cof Z.E.cl e ∈ _
    rw [cof_eq hZ hC heC]
    exact mem_filter.2 ⟨hC, hvC⟩
  · have ht1 : t ∈ Z.r v := by simpa using ht
    have ht1' : t' ∈ Z.r v := by simpa using ht'
    obtain ⟨e, y, e'⟩ := t
    obtain ⟨f, y', f'⟩ := t'
    obtain ⟨C, hC, heC, -, -, -⟩ := hZ.wf.clus _ _ _ _ ht1
    obtain ⟨C', hC', heC', -, -, -⟩ := hZ.wf.clus _ _ _ _ ht1'
    simp only at h
    rw [cof_eq hZ hC heC, cof_eq hZ hC' heC'] at h
    subst h
    have h1 := hZ.wf.simple v C hC
    have h2 : ((Z.r v).filter (fun t => decide (t.1 ∈ C))).toFinset.card ≤ 1 :=
      (List.toFinset_card_le _).trans h1
    exact card_le_one.1 h2 _ (by simp [ht1, heC]) _ (by simp [ht1', heC'])

/-- a node is in at most `n` clusters -/
lemma clusters_le_card (hZ : Z.OK) (v : V) : (clustersOf Z.E.cl v).card ≤ Fintype.card V := by
  classical
  have hf : ∀ C ∈ clustersOf Z.E.cl v, ∃ e ∈ C, v ∈ e := fun C hC =>
    mem_nodes.1 (mem_filter.1 hC).2
  let f : Finset (Sym2 V) → V := fun C => if h : ∃ e ∈ C, v ∈ e then oth v h.choose else v
  rw [← card_univ]
  refine card_le_card_of_injOn f (fun _ _ => by simp) (fun C hC C' hC' h => ?_)
  have hC1 := hf C hC
  have hC2 := hf C' hC'
  simp only [f, dite_eq_left hC1, dite_eq_left hC2] at h
  obtain ⟨he1, hv1⟩ := hC1.choose_spec
  obtain ⟨he2, hv2⟩ := hC2.choose_spec
  have e1 := oth_spec hv1
  have e2 := oth_spec hv2
  rw [h] at e1
  rw [← e2] at e1
  by_contra hne
  exact disjoint_left.1 (hZ.emb.disj _ (mem_filter.1 hC).1 _ (mem_filter.1 hC').1 hne) he1
    (by rw [e1]; exact he2)

lemma ov_le_card (hZ : Z.OK) : Z.E.ov ≤ Fintype.card V :=
  Finset.sup_le (fun v _ => clusters_le_card hZ v)

/-- the origin indices are small -/
lemma len_le_card (hZ : Z.OK) (v : V) : (Z.r v).length ≤ Fintype.card V :=
  (len_le_clusters hZ v).trans (clusters_le_card hZ v)

lemma card_ringDarts (r : V → RingIn V) : (ringDarts r).card = ∑ v, (r v).length := by
  unfold ringDarts
  rw [card_biUnion]
  · refine sum_congr rfl (fun v _ => ?_)
    rw [card_image_of_injective _ (fun a b h => (Prod.ext_iff.1 h).2), card_range]
  · intro v _ w _ hvw
    rw [Function.onFun, disjoint_left]
    intro p hp hq
    simp only [mem_image] at hp hq
    obtain ⟨_, _, rfl⟩ := hp
    obtain ⟨_, _, h⟩ := hq
    exact hvw (congrArg Prod.fst h).symm

/-- **The number of elements is at most `B = ov · min(sz, n)`.** -/
lemma card_elems_le (hZ : Z.OK) : (ringElems Z.r).card ≤ Z.B := by
  have h1 : (ringElems Z.r).card ≤ (ringDarts Z.r).card := card_image_le
  rw [card_ringDarts] at h1
  have h2 : ∑ v, (Z.r v).length = ∑ v ∈ Z.S, (Z.r v).length := by
    rw [← sum_subset (subset_univ Z.S)]
    intro v _ hv
    rw [hZ.wf.out v hv]; rfl
  have h3 : ∑ v ∈ Z.S, (Z.r v).length ≤ Z.S.card * Z.E.ov := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum (fun v _ => (len_le_clusters hZ v).trans (Z.E.card_clustersOf_le_ov v))
  have h4 : Z.S.card ≤ min Z.sz (Fintype.card V) := le_min hZ.hsz (card_le_univ _)
  unfold B
  calc (ringElems Z.r).card ≤ Z.S.card * Z.E.ov := by omega
    _ ≤ min Z.sz (Fintype.card V) * Z.E.ov := Nat.mul_le_mul_right _ h4
    _ = _ := mul_comm _ _

lemma B_le (hZ : Z.OK) : Z.B ≤ Fintype.card V * Fintype.card V :=
  Nat.mul_le_mul (ov_le_card hZ) (min_le_right _ _)

/-- all rings are decided after phase `Φ` -/
lemma card_elems_lt (hZ : Z.OK) : (ringElems Z.r).card < 2 ^ phiOf Z.B :=
  (card_elems_le hZ).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) _)

/-- fewer probes in flight than slots -/
lemma flightA_lt_slots (hZ : Z.OK) (i k : ℕ) : (flightA Z.r i k).card < slots Z.B i := by
  have h1 := card_flightA_le hZ.wf i k
  have h2 : 4 * (ringElems Z.r).card / 2 ^ i ≤ 4 * Z.B / 2 ^ i :=
    Nat.div_le_div_right (by have := card_elems_le hZ; omega)
  unfold slots; omega

/-! ## Membership -/

lemma mem_flightA' {i k : ℕ} {a : V × ℕ} :
    a ∈ flightA Z.r i k ↔ a ∈ ringDarts Z.r ∧ elemOf a ∈ cand Z.r i ∧ k < hops Z.r i a ∧
      Active Z.r i a := by
  classical
  unfold flightA
  rw [mem_filter, mem_flight]
  tauto

lemma depEnd_mem' (hZ : Z.OK) {i k : ℕ} {a : V × ℕ} (ha : a ∈ flightA Z.r i k) :
    depEnd Z.r a k ∈ ringDarts Z.r :=
  depEnd_mem hZ.wf (mem_flightA'.1 ha).1 k

lemma mem_held {i k h : ℕ} {u : V} {π : Pk V} :
    π ∈ Z.held i k h u ↔ ∃ a ∈ flightA Z.r i k, Z.pos (depEnd Z.r a k) h = u ∧
      Z.pk a (depEnd Z.r a k) h = π := by
  unfold held
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hp⟩, rfl⟩; exact ⟨a, ha, hp, rfl⟩
  · rintro ⟨a, ha, hp, rfl⟩; exact ⟨a, ⟨ha, hp⟩, rfl⟩

lemma mem_recv {i k h : ℕ} {u : V} {π : Pk V} :
    π ∈ Z.recv i k h u ↔ ∃ a ∈ flightA Z.r i k, Z.moves (depEnd Z.r a k) h ∧
      Z.pos (depEnd Z.r a k) (h + 1) = u ∧ Z.pk a (depEnd Z.r a k) h = π := by
  unfold recv
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hm, hp⟩, rfl⟩; exact ⟨a, ha, hm, hp, rfl⟩
  · rintro ⟨a, ha, hm, hp, rfl⟩; exact ⟨a, ⟨ha, hm, hp⟩, rfl⟩

lemma pk_orig (a x : V × ℕ) (h : ℕ) : (Z.pk a x h).orig = a := rfl

lemma held_keyInj (i k h : ℕ) (u : V) : KeyInj (Z.held i k h u) := by
  intro π hπ π' hπ' hk
  obtain ⟨a, _, _, rfl⟩ := mem_held.1 hπ
  obtain ⟨a', _, _, rfl⟩ := mem_held.1 hπ'
  have := pkKey_eq hk
  rw [pk_orig, pk_orig] at this
  subst this; rfl

lemma card_held_le (i k h : ℕ) (u : V) : (Z.held i k h u).card ≤ (flightA Z.r i k).card :=
  card_image_le.trans (card_filter_le _ _)

/-- **The held sets evolve by the local rules.** -/
lemma held_succ (hZ : Z.OK) {i k h : ℕ} (hh : h < 2 * Z.D) (u : V) :
    Z.held i k (h + 1) u = (((Z.held i k h u).filter (fun π => stepL (Z.I.ctx u) h π = none)) ∪
      Z.recv i k h u).image (adjL (Z.I.ctx u) (h + 1)) := by
  ext π
  rw [mem_held, mem_image]
  constructor
  · rintro ⟨a, ha, hp, rfl⟩
    obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ ha)
    refine ⟨Z.pk a (depEnd Z.r a k) h, ?_, by rw [← hp]; exact adj_pk hZ hL a h⟩
    by_cases hm : Z.moves (depEnd Z.r a k) h
    · exact mem_union_right _ (mem_recv.2 ⟨a, ha, hm, hp, rfl⟩)
    · have hp' : Z.pos (depEnd Z.r a k) h = u := by rw [← pos_not_moves hL hh hm, hp]
      refine mem_union_left _ (mem_filter.2 ⟨mem_held.2 ⟨a, ha, hp', rfl⟩, ?_⟩)
      rw [← hp', step_pk hZ hL a hh, ite_eq_right hm]
  · rintro ⟨π0, hπ0, rfl⟩
    rcases mem_union.1 hπ0 with h1 | h1
    · obtain ⟨h1, h2⟩ := mem_filter.1 h1
      obtain ⟨a, ha, hp, rfl⟩ := mem_held.1 h1
      obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ ha)
      have hm : ¬ Z.moves (depEnd Z.r a k) h := by
        intro hm
        rw [← hp, step_pk hZ hL a hh, ite_eq_left hm] at h2
        cases h2
      have hp' : Z.pos (depEnd Z.r a k) (h + 1) = u := by rw [pos_not_moves hL hh hm, hp]
      refine ⟨a, ha, hp', ?_⟩
      rw [← hp']; exact (adj_pk hZ hL a h).symm
    · obtain ⟨a, ha, hm, hp, rfl⟩ := mem_recv.1 h1
      obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ ha)
      refine ⟨a, ha, hp, ?_⟩
      rw [← hp]; exact (adj_pk hZ hL a h).symm

/-! ## The schedule uses edges and valid words -/

lemma M_some {u w : V} {s : ℕ} {wd : Word V} (h : Z.M u w s = some wd) :
    ∃ q : Tm, q.Valid Z.D Z.B ∧ rnd Z.D Z.B q = s ∧ ∃ π, atRank (Z.held q.i q.k q.h u) q.σ = some π ∧
      stepL (Z.I.ctx u) q.h π = some w ∧ wd = pkWord π q.t := by
  unfold M at h
  cases hq : tq Z.D Z.B s with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    dsimp only at h
    obtain ⟨hv, hr⟩ := tq_some hq
    unfold sendFrom at h
    cases ha : atRank (Z.held q.i q.k q.h u) q.σ with
    | none => rw [ha] at h; cases h
    | some π =>
      rw [ha] at h
      simp only at h
      obtain ⟨hs, rfl⟩ := ite_some_eq h
      exact ⟨q, hv, hr, π, ha, hs, rfl⟩

lemma M_adj (hZ : Z.OK) {u w : V} {s : ℕ} (h : (Z.M u w s).isSome) :
    (Z.I.G).Adj u w := by
  obtain ⟨wd, hwd⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨q, hv, -, π, hπ, hs, -⟩ := M_some hwd
  obtain ⟨hmem, -⟩ := atRank_some hπ
  obtain ⟨a, ha, hp, rfl⟩ := mem_held.1 hmem
  obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ ha)
  rw [← hp, step_pk hZ hL a hv.2.2.1] at hs
  obtain ⟨hm, hw⟩ := ite_some_eq hs
  rw [← hw, ← hp]
  exact (moves_adj hZ hL hv.2.2.1 hm).1

lemma M_ok (hZ : Z.OK) {u w : V} {s : ℕ} {wd : Word V} (h : Z.M u w s = some wd) :
    WordOK (Fintype.card V) wd := by
  obtain ⟨q, -, -, π, hπ, -, rfl⟩ := M_some h
  obtain ⟨hmem, -⟩ := atRank_some hπ
  obtain ⟨a, ha, -, rfl⟩ := mem_held.1 hmem
  apply pkWord_ok
  have ha' := mem_ringDarts.1 (mem_flightA'.1 ha).1
  have := len_le_card hZ a.1
  show a.2 ≤ _
  omega

end RS

end RingLE
end APSP.Stoc.Congest
