import ApspStoc.Congest.RingLEMatch

/-!
# Ring orientation in CONGEST: local reconstruction (`ringLE_congest`, part 5)

Fed with the messages of the global schedule, a node reconstructs exactly the scheduled packets
(`RS.lRecv_eq`, `RS.lHeldFrom_eq`), departures (`RS.dep0_eq`, `RS.depF_eq`) and status
(`RS.stOK_succ`); `RS.lHeld_eq` is the main induction and `RS.sendL_eq` the conclusion: the
protocol sends exactly the messages of the schedule.
-/

namespace APSP.Stoc.Congest
namespace RingLE

open APSP Finset APSP.Stoc.RingComb

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

lemma pkDec_sendFrom (c : NCtx V) (h σ : ℕ) (X : Finset (Pk V)) (v : V) :
    pkDec (fun t => sendFrom c h σ t X v) =
      (atRank X σ).bind (fun π => if stepL c h π = some v then some π else none) := by
  unfold sendFrom
  cases atRank X σ with
  | none => rfl
  | some π =>
    simp only [Option.bind_some]
    by_cases hs : stepL c h π = some v
    · simp only [hs, ite_true]; exact pkDec_word π
    · simp only [hs, ite_false]; rfl

namespace RS

variable {Z : RS V}

/-- **Receiving**: fed with the schedule, a node decodes exactly the packets moving to it. -/
lemma lRecv_eq (hZ : Z.OK) {u : V} {H : ℕ → V → Option (Word V)} {T0 i k h : ℕ}
    (hH : ∀ t < T0, ∀ w, H t w = Z.M w u t) (hi : i ≤ phiOf Z.B) (hk : k < 2 ^ i)
    (hh : h < 2 * Z.D) (hT : hopStart Z.D Z.B i k (h + 1) ≤ T0) :
    lRecv (Z.I.ctx u) H i k h = Z.recv i k h u := by
  have key : ∀ w σ, σ < slots Z.B i →
      pkDec (fun t => H (rnd Z.D Z.B ⟨i, k, h, σ, t⟩) w) =
        (atRank (Z.held i k h w) σ).bind
          (fun π => if stepL (Z.I.ctx w) h π = some u then some π else none) := by
    intro w σ hσ
    rw [← pkDec_sendFrom]
    apply pkDec_congr
    intro t ht
    have hq : (⟨i, k, h, σ, t⟩ : Tm).Valid Z.D Z.B := ⟨hi, hk, hh, hσ, ht⟩
    have hlt := (rnd_lt_hopStart Z.D Z.B hq).2
    rw [hH _ (by simp only at hlt; omega) w]
    unfold M
    rw [tq_rnd Z.D Z.B hq]
  ext π
  unfold lRecv
  simp only [bnd_ctx, hD_ctx, mem_biUnion, mem_product, mem_univ, true_and, mem_range,
    Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨⟨w, σ⟩, hσ, hπ⟩
    simp only at hσ hπ
    rw [key w σ hσ, Option.bind_eq_some_iff] at hπ
    obtain ⟨π0, h0, h1⟩ := hπ
    obtain ⟨hs, rfl⟩ := ite_some_eq h1
    obtain ⟨hmem, -⟩ := atRank_some h0
    obtain ⟨a, ha, hp, rfl⟩ := mem_held.1 hmem
    obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ ha)
    rw [← hp, step_pk hZ hL a hh] at hs
    obtain ⟨hm, hpos⟩ := ite_some_eq hs
    exact mem_recv.2 ⟨a, ha, hm, hpos, rfl⟩
  · intro hπ
    obtain ⟨a, ha, hm, hp, rfl⟩ := mem_recv.1 hπ
    obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ ha)
    set w := Z.pos (depEnd Z.r a k) h
    have hmem : Z.pk a (depEnd Z.r a k) h ∈ Z.held i k h w := mem_held.2 ⟨a, ha, rfl, rfl⟩
    refine ⟨⟨w, rank (Z.held i k h w) (Z.pk a (depEnd Z.r a k) h)⟩, ?_, ?_⟩
    · exact (rank_lt_card hmem).trans_le ((card_held_le i k h w).trans
        (flightA_lt_slots hZ i k).le)
    · simp only
      rw [key _ _ ((rank_lt_card hmem).trans_le ((card_held_le i k h w).trans
        (flightA_lt_slots hZ i k).le)), atRank_rank (held_keyInj i k h w) hmem, Option.bind_some,
        step_pk hZ hL a hh, ite_eq_left hm, hp, ite_eq_left rfl]

/-- **Holding**: fed with the schedule, a node holds exactly the scheduled packets at every hop
of a link step whose departures are right. -/
lemma lHeldFrom_eq (hZ : Z.OK) {u : V} {H : ℕ → V → Option (Word V)} {T0 i k : ℕ}
    (hH : ∀ t < T0, ∀ w, H t w = Z.M w u t) (hi : i ≤ phiOf Z.B) (hk : k < 2 ^ i)
    {X0 : Finset (Pk V)} (h0 : X0 = Z.held i k 0 u) :
    ∀ h ≤ 2 * Z.D, hopStart Z.D Z.B i k h ≤ T0 →
      lHeldFrom (Z.I.ctx u) H i k X0 h = Z.held i k h u
  | 0, _, _ => h0
  | h + 1, hh, hT => by
    have ih := lHeldFrom_eq hZ hH hi hk h0 h (by omega)
      ((hopStart_mono_h Z.D Z.B i k (Nat.le_succ h)).trans hT)
    show (((lHeldFrom (Z.I.ctx u) H i k X0 h).filter _) ∪ _).image _ = _
    rw [ih, lRecv_eq hZ hH hi hk (by omega) hT, held_succ hZ (by omega)]

/-! ## Departures -/

lemma flightA_zero (hZ : Z.OK) {i : ℕ} {a : V × ℕ} :
    a ∈ flightA Z.r i 0 ↔ a ∈ ringDarts Z.r ∧ elemOf a ∈ cand Z.r i ∧ Active Z.r i a := by
  rw [mem_flightA']
  constructor
  · rintro ⟨h1, h2, -, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨h1, h2, hops_pos hZ.wf h1 i, h4⟩

lemma active_evE (hZ : Z.OK) {i : ℕ} {a : V × ℕ} (ha : a ∈ ringDarts Z.r) :
    Active Z.r i a ↔ Active Z.r i (evE (elemOf a)) := by
  obtain ⟨E, hE⟩ : ∃ E, elemOf a = E := ⟨_, rfl⟩
  rw [hE]
  rcases eq_evE_or_odE hE with rfl | rfl
  · rfl
  · rw [odE_eq_pairD, active_pairD hZ.wf ((evE_mem_iff hZ.wf).2 ha)]

/-- the packet of a departing probe, computed locally -/
lemma pkL_eq (hZ : Z.OK) {y : V × ℕ} (hy : y ∈ ringDarts Z.r) (a : V × ℕ) :
    pkL (Z.I.ctx y.1) (Z.r y.1) a y.2 = some (Z.pk a y 0) := by
  obtain ⟨hN, hL⟩ := linkF hZ hy
  unfold pkL
  rw [ent_eq hy, Option.map_some]
  congr 1
  simp only [pk, me_ctx, show (0 : ℕ) < Z.D by unfold D; omega, ite_true]
  rw [keyL_eq hZ hL]

/-- the own end from which a scheduled packet departs -/
lemma depIdx_pk (hZ : Z.OK) {y : V × ℕ} (hy : y ∈ ringDarts Z.r) (a : V × ℕ) (h : ℕ) :
    depIdx (Z.r y.1) (Z.pk a y h) = y.2 := by
  unfold depIdx
  have hent := ent_eq hy
  have hy' := mem_ringDarts.1 hy
  show (Z.r y.1).idxOf ((Z.ent y).1, (Z.ent y).2.1, (Z.ent y).2.2) = y.2
  have : (Z.r y.1)[y.2] = Z.ent y := by
    rw [List.getElem?_eq_getElem hy'] at hent; exact Option.some.inj hent
  rw [← this]
  exact List.Nodup.idxOf_getElem (hZ.wf.nodup _) _ hy'

/-- the own end at which a scheduled packet arrives -/
lemma arrIdx_pk (hZ : Z.OK) {y : V × ℕ} (hy : y ∈ ringDarts Z.r) (a : V × ℕ) (h : ℕ) :
    (segPartner Z.r y).1 = (Z.pk a y h).w ∧
      arrIdx (Z.r (segPartner Z.r y).1) (Z.pk a y h) = (segPartner Z.r y).2 := by
  obtain ⟨hN, hL⟩ := linkF hZ hy
  rw [hL.part]
  exact ⟨rfl, rfl⟩

/-- the arriving packets at the end of a link step -/
lemma mem_held_end (hZ : Z.OK) {i k : ℕ} {u : V} {π : Pk V} :
    π ∈ Z.held i k (2 * Z.D) u ↔ ∃ a ∈ flightA Z.r i k, (arrEnd Z.r a k).1 = u ∧
      Z.pk a (depEnd Z.r a k) (2 * Z.D) = π := by
  rw [mem_held]
  refine exists_congr fun a => and_congr_right fun ha => and_congr_left fun _ => ?_
  obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ ha)
  rw [pos_end hL, show arrEnd Z.r a k = segPartner Z.r (depEnd Z.r a k) from rfl, hL.part]

/-- **First departures**: the own probes of the active candidates. -/
lemma dep0_eq (hZ : Z.OK) {i : ℕ} (u : V) (st : ℕ → Bool × Bool)
    (hst : ∀ m, (u, m) ∈ ringElems Z.r → ((st m).1 = true ∧ (st m).2 = false ↔
      (u, m) ∈ cand Z.r i ∧ Active Z.r i (evE (u, m)))) :
    dep0 (Z.I.ctx u) (Z.r u) st = Z.held i 0 0 u := by
  ext π
  unfold dep0
  simp only [mem_biUnion, mem_filter, mem_range, Option.mem_toFinset, Option.mem_def]
  rw [mem_held]
  constructor
  · rintro ⟨ix, ⟨hix, hc⟩, hπ⟩
    have hy : (u, ix) ∈ ringDarts Z.r := mem_ringDarts.2 hix
    have hE : (u, ix / 2) ∈ ringElems Z.r := elemOf_mem hy
    obtain ⟨h1, h2⟩ := (hst _ hE).1 hc
    rw [me_ctx, pkL_eq hZ hy] at hπ
    cases hπ
    refine ⟨(u, ix), (flightA_zero hZ).2 ⟨hy, h1, (active_evE hZ hy).2 h2⟩, ?_, rfl⟩
    exact pos_zero _
  · rintro ⟨a, ha, hp, rfl⟩
    obtain ⟨hy, h1, h2⟩ := (flightA_zero hZ).1 ha
    have hpu : a.1 = u := by rw [← hp]; exact (pos_zero _).symm
    obtain ⟨v, ix⟩ := a
    simp only at hpu
    subst hpu
    refine ⟨ix, ⟨mem_ringDarts.1 hy, (hst _ (elemOf_mem hy)).2 ⟨h1, (active_evE hZ hy).1 h2⟩⟩, ?_⟩
    rw [me_ctx, pkL_eq hZ hy]
    rfl

lemma mem_flightA_succ {i k : ℕ} {a : V × ℕ} :
    a ∈ flightA Z.r i (k + 1) ↔ a ∈ flightA Z.r i k ∧ k + 1 < hops Z.r i a := by
  rw [mem_flightA', mem_flightA']
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, by omega, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2, -, h4⟩, h3⟩; exact ⟨h1, h2, h3, h4⟩

/-- **Forwarding**: the probes forwarded at link step `k + 1`. -/
lemma depF_eq (hZ : Z.OK) {i k : ℕ} (u : V) :
    depF (Z.I.ctx u) (Z.r u) i k (Z.held i k (2 * Z.D) u) = Z.held i (k + 1) 0 u := by
  classical
  have key : ∀ a ∈ flightA Z.r i k, (arrEnd Z.r a k).1 = u →
      (FwdOK (Z.I.ctx u) (Z.r u) i k (Z.pk a (depEnd Z.r a k) (2 * Z.D)) ↔
        k + 1 < hops Z.r i a) ∧
      pkL (Z.I.ctx u) (Z.r u) (Z.pk a (depEnd Z.r a k) (2 * Z.D)).orig
        (pairIdx (arrIdx (Z.r u) (Z.pk a (depEnd Z.r a k) (2 * Z.D)))) =
        some (Z.pk a (depEnd Z.r a (k + 1)) 0) := by
    intro a ha hu
    have hx := depEnd_mem' hZ ha
    obtain ⟨-, harr⟩ := arrIdx_pk hZ hx a (2 * Z.D)
    have hu' : (segPartner Z.r (depEnd Z.r a k)).1 = u := hu
    rw [hu'] at harr
    have harr' : arrIdx (Z.r u) (Z.pk a (depEnd Z.r a k) (2 * Z.D)) = (arrEnd Z.r a k).2 := harr
    have hy : depEnd Z.r a (k + 1) ∈ ringDarts Z.r := depEnd_mem hZ.wf (mem_flightA'.1 ha).1 _
    have hd : depEnd Z.r a (k + 1) = (u, pairIdx (arrEnd Z.r a k).2) := by
      rw [show depEnd Z.r a (k + 1) = pairD (arrEnd Z.r a k) from depEnd_succ a k]
      unfold pairD; rw [hu]
    constructor
    · unfold FwdOK
      rw [harr', forward_iff hZ.wf (mem_flightA'.1 ha).1 (mem_flightA'.1 ha).2.2.1, me_ctx]
      have : elemOf (segPartner Z.r ((sig Z.r)^[k] a)) = (u, (arrEnd Z.r a k).2 / 2) := by
        show elemOf (arrEnd Z.r a k) = _
        unfold elemOf; rw [hu]
      rw [this]; rfl
    · rw [harr', pk_orig]
      have := pkL_eq hZ hy a
      rw [hd] at this ⊢
      exact this
  ext π
  unfold depF
  simp only [mem_biUnion, mem_filter, Option.mem_toFinset, Option.mem_def]
  rw [mem_held]
  constructor
  · rintro ⟨π0, ⟨h0, hf⟩, hπ⟩
    obtain ⟨a, ha, hu, rfl⟩ := (mem_held_end hZ).1 h0
    obtain ⟨k1, k2⟩ := key a ha hu
    rw [k2] at hπ
    cases hπ
    refine ⟨a, mem_flightA_succ.2 ⟨ha, k1.1 hf⟩, ?_, rfl⟩
    rw [pos_zero, show depEnd Z.r a (k + 1) = pairD (arrEnd Z.r a k) from depEnd_succ a k]
    exact hu
  · rintro ⟨a, ha, hp, rfl⟩
    obtain ⟨ha', hfw⟩ := mem_flightA_succ.1 ha
    have hu : (arrEnd Z.r a k).1 = u := by
      rw [← hp, pos_zero, show depEnd Z.r a (k + 1) = pairD (arrEnd Z.r a k) from depEnd_succ a k]
      rfl
    obtain ⟨k1, k2⟩ := key a ha' hu
    exact ⟨_, ⟨(mem_held_end hZ).2 ⟨a, ha', hu, rfl⟩, k1.2 hfw⟩, k2⟩

/-! ## Status -/

/-- the status of the elements of `u` at the start of phase `i` is that of the election -/
def StOK (Z : RS V) (u : V) (i : ℕ) (st : ℕ → Bool × Bool) : Prop :=
  ∀ m, (u, m) ∈ ringElems Z.r → ((st m).1 = true ↔ (u, m) ∈ cand Z.r i) ∧
    ((u, m) ∈ cand Z.r i → ((st m).2 = true ↔ ¬ Active Z.r i (evE (u, m))))

lemma StOK.dep {u : V} {i : ℕ} {st : ℕ → Bool × Bool} (h : StOK Z u i st) (m : ℕ)
    (hm : (u, m) ∈ ringElems Z.r) :
    ((st m).1 = true ∧ (st m).2 = false ↔ (u, m) ∈ cand Z.r i ∧ Active Z.r i (evE (u, m))) := by
  obtain ⟨h1, h2⟩ := h m hm
  constructor
  · rintro ⟨a, b⟩
    have hc := h1.1 a
    refine ⟨hc, ?_⟩
    by_contra hna
    have := (h2 hc).2 hna
    rw [b] at this; cases this
  · rintro ⟨hc, hact⟩
    refine ⟨h1.2 hc, ?_⟩
    cases hb : (st m).2
    · rfl
    · exact absurd ((h2 hc).1 hb) (not_not.2 hact)

lemma stOK_zero (u : V) : StOK Z u 0 (fun _ => (true, false)) := by
  intro m hm
  refine ⟨⟨fun _ => hm, fun _ => rfl⟩, fun _ => ?_⟩
  simp only [Bool.false_eq_true, false_iff, not_not]
  exact Or.inl rfl

/-- the arrivals at the elements of `u` in phase `i` -/
lemma arr_iff (hZ : Z.OK) {u : V} {i : ℕ} {arr : ℕ → Finset (Pk V)}
    (harr : ∀ k < 2 ^ i, arr k = Z.held i k (2 * Z.D) u) (m : ℕ) (P : V × ℕ → Prop) :
    (∃ k < 2 ^ i, ∃ π ∈ arr k, arrIdx (Z.r u) π / 2 = m ∧ P (π.o, π.oi / 2)) ↔
      ∃ k < 2 ^ i, ∃ a ∈ flightA Z.r i k, elemOf (arrEnd Z.r a k) = (u, m) ∧ P (elemOf a) := by
  refine exists_congr fun k => and_congr_right fun hk => ?_
  rw [harr k hk]
  constructor
  · rintro ⟨π, hπ, h1, h2⟩
    obtain ⟨a, ha, hu, rfl⟩ := (mem_held_end hZ).1 hπ
    have hx := depEnd_mem' hZ ha
    obtain ⟨-, harr'⟩ := arrIdx_pk hZ hx a (2 * Z.D)
    have hu' : (segPartner Z.r (depEnd Z.r a k)).1 = u := hu
    rw [hu'] at harr'
    refine ⟨a, ha, ?_, h2⟩
    show ((arrEnd Z.r a k).1, (arrEnd Z.r a k).2 / 2) = (u, m)
    rw [hu, ← h1, harr']
  · rintro ⟨a, ha, h1, h2⟩
    have hu : (arrEnd Z.r a k).1 = u := congrArg Prod.fst h1
    refine ⟨_, (mem_held_end hZ).2 ⟨a, ha, hu, rfl⟩, ?_, h2⟩
    have hx := depEnd_mem' hZ ha
    obtain ⟨-, harr'⟩ := arrIdx_pk hZ hx a (2 * Z.D)
    have hu' : (segPartner Z.r (depEnd Z.r a k)).1 = u := hu
    rw [hu'] at harr'
    rw [harr']
    exact congrArg Prod.snd h1

/-- a larger candidate's probe arrived iff a larger active candidate reaches the element -/
lemma big_iff (hZ : Z.OK) {i : ℕ} {F : V × ℕ} :
    (∃ k < 2 ^ i, ∃ a ∈ flightA Z.r i k, elemOf (arrEnd Z.r a k) = F ∧ eid F < eid (elemOf a)) ↔
      ¬ ∀ E ∈ cand Z.r i, Active Z.r i (evE E) → eid F < eid E →
        ¬ Reach Z.r i (evE E) F ∧ ¬ Reach Z.r i (odE E) F := by
  constructor
  · rintro ⟨k, hk, a, ha, h1, h2⟩ hall
    obtain ⟨had, hac, hkh, hact⟩ := mem_flightA'.1 ha
    have hre : Reach Z.r i a F := ⟨k, hkh, h1⟩
    have := hall _ hac ((active_evE hZ had).1 hact) h2
    rcases eq_evE_or_odE (rfl : elemOf a = elemOf a) with h | h
    · rw [← h] at this; exact this.1 hre
    · rw [← h] at this; exact this.2 hre
  · intro h
    push Not at h
    obtain ⟨E, hE, hact, hlt, hre⟩ := h
    have hEe := cand_subset i hE
    have hev : evE E ∈ ringDarts Z.r := (mem_ringElems hZ.wf).1 hEe
    have hod : odE E ∈ ringDarts Z.r := (evE_mem_iff hZ.wf).1 hev
    have go : ∀ b ∈ ringDarts Z.r, elemOf b = E → Reach Z.r i b F →
        ∃ k < 2 ^ i, ∃ a ∈ flightA Z.r i k, elemOf (arrEnd Z.r a k) = F ∧
          eid F < eid (elemOf a) := by
      rintro b hb hbE ⟨k, hk, hkF⟩
      refine ⟨k, hk.trans_le (hops_le_pow i b), b, ?_, hkF, by rw [hbE]; exact hlt⟩
      refine mem_flightA'.2 ⟨hb, by rw [hbE]; exact hE, hk, ?_⟩
      rw [active_evE hZ hb, hbE]; exact hact
    by_cases h1 : Reach Z.r i (evE E) F
    · exact go _ hev (elemOf_evE E) h1
    · exact go _ hod (elemOf_odE E) (hre h1)

/-- the own probe of a candidate returned in phase `i` iff the candidate was active and its ring is
decided after phase `i` -/
lemma own_iff (hZ : Z.OK) {i : ℕ} {F : V × ℕ} (hF : F ∈ cand Z.r i) :
    (∃ k < 2 ^ i, ∃ a ∈ flightA Z.r i k, elemOf (arrEnd Z.r a k) = F ∧ elemOf a = F) ↔
      Active Z.r i (evE F) ∧ per Z.r (evE F) ≤ 2 ^ i := by
  have hFe := cand_subset i hF
  have hev : evE F ∈ ringDarts Z.r := (mem_ringElems hZ.wf).1 hFe
  constructor
  · rintro ⟨k, hk, a, ha, h1, h2⟩
    obtain ⟨had, -, hkh, hact⟩ := mem_flightA'.1 ha
    refine ⟨by rw [← h2, ← active_evE hZ had]; exact hact, ?_⟩
    have hre : Reach Z.r i a (elemOf a) := ⟨k, hkh, by rw [h2]; exact h1⟩
    have hper := (reach_self_iff hZ.wf had).1 hre
    rcases eq_evE_or_odE h2 with rfl | rfl
    · exact hper
    · rw [odE_eq_pairD, per_pairD hZ.wf hev] at hper; exact hper
  · rintro ⟨hact, hper⟩
    have hp := per_pos hZ.wf hev
    have hhops : hops Z.r i (evE F) = per Z.r (evE F) := min_eq_right hper
    refine ⟨per Z.r (evE F) - 1, by omega, evE F, ?_, ?_, elemOf_evE F⟩
    · exact mem_flightA'.2 ⟨hev, by rw [elemOf_evE]; exact hF, by rw [hhops]; omega, hact⟩
    · show elemOf (segPartner Z.r ((sig Z.r)^[per Z.r (evE F) - 1] (evE F))) = F
      rw [part_iter_pred hZ.wf hev, elemOf_pairD, elemOf_evE]

/-- **The status update** follows the election. -/
lemma stOK_succ (hZ : Z.OK) {u : V} {i : ℕ} {st : ℕ → Bool × Bool} (hst : StOK Z u i st)
    {arr : ℕ → Finset (Pk V)} (harr : ∀ k < 2 ^ i, arr k = Z.held i k (2 * Z.D) u) :
    StOK Z u (i + 1) (updSt (Z.I.ctx u) (Z.r u) i st arr) := by
  classical
  intro m hm
  set F : V × ℕ := (u, m)
  have hbig : BigArr (Z.I.ctx u) (Z.r u) i arr m ↔ ¬ ∀ E ∈ cand Z.r i, Active Z.r i (evE E) →
      eid F < eid E → ¬ Reach Z.r i (evE E) F ∧ ¬ Reach Z.r i (odE E) F := by
    unfold BigArr
    rw [me_ctx, arr_iff hZ harr m (fun E => eid F < eid E)]
    exact big_iff hZ
  have hown : OwnArr (Z.I.ctx u) (Z.r u) i arr m ↔
      ∃ k < 2 ^ i, ∃ a ∈ flightA Z.r i k, elemOf (arrEnd Z.r a k) = F ∧ elemOf a = F := by
    unfold OwnArr
    rw [me_ctx, arr_iff hZ harr m (fun E => E = F)]
  obtain ⟨h1, h2⟩ := hst m hm
  have hc : (updSt (Z.I.ctx u) (Z.r u) i st arr m).1 = true ↔ F ∈ cand Z.r (i + 1) := by
    simp only [updSt, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    rw [h1, hbig, not_not, mem_cand_succ_active hZ.wf]
  refine ⟨hc, fun hF => ?_⟩
  have hFi := cand_succ_subset i hF
  have hd := h2 hFi
  simp only [updSt, Bool.or_eq_true, decide_eq_true_eq]
  rw [hd, hown, own_iff hZ hFi]
  unfold Active
  simp only [add_eq_zero, one_ne_zero, and_false, false_or, Nat.add_sub_cancel, not_lt]
  constructor
  · rintro (h | ⟨-, h⟩)
    · push Not at h
      exact h.2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact h
  · intro h
    by_cases ha : i = 0 ∨ 2 ^ (i - 1) < per Z.r (evE F)
    · exact Or.inr ⟨ha, h⟩
    · exact Or.inl ha

/-! ## The main induction -/

/-- **Fed with the schedule, the protocol reconstructs the scheduled run**: the status of the
elements at the start of every phase, and the packets held at every hop. -/
theorem lHeld_eq (hZ : Z.OK) {u : V} {H : ℕ → V → Option (Word V)} {T0 : ℕ}
    (hH : ∀ t < T0, ∀ w, H t w = Z.M w u t) :
    (∀ i ≤ phiOf Z.B + 1, phStart Z.D Z.B i ≤ T0 → StOK Z u i (lSt (Z.I.ctx u) (Z.r u) H i)) ∧
    (∀ i ≤ phiOf Z.B, ∀ k < 2 ^ i, ∀ h ≤ 2 * Z.D, hopStart Z.D Z.B i k h ≤ T0 →
      lHeld (Z.I.ctx u) (Z.r u) H i k h = Z.held i k h u) := by
  -- within a phase with the right status
  have A : ∀ i ≤ phiOf Z.B, StOK Z u i (lSt (Z.I.ctx u) (Z.r u) H i) →
      ∀ k < 2 ^ i, ∀ h ≤ 2 * Z.D, hopStart Z.D Z.B i k h ≤ T0 →
        lHeld (Z.I.ctx u) (Z.r u) H i k h = Z.held i k h u := by
    intro i hi hst k
    induction k with
    | zero =>
      intro hk h hh hT
      exact lHeldFrom_eq hZ hH hi hk (dep0_eq hZ u _ hst.dep) h hh hT
    | succ k ih =>
      intro hk h hh hT
      have hprev := ih (by omega) (2 * Z.D) le_rfl (by
        rw [hopStart_end]
        exact (hopStart_mono_h Z.D Z.B i (k + 1) (Nat.zero_le h)).trans hT)
      refine lHeldFrom_eq hZ hH hi hk ?_ h hh hT
      show depF (Z.I.ctx u) (Z.r u) i k (lPhase (Z.I.ctx u) (Z.r u) H i
        (lSt (Z.I.ctx u) (Z.r u) H i) k) = _
      rw [lPhase_eq, hD_ctx, hprev, depF_eq hZ u]
  have B : ∀ i ≤ phiOf Z.B + 1, phStart Z.D Z.B i ≤ T0 →
      StOK Z u i (lSt (Z.I.ctx u) (Z.r u) H i) := by
    intro i
    induction i with
    | zero => intro _ _; exact stOK_zero u
    | succ i ih =>
      intro hi hT
      have hT' : phStart Z.D Z.B i ≤ T0 := (phStart_mono Z.D Z.B (Nat.le_succ i)).trans hT
      have hst := ih (by omega) hT'
      refine stOK_succ hZ hst (fun k hk => ?_)
      rw [lPhase_eq, hD_ctx]
      exact A i (by omega) hst k hk (2 * Z.D) le_rfl
        ((hopStart_le_phStart Z.D Z.B hk le_rfl).trans hT)
  refine ⟨B, fun i hi k hk h hh hT => A i hi (B i (by omega)
    ((phStart_le_hopStart Z.D Z.B i k h).trans hT)) k hk h hh hT⟩

/-- **The protocol sends exactly the messages of the schedule.** -/
theorem sendL_eq (hZ : Z.OK) (u : V) (s : ℕ) (v : V) :
    sendL (Z.I.ctx u) (Z.r u) (hget (schedHist Z.M u s)) s v = Z.M u v s := by
  have hH : ∀ t < s, ∀ w, hget (schedHist Z.M u s) t w = Z.M w u t :=
    fun t ht w => hget_schedHist Z.M u ht w
  unfold sendL
  conv_rhs => unfold M
  simp only [hD_ctx, bnd_ctx]
  cases hq : tq Z.D Z.B s with
  | none => rfl
  | some q =>
    obtain ⟨hv, hr⟩ := tq_some hq
    simp only
    rw [(lHeld_eq hZ hH).2 q.i hv.1 q.k hv.2.1 q.h hv.2.2.1.le
      (by rw [← hr]; exact (rnd_lt_hopStart Z.D Z.B hv).1)]

end RS

end RingLE
end APSP.Stoc.Congest
