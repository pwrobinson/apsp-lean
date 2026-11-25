import ApspStoc.Congest.RingLEOut

/-!
# Ring orientation in CONGEST: the costs (`ringLE_congest`, part 7)

* **Rounds**: phase `i` has `2^i` link steps of `2 D` hops of `slots B i = ⌊4B/2^i⌋ + 1` slots of
  `7` rounds, so `2^i · slots ≤ 4B + 2^i ≤ 6B + 2`; with `Φ + 1 ≤ 3 lg n` phases
  (`B ≤ n²`), `tEnd ≤ 336 · lg n · (ov+1)(dil+1)(sz+1)` (`tEnd_le`).
* **Messages and load** (`sends_le`): in a hop, the slots of a node carry its held packets that
  move (`hop_sends`); a packet crosses the edges of the two paths of its link once each
  (`link_count`). In a phase every end departs at most two probes and receives at most two
  (`card_departs_le_two`, `card_arrives_le_two`), and the path of the end `(v, i)` is the path of
  `v` in the cluster of the end, a different cluster for every end of `v` (`RingWF.simple`). So
  over a phase the probes cross the occurrences of every path edge of `S` at most `4` times, with
  `7` words each, and over `Φ + 1` phases at most `28 (Φ+1)` times: the messages over an edge
  are at most `28 (Φ+1) · rhoAgg j S e`, all messages at most `28 (Φ+1) · aggLen j S`.
-/

namespace APSP.Stoc.Congest
namespace RingLE

open APSP Finset APSP.Stoc.RingComb

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Sums over the rounds -/

lemma sum_range_mul (f : ℕ → ℕ) (a b : ℕ) :
    ∑ x ∈ range (a * b), f x = ∑ k ∈ range a, ∑ y ∈ range b, f (k * b + y) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

lemma sum_phStart (D B : ℕ) (f : ℕ → ℕ) (m : ℕ) :
    ∑ s ∈ range (phStart D B m), f s =
      ∑ i ∈ range m, ∑ s ∈ range (phLen D B i), f (phStart D B i + s) := by
  induction m with
  | zero => simp [phStart]
  | succ m ih => rw [phStart_succ, sum_range_add, ih, sum_range_succ]

/-- the rounds, decomposed by time points -/
lemma sum_tEnd (D B : ℕ) (f : ℕ → ℕ) :
    ∑ s ∈ range (tEnd D B), f s = ∑ i ∈ range (phiOf B + 1), ∑ k ∈ range (2 ^ i),
      ∑ h ∈ range (2 * D), ∑ σ ∈ range (slots B i), ∑ t ∈ range 7,
        f (rnd D B ⟨i, k, h, σ, t⟩) := by
  unfold tEnd
  rw [sum_phStart]
  refine sum_congr rfl (fun i _ => ?_)
  unfold phLen
  rw [sum_range_mul]
  refine sum_congr rfl (fun k _ => ?_)
  unfold stepLen
  rw [sum_range_mul]
  refine sum_congr rfl (fun h _ => ?_)
  unfold hopLen
  rw [sum_range_mul]
  refine sum_congr rfl (fun σ _ => sum_congr rfl (fun t _ => ?_))
  unfold rnd hopStart stepLen hopLen
  congr 1
  simp only
  ring

lemma ite_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then (1 : ℕ) else 0) = if q then 1 else 0 := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left (h.1 hp)]
  · rw [ite_eq_right hp, ite_eq_right (fun hq => hp (h.2 hq))]

open Classical in
/-- counting the positions of a list satisfying a predicate -/
lemma sum_count_range {α : Type} (P : α → Prop) [DecidablePred P] :
    ∀ (l : List α) (N : ℕ), l.length ≤ N →
      ∑ h ∈ range N, (if ∃ e, l[h]? = some e ∧ P e then 1 else 0) = l.countP (fun e => decide (P e))
  | [], N, _ => by simp
  | a :: l, N, hN => by
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      exists_eq_left']
    rw [sum_count_range P l N (by simp at hN; omega), List.countP_cons]
    by_cases ha : P a <;> simp [ha]

namespace RS

variable {Z : RS V}

/-- **The hops of a link**: a packet crosses each edge occurrence of its two paths once. -/
lemma link_count {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) (P : Sym2 V → Prop)
    [DecidablePred P] :
    ((range (2 * Z.D)).filter (fun h => Z.moves x h ∧ P s(Z.pos x h, Z.pos x (h + 1)))).card =
      (Z.pUp x).countP (fun e => decide (P e)) + (Z.pDn x).countP (fun e => decide (P e)) := by
  have hlu := hL.lUp
  have hld := hL.lDn
  have hD : Z.D = Z.E.dil + 1 := rfl
  rw [card_filter, two_mul, sum_range_add]
  congr 1
  · rw [← sum_count_range P (Z.pUp x) Z.D (by omega)]
    refine sum_congr rfl (fun h hh => ?_)
    rw [mem_range] at hh
    apply ite_iff
    unfold moves
    rw [ite_eq_left hh]
    constructor
    · rintro ⟨hm, hp⟩
      refine ⟨(Z.pUp x)[h], List.getElem?_eq_getElem hm, ?_⟩
      have e1 : Z.pos x h = wnode (Z.pUp x) x.1 h := by unfold pos; rw [ite_eq_left hh.le]
      have e2 : Z.pos x (h + 1) = wnode (Z.pUp x) x.1 (h + 1) := by
        unfold pos; rw [ite_eq_left (by omega)]
      rw [wnode_get hL.wUp hm, ← e1, ← e2]; exact hp
    · rintro ⟨e, he, hp⟩
      have hm : h < (Z.pUp x).length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at he; cases he
      refine ⟨hm, ?_⟩
      rw [List.getElem?_eq_getElem hm, Option.some.injEq] at he
      have e1 : Z.pos x h = wnode (Z.pUp x) x.1 h := by unfold pos; rw [ite_eq_left hh.le]
      have e2 : Z.pos x (h + 1) = wnode (Z.pUp x) x.1 (h + 1) := by
        unfold pos; rw [ite_eq_left (by omega)]
      rw [e1, e2, ← wnode_get hL.wUp hm, he]; exact hp
  · rw [← sum_count_range P (Z.pDn x) Z.D (by omega)]
    conv_rhs => rw [← sum_range_reflect]
    refine sum_congr rfl (fun h hh => ?_)
    rw [mem_range] at hh
    apply ite_iff
    unfold moves
    rw [ite_eq_right (by omega), show 2 * Z.D - 1 - (Z.D + h) = Z.D - 1 - h by omega]
    have e1 : Z.pos x (Z.D + h) = wnode (Z.pDn x) (Z.ent x).2.1 (Z.D - 1 - h + 1) := by
      rw [pos_dn hL (h := Z.D + h) (by omega) (by omega)]; congr 1; omega
    have e2 : Z.pos x (Z.D + h + 1) = wnode (Z.pDn x) (Z.ent x).2.1 (Z.D - 1 - h) := by
      rw [pos_dn hL (h := Z.D + h + 1) (by omega) (by omega)]; congr 1; omega
    rw [e1, e2]
    constructor
    · rintro ⟨hm, hp⟩
      refine ⟨(Z.pDn x)[Z.D - 1 - h], List.getElem?_eq_getElem hm, ?_⟩
      rw [wnode_get hL.wDn hm, Sym2.eq_swap]; exact hp
    · rintro ⟨e, he, hp⟩
      have hm : Z.D - 1 - h < (Z.pDn x).length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at he; cases he
      refine ⟨hm, ?_⟩
      rw [List.getElem?_eq_getElem hm, Option.some.injEq] at he
      rw [Sym2.eq_swap, ← wnode_get hL.wDn hm, he]; exact hp

/-- **The sends of a hop**: over its slots, the messages (on edges satisfying `P`) are the words of
the held packets that move. -/
lemma hop_sends (hZ : Z.OK) (P : Sym2 V → Prop) [DecidablePred P] {i k h : ℕ} (hi : i ≤ phiOf Z.B) (hk : k < 2 ^ i)
    (hh : h < 2 * Z.D) :
    ∑ σ ∈ range (slots Z.B i), ∑ t ∈ range 7,
      ((univ.filter (fun uv : V × V => (Z.M uv.1 uv.2 (rnd Z.D Z.B ⟨i, k, h, σ, t⟩)).isSome)).filter
        (fun uv => P s(uv.1, uv.2))).card ≤
      7 * ((flightA Z.r i k).filter (fun a => Z.moves (depEnd Z.r a k) h ∧
        P s(Z.pos (depEnd Z.r a k) h, Z.pos (depEnd Z.r a k) (h + 1)))).card := by
  set T := (flightA Z.r i k).filter (fun a => Z.moves (depEnd Z.r a k) h ∧
    P s(Z.pos (depEnd Z.r a k) h, Z.pos (depEnd Z.r a k) (h + 1))) with hTdef
  set g : V × ℕ → ℕ := fun a => rank (Z.held i k h (Z.pos (depEnd Z.r a k) h))
    (Z.pk a (depEnd Z.r a k) h) with hgdef
  -- the sends of a slot
  have hslot : ∀ σ ∈ range (slots Z.B i), ∀ t ∈ range 7,
      ((univ.filter (fun uv : V × V => (Z.M uv.1 uv.2 (rnd Z.D Z.B ⟨i, k, h, σ, t⟩)).isSome)).filter
        (fun uv => P s(uv.1, uv.2))).card ≤ (T.filter (fun a => g a = σ)).card := by
    intro σ hσ t ht
    rw [mem_range] at hσ ht
    have hq : (⟨i, k, h, σ, t⟩ : Tm).Valid Z.D Z.B := ⟨hi, hk, hh, hσ, ht⟩
    let f : V × V → V × ℕ := fun uv => match atRank (Z.held i k h uv.1) σ with
      | some π => π.orig
      | none => (uv.1, 0)
    refine card_le_card_of_injOn f (fun uv huv => ?_) (fun uv huv uv' huv' he => ?_)
    · simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv
      obtain ⟨hs, hP⟩ := huv
      unfold M at hs
      rw [tq_rnd Z.D Z.B hq] at hs
      unfold sendFrom at hs
      simp only at hs
      cases ha : atRank (Z.held i k h uv.1) σ with
      | none => rw [ha] at hs; simp at hs
      | some π =>
        rw [ha] at hs
        simp only at hs
        by_cases hst : stepL (Z.I.ctx uv.1) h π = some uv.2
        · obtain ⟨hmem, hr⟩ := atRank_some ha
          obtain ⟨a, haf, hp, rfl⟩ := mem_held.1 hmem
          obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ haf)
          rw [← hp, step_pk hZ hL a hh] at hst
          obtain ⟨hm, hw⟩ := ite_some_eq hst
          have hfa : f uv = a := by simp only [f, ha, pk_orig]
          rw [mem_coe, hfa, mem_filter, hTdef, mem_filter]
          refine ⟨⟨haf, hm, ?_⟩, ?_⟩
          · rw [hp, hw]; exact hP
          · show rank (Z.held i k h (Z.pos (depEnd Z.r a k) h)) (Z.pk a (depEnd Z.r a k) h) = σ
            rw [hp]; exact hr
        · rw [ite_eq_right hst] at hs; simp at hs
    · simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv huv'
      obtain ⟨hs, -⟩ := huv
      obtain ⟨hs', -⟩ := huv'
      unfold M at hs hs'
      rw [tq_rnd Z.D Z.B hq] at hs hs'
      unfold sendFrom at hs hs'
      simp only at hs hs'
      cases ha : atRank (Z.held i k h uv.1) σ with
      | none => rw [ha] at hs; simp at hs
      | some π =>
        cases ha' : atRank (Z.held i k h uv'.1) σ with
        | none => rw [ha'] at hs'; simp at hs'
        | some π' =>
          rw [ha] at hs; rw [ha'] at hs'
          simp only at hs hs'
          by_cases hst : stepL (Z.I.ctx uv.1) h π = some uv.2
          · by_cases hst' : stepL (Z.I.ctx uv'.1) h π' = some uv'.2
            · obtain ⟨hmem, -⟩ := atRank_some ha
              obtain ⟨a, haf, hp, rfl⟩ := mem_held.1 hmem
              obtain ⟨hmem', -⟩ := atRank_some ha'
              obtain ⟨a', haf', hp', rfl⟩ := mem_held.1 hmem'
              have hfe : a = a' := by
                have := he
                simp only [f, ha, ha', pk_orig] at this
                exact this
              subst hfe
              obtain ⟨hN, hL⟩ := linkF hZ (depEnd_mem' hZ haf)
              rw [← hp, step_pk hZ hL a hh] at hst
              rw [← hp', step_pk hZ hL a hh] at hst'
              obtain ⟨-, hw⟩ := ite_some_eq hst
              obtain ⟨-, hw'⟩ := ite_some_eq hst'
              exact Prod.ext (hp.symm.trans hp') (hw.symm.trans hw')
            · rw [ite_eq_right hst'] at hs'; simp at hs'
          · rw [ite_eq_right hst] at hs; simp at hs
  calc _ ≤ ∑ σ ∈ range (slots Z.B i), ∑ t ∈ range 7, (T.filter (fun a => g a = σ)).card :=
        sum_le_sum (fun σ hσ => sum_le_sum (fun t ht => hslot σ hσ t ht))
    _ = 7 * ∑ σ ∈ range (slots Z.B i), (T.filter (fun a => g a = σ)).card := by
        rw [mul_sum]; refine sum_congr rfl (fun σ _ => ?_); rw [sum_const, card_range, smul_eq_mul]
    _ ≤ 7 * T.card := by
        apply Nat.mul_le_mul_left
        have e : ∀ σ ∈ range (slots Z.B i), T.filter (fun a => g a = σ) =
            (T.filter (fun a => g a < slots Z.B i)).filter (fun a => g a = σ) := by
          intro σ hσ
          ext a
          simp only [mem_filter, mem_range] at hσ ⊢
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hσ⟩, h2⟩
          · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        rw [sum_congr rfl (fun σ hσ => by rw [e σ hσ]),
          ← card_eq_sum_card_fiberwise (fun a ha => mem_range.2 (mem_filter.1 ha).2)]
        exact card_le_card (filter_subset _ _)


/-! ## Regrouping by ends -/

lemma ent_mem3 {x : V × ℕ} (hx : x ∈ ringDarts Z.r) :
    ((Z.ent x).1, (Z.ent x).2.1, (Z.ent x).2.2) ∈ Z.r x.1 := ent_mem hx

lemma ringDarts_disj (r : V → RingIn V) :
    ((univ : Finset V) : Set V).PairwiseDisjoint
      (fun v => (range (r v).length).image (fun i => (v, i))) := by
  intro v _ w _ hvw
  rw [Function.onFun, disjoint_left]
  intro p hp hq
  simp only [mem_image] at hp hq
  obtain ⟨_, _, rfl⟩ := hp
  obtain ⟨_, _, h⟩ := hq
  exact hvw (congrArg Prod.fst h).symm

lemma sum_darts (r : V → RingIn V) (g : V × ℕ → ℕ) :
    ∑ y ∈ ringDarts r, g y = ∑ v, ∑ ix ∈ range (r v).length, g (v, ix) := by
  unfold ringDarts
  rw [sum_biUnion (ringDarts_disj r)]
  refine sum_congr rfl (fun v _ => ?_)
  rw [sum_image (fun a _ b _ h => (Prod.ext_iff.1 h).2)]

/-- the ends of `v` lie in different clusters -/
lemma sum_darts_le (hZ : Z.OK) (f : V → Finset (Sym2 V) → ℕ) :
    ∑ y ∈ ringDarts Z.r, f y.1 (Z.cl y) ≤ ∑ v ∈ Z.S, ∑ C ∈ clustersOf Z.E.cl v, f v C := by
  classical
  rw [sum_darts Z.r (fun y => f y.1 (Z.cl y))]
  rw [← sum_subset (subset_univ Z.S) (fun v _ hv => by rw [hZ.wf.out v hv]; simp)]
  refine sum_le_sum (fun v _ => ?_)
  have hinj : Set.InjOn (fun ix => Z.cl (v, ix)) (range (Z.r v).length : Set ℕ) := by
    intro ix hix ix' hix' h
    simp only [coe_range, Set.mem_Iio] at hix hix'
    have hy : (v, ix) ∈ ringDarts Z.r := mem_ringDarts.2 hix
    have hy' : (v, ix') ∈ ringDarts Z.r := mem_ringDarts.2 hix'
    obtain ⟨C, hC, heC, -, -, -⟩ := hZ.wf.clus _ _ _ _ (ent_mem3 hy)
    obtain ⟨C', hC', heC', -, -, -⟩ := hZ.wf.clus _ _ _ _ (ent_mem3 hy')
    simp only [cl] at h
    rw [cof_eq hZ hC heC, cof_eq hZ hC' heC'] at h
    subst h
    have h1 := hZ.wf.simple v C hC
    have h2 : ((Z.r v).filter (fun t => decide (t.1 ∈ C))).toFinset.card ≤ 1 :=
      (List.toFinset_card_le _).trans h1
    have he := card_le_one.1 h2 (Z.ent (v, ix)) (by simp [ent_mem hy, heC])
      (Z.ent (v, ix')) (by simp [ent_mem hy', heC'])
    have g1 := ent_eq hy
    have g2 := ent_eq hy'
    rw [List.getElem?_eq_getElem hix] at g1
    rw [List.getElem?_eq_getElem hix'] at g2
    have := (Option.some.inj g1).trans (he.trans (Option.some.inj g2).symm)
    exact (List.Nodup.getElem_inj_iff (hZ.wf.nodup v)).1 this
  rw [← sum_image (f := f v) hinj]
  refine sum_le_sum_of_subset (fun C hC => ?_)
  simp only [mem_image, mem_range] at hC
  obtain ⟨ix, hix, rfl⟩ := hC
  have hy : (v, ix) ∈ ringDarts Z.r := mem_ringDarts.2 hix
  obtain ⟨C, hC, heC, -, hvC, -⟩ := hZ.wf.clus _ _ _ _ (ent_mem3 hy)
  show Cof Z.E.cl (Z.ent (v, ix)).1 ∈ _
  rw [cof_eq hZ hC heC]
  exact mem_filter.2 ⟨hC, hvC⟩

/-- the partner's path is the path of the partner end -/
lemma pDn_eq (hZ : Z.OK) {x : V × ℕ} (hx : x ∈ ringDarts Z.r) :
    Z.pDn x = Z.pUp (segPartner Z.r x) := by
  obtain ⟨hN, hL⟩ := linkF hZ hx
  have hsym := hZ.wf.symm _ _ _ _ (ent_mem3 hx)
  have hlt := List.idxOf_lt_length_of_mem hsym
  have hy : segPartner Z.r x ∈ ringDarts Z.r := part_mem hZ.wf hx
  have hmem2 : (Z.r (segPartner Z.r x).1)[(segPartner Z.r x).2]? =
      some ((Z.ent x).2.2, x.1, (Z.ent x).1) := by
    rw [hL.part]
    exact (List.getElem?_eq_getElem hlt).trans (congrArg some (List.getElem_idxOf hlt))
  have hent : Z.ent (segPartner Z.r x) = ((Z.ent x).2.2, x.1, (Z.ent x).1) :=
    Option.some.inj ((ent_eq hy).symm.trans hmem2)
  have hcly : Z.cl (segPartner Z.r x) = Z.cl x := by
    unfold cl
    rw [hent]
    simp only
    rw [cof_eq hZ hL.clC hL.e'C]
    rfl
  have hy1 : (segPartner Z.r x).1 = (Z.ent x).2.1 := by rw [hL.part]
  unfold pDn pUp
  rw [hcly, hy1]

/-- departures regrouped by ends: at most two per end and phase -/
lemma sum_dep_le (hZ : Z.OK) (i : ℕ) (g : V × ℕ → ℕ) :
    ∑ k ∈ range (2 ^ i), ∑ a ∈ flightA Z.r i k, g (depEnd Z.r a k) ≤
      2 * ∑ y ∈ ringDarts Z.r, g y := by
  classical
  rw [sum_sigma' (range (2 ^ i)) (fun k => flightA Z.r i k) (fun k a => g (depEnd Z.r a k))]
  rw [← sum_fiberwise_of_maps_to (s := (range (2 ^ i)).sigma (fun k => flightA Z.r i k))
    (t := ringDarts Z.r) (g := fun p => depEnd Z.r p.2 p.1)
    (fun p hp => depEnd_mem' hZ (mem_sigma.1 hp).2)]
  rw [mul_sum]
  refine sum_le_sum (fun y _ => ?_)
  rw [sum_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  refine le_trans (card_le_card_of_injOn (fun p => p.2) (t := departs Z.r i y)
    (fun p hp => ?_) (fun p hp p' hp' h => ?_)) (card_departs_le_two hZ.wf i y)
  · simp only [coe_filter, mem_sigma, mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨-, ha⟩, hy⟩ := hp
    obtain ⟨h1, h2, h3, -⟩ := mem_flightA'.1 ha
    exact mem_departs.2 ⟨h1, h2, p.1, h3, hy⟩
  · simp only [coe_filter, mem_sigma, mem_range, Set.mem_ofPred_eq] at hp hp'
    obtain ⟨k, a⟩ := p
    obtain ⟨k', a'⟩ := p'
    simp only at h hp hp'
    subst h
    have hk := dep_step_unique (mem_flightA'.1 hp.1.2).2.2.1 (mem_flightA'.1 hp'.1.2).2.2.1 hp.2
      hp'.2
    rw [hk]

/-- arrivals regrouped by ends: at most two per end and phase -/
lemma sum_arr_le (hZ : Z.OK) (i : ℕ) (g : V × ℕ → ℕ) :
    ∑ k ∈ range (2 ^ i), ∑ a ∈ flightA Z.r i k, g (arrEnd Z.r a k) ≤
      2 * ∑ y ∈ ringDarts Z.r, g y := by
  classical
  rw [sum_sigma' (range (2 ^ i)) (fun k => flightA Z.r i k) (fun k a => g (arrEnd Z.r a k))]
  rw [← sum_fiberwise_of_maps_to (s := (range (2 ^ i)).sigma (fun k => flightA Z.r i k))
    (t := ringDarts Z.r) (g := fun p => arrEnd Z.r p.2 p.1)
    (fun p hp => part_mem hZ.wf (depEnd_mem' hZ (mem_sigma.1 hp).2))]
  rw [mul_sum]
  refine sum_le_sum (fun y hy => ?_)
  rw [sum_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  refine le_trans (card_le_card_of_injOn (fun p => p.2)
    (t := (ringDarts Z.r).filter (fun a => elemOf a ∈ cand Z.r i ∧
      ∃ k < hops Z.r i a, segPartner Z.r ((sig Z.r)^[k] a) = y))
    (fun p hp => ?_) (fun p hp p' hp' h => ?_)) (card_arrives_le_two hZ.wf i hy)
  · simp only [coe_filter, mem_sigma, mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨-, ha⟩, hy⟩ := hp
    obtain ⟨h1, h2, h3, -⟩ := mem_flightA'.1 ha
    simp only [coe_filter, Set.mem_ofPred_eq]
    exact ⟨h1, h2, p.1, h3, hy⟩
  · simp only [coe_filter, mem_sigma, mem_range, Set.mem_ofPred_eq] at hp hp'
    obtain ⟨k, a⟩ := p
    obtain ⟨k', a'⟩ := p'
    simp only at h hp hp'
    subst h
    have had := (mem_flightA'.1 hp.1.2).1
    have e : (sig Z.r)^[k] a = (sig Z.r)^[k'] a := by
      have := congrArg (segPartner Z.r) (hp.2.trans hp'.2.symm)
      rwa [part_part hZ.wf (iter_mem hZ.wf had k), part_part hZ.wf (iter_mem hZ.wf had k')] at this
    have hk := dep_step_unique (mem_flightA'.1 hp.1.2).2.2.1 (mem_flightA'.1 hp'.1.2).2.2.1 e rfl
    rw [hk]


/-! ## Totals -/

/-- the edge usage of the paths of `S` (filtered by `P`) -/
noncomputable def useP (Z : RS V) (P : Sym2 V → Prop) [DecidablePred P] : ℕ :=
  ∑ v ∈ Z.S, ∑ C ∈ clustersOf Z.E.cl v, (Z.E.path Z.j v C).countP (fun e => decide (P e))

/-- the moves of a phase: every path edge occurrence of `S` is crossed at most `4` times -/
lemma phase_moves (hZ : Z.OK) (P : Sym2 V → Prop) [DecidablePred P] (i : ℕ) :
    ∑ k ∈ range (2 ^ i), ∑ h ∈ range (2 * Z.D),
      ((flightA Z.r i k).filter (fun a => Z.moves (depEnd Z.r a k) h ∧
        P s(Z.pos (depEnd Z.r a k) h, Z.pos (depEnd Z.r a k) (h + 1)))).card ≤ 4 * Z.useP P := by
  have hswap : ∀ k, ∑ h ∈ range (2 * Z.D),
      ((flightA Z.r i k).filter (fun a => Z.moves (depEnd Z.r a k) h ∧
        P s(Z.pos (depEnd Z.r a k) h, Z.pos (depEnd Z.r a k) (h + 1)))).card =
      ∑ a ∈ flightA Z.r i k, ((Z.pUp (depEnd Z.r a k)).countP (fun e => decide (P e)) +
        (Z.pUp (arrEnd Z.r a k)).countP (fun e => decide (P e))) := by
    intro k
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun a ha => ?_)
    have hx := depEnd_mem' hZ ha
    obtain ⟨hN, hL⟩ := linkF hZ hx
    rw [← card_filter, link_count hL P, pDn_eq hZ hx]
  rw [sum_congr rfl (fun k _ => hswap k)]
  simp only [sum_add_distrib]
  have h1 : ∑ k ∈ range (2 ^ i), ∑ a ∈ flightA Z.r i k,
      (Z.pUp (depEnd Z.r a k)).countP (fun e => decide (P e)) ≤
      2 * ∑ y ∈ ringDarts Z.r, (Z.pUp y).countP (fun e => decide (P e)) :=
    sum_dep_le hZ i (fun y => (Z.pUp y).countP (fun e => decide (P e)))
  have h2 : ∑ k ∈ range (2 ^ i), ∑ a ∈ flightA Z.r i k,
      (Z.pUp (arrEnd Z.r a k)).countP (fun e => decide (P e)) ≤
      2 * ∑ y ∈ ringDarts Z.r, (Z.pUp y).countP (fun e => decide (P e)) :=
    sum_arr_le hZ i (fun y => (Z.pUp y).countP (fun e => decide (P e)))
  have h3 : ∑ y ∈ ringDarts Z.r, (Z.pUp y).countP (fun e => decide (P e)) ≤ Z.useP P :=
    sum_darts_le hZ (fun v C => (Z.E.path Z.j v C).countP (fun e => decide (P e)))
  omega

/-- **Messages over edges satisfying `P`**: at most `28 (Φ+1)` per path edge occurrence of `S`. -/
theorem sends_le (hZ : Z.OK) (P : Sym2 V → Prop) [DecidablePred P] :
    ∑ s ∈ range (tEnd Z.D Z.B),
      ((univ.filter (fun uv : V × V => (Z.M uv.1 uv.2 s).isSome)).filter
        (fun uv => P s(uv.1, uv.2))).card ≤ 28 * (phiOf Z.B + 1) * Z.useP P := by
  rw [sum_tEnd]
  calc _ ≤ ∑ i ∈ range (phiOf Z.B + 1), ∑ k ∈ range (2 ^ i), ∑ h ∈ range (2 * Z.D),
        7 * ((flightA Z.r i k).filter (fun a => Z.moves (depEnd Z.r a k) h ∧
          P s(Z.pos (depEnd Z.r a k) h, Z.pos (depEnd Z.r a k) (h + 1)))).card := by
        refine sum_le_sum (fun i hi => sum_le_sum (fun k hk => sum_le_sum (fun h hh => ?_)))
        rw [mem_range] at hi hk hh
        exact hop_sends hZ P (by omega) hk hh
    _ ≤ ∑ _i ∈ range (phiOf Z.B + 1), 7 * (4 * Z.useP P) := by
        refine sum_le_sum (fun i _ => ?_)
        simp only [← mul_sum]
        exact Nat.mul_le_mul_left _ (phase_moves hZ P i)
    _ = 28 * (phiOf Z.B + 1) * Z.useP P := by
        rw [sum_const, card_range, smul_eq_mul]; ring

/-! ## Rounds -/

lemma phStart_eq_sum (D B m : ℕ) : phStart D B m = ∑ i ∈ range m, phLen D B i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [phStart_succ, ih, sum_range_succ]

lemma pow_phi_le (B : ℕ) : 2 ^ phiOf B ≤ 2 * B + 2 := by
  unfold phiOf
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  · have := Nat.pow_log_le_self 2 (show B ≠ 0 by omega)
    omega

lemma phLen_le (D B i : ℕ) (hi : i ≤ phiOf B) : phLen D B i ≤ 14 * D * (6 * B + 2) := by
  unfold phLen stepLen hopLen slots
  have h1 : 2 ^ i * (4 * B / 2 ^ i) ≤ 4 * B := Nat.mul_div_le _ _
  have h2 : 2 ^ i ≤ 2 ^ phiOf B := Nat.pow_le_pow_right (by norm_num) hi
  have h3 := pow_phi_le B
  have h4 : 2 ^ i * (4 * B / 2 ^ i + 1) ≤ 6 * B + 2 := by rw [mul_add, mul_one]; omega
  calc 2 ^ i * (2 * D * ((4 * B / 2 ^ i + 1) * 7)) = 14 * D * (2 ^ i * (4 * B / 2 ^ i + 1)) := by
        ring
    _ ≤ 14 * D * (6 * B + 2) := Nat.mul_le_mul_left _ h4

lemma tEnd_le' (D B : ℕ) : tEnd D B ≤ (phiOf B + 1) * (14 * D * (6 * B + 2)) := by
  unfold tEnd
  rw [phStart_eq_sum]
  calc _ ≤ ∑ _i ∈ range (phiOf B + 1), 14 * D * (6 * B + 2) :=
        sum_le_sum (fun i hi => phLen_le D B i (by rw [mem_range] at hi; omega))
    _ = _ := by rw [sum_const, card_range, smul_eq_mul]

lemma log_sq_le (n : ℕ) : Nat.log 2 (n * n) ≤ 2 * Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) n
    have h2 : n * n < 2 ^ (2 * Nat.log 2 n + 2) := by
      calc n * n < 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1) := Nat.mul_lt_mul'' h1 h1
        _ = _ := by rw [← pow_add]; ring_nf
    have := Nat.log_lt_of_lt_pow (show n * n ≠ 0 by positivity) h2
    omega

/-- the number of phases is `O(lg n)` -/
lemma phi_le {n B : ℕ} (hB : B ≤ n * n) : phiOf B + 1 ≤ 3 * lg n := by
  unfold phiOf lg
  have := (Nat.log_mono_right hB).trans (log_sq_le n)
  omega

end RS

end RingLE
end APSP.Stoc.Congest
