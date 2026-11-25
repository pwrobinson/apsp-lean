import ApspStoc.Congest.KTGatherFlood

/-!
# The gather phase: the windows on the BFS tree

For a node `u ∈ S` fed with the history of the schedule `gM`, the local computations of the
windows SZ, PRE and PP agree with the global objects of `KTGraph.lean`:

* window SZ: the local subtree size is `ksz u` when it is sent (`szL_eq`, `szSend_eq`);
* window PRE: the local preorder number is `kpre u` (`preL_eq`), and the numbers sent to the
  children are theirs (`preSend_eq`);
* window PP: the ID sent up in round `j` is the one of `upSet u j`, the ID sent down the one of
  `downSet u j` (`upL_eq`, `downL_eq`, `ppSend_eq`); both sets have at most one element since
  preorder numbers are injective;
* the output is `S` (`outSet_eq`).
-/

namespace APSP.Stoc.Congest

namespace KT

open APSP Finset

set_option linter.unusedSectionVars false

variable {U : Type} [Fintype U] [DecidableEq U]

/-- a sum with a single non-zero term -/
lemma sum_range_single (L j0 a : ℕ) (P : Prop) [Decidable P] (f : ℕ → ℕ)
    (hf : ∀ j < L, f j = if j = j0 ∧ P then a else 0) :
    ∑ j ∈ range L, f j = if j0 < L ∧ P then a else 0 := by
  rw [sum_congr rfl (fun j hj => hf j (mem_range.1 hj))]
  by_cases hP : P
  · simp only [hP, and_true]
    rw [sum_ite_eq' (range L) j0 (fun _ => a)]
    simp [mem_range]
  · simp [hP]

lemma idOf_map (o : Option U) : idOf (o.map Word.id) = o := by
  cases o <;> rfl

section Sched

variable {S : Finset U} {N : WNet S} (hS : S.Nonempty)
include hS

/-! ## Window SZ -/

lemma rcvNum_sz {u w : U} {s : ℕ} :
    rcvNum (schedHist (gM S N) u s) (tSZ S.card (nB U)) S.card w =
      if kpar S N w = some u ∧ tSZ S.card (nB U) + (S.card - 1 - kdep S N w) < s then
        ksz S N w else 0 := by
  classical
  have hn : 0 < S.card := card_pos.2 hS
  unfold rcvNum
  rw [sum_range_single S.card (S.card - 1 - kdep S N w) (ksz S N w)
    (kpar S N w = some u ∧ tSZ S.card (nB U) + (S.card - 1 - kdep S N w) < s)]
  · exact if_congr ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩ rfl rfl
  · intro j hj
    rw [hget_sched]
    by_cases hs : tSZ S.card (nB U) + j < s
    · rw [ite_eq_left hs, gM_sz hj]
      unfold gSZ
      by_cases h : kpar S N w = some u ∧ j + 1 + kdep S N w = S.card
      · have := kdep_lt (N := N) hS (kpar_spec h.1).1
        rw [ite_eq_left h, ite_eq_left ⟨by omega, h.1, by omega⟩]; rfl
      · rw [ite_eq_right h, ite_eq_right]
        · rfl
        · rintro ⟨h1, h2, h3⟩
          have := kdep_lt (N := N) hS (kpar_spec h2).1
          exact h ⟨h2, by omega⟩
    · rw [ite_eq_right hs, ite_eq_right]
      · rfl
      · rintro ⟨h1, h2, h3⟩; exact hs (by omega)

lemma sum_rcvNum_sz {u : U} (_hu : u ∈ S) {s : ℕ}
    (hs : tSZ S.card (nB U) + (S.card - 1 - kdep S N u) ≤ s) :
    ∑ w, rcvNum (schedHist (gM S N) u s) (tSZ S.card (nB U)) S.card w =
      ∑ c ∈ kidsOf S (kpar S N) u, ksz S N c := by
  classical
  simp only [rcvNum_sz hS]
  rw [← sum_filter]
  refine sum_congr ?_ (fun _ _ => rfl)
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_kidsOf]
  constructor
  · rintro ⟨h1, -⟩; exact ⟨(kpar_spec h1).1, h1⟩
  · rintro ⟨hw, h1⟩
    refine ⟨h1, ?_⟩
    have h2 := (kpar_spec h1).2.2.2
    have h3 := kdep_lt (N := N) hS hw
    omega

lemma szL_eq {u : U} (hu : u ∈ S) {s : ℕ}
    (hs : tSZ S.card (nB U) + (S.card - 1 - kdep S N u) ≤ s) :
    szL S.card (nB U) (schedHist (gM S N) u s) = ksz S N u := by
  unfold szL
  rw [sum_rcvNum_sz hS hu hs, ksz_eq hS hu]

lemma szSend_eq {u : U} (hu : u ∈ S) {j : ℕ} (_hj : j < S.card) (v : U) :
    szSend S.card (nB U) ((ktInst S N).ctx u) (schedHist (gM S N) u (tSZ S.card (nB U) + j)) j v =
      gSZ S N j u v := by
  classical
  unfold szSend gSZ
  have hme : ((ktInst S N).ctx u).me = u := rfl
  rw [hme, parTL_eq hS hu (by omega), depL_eq hS hu (by omega)]
  by_cases h : kpar S N u = some v ∧ j + 1 + kdep S N u = S.card
  · rw [ite_eq_left h, ite_eq_left h, szL_eq hS hu (by omega)]
  · rw [ite_eq_right h, ite_eq_right h]

/-! ## Window PRE -/

lemma rcvNum_sz_full {u w : U} {s : ℕ} (hs : tPRE S.card (nB U) ≤ s) :
    rcvNum (schedHist (gM S N) u s) (tSZ S.card (nB U)) S.card w =
      if kpar S N w = some u then ksz S N w else 0 := by
  have hn : 0 < S.card := card_pos.2 hS
  rw [rcvNum_sz hS]
  unfold tPRE at hs
  by_cases h : kpar S N w = some u
  · rw [ite_eq_left ⟨h, by omega⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.1), ite_eq_right h]

lemma rcvNum_pre {u w : U} {s : ℕ} :
    rcvNum (schedHist (gM S N) u s) (tPRE S.card (nB U)) S.card w =
      if kpar S N u = some w ∧ tPRE S.card (nB U) + kdep S N w < s then kpre S N u else 0 := by
  classical
  unfold rcvNum
  rw [sum_range_single S.card (kdep S N w) (kpre S N u)
    (kpar S N u = some w ∧ tPRE S.card (nB U) + kdep S N w < s)]
  · by_cases h : kpar S N u = some w ∧ tPRE S.card (nB U) + kdep S N w < s
    · have := kdep_lt (N := N) hS (kpar_spec h.1).2.1
      rw [ite_eq_left ⟨this, h⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h]
  · intro j hj
    rw [hget_sched]
    by_cases hs : tPRE S.card (nB U) + j < s
    · rw [ite_eq_left hs, gM_pre hj]
      unfold gPRE
      by_cases h : kpar S N u = some w ∧ j = kdep S N w
      · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1, by rw [← h.2]; exact hs⟩]; rfl
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2.1, h'.1⟩)]; rfl
    · rw [ite_eq_right hs, ite_eq_right (fun h' => hs (by rw [h'.1]; exact h'.2.2))]; rfl

lemma preL_eq {u : U} (_hu : u ∈ S) {s : ℕ} (hs : tPRE S.card (nB U) + kdep S N u ≤ s) :
    preL S.card (nB U) (schedHist (gM S N) u s) = kpre S N u := by
  classical
  unfold preL
  simp only [rcvNum_pre hS]
  cases hp : kpar S N u with
  | none =>
    rw [kpre_none hp]
    simp
  | some p =>
    have hd := (kpar_spec hp).2.2.2
    have : ∀ w, (if some p = some w ∧ tPRE S.card (nB U) + kdep S N w < s then kpre S N u else 0) =
        if p = w then kpre S N u else 0 := by
      intro w
      by_cases hw : p = w
      · subst hw; rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left rfl]
      · rw [ite_eq_right (fun h => hw (Option.some.inj h.1)), ite_eq_right hw]
    simp only [this, sum_ite_eq, mem_univ, ite_true]

lemma preSend_eq {u : U} (hu : u ∈ S) {j : ℕ} (_hj : j < S.card) (v : U) :
    preSend S.card (nB U) ((ktInst S N).ctx u) (schedHist (gM S N) u (tPRE S.card (nB U) + j)) j v =
      gPRE S N j u v := by
  classical
  have hs1 : tSZ S.card (nB U) ≤ tPRE S.card (nB U) + j := by unfold tPRE; omega
  unfold preSend gPRE
  have hme : ((ktInst S N).ctx u).me = u := rfl
  rw [hme, kidsL_eq hS hs1, depL_eq hS hu hs1]
  have hc : (v ∈ kidsOf S (kpar S N) u ∧ j = kdep S N u) ↔ (kpar S N v = some u ∧ j = kdep S N u) := by
    rw [mem_kidsOf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨(kpar_spec h.1).1, h.1⟩, h.2⟩⟩
  by_cases h : kpar S N v = some u ∧ j = kdep S N u
  · rw [ite_eq_left (hc.2 h), ite_eq_left h, preL_eq hS hu (by omega), kpre_some h.1]
    congr 3
    refine sum_congr rfl (fun c hc => ?_)
    rw [mem_filter, mem_kidsOf] at hc
    rw [rcvNum_sz_full hS (by unfold tPRE; omega), ite_eq_left hc.1.2]
  · rw [ite_eq_right (fun h' => h (hc.1 h')), ite_eq_right h]

/-! ## Window PP -/

lemma upSet_sub {u : U} {j : ℕ} {x y : U} (hx : x ∈ upSet S N u j) (hy : y ∈ upSet S N u j) :
    x = y := by
  obtain ⟨ℓ, -, hℓ⟩ := srcB_last (U := U) hS
  unfold upSet at hx hy
  rw [mem_filter, mem_desc] at hx hy
  exact kpre_inj (N := N) hS hℓ hx.1.1 hy.1.1 (by omega)

lemma downSet_sub {u : U} {j : ℕ} {x y : U} (hx : x ∈ downSet S N u j) (hy : y ∈ downSet S N u j) :
    x = y := by
  obtain ⟨ℓ, -, hℓ⟩ := srcB_last (U := U) hS
  unfold downSet at hx hy
  rw [mem_filter] at hx hy
  exact kpre_inj (N := N) hS hℓ hx.1 hy.1 (by omega)

lemma argminIdx_up {u : U} {j : ℕ} {x : U} : argminIdx (upSet S N u j) = some x ↔ x ∈ upSet S N u j :=
  ⟨argminIdx_mem, fun h => argminIdx_of_sub h (fun _ hy => upSet_sub hS hy h)⟩

lemma argminIdx_down {u : U} {j : ℕ} {x : U} :
    argminIdx (downSet S N u j) = some x ↔ x ∈ downSet S N u j :=
  ⟨argminIdx_mem, fun h => argminIdx_of_sub h (fun _ hy => downSet_sub hS hy h)⟩

lemma upSet_self {u : U} (hu : u ∈ S) {j : ℕ} (h : kpre S N u + S.card = j + kdep S N u) :
    upSet S N u j = {u} := by
  ext x
  rw [mem_singleton]
  have hu' : u ∈ upSet S N u j := by
    unfold upSet; rw [mem_filter, mem_desc]; exact ⟨⟨hu, Relation.ReflTransGen.refl⟩, h⟩
  exact ⟨fun hx => upSet_sub hS hx hu', fun hx => hx ▸ hu'⟩

lemma upSet_zero {u : U} (hu : u ∈ S) : upSet S N u 0 = ∅ := by
  have := kdep_lt (N := N) hS hu
  refine eq_empty_of_forall_notMem (fun x hx => ?_)
  unfold upSet at hx
  rw [mem_filter] at hx
  omega

lemma upSet_succ {u : U} (hu : u ∈ S) {j : ℕ} (h : kpre S N u + S.card ≠ j + kdep S N u)
    (hj : 1 ≤ j) : upSet S N u j = (kidsOf S (kpar S N) u).biUnion (fun c => upSet S N c (j - 1)) := by
  ext x
  simp only [upSet, mem_filter, mem_biUnion]
  rw [desc_eq kpar_mem kpar_rk hu, mem_insert, mem_biUnion]
  constructor
  · rintro ⟨rfl | ⟨c, hc, hx⟩, hk⟩
    · exact absurd hk h
    · have := (kpar_spec (mem_kidsOf.1 hc).2).2.2.2
      exact ⟨c, hc, hx, by omega⟩
  · rintro ⟨c, hc, hx, hk⟩
    have := (kpar_spec (mem_kidsOf.1 hc).2).2.2.2
    exact ⟨Or.inr ⟨c, hc, hx⟩, by omega⟩

lemma kpar_not_both {u w : U} (h1 : kpar S N u = some w) (h2 : kpar S N w = some u) : False := by
  have a := (kpar_spec h1).2.2.2
  have b := (kpar_spec h2).2.2.2
  omega

lemma gPP_down_ne {u w : U} {j : ℕ} {x : U} (h : some w ≠ kpar S N u)
    (hx : gPP S N j w u = some (.id x)) : kpar S N w = some u ∧ x ∈ upSet S N w j := by
  classical
  unfold gPP at hx
  split_ifs at hx with h1 h2
  · refine ⟨h1, ?_⟩
    cases ha : argminIdx (upSet S N w j) with
    | none => rw [ha] at hx; cases hx
    | some y =>
      rw [ha] at hx
      simp only [Option.map_some, Option.some.injEq, Word.id.injEq] at hx
      subst hx
      exact argminIdx_mem ha
  · exact absurd h2.symm h

lemma preL_pp {u : U} (hu : u ∈ S) {j : ℕ} :
    preL S.card (nB U) (schedHist (gM S N) u (tPP S.card (nB U) + j)) = kpre S N u := by
  have := kdep_lt (N := N) hS hu
  exact preL_eq hS hu (by unfold tPP; omega)

lemma upL_eq {u : U} (hu : u ∈ S) {j : ℕ} (hj : j < 3 * S.card) :
    upL S.card (nB U) u (schedHist (gM S N) u (tPP S.card (nB U) + j)) j =
      argminIdx (upSet S N u j) := by
  classical
  have hs1 : tSZ S.card (nB U) ≤ tPP S.card (nB U) + j := by unfold tPP tPRE; omega
  unfold upL
  rw [preL_pp hS hu, depL_eq hS hu hs1, parTL_eq hS hu hs1]
  by_cases h1 : kpre S N u + S.card = j + kdep S N u
  · rw [ite_eq_left h1, upSet_self hS hu h1]
    exact (argminIdx_of_sub (mem_singleton_self u) (fun y hy => mem_singleton.1 hy)).symm
  · rw [ite_eq_right h1]
    by_cases h0 : j = 0
    · subst h0
      rw [ite_eq_left rfl, upSet_zero hS hu]
      exact (argminIdx_eq_none.2 rfl).symm
    · rw [ite_eq_right h0, upSet_succ hS hu h1 (by omega)]
      unfold rcvIdEx
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_biUnion]
      have hidx : tPP S.card (nB U) + j - 1 = tPP S.card (nB U) + (j - 1) := by omega
      constructor
      · rintro ⟨w, hw, hx⟩
        rw [hget_sched, ite_eq_left (by omega), hidx, gM_pp (by omega)] at hx
        obtain ⟨h2, h3⟩ := gPP_down_ne hS hw hx
        exact ⟨w, mem_kidsOf.2 ⟨(kpar_spec h2).1, h2⟩, h3⟩
      · rintro ⟨c, hc, hx⟩
        have hcu := (mem_kidsOf.1 hc).2
        refine ⟨c, fun h => kpar_not_both hS h.symm hcu, ?_⟩
        rw [hget_sched, ite_eq_left (by omega), hidx, gM_pp (by omega)]
        unfold gPP
        rw [ite_eq_left hcu, (argminIdx_up hS).2 hx]
        rfl

lemma downSet_zero (u : U) : downSet S N u 0 = ∅ := by
  have hn : 0 < S.card := card_pos.2 hS
  refine eq_empty_of_forall_notMem (fun x hx => ?_)
  unfold downSet at hx
  rw [mem_filter] at hx
  omega

lemma downL_eq {u : U} (hu : u ∈ S) {j : ℕ} (hj : j < 3 * S.card) :
    downL S.card (nB U) u (schedHist (gM S N) u (tPP S.card (nB U) + j)) j =
      argminIdx (downSet S N u j) := by
  classical
  have hs1 : tSZ S.card (nB U) ≤ tPP S.card (nB U) + j := by unfold tPP tPRE; omega
  unfold downL
  rw [parTL_eq hS hu hs1]
  cases hp : kpar S N u with
  | none =>
    dsimp only
    rw [upL_eq hS hu hj]
    obtain ⟨ℓ, hℓS, hℓ⟩ := srcB_last (U := U) hS
    have huℓ : u ∈ srcB S (nB U) := (kpar_none hS hu).1 hp
    have hd : kdep S N u = 0 :=
      (dA_zero (srcB_sub _) (srcB_last_nonempty hS) hu).2 huℓ
    rw [hℓ, mem_singleton] at huℓ
    subst huℓ
    congr 1
    unfold upSet downSet
    rw [desc_root hS hℓ, hd]
    ext x; simp
  | some p =>
    dsimp only
    by_cases h0 : j = 0
    · subst h0
      rw [ite_eq_left rfl, downSet_zero hS]
      exact (argminIdx_eq_none.2 rfl).symm
    · rw [ite_eq_right h0]
      have hidx : tPP S.card (nB U) + j - 1 = tPP S.card (nB U) + (j - 1) := by omega
      rw [hget_sched, ite_eq_left (by omega), hidx, gM_pp (by omega)]
      unfold gPP
      rw [ite_eq_right (fun h => kpar_not_both hS hp h), ite_eq_left hp, idOf_map]
      congr 1
      have hd := (kpar_spec hp).2.2.2
      unfold downSet
      ext x; simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- **Window PP follows the schedule.** -/
lemma ppSend_eq {u : U} (hu : u ∈ S) {j : ℕ} (hj : j < 3 * S.card) (v : U) :
    ppSend S.card (nB U) ((ktInst S N).ctx u) (schedHist (gM S N) u (tPP S.card (nB U) + j)) j v =
      gPP S N j u v := by
  classical
  have hs1 : tSZ S.card (nB U) ≤ tPP S.card (nB U) + j := by unfold tPP tPRE; omega
  unfold ppSend gPP
  have hme : ((ktInst S N).ctx u).me = u := rfl
  rw [hme, parTL_eq hS hu hs1, kidsL_eq hS hs1, upL_eq hS hu hj, downL_eq hS hu hj]
  by_cases h1 : kpar S N u = some v
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    have hc : v ∈ kidsOf S (kpar S N) u ↔ kpar S N v = some u := by
      rw [mem_kidsOf]; exact ⟨fun h => h.2, fun h => ⟨(kpar_spec h).1, h⟩⟩
    by_cases h2 : kpar S N v = some u
    · rw [ite_eq_left (hc.2 h2), ite_eq_left h2]
    · rw [ite_eq_right (fun h => h2 (hc.1 h)), ite_eq_right h2]

/-! ## The output -/

/-- **Every node learns `S`.** -/
lemma outSet_eq {u : U} (hu : u ∈ S) :
    outSet S.card (nB U) u (schedHist (gM S N) u (tFin S.card (nB U))) = S := by
  classical
  have hn : 0 < S.card := card_pos.2 hS
  obtain ⟨ℓ, hℓS, hℓ⟩ := srcB_last (U := U) hS
  unfold outSet
  ext x
  rw [mem_insert, mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨j, hj, w, hx⟩)
    · exact hu
    · rw [hget_sched, ite_eq_left (by unfold tFin; omega), gM_pp hj] at hx
      unfold gPP at hx
      split_ifs at hx with h1 h2
      · cases ha : argminIdx (upSet S N w j) with
        | none => rw [ha] at hx; cases hx
        | some y =>
          rw [ha] at hx
          simp only [Option.map_some, Option.some.injEq, Word.id.injEq] at hx
          subst hx
          have := argminIdx_mem ha
          unfold upSet at this
          rw [mem_filter, mem_desc] at this
          exact this.1.1
      · cases ha : argminIdx (downSet S N w j) with
        | none => rw [ha] at hx; cases hx
        | some y =>
          rw [ha] at hx
          simp only [Option.map_some, Option.some.injEq, Word.id.injEq] at hx
          subst hx
          have := argminIdx_mem ha
          unfold downSet at this
          rw [mem_filter] at this
          exact this.1
  · intro hx
    by_cases hxu : x = u
    · exact Or.inl hxu
    right
    have hpx := kpre_lt (N := N) hS hℓ hx
    cases hp : kpar S N u with
    | some p =>
      have hpS := (kpar_spec hp).2.1
      have hdp := kdep_lt (N := N) hS hpS
      refine ⟨kpre S N x + S.card + kdep S N p, by omega, p, ?_⟩
      rw [hget_sched, ite_eq_left (by unfold tFin; omega), gM_pp (by omega)]
      unfold gPP
      rw [ite_eq_right (fun h => kpar_not_both hS hp h), ite_eq_left hp,
        (argminIdx_down hS).2 (by unfold downSet; rw [mem_filter]; exact ⟨hx, rfl⟩)]
      rfl
    | none =>
      have huℓ : u ∈ srcB S (nB U) := (kpar_none hS hu).1 hp
      rw [hℓ, mem_singleton] at huℓ
      subst huℓ
      have hxd : x ∈ desc S (kpar S N) u := by rw [desc_root hS hℓ]; exact hx
      rw [desc_eq kpar_mem kpar_rk hu, mem_insert, mem_biUnion] at hxd
      rcases hxd with h | ⟨c, hc, hxc⟩
      · exact absurd h hxu
      have hcu := (mem_kidsOf.1 hc).2
      have hdc := kdep_lt (N := N) hS (mem_kidsOf.1 hc).1
      refine ⟨kpre S N x + S.card - kdep S N c, by omega, c, ?_⟩
      rw [hget_sched, ite_eq_left (by unfold tFin; omega), gM_pp (by omega)]
      unfold gPP
      rw [ite_eq_left hcu, (argminIdx_up hS).2 (by
        unfold upSet; rw [mem_filter]; exact ⟨hxc, by omega⟩)]
      rfl

end Sched

end KT

end APSP.Stoc.Congest
