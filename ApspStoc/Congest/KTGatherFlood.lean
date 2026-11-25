import ApspStoc.Congest.KTGatherDefs

/-!
# The gather phase: the flooding windows

For a node `u ∈ S` fed with the history of the schedule `gM` (`KTGatherDefs.lean`), the local
computations of the flooding windows `0, …, B` agree with the global objects:

* `firstR_flood`: a node outside the sources of window `b` first hears the token in round
  `dA u - 1` of the window (if there is a source);
* `loL_eq`: the local search interval is the global one (`gLo`);
* `floodSend_eq`: the node sends what the schedule says;
* after window `B` (`depL_eq`, `parTL_eq`, `kidsL_eq`): the node knows its depth, parent and
  children in the BFS tree from the leader.
-/

namespace APSP.Stoc.Congest

namespace KT

open APSP Finset

set_option linter.unusedSectionVars false

variable {U : Type} [Fintype U] [DecidableEq U]

/-! ## Histories of schedules -/

lemma hget_sched (M : U → U → ℕ → Option (Word U)) (u : U) (s i : ℕ) (w : U) :
    hget (schedHist M u s) i w = if i < s then M w u i else none := by
  split_ifs with h
  · exact hget_schedHist M u h w
  · unfold hget
    rw [List.getD_eq_default _ _ (by rw [length_schedHist]; omega)]

lemma sendersH_sched (M : U → U → ℕ → Option (Word U)) (u : U) (s i : ℕ) :
    sendersH (schedHist M u s) i = if i < s then univ.filter (fun w => (M w u i).isSome) else ∅ := by
  unfold sendersH
  split_ifs with h
  · simp only [hget_sched, h, ite_true]
  · ext w; simp [hget_sched, h]

section Sched

variable {S : Finset U} {N : WNet S}

/-! ## Windows of the schedule -/

lemma gM_flood (hS : S.Nonempty) {b j : ℕ} (hb : b ≤ nB U) (hj : j < S.card) (w u : U) :
    gM S N w u (b * S.card + j) = gFlood S N b j w u := by
  have hn : 0 < S.card := card_pos.2 hS
  have h1 : b * S.card + j < tSZ S.card (nB U) := by
    unfold tSZ
    have : b * S.card ≤ nB U * S.card := Nat.mul_le_mul_right _ hb
    rw [Nat.add_mul, one_mul]; omega
  have h2 : (b * S.card + j) / S.card = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, zero_add]
  have h3 : (b * S.card + j) % S.card = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  unfold gM
  rw [ite_eq_left h1, h2, h3]

lemma gM_sz {j : ℕ} (hj : j < S.card) (w u : U) :
    gM S N w u (tSZ S.card (nB U) + j) = gSZ S N j w u := by
  unfold gM
  rw [ite_eq_right (by omega), ite_eq_left (by unfold tPRE; omega), Nat.add_sub_cancel_left]

lemma gM_pre {j : ℕ} (hj : j < S.card) (w u : U) :
    gM S N w u (tPRE S.card (nB U) + j) = gPRE S N j w u := by
  unfold gM
  rw [ite_eq_right (by unfold tPRE; omega), ite_eq_right (by omega),
    ite_eq_left (by unfold tPP; omega), Nat.add_sub_cancel_left]

lemma gM_pp {j : ℕ} (hj : j < 3 * S.card) (w u : U) :
    gM S N w u (tPP S.card (nB U) + j) = gPP S N j w u := by
  unfold gM
  rw [ite_eq_right (by unfold tPP tPRE; omega), ite_eq_right (by unfold tPP; omega),
    ite_eq_right (by omega), ite_eq_left (by unfold tFin; omega), Nat.add_sub_cancel_left]

/-! ## The flooding windows -/

lemma gFlood_isSome {b j : ℕ} {w u : U} : (gFlood S N b j w u).isSome ↔
    (srcB S b).Nonempty ∧ (ktInst S N).G.Adj w u ∧ dA S N (srcB S b) w = j := by
  classical
  unfold gFlood
  split_ifs with h <;> simp [h]

variable (hS : S.Nonempty)
include hS

lemma senders_flood {b j : ℕ} (hb : b ≤ nB U) (hj : j < S.card) (u : U) (s : ℕ) :
    (sendersH (schedHist (gM S N) u s) (b * S.card + j)).Nonempty ↔
      b * S.card + j < s ∧ (srcB S b).Nonempty ∧
        ∃ w, (ktInst S N).G.Adj w u ∧ dA S N (srcB S b) w = j := by
  rw [sendersH_sched]
  split_ifs with h
  · simp only [gM_flood hS hb hj, gFlood_isSome, filter_nonempty_iff, mem_univ, true_and, h]
    constructor
    · rintro ⟨w, h1, h2, h3⟩; exact ⟨h1, w, h2, h3⟩
    · rintro ⟨h1, w, h2, h3⟩; exact ⟨w, h1, h2, h3⟩
  · simp [h]

/-- **First receipt**: a node that is not a source of window `b` first hears the token in round
`dA u - 1` of the window. -/
lemma firstR_flood {b : ℕ} (hb : b ≤ nB U) {u : U} (hu : u ∈ S) (huA : u ∉ srcB S b) (s : ℕ) :
    firstR (schedHist (gM S N) u s) (b * S.card) S.card =
      if (srcB S b).Nonempty ∧ b * S.card + dA S N (srcB S b) u - 1 < s then
        some (dA S N (srcB S b) u - 1) else none := by
  classical
  unfold firstR
  by_cases hne : (srcB S b).Nonempty
  · have hpos : dA S N (srcB S b) u ≠ 0 := fun h => huA ((dA_zero (srcB_sub b) hne hu).1 h)
    have hlt := dA_lt (N := N) hne (srcB_sub b) hu
    obtain ⟨v, hv, hdv⟩ := dA_closer (N := N) (srcB_sub b) hne hu huA
    -- the senders of a round
    have hlow : ∀ j, (∃ w, (ktInst S N).G.Adj w u ∧ dA S N (srcB S b) w = j) →
        dA S N (srcB S b) u - 1 ≤ j := by
      rintro j ⟨w, hw, rfl⟩
      have := dA_adj (N := N) hne hw.symm
      omega
    by_cases hs : b * S.card + dA S N (srcB S b) u - 1 < s
    · have hP : dA S N (srcB S b) u - 1 < S.card ∧
          (sendersH (schedHist (gM S N) u s) (b * S.card + (dA S N (srcB S b) u - 1))).Nonempty :=
        ⟨by omega, (senders_flood hS hb (by omega) u s).2 ⟨by omega, hne, v, hv, by omega⟩⟩
      have hex : ∃ j, j < S.card ∧ (sendersH (schedHist (gM S N) u s) (b * S.card + j)).Nonempty :=
        ⟨_, hP⟩
      rw [dite_eq_left hex, ite_eq_left ⟨hne, hs⟩]
      congr 1
      rw [Nat.find_eq_iff]
      refine ⟨hP, fun j hj ⟨hj', hsn⟩ => ?_⟩
      obtain ⟨-, -, hw⟩ := (senders_flood hS hb hj' u s).1 hsn
      have := hlow j hw
      omega
    · rw [ite_eq_right (fun h => hs h.2), dite_eq_right]
      rintro ⟨j, hj, hsn⟩
      obtain ⟨h1, -, hw⟩ := (senders_flood hS hb hj u s).1 hsn
      have := hlow j hw
      omega
  · rw [ite_eq_right (fun h => hne h.1), dite_eq_right]
    rintro ⟨j, hj, hsn⟩
    exact hne ((senders_flood hS hb hj u s).1 hsn).2.1

lemma src_iff {b : ℕ} {u : U} (hu : u ∈ S) :
    idx u < gLo S b + 2 ^ (nB U - b - 1) ↔ u ∈ srcB S b := by
  rw [mem_srcB]; exact ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩

/-- **The search interval** is known locally. -/
lemma loL_eq {u : U} (hu : u ∈ S) {s : ℕ} :
    ∀ b ≤ nB U, b * S.card ≤ s → loL S.card (nB U) u (schedHist (gM S N) u s) b = gLo S b := by
  intro b
  induction b with
  | zero => intros; rfl
  | succ b ih =>
    intro hb hs
    have hn : 0 < S.card := card_pos.2 hS
    have ih' := ih (by omega) (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ b)) hs)
    have hflag : (idx u < loL S.card (nB U) u (schedHist (gM S N) u s) b + 2 ^ (nB U - b - 1) ∨
        (firstR (schedHist (gM S N) u s) (b * S.card) S.card).isSome) ↔
        mstar S < gLo S b + 2 ^ (nB U - b - 1) := by
      rw [ih', ← srcB_nonempty_iff hS, src_iff hS hu]
      by_cases huA : u ∈ srcB S b
      · exact ⟨fun _ => ⟨u, huA⟩, fun _ => Or.inl huA⟩
      · rw [firstR_flood hS (by omega) hu huA]
        have hlt : ∀ hne : (srcB S b).Nonempty, b * S.card + dA S N (srcB S b) u - 1 < s :=
          fun hne => by
            have := dA_lt (N := N) hne (srcB_sub b) hu
            rw [Nat.succ_mul] at hs
            omega
        constructor
        · rintro (h | h)
          · exact absurd h huA
          · by_contra hne
            rw [ite_eq_right (fun h => hne h.1)] at h
            simp at h
        · intro hne
          right
          rw [ite_eq_left ⟨hne, hlt hne⟩]
          rfl
    show (if _ then _ else _) = (if _ then _ else _)
    by_cases h : mstar S < gLo S b + 2 ^ (nB U - b - 1)
    · rw [ite_eq_left (hflag.2 h), ite_eq_left h, ih']
    · rw [ite_eq_right (fun h' => h (hflag.1 h')), ite_eq_right h, ih']

lemma actL_eq {b : ℕ} (hb : b ≤ nB U) {u : U} (hu : u ∈ S) {s : ℕ} (hs : b * S.card ≤ s) :
    actL S.card (nB U) u (schedHist (gM S N) u s) b =
      if u ∈ srcB S b then some 0
      else if (srcB S b).Nonempty ∧ b * S.card + dA S N (srcB S b) u - 1 < s then
        some (dA S N (srcB S b) u) else none := by
  unfold actL
  have hc : idx u < loL S.card (nB U) u (schedHist (gM S N) u s) b + 2 ^ (nB U - b - 1) ↔
      u ∈ srcB S b := by rw [loL_eq hS hu b hb hs, src_iff hS hu]
  by_cases huA : u ∈ srcB S b
  · rw [ite_eq_left (hc.2 huA), ite_eq_left huA]
  · rw [ite_eq_right (fun h => huA (hc.1 h)), ite_eq_right huA, firstR_flood hS hb hu huA]
    split_ifs with h
    · have : dA S N (srcB S b) u ≠ 0 := fun h0 => huA ((dA_zero (srcB_sub b) h.1 hu).1 h0)
      simp only [Option.map_some]
      congr 1; omega
    · rfl

lemma actL_some_iff {b j : ℕ} (hb : b ≤ nB U) (_hj : j < S.card) {u : U} (hu : u ∈ S) :
    actL S.card (nB U) u (schedHist (gM S N) u (b * S.card + j)) b = some j ↔
      (srcB S b).Nonempty ∧ dA S N (srcB S b) u = j := by
  rw [actL_eq hS hb hu (by omega)]
  by_cases huA : u ∈ srcB S b
  · rw [ite_eq_left huA, (dA_zero (srcB_sub b) ⟨u, huA⟩ hu).2 huA]
    simp only [Option.some.injEq]
    exact ⟨fun h => ⟨⟨u, huA⟩, h⟩, fun h => h.2⟩
  · rw [ite_eq_right huA]
    split_ifs with h
    · simp only [Option.some.injEq]
      constructor
      · intro h'; exact ⟨h.1, h'⟩
      · intro h'; exact h'.2
    · simp only [false_iff, not_and]
      intro hne hd
      have : dA S N (srcB S b) u ≠ 0 := fun h0 => huA ((dA_zero (srcB_sub b) hne hu).1 h0)
      exact h ⟨hne, by omega⟩

lemma parL_eq {b : ℕ} (hb : b ≤ nB U) {u : U} (hu : u ∈ S) (hne : (srcB S b).Nonempty) {s : ℕ}
    (hs : b * S.card + dA S N (srcB S b) u ≤ s) :
    parL S.card (nB U) u (schedHist (gM S N) u s) b = parA S N (srcB S b) u := by
  classical
  unfold parL
  have hc : idx u < loL S.card (nB U) u (schedHist (gM S N) u s) b + 2 ^ (nB U - b - 1) ↔
      u ∈ srcB S b := by rw [loL_eq hS hu b hb (by omega), src_iff hS hu]
  by_cases huA : u ∈ srcB S b
  · rw [ite_eq_left (hc.2 huA), ((parA_eq_none (srcB_sub b) hne hu).2 huA)]
  · rw [ite_eq_right (fun h => huA (hc.1 h)), firstR_flood hS hb hu huA]
    have hpos : dA S N (srcB S b) u ≠ 0 := fun h0 => huA ((dA_zero (srcB_sub b) hne hu).1 h0)
    rw [ite_eq_left ⟨hne, by omega⟩, Option.bind_some, parA_eq hu huA]
    congr 1
    have hlt := dA_lt (N := N) hne (srcB_sub b) hu
    ext w
    rw [sendersH_sched, ite_eq_left (by omega)]
    simp only [mem_filter, mem_univ, true_and, gM_flood hS hb (show dA S N (srcB S b) u - 1 < S.card
      by omega), gFlood_isSome]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨hne, h1, by omega⟩

omit hS in
lemma kv_ctx (u : U) : kv ((ktInst S N).ctx u) = ktView S N u := by
  simp [kv, ktInst_ctx]

/-- **The flooding windows follow the schedule.** -/
lemma floodSend_eq {b j : ℕ} (hb : b ≤ nB U) (hj : j < S.card) {u : U} (hu : u ∈ S) (v : U) :
    floodSend S.card (nB U) ((ktInst S N).ctx u) (schedHist (gM S N) u (b * S.card + j)) b j v =
      gFlood S N b j u v := by
  classical
  unfold floodSend gFlood
  have hme : ((ktInst S N).ctx u).me = u := rfl
  rw [hme, kv_ctx]
  have hc : (actL S.card (nB U) u (schedHist (gM S N) u (b * S.card + j)) b = some j ∧
      ktView S N u s(u, v) ≠ 0) ↔
      (srcB S b).Nonempty ∧ dA S N (srcB S b) u = j ∧ (ktInst S N).G.Adj u v := by
    rw [actL_some_iff hS hb hj hu, ktView_ne_zero_iff]; tauto
  by_cases h : (srcB S b).Nonempty ∧ dA S N (srcB S b) u = j ∧ (ktInst S N).G.Adj u v
  · rw [ite_eq_left (hc.2 h), ite_eq_left (show (srcB S b).Nonempty ∧ (ktInst S N).G.Adj u v ∧
      dA S N (srcB S b) u = j from ⟨h.1, h.2.2, h.2.1⟩),
      parL_eq (N := N) (s := b * S.card + j) hS hb hu h.1 (by omega)]
  · rw [ite_eq_right (fun h' => h (hc.1 h')),
      ite_eq_right (fun h' => h ⟨h'.1, h'.2.2, h'.2.1⟩)]

/-! ## The BFS tree from the leader -/

lemma actL_last {u : U} (hu : u ∈ S) {s : ℕ} (hs : tSZ S.card (nB U) ≤ s) :
    actL S.card (nB U) u (schedHist (gM S N) u s) (nB U) = some (kdep S N u) := by
  have hne := srcB_last_nonempty (U := U) hS
  have hlt := dA_lt (N := N) hne (srcB_sub _) hu
  unfold tSZ at hs
  rw [Nat.add_mul, one_mul] at hs
  rw [actL_eq hS le_rfl hu (by omega)]
  unfold kdep
  by_cases huA : u ∈ srcB S (nB U)
  · rw [ite_eq_left huA, (dA_zero (srcB_sub _) hne hu).2 huA]
  · rw [ite_eq_right huA, ite_eq_left ⟨hne, by omega⟩]

lemma depL_eq {u : U} (hu : u ∈ S) {s : ℕ} (hs : tSZ S.card (nB U) ≤ s) :
    depL S.card (nB U) u (schedHist (gM S N) u s) = kdep S N u := by
  unfold depL; rw [actL_last hS hu hs]; rfl

lemma parTL_eq {u : U} (hu : u ∈ S) {s : ℕ} (hs : tSZ S.card (nB U) ≤ s) :
    parTL S.card (nB U) u (schedHist (gM S N) u s) = kpar S N u := by
  have hne := srcB_last_nonempty (U := U) hS
  have hlt := dA_lt (N := N) hne (srcB_sub _) hu
  unfold tSZ at hs
  rw [Nat.add_mul, one_mul] at hs
  exact parL_eq hS le_rfl hu hne (by omega)

lemma kidsL_eq {u : U} {s : ℕ} (hs : tSZ S.card (nB U) ≤ s) :
    kidsL S.card (nB U) (schedHist (gM S N) u s) = kidsOf S (kpar S N) u := by
  classical
  have hne := srcB_last_nonempty (U := U) hS
  unfold tSZ at hs
  rw [Nat.add_mul, one_mul] at hs
  ext w
  unfold kidsL
  simp only [mem_filter, mem_univ, true_and, mem_kidsOf]
  constructor
  · rintro ⟨j, hj, hw⟩
    rw [hget_sched, ite_eq_left (by omega), gM_flood hS le_rfl hj] at hw
    unfold gFlood at hw
    split_ifs at hw with h1 h2
    · exact ⟨(kpar_spec h2).1, h2⟩
    · simp at hw
  · rintro ⟨hwS, hw⟩
    have hlt := dA_lt (N := N) hne (srcB_sub _) hwS
    refine ⟨dA S N (srcB S (nB U)) w, hlt, ?_⟩
    rw [hget_sched, ite_eq_left (by omega), gM_flood hS le_rfl hlt]
    unfold gFlood
    rw [ite_eq_left ⟨hne, kpar_adj hw, rfl⟩]
    rw [ite_eq_left (show parA S N (srcB S (nB U)) w = some u from hw)]

end Sched

end KT

end APSP.Stoc.Congest
