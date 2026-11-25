import ApspStoc.Congest.KTGatherTree

/-!
# The gather phase: success

`gather_implI`: on the KT1 instance `ktInst S N`, the protocol `gatherP |S| U` (`KTGatherDefs.lean`)
halts at all nodes of `S` in round `tFin = (nB U + 6)·|S|`, deterministically (failure
probability `0`), with every node of `S` outputting `S`. It sends only along edges of the
network, at most `(nB U + 11)·|S|²` messages: at most one per directed edge in each of the
`nB U + 1` flooding windows, and at most `2|S|` per round (over tree edges) in the `5|S|` rounds of
the windows SZ, PRE and PP.

The proof applies `succ_histP` to the schedule `gM`: the local computations fed with the history
of `gM` send what `gM` says (`KTGatherFlood.lean`, `KTGatherTree.lean`), `gM` uses only edges and
valid words, and its outputs are `S` (`outSet_eq`).
-/

namespace APSP.Stoc.Congest

namespace KT

open APSP Finset

set_option linter.unusedSectionVars false

variable {U : Type} [Fintype U] [DecidableEq U]

lemma sum_range_mul_split (f : ℕ → ℕ) (n : ℕ) :
    ∀ k, ∑ s ∈ range (k * n), f s = ∑ b ∈ range k, ∑ j ∈ range n, f (b * n + j)
  | 0 => by simp
  | k + 1 => by rw [Nat.succ_mul, sum_range_add, sum_range_mul_split f n k, sum_range_succ]

section Sched

variable {S : Finset U} {N : WNet S} (hS : S.Nonempty)
include hS

omit hS in
lemma ksz_le (u : U) : ksz S N u ≤ S.card := by
  unfold ksz
  exact card_le_card (fun w hw => (mem_desc.1 hw).1)

/-- the schedule uses only edges of the network -/
lemma gM_adj {w u : U} {s : ℕ} (h : (gM S N w u s).isSome) : (ktInst S N).G.Adj w u := by
  classical
  unfold gM at h
  split_ifs at h
  · exact (gFlood_isSome.1 h).2.1
  · unfold gSZ at h
    split_ifs at h with h1
    · exact kpar_adj h1.1
    · simp at h
  · unfold gPRE at h
    split_ifs at h with h1
    · exact (kpar_adj h1.1).symm
    · simp at h
  · unfold gPP at h
    split_ifs at h with h1 h2
    · exact kpar_adj h1
    · exact (kpar_adj h2).symm
    · simp at h
  · simp at h

/-- after the flooding windows, the schedule uses only tree edges -/
lemma gM_tree {w u : U} {s : ℕ} (hs : tSZ S.card (nB U) ≤ s) (h : (gM S N w u s).isSome) :
    (w ∈ S ∧ kpar S N w = some u) ∨ (u ∈ S ∧ kpar S N u = some w) := by
  classical
  unfold gM at h
  rw [ite_eq_right (by omega)] at h
  split_ifs at h
  · unfold gSZ at h
    split_ifs at h with h1
    · exact Or.inl ⟨(kpar_spec h1.1).1, h1.1⟩
    · simp at h
  · unfold gPRE at h
    split_ifs at h with h1
    · exact Or.inr ⟨(kpar_spec h1.1).1, h1.1⟩
    · simp at h
  · unfold gPP at h
    split_ifs at h with h1 h2
    · exact Or.inl ⟨(kpar_spec h1).1, h1⟩
    · exact Or.inr ⟨(kpar_spec h2).1, h2⟩
    · simp at h
  · simp at h

/-- the schedule uses only valid words -/
lemma gM_wordOK {w u : U} {s : ℕ} {x : Word U} (h : gM S N w u s = some x) :
    WordOK (Fintype.card U) x := by
  classical
  have hcard : S.card ≤ Fintype.card U := card_le_univ S
  obtain ⟨ℓ, -, hℓ⟩ := srcB_last (U := U) hS
  unfold gM at h
  split_ifs at h
  · unfold gFlood at h
    split_ifs at h with h1 h2
    · cases h; show 1 ≤ _ + 3; omega
    · cases h; show 0 ≤ _ + 3; omega
  · unfold gSZ at h
    split_ifs at h with h1
    cases h
    have := ksz_le (N := N) w
    show ksz S N w ≤ _ + 3; omega
  · unfold gPRE at h
    split_ifs at h with h1
    cases h
    have := kpre_lt (N := N) hS hℓ (kpar_spec h1.1).1
    show kpre S N u ≤ _ + 3; omega
  · unfold gPP at h
    split_ifs at h with h1 h2
    · cases ha : argminIdx (upSet S N w (s - tPP S.card (nB U))) with
      | none => rw [ha] at h; cases h
      | some y => rw [ha] at h; cases h; trivial
    · cases ha : argminIdx (downSet S N w (s - tPP S.card (nB U))) with
      | none => rw [ha] at h; cases h
      | some y => rw [ha] at h; cases h; trivial

lemma msgs_flood {b : ℕ} (hb : b ≤ nB U) :
    ∑ j ∈ range S.card, (univ.filter (fun uv : U × U =>
      (gM S N uv.1 uv.2 (b * S.card + j)).isSome)).card ≤ S.card ^ 2 := by
  classical
  have h1 : ∀ j ∈ range S.card, (univ.filter (fun uv : U × U =>
      (gM S N uv.1 uv.2 (b * S.card + j)).isSome)).card =
      (univ.filter (fun uv : U × U => (gFlood S N b j uv.1 uv.2).isSome)).card := by
    intro j hj
    congr 1
    ext uv
    simp only [mem_filter, mem_univ, true_and, gM_flood hS hb (mem_range.1 hj)]
  rw [sum_congr rfl h1, sum_card_filter_swap]
  calc ∑ uv : U × U, ((range S.card).filter (fun j => (gFlood S N b j uv.1 uv.2).isSome)).card
      ≤ ∑ uv : U × U, (if uv.1 ∈ S ∧ uv.2 ∈ S then 1 else 0) := by
        refine sum_le_sum (fun uv _ => ?_)
        split_ifs with hS'
        · refine card_le_one.2 (fun a ha a' ha' => ?_)
          simp only [mem_filter, gFlood_isSome] at ha ha'
          rw [← ha.2.2.2, ← ha'.2.2.2]
        · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
          intro j _ hj
          have := (gFlood_isSome.1 hj).2.1
          exact hS' ⟨ktInst_mem_left this, ktInst_mem_right this⟩
    _ = S.card ^ 2 := by
        rw [sum_boole]
        have : (univ.filter (fun uv : U × U => uv.1 ∈ S ∧ uv.2 ∈ S)) = S ×ˢ S := by
          ext uv; simp [mem_product]
        rw [this, card_product, sq]
        rfl

lemma msgs_tree {s : ℕ} (hs : tSZ S.card (nB U) ≤ s) :
    (univ.filter (fun uv : U × U => (gM S N uv.1 uv.2 s).isSome)).card ≤ 2 * S.card := by
  classical
  refine le_trans (card_le_card (fun uv huv => ?_)) (card_treePairs S (kpar S N))
  simp only [mem_filter, mem_univ, true_and] at huv ⊢
  exact gM_tree hS hs huv

/-- **Messages of the gather phase.** -/
lemma msgs_gM : ∑ s ∈ range (tFin S.card (nB U)),
    (univ.filter (fun uv : U × U => (gM S N uv.1 uv.2 s).isSome)).card ≤
      (nB U + 11) * S.card ^ 2 := by
  classical
  have ht : tFin S.card (nB U) = (nB U + 1) * S.card + 5 * S.card := by
    unfold tFin tPP tPRE tSZ; ring
  rw [ht, sum_range_add, sum_range_mul_split]
  have h1 : ∑ b ∈ range (nB U + 1), ∑ j ∈ range S.card, (univ.filter (fun uv : U × U =>
      (gM S N uv.1 uv.2 (b * S.card + j)).isSome)).card ≤ (nB U + 1) * S.card ^ 2 := by
    calc _ ≤ ∑ _b ∈ range (nB U + 1), S.card ^ 2 :=
          sum_le_sum (fun b hb => msgs_flood hS (by have := mem_range.1 hb; omega))
      _ = _ := by rw [sum_const, card_range, smul_eq_mul]
  have h2 : ∑ j ∈ range (5 * S.card), (univ.filter (fun uv : U × U =>
      (gM S N uv.1 uv.2 ((nB U + 1) * S.card + j)).isSome)).card ≤ 5 * S.card * (2 * S.card) := by
    calc _ ≤ ∑ _j ∈ range (5 * S.card), 2 * S.card :=
          sum_le_sum (fun j _ => msgs_tree hS (by unfold tSZ; omega))
      _ = _ := by rw [sum_const, card_range, smul_eq_mul]
  calc _ ≤ (nB U + 1) * S.card ^ 2 + 5 * S.card * (2 * S.card) := Nat.add_le_add h1 h2
    _ = (nB U + 11) * S.card ^ 2 := by ring

/-- **The gather phase**: deterministically, all nodes of `S` halt in round `(nB U + 6)·|S|` and
output `S`, after at most `(nB U + 11)·|S|²` messages. -/
theorem gather_implI :
    ImplI (gatherP S.card U) (ktInst S N) (inOf (fun _ => ()))
      (postOf (ktInst S N) (fun z : Agent U → Finset U => ∀ v ∈ S, z (.inl v) = S))
      (Prof.mk (tFin S.card (nB U)) (fun _ => (nB U + 11) * S.card ^ 2)
        ((nB U + 11) * S.card ^ 2)) 0 := by
  classical
  have hn : 0 < S.card := card_pos.2 hS
  refine ImplI.of_forall _ _ le_rfl (fun ω => ?_)
  have hM : ∀ s < tFin S.card (nB U), ∀ u v,
      ((ktInst S N).part u → gSend S.card (nB U) ((ktInst S N).ctx u)
        (schedHist (gM S N) u s) v = gM S N u v s) ∧
      (¬ (ktInst S N).G.Adj u v → gM S N u v s = none) ∧
      ∀ w, gM S N u v s = some w → WordOK (Fintype.card U) w := by
    intro s hs u v
    refine ⟨fun hu => ?_, fun hadj => ?_, fun w hw => gM_wordOK hS hw⟩
    · have hu : u ∈ S := hu
      unfold gSend
      rw [length_schedHist]
      by_cases h1 : s < tSZ S.card (nB U)
      · rw [ite_eq_left h1]
        obtain ⟨b, j, hj, rfl⟩ : ∃ b j, j < S.card ∧ s = b * S.card + j :=
          ⟨s / S.card, s % S.card, Nat.mod_lt _ hn, by rw [mul_comm]; exact (Nat.div_add_mod s S.card).symm⟩
        have hb : b ≤ nB U := by
          unfold tSZ at h1
          by_contra hb
          have : (nB U + 1) * S.card ≤ b * S.card := Nat.mul_le_mul_right _ (by omega)
          omega
        have h2 : (b * S.card + j) / S.card = b := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, zero_add]
        have h3 : (b * S.card + j) % S.card = j := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
        rw [h2, h3, floodSend_eq hS hb hj hu, gM_flood hS hb hj]
      · rw [ite_eq_right h1]
        obtain ⟨j, rfl⟩ : ∃ j, s = tSZ S.card (nB U) + j := ⟨s - tSZ S.card (nB U), by omega⟩
        by_cases h2 : tSZ S.card (nB U) + j < tPRE S.card (nB U)
        · have hj : j < S.card := by unfold tPRE at h2; omega
          rw [ite_eq_left h2, Nat.add_sub_cancel_left, szSend_eq hS hu hj, gM_sz hj]
        · rw [ite_eq_right h2]
          obtain ⟨j', hj'⟩ : ∃ j', tSZ S.card (nB U) + j = tPRE S.card (nB U) + j' :=
            ⟨tSZ S.card (nB U) + j - tPRE S.card (nB U), by omega⟩
          rw [hj'] at hs ⊢
          by_cases h3 : tPRE S.card (nB U) + j' < tPP S.card (nB U)
          · have hj : j' < S.card := by unfold tPP at h3; omega
            rw [ite_eq_left h3, Nat.add_sub_cancel_left, preSend_eq hS hu hj, gM_pre hj]
          · rw [ite_eq_right h3]
            obtain ⟨j'', hj''⟩ : ∃ j'', tPRE S.card (nB U) + j' = tPP S.card (nB U) + j'' :=
              ⟨tPRE S.card (nB U) + j' - tPP S.card (nB U), by omega⟩
            rw [hj''] at hs ⊢
            have hj : j'' < 3 * S.card := by unfold tFin at hs; omega
            rw [ite_eq_left hs, Nat.add_sub_cancel_left, ppSend_eq hS hu hj, gM_pp hj]
    · cases hm : gM S N u v s with
      | none => rfl
      | some w => exact absurd (gM_adj hS (by rw [hm]; rfl)) hadj
  refine succ_histP (F := fun c _ h v => gSend S.card (nB U) c h v)
    (Tf := fun _ => tFin S.card (nB U))
    (O := fun c _ h g => if g = .inl c.me then
      some ⟨Finset U, outSet S.card (nB U) c.me h⟩ else none)
    (I := ktInst S N) (x := inOf (fun _ => ())) (fun _ => rfl) (gM S N) hM le_rfl ?_ ?_
    (fun _ => ⟨Finset U, S⟩) ?_ ⟨fun _ => S, fun _ _ => rfl, fun _ _ => rfl⟩
  · exact msgs_gM hS
  · intro e
    refine le_trans (sum_le_sum (fun s _ => card_filter_le _ _)) (msgs_gM hS)
  · intro g v hg
    obtain ⟨rfl, hv⟩ := ktInst_host_eq.1 hg
    show (if (Sum.inl v : Agent U) = .inl v then some (⟨Finset U, outSet S.card (nB U) v
      (schedHist (gM S N) v (tFin S.card (nB U)))⟩ : Mem) else none) = _
    rw [ite_eq_left rfl, outSet_eq hS hv]

end Sched

end KT

end APSP.Stoc.Congest
