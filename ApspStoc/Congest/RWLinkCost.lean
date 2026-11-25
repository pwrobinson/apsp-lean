import ApspStoc.Congest.RWLinkWalk

/-!
# The random-walk construction: properties of the global schedule

* `schedG_adj`: packets are sent only along edges of `C` (in both directions of a crossing);
* `schedG_encOK`: unless the walks overflow, every packet has `5` words and numbers
  `≤ R + 2ℓ` (indices `< R`, path positions `≤ 2ℓ`);
* `sum_schedG_le`: unless the walks overflow, at most `|P|·R·(4ℓ + 2)` packets are sent in total:
  `|P|·R` first crossings, at most `|P|·R` crossings per step, as many reports.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma num_mem_tokMsg (z : TokF V) (k : ℕ) :
    Word.num k ∈ tokMsg z ↔ k = z.2.1 ∨ k = z.2.2.1 := by
  simp [tokMsg]

omit [Fintype V] [DecidableEq V] in
lemma num_mem_repMsg (r : Rep V) (k : ℕ) : Word.num k ∈ repMsg r ↔ k = r.2.1 := by
  simp [repMsg]

lemma repFor_isSome {K : Finset (Rep V)} {o : Option (Msg V)} (h : (repFor K o).isSome) :
    o.isSome := by
  cases o with
  | none => simp [repFor] at h
  | some m => rfl

lemma repFor_tok (K : Finset (Rep V)) (o : Option (TokF V)) :
    repFor K (o.map tokMsg) = o.bind (fun z => (lookup K z.1 z.2.1).map
      (fun q => repMsg (z.1, z.2.1, q))) := by
  cases o with
  | none => rfl
  | some z => simp [repFor]

section Sched

variable {C : Finset (Sym2 V)} {P : Finset (Port V)} {R t Rmax ℓ Dmax : ℕ}
  (τ : V → RWTable V Rmax ℓ Dmax)

/-- **Proper sends**: packets travel only along edges of the cluster. -/
theorem schedG_adj {N : WNet V} (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C) (s : ℕ) (u v : V)
    (h : (schedG C P R t τ s u v).isSome) : (clG N C).Adj u v := by
  have hA : ∀ s < R, ∀ u v, (schedG C P R t τ s u v).isSome → (clG N C).Adj u v := by
    intro s hs u v h
    rw [schedG_A C P R t τ hs, aSend_eq (τ := τ) hP] at h
    by_cases hex : ∃ p ∈ P, p.1 = u ∧ otherEnd p.2 u = v
    · obtain ⟨p, hp, h1, h2⟩ := hex
      have hpm := port_mem hP hp
      subst h1 h2
      exact clG_adj_of hCN hpm.1 hpm.2
    · rw [dif_neg hex] at h; simp at h
  have hB : ∀ j k, j < 2 * ℓ → k < t → ∀ u v, (schedG C P R t τ (bAt R t j k) u v).isSome →
      (clG N C).Adj u v := by
    intro j k hj hk u v h
    rw [schedG_B C P R t τ hj hk, bSend] at h
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨z', hz', -⟩ := Option.map_eq_some_iff.1 hz
    have hzm := mem_toList.1 (List.mem_of_getElem? hz')
    unfold crossTo at hzm
    obtain ⟨x, -, hx⟩ := mem_biUnion.1 hzm
    rw [Option.mem_toFinset, Option.mem_def, crossOf_eq_some] at hx
    obtain ⟨e, he, -⟩ := hx
    obtain ⟨he1, he2, he3⟩ := lazyStepD_some he
    rw [envG_E, mem_filter] at he1
    rw [envG_me] at he2 he3
    rw [he3]
    exact clG_adj_of hCN he1.1 he2
  by_cases hs : s < tEndRW R t ℓ
  · rcases phase_cases R t s hs with h1 | ⟨j, k, hj, hk, rfl⟩ | ⟨j, k, hj, hk, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hA s h1 u v h
    · exact hB j k hj hk u v h
    · rw [schedG_C C P R t τ hj hk, cSend] at h
      exact (hB j k hj hk v u (repFor_isSome h)).symm
    · rw [schedG_D C P R t τ hi, dSend] at h
      exact (hA i hi v u (repFor_isSome h)).symm
  · rw [schedG_end C P R t τ (by omega)] at h; simp at h

variable {hR : R ≤ Rmax} (N : WNet V) (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C)
  (hD : seedRange C ∣ Dmax) (hpos : 0 < Dmax)
  (hov : ¬ rwOverflow C P R ℓ t (rwSeedMap C P hR τ))

include N hCN hP hD hpos hov in
/-- The packets of phase B: tokens of crossing walks. -/
lemma schedG_B_eq {j k : ℕ} (hj : j < 2 * ℓ) (hk : k < t) (u v : V) :
    schedG C P R t τ (bAt R t j k) u v =
      ((crossTo (envG C P R t τ u) (heldG C P hR τ u j) j v).toList[k]?).map tokMsg := by
  rw [schedG_B C P R t τ hj hk, bSend, held_eq R N hCN hP hD hpos t hov j (by omega) u]

include N hCN hP hD hpos hov in
/-- **Encodable packets**: `5` words, numbers `≤ R + 2ℓ`. -/
theorem schedG_small (s : ℕ) (u v : V) (m : Msg V) (h : schedG C P R t τ s u v = some m) :
    m.length ≤ 5 ∧ ∀ k, Word.num k ∈ m → k ≤ R + 2 * ℓ := by
  have htok : ∀ j k, j < 2 * ℓ → k < t → ∀ u v z,
      (crossTo (envG C P R t τ u) (heldG C P hR τ u j) j v).toList[k]? = some z →
        z.2.1 < R ∧ z.2.2.1 ≤ 2 * ℓ := by
    intro j k hj hk u v z hz
    have hzm := mem_toList.1 (List.mem_of_getElem? hz)
    rw [mem_crossTo_heldG t hj] at hzm
    obtain ⟨w, e, -, -, rfl⟩ := hzm
    exact ⟨w.2.2, by have := cntG_le (C := C) (hR := hR) (τ := τ) w j; simp only; omega⟩
  have hA : ∀ s < R, ∀ u v m, aSend (envG C P R t τ u) v s = some m →
      m.length ≤ 5 ∧ ∀ k, Word.num k ∈ m → k < R := by
    intro s hs u v m h
    rw [aSend_eq (τ := τ) hP] at h
    by_cases hex : ∃ p ∈ P, p.1 = u ∧ otherEnd p.2 u = v
    · rw [dif_pos hex, Option.some.injEq] at h
      subst h
      refine ⟨by simp [tokMsg], fun k hk => ?_⟩
      rw [num_mem_tokMsg] at hk
      simp only at hk
      omega
    · rw [dif_neg hex] at h; simp at h
  by_cases hs : s < tEndRW R t ℓ
  · rcases phase_cases R t s hs with h1 | ⟨j, k, hj, hk, rfl⟩ | ⟨j, k, hj, hk, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [schedG_A C P R t τ h1] at h
      exact ⟨(hA s h1 u v m h).1, fun k hk => by have := (hA s h1 u v m h).2 k hk; omega⟩
    · rw [schedG_B_eq τ N hCN hP hD hpos hov hj hk] at h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
      have := htok j k hj hk u v z hz
      refine ⟨by simp [tokMsg], fun k hk => ?_⟩
      rw [num_mem_tokMsg] at hk
      omega
    · rw [schedG_C C P R t τ hj hk, cSend] at h
      simp only [fullO, envG_R, envG_t, envG_ℓ] at h
      rw [schedG_B_eq τ N hCN hP hD hpos hov hj hk, repFor_tok] at h
      obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 h
      have := htok j k hj hk v u z hz
      refine ⟨by simp [repMsg], fun k hk => ?_⟩
      rw [num_mem_repMsg] at hk
      simp only at hk
      omega
    · rw [schedG_D C P R t τ hi, dSend] at h
      simp only [fullO] at h
      rw [schedG_A C P R t τ hi, aSend_eq (τ := τ) hP] at h
      by_cases hex : ∃ p ∈ P, p.1 = v ∧ otherEnd p.2 v = u
      · rw [dif_pos hex, show some (tokMsg (hex.choose, i, 0, hex.choose.2)) =
          (some (hex.choose, i, 0, hex.choose.2)).map tokMsg from rfl, repFor_tok] at h
        obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 h
        simp only [Option.some.injEq] at hz
        subst hz
        refine ⟨by simp [repMsg], fun k hk => ?_⟩
        rw [num_mem_repMsg] at hk
        simp only at hk
        omega
      · rw [dif_neg hex] at h; simp [repFor] at h
  · rw [schedG_end C P R t τ (by omega)] at h; simp at h

/-! ### Counting packets -/

include hP in
lemma card_A_le (s : ℕ) :
    (univ.filter (fun uv : V × V => (aSend (envG C P R t τ uv.1) uv.2 s).isSome)).card ≤ P.card := by
  refine le_trans (card_le_card (t := P.image (fun p => (p.1, otherEnd p.2 p.1))) ?_) card_image_le
  intro uv huv
  rw [mem_filter, aSend_eq (τ := τ) hP] at huv
  by_cases hex : ∃ p ∈ P, p.1 = uv.1 ∧ otherEnd p.2 uv.1 = uv.2
  · obtain ⟨hp, h1, h2⟩ := hex.choose_spec
    refine mem_image.2 ⟨hex.choose, hp, ?_⟩
    exact Prod.ext h1 (by rw [h1]; exact h2)
  · rw [dif_neg hex] at huv; simp at huv

include N hCN hP hD hpos hov in
/-- At most `|P|·R` tokens cross in a step. -/
lemma sum_B_le {j : ℕ} (hj : j < 2 * ℓ) :
    ∑ k ∈ range t, (univ.filter (fun uv : V × V =>
      (schedG C P R t τ (bAt R t j k) uv.1 uv.2).isSome)).card ≤ P.card * R := by
  classical
  have h1 : ∀ k ∈ range t, (univ.filter (fun uv : V × V =>
      (schedG C P R t τ (bAt R t j k) uv.1 uv.2).isSome)).card =
      (univ.filter (fun uv : V × V =>
        k < (crossTo (envG C P R t τ uv.1) (heldG C P hR τ uv.1 j) j uv.2).card)).card := by
    intro k hk
    congr 1
    ext uv
    simp only [mem_filter, mem_univ, true_and]
    rw [schedG_B_eq τ N hCN hP hD hpos hov hj (mem_range.1 hk)]
    constructor
    · intro h
      by_contra hk'
      rw [List.getElem?_eq_none (by rw [length_toList]; omega)] at h
      simp at h
    · intro hk'
      rw [List.getElem?_eq_getElem (by rw [length_toList]; exact hk')]
      rfl
  rw [sum_congr rfl h1, sum_card_filter_swap]
  have h2 : ∀ uv : V × V, ((range t).filter (fun k =>
      k < (crossTo (envG C P R t τ uv.1) (heldG C P hR τ uv.1 j) j uv.2).card)).card ≤
      (univ.filter (fun w : RWIdx P R => (posG C P hR τ w j, (stepG C P hR τ w j).1) = uv)).card := by
    intro uv
    calc ((range t).filter (fun k =>
          k < (crossTo (envG C P R t τ uv.1) (heldG C P hR τ uv.1 j) j uv.2).card)).card
        ≤ (range (crossTo (envG C P R t τ uv.1) (heldG C P hR τ uv.1 j) j uv.2).card).card := by
          apply card_le_card
          intro k hk
          rw [mem_filter] at hk
          exact mem_range.2 hk.2
      _ = (crossTo (envG C P R t τ uv.1) (heldG C P hR τ uv.1 j) j uv.2).card := card_range _
      _ ≤ _ := by
          refine le_trans (card_le_card (t := (univ.filter (fun w : RWIdx P R =>
            (posG C P hR τ w j, (stepG C P hR τ w j).1) = uv)).image
              (fun w => (w.1.1, w.2.val, cntG C P hR τ w j + 1,
                ((stepG C P hR τ w j).2).getD (s(uv.1, uv.1))))) ?_) card_image_le
          intro z hz
          rw [mem_crossTo_heldG t hj] at hz
          obtain ⟨w, e, hw, h, rfl⟩ := hz
          refine mem_image.2 ⟨w, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
          · simp [hw, h]
          · simp [h]
  calc ∑ uv : V × V, ((range t).filter (fun k =>
        k < (crossTo (envG C P R t τ uv.1) (heldG C P hR τ uv.1 j) j uv.2).card)).card
      ≤ ∑ uv : V × V, (univ.filter (fun w : RWIdx P R =>
          (posG C P hR τ w j, (stepG C P hR τ w j).1) = uv)).card := sum_le_sum (fun uv _ => h2 uv)
    _ = (univ : Finset (RWIdx P R)).card :=
        (card_eq_sum_card_fiberwise (fun _ _ => mem_coe.2 (mem_univ _))).symm
    _ = P.card * R := by simp [RWIdx, Fintype.card_prod, Fintype.card_coe]

/-- A reply is sent only for a received packet. -/
lemma card_reply_le {f g : V → V → Option (Msg V)} (h : ∀ u v, (f u v).isSome → (g v u).isSome) :
    (univ.filter (fun uv : V × V => (f uv.1 uv.2).isSome)).card ≤
      (univ.filter (fun uv : V × V => (g uv.1 uv.2).isSome)).card := by
  refine card_le_card_of_injOn Prod.swap (fun uv huv => ?_) (fun a _ b _ hab => Prod.swap_injective hab)
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at huv ⊢
  exact h _ _ huv

/-- Sums over the macro-rounds of a window of `J` steps of `t` slots. -/
lemma sum_range_mul_split (J t : ℕ) (f : ℕ → ℕ) :
    ∑ s ∈ range (J * t), f s = ∑ j ∈ range J, ∑ k ∈ range t, f (j * t + k) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

include N hCN hP hD hpos hov in
/-- **The number of packets**: at most `|P|·R·(4ℓ + 2)`. -/
theorem sum_schedG_le :
    ∑ s ∈ range (tEndRW R t ℓ), (univ.filter (fun uv : V × V =>
      (schedG C P R t τ s uv.1 uv.2).isSome)).card ≤ P.card * R * (4 * ℓ + 2) := by
  set f : ℕ → ℕ := fun s => (univ.filter (fun uv : V × V =>
      (schedG C P R t τ s uv.1 uv.2).isSome)).card with hf
  have hT : tEndRW R t ℓ = R + 2 * ℓ * t + 2 * ℓ * t + R := by unfold tEndRW; ring
  rw [hT, sum_range_add, sum_range_add, sum_range_add]
  have hA : ∀ s < R, f s ≤ P.card := by
    intro s hs
    simp only [hf]
    rw [show (univ.filter (fun uv : V × V => (schedG C P R t τ s uv.1 uv.2).isSome)) =
      univ.filter (fun uv : V × V => (aSend (envG C P R t τ uv.1) uv.2 s).isSome) by
        ext uv; simp [schedG_A C P R t τ hs]]
    exact card_A_le τ hP s
  have hBsum : ∀ j < 2 * ℓ, ∑ k ∈ range t, f (bAt R t j k) ≤ P.card * R :=
    fun j hj => sum_B_le τ N hCN hP hD hpos hov hj
  have hC : ∀ j < 2 * ℓ, ∀ k < t, f (cAt R t ℓ j k) ≤ f (bAt R t j k) := by
    intro j hj k hk
    apply card_reply_le
    intro u v h
    rw [schedG_C C P R t τ hj hk, cSend] at h
    exact repFor_isSome h
  have hDl : ∀ i < R, f (dRnd R t ℓ i) ≤ P.card := by
    intro i hi
    refine le_trans ?_ (hA i hi)
    apply card_reply_le
    intro u v h
    rw [schedG_D C P R t τ hi, dSend] at h
    exact repFor_isSome h
  have s1 : ∑ s ∈ range R, f s ≤ R * P.card := by
    calc ∑ s ∈ range R, f s ≤ ∑ _s ∈ range R, P.card :=
          sum_le_sum (fun s hs => hA s (mem_range.1 hs))
      _ = R * P.card := by simp
  have s2 : ∑ s ∈ range (2 * ℓ * t), f (R + s) ≤ 2 * ℓ * (P.card * R) := by
    rw [sum_range_mul_split]
    calc ∑ j ∈ range (2 * ℓ), ∑ k ∈ range t, f (R + (j * t + k))
        ≤ ∑ _j ∈ range (2 * ℓ), P.card * R := by
          refine sum_le_sum (fun j hj => ?_)
          have := hBsum j (mem_range.1 hj)
          simpa [bAt, add_assoc] using this
      _ = 2 * ℓ * (P.card * R) := by simp
  have s3 : ∑ s ∈ range (2 * ℓ * t), f (R + 2 * ℓ * t + s) ≤ 2 * ℓ * (P.card * R) := by
    rw [sum_range_mul_split, ← sum_range_reflect]
    calc ∑ j ∈ range (2 * ℓ), ∑ k ∈ range t, f (R + 2 * ℓ * t + ((2 * ℓ - 1 - j) * t + k))
        ≤ ∑ _j ∈ range (2 * ℓ), P.card * R := by
          refine sum_le_sum (fun j hj => ?_)
          have hj := mem_range.1 hj
          refine le_trans (sum_le_sum (fun k hk => ?_)) (hBsum j hj)
          have := hC j hj k (mem_range.1 hk)
          simpa [cAt, add_assoc] using this
      _ = 2 * ℓ * (P.card * R) := by simp
  have s4 : ∑ s ∈ range R, f (R + 2 * ℓ * t + 2 * ℓ * t + s) ≤ R * P.card := by
    calc ∑ s ∈ range R, f (R + 2 * ℓ * t + 2 * ℓ * t + s) ≤ ∑ _s ∈ range R, P.card := by
          refine sum_le_sum (fun s hs => ?_)
          have := hDl s (mem_range.1 hs)
          have e : dRnd R t ℓ s = R + 2 * ℓ * t + 2 * ℓ * t + s := by unfold dRnd; ring
          rw [← e]; exact this
      _ = R * P.card := by simp
  calc _ ≤ R * P.card + 2 * ℓ * (P.card * R) + 2 * ℓ * (P.card * R) + R * P.card :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add s1 s2) s3) s4
    _ = P.card * R * (4 * ℓ + 2) := by ring

end Sched

end APSP.Stoc.Congest
