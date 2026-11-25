import ApspStoc.Congest.AggUpDownCore

/-!
# Costs and success of the store-and-forward protocol (`AggUpDownCore.lean`)

`sfM_count`: the words of the schedule `sfM` are at most `L` per active packet and hop of its
walk (the map from a word to its packet, hop and position is injective, as the slot of a packet
is determined by its rank). Hence at most `L · aggLen j S` messages (`sfM_msgs`) and at most
`L · rhoAgg j S e` words over the edge `e` (`sfM_load`). `sfM_adj`: words travel only along edges
of the overlay instance (edges of clusters between nodes of the footprint of `S`). `sf_succ`:
success of the protocol on the overlay instance, via `succ_histP`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Costs -/

open Classical in
/-- the active packets -/
noncomputable def actSet (E : Overlays V) (val : V → Finset (Sym2 V) → Option (Msg V)) :
    Finset (V × Finset (Sym2 V)) :=
  univ.filter (fun p => Act E val p.1 p.2)

section Cost

variable {N : WNet V} {E : Overlays V} {j : ℕ} {d : Bool}
  {val : V → Finset (Sym2 V) → Option (Msg V)} {Bw μ sz : ℕ}
  (hE : EmbValid N.G E) (hj : j < Fintype.card V)
include hE hj

/-- **Counting**: the words of the schedule over directed pairs whose edge satisfies `Pe` are at
most `L` per active packet and hop of its walk over such an edge. -/
lemma sfM_count (Pe : Sym2 V → Prop) [DecidablePred Pe] (hs : V × Finset (Sym2 V) → Finset ℕ)
    (hhs : ∀ p h e, (pkW E j d p.1 p.2)[h]? = some e → Pe e → h ∈ hs p) :
    ∑ s ∈ range (E.dil * (sz * sfL Bw μ)), ((univ.filter (fun uv : V × V =>
      (sfM E j d val Bw μ sz uv.1 uv.2 s).isSome)).filter (fun uv => Pe s(uv.1, uv.2))).card ≤
    sfL Bw μ * ∑ p ∈ actSet E val, (hs p).card := by
  have h1 : ∑ s ∈ range (E.dil * (sz * sfL Bw μ)), ((univ.filter (fun uv : V × V =>
      (sfM E j d val Bw μ sz uv.1 uv.2 s).isSome)).filter (fun uv => Pe s(uv.1, uv.2))).card =
      ((range (E.dil * (sz * sfL Bw μ)) ×ˢ (univ : Finset (V × V))).filter (fun x =>
        (sfM E j d val Bw μ sz x.2.1 x.2.2 x.1).isSome ∧ Pe s(x.2.1, x.2.2))).card := by
    rw [card_filter, sum_product]
    refine sum_congr rfl (fun s _ => ?_)
    rw [filter_filter, card_filter]
  rw [h1]
  have hsub : (range (E.dil * (sz * sfL Bw μ)) ×ˢ (univ : Finset (V × V))).filter (fun x =>
        (sfM E j d val Bw μ sz x.2.1 x.2.2 x.1).isSome ∧ Pe s(x.2.1, x.2.2)) ⊆
      (actSet E val).biUnion (fun p => (hs p).biUnion
          (fun h => (range (sfL Bw μ)).image (fun r =>
            (h * (sz * sfL Bw μ) + rkIn (srcs E j d val (wv (pkW E j d p.1 p.2) (pkS E j d p.1 p.2) h)
              (wv (pkW E j d p.1 p.2) (pkS E j d p.1 p.2) (h + 1)) h) p.1 * sfL Bw μ + r,
              (wv (pkW E j d p.1 p.2) (pkS E j d p.1 p.2) h,
                wv (pkW E j d p.1 p.2) (pkS E j d p.1 p.2) (h + 1)))))) := by
    rintro ⟨s, a, b⟩ hx
    simp only [mem_filter, mem_product, mem_range, mem_univ, and_true] at hx
    obtain ⟨-, u, hp⟩ := sfM_isSome hx.2.1
    obtain ⟨hu, hq⟩ := pickR_eq_some.1 hp
    have hu' := hu
    simp only [srcs, mem_filter, mem_univ, true_and] at hu'
    obtain ⟨C, hA, hW, hv⟩ := hu'
    have hlt : s / (sz * sfL Bw μ) < (pkW E j d u C).length :=
      (List.getElem?_eq_some_iff.1 hW).1
    have hwk := pk_walk d hE hj hA.1 hA.2.1
    have hab : wv (pkW E j d u C) (pkS E j d u C) (s / (sz * sfL Bw μ) + 1) = b := by
      have := walk_get? hwk hlt
      rw [hW, hv] at this
      exact (Sym2.congr_right.1 (Option.some.inj this)).symm
    have hAct : (u, C) ∈ actSet E val := by
      simp only [actSet, mem_filter, mem_univ, true_and]; exact hA
    refine mem_biUnion.2 ⟨(u, C), hAct, mem_biUnion.2 ⟨s / (sz * sfL Bw μ),
      hhs (u, C) _ _ hW hx.2.2,
      mem_image.2 ⟨s % (sz * sfL Bw μ) % sfL Bw μ, mem_range.2 (Nat.mod_lt _ (sfL_pos Bw μ)), ?_⟩⟩⟩
    dsimp only
    rw [hv, hab, hq, ← slot_recomp s (sz * sfL Bw μ) (sfL Bw μ)]
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  rw [mul_sum]
  refine sum_le_sum (fun p _ => (card_biUnion_le).trans ?_)
  refine (sum_le_sum (fun h _ => (card_image_le).trans (le_of_eq (card_range _)))).trans ?_
  rw [sum_const, smul_eq_mul, mul_comm]

omit hE hj in
/-- Sums over the active packets are bounded by sums over the aggregator edges of `S`. -/
lemma sum_act_le {S : Finset V} (hS : ∀ u C, Act E val u C → u ∈ S)
    (f : V × Finset (Sym2 V) → ℕ) :
    ∑ p ∈ actSet E val, f p ≤ ∑ v ∈ S, ∑ C ∈ clustersOf E.cl v, f (v, C) := by
  classical
  calc ∑ p ∈ actSet E val, f p ≤ ∑ p ∈ (S ×ˢ E.cl).filter (fun p => p.1 ∈ nodes p.2), f p := by
        refine sum_le_sum_of_subset (fun p hp => ?_)
        simp only [actSet, mem_filter, mem_univ, true_and] at hp
        simp only [mem_filter, mem_product]
        exact ⟨⟨hS _ _ hp, hp.1⟩, hp.2.1⟩
    _ = ∑ v ∈ S, ∑ C ∈ clustersOf E.cl v, f (v, C) := by
        rw [sum_filter, sum_product]
        refine sum_congr rfl (fun v _ => ?_)
        rw [clustersOf, sum_filter]

/-- Messages: at most `L · aggLen j S`. -/
lemma sfM_msgs {S : Finset V} (hS : ∀ u C, Act E val u C → u ∈ S) :
    ∑ s ∈ range (E.dil * (sz * sfL Bw μ)), (univ.filter (fun uv : V × V =>
      (sfM E j d val Bw μ sz uv.1 uv.2 s).isSome)).card ≤ sfL Bw μ * E.aggLen j S := by
  have h := sfM_count (d := d) (val := val) (Bw := Bw) (μ := μ) (sz := sz) hE hj (fun _ => True)
    (fun p => range (pkW E j d p.1 p.2).length)
    (fun p h e he _ => mem_range.2 (List.getElem?_eq_some_iff.1 he).1)
  simp only [filter_true] at h
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  simp only [card_range, pkW, length_trB]
  exact sum_act_le hS (fun p => (E.path j p.1 p.2).length)

/-- Load: at most `L · rhoAgg j S e` on the edge `e`. -/
lemma sfM_load {S : Finset V} (hS : ∀ u C, Act E val u C → u ∈ S) (e : Sym2 V) :
    ∑ s ∈ range (E.dil * (sz * sfL Bw μ)), ((univ.filter (fun uv : V × V =>
      (sfM E j d val Bw μ sz uv.1 uv.2 s).isSome)).filter (fun uv => s(uv.1, uv.2) = e)).card ≤
      sfL Bw μ * E.rhoAgg j S e := by
  refine (sfM_count (d := d) (val := val) (Bw := Bw) (μ := μ) (sz := sz) hE hj
    (fun e' => e' = e)
    (fun p => (range (pkW E j d p.1 p.2).length).filter (fun h => (pkW E j d p.1 p.2)[h]? = some e))
    (fun p h e' he he' => mem_filter.2 ⟨mem_range.2 (List.getElem?_eq_some_iff.1 he).1,
      by rw [he, he']⟩)).trans (Nat.mul_le_mul_left _ ?_)
  refine le_trans (le_of_eq (sum_congr rfl (fun p _ => ?_)))
    (sum_act_le hS (fun p => (E.path j p.1 p.2).count e))
  show _ = (E.path j p.1 p.2).count e
  rw [← count_trB d]
  exact card_filter_getElem?_eq_count e (pkW E j d p.1 p.2)

/-- Words are sent only along edges of the overlay instance. -/
lemma sfM_adj {Pt S : Finset V} (hfp : footprint E j S ⊆ Pt)
    (hS : ∀ u C, Act E val u C → u ∈ S) {a b : V} {s : ℕ}
    (h : (sfM E j d val Bw μ sz a b s).isSome) : (ioG N Pt).Adj a b := by
  classical
  obtain ⟨-, u, hp⟩ := sfM_isSome h
  have hu := mem_of_pickR hp
  simp only [srcs, mem_filter, mem_univ, true_and] at hu
  obtain ⟨C, hA, hW, -⟩ := hu
  have hpath : s(a, b) ∈ E.path j u C := (trB_mem d).1 (List.mem_of_getElem? hW)
  have hG : s(a, b) ∈ N.G.edgeFinset := hE.sub C hA.1 (hE.local_ j u C _ hpath)
  have hcl : C ∈ clustersOf E.cl u := mem_filter.2 ⟨hA.1, hA.2.1⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hG
  exact ⟨hG, hfp (mem_footprint.2 (Or.inr ⟨u, hS u C hA, C, hcl, _, hpath,
    Sym2.mem_mk_left a b⟩)), hfp (mem_footprint.2 (Or.inr ⟨u, hS u C hA, C, hcl, _, hpath,
    Sym2.mem_mk_right a b⟩))⟩

end Cost

/-! ## Success -/

/-- **Success of the store-and-forward protocol** on the overlay instance, for an origin rule that
produces the packets of the schedule at hop `0` and an output rule that is correct on the history
of the schedule: the run follows the schedule `sfM`, halts at the public round
`E.dil · sz · L`, and its costs are within `L ≤ (Bw + 3)(μ + 1)` times the aggregator load and
length of `S`. -/
theorem sf_succ (Bw μ : ℕ) (d : Bool) (orig : Orig V)
    (O : NCtx V → (Agent V → Option Mem) → Hist V → Agent V → Option Mem)
    (N : WNet V) (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (x : Agent V → Mem)
    (val : V → Finset (Sym2 V) → Option (Msg V))
    (hE : EmbValid N.G E) (hj : j < Fintype.card V) (hsz : S.card ≤ sz)
    (hfp : footprint E j S ⊆ Pt) (hS : ∀ u C, Act E val u C → u ∈ S)
    (horig : ∀ a ∈ Pt, ∀ b u, orig ((ioInst N E j sz Pt).ctx a)
      (inpAt (ioInst N E j sz Pt) x a) b u =
      if u ∈ srcs E j d val a b 0 then some (pay E val u s(a, b)) else none)
    {Q : (Agent V → Mem) → Prop} (y : Agent V → Mem)
    (hy : ∀ g v, (ioInst N E j sz Pt).host g = some v →
      O ((ioInst N E j sz Pt).ctx v) (inpAt (ioInst N E j sz Pt) x v)
        (schedHist (sfM E j d val Bw μ sz) v (E.dil * (sz * sfL Bw μ))) g = some (y g))
    (hQ : Q y) (ω : V → Unit) :
    Succ (sfProto Bw μ d orig O) (ioInst N E j sz Pt) x Q
      (Prof.mk ((Bw + 3) * (μ + 1) * (E.dil + 1) * (sz + 1))
        (((Bw + 3) * (μ + 1)) • E.rhoAgg j S) ((Bw + 3) * (μ + 1) * E.aggLen j S)) ω := by
  classical
  have hL : sfL Bw μ ≤ (Bw + 3) * (μ + 1) := by
    unfold sfL encLen; nlinarith
  unfold sfProto
  refine succ_histP (F := sfSend Bw μ d orig) (Tf := sfT Bw μ) (O := O)
    (T := E.dil * (sz * sfL Bw μ)) (fun v => ?_) (sfM E j d val Bw μ sz) ?_ ?_ ?_ ?_ y hy hQ
  · unfold sfT sfB
    rw [(ctxOK_ioInst N E j sz Pt v).dil, (ctxOK_ioInst N E j sz Pt v).sz]
  · intro s hs u v
    refine ⟨fun hu => sfSend_sched hE hj hS hsz orig (ctxOK_ioInst N E j sz Pt u)
      (horig u hu) hs v, fun hn => ?_, fun w hw => sfM_wordOK hw⟩
    cases hm : sfM E j d val Bw μ sz u v s with
    | none => rfl
    | some w => exact absurd (sfM_adj hE hj hfp hS (by rw [hm]; rfl)) hn
  · simp only [Prof.rounds_mk]
    calc E.dil * (sz * sfL Bw μ) ≤ (E.dil + 1) * ((sz + 1) * ((Bw + 3) * (μ + 1))) :=
          Nat.mul_le_mul (Nat.le_succ _) (Nat.mul_le_mul (Nat.le_succ _) hL)
      _ = (Bw + 3) * (μ + 1) * (E.dil + 1) * (sz + 1) := by ring
  · simp only [Prof.msgs_mk]
    exact (sfM_msgs hE hj hS).trans (Nat.mul_le_mul_right _ hL)
  · intro e
    simp only [Prof.load_mk, Pi.smul_apply, smul_eq_mul]
    exact (sfM_load hE hj hS e).trans (Nat.mul_le_mul_right _ hL)

end APSP.Stoc.Congest
