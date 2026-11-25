import ApspStoc.Congest.AggUpDownCost

/-!
# The aggregator exchanges `aggUp` and `aggDown` in the CONGEST semantics

`aggUp_congest : AggUpC` and `aggDown_congest : AggDownC` prove the toolkit fields `aggUp` and
`aggDown` (Lemma 2.2 on the aggregator edges of `S` in `L_j`) for the concrete semantics, with the
deterministic store-and-forward protocol of `AggUpDownCore.lean` (failure probability `0`,
`Kδ = 0`), constant `K = Bw + 3` and `k = 0`.

## `aggUp` (`upAlg`)
Every node `v ∈ S` with a value `x v = some m` sends `m` along the embedded path
`E.path j v C` to the host of the aggregator of each of its clusters `C`. The node knows these
paths: `emb j v k` for the key edges `k` of its clusters. Relays forward by the header `.id v` and
the edge over which the packet arrived (the store-and-forward schedule `sfM` of the core file,
upwards). The host of the aggregator of `C` (the common end of the paths of `C`, `aggHost`) outputs
for every `v ∈ nodes C`: its own value if the path is empty (then `v` is the host), otherwise the
value decoded from the stream received at the last hop of `E.path j v C` (none if nothing arrived).
Aggregators hosted outside `Pt` are not simulated; they have no node of `S` (their host would be in
the footprint of `S`).

## `aggDown` (`downAlg`)
The host of the aggregator of `C` sends `x (.inr C) v` to every `v ∈ nodes C` with a value, along
the reversed path `E.path j v C` (header `.id v`, the destination). Every node `v` outputs, for
each key edge `k` of its clusters (`emb j v k ≠ none`), the value received at the last hop of the
reversed path (or, if the path is empty, the value of the aggregator it hosts itself), collected in
a multiset; the key edges of `v`'s clusters are in bijection with the clusters of `v`.

## Costs
`E.dil · sz · L` rounds with `L = 1 + encLen Bw μ ≤ (Bw + 3)(μ + 1)`; every packet crosses each edge
of its path once, in `L` words, so the load is at most `L · rhoAgg j S` and the number of messages
at most `L · aggLen j S`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The statements -/

/-- the toolkit field `aggUp` for the CONGEST semantics -/
def AggUpC : Prop := ∀ c Bw : ℕ, ∃ (K k Kδ : ℕ) (A : ℕ → ℕ → CAlg), ∀ {V : Type} [Fintype V]
    [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V)
    (μ : ℕ) (x : Agent V → Option (Msg V)), EmbValid N.G E → j < Fintype.card V → S.card ≤ sz →
    footprint E j S ⊆ Pt →
    (∀ v, x (.inl v) ≠ none → v ∈ S) → (∀ v m, x (.inl v) = some m → m.Small μ (ν ^ Bw)) →
    CImplT (A ν μ) N (.io E j sz Pt (Option (Msg V)) (V → Option (Msg V)) x
      (fun y => ∀ C ∈ E.cl, ∀ v, y (.inr C) v = if v ∈ nodes C then x (.inl v) else none))
      (Prof.mk (K * lg ν ^ k * (μ + 1) * (E.dil + 1) * (sz + 1)) ((K * (μ + 1)) • E.rhoAgg j S)
        (K * (μ + 1) * E.aggLen j S))
      (whp Kδ c ν)

/-- the toolkit field `aggDown` for the CONGEST semantics -/
def AggDownC : Prop := ∀ c Bw : ℕ, ∃ (K k Kδ : ℕ) (A : ℕ → ℕ → CAlg), ∀ {V : Type} [Fintype V]
    [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V)
    (μ : ℕ) (x : Agent V → V → Option (Msg V)), EmbValid N.G E → j < Fintype.card V →
    S.card ≤ sz → footprint E j S ⊆ Pt →
    (∀ C ∈ E.cl, ∀ v, x (.inr C) v ≠ none → v ∈ S ∧ v ∈ nodes C) →
    (∀ C ∈ E.cl, ∀ v m, x (.inr C) v = some m → m.Small μ (ν ^ Bw)) →
    CImplT (A ν μ) N (.io E j sz Pt (V → Option (Msg V)) (Multiset (Msg V)) x
      (fun y => ∀ v, y (.inl v) = (clustersOf E.cl v).val.filterMap (fun C => x (.inr C) v)))
      (Prof.mk (K * lg ν ^ k * (μ + 1) * (E.dil + 1) * (sz + 1)) ((K * (μ + 1)) • E.rhoAgg j S)
        (K * (μ + 1) * E.aggLen j S))
      (whp Kδ c ν)

/-! ## Common facts -/

section Common

variable {N : WNet V} {E : Overlays V} {j : ℕ}

/-- A value with `≤ μ` words and numbers `≤ ν^Bw`, `ν ≤ n`, can be encoded. -/
lemma encOK_of_small {ν Bw μ : ℕ} (hν : ν ≤ Fintype.card V) {m : Msg V}
    (h : m.Small μ (ν ^ Bw)) : EncOK (Fintype.card V) Bw μ m := by
  refine ⟨h.1, fun k hk => ?_⟩
  calc k ≤ ν ^ Bw := h.2 k hk
    _ ≤ (Fintype.card V + 4) ^ Bw := Nat.pow_le_pow_left (by omega) _
    _ < (Fintype.card V + 4) ^ (Bw + 1) := Nat.pow_lt_pow_right (by omega) (by omega)

/-- The host of a simulated aggregator. -/
lemma ioHost_inr_some {Pt : Finset V} {C : Finset (Sym2 V)} {a : V}
    (h : ioHost E j Pt (.inr C) = some a) : aggHost E j C = some a ∧ a ∈ Pt := by
  simp only [ioHost] at h
  cases hh : aggHost E j C with
  | none => rw [hh] at h; cases h
  | some h' =>
    rw [hh] at h
    dsimp only at h
    by_cases ha : h' ∈ Pt
    · rw [ite_eq_left ha] at h; cases h; exact ⟨rfl, ha⟩
    · rw [ite_eq_right ha] at h; cases h

variable (hE : EmbValid N.G E) (hj : j < Fintype.card V)
include hE hj

/-- The aggregator of a cluster is hosted at the end of the paths of its nodes. -/
lemma aggHost_eq {C : Finset (Sym2 V)} {u : V} (hC : C ∈ E.cl) (hu : u ∈ nodes C) :
    aggHost E j C = some (pEnd E j u C) := by
  classical
  have hex : C ∈ E.cl ∧ (nodes C).Nonempty ∧
      ∃ hv : V, ∀ v ∈ nodes C, IsEdgeWalk (E.path j v C) v hv := by
    obtain ⟨h, -, hw⟩ := hE.walk j hj C hC
    exact ⟨hC, ⟨u, hu⟩, h, hw⟩
  unfold aggHost
  rw [dite_eq_left hex]
  exact congrArg some (walk_end_unique (hex.2.2.choose_spec u hu) (path_walk hE hj hC hu))

omit hj in
/-- A hosted aggregator belongs to a cluster of the family. -/
lemma mem_of_aggHost {C : Finset (Sym2 V)} {h : V} (hh : aggHost E j C = some h) : C ∈ E.cl := by
  classical
  by_contra hn
  unfold aggHost at hh
  rw [dite_eq_right (fun hex => hn hex.1)] at hh
  cases hh

/-- The host of the aggregator of `C` in the overlay instance. -/
lemma ioHost_inr_iff {Pt : Finset V} {C : Finset (Sym2 V)} {u a : V} (hC : C ∈ E.cl)
    (hu : u ∈ nodes C) : ioHost E j Pt (.inr C) = some a ↔ pEnd E j u C = a ∧ a ∈ Pt := by
  simp only [ioHost, aggHost_eq hE hj hC hu]
  constructor
  · intro h
    by_cases ha : pEnd E j u C ∈ Pt
    · rw [ite_eq_left ha] at h; exact ⟨Option.some.inj h, (Option.some.inj h) ▸ ha⟩
    · rw [ite_eq_right ha] at h; cases h
  · rintro ⟨rfl, ha⟩
    rw [ite_eq_left ha]

omit hj in
/-- The path known to a node under the key edge of a cluster of the source is the path of that
cluster. -/
lemma emb_key {a u : V} {C : Finset (Sym2 V)} {l : List (Sym2 V)} (hC : C ∈ E.cl)
    (hu : u ∈ nodes C) (hl : ioEmb E a j u (srcPort C u).2 = some l) : l = E.path j u C := by
  obtain ⟨C', hC', hu', hk, -, rfl⟩ := ioEmb_spec hl
  have h1 := (srcPort_snd_mem hu').1
  rw [hk] at h1
  rw [clu_eq hE hC' hC h1 (srcPort_snd_mem hu).1]

end Common

/-- A multiset `filterMap` over a finite set as a sum. -/
lemma filterMap_val_eq_sum {α β : Type} (s : Finset α) (f : α → Option β) :
    s.val.filterMap f = ∑ x ∈ s, ((f x).toList : Multiset β) := by
  rw [Finset.sum_eq_multiset_sum]
  generalize s.val = m
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    cases hf : f a with
    | none => rw [Multiset.filterMap_cons_none _ _ hf, ih]; simp [hf]
    | some b => rw [Multiset.filterMap_cons_some _ _ _ hf, ih]; simp [hf]

/-! ## `aggUp` -/

open Classical in
/-- the node's own value (`none` if absent or of another type) -/
noncomputable def myVal (inp : Agent V → Option Mem) (v : V) : Option (Msg V) :=
  match inp (.inl v) with
  | some m => if h : m.1 = Option (Msg V) then cast h m.2 else none
  | none => none

open Classical in
/-- upwards, a node originates its own value on the first edge of each of its paths -/
noncomputable def upOrig : Orig V := fun c inp b u =>
  if u = c.me ∧ ∃ k l, c.emb (jOf c) c.me k = some l ∧ l[0]? = some s(c.me, b) then
    myVal inp c.me else none

/-- the value of `v` received by the host of the aggregator of `C` -/
noncomputable def upRes (Bw μ : ℕ) (c : NCtx V) (inp : Agent V → Option Mem)
    (H : ℕ → V → Option (Word V)) (C : Finset (Sym2 V)) (v : V) : Option (Msg V) :=
  match c.emb (jOf c) v (srcPort C v).2 with
  | none => none
  | some l => if l = [] then myVal inp v else rcv Bw μ c H v l

/-- the outputs of `aggUp`: the aggregator of `C` outputs the values of the nodes of `C` -/
noncomputable def upOut (Bw μ : ℕ) (c : NCtx V) (inp : Agent V → Option Mem) (hist : Hist V) :
    Agent V → Option Mem
  | .inl _ => some ⟨V → Option (Msg V), fun _ => none⟩
  | .inr C => some ⟨V → Option (Msg V), fun v =>
      if v ∈ nodes C then upRes Bw μ c inp (hget hist) C v else none⟩

/-- **The `aggUp` algorithm** (it does not use `ν`). -/
noncomputable def upAlg (Bw : ℕ) (_ν μ : ℕ) : CAlg := fun _V _ _ =>
  sfProto Bw μ false upOrig (upOut Bw μ)

section Up

variable {N : WNet V} {E : Overlays V} {j sz : ℕ} {Pt : Finset V} {x : Agent V → Option (Msg V)}

lemma myVal_io {a : V} (ha : a ∈ Pt) :
    myVal (inpAt (ioInst N E j sz Pt) (inOf x) a) a = x (.inl a) := by
  simp [myVal, inpAt, ioInst, ioHost, inOf, ha]

end Up

/-- **`aggUp` in the CONGEST semantics.** -/
theorem aggUp_congest : AggUpC := by
  intro c Bw
  refine ⟨Bw + 3, 0, 0, upAlg Bw, ?_⟩
  intro V _ _ N ν _ hν2 E j sz Pt S μ x hE hj hsz hfp hxS hsmall
  classical
  let val : V → Finset (Sym2 V) → Option (Msg V) := fun u _ => x (.inl u)
  have hS : ∀ u C, Act E val u C → u ∈ S := fun u C h =>
    hxS u (Option.isSome_iff_ne_none.1 h.2.2)
  show ImplI (sfProto Bw μ false upOrig (upOut Bw μ)) (ioInst N E j sz Pt) (inOf x)
    (postOf (ioInst N E j sz Pt) _) _ _
  refine ImplI.of_forall _ _ (by unfold whp; simp) (fun ω => ?_)
  simp only [pow_zero, mul_one]
  let z : Agent V → V → Option (Msg V) := fun g => match g with
    | .inl _ => fun _ => none
    | .inr C => fun v => if v ∈ nodes C then x (.inl v) else none
  refine sf_succ Bw μ false upOrig (upOut Bw μ) N E j sz Pt S (inOf x) val hE hj hsz hfp hS
    ?_ (fun g => ⟨V → Option (Msg V), z g⟩) ?_ ⟨z, fun g _ => rfl, fun C _ v => rfl⟩ ω
  · -- the origin rule produces the packets of hop `0`
    intro a ha b u
    have hc := ctxOK_ioInst N E j sz Pt a
    unfold upOrig
    rw [hc.me, hc.j, hc.emb, myVal_io ha]
    by_cases hcond : u = a ∧ ∃ k l, ioEmb E a j a k = some l ∧ l[0]? = some s(a, b)
    · rw [ite_eq_left hcond]
      obtain ⟨hua, k, l, hl, hl0⟩ := hcond
      rw [hua]
      cases hx : x (.inl a) with
      | none =>
        rw [ite_eq_right]
        simp only [srcs, mem_filter, mem_univ, true_and, not_exists]
        intro C hA
        simp [Act, val, hx] at hA
      | some m =>
        obtain ⟨C, hC, hu, -, -, rfl⟩ := ioEmb_spec hl
        rw [ite_eq_left]
        · simp [pay, val, hx]
        · simp only [srcs, mem_filter, mem_univ, true_and]
          exact ⟨C, ⟨hC, hu, by simp [val, hx]⟩, hl0, by simp [pkS]⟩
    · rw [ite_eq_right hcond, ite_eq_right]
      simp only [srcs, mem_filter, mem_univ, true_and, not_exists]
      rintro C ⟨hA, hW, hv⟩
      have hv' : u = a := by simpa [pkS] using hv
      subst hv'
      exact hcond ⟨rfl, _, _, ioEmb_eq_some hE.disj hA.1 hA.2.1 (Or.inl rfl), hW⟩
  · -- outputs
    intro g v hg
    cases g with
    | inl w => rfl
    | inr C =>
      have hg' : ioHost E j Pt (.inr C) = some v := hg
      have hC := mem_of_aggHost hE (ioHost_inr_some hg').1
      simp only [upOut, z]
      refine congrArg (fun f => some (⟨V → Option (Msg V), f⟩ : Mem)) (funext fun u => ?_)
      by_cases hu : u ∈ nodes C
      · rw [ite_eq_left hu, ite_eq_left hu]
        have hc := ctxOK_ioInst N E j sz Pt v
        obtain ⟨hend, hv⟩ := (ioHost_inr_iff hE hj hC hu).1 hg'
        have hpe : pkE E j false u C = v := hend
        unfold upRes
        rw [hc.j, hc.emb]
        have hemb : ioEmb E v j u (srcPort C u).2 = some (E.path j u C) := by
          have := emb_pk false hE hj hC hu (le_refl _)
          rw [walk_end _ _ _ (pk_walk false hE hj hC hu), hpe] at this
          exact this
        rw [hemb]
        dsimp only
        by_cases hnil : E.path j u C = []
        · rw [ite_eq_left hnil]
          have : u = v := by
            have := path_walk hE hj hC hu
            rw [hnil] at this
            exact (show u = pEnd E j u C from this).trans hend
          subst this
          exact myVal_io hv
        · rw [ite_eq_right hnil]
          exact rcv_sched hE hj hS hsz hC hu hnil (d := false) hpe hc
            (fun m hm => encOK_of_small hν2 (hsmall u m hm)) le_rfl
      · rw [ite_eq_right hu, ite_eq_right hu]

/-! ## `aggDown` -/

open Classical in
/-- the data of the aggregator of `C` if the node hosts it (`none` otherwise or if of another
type) -/
noncomputable def aggIn (inp : Agent V → Option Mem) (C : Finset (Sym2 V)) :
    Option (V → Option (Msg V)) :=
  match inp (.inr C) with
  | some m => if h : m.1 = (V → Option (Msg V)) then some (cast h m.2) else none
  | none => none

open Classical in
/-- downwards, the host of the aggregator of `C` originates the value for `u` on the last edge of
the path of `u` (the first edge of the reversed path) -/
noncomputable def downOrig : Orig V := fun c inp b u =>
  if hc : ∃ C, ((aggIn inp C).bind (fun f => f u)).isSome ∧ u ∈ nodes C ∧
      ∃ l, c.emb (jOf c) u (srcPort C u).2 = some l ∧ l.reverse[0]? = some s(c.me, b) then
    (aggIn inp hc.choose).bind (fun f => f u)
  else none

open Classical in
/-- the value for the node itself of the aggregator with key edge `k` that the node hosts (the
case of an empty path) -/
noncomputable def ownAgg (c : NCtx V) (inp : Agent V → Option Mem) (k : Sym2 V) :
    Option (Msg V) :=
  if h : ∃ C, (aggIn inp C).isSome ∧ c.me ∈ nodes C ∧ (srcPort C c.me).2 = k then
    (aggIn inp h.choose).bind (fun f => f c.me)
  else none

/-- the value received from the aggregator of the cluster of the node with key edge `k` -/
noncomputable def downVal (Bw μ : ℕ) (c : NCtx V) (inp : Agent V → Option Mem)
    (H : ℕ → V → Option (Word V)) (k : Sym2 V) : Option (Msg V) :=
  match c.emb (jOf c) c.me k with
  | none => none
  | some l => if l = [] then ownAgg c inp k else rcv Bw μ c H c.me l.reverse

/-- the outputs of `aggDown`: a node outputs the multiset of the values received over its key
edges -/
noncomputable def downOut (Bw μ : ℕ) (c : NCtx V) (inp : Agent V → Option Mem) (hist : Hist V) :
    Agent V → Option Mem
  | .inl _ => some ⟨Multiset (Msg V),
      (univ : Finset (Sym2 V)).val.filterMap (downVal Bw μ c inp (hget hist))⟩
  | .inr _ => some ⟨Multiset (Msg V), 0⟩

/-- **The `aggDown` algorithm** (it does not use `ν`). -/
noncomputable def downAlg (Bw : ℕ) (_ν μ : ℕ) : CAlg := fun _V _ _ =>
  sfProto Bw μ true downOrig (downOut Bw μ)

section Down

variable {N : WNet V} {E : Overlays V} {j sz : ℕ} {Pt : Finset V}
  {x : Agent V → V → Option (Msg V)}

lemma aggIn_io (a : V) (C : Finset (Sym2 V)) :
    aggIn (inpAt (ioInst N E j sz Pt) (inOf x) a) C =
      if ioHost E j Pt (.inr C) = some a then some (x (.inr C)) else none := by
  by_cases h : ioHost E j Pt (.inr C) = some a
  · rw [ite_eq_left h]
    have h' : (ioInst N E j sz Pt).host (.inr C) = some a := h
    simp [aggIn, inpAt, h', inOf]
  · rw [ite_eq_right h]
    have h' : ¬ (ioInst N E j sz Pt).host (.inr C) = some a := h
    simp [aggIn, inpAt, h']

lemma bind_ite_isSome {C : Finset (Sym2 V)} {a u : V}
    (h : ((if ioHost E j Pt (.inr C) = some a then some (x (.inr C)) else none).bind
      (fun f => f u)).isSome) :
    ioHost E j Pt (.inr C) = some a ∧ (x (.inr C) u).isSome := by
  by_cases hh : ioHost E j Pt (.inr C) = some a
  · rw [ite_eq_left hh] at h; exact ⟨hh, by simpa using h⟩
  · rw [ite_eq_right hh] at h; simp at h

end Down

/-- **`aggDown` in the CONGEST semantics.** -/
theorem aggDown_congest : AggDownC := by
  intro c Bw
  refine ⟨Bw + 3, 0, 0, downAlg Bw, ?_⟩
  intro V _ _ N ν _ hν2 E j sz Pt S μ x hE hj hsz hfp hxS hsmall
  classical
  let val : V → Finset (Sym2 V) → Option (Msg V) := fun u C => x (.inr C) u
  have hS : ∀ u C, Act E val u C → u ∈ S := fun u C h =>
    (hxS C h.1 u (Option.isSome_iff_ne_none.1 h.2.2)).1
  show ImplI (sfProto Bw μ true downOrig (downOut Bw μ)) (ioInst N E j sz Pt) (inOf x)
    (postOf (ioInst N E j sz Pt) _) _ _
  refine ImplI.of_forall _ _ (by unfold whp; simp) (fun ω => ?_)
  simp only [pow_zero, mul_one]
  let z : Agent V → Multiset (Msg V) := fun g => match g with
    | .inl v => (clustersOf E.cl v).val.filterMap (fun C => x (.inr C) v)
    | .inr _ => 0
  refine sf_succ Bw μ true downOrig (downOut Bw μ) N E j sz Pt S (inOf x) val hE hj hsz hfp hS
    ?_ (fun g => ⟨Multiset (Msg V), z g⟩) ?_ ⟨z, fun g _ => rfl, fun v => rfl⟩ ω
  · -- the origin rule produces the packets of hop `0`
    intro a ha b u
    have hc := ctxOK_ioInst N E j sz Pt a
    unfold downOrig
    rw [hc.me, hc.j, hc.emb]
    -- a candidate cluster is the cluster of the packet
    have hcand : ∀ C', ((aggIn (inpAt (ioInst N E j sz Pt) (inOf x) a) C').bind
        (fun f => f u)).isSome → u ∈ nodes C' → ∀ l, ioEmb E a j u (srcPort C' u).2 = some l →
        C' ∈ E.cl ∧ ioHost E j Pt (.inr C') = some a ∧ (x (.inr C') u).isSome ∧
          l = E.path j u C' ∧ pEnd E j u C' = a := by
      intro C' h1 h2 l hl
      rw [aggIn_io] at h1
      obtain ⟨hh1, hx⟩ := bind_ite_isSome h1
      obtain ⟨hagg, -⟩ := ioHost_inr_some hh1
      have hC' := mem_of_aggHost hE hagg
      refine ⟨hC', hh1, hx, emb_key hE hC' h2 hl, ?_⟩
      rw [aggHost_eq hE hj hC' h2] at hagg
      exact Option.some.inj hagg
    by_cases hu : u ∈ srcs E j true val a b 0
    · rw [ite_eq_left hu]
      have hu' := hu
      simp only [srcs, mem_filter, mem_univ, true_and] at hu'
      obtain ⟨C, hA, hW, hv⟩ := hu'
      have hC : C ∈ E.cl := hA.1
      have huC : u ∈ nodes C := hA.2.1
      have hx : (val u C).isSome := hA.2.2
      have hend : pEnd E j u C = a := by simpa [pkS] using hv
      have hhost : ioHost E j Pt (.inr C) = some a := (ioHost_inr_iff hE hj hC huC).2 ⟨hend, ha⟩
      have hemb : ioEmb E a j u (srcPort C u).2 = some (E.path j u C) := by
        have := emb_pk true hE hj hC huC (Nat.zero_le _)
        rwa [wv_zero, pkS, ite_eq_left rfl, hend] at this
      have hex : ∃ C', ((aggIn (inpAt (ioInst N E j sz Pt) (inOf x) a) C').bind
          (fun f => f u)).isSome ∧ u ∈ nodes C' ∧ ∃ l, ioEmb E a j u (srcPort C' u).2 = some l ∧
            l.reverse[0]? = some s(a, b) :=
        ⟨C, by rw [aggIn_io, ite_eq_left hhost]; simpa [val] using hx, huC, E.path j u C, hemb, hW⟩
      rw [dite_eq_left hex]
      obtain ⟨h1, h2, l, hl, hl0⟩ := hex.choose_spec
      obtain ⟨hC1, -, -, hl', -⟩ := hcand _ h1 h2 l hl
      have he1 : s(a, b) ∈ hex.choose := hE.local_ j u _ _ (by
        rw [← hl']; exact List.mem_reverse.1 (List.mem_of_getElem? hl0))
      have he2 : s(a, b) ∈ C := pk_edge true hE (List.mem_of_getElem? hW)
      have heq : hex.choose = C := clu_eq hE hC1 hC he1 he2
      rw [heq, aggIn_io, ite_eq_left hhost]
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hx
      have hm' : x (.inr C) u = some m := hm
      simp [pay, val, clOf_eq hE hC he2, hm']
    · rw [ite_eq_right hu, dite_eq_right]
      rintro ⟨C, h1, h2, l, hl, hl0⟩
      obtain ⟨hC, -, hx, hl', hend⟩ := hcand C h1 h2 l hl
      apply hu
      simp only [srcs, mem_filter, mem_univ, true_and]
      refine ⟨C, ⟨hC, h2, hx⟩, ?_, ?_⟩
      · show (E.path j u C).reverse[0]? = some s(a, b)
        rw [← hl']; exact hl0
      · simp [pkS, hend]
  · -- outputs
    intro g v hg
    cases g with
    | inr C => rfl
    | inl w =>
      have hw : w = v ∧ v ∈ Pt := by
        have hg' : ioHost E j Pt (.inl w) = some v := hg
        simp only [ioHost] at hg'
        split_ifs at hg' with hw
        cases hg'
        exact ⟨rfl, hw⟩
      obtain ⟨hwv, hvPt⟩ := hw
      rw [hwv]
      have hc := ctxOK_ioInst N E j sz Pt v
      -- the value received over the key edge of each cluster of `v`
      have hval : ∀ C ∈ clustersOf E.cl v, downVal Bw μ ((ioInst N E j sz Pt).ctx v)
          (inpAt (ioInst N E j sz Pt) (inOf x) v)
          (hget (schedHist (sfM E j true val Bw μ sz) v (E.dil * (sz * sfL Bw μ))))
          (srcPort C v).2 = x (.inr C) v := by
        intro C hC
        obtain ⟨hC, hvC⟩ := mem_filter.1 hC
        unfold downVal
        rw [hc.me, hc.j, hc.emb, ioEmb_eq_some hE.disj hC hvC (Or.inl rfl)]
        dsimp only
        by_cases hnil : E.path j v C = []
        · rw [ite_eq_left hnil]
          have hend : pEnd E j v C = v := by simp [pEnd, hnil]
          have hhost : ioHost E j Pt (.inr C) = some v :=
            (ioHost_inr_iff hE hj hC hvC).2 ⟨hend, hvPt⟩
          unfold ownAgg
          rw [hc.me]
          have hex : ∃ C', (aggIn (inpAt (ioInst N E j sz Pt) (inOf x) v) C').isSome ∧
              v ∈ nodes C' ∧ (srcPort C' v).2 = (srcPort C v).2 :=
            ⟨C, by simp [aggIn_io, hhost], hvC, rfl⟩
          rw [dite_eq_left hex]
          obtain ⟨h1, h2, h3⟩ := hex.choose_spec
          have hh1 : ioHost E j Pt (.inr hex.choose) = some v := by
            rw [aggIn_io] at h1
            by_contra hn
            rw [ite_eq_right hn] at h1
            simp at h1
          have hC1 := mem_of_aggHost hE (ioHost_inr_some hh1).1
          have heq : hex.choose = C := clu_eq hE hC1 hC (srcPort_snd_mem h2).1
            (by rw [h3]; exact (srcPort_snd_mem hvC).1)
          rw [heq, aggIn_io, ite_eq_left hhost, Option.bind_some]
        · rw [ite_eq_right hnil]
          exact rcv_sched hE hj hS hsz hC hvC hnil (d := true) (by simp [pkE]) hc
            (fun m hm => encOK_of_small hν2 (hsmall C hC v m hm)) le_rfl
      -- the key edges of the clusters of `v`
      have hinj : Set.InjOn (fun C : Finset (Sym2 V) => (srcPort C v).2) ↑(clustersOf E.cl v) := by
        intro C hC C' hC' heq
        have h1 := mem_filter.1 (mem_coe.1 hC)
        have h2 := mem_filter.1 (mem_coe.1 hC')
        have heq' : (srcPort C v).2 = (srcPort C' v).2 := heq
        exact clu_eq hE h1.1 h2.1 (srcPort_snd_mem h1.2).1
          (by rw [heq']; exact (srcPort_snd_mem h2.2).1)
      -- other edges carry nothing
      have hzero : ∀ k ∈ (univ : Finset (Sym2 V)),
          k ∉ (clustersOf E.cl v).image (fun C => (srcPort C v).2) →
          (((downVal Bw μ ((ioInst N E j sz Pt).ctx v) (inpAt (ioInst N E j sz Pt) (inOf x) v)
            (hget (schedHist (sfM E j true val Bw μ sz) v (E.dil * (sz * sfL Bw μ)))) k).toList :
              Multiset (Msg V)) = 0) := by
        intro k _ hk
        unfold downVal
        rw [hc.me, hc.j, hc.emb]
        cases hk' : ioEmb E v j v k with
        | none => rfl
        | some l =>
          exfalso
          obtain ⟨C, hC, hvC, hkC, -, -⟩ := ioEmb_spec hk'
          exact hk (mem_image.2 ⟨C, mem_filter.2 ⟨hC, hvC⟩, hkC⟩)
      simp only [downOut, z]
      refine congrArg (fun f => some (⟨Multiset (Msg V), f⟩ : Mem)) ?_
      rw [filterMap_val_eq_sum, filterMap_val_eq_sum, ← sum_subset (subset_univ _) hzero,
        sum_image hinj]
      exact sum_congr rfl (fun C hC => by simp only [hval C hC])

end APSP.Stoc.Congest
