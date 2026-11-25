import ApspStoc.Congest.RingLECost

/-!
# Ring orientation in the CONGEST semantics (`ringLE_congest`)

`ringLE_congest : RingLEC` is the concrete version of the toolkit field `ringLE`, with the
algorithm `ringAlg` (`RingLELocal.lean`) and the constant `K = 336`.

## The protocol
A deterministic, synchronous version of the Hirschberg–Sinclair election on the rings of segment
ends, following the mathematical model of `RingComb.lean`:
* Phases `i = 0, …, Φ` (`Φ = ⌊log₂ B⌋ + 1`, `B = ov · min(sz, n)` a public bound on the number of
  elements). In phase `i` every *active candidate* (an element whose ring is not yet decided)
  sends a probe out of each of its two ends; probes are forwarded for `2^i` links or until they
  return to their originator. A candidate survives the phase iff no probe with a larger ID arrived
  at it; a candidate is decided once its own probe returned.
* A phase has `2^i` *link steps*; in a link step every probe in flight crosses one segment: up the
  embedded path of the departure node in the segment's cluster to the host of the cluster's
  aggregator (`D = dil + 1` hops), then down the partner's path (`D` hops). The departure node
  finds the path from its cluster slices (the segment edge is incident to it, `RingWF.inc`); the
  host turns the packet to the partner's path (it knows its cluster); the partner finds its
  arrival end from the link's edges carried in the packet (`segPartner_eq`).
* A hop has `slots B i = ⌊4B/2^i⌋ + 1` slots of `7` rounds (a packet has `7` words): every node
  sends its held packets in the order of their origins, one per slot. By `card_flightA_mul`
  (`RingComb`), there are fewer probes in flight than slots.
* At the end every end outputs the direction induced by the largest probe that crossed it; by
  `max_probe_crosses`, `probe_le_ringMax` and `dir_of_max_probe` this is `RingComb.dir`, so the
  outputs form `ringDir r`, which satisfies `RingSpec` (`ringDir_spec`).

## The proof
The protocol is a full-information protocol (`histP`). The global schedule `RS.M` is defined from
the election of `RingComb` (`RS.held`: the packets held by every node at every hop); `RS.sendL_eq`
shows that every node, fed with the schedule, sends exactly the scheduled messages, so the run
follows the schedule (`succ_histP`), whose messages only use instance edges (`RS.M_adj`) and valid
words (`RS.M_ok`). The costs are read off the schedule (`RingLECost.lean`):
* rounds `tEnd ≤ (Φ+1) · 14 D (6B + 2) ≤ 336 · lg n · (ov+1)(dil+1)(sz+1)`;
* messages over an edge `e` at most `28 (Φ+1) · rhoAgg j S e`, in total at most
  `28 (Φ+1) · aggLen j S`, with `28 (Φ+1) ≤ 84 lg n`.

## Contract repair
`RingWF` gained the field `inc` (the own edge of a segment end is incident to the node: segment
ends are darts). Without it a node cannot determine the cluster, hence the embedded path, of a
segment end from its local knowledge (its cluster slices `C ∩ inc(v)`); the ring data constructed
in the proof of Lemma 5.3 (`Sec5EOAux.ringWF`) satisfies it.
-/

namespace APSP.Stoc.Congest

open APSP Finset APSP.Stoc.RingComb RingLE

/-- The toolkit field `ringLE` in the concrete CONGEST semantics. -/
def RingLEC : Prop :=
  ∃ (K : ℕ) (A : ℕ → CAlg), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V)
    (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (r : V → RingIn V)
    (x : Agent V → RingIn V), EmbValid N.G E → j < Fintype.card V → RingWF E.cl S r →
    S.card ≤ sz → footprint E j S ⊆ Pt → (∀ v, x (.inl v) = r v) →
    CImplT (A ν) N (.io E j sz Pt (RingIn V) (List Bool) x
      (fun y => RingSpec r (fun v => y (.inl v))))
      (Prof.mk (K * lg ν * (E.ov + 1) * (E.dil + 1) * (sz + 1)) ((K * lg ν) • E.rhoAgg j S)
        (K * lg ν * E.aggLen j S)) 0

namespace RingLE

variable {V : Type} [Fintype V] [DecidableEq V]

lemma myRing_inp {Z : RS V} {x : Agent V → RingIn V} (hx : ∀ v, x (.inl v) = Z.r v) {u : V}
    (hu : u ∈ Z.Pt) : myRing (inpAt Z.I (inOf x) u) u = Z.r u := by
  have h : inpAt Z.I (inOf x) u (.inl u) = some ⟨RingIn V, x (.inl u)⟩ := by
    simp [inpAt, RS.I, ioInst, ioHost, inOf, hu]
  unfold myRing
  rw [h]
  simp [hx u]

omit [Fintype V] in
lemma countP_eq_count (l : List (Sym2 V)) (e : Sym2 V) :
    l.countP (fun e' => decide (e' = e)) = l.count e := by
  rw [List.count_eq_countP]
  congr 1

omit [Fintype V] [DecidableEq V] in
lemma countP_true (l : List (Sym2 V)) : l.countP (fun _ => decide True) = l.length := by
  simp

end RingLE

/-- **Ring orientation** in the concrete CONGEST semantics. -/
theorem ringLE_congest : RingLEC := by
  refine ⟨336, ringAlg, ?_⟩
  intro V _ _ N ν hν hνn E j sz Pt S r x hE hj hWF hsz hPt hx
  set Z : RS V := ⟨N, E, j, sz, Pt, S, r⟩ with hZdef
  have hZ : Z.OK := ⟨hE, hj, hWF, hsz, hPt⟩
  have hνeq : ν = Fintype.card V := le_antisymm hνn hν
  subst hνeq
  show ImplI (ringProto V) Z.I (inOf x) _ _ 0
  refine ImplI.of_forall _ _ le_rfl (fun ω => ?_)
  have hT : ∀ v, tEnd (hD (Z.I.ctx v)) (bnd (Z.I.ctx v)) = tEnd Z.D Z.B := fun v => rfl
  have hM : ∀ s < tEnd Z.D Z.B, ∀ u v,
      (Z.I.part u → sendL (Z.I.ctx u) (myRing (inpAt Z.I (inOf x) u) (Z.I.ctx u).me)
        (hget (schedHist Z.M u s)) (schedHist Z.M u s).length v = Z.M u v s) ∧
      (¬ Z.I.G.Adj u v → Z.M u v s = none) ∧
      ∀ w, Z.M u v s = some w → WordOK (Fintype.card V) w := by
    intro s _ u v
    refine ⟨fun hu => ?_, fun hadj => ?_, fun w hw => RS.M_ok hZ hw⟩
    · rw [RS.me_ctx, myRing_inp hx hu, length_schedHist]
      exact RS.sendL_eq hZ u s v
    · by_contra hne
      exact hadj (RS.M_adj hZ (Option.ne_none_iff_isSome.1 hne))
  -- the outputs
  let z : Agent V → List Bool := fun g => match g with
    | .inl v => ringDir r v
    | .inr _ => []
  have hB := RS.B_le hZ
  have hphi := RS.phi_le hB
  refine succ_histP (F := fun c inp h v => sendL c (myRing inp c.me) (hget h) h.length v)
    (Tf := fun c => tEnd (hD c) (bnd c))
    (O := fun c inp h g => some ⟨List Bool,
      if g = .inl c.me then outL c (myRing inp c.me) (hget h) else []⟩)
    (I := Z.I) (x := inOf x) (ω := ω) hT Z.M hM
    (Q := postOf Z.I (fun y : Agent V → List Bool => RingSpec r (fun v => y (.inl v))))
    ?_ ?_ ?_ (fun g => ⟨List Bool, z g⟩) ?_ ⟨z, fun g _ => rfl, ringDir_spec hWF⟩
  · -- rounds
    show tEnd Z.D Z.B ≤ 336 * lg (Fintype.card V) * (E.ov + 1) * (E.dil + 1) * (sz + 1)
    have h1 := RS.tEnd_le' Z.D Z.B
    have h2 : Z.B ≤ E.ov * sz := Nat.mul_le_mul_left _ (min_le_left _ _)
    have h3 : 6 * Z.B + 2 ≤ 8 * ((E.ov + 1) * (sz + 1)) := by nlinarith
    have hD : Z.D = E.dil + 1 := rfl
    calc tEnd Z.D Z.B ≤ (phiOf Z.B + 1) * (14 * Z.D * (6 * Z.B + 2)) := h1
      _ ≤ (3 * lg (Fintype.card V)) * (14 * Z.D * (8 * ((E.ov + 1) * (sz + 1)))) :=
          Nat.mul_le_mul hphi (Nat.mul_le_mul_left _ h3)
      _ = 336 * lg (Fintype.card V) * (E.ov + 1) * (E.dil + 1) * (sz + 1) := by rw [hD]; ring
  · -- messages
    have h := RS.sends_le hZ (fun _ => True)
    have hu : Z.useP (fun _ => True) = E.aggLen j S := by
      unfold RS.useP Overlays.aggLen
      simp only [countP_true]
      rfl
    rw [hu] at h
    simp only [Finset.filter_true] at h
    show _ ≤ 336 * lg (Fintype.card V) * E.aggLen j S
    calc _ ≤ 28 * (phiOf Z.B + 1) * E.aggLen j S := h
      _ ≤ 28 * (3 * lg (Fintype.card V)) * E.aggLen j S :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hphi)
      _ ≤ 336 * lg (Fintype.card V) * E.aggLen j S := by
          apply Nat.mul_le_mul_right; nlinarith
  · -- load
    intro e
    have h := RS.sends_le hZ (fun e' => e' = e)
    have hu : Z.useP (fun e' => e' = e) = E.rhoAgg j S e := by
      unfold RS.useP Overlays.rhoAgg
      simp only [countP_eq_count]
      rfl
    rw [hu] at h
    show _ ≤ ((336 * lg (Fintype.card V)) • E.rhoAgg j S) e
    rw [Pi.smul_apply, smul_eq_mul]
    calc _ ≤ 28 * (phiOf Z.B + 1) * E.rhoAgg j S e := h
      _ ≤ 28 * (3 * lg (Fintype.card V)) * E.rhoAgg j S e :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hphi)
      _ ≤ 336 * lg (Fintype.card V) * E.rhoAgg j S e := by
          apply Nat.mul_le_mul_right; nlinarith
  · -- the outputs
    intro g v hg
    have hH : ∀ t < tEnd Z.D Z.B, ∀ w, hget (schedHist Z.M v (tEnd Z.D Z.B)) t w = Z.M w v t :=
      fun t ht w => hget_schedHist Z.M v ht w
    have hv : v ∈ Pt := Z.I.host_part g v hg
    show some (⟨List Bool, if g = .inl (Z.I.ctx v).me then outL (Z.I.ctx v)
      (myRing (inpAt Z.I (inOf x) v) (Z.I.ctx v).me) (hget (schedHist Z.M v (tEnd Z.D Z.B)))
      else []⟩ : Mem) = some (⟨List Bool, z g⟩ : Mem)
    rw [RS.me_ctx, myRing_inp hx hv]
    cases g with
    | inl w =>
      have hw : w = v := by
        have hg' : ioHost E j Pt (.inl w) = some v := hg
        by_cases hwP : w ∈ Pt
        · simp only [ioHost, hwP, ite_true, Option.some.injEq] at hg'
          exact hg'
        · simp [ioHost, hwP] at hg'
      subst hw
      rw [ite_eq_left rfl, RS.outL_eq hZ hH]
    | inr C =>
      rw [ite_eq_right (by simp)]

end APSP.Stoc.Congest
