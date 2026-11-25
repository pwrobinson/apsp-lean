import ApspStoc.Sec5EOAux

/-!
# Lemma 5.3, physical case: Eulerian orientation by cluster pairings and ring leader election

The algorithm (proof of Lemma 5.3, "Physical Nodes Only"):

1. (local, aggregators) the aggregator of every cluster `C` pairs, at every node `v`, the physical
   edges of `C` at `v`, leaving at most one left-over edge per `(v, C)`; the pairings decompose the
   physical edges of `C` into closed trails and *segments* (trails between two left-over edges); for
   every left-over end `(v, e)` it computes the other end `(x, e')` of its segment (`oend`);
2. (`aggDown`, 3 words) it sends `(e, x, e')` to `v`;
3. (local, nodes) `v` lists its segment ends (its `RingIn` data; consecutive ends are paired);
4. (`ringLE`) the rings formed by segments and node pairings are consistently oriented;
5. (`aggUp`, `≤ fov` words) `v` sends the edges of its outgoing ends to its aggregators;
6. (local, aggregators) every aggregator orients its edges consistently with the received
   directions (`colorOf`), which is possible since the two ends of every segment got opposite
   directions.

The combinatorics is in `Sec5EOAux.lean`; here we compose the primitives and account for costs.
-/

namespace APSP.Stoc

open APSP Finset

section Alg

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the physical edges of `C`, as known by its aggregator -/
def aggF (C : Finset (Sym2 V)) (inp : EOIn V) : Finset (Sym2 V) :=
  C.filter (fun e => inp.hp e = true)

/-- the data held after each step -/
abbrev EOT1 (V : Type) := EOIn V × (V → Option (Msg V))
abbrev EOT2 (V : Type) := EOT1 V × Multiset (Msg V)
abbrev EOT3 (V : Type) := EOT2 V × RingIn V
abbrev EOT4 (V : Type) := EOT3 V × List Bool
abbrev EOT5 (V : Type) := EOT4 V × Option (Msg V)
abbrev EOT6 (V : Type) := EOT5 V × (V → Option (Msg V))

/-- step 1: the aggregators compute the segment ends to be sent to the nodes -/
noncomputable def eoF1 : Agent V → (Sym2 V → ℕ) → EOIn V → (V → Option (Msg V))
  | .inl _, _, _ => fun _ => none
  | .inr C, _, inp => fun v => segMsg (aggF C inp) v

/-- step 3: the nodes form their ring data -/
noncomputable def eoF3 : Agent V → (Sym2 V → ℕ) → EOT2 V → RingIn V
  | .inl _, _, inp => ringOf inp.2
  | .inr _, _, _ => []

/-- step 5: the nodes of `S` prepare the directions of their ends for their aggregators -/
def eoF5 : Agent V → (Sym2 V → ℕ) → EOT4 V → Option (Msg V)
  | .inl _, _, inp => if inp.1.1.1.1.inS = true then some (outMsg inp.1.2 inp.2) else none
  | .inr _, _, _ => none

/-- the direction of a dart `(v, e)` read from the message of `v` -/
def dirFrom (M : V → Option (Msg V)) (p : V × Sym2 V) : Bool :=
  match M p.1 with
  | some m => decide (Word.edge p.2 ∈ m)
  | none => false

/-- step 6: the aggregators orient their edges -/
noncomputable def eoF7 : Agent V → (Sym2 V → ℕ) → EOT6 V → EOOut V
  | .inl _, _, _ => ⟨[], [], fun _ => none⟩
  | .inr C, _, inp =>
    ⟨[], [], fun e => some (headOf (aggF C inp.1.1.1.1.1.1) (dirFrom inp.2) e)⟩

end Alg

noncomputable abbrev EOL1 : LocFn := ⟨fun V => EOIn V, fun V => V → Option (Msg V), fun _ _ _ => eoF1⟩
noncomputable abbrev EOL3 : LocFn := ⟨fun V => EOT2 V, fun V => RingIn V, fun _ _ _ => eoF3⟩
abbrev EOL5 : LocFn := ⟨fun V => EOT4 V, fun V => Option (Msg V), fun _ _ _ => eoF5⟩
noncomputable abbrev EOL7 : LocFn := ⟨fun V => EOT6 V, fun V => EOOut V, fun _ _ _ => eoF7⟩

/-- The algorithm of the physical case of Lemma 5.3, from the aggregator exchanges `Ad`, `Au` and
the ring leader election `Ar`. Each building block is run by a local call that drops the data
held so far (`sndF`), which is kept for the later steps. -/
noncomputable def eoPhysAlg (T : Toolkit) (Ad Ar Au : T.Alg) : T.Alg :=
  T.seq (T.loc EOL1) (T.seq (T.call (sndF EOIn (fun V => V → Option (Msg V))) Ad)
    (T.seq (T.loc EOL3) (T.seq (T.call (sndF EOT2 RingIn) Ar)
      (T.seq (T.loc EOL5) (T.seq (T.call (sndF EOT4 (fun V => Option (Msg V))) Au)
        (T.loc EOL7))))))

/-- **Lemma 5.3**, physical nodes only. -/
theorem eo_physical (T : Toolkit) : EOPhys T := by
  intro c fov fd hov hd
  obtain ⟨Kd, kd, Kδd, Ad, hDn⟩ := T.aggDown c 0
  obtain ⟨Kr, Ar, hRg⟩ := T.ringLE
  obtain ⟨Ku, ku, Kδu, Au, hUp⟩ := T.aggUp c 0
  refine ⟨fun ν => Kd * lg ν ^ kd * 4 * (fd ν + 1) + Kr * lg ν * (fov ν + 1) * (fd ν + 1) +
      Ku * lg ν ^ ku * (fov ν + 1) * (fd ν + 1) +
      (Kd * 4 + Kr * lg ν + Ku * (fov ν + 1)) * (fov ν * fd ν + 1),
    ?_, Kδd + Kδu, fun ν => eoPhysAlg T (Ad ν 3) (Ar ν) (Au ν (fov ν)), ?_⟩
  · have hd1 := hd.add (IsPL.const 1)
    have hov1 := hov.add (IsPL.const 1)
    exact (((((IsPL.const Kd).mul (IsPL.lgpow kd)).mul (IsPL.const 4)).mul hd1).add
      ((((IsPL.const Kr).mul IsPL.lg').mul hov1).mul hd1)).add
      ((((IsPL.const Ku).mul (IsPL.lgpow ku)).mul hov1).mul hd1) |>.add
      ((((IsPL.const (Kd * 4)).add ((IsPL.const Kr).mul IsPL.lg')).add
        ((IsPL.const Ku).mul (hov.add (IsPL.const 1)))).mul ((hov.mul hd).add (IsPL.const 1)))
  intro V _ _ N ν hν hνn E X hE j sz H hj hsz hPh hWF Pt hPt
  -- the setting
  let FF : Finset (Sym2 V) → Finset (Sym2 V) := fun C => aggF C (eoInput H (.inr C))
  have hFF : ∀ C e, e ∈ FF C ↔ e ∈ C ∧ e ∈ H.Hp := by
    intro C e; simp [FF, aggF, eoInput]
  have hG : ∀ e ∈ H.Hp, e ∈ N.G.edgeFinset ∧ ∀ v ∈ e, v ∈ H.S := by
    intro e he
    have := hWF.sub he
    unfold inducedEdges at this
    exact Finset.mem_filter.1 this
  have hFam : FamOK E.cl FF H.Hp H.S := by
    refine ⟨hE.disj, hFF, fun e he => hE.valid.cover e (hG e he).1,
      fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset (hG e he).1,
      fun e he => (hG e he).2, fun v hv => ?_⟩
    have := hWF.even_p v hv
    rw [hPh.2.1 v, List.length_nil, add_zero] at this
    unfold EOInst.pdeg at this
    convert this using 2
  -- the cost profiles of the communication steps
  have main : T.Impl (eoPhysAlg T (Ad ν 3) (Ar ν) (Au ν (fov ν))) N (eoTask E j sz Pt H)
      (0 + (Prof.mk (Kd * lg ν ^ kd * (3 + 1) * (E.dil + 1) * (sz + 1))
          ((Kd * (3 + 1)) • E.rhoAgg j H.S) (Kd * (3 + 1) * E.aggLen j H.S) +
        (0 + (Prof.mk (Kr * lg ν * (E.ov + 1) * (E.dil + 1) * (sz + 1)) ((Kr * lg ν) • E.rhoAgg j H.S)
          (Kr * lg ν * E.aggLen j H.S) +
        (0 + (Prof.mk (Ku * lg ν ^ ku * (fov ν + 1) * (E.dil + 1) * (sz + 1))
          ((Ku * (fov ν + 1)) • E.rhoAgg j H.S) (Ku * (fov ν + 1) * E.aggLen j H.S) + 0))))))
      (0 + (whp Kδd c ν + (0 + (0 + (0 + (whp Kδu c ν + 0)))))) := by
    unfold eoPhysAlg
    -- step 1
    refine T.bind (T.locR EOL1 N E j sz Pt (eoInput H)) (fun y1 hy1 => ?_)
      (by (try unfold whp); positivity)
    have hy1a : ∀ C, y1 (.inr C) = fun v => segMsg (FF C) v := fun C => hy1 (.inr C)
    -- step 2
    have hD1 := hDn N ν hν hνn E j sz Pt H.S 3 y1 hE.valid hj hsz hPt
      (by
        intro C _ v hne
        rw [hy1a] at hne
        cases hl : lo (FF C) v with
        | none => exfalso; apply hne; simp [segMsg, segEnd, hl]
        | some e =>
          obtain ⟨hdd, _⟩ := lo_eq_some.1 hl
          obtain ⟨he, hv, _⟩ := mem_darts.1 hdd
          have := (hFF C e).1 he
          exact ⟨(hG e this.2).2 v hv, mem_nodes.2 ⟨e, this.1, hv⟩⟩)
      (by intro C _ v m hm; rw [hy1a] at hm; exact segMsg_small _ _ _ _ hm)
    refine T.bind (T.frameCall (eoInput H) hD1) (fun y2 hy2 => ?_) (by (try unfold whp); positivity)
    -- step 3
    refine T.bind (T.locR EOL3 N E j sz Pt (fun g => ((eoInput H g, y1 g), y2 g))) (fun y3 hy3 => ?_)
      (by (try unfold whp); positivity)
    have hy3n : ∀ v, y3 (.inl v) = ringFam E.cl FF v := by
      intro v
      rw [hy3 (.inl v)]
      show ringOf (y2 (.inl v)) = _
      rw [hy2 v]
      simp only [hy1a]
      rfl
    -- step 4
    have hR1 := hRg N ν hν hνn E j sz Pt H.S (ringFam E.cl FF) y3 hE.valid hj hFam.ringWF hsz hPt
      hy3n
    refine T.bind (T.frameCall (Γ := EOT2) (fun g => ((eoInput H g, y1 g), y2 g)) hR1)
      (fun y4 hy4 => ?_) (by (try unfold whp); positivity)
    -- step 5
    refine T.bind (T.locR EOL5 N E j sz Pt (fun g => ((((eoInput H g, y1 g), y2 g), y3 g), y4 g)))
      (fun y5 hy5 => ?_) (by (try unfold whp); positivity)
    have hy5n : ∀ v, y5 (.inl v) =
        if v ∈ H.S then some (outMsg (ringFam E.cl FF v) (y4 (.inl v))) else none := by
      intro v
      rw [hy5 (.inl v)]
      show (if decide (v ∈ H.S) = true then some (outMsg (y3 (.inl v)) (y4 (.inl v))) else none) = _
      rw [hy3n v]
      by_cases hv : v ∈ H.S <;> simp [hv]
    -- step 6
    have hU1 := hUp N ν hν hνn E j sz Pt H.S (fov ν) y5 hE.valid hj hsz hPt
      (by
        intro v hne
        rw [hy5n] at hne
        by_contra hv
        rw [if_neg hv] at hne
        exact hne rfl)
      (by
        intro v m hm
        rw [hy5n] at hm
        split_ifs at hm with hv
        cases hm
        have hlen : (ringFam E.cl FF v).length ≤ fov ν := by
          rw [hFam.length_eq]
          exact (Finset.card_filter_le _ _).trans (hE.overlap v)
        exact ⟨(outMsg_small _ _ (ν ^ 0)).1.trans hlen, (outMsg_small _ _ _).2⟩)
    refine T.bind
      (T.frameCall (Γ := EOT4) (fun g => ((((eoInput H g, y1 g), y2 g), y3 g), y4 g)) hU1)
      (fun y6 hy6 => ?_) le_rfl
    -- step 7
    refine T.weakenIO (fun y7 hy7 => ?_) (T.locR EOL7 N E j sz Pt
      (fun g => ((((((eoInput H g, y1 g), y2 g), y3 g), y4 g), y5 g), y6 g)))
    -- correctness
    let dir : Finset (Sym2 V) → V × Sym2 V → Bool := fun C => dirFrom (y6 (.inr C))
    have hdir : ∀ C ∈ E.cl, ∀ v e, (v, e) ∈ darts (FF C) → piD (FF C) (v, e) = (v, e) →
        dir C (v, e) = decide (Word.edge e ∈ outMsg (ringFam E.cl FF v) (y4 (.inl v))) := by
      intro C hC v e hdd _
      obtain ⟨he, hv, _⟩ := mem_darts.1 hdd
      have he' := (hFF C e).1 he
      have hvS : v ∈ H.S := (hG e he'.2).2 v hv
      have hvC : v ∈ nodes C := mem_nodes.2 ⟨e, he'.1, hv⟩
      simp only [dir, dirFrom, hy6 C hC v, if_pos hvC, hy5n, if_pos hvS]
    obtain ⟨o1, o2, o3⟩ := hFam.orient (fun v => y4 (.inl v)) hy4 dir hdir
    refine ⟨gHead E.cl FF dir, fun _ => [], [], o1, ?_, ?_, ?_, ?_, ?_⟩
    · intro C hC e he heC
      rw [hy7 (.inr C), ← o2 C hC e he heC]
      rfl
    · intro v _
      rw [hy7 (.inl v), hPh.2.1 v]
      exact ⟨rfl, rfl, rfl⟩
    · rw [hPh.2.2]; rfl
    · intro v _
      simp only [List.count_nil, add_zero]
      convert o3 v using 2
    · intro i hi
      rw [hPh.1] at hi
      exact absurd hi (Nat.not_lt_zero i)
  refine T.mono main ?_ ?_
  · have hal := aggLen_le hE j H.S
    unfold szProf
    refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
    · simp only [Prof.rounds_add, Prof.rounds_mk, zero_add, add_zero]
      have h1 : E.dil + 1 ≤ fd ν + 1 := Nat.add_le_add_right (dil_le_of_props hE) 1
      have h2 : E.ov + 1 ≤ fov ν + 1 := Nat.add_le_add_right (ov_le_of_props hE) 1
      set L := lg ν; set o := fov ν; set dd := fd ν
      have hA : Kd * L ^ kd * (3 + 1) * (E.dil + 1) * (sz + 1) ≤
          Kd * L ^ kd * 4 * (dd + 1) * (sz + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      have hB : Kr * L * (E.ov + 1) * (E.dil + 1) * (sz + 1) ≤
          Kr * L * (o + 1) * (dd + 1) * (sz + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h1)
      have hC : Ku * L ^ ku * (o + 1) * (E.dil + 1) * (sz + 1) ≤
          Ku * L ^ ku * (o + 1) * (dd + 1) * (sz + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      calc _ ≤ Kd * L ^ kd * 4 * (dd + 1) * (sz + 1) + (Kr * L * (o + 1) * (dd + 1) * (sz + 1) +
            Ku * L ^ ku * (o + 1) * (dd + 1) * (sz + 1)) := add_le_add hA (add_le_add hB hC)
        _ = (Kd * L ^ kd * 4 * (dd + 1) + Kr * L * (o + 1) * (dd + 1) +
            Ku * L ^ ku * (o + 1) * (dd + 1)) * (sz + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    · simp only [Prof.load_add, Prof.load_mk, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, zero_add, add_zero]
      have hr := rhoAgg_le_rho (G := N.G) E j H.S e
      set r := E.rho N.G j H.S e; set ra := E.rhoAgg j H.S e
      set L := lg ν; set o := fov ν; set dd := fd ν
      calc _ = (Kd * 4 + Kr * L + Ku * (o + 1)) * ra := by ring
        _ ≤ (Kd * 4 + Kr * L + Ku * (o + 1)) * r := Nat.mul_le_mul_left _ hr
        _ ≤ (Kd * 4 + Kr * L + Ku * (o + 1)) * (o * dd + 1) * r :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    · simp only [Prof.msgs_add, Prof.msgs_mk, zero_add, add_zero]
      set s := H.S.card; set L := lg ν; set o := fov ν; set dd := fd ν
      set al := E.aggLen j H.S
      calc Kd * (3 + 1) * al + (Kr * L * al + Ku * (o + 1) * al) =
            (Kd * 4 + Kr * L + Ku * (o + 1)) * al := by ring
        _ ≤ (Kd * 4 + Kr * L + Ku * (o + 1)) * (o * dd * s) := Nat.mul_le_mul_left _ hal
        _ ≤ (Kd * 4 + Kr * L + Ku * (o + 1)) * (o * dd + 1) * (s + 1) := by
          rw [mul_assoc (Kd * 4 + Kr * L + Ku * (o + 1))]; apply Nat.mul_le_mul_left; nlinarith
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  · simp only [zero_add, add_zero]
    rw [whp_add]

end APSP.Stoc
