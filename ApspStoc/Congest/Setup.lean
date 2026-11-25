import ApspStoc.Congest.SetupRun

/-!
# Cluster setup in CONGEST

**Theorem** (`clusterSetup_congest`, the toolkit field `clusterSetup`). In a `1/φinv`-expander
cluster `C` with `φinv ≤ Kφ · lg^kφ ν`, the protocol `setupProto V D`, with the public diameter
bound `D = diamBound (Kφ · lg^kφ ν) (ν²) = O(lg^(kφ+1) ν)`, elects a leader `ℓ` (the node of `C` of
largest index), builds a BFS tree of `C` rooted at `ℓ`, and lets every node of `C` learn `ℓ`, its
parent, the (ID, degree) pairs of all nodes of `C`, and the ports `portsA C` of the aggregator set
`A(C)` (`SetupSpec`). The phases (`SetupProto.lean`): F (flooding the maximum index: leader and BFS
parents), C (counting `n_C`), B (broadcasting `n_C`), G (gossip of the degree table on the tree),
A (every node computes `A(C)` from the table, `aggSet_eq_aggT`), H (gossip of the ports of the
nodes of `A(C)` on the tree, fewer than `2n_C` ports of two words each). All nodes of `C` halt in
round `tH D n_C = 3D + 2 + 2D · 2n_C + 2D · 4n_C = O(lg^(kφ+1) ν · n_C)`, after at most
`(3D + 2) · 2|C| + (2D · 2n_C + 2D · 4n_C) · 2n_C = O(lg^(kφ+1) ν · n_C²)` messages, with at most
two messages per round over each edge of `C` and none over other edges; every node sends only to
its neighbours in `C` (proper sends). The protocol is deterministic.

The protocol is defined in `SetupProto.lean`, the graph facts are in `SetupTree.lean`, and the run
is described phase by phase in `SetupRun.lean`.
-/

namespace APSP.Stoc.Congest

open APSP Finset SimpleGraph

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the halting round -/
def setupT (C : Finset (Sym2 V)) (D : ℕ) : ℕ := tH D (nodes C).card

/-- a message is sent only if the protocol sends a word -/
lemma send_isSome_of_msg {D : ℕ} {I : Inst V} {σ : V → SetupSt V} {u v : V}
    (h : (msg (setupProto V D) I σ u v).isSome) : (suSend D (σ u) v).isSome := by
  classical
  by_contra hs
  have hs' : (setupProto V D).send (I.ctx u) (σ u) v = none := by
    show suSendG D (I.ctx u) (σ u) v = none
    cases hg : suSendG D (I.ctx u) (σ u) v with
    | none => rfl
    | some w => exact absurd (suSendG_isSome (D := D) (c := I.ctx u) (s := σ u) (u := v)
        (by rw [hg]; rfl)).2 hs
  unfold msg at h
  rw [hs'] at h
  split_ifs at h <;> simp at h

/-- **Proper sends**: a node sends only to its neighbours in `C`. -/
lemma properUpTo_setup {N : WNet V} {C : Finset (Sym2 V)} {D : ℕ} (hCG : C ⊆ N.G.edgeFinset)
    (x : Agent V → Mem) (ω : V → Unit) (t : ℕ) :
    ProperUpTo (setupProto V D) (clInst0 N C) x ω t := by
  intro s _ u _ _ v hv
  exact (clInst0_adj N C hCG).2 ((suNb_clInst0 N C hCG).1 (suSendG_isSome hv).1)

/-- connectivity in the graph of a cluster gives connectivity along edges of `C` -/
lemma eReach_of_reachable {C : Finset (Sym2 V)} {u v : V} (h : (clGraph C).Reachable u v) :
    EReach C u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons hadj _ ih => exact Relation.ReflTransGen.head hadj.2 ih

section Final

variable {N : WNet V} {C : Finset (Sym2 V)} {D : ℕ} {ℓ : V}
  (hCG : C ⊆ N.G.edgeFinset) (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C)
  (hmax : ∀ u ∈ nodes C, suIdx u ≤ suIdx ℓ) (x : Agent V → Mem) (ω : V → Unit)

/-- the ports of `A(C)` fit in a window of phase H -/
lemma portsA_card_lt {N : WNet V} {C : Finset (Sym2 V)} (hCG : C ⊆ N.G.edgeFinset) {ℓ : V}
    (hℓ : ℓ ∈ nodes C) : (portsA C).card < 2 * (nodes C).card := by
  obtain ⟨e, he, _⟩ := mem_nodes.1 hℓ
  exact (card_portsA_bounds (noLoops_of_sub N C hCG) ⟨e, he⟩).2

include hCG hd hℓ hmax in
lemma out_none_before : ∀ s < setupT C D, ∀ v ∈ nodes C,
    suOut D (st (setupProto V D) (clInst0 N C) x ω s v) = none := by
  intro s hs v hv
  unfold setupT tH at hs
  by_cases h1 : s ≤ D
  · rw [runF hCG x ω s h1 v hv]
    exact suOut_none_lt (not_mem_single_zero hv) (by show s < _; omega)
  by_cases h2 : s < 2 * D + 1
  · obtain ⟨j, rfl⟩ : ∃ j, s = D + j := ⟨s - D, by omega⟩
    rw [runC hCG hd hℓ hmax x ω j (by omega) v hv]
    exact suOut_none_lt (not_mem_single_zero hv) (by show D + j < _; omega)
  by_cases h3 : s < 3 * D + 1
  · obtain ⟨j, rfl⟩ : ∃ j, s = 2 * D + 1 + j := ⟨s - (2 * D + 1), by omega⟩
    rw [runB hCG hd hℓ hmax x ω j (by omega) v hv]
    exact suOut_none_lt (not_mem_single_zero hv) (by show 2 * D + 1 + j < _; omega)
  by_cases h4 : s < tG D (nodes C).card
  · obtain ⟨i, rfl⟩ : ∃ i, s = 3 * D + 1 + i := ⟨s - (3 * D + 1), by omega⟩
    have hi : i < 2 * D * (2 * (nodes C).card) := by unfold tG at h4; omega
    rw [runG_at hCG hd hℓ hmax x ω hi v hv]
    apply suOut_none (not_mem_Sg_zero hv)
    show 3 * D + 1 + i / (2 * (nodes C).card) * (2 * (nodes C).card) + i % (2 * (nodes C).card) <
      tH D (nodes C).card
    have := Nat.div_add_mod' i (2 * (nodes C).card)
    unfold tH tG
    omega
  by_cases h5 : s = tG D (nodes C).card
  · subst h5
    unfold tG
    rw [runG hCG hd hℓ hmax x ω (2 * D) le_rfl v hv]
    apply suOut_none (not_mem_Sg_zero hv)
    show 3 * D + 1 + 2 * D * (2 * (nodes C).card) + 0 < tH D (nodes C).card
    unfold tH tG
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, s = tG D (nodes C).card + 1 + i :=
      ⟨s - (tG D (nodes C).card + 1), by omega⟩
    have hi : i < 2 * D * (4 * (nodes C).card) := by omega
    rw [runH_at hCG hd hℓ hmax x ω (portsA_card_lt hCG hℓ) hi v hv]
    apply suOut_none (not_mem_truePairs_zero)
    show tG D (nodes C).card + 1 + i / (4 * (nodes C).card) * (4 * (nodes C).card) +
      i % (4 * (nodes C).card) < tH D (nodes C).card
    have := Nat.div_add_mod' i (4 * (nodes C).card)
    unfold tH
    omega

include hCG hd hℓ hmax in
lemma st_setupT {v : V} (hv : v ∈ nodes C) :
    st (setupProto V D) (clInst0 N C) x ω (setupT C D) v = EH C D ℓ (2 * D) 0 v :=
  runH hCG hd hℓ hmax x ω (portsA_card_lt hCG hℓ) (2 * D) le_rfl v hv

lemma suOut_EH_last {v : V} :
    suOut D (EH C D ℓ (2 * D) 0 v) = some (fun _ => some ⟨SetupOut V,
      ((suDec (suIdx ℓ)).getD v, parOf C ℓ v, truePairs C, Pg C ℓ (2 * D) v)⟩) := by
  unfold suOut
  rw [ite_eq_left (Or.inr (by
    show tH D (nodes C).card ≤ tG D (nodes C).card + 1 + 2 * D * (4 * (nodes C).card) + 0
    unfold tH; omega))]
  rfl

include hCG hd hℓ hmax in
/-- **Simultaneous halting** at round `setupT C D`. -/
lemma haltsAt_setup :
    HaltsAt (setupProto V D) (clInst0 N C) x ω (setupT C D) := by
  refine ⟨fun v hv => ?_, fun s hs v hv => out_none_before hCG hd hℓ hmax x ω s hs v hv⟩
  show (suOut D _).isSome
  rw [st_setupT hCG hd hℓ hmax x ω hv, suOut_EH_last]
  rfl

include hCG hd hℓ hmax in
/-- **The outputs.** -/
lemma outAt_setupT {v : V} (hv : v ∈ nodes C) :
    outAt (setupProto V D) (clInst0 N C) x ω (setupT C D) (.inl v) =
      some ⟨SetupOut V, (ℓ, parOf C ℓ v, truePairs C, portsA C)⟩ := by
  have hh : (clInst0 N C).host (.inl v) = some v := by
    simp [clInst0, clInstP, clHost, hv]
  unfold outAt
  rw [hh]
  show (suOut D (st (setupProto V D) (clInst0 N C) x ω (setupT C D) v)).bind _ = _
  rw [st_setupT hCG hd hℓ hmax x ω hv, suOut_EH_last, Option.bind_some]
  show some (⟨SetupOut V, ((suDec (suIdx ℓ)).getD v, parOf C ℓ v, truePairs C,
    Pg C ℓ (2 * D) v)⟩ : Mem) = _
  rw [suDec_suIdx, Pg_full hd hℓ hv]
  rfl

/-! ### Messages -/

include hCG hd hℓ hmax in
/-- in phase G, messages travel along tree edges only -/
lemma sentSet_G_sub {i : ℕ} (hi : i < 2 * D * (2 * (nodes C).card)) :
    sentSet (setupProto V D) (clInst0 N C) (st (setupProto V D) (clInst0 N C) x ω (3 * D + 1 + i)) ⊆
      univ.filter (fun uv : V × V => uv.1 ∈ nodes C ∧ tnb C ℓ uv.1 uv.2) := by
  classical
  intro uv huv
  have hadj := mem_sentSet_setup hCG huv
  have hu := mem_nodes_of_adj hadj
  have hmsg : (msg (setupProto V D) (clInst0 N C)
      (st (setupProto V D) (clInst0 N C) x ω (3 * D + 1 + i)) uv.1 uv.2).isSome := by
    unfold sentSet at huv
    exact (mem_filter.1 huv).2
  have hn : 0 < (nodes C).card := card_pos.2 ⟨ℓ, hℓ⟩
  have hs := send_isSome_of_msg hmsg
  have hk : i / (2 * (nodes C).card) < 2 * D :=
    Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi)
  rw [runG_at hCG hd hℓ hmax x ω hi _ hu, suSend_EG hk (Nat.mod_lt _ (by omega))] at hs
  rw [mem_filter]
  refine ⟨mem_univ _, hu, ?_⟩
  split_ifs at hs with hc
  · rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (latC_ne_zero_iff.1 hc)
  · simp at hs

include hCG hd hℓ hmax in
/-- in phase H, messages travel along tree edges only -/
lemma sentSet_H_sub {i : ℕ} (hi : i < 2 * D * (4 * (nodes C).card)) :
    sentSet (setupProto V D) (clInst0 N C)
        (st (setupProto V D) (clInst0 N C) x ω (tG D (nodes C).card + 1 + i)) ⊆
      univ.filter (fun uv : V × V => uv.1 ∈ nodes C ∧ tnb C ℓ uv.1 uv.2) := by
  classical
  intro uv huv
  have hadj := mem_sentSet_setup hCG huv
  have hu := mem_nodes_of_adj hadj
  have hmsg : (msg (setupProto V D) (clInst0 N C)
      (st (setupProto V D) (clInst0 N C) x ω (tG D (nodes C).card + 1 + i)) uv.1 uv.2).isSome := by
    unfold sentSet at huv
    exact (mem_filter.1 huv).2
  have hn : 0 < (nodes C).card := card_pos.2 ⟨ℓ, hℓ⟩
  have hs := send_isSome_of_msg hmsg
  rw [runH_at hCG hd hℓ hmax x ω (portsA_card_lt hCG hℓ) hi _ hu,
    suSend_EH (Nat.mod_lt _ (by omega))] at hs
  rw [mem_filter]
  refine ⟨mem_univ _, hu, ?_⟩
  split_ifs at hs with hc
  · rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (latC_ne_zero_iff.1 hc)
  · simp at hs

lemma setup_card_treePairs :
    (univ.filter (fun uv : V × V => uv.1 ∈ nodes C ∧ tnb C ℓ uv.1 uv.2)).card ≤
      2 * (nodes C).card := by
  set A := univ.filter (fun uv : V × V => uv.1 ∈ nodes C ∧ parOf C ℓ uv.1 = some uv.2)
  set B := univ.filter (fun uv : V × V => uv.2 ∈ nodes C ∧ parOf C ℓ uv.2 = some uv.1)
  have hA : A.card ≤ (nodes C).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro uv huv
      simp only [A, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv
      exact mem_coe.2 huv.1
    · intro a ha b hb hab
      simp only [A, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have h2 : some a.2 = some b.2 := by rw [← ha.2, ← hb.2, hab]
      exact Prod.ext hab (Option.some.inj h2)
  have hB : B.card ≤ (nodes C).card := by
    apply card_le_card_of_injOn Prod.snd
    · intro uv huv
      simp only [B, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv
      exact mem_coe.2 huv.1
    · intro a ha b hb hab
      simp only [B, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have h1 : some a.1 = some b.1 := by rw [← ha.2, ← hb.2, hab]
      exact Prod.ext (Option.some.inj h1) hab
  have hsub : univ.filter (fun uv : V × V => uv.1 ∈ nodes C ∧ tnb C ℓ uv.1 uv.2) ⊆ A ∪ B := by
    intro uv huv
    rw [mem_filter] at huv
    rw [mem_union]
    rcases huv.2.2 with h | h
    · exact Or.inl (mem_filter.2 ⟨mem_univ _, huv.2.1, h⟩)
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, h⟩)
  calc _ ≤ (A ∪ B).card := card_le_card hsub
    _ ≤ A.card + B.card := card_union_le _ _
    _ ≤ _ := by omega

include hCG hd hℓ hmax in
/-- **Messages.** -/
lemma msgsUpTo_setup_le :
    msgsUpTo (setupProto V D) (clInst0 N C) x ω (setupT C D) ≤
      (3 * D + 1) * (2 * C.card) + 2 * D * (2 * (nodes C).card) * (2 * (nodes C).card) +
        2 * C.card + 2 * D * (4 * (nodes C).card) * (2 * (nodes C).card) := by
  unfold msgsUpTo setupT tH tG
  rw [sum_range_add, sum_range_add, sum_range_add]
  apply add_le_add
  apply add_le_add
  apply add_le_add
  · calc _ ≤ ∑ _s ∈ range (3 * D + 1), 2 * C.card := sum_le_sum (fun s _ => card_sentSet_le hCG _)
      _ = _ := by simp
  · calc _ ≤ ∑ _i ∈ range (2 * D * (2 * (nodes C).card)), 2 * (nodes C).card :=
          sum_le_sum (fun i hi => (card_le_card
            (sentSet_G_sub hCG hd hℓ hmax x ω (mem_range.1 hi))).trans setup_card_treePairs)
      _ = _ := by simp
  · calc _ ≤ ∑ _s ∈ range 1, 2 * C.card := sum_le_sum (fun s _ => card_sentSet_le hCG _)
      _ = _ := by simp
  · calc _ ≤ ∑ _i ∈ range (2 * D * (4 * (nodes C).card)), 2 * (nodes C).card :=
          sum_le_sum (fun i hi => (card_le_card
            (sentSet_H_sub hCG hd hℓ hmax x ω (mem_range.1 hi))).trans setup_card_treePairs)
      _ = _ := by simp

/-! ### The spanning tree -/

include hd hℓ in
lemma spanForest_parOf : SpanForest (nodes C) C (parOf C ℓ) (fun _ => ℓ) where
  edge _ _ _ h := (parOf_spec h).1.2
  mem v hv _ h := (parOf_mem hd hℓ hv h).1
  root_par _ _ _ _ := rfl
  root_self v hv h := ((parOf_eq_none_iff hd hℓ hv).1 h).symm
  rank := ⟨fun v => (clGraph C).dist ℓ v, fun _ _ _ h => by
    have := (parOf_spec h).2
    beta_reduce
    omega⟩
  conn u hu v hv := by
    simp only [true_iff]
    exact eReach_of_reachable (hd u hu v hv).1

/-- the outputs of the agents -/
noncomputable def setupZ (C : Finset (Sym2 V)) (ℓ : V) : Agent V → SetupOut V
  | .inl v => (ℓ, parOf C ℓ v, truePairs C, portsA C)
  | .inr _ => (ℓ, none, ∅, ∅)

/-- the message bound of a run -/
def setupM (C : Finset (Sym2 V)) (D : ℕ) : ℕ :=
  (3 * D + 1) * (2 * C.card) + 2 * D * (2 * (nodes C).card) * (2 * (nodes C).card) +
    2 * C.card + 2 * D * (4 * (nodes C).card) * (2 * (nodes C).card)

include hCG hd hℓ hmax in
/-- **The run succeeds.** -/
theorem setup_succ :
    Succ (setupProto V D) (clInst0 N C) x (postOf (clInst0 N C) (SetupSpec C))
      (Prof.mk (setupT C D) (onEdges C (2 * setupT C D)) (setupM C D)) ω := by
  refine ⟨setupT C D, haltsAt_setup hCG hd hℓ hmax x ω, properUpTo_setup hCG x ω _, le_rfl,
    msgsUpTo_setup_le hCG hd hℓ hmax x ω, fun e => ?_,
    fun g => ⟨SetupOut V, setupZ C ℓ g⟩, ?_, ?_⟩
  · have := loadUpTo_setup_le hCG (D := D) (x := x) (ω := ω) (setupT C D) e
    simpa only [Prof.load_mk, onEdges] using this
  · intro g hg
    cases g with
    | inl v =>
      have hv : v ∈ nodes C := by
        by_contra hv
        simp [clInst0, clInstP, clHost, hv] at hg
      rw [outAt_setupT hCG hd hℓ hmax x ω hv]
      rfl
    | inr _ => simp [clInst0, clInstP, clHost] at hg
  · exact ⟨setupZ C ℓ, fun _ _ => rfl, ℓ, hℓ, parOf C ℓ, spanForest_parOf hd hℓ,
      fun _ _ => rfl⟩

end Final

/-! ## Constants -/

lemma diamBound_mono {a a' m m' : ℕ} (ha : a ≤ a') (hm : m ≤ m') :
    diamBound a m ≤ diamBound a' m' := by
  unfold diamBound
  have h1 : Nat.log 2 (2 * m) ≤ Nat.log 2 (2 * m') := Nat.log_mono_right (by omega)
  have h2 : 4 * (a + 1) ≤ 4 * (a' + 1) := by omega
  have := Nat.mul_le_mul h2 (Nat.add_le_add_right h1 1)
  omega

lemma diamBound_le_polylog (Kφ kφ ν : ℕ) :
    diamBound (Kφ * lg ν ^ kφ) (ν ^ 2) ≤ (20 * Kφ + 22) * lg ν ^ (kφ + 1) := by
  unfold diamBound
  have hlg : Nat.log 2 (2 * ν ^ 2) + 1 ≤ 5 * lg ν := by
    have h1 : lg (2 * ν ^ 2) ≤ lg 2 + lg (ν ^ 2) := lg_mul_le _ _
    have h2 : lg (ν ^ 2) ≤ 2 * lg ν + 1 := lg_pow_le _ _
    have h3 : lg 2 = 2 := by decide
    have h1' : Nat.log 2 (2 * ν ^ 2) + 1 ≤ 2 + lg (ν ^ 2) := by rw [h3] at h1; exact h1
    have h4 := one_le_lg ν
    omega
  have ha : 1 ≤ lg ν := one_le_lg ν
  have hb : 1 ≤ lg ν ^ kφ := Nat.one_le_pow _ _ (lg_pos ν)
  rw [pow_succ]
  set a := lg ν
  set b := lg ν ^ kφ
  have hab : 1 ≤ b * a := Nat.one_le_iff_ne_zero.2 (by positivity)
  calc 4 * (Kφ * b + 1) * (Nat.log 2 (2 * ν ^ 2) + 1) + 2
      ≤ 4 * (Kφ * b + b) * (5 * a) + 2 * (b * a) :=
        Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 4 (by omega)) hlg) (by omega)
    _ = (20 * Kφ + 22) * (b * a) := by ring

/-- **Cluster setup in CONGEST** (the [STD] tree primitives of the toolkit): leader election,
a BFS spanning tree, gathering and broadcasting all (ID, degree) pairs, and broadcasting the ports
of `A(C)` (`SetupSpec`) in a `1/polylog`-expander cluster, deterministically, in
`O(polylog ν · n_C)` rounds with `O(polylog ν · n_C²)` messages. -/
theorem clusterSetup_congest (Kφ kφ : ℕ) : ∃ (K k : ℕ) (A : ℕ → CAlg), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (ν : ℕ) (C : Finset (Sym2 V)) (φinv : ℕ),
    Fintype.card V ≤ ν → ν ≤ Fintype.card V → C ⊆ N.G.edgeFinset → C.Nonempty →
    IsExpander C φinv → φinv ≤ Kφ * lg ν ^ kφ →
    CImplT (A ν) N (.clusterSetup C) (Prof.mk (K * lg ν ^ k * (nodes C).card)
      (onEdges C (2 * (K * lg ν ^ k * (nodes C).card))) (K * lg ν ^ k * (nodes C).card ^ 2)) 0 := by
  refine ⟨40 * (20 * Kφ + 22), kφ + 1,
    fun ν V _ _ => setupProto V (diamBound (Kφ * lg ν ^ kφ) (ν ^ 2)), ?_⟩
  intro V _ _ N ν C φinv hV1 _ hCG hne hexp hφ
  set D := diamBound (Kφ * lg ν ^ kφ) (ν ^ 2) with hDdef
  set n := (nodes C).card with hndef
  set L := lg ν ^ (kφ + 1) with hLdef
  have hC := noLoops_of_sub N C hCG
  have hn2 : 2 ≤ n := two_le_card_nodes hC hne
  have hnV : n ≤ ν := (card_le_univ _).trans hV1
  have hCn : C.card ≤ n ^ 2 := card_le_sq hC
  have hCν : C.card ≤ ν ^ 2 := hCn.trans (Nat.pow_le_pow_left hnV 2)
  have hd : DiamLe C D := fun u hu v hv =>
    let h := expander_dist_le hC hexp hu hv
    ⟨h.1, h.2.trans (diamBound_mono hφ hCν)⟩
  have hD1 : 1 ≤ D := by rw [hDdef]; unfold diamBound; omega
  have hDK : D ≤ (20 * Kφ + 22) * L := diamBound_le_polylog Kφ kφ ν
  obtain ⟨ℓ, hℓ, hℓmax⟩ := exists_mem_eq_sup (nodes C) (nodes_nonempty hne) suIdx
  have hmax : ∀ u ∈ nodes C, suIdx u ≤ suIdx ℓ := fun u hu => hℓmax ▸ le_sup hu
  show ImplI (setupProto V D) (clInst0 N C) (inOf (fun _ => ()))
    (postOf (clInst0 N C) (SetupSpec C)) _ 0
  refine ImplI.of_forall _ _ le_rfl (fun ω => ?_)
  -- the cost profile
  have hT : setupT C D ≤ 40 * (20 * Kφ + 22) * L * n := by
    unfold setupT tH tG
    rw [← hndef]
    calc 3 * D + 1 + 2 * D * (2 * n) + 1 + 2 * D * (4 * n) ≤ 40 * D * n := by nlinarith
      _ ≤ 40 * ((20 * Kφ + 22) * L) * n := by gcongr
      _ = 40 * (20 * Kφ + 22) * L * n := by ring
  have hM : setupM C D ≤ 40 * (20 * Kφ + 22) * L * n ^ 2 := by
    unfold setupM
    rw [← hndef]
    have h1 : (3 * D + 1) * (2 * C.card) ≤ (4 * D) * (2 * n ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : 1 * (2 * C.card) ≤ D * (2 * n ^ 2) := Nat.mul_le_mul hD1 (by omega)
    calc (3 * D + 1) * (2 * C.card) + 2 * D * (2 * n) * (2 * n) + 2 * C.card +
          2 * D * (4 * n) * (2 * n)
        ≤ (4 * D) * (2 * n ^ 2) + 2 * D * (2 * n) * (2 * n) + D * (2 * n ^ 2) +
          2 * D * (4 * n) * (2 * n) := by omega
      _ = 34 * D * n ^ 2 := by ring
      _ ≤ 40 * D * n ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
      _ ≤ 40 * ((20 * Kφ + 22) * L) * n ^ 2 := by gcongr
      _ = 40 * (20 * Kφ + 22) * L * n ^ 2 := by ring
  refine (setup_succ hCG hd hℓ hmax _ ω).mono _ _ ?_ (fun _ h => h)
  apply Prof.le_mk
  · exact hT
  · intro e
    simp only [Prof.load_mk, onEdges]
    split_ifs <;> omega
  · exact hM

end APSP.Stoc.Congest
