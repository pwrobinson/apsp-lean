import ApspStoc.Congest.Model
import ApspStoc.Congest.KTGather

/-!
# Theorem 5.6 in the KT1 model: nodes do not know the set of IDs

In `thm_5_6_congest` (`Model.lean`) the protocol run on a network with node set `V` is a
`Proto V`, so every node knows the set of all IDs. Here this assumption is removed.

**The model** (`KTDefs.lean`). IDs come from a known universe `U` (a `Fintype`, of size polynomial
in `n`: `|U| ≤ (n + 1)^idexp`); the node set is an unknown `S : Finset U` and the network is
`N : WNet S`. The protocol is a `Proto U` (it knows `U`), the algorithm is indexed by `n = |S|`,
and the instance `ktInst S N` gives every node of `S` only its ID and its incident edges with their
weights (hence its neighbours' IDs). The outputs are read back on `S` with `ktOut`.

**The protocol** `ktAlg Ain n U = seqP (gatherP n U) (simP Ain n U)`, where `Ain` is the algorithm
of `thm_5_6_congest`:

1. **Gather** (`gatherP`, `KTGatherDefs.lean`, deterministic): binary search for the least index
   of a node of `S` by `B = lg |U|` floodings of `n` rounds each, BFS by flooding from that
   leader, subtree sizes, preorder numbers, and a collision-free pipelined upcast/broadcast of all
   IDs along the BFS tree. Every node of `S` learns `S`, in `(B + 6) n` rounds and with at most
   `(B + 11) n²` messages (`gather_implI`).
2. **Simulate** (`simP`, `KTSim.lean`): every node runs `Ain n ↥S` on the node set `↥S` it has
   learned, as in the model with known node set; the run is the inner run, translated
   (`st_sim`), and the failure probability is the inner one (`implI_sim`).

The costs add up (`bindI`). With `B ≤ (idexp + 1) lg n` (`lg_card_le`), the bounds keep the form
`C lg^k n · n` rounds and `C lg^k n · n²` messages, and the failure probability is the one of
`thm_5_6_congest`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

/-- **The KT1 algorithm** for networks with `n` nodes: gather the node set, then run `Ain n` on
it. -/
noncomputable def ktAlg (Ain : ℕ → CAlg) (n : ℕ) : CAlg :=
  fun U _ _ => seqP (KT.gatherP n U) (KT.simP Ain n U)

/-- the number of windows of the binary search is `O(idexp · lg n)` -/
lemma lg_card_le {M n e : ℕ} (hM : M ≤ (n + 1) ^ e) : lg M ≤ (e + 1) * lg n := by
  have h1 : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : M ≤ 2 ^ ((Nat.log 2 n + 1) * e) :=
    le_trans hM (by rw [pow_mul]; exact Nat.pow_le_pow_left h1 e)
  have h3 : Nat.log 2 M ≤ (Nat.log 2 n + 1) * e :=
    le_trans (Nat.log_mono_right h2) (by rw [Nat.log_pow (by norm_num)])
  unfold lg
  nlinarith

/-- **Theorem 5.6 (= Theorem 1.1) in the KT1 model.** Given the assumed contracts (`CAssume`) and
`Mixing`, there is a uniform randomized CONGEST algorithm (`A n` for networks with `n` nodes) that
solves weighted APSP on any connected network `N` on an unknown node set `S` of `n ≥ 1` IDs from a
known universe `U` with `|U| ≤ (n + 1)^idexp`, with weights `≤ n^wexp`, from nodes that know only
their ID, `n`, the universe and their incident edges with their weights: all nodes of `S` halt in
the same round and output their distances and next hops, within `C·lg^k n·n` rounds and
`C·lg^k n·n²` messages, except with probability `≤ K/n^c`. -/
theorem thm_5_6_kt1 (H : CAssume) (hmix : Mixing) (wexp c idexp : ℕ) :
    ∃ (A : ℕ → CAlg) (C k K : ℕ), ∀ {U : Type} [Fintype U] [DecidableEq U] (S : Finset U)
      (N : WNet S), 1 ≤ S.card → Fintype.card U ≤ (S.card + 1) ^ idexp →
      (∀ e ∈ N.G.edgeSet, N.w e ≤ S.card ^ wexp) →
      ∃ (p : Prof U) (δ : ℝ),
        ImplI (A S.card U) (ktInst S N) (inOf (fun _ => ()))
          (postOf (ktInst S N) (fun z : Agent U → (U → ℕ × U) => APSPSpec N (ktOut S z))) p δ ∧
        p.rounds ≤ C * lg S.card ^ k * S.card ∧
        p.msgs ≤ C * lg S.card ^ k * S.card ^ 2 ∧
        δ ≤ (K : ℝ) / (S.card : ℝ) ^ c := by
  obtain ⟨Ain, C, k, K, hA⟩ := thm_5_6_congest H hmix wexp c
  refine ⟨ktAlg Ain, C + idexp + 12, k + 1, K, ?_⟩
  intro U _ _ S N hn hU hw
  have hS : S.Nonempty := card_pos.1 hn
  have hcard : Fintype.card S = S.card := Fintype.card_coe S
  obtain ⟨q, δ, hq, hqr, hqm, hδ⟩ := hA N (by rw [hcard]; exact hn) (by rw [hcard]; exact hw)
  rw [hcard] at hq hqr hqm hδ
  have hδ0 : 0 ≤ δ := hq.nonneg
  -- the simulation phase, from any output of the gather phase
  have hsim : ∀ y, postOf (ktInst S N) (fun z : Agent U → Finset U => ∀ v ∈ S, z (.inl v) = S) y →
      ImplI (KT.simP Ain S.card U) (ktInst S N) (fun g => pairMem (inOf (fun _ => ()) g) (y g))
        (KT.postKT N) (Prof.mk q.rounds (fun _ => q.msgs) q.msgs) δ := by
    rintro y ⟨z, hz, hzS⟩
    refine KT.implI_sim (fun v hv => ?_) hq
    have h1 := hz (.inl v) (by rw [ktInst_host_inl, ite_eq_left hv]; rfl)
    rw [hzS v hv] at h1
    show pairMem (inOf (fun _ => ()) (Sum.inl v)) (y (.inl v)) = _
    rw [h1]
    rfl
  have hall := bindI (KT.gather_implI (N := N) hS) hsim hδ0
  refine ⟨_, 0 + δ, hall, ?_, ?_, ?_⟩
  · -- rounds
    simp only [Prof.rounds_add, Prof.rounds_mk]
    have hB := lg_card_le hU
    have hL := lg_pos S.card
    have hP : 1 ≤ lg S.card ^ k := Nat.one_le_pow _ _ hL
    have ht : KT.tFin S.card (KT.nB U) = (KT.nB U + 6) * S.card := by
      unfold KT.tFin KT.tPP KT.tPRE KT.tSZ; ring
    have hnB : KT.nB U ≤ (idexp + 1) * lg S.card := hB
    rw [ht, pow_succ]
    have e1 : (KT.nB U + 6) * S.card ≤ (idexp + 7) * (lg S.card ^ k * lg S.card) * S.card := by
      have : KT.nB U + 6 ≤ (idexp + 7) * lg S.card := by nlinarith
      calc (KT.nB U + 6) * S.card ≤ (idexp + 7) * lg S.card * S.card := Nat.mul_le_mul_right _ this
        _ ≤ (idexp + 7) * (lg S.card ^ k * lg S.card) * S.card := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; nlinarith
    have e2 : q.rounds ≤ C * (lg S.card ^ k * lg S.card) * S.card :=
      le_trans hqr (by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; nlinarith)
    calc (KT.nB U + 6) * S.card + q.rounds
        ≤ (idexp + 7) * (lg S.card ^ k * lg S.card) * S.card +
          C * (lg S.card ^ k * lg S.card) * S.card := Nat.add_le_add e1 e2
      _ ≤ (C + idexp + 12) * (lg S.card ^ k * lg S.card) * S.card := by nlinarith
  · -- messages
    simp only [Prof.msgs_add, Prof.msgs_mk]
    have hB := lg_card_le hU
    have hL := lg_pos S.card
    have hP : 1 ≤ lg S.card ^ k := Nat.one_le_pow _ _ hL
    have hnB : KT.nB U ≤ (idexp + 1) * lg S.card := hB
    rw [pow_succ]
    have e1 : (KT.nB U + 11) * S.card ^ 2 ≤ (idexp + 12) * (lg S.card ^ k * lg S.card) * S.card ^ 2 := by
      have : KT.nB U + 11 ≤ (idexp + 12) * lg S.card := by nlinarith
      calc (KT.nB U + 11) * S.card ^ 2 ≤ (idexp + 12) * lg S.card * S.card ^ 2 :=
            Nat.mul_le_mul_right _ this
        _ ≤ (idexp + 12) * (lg S.card ^ k * lg S.card) * S.card ^ 2 := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; nlinarith
    have e2 : q.msgs ≤ C * (lg S.card ^ k * lg S.card) * S.card ^ 2 :=
      le_trans hqm (by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; nlinarith)
    calc (KT.nB U + 11) * S.card ^ 2 + q.msgs
        ≤ (idexp + 12) * (lg S.card ^ k * lg S.card) * S.card ^ 2 +
          C * (lg S.card ^ k * lg S.card) * S.card ^ 2 := Nat.add_le_add e1 e2
      _ ≤ (C + idexp + 12) * (lg S.card ^ k * lg S.card) * S.card ^ 2 := by nlinarith
  · simpa using hδ

end APSP.Stoc.Congest
