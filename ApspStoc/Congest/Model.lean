import ApspStoc.Congest.Assume
import ApspStoc.Congest.Notify
import ApspStoc.Congest.TreeCast
import ApspStoc.Congest.Setup
import ApspStoc.Congest.AggUpDown
import ApspStoc.Congest.EmbConstruct
import ApspStoc.Congest.RWLink
import ApspStoc.Congest.RingLE
import ApspStoc.Congest.PerComp
import ApspStoc.Main

/-!
# The toolkit in the CONGEST semantics, and the main theorem there

`toToolkit` builds a `Toolkit` whose algorithms are concrete CONGEST protocols (`CAlg`) and whose
judgement is the concrete one (`CImplT`, `Tasks.lean`):

* every [STD] field is a theorem about the semantics: the generic rules (`Rules.lean`), one round of
  direct messages (`notify_congest`, `Notify.lean`), tree convergecast and broadcast
  (`TreeCastC`), and the cluster setup (`SetupC`, `clusterSetup_congest` in `Setup.lean`: leader,
  BFS tree, the degree table and the ports of `A(C)`);
* every [IMPL] field is a theorem about concrete protocols: Lemma 2.2 (`aggUp_congest`,
  `aggDown_congest`, `AggUpDown.lean`), the ring leader election (`ringLE_congest`, `RingLE.lean`),
  the sequential execution on components (`perCompR_congest` with `perCompC`, `PerComp.lean`), the
  random-walk construction of `G₀` (`rwLink_congest` with `rwAlgC`, `RWLink.lean`) and the
  per-cluster preprocessing (`embedConstruct_congest` with `clusterParC`, `EmbConstruct.lean`);
* the [PRIOR] and [PRIOR+] fields come from a `CAssume`: the cited theorems, stated for concrete
  protocols.

`thm_5_6_congest` is the main theorem (Theorem 5.6 = Theorem 1.1) for the concrete semantics: from
the cited theorems (`CAssume`) and `Mixing`, there is a uniform CONGEST protocol solving APSP in
`Õ(n)` rounds and `Õ(n²)` messages with failure probability `≤ K / n^c`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

/-- the toolkit field `notify` for the CONGEST semantics -/
def NotifyC : Prop := ∃ A : CAlg, ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (E : Overlays V)
    (j sz : ℕ) (Pt S : Finset V) (F : Finset (Sym2 V)) (x : Agent V → Finset V),
    (∀ v, ∀ u ∈ x (.inl v), v ∈ S ∧ N.G.Adj v u ∧ s(v, u) ∈ F) →
    (∀ v, ∀ u ∈ x (.inl v), u ∈ Pt) → S ⊆ Pt →
    CImplT A N (.io E j sz Pt (Finset V) (Finset V) x
      (fun y => ∀ v, y (.inl v) = univ.filter (fun u => v ∈ x (.inl u))))
      (Prof.mk 1 (onEdges F 2) (2 * F.card)) 0

/-- the toolkit field `treeCast` for the CONGEST semantics -/
def TreeCastC : Prop := ∀ Bw : ℕ, ∃ (K : ℕ) (A : ℕ → ℕ → CAlg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (b : ℕ) (par : V → Option V)
    (root : V → V) (val : V → Msg V) (op : Msg V → Msg V → Msg V) (Fp : Finset (Sym2 V))
    (x : Agent V → Option (Option V × V × Msg V × (Msg V → Msg V → Msg V))),
    (∀ v, x (.inl v) = if v ∈ S then some (par v, root v, val v, op) else none) →
    S.card ≤ sz → S ⊆ Pt → Fp ⊆ N.G.edgeFinset →
    (∀ v ∈ S, ∀ u, par v = some u → u ∈ S ∧ s(v, u) ∈ Fp) →
    (∀ v ∈ S, ∀ u, par v = some u → root u = root v) → (∀ v ∈ S, par v = none → root v = v) →
    (∃ r : V → ℕ, ∀ v ∈ S, ∀ u, par v = some u → r u < r v) →
    (∀ v ∈ S, (val v).Small b (ν ^ Bw)) →
    (∀ m m', m.Small b (ν ^ Bw) → m'.Small b (ν ^ Bw) → (op m m').Small b (ν ^ Bw)) →
    CImplT (A ν b) N (.io E j sz Pt (Option (Option V × V × Msg V × (Msg V → Msg V → Msg V)))
        (Option (Msg V)) x
      (fun y => ∀ v ∈ S, ∃ Y, y (.inl v) = some Y ∧
        AggOf op ((S.filter (fun u => root u = root v)).val.map val) Y ∧
        ∀ u ∈ S, root u = root v → y (.inl u) = some Y))
      (Prof.mk (K * (b + 1) * (sz + 1)) (onEdges Fp (K * (b + 1))) (K * (b + 1) * (S.card + 1)))
      0

/-- the toolkit field `clusterSetup` for the CONGEST semantics -/
def SetupC : Prop := ∀ Kφ kφ : ℕ, ∃ (K k : ℕ) (A : ℕ → CAlg), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (ν : ℕ) (C : Finset (Sym2 V)) (φinv : ℕ),
    Fintype.card V ≤ ν → ν ≤ Fintype.card V → C ⊆ N.G.edgeFinset → C.Nonempty →
    IsExpander C φinv → φinv ≤ Kφ * lg ν ^ kφ →
    CImplT (A ν) N (.clusterSetup C) (Prof.mk (K * lg ν ^ k * (nodes C).card)
      (onEdges C (2 * (K * lg ν ^ k * (nodes C).card))) (K * lg ν ^ k * (nodes C).card ^ 2)) 0

/-- The toolkit of the CONGEST semantics, given the assumed contracts. -/
noncomputable def toToolkit (H : CAssume) : Toolkit where
  Alg := CAlg
  Impl := CImplT
  seq := cseq
  skip := cskip
  loc := cloc
  call := ccall
  dstart := cdstart
  dstep := cdstep
  sched := H.sched
  clusterPar := clusterParC
  rwAlg := rwAlgC
  perComp := perCompC
  mstAlg := H.mstAlg
  approxAlg := H.approxAlg
  eoAlg := H.eoAlg
  mono := c_mono
  weaken := c_weaken
  weakenIO := c_weakenIO
  bind := c_bind
  callR := fun F {_} {_} _ _ {_} {_} {_} {_} {_} {_} x {_} {_} {_} h => c_callR F x h
  locR := fun F {_} _ _ N E j sz Pt x => c_locR F N E j sz Pt x
  embThen := c_embThen
  embWeaken := c_embWeaken
  decompThen := c_decompThen
  decompStart := c_decompStart
  decompBase := c_decompBase
  decompStep := c_decompStep
  expDecomp := H.expDecomp
  clusterSetup := clusterSetup_congest
  rwLink := rwLink_congest
  routeG0 := H.routeG0
  g0Then := c_g0Then
  routeViaWeaken := c_routeViaWeaken
  routeWeaken := c_routeWeaken
  embedConstruct := embedConstruct_congest
  aggUp := aggUp_congest
  aggDown := aggDown_congest
  notify := notify_congest
  ghs := H.ghs
  treeCast := treeCast_congest
  ringLE := ringLE_congest
  perCompR := perCompR_congest
  mstRed := H.mstRed
  approxRed := H.approxRed
  eoVirt := H.eoVirt
  schedule := H.schedule

/-- **Theorem 5.6 (= Theorem 1.1) in the CONGEST semantics.** Given the assumed contracts (the
cited theorems, `CAssume`) and `Mixing`, there is a uniform
randomized CONGEST protocol (`A n` for networks with `n` nodes) that solves weighted APSP: run on
any connected network with `n ≥ 1` nodes and weights `≤ n^wexp`, from nodes that know only their
ID, the set of IDs and their incident edges, all nodes halt in the same round and output their
distances and shortest-path parents, within `C·lg^k n·n` rounds and `C·lg^k n·n²` messages,
except with probability `≤ K/n^c`. -/
theorem thm_5_6_congest (H : CAssume) (hmix : Mixing)
    (wexp c : ℕ) :
    ∃ (A : ℕ → CAlg) (C k K : ℕ), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V),
      1 ≤ Fintype.card V → (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp) →
      ∃ (p : Prof V) (δ : ℝ),
        ImplI (A (Fintype.card V) V) (baseInst N) (inOf (fun _ => ()))
          (postOf (baseInst N) (fun z : Agent V → (V → ℕ × V) => APSPSpec N (fun v => z (.inl v))))
          p δ ∧
        p.rounds ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ∧
        p.msgs ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ^ 2 ∧
        δ ≤ (K : ℝ) / (Fintype.card V : ℝ) ^ c :=
  thm_5_6 (toToolkit H) hmix wexp c

end APSP.Stoc.Congest
