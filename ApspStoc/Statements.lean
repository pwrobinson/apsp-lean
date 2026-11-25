import ApspStoc.Basics

/-!
# Statements of the shortest-path-phase lemmas

The lemmas of Sections 4 and 5 are stated here as propositions about a toolkit, so that their
proofs (in separate files) can be developed independently; `Main.lean` combines the proofs.

Throughout, `E` is an overlay embedding with the properties of Theorem 3.10 (`OverlayProps`), with
cluster overlap `fov ν` and embedded path length `fd ν`, both polylogarithmic; `ν = n` is the
public size bound (`ν ≤ n` is needed for numbers `≤ ν^Bw` to fit in `O(Bw)` words, see
`Toolkit.lean`), and failure probabilities are `whp K c ν = K / ν^c`. Each task carries a
public size bound `sz` (known to the participants) bounding the size of the set it works on; round
budgets are stated in terms of `sz` (`szProf`), loads and messages in terms of the actual set.
Each task also carries its participant set `Pt` (`Π` in prose, see `Toolkit.lean`): a lemma on a
set `S` holds for every participant set containing the footprint of `S` (`footprint E j S ⊆ Pt`),
i.e. the nodes of `S`, the relays on their aggregator paths in `L_j` and the hosts of their
aggregators.
-/

namespace APSP.Stoc

open APSP Finset

/-- **Lemma 4.2** (Minor-Aggregation on a subset): with the overlays embedded, one round of any
Minor-Aggregation algorithm on `(S, F)` (`F` ⊆ `G[S]`) with `b`-word values can be executed in
`Õ(b·|S|)` rounds and messages, putting load `Õ(b)·ρ^S_j(e)` on every edge `e` (direct edges of
`G` incident to `S` and the embedded aggregator paths of `S` in `L_j`). The value size `b` is
public: the algorithm `A ν b` depends on it (its round budget does). The participants contain
the footprint of `S`. -/
def Lemma_4_2 (T : Toolkit) : Prop :=
  ∀ (c Bw : ℕ) {fov fd : ℕ → ℕ}, IsPL fov → IsPL fd →
  ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (X : ℕ),
    OverlayProps N.G E (fov ν) (fd ν) X → ∀ (j sz : ℕ) (I : MAInst V) (b : ℕ),
    j < Fintype.card V → I.S.card ≤ sz → I.Small b (ν ^ Bw) →
    ∀ Pt : Finset V, footprint E j I.S ⊆ Pt →
    T.Impl (A ν b) N (maTask N.G E j sz Pt I) (szProf N.G E j sz I.S (q ν * (b + 1)))
      (whp Kδ c ν)

/-- The physical case of **Lemma 5.3** (the paper's contribution in Section 5.1): Eulerian
orientation of an even-degree subgraph of `G[S]` in `Õ(|S|)` rounds and messages, with load
`Õ(1)·ρ^S_j`. -/
def EOPhys (T : Toolkit) : Prop :=
  ∀ (c : ℕ) {fov fd : ℕ → ℕ}, IsPL fov → IsPL fd →
  ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (X : ℕ),
    OverlayProps N.G E (fov ν) (fd ν) X → ∀ (j sz : ℕ) (H : EOInst V),
    j < Fintype.card V → H.S.card ≤ sz → H.Physical → H.WF N.G →
    ∀ Pt : Finset V, footprint E j H.S ⊆ Pt →
    T.Impl (A ν) N (eoTask E j sz Pt H) (szProf N.G E j sz H.S (q ν)) (whp Kδ c ν)

/-- **Lemma 5.3** (Eulerian orientation on a subset): on a connected set `S`, with at most
`kv ν` (polylogarithmically many) virtual nodes; the bound `kv ν` is public (a function of `ν`),
so the algorithm can use it for its round budget. -/
def Lemma_5_3 (T : Toolkit) : Prop :=
  ∀ {kv : ℕ → ℕ}, IsPL kv → ∃ qδ : ℕ → ℕ, IsPL qδ ∧
  ∀ (c : ℕ) {fov fd : ℕ → ℕ}, IsPL fov → IsPL fd →
  ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (X : ℕ),
    OverlayProps N.G E (fov ν) (fd ν) X → ∀ (j sz : ℕ) (H : EOInst V),
    j < Fintype.card V → H.S.card ≤ sz → ConnSet N.G H.S → H.WF N.G → H.k ≤ kv ν →
    ∀ Pt : Finset V, footprint E j H.S ⊆ Pt →
    T.Impl (A ν) N (eoTask E j sz Pt H) (szProf N.G E j sz H.S (q ν)) ((qδ ν : ℝ) * whp Kδ c ν)

/-- **Lemma 5.4** (approximate SSSP on a subset), with `ε = 1/2`, weights and virtual-edge weights
at most `ν^Bw`. -/
def Lemma_5_4 (T : Toolkit) : Prop :=
  ∀ Bw : ℕ, ∃ qδ : ℕ → ℕ, IsPL qδ ∧ ∀ (c : ℕ) {fov fd : ℕ → ℕ}, IsPL fov → IsPL fd →
  ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    (∀ e ∈ N.G.edgeFinset, N.w e ≤ ν ^ Bw) →
    ∀ (E : Overlays V) (X : ℕ), OverlayProps N.G E (fov ν) (fd ν) X →
    ∀ (j sz : ℕ) (S : Finset V) (w0 : V → Option (ℕ × V)), j < Fintype.card V →
    S.card ≤ sz → ConnSet N.G S → (∀ v c p, w0 v = some (c, p) → c ≤ ν ^ Bw) →
    ∀ Pt : Finset V, footprint E j S ⊆ Pt →
    T.Impl (A ν) N (.io E j sz Pt (SubIn V) (Option (ℕ × V)) (subInput S w0)
        (fun y => ApproxSpec N S w0 (fun v => y (.inl v))))
      (szProf N.G E j sz S (q ν)) ((qδ ν : ℝ) * whp Kδ c ν)

/-- MST / leader election and spanning trees on the components of `G[S]` (used in Steps 3 and 6
of the proof of Theorem 5.5, via Lemma 4.2). -/
def LemmaMST (T : Toolkit) : Prop :=
  ∃ qδ : ℕ → ℕ, IsPL qδ ∧ ∀ (c : ℕ) {fov fd : ℕ → ℕ}, IsPL fov → IsPL fd →
  ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (E : Overlays V) (X : ℕ),
    OverlayProps N.G E (fov ν) (fd ν) X → ∀ (j sz : ℕ) (S : Finset V), j < Fintype.card V →
    S.card ≤ sz → ∀ Pt : Finset V, footprint E j S ⊆ Pt →
    T.Impl (A ν) N (.mst E j sz Pt S) (szProf N.G E j sz S (q ν)) ((qδ ν : ℝ) * whp Kδ c ν)

/-- **Theorem 5.5** (message-optimal exact SSSP): SSSP from `s` (every node learns its distance
and its parent in a shortest-path tree), run on overlay `rank(s)`, in `Õ(n)` rounds and messages,
with load `Õ(1)·ρ_{rank(s)}(e)` on every edge `e`. All nodes take part (`Pt = univ`, the
footprint of `V`). The number of failure events `qδ ν · ν` does not depend on the confidence
`c`. -/
def Thm_5_5 (T : Toolkit) : Prop :=
  ∀ wexp : ℕ, ∃ qδ : ℕ → ℕ, IsPL qδ ∧ ∀ (c : ℕ) {fov fd : ℕ → ℕ}, IsPL fov → IsPL fd →
  ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
    (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V → (∀ e ∈ N.G.edgeSet, N.w e ≤ ν ^ wexp) →
    ∀ (E : Overlays V) (X : ℕ), OverlayProps N.G E (fov ν) (fd ν) X → ∀ (s : V),
    T.Impl (A ν) N (.io E (Fintype.equivFin V s : ℕ) (Fintype.card V) univ V (ℕ × V) (fun _ => s)
        (fun y => SSSPSpec N s (fun v => y (.inl v))))
      (Prof.mk (q ν * ν) (fun e => q ν * E.rho N.G (Fintype.equivFin V s : ℕ) univ e) (q ν * ν))
      (((qδ ν * ν : ℕ) : ℝ) * whp Kδ c ν)

end APSP.Stoc
