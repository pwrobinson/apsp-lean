import ApspStoc.Toolkit
import ApspStoc.G0Model

/-!
# Claims 3.4 and 3.5: statements

`RWLink T` is the standard fact connecting the random-walk construction (an algorithm) with the
probabilistic model of `G0Model.lean`; `BuildG0Stmt T` is the conclusion of Claims 3.4/3.5 in the
form used by the proof of Theorem 3.3 (it is the statement of the field `buildG0` of the toolkit).
-/

namespace APSP.Stoc

open APSP Finset

/-- **[STD]** The random-walk construction (proof of Theorem 3.3), with parameters computed from
`(n_C, m_C)` by `Rf` (tokens per port) and `tf` (rounds per step) and walk length `2ℓ`: every port
of `P` sends `R` tokens over its edge (`R` rounds), the tokens perform `2ℓ` lazy random-walk steps
with independent uniform seeds (each step allotted `t` rounds), every walk's final node keeps the
token iff it entered through a port of `P`, and the survival is reported back along the reversed
walk; nodes on a walk record its next hops. Every step sends at most two messages per edge and
round, and every walk costs `O(ℓ)` messages. Unless the construction overflows (a step needs more
than `t` rounds), the result is the multigraph `rwG0` on `P`, algorithmically embedded along the
walks. The nodes output the *public* parameters `gf (n_C, m_C)`, which must satisfy `Good`
(premise); the construction fails if they do not describe the constructed `G₀` (`TrueParams` is
part of the failure event). A token carries its walk index and path position (`O(log_n (R + ℓ))`
words), so the constant `Kc` depends on an exponent `kB` with `R + 2ℓ + 2 ≤ (n + 4)^kB`. -/
def RWLink (T : Toolkit) : Prop :=
  ∃ rw : (ℕ → ℕ → ℕ) → ℕ → (ℕ → ℕ → ℕ) → (ℕ → ℕ → G0Data) → T.Alg, ∀ kB : ℕ, ∃ Kc : ℕ,
  ∀ (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data) {V : Type} [Fintype V]
    [DecidableEq V]
    (N : WNet V) (C : Finset (Sym2 V)) (P : Finset (Port V)) (Good : G0Data → Prop),
    C ⊆ N.G.edgeFinset → C.Nonempty → P ⊆ allPorts C → Good (gf (nodes C).card C.card) →
    Rf (nodes C).card C.card + 2 * ℓ + 2 ≤ (Fintype.card V + 4) ^ kB →
    T.Impl (rw Rf ℓ tf gf) N (.buildG0 C P Good)
      (Prof.mk (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1))
        (onEdges C (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1)))
        (Kc * (P.card * Rf (nodes C).card C.card * (ℓ + 1))))
      (rwProb C P (Rf (nodes C).card C.card) ℓ (fun ω =>
        rwOverflow C P (Rf (nodes C).card C.card) ℓ (tf (nodes C).card C.card) ω ∨
        ¬ TrueParams C P (Rf (nodes C).card C.card) ℓ ω (gf (nodes C).card C.card)))

/-- **Claims 3.4 and 3.5** (in the form used by Theorem 3.3): on a port set `P` with
`n_C ≤ |P| ≤ a·n_C` of a `1/polylog`-expander cluster `C`, the construction takes `Õ(m_C/n_C)`
rounds and `Õ(m_C)` messages and yields, w.h.p., a `1/polylog`-expander on `P` with `Õ(|P|)`
edges, embedded into `C` with polylog congestion and dilation. The parameters `g` of `G₀` that the
nodes output are public (computed from `n_C`, `m_C` and `ν`), so the size bound `g.n0` is only
known to lie between `|P|` and `a·n_C`; the edge bound is `g.m0 ≤ Õ(g.n0)`. -/
def BuildG0Stmt (T : Toolkit) : Prop :=
  ∀ (c a Kφ kφ : ℕ), ∃ (K k Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
    ∀ (C : Finset (Sym2 V)) (P : Finset (Port V)) (φinv : ℕ), C ⊆ N.G.edgeFinset → C.Nonempty →
    IsExpander C φinv → φinv ≤ Kφ * lg ν ^ kφ → P ⊆ allPorts C → (nodes C).card ≤ P.card →
    P.card ≤ a * (nodes C).card →
    T.Impl (A ν) N (.buildG0 C P (fun g => P.card ≤ g.n0 ∧ g.n0 ≤ a * (nodes C).card ∧
        g.m0 ≤ K * lg ν ^ k * g.n0 ∧ g.φinv ≤ K * lg ν ^ k ∧ g.cong ≤ K * lg ν ^ k ∧
        g.dil ≤ K * lg ν ^ k))
      (Prof.mk (K * lg ν ^ k * (C.card / (nodes C).card + 1))
        (onEdges C (2 * (K * lg ν ^ k * (C.card / (nodes C).card + 1))))
        (K * lg ν ^ k * C.card))
      (whp Kδ c ν)

/-- The random-walk link holds for every toolkit (it is its field `rwLink`). -/
theorem rwLink_of_toolkit (T : Toolkit) : RWLink T := ⟨T.rwAlg, T.rwLink⟩

end APSP.Stoc
