import ApspStoc.Defs

/-!
# The random-walk construction of `G₀` (proof of Theorem 3.3): the probabilistic model

Lazy random walks on a cluster `C`, driven by uniformly random seeds. A step from `v` uses a seed
`r < D` where `D = seedRange C` is a common multiple of all `2·deg_C(v)`: the walk stays if
`r < D/2` and otherwise crosses the incident edge of `C` with index `⌊(r - D/2) / (D/(2 deg v))⌋`;
hence it stays with probability `1/2` and crosses every incident edge with probability
`1/(2 deg v)` — exactly the lazy random walk.

The construction of the paper (proof of Theorem 3.3): every port `p = (v, e) ∈ P` generates `R`
tokens; a token first crosses `e` and then performs `2ℓ` lazy random-walk steps. The walk
*survives* if its last step crossed an edge `e'` into a node `x` with `(x, e') ∈ P`; it then
becomes an edge of `G₀` between `p` and `(x, e')`, embedded along the walk. The construction
*overflows* if in some step more than `t` tokens cross some edge in the same direction (each step
is allotted `t` rounds).
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Lazy random walks with seeds -/

/-- The incident edges of `v` in `C`, in a fixed enumeration. -/
noncomputable def incList (C : Finset (Sym2 V)) (v : V) : List (Sym2 V) :=
  (C.filter (fun e => v ∈ e)).toList

/-- The seed range: a common multiple of `2·deg_C(v)` for all `v`. -/
noncomputable def seedRange (C : Finset (Sym2 V)) : ℕ := 2 * ∏ v, max 1 (degIn C v)

/-- The other endpoint of `e` seen from `v` (`v` itself if `v ∉ e`). -/
noncomputable def otherEnd (e : Sym2 V) (v : V) : V :=
  if h : v ∈ e then Sym2.Mem.other h else v

/-- One lazy step from `v` with seed `r < seedRange C`: the new node and the crossed edge (if any). -/
noncomputable def lazyStep (C : Finset (Sym2 V)) (v : V) (r : ℕ) : V × Option (Sym2 V) :=
  if r < seedRange C / 2 ∨ degIn C v = 0 then (v, none)
  else
    match (incList C v)[(r - seedRange C / 2) / (seedRange C / 2 / degIn C v)]? with
    | some e => (otherEnd e v, some e)
    | none => (v, none)

/-- The steps of a lazy walk from `u` with the given seeds: (node after the step, crossed edge). -/
noncomputable def walkSteps (C : Finset (Sym2 V)) : V → List ℕ → List (V × Option (Sym2 V))
  | _, [] => []
  | u, r :: rs => lazyStep C u r :: walkSteps C (lazyStep C u r).1 rs

/-- The final node of a lazy walk from `u` with the given seeds. -/
noncomputable def walkEnd (C : Finset (Sym2 V)) (u : V) (rs : List ℕ) : V :=
  rs.foldl (fun v r => (lazyStep C v r).1) u

/-- `t`-step transition probability `P^t(u, x)` of the lazy random walk on `C`. -/
noncomputable def walkProb (C : Finset (Sym2 V)) (t : ℕ) (u x : V) : ℝ := by
  classical exact
    ((univ.filter (fun s : Fin t → Fin (seedRange C) =>
      walkEnd C u (List.ofFn (fun i => (s i : ℕ))) = x)).card : ℝ) / (seedRange C : ℝ) ^ t

/-- **[PRIOR] Mixing of lazy random walks on expanders** (Jerrum–Sinclair; Cheeger's inequality
for reversible chains and the spectral bound `|P^t(u,x) - π(x)| ≤ √(π(x)/π(u)) (1 - Φ²/2)^t`):
on a cluster with conductance `≥ 1/φinv`, after `t ≥ Km (φinv + 1)² lg ν` steps the lazy walk
from any node is at every node `x` with probability within a factor `[1/2, 3/2]` of the stationary
probability `π(x) = deg(x)/2m`. (For a suitable constant `Km` this follows from the spectral
bound, since the lazy chain has conductance `≥ 1/(2 φinv)`, `π ≥ 1/2m` and `m ≤ ν²`.) This is a theorem of mathematics, not a fact about CONGEST; the main
theorem takes it as a hypothesis. -/
def Mixing : Prop :=
  ∃ Km : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (C : Finset (Sym2 V)) (φinv ν : ℕ),
    NoLoops C → C.Nonempty → IsExpander C φinv → Fintype.card V ≤ ν →
    ∀ t, Km * (φinv + 1) ^ 2 * lg ν ≤ t → ∀ u ∈ nodes C, ∀ x ∈ nodes C,
      |walkProb C t u x - (degIn C x : ℝ) / (2 * C.card)| ≤ (degIn C x : ℝ) / (4 * C.card)

/-! ## The construction -/

/-- Index set of the walks: `R` tokens per port of `P`. -/
abbrev RWIdx (P : Finset (Port V)) (R : ℕ) := {p // p ∈ P} × Fin R

/-- The random seeds of all walks (each walk performs `2ℓ` lazy steps). -/
abbrev RWSeeds (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ) :=
  RWIdx P R → Fin (2 * ℓ) → Fin (seedRange C)

/-- Probability of an event under uniform seeds. -/
noncomputable def rwProb (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ)
    (ev : RWSeeds C P R ℓ → Prop) : ℝ := by
  classical exact ((univ.filter ev).card : ℝ) / (Fintype.card (RWSeeds C P R ℓ) : ℝ)

/-- The trajectory of the walk generated at port `p = (v, e)` with seeds `σ`: first the crossing of
`e`, then the `2ℓ` lazy steps; each entry is (node after the step, crossed edge). -/
noncomputable def rwTraj (C : Finset (Sym2 V)) (p : Port V) {ℓ : ℕ}
    (σ : Fin (2 * ℓ) → Fin (seedRange C)) : List (V × Option (Sym2 V)) :=
  (otherEnd p.2 p.1, some p.2) :: walkSteps C (otherEnd p.2 p.1) (List.ofFn (fun i => (σ i : ℕ)))

/-- The port through which the walk's last step entered its final node (if the last step moved). -/
noncomputable def rwEnd (C : Finset (Sym2 V)) (p : Port V) {ℓ : ℕ}
    (σ : Fin (2 * ℓ) → Fin (seedRange C)) : Option (Port V) :=
  match (rwTraj C p σ).getLast? with
  | some (x, some e) => some (x, e)
  | _ => none

/-- The walk survives: its last step entered its final node through a port of `P`. -/
def rwSurv (C : Finset (Sym2 V)) (P : Finset (Port V)) (p : Port V) {ℓ : ℕ}
    (σ : Fin (2 * ℓ) → Fin (seedRange C)) : Prop :=
  ∃ q ∈ P, rwEnd C p σ = some q

/-- The embedded path of a walk: the edges it crossed. -/
noncomputable def rwPath (C : Finset (Sym2 V)) (p : Port V) {ℓ : ℕ}
    (σ : Fin (2 * ℓ) → Fin (seedRange C)) : List (Sym2 V) :=
  (rwTraj C p σ).filterMap (fun st => st.2)

/-- The surviving walks. -/
noncomputable def rwSurvivors (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ)
    (ω : RWSeeds C P R ℓ) : Finset (RWIdx P R) := by
  classical exact univ.filter (fun w => rwSurv C P w.1.1 (ω w))

/-- The edges of `G₀` (a multigraph on `P`): one edge `(p, q)` per surviving walk from `p` ending
through `q`. -/
noncomputable def rwG0 (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ)
    (ω : RWSeeds C P R ℓ) : Multiset (Port V × Port V) :=
  (rwSurvivors C P R ℓ ω).val.map (fun w => (w.1.1, (rwEnd C w.1.1 (ω w)).getD w.1.1))

/-- Congestion of the embedding of `G₀`: the maximum number of crossings of an edge of `C` by
surviving walks. -/
noncomputable def rwCong (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ)
    (ω : RWSeeds C P R ℓ) : ℕ :=
  C.sup (fun e => ∑ w ∈ rwSurvivors C P R ℓ ω, (rwPath C w.1.1 (ω w)).count e)

/-- Overflow: in some lazy step `j < 2ℓ`, more than `t` walks enter some node `y` through the same
edge `e` (the step is allotted `t` rounds). -/
def rwOverflow (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ t : ℕ) (ω : RWSeeds C P R ℓ) :
    Prop := by
  classical exact ∃ j < 2 * ℓ, ∃ (y : V) (e : Sym2 V),
    t < (univ.filter (fun w : RWIdx P R => (rwTraj C w.1.1 (ω w))[j + 1]? = some (y, some e))).card

/-! ## Expansion of a multigraph on ports -/

/-- Volume of a set of ports in a multigraph given by its edge multiset. -/
def volMG (E : Multiset (Port V × Port V)) (A : Finset (Port V)) : ℕ :=
  (E.map (fun pq => (if pq.1 ∈ A then 1 else 0) + (if pq.2 ∈ A then 1 else 0))).sum

/-- Number of edges of the multigraph crossing the cut `(A, Aᶜ)`. -/
def cutMG (E : Multiset (Port V × Port V)) (A : Finset (Port V)) : ℕ :=
  (E.filter (fun pq => (pq.1 ∈ A ∧ pq.2 ∉ A) ∨ (pq.1 ∉ A ∧ pq.2 ∈ A))).card

/-- The multigraph on `P` has no isolated node and conductance at least `1/φinv`. -/
def IsExpanderMG (P : Finset (Port V)) (E : Multiset (Port V × Port V)) (φinv : ℕ) : Prop :=
  (∀ p ∈ P, 1 ≤ volMG E {p}) ∧
  ∀ A ⊆ P, min (volMG E A) (volMG E (P \ A)) ≤ φinv * cutMG E A

/-- `g` truthfully describes the constructed `G₀`: at most `g.n0` nodes (`|P|`), at most `g.m0` edges, conductance at
least `1/g.φinv` (and no isolated node), embedding congestion at most `g.cong` and dilation at most
`g.dil`. -/
def TrueParams (C : Finset (Sym2 V)) (P : Finset (Port V)) (R ℓ : ℕ) (ω : RWSeeds C P R ℓ)
    (g : G0Data) : Prop :=
  P.card ≤ g.n0 ∧ (rwSurvivors C P R ℓ ω).card ≤ g.m0 ∧ IsExpanderMG P (rwG0 C P R ℓ ω) g.φinv ∧
  rwCong C P R ℓ ω ≤ g.cong ∧ 2 * ℓ + 1 ≤ g.dil

end APSP.Stoc
