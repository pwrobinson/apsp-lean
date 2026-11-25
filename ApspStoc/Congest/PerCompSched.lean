import ApspStoc.Congest.PerCompLocal

/-!
# The global schedule of the component traversal (for `perCompR`)

Given the spanning tree of `P` (parents `parP`, ranks `rkP`, root `r`), the spanning forest of
`G[S]` (`parS`, `rkS`, roots `rtS`) and the durations `tB ℓ` of the sub-runs of `B` (one per
leader `ℓ`, i.e. per component `comp ℓ`), `PCG` defines the explicit schedule of the traversal,
in frames:

* frame `0` is idle; the segments of the traversal (`tl = segs …`, `PerCompSeg`) follow each other
  from frame `1` on (`stF i` is the first frame of segment `i`): a token move lasts one frame, the
  phase of leader `ℓ` started in frame `a` lasts until the end of its sub-run,
  `phEnd ℓ a = alignUp a Π + 2Π + ⌈tB ℓ / 3⌉`;
* the final phase starts at `E0 = stF |tl|` and all nodes halt at `TL = A0 + 2Π` of the final
  phase;
* `ML u w φ`: the message from `u` to `w` in frame `φ` (token moves, and the broadcasts and
  packets of the phases, `phMsg`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

section Align

lemma le_alignUp (x : ℕ) {q : ℕ} (hq : 0 < q) : x ≤ alignUp x q := by
  unfold alignUp
  have := Nat.div_add_mod (x + q - 1) q
  have := Nat.mod_lt (x + q - 1) hq
  omega

lemma alignUp_lt (x : ℕ) {q : ℕ} (hq : 0 < q) : alignUp x q < x + q := by
  unfold alignUp
  have := Nat.div_mul_le_self (x + q - 1) q
  rw [mul_comm] at this
  omega

lemma dvd_alignUp (x q : ℕ) : q ∣ alignUp x q := Dvd.intro _ rfl

/-- In a window of length `q` starting at a multiple `A` of `q`, `A` is the floor. -/
lemma floor_window {q A ψ : ℕ} (hq : 0 < q) (hA : q ∣ A) (h1 : A ≤ ψ) (h2 : ψ < A + q) :
    q * (ψ / q) = A := by
  obtain ⟨k, rfl⟩ := hA
  have : ψ / q = k := Nat.div_eq_of_lt_le (by rw [mul_comm]; exact h1)
    (by rw [add_mul, one_mul, mul_comm]; exact h2)
  rw [this]

end Align

/-- A global phase: start `A0`, size parameter `L`, content `c`, leader `l`, sources `Q`, and the
tree of the broadcast (`par`, `rk`). -/
structure GPh (V : Type) where
  A0 : ℕ
  L : ℕ
  c : ℕ
  l : V
  Q : Finset V
  par : V → Option V
  rk : V → ℕ

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- The messages of a phase: the broadcast (a node of depth `d` sends to its children in frame
`A0 + d`), then the packets (sub-phase `h`, slot `s`, in frame `A0 + Π + h·L + s`). -/
noncomputable def phMsg (E : Overlays V) (j dil : ℕ) (Y : GPh V) (u w : V) (φ : ℕ) :
    Option (W3 V) :=
  if Y.A0 ≤ φ ∧ φ < Y.A0 + Y.L then
    (if u ∈ Y.Q ∧ w ∈ Y.Q ∧ Y.par w = some u ∧ dep Y.par Y.rk u = φ - Y.A0 then
      some (bcW Y.c) else none)
  else if Y.A0 + PiL dil Y.L ≤ φ ∧ φ < Y.A0 + PiL dil Y.L + dil * Y.L then
    slotMsg (pk E j Y.Q ((φ - Y.A0 - PiL dil Y.L) / Y.L) u w) ((φ - Y.A0 - PiL dil Y.L) % Y.L)
      Y.c Y.l
  else none

/-- The global data of the traversal. -/
structure PCG (V : Type) [Fintype V] [DecidableEq V] where
  N : WNet V
  E : Overlays V
  j : ℕ
  sz : ℕ
  P : Finset V
  S : Finset V
  parP : V → Option V
  rkP : V → ℕ
  r : V
  parS : V → Option V
  rkS : V → ℕ
  rtS : V → V
  tB : V → ℕ

namespace PCG

variable (X : PCG V)

/-- the public dilation -/
noncomputable def dil : ℕ := X.E.dil

/-- leaders -/
noncomputable def isL (v : V) : Bool := by
  classical exact decide (v ∈ X.S ∧ X.parS v = none)

/-- the leaders -/
noncomputable def lds : Finset V := by classical exact X.S.filter (fun v => X.parS v = none)

/-- the component of leader `ℓ` -/
noncomputable def comp (ℓ : V) : Finset V := by classical exact X.S.filter (fun v => X.rtS v = ℓ)

/-- the period of the phase of `ℓ` -/
noncomputable def PiK (ℓ : V) : ℕ := PiL X.dil (X.comp ℓ).card

/-- the end of the phase of `ℓ` started in frame `a` -/
noncomputable def phEnd (ℓ : V) (a : ℕ) : ℕ :=
  alignUp a (X.PiK ℓ) + 2 * X.PiK ℓ + (X.tB ℓ + 2) / 3

/-- the duration of a segment started in frame `a` -/
noncomputable def dur : TSg V → ℕ → ℕ
  | .tk _ _, _ => 1
  | .ph ℓ, a => X.phEnd ℓ a - a

/-- the traversal -/
noncomputable def tl : List (TSg V) := segs X.P X.parP X.rkP X.isL X.r

/-- the first frame of segment `i` -/
noncomputable def stF (i : ℕ) : ℕ := (X.tl.take i).foldl (fun t g => t + X.dur g t) 1

/-- the start of the final phase -/
noncomputable def E0 : ℕ := X.stF X.tl.length

/-- the first frame of the phase of `ℓ` -/
noncomputable def aOf (ℓ : V) : ℕ := X.stF (X.tl.idxOf (TSg.ph ℓ))

/-- the phase of leader `ℓ` -/
noncomputable def kPh (ℓ : V) : GPh V :=
  ⟨alignUp (X.aOf ℓ) (X.PiK ℓ), (X.comp ℓ).card, (X.comp ℓ).card, ℓ, X.comp ℓ, X.parS, X.rkS⟩

/-- the final phase -/
noncomputable def ePh : GPh V := ⟨alignUp X.E0 (PiL X.dil X.sz), X.sz, 0, X.r, X.P, X.parP, X.rkP⟩

/-- the start frame of the sub-run of `ℓ` -/
noncomputable def bOf (ℓ : V) : ℕ := (X.kPh ℓ).A0 + 2 * X.PiK ℓ

/-- the halting frame -/
noncomputable def TL : ℕ := X.ePh.A0 + 2 * PiL X.dil X.sz

/-- the segment containing frame `φ` -/
noncomputable def idx (φ : ℕ) : ℕ := by
  classical exact ((range X.tl.length).filter (fun i => X.stF (i + 1) ≤ φ)).card

/-- the messages of segment `i` -/
noncomputable def segMsg (i : ℕ) (u w : V) (φ : ℕ) : Option (W3 V) := by
  classical exact match X.tl[i]? with
  | some (.tk a b) => if u = a ∧ w = b ∧ φ = X.stF i then some tokW else none
  | some (.ph ℓ) => phMsg X.E X.j X.dil (X.kPh ℓ) u w φ
  | none => none

/-- **The schedule**: the message from `u` to `w` in frame `φ`. -/
noncomputable def ML (u w : V) (φ : ℕ) : Option (W3 V) :=
  if 1 ≤ φ ∧ φ < X.E0 then X.segMsg (X.idx φ) u w φ
  else if X.E0 ≤ φ then phMsg X.E X.j X.dil X.ePh u w φ else none

/-- the sub-instance of the component of `ℓ` -/
noncomputable def J (ℓ : V) : Inst V :=
  ioInst X.N X.E X.j (X.comp ℓ).card (footprint X.E X.j (X.comp ℓ))

/-- the true local data of node `v` -/
structure LDOK (d : LD V) (v : V) : Prop where
  bP : d.bP = decide (v ∈ X.P)
  bS : d.bS = decide (v ∈ X.S)
  parP : d.parP = X.parP v
  parS : d.parS = X.parS v
  rtS : d.rtS = X.rtS v
  rtP : v ∈ X.P → d.rtP = X.r
  cnt : v ∈ X.S → d.cnt = (X.comp (X.rtS v)).card
  kP : d.kP = kidsOf X.P X.parP v
  kS : d.kS = kidsOf X.S X.parS v

/-- The hypotheses on the global data. -/
structure OK : Prop where
  hE : EmbValid X.N.G X.E
  hj : X.j < Fintype.card V
  SP : X.S ⊆ X.P
  Psz : X.P.card ≤ X.sz
  rP : X.r ∈ X.P
  parr : X.parP X.r = none
  Pmem : ∀ v ∈ X.P, ∀ u, X.parP v = some u → u ∈ X.P
  Prk : ∀ v ∈ X.P, ∀ u, X.parP v = some u → X.rkP u < X.rkP v
  Pdesc : desc X.P X.parP X.r = X.P
  Padj : ∀ v ∈ X.P, ∀ u, X.parP v = some u → X.N.G.Adj v u
  Smem : ∀ v ∈ X.S, ∀ u, X.parS v = some u → u ∈ X.S
  Srk : ∀ v ∈ X.S, ∀ u, X.parS v = some u → X.rkS u < X.rkS v
  Sroot : ∀ v ∈ X.S, ∀ u, X.parS v = some u → X.rtS u = X.rtS v
  Sself : ∀ v ∈ X.S, X.parS v = none → X.rtS v = v
  Sadj : ∀ v ∈ X.S, ∀ u, X.parS v = some u → X.N.G.Adj v u

end PCG

end APSP.Stoc.Congest
