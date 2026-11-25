import ApspStoc.Sec5bAux1

/-!
# Theorem 5.5, auxiliary file 2: specifications, local data and the algorithm

* `ThreshSpec`: the thresholded exact SSSP problem of the proof of Theorem 5.5 (every node within
  distance `Δ` of the virtual source learns its exact distance and a parent in a shortest-path
  tree; the other nodes output `none`).
* `Valid`: the invariant of a subproblem with offset `a` used in the participation argument.
* `GS`: the local state of an agent during one call of the recursion.
* `stageAlg`: a local computation preparing the input of a building block, the building block
  (run by a local call that drops the state, `sndF`), and a local computation storing its output;
  `stage_impl` is its Hoare rule.
* `recAlg`: the recursion (Steps 1–7 of the proof of Theorem 5.5).
-/

namespace APSP.Stoc

open APSP Finset

/-! ## Specifications -/

section Specs
variable {V : Type} [Fintype V] [DecidableEq V]

/-- `p` is a valid parent of `v` in a shortest-path tree from the virtual source: a neighbour in
`S` on a shortest path, or the label of a virtual edge of minimal weight. -/
def ParOK (N : WNet V) (S : Finset V) (w0 : V → Option (ℕ × V)) (v p : V) : Prop :=
  (p ∈ S ∧ N.G.Adj p v ∧ subDist N S w0 p + (N.w s(p, v) : ℕ∞) = subDist N S w0 v) ∨
  ∃ c, w0 v = some (c, p) ∧ (c : ℕ∞) = subDist N S w0 v

/-- Thresholded exact SSSP on `G[S]` from the virtual source with threshold `Δ`. -/
def ThreshSpec (N : WNet V) (S : Finset V) (w0 : V → Option (ℕ × V)) (Δ : ℕ)
    (o : V → Option (ℕ × V)) : Prop :=
  ∀ v ∈ S, (subDist N S w0 v ≤ Δ → ∃ d p, o v = some (d, p) ∧ (d : ℕ∞) = subDist N S w0 v ∧
      ParOK N S w0 v p) ∧
    (¬ subDist N S w0 v ≤ Δ → o v = none)

/-- The invariant of a subproblem at height `k` (threshold `2^k`) with offset `a`: virtual weights
are bounded by `W`; virtual edges do not undercut the true distances; every node has true
distance in `[a, a + 3·2^k]` (the paper's claim); nodes with true distance `≤ a + 2^k` have
`subDist = dist - a`; and `a` is a multiple of `2^k`. -/
structure Valid (N : WNet V) (s : V) (W k : ℕ) (S : Finset V) (w0 : V → Option (ℕ × V))
    (a : ℕ) : Prop where
  bnd : ∀ v c p, w0 v = some (c, p) → c ≤ W
  low : ∀ u ∈ S, ∀ c p, w0 u = some (c, p) → N.wdist s u ≤ c + a
  win : ∀ v ∈ S, a ≤ N.wdist s v ∧ N.wdist s v ≤ a + 3 * 2 ^ k
  ex : ∀ v ∈ S, N.wdist s v ≤ a + 2 ^ k → subDist N S w0 v + a = N.wdist s v
  dvd : 2 ^ k ∣ a

/-- The cost bound of a subproblem (participation argument). -/
noncomputable def costB (N : WNet V) (E : Overlays V) (j : ℕ) (s : V) (Q k : ℕ) (S : Finset V) (a : ℕ) :
    Prof V :=
  Prof.mk (Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) k a))
    (fun e => Q * ∑ v ∈ S, Nw (N.wdist s v) k a * hg N.G E j v e)
    (Q * (2 * ∑ v ∈ S, Nw (N.wdist s v) k a))

/-- The failure bound of a subproblem. -/
noncomputable def δB (N : WNet V) (s : V) (η : ℝ) (k : ℕ) (S : Finset V) (a : ℕ) : ℝ :=
  ((∑ v ∈ S, Nw (N.wdist s v) k a : ℕ) : ℝ) * (7 * η)

end Specs

/-! ## Local data -/

/-- The local state of an agent during a call of the recursion. -/
structure GS (V : Type) where
  inS : Bool
  w0 : Option (ℕ × V)
  y1 : Option (ℕ × V)
  o1 : Option (ℕ × V)
  up : V → Option (Msg V)
  recv : Multiset (Msg V)

section Local
variable {V : Type}

/-- `o = some (d, _)` with `d ≤ b` -/
def leB (b : ℕ) : Option (ℕ × V) → Bool
  | some (d, _) => decide (d ≤ b)
  | none => false

/-- membership in `S₁` (Step 3) -/
def GS.in1 (δ : ℕ) (st : GS V) : Bool := st.inS && leB (3 * δ) st.y1
/-- membership in `S₂` (Step 4) -/
def GS.in2 (δ : ℕ) (st : GS V) : Bool := st.in1 δ && st.o1.isSome
/-- membership in `S₁ \ S₂` -/
def GS.inT (δ : ℕ) (st : GS V) : Bool := st.in1 δ && !st.o1.isSome

/-- the message of a node of `S₁` to its aggregators (Step 5): `(0, d)` for `S₂`, `(1)` for
`S₁ \ S₂` -/
def upOf : Option (ℕ × V) → Msg V
  | some (d, _) => [Word.num 0, Word.num d]
  | none => [Word.num 1]

def GS.upMsg (δ : ℕ) (st : GS V) : Option (Msg V) := if st.in1 δ then some (upOf st.o1) else none

/-- the distance announced by a node of `S₂` -/
def s2val : Option (Msg V) → Option ℕ
  | some [Word.num 0, Word.num d] => some d
  | _ => none

/-- parse an aggregator's answer `(distance, predecessor)` -/
def parseDn : Msg V → Option (ℕ × V)
  | [Word.num c, Word.id u] => some (c, u)
  | _ => none

variable [Fintype V] [DecidableEq V]

/-- the Bellman–Ford candidates computed by the aggregator of `C` for the node `x`: the
neighbours `u ∈ S₂` of `x` along edges of `C`, with value `d(u) + w(u, x)` -/
noncomputable def aggCands (C : Finset (Sym2 V)) (wt : Sym2 V → ℕ) (up : V → Option (Msg V))
    (x : V) : Finset (ℕ × V) :=
  (univ.filter (fun u => s(u, x) ∈ C ∧ (s2val (up u)).isSome)).image
    (fun u => ((s2val (up u)).getD 0 + wt s(u, x), u))

/-- the aggregator's answer to a node `x ∈ S₁ \ S₂`: its best candidate -/
noncomputable def dnMsg (C : Finset (Sym2 V)) (wt : Sym2 V → ℕ) (up : V → Option (Msg V))
    (x : V) : Option (Msg V) :=
  if up x = some [Word.num 1] then
    (bestOf (aggCands C wt up x)).map (fun q => [Word.num q.1, Word.id q.2])
  else none

/-- the candidates of a node: its old virtual edge and the answers of its aggregators -/
noncomputable def nodeCands (w0 : Option (ℕ × V)) (recv : Multiset (Msg V)) : Finset (ℕ × V) :=
  w0.toFinset ∪ (recv.filterMap parseDn).toFinset

/-- the new virtual edge (Step 7: minimum, minus `δ`) of a node of `S₁ \ S₂` -/
noncomputable def GS.z2 (δ : ℕ) (st : GS V) : Option (ℕ × V) :=
  if st.inT δ then (bestOf (nodeCands st.w0 st.recv)).map (fun q => (q.1 - δ, q.2)) else none

/-- the output of a call: first recursion on `S₂`, second recursion (plus `δ`) on `S₁ \ S₂` -/
def finalOut (δ : ℕ) (st : GS V) (o2 : Option (ℕ × V)) : Option (ℕ × V) :=
  if st.in2 δ then st.o1 else if st.inT δ then o2.map (fun q => (q.1 + δ, q.2)) else none

def initGS (x : SubIn V) (y : Option (ℕ × V)) : GS V := ⟨x.1, x.2, y, none, fun _ => none, 0⟩

/-- base case output: the estimate, if it is `≤ 1` -/
def baseOut : Option (ℕ × V) → Option (ℕ × V)
  | some (d, p) => if d ≤ 1 then some (d, p) else none
  | none => none

end Local

/-! ## Local computations -/

noncomputable def initF : LocFn :=
  ⟨fun V => SubIn V × Option (ℕ × V), GS, fun _ _ _ _ _ t => initGS t.1 t.2⟩

noncomputable def baseF : LocFn :=
  ⟨fun V => SubIn V × Option (ℕ × V), fun V => Option (ℕ × V), fun _ _ _ _ _ t => baseOut t.2⟩

def in2F (δ : ℕ) : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V →
    (Bool × Bool) × Option (ℕ × V) := fun _ _ _ _ _ st => ((st.inS, st.in1 δ), st.w0)

def upd2F : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V →
    Option (ℕ × V) → GS V := fun _ _ _ _ _ st o => { st with o1 := o }

def in3F (δ : ℕ) : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V →
    Option (Msg V) := fun _ _ _ _ _ st => st.upMsg δ

def upd3F : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V →
    (V → Option (Msg V)) → GS V := fun _ _ _ _ _ st y => { st with up := y }

noncomputable def in4F : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) →
    GS V → V → Option (Msg V)
  | _, _, _, .inl _, _, _ => fun _ => none
  | _, _, _, .inr C, wt, st => dnMsg C wt st.up

def upd4F : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V →
    Multiset (Msg V) → GS V := fun _ _ _ _ _ st r => { st with recv := r }

noncomputable def in5F (δ : ℕ) : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V →
    (Sym2 V → ℕ) → GS V → (Bool × Bool) × Option (ℕ × V) :=
  fun _ _ _ _ _ st => ((st.inS, st.inT δ), st.z2 δ)

def upd5F (δ : ℕ) : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V →
    Option (ℕ × V) → Option (ℕ × V) := fun _ _ _ _ _ st o => finalOut δ st o

/-! ## Stages -/

/-- the local computation preparing the input of a stage -/
def stageInF (Pre α' : Type → Type)
    (In : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V → α' V) :
    LocFn :=
  ⟨fun V => Pre V × GS V, α', fun V _ _ g wt t => In V g wt t.2⟩

/-- the local computation storing the output of a stage -/
def stageUpdF (Pre α' β' γ : Type → Type)
    (Upd : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V → β' V → γ V) :
    LocFn :=
  ⟨fun V => ((Pre V × GS V) × α' V) × β' V, γ, fun V _ _ g wt t => Upd V g wt t.1.1.2 t.2⟩

/-- A stage: prepare the input of `P` locally from the current state, run `P` on it (a local call
dropping the state, which is kept for the update), store its output locally. -/
noncomputable def stageAlg (T : Toolkit) (Pre α' β' γ : Type → Type)
    (In : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V → α' V)
    (P : T.Alg)
    (Upd : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V → β' V → γ V) :
    T.Alg :=
  T.seq (T.loc (stageInF Pre α' In))
    (T.seq (T.call (sndF (fun V => Pre V × GS V) α') P) (T.loc (stageUpdF Pre α' β' γ Upd)))

theorem stage_impl (T : Toolkit) {Pre α' β' γ : Type → Type}
    {In : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V → α' V}
    {P : T.Alg}
    {Upd : ∀ (V : Type) [Fintype V] [DecidableEq V], Agent V → (Sym2 V → ℕ) → GS V → β' V → γ V}
    {V : Type} [Fintype V] [DecidableEq V] {N : WNet V} {E : Overlays V} {j sz : ℕ}
    {Pt : Finset V} (pre : Agent V → Pre V) (st : Agent V → GS V) (pin : Agent V → α' V)
    {R : (Agent V → β' V) → Prop} {p : Prof V} {δ : ℝ}
    (hin : ∀ g, In V g (lview N g) (st g) = pin g)
    (hP : T.Impl P N (.io E j sz Pt (α' V) (β' V) pin R) p δ) (hδ : 0 ≤ δ) :
    T.Impl (stageAlg T Pre α' β' γ In P Upd) N
      (.io E j sz Pt (Pre V × GS V) (γ V) (fun g => (pre g, st g))
        (fun out => ∃ o, R o ∧ ∀ g, out g = Upd V g (lview N g) (st g) (o g))) p δ := by
  refine T.mono (T.bind (q := p + 0) (δ' := δ + 0)
    (T.locR (stageInF Pre α' In) N E j sz Pt (fun g => (pre g, st g))) (fun y hy => ?_)
    (by rw [add_zero]; exact hδ)) ?_ ?_
  · have hy' : y = pin := funext (fun g => (hy g).trans (hin g))
    subst hy'
    refine T.bind (T.frameCall (Γ := fun V => Pre V × GS V) (fun g => (pre g, st g)) hP)
      (fun o ho => ?_) le_rfl
    exact T.weakenIO (fun out hout => ⟨o, ho, fun g => hout g⟩)
      (T.locR (stageUpdF Pre α' β' γ Upd) N E j sz Pt _)
  · simp
  · simp

/-! ## The algorithm -/

/-- one call of the recursion at height `k + 1` (threshold `2δ`, `δ = 2^k`), using the
algorithm `B` for the calls at height `k` -/
noncomputable def stepAlg (T : Toolkit) (k : ℕ) (Aa Am Au Ad B : T.Alg) : T.Alg :=
  T.seq (T.seq Aa (T.loc initF))
   (T.seq (stageAlg T SubIn (fun V => (Bool × Bool) × Option (ℕ × V)) (fun V => Option (ℕ × V))
      GS (in2F (2 ^ k)) (T.perComp (fun V => Option (ℕ × V)) (fun V => Option (ℕ × V)) Am B)
      upd2F)
    (T.seq (stageAlg T (fun V => SubIn V × GS V) (fun V => Option (Msg V))
        (fun V => V → Option (Msg V)) GS (in3F (2 ^ k)) Au upd3F)
     (T.seq (stageAlg T (fun V => (SubIn V × GS V) × GS V) (fun V => V → Option (Msg V))
          (fun V => Multiset (Msg V)) GS in4F Ad upd4F)
       (stageAlg T (fun V => ((SubIn V × GS V) × GS V) × GS V)
          (fun V => (Bool × Bool) × Option (ℕ × V)) (fun V => Option (ℕ × V))
          (fun V => Option (ℕ × V)) (in5F (2 ^ k))
          (T.perComp (fun V => Option (ℕ × V)) (fun V => Option (ℕ × V)) Am B) (upd5F (2 ^ k))))))

/-- the recursion: height `0` is the base case (threshold `1`) -/
noncomputable def recAlg (T : Toolkit) (Aa Am Au Ad : T.Alg) : ℕ → T.Alg
  | 0 => T.seq Aa (T.loc baseF)
  | k + 1 => stepAlg T k Aa Am Au Ad (recAlg T Aa Am Au Ad k)

/-- the virtual source of the top level: one virtual edge `(σ, s)` of weight `0` -/
def topW0 {V : Type} [DecidableEq V] (s : V) : V → Option (ℕ × V) :=
  fun v => if v = s then some (0, s) else none

noncomputable def topInF : LocFn :=
  ⟨fun V => V, SubIn, fun V _ _ g _ s => match g with
    | .inl v => (true, topW0 s v)
    | .inr _ => (false, none)⟩

noncomputable def topOutF : LocFn :=
  ⟨fun V => (V × SubIn V) × Option (ℕ × V), fun V => ℕ × V, fun _ _ _ _ _ t => t.2.getD (0, t.1.1)⟩

/-- Theorem 5.5's algorithm: run the recursion at height `L` on `V` from `s` (a local call dropping
`s`, which is kept for the output). -/
noncomputable def topAlg (T : Toolkit) (L : ℕ) (Aa Am Au Ad : T.Alg) : T.Alg :=
  T.seq (T.loc topInF)
    (T.seq (T.call (sndF (fun V => V) SubIn) (recAlg T Aa Am Au Ad L)) (T.loc topOutF))

end APSP.Stoc
