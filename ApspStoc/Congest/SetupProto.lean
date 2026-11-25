import ApspStoc.Congest.Tasks

/-!
# Cluster setup in CONGEST: the protocol

The protocol `setupProto V D` solves the cluster setup task on `clInst0 N C` whenever `D` bounds
the diameter of the cluster. It is a uniform state machine driven by a round counter; all phase
boundaries are functions of the public number `D` and, from phase G on, of `n_C`, which every
node learns before it is needed.

* **Phase F, rounds `[0, D)`: leader election and BFS tree.** Every node floods the largest index
  (`Fintype.equivFin`) it has seen. When the maximum increases, the node takes as parent one of
  the neighbours that sent the new maximum. After `D` rounds, every node knows the leader `ℓ` (the
  node of `C` of largest index) and its parent in a BFS tree rooted at `ℓ`.
* **Phase C, rounds `[D, 2D + 1)`: counting.** Every round, every node sends to its parent
  `1 + (sum of the latest values received from its children)`. After `D + 1` rounds the values
  are stable and the root knows `n_C`. Every node also knows its children (the senders).
* **Phase B, rounds `[2D + 1, 3D + 1)`: broadcast of `n_C`** by flooding the maximum.
* **Phase G, rounds `[3D + 1, tG)`, `tG = 3D + 1 + 2D · 2n_C`: gossip of the degree table on the
  tree.** `2D` windows of `2n_C` rounds. In a window, every node sends its whole current set of
  `(ID, degree)` pairs (two words per pair) to its parent and its children; at the end of the
  window it adds all pairs received. After `2D` windows every node knows all pairs.
* **Phase A, round `tG`: the aggregator set.** No messages. Every node computes `A(C)` from the
  table (`aggT`, which is `aggSet C` on the true table, `aggSet_eq_aggT`). A node of `A(C)` keeps
  its own ports (read from its local view at the start) as its port set; the other nodes empty it.
* **Phase H, rounds `[tG + 1, tH)`, `tH = tG + 1 + 2D · 4n_C`: gossip of the ports of `A(C)` on the
  tree**, exactly as in phase G, with `2D` windows of `4n_C` rounds and two words (`id`, `edge`)
  per port; there are fewer than `2n_C` ports of `A(C)`. After `2D` windows every node knows
  `portsA C`.
* **Halting** at round `tH`, with output (leader, parent, table, `portsA C`). A node of degree `0`
  (not a node of `C`; it has no edges in the instance) halts at once.

Sends are proper: a node sends only to its neighbours by its local view (`suNb`: the incident
edges of `C`, which have non-zero weight), i.e. along edges of the instance (`suSendG`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

/-- Local state of the cluster-setup protocol. -/
structure SetupSt (V : Type) : Type 1 where
  /-- round counter -/
  r : ℕ
  /-- own identifier -/
  me : V
  /-- largest index seen (leader election) -/
  m : ℕ
  /-- parent pointer -/
  par : Option V
  /-- latest subtree counts received from the children -/
  lat : V → ℕ
  /-- the number of nodes of the cluster (once known) -/
  nc : ℕ
  /-- the (ID, degree) pairs known at the start of the current window -/
  S : Finset (V × ℕ)
  /-- the words received in the current window, per sender -/
  rcv : V → List (Word V)
  /-- the ports of `A(C)` known at the start of the current window of phase H (before phase A:
  the node's own ports) -/
  PS : Finset (Port V)

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Auxiliary functions -/

/-- the index of a node -/
noncomputable def suIdx (u : V) : ℕ := (Fintype.equivFin V u : ℕ)

/-- the node of a given index -/
noncomputable def suDec (k : ℕ) : Option V :=
  if h : k < Fintype.card V then some ((Fintype.equivFin V).symm ⟨k, h⟩) else none

/-- a deterministic choice of an element -/
noncomputable def suPick (s : Finset V) : Option V := s.toList.head?

/-- the number carried by a word (`0` for other words) -/
def numOf : Option (Word V) → ℕ
  | some (.num k) => k
  | _ => 0

/-- encoding of a list of pairs as words (two words per pair) -/
def encW : List (V × ℕ) → List (Word V)
  | [] => []
  | p :: l => .id p.1 :: .num p.2 :: encW l

/-- decoding of a list of words into pairs -/
def decW : List (Word V) → List (V × ℕ)
  | .id a :: .num d :: l => (a, d) :: decW l
  | _ => []

/-- encoding of a list of ports as words (two words per port) -/
def encP : List (Port V) → List (Word V)
  | [] => []
  | p :: l => .id p.1 :: .edge p.2 :: encP l

/-- decoding of a list of words into ports -/
def decP : List (Word V) → List (Port V)
  | .id a :: .edge e :: l => (a, e) :: decP l
  | _ => []

/-- the end of phase G (and the round of phase A) -/
def tG (D nc : ℕ) : ℕ := 3 * D + 1 + 2 * D * (2 * nc)

/-- the halting round (the end of phase H) -/
def tH (D nc : ℕ) : ℕ := tG D nc + 1 + 2 * D * (4 * nc)

/-! ### The aggregator set from the degree table -/

/-- the degree function of a table of (ID, degree) pairs (`0` for IDs not in the table) -/
def degT (T : Finset (V × ℕ)) (u : V) : ℕ := (T.filter (fun p => p.1 = u)).sup Prod.snd

/-- the aggregator set computed from a table of (ID, degree) pairs, by the same choice as
`aggSet` (the nodes are the IDs of the table, the degrees are read from the table) -/
noncomputable def aggT (T : Finset (V × ℕ)) : Finset V :=
  Classical.epsilon (fun A => IsAggSet (T.image Prod.fst) A (degT T))

lemma image_fst_table (C : Finset (Sym2 V)) :
    ((nodes C).image (fun u => (u, degIn C u))).image Prod.fst = nodes C := by
  ext u
  simp

/-- The degree function of the true table is the degree function of the cluster. -/
lemma degT_table (C : Finset (Sym2 V)) :
    degT ((nodes C).image (fun u => (u, degIn C u))) = degIn C := by
  funext u
  unfold degT
  by_cases hu : u ∈ nodes C
  · have : ((nodes C).image (fun u => (u, degIn C u))).filter (fun p => p.1 = u) =
        {(u, degIn C u)} := by
      ext p
      simp only [mem_filter, mem_image, mem_singleton]
      constructor
      · rintro ⟨⟨a, _, rfl⟩, h⟩
        simp only at h
        subst h
        rfl
      · rintro rfl
        exact ⟨⟨u, hu, rfl⟩, rfl⟩
    rw [this, sup_singleton]
  · have : ((nodes C).image (fun u => (u, degIn C u))).filter (fun p => p.1 = u) = ∅ := by
      rw [filter_eq_empty_iff]
      intro p hp hpu
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
      exact hu (hpu ▸ ha)
    rw [this, sup_empty, degIn_eq_zero hu]
    rfl

/-- **The aggregator set is a function of the degree table**: every node that knows the
(ID, degree) pairs of all nodes of `C` computes `A(C)` locally. -/
theorem aggSet_eq_aggT (C : Finset (Sym2 V)) :
    aggSet C = aggT ((nodes C).image (fun u => (u, degIn C u))) := by
  unfold aggT aggSet
  rw [image_fst_table, degT_table]

lemma suIdx_lt (u : V) : suIdx u < Fintype.card V := (Fintype.equivFin V u).isLt

lemma suIdx_inj : Function.Injective (suIdx : V → ℕ) := fun _ _ h =>
  (Fintype.equivFin V).injective (Fin.ext h)

lemma suDec_suIdx (u : V) : suDec (suIdx u) = some u := by
  simp [suDec, suIdx]

lemma suPick_mem {s : Finset V} {u : V} (h : suPick s = some u) : u ∈ s :=
  mem_toList.1 (List.mem_of_mem_head? h)

lemma suPick_isSome {s : Finset V} (h : s.Nonempty) : (suPick s).isSome := by
  unfold suPick
  rw [List.isSome_head?]
  intro h0
  rw [toList_eq_nil] at h0
  exact h.ne_empty h0

@[simp] lemma encW_nil : encW ([] : List (V × ℕ)) = [] := rfl
@[simp] lemma encW_cons (p : V × ℕ) (l : List (V × ℕ)) :
    encW (p :: l) = .id p.1 :: .num p.2 :: encW l := rfl

lemma length_encW (l : List (V × ℕ)) : (encW l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [ih]; ring

lemma decW_encW (l : List (V × ℕ)) : decW (encW l) = l := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [decW, ih]

@[simp] lemma encP_nil : encP ([] : List (Port V)) = [] := rfl
@[simp] lemma encP_cons (p : Port V) (l : List (Port V)) :
    encP (p :: l) = .id p.1 :: .edge p.2 :: encP l := rfl

lemma length_encP (l : List (Port V)) : (encP l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [ih]; ring

lemma decP_encP (l : List (Port V)) : decP (encP l) = l := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [decP, ih]

/-- the words of a port list are valid (they carry no numbers) -/
lemma wordOK_of_mem_encP {n : ℕ} {l : List (Port V)} {w : Word V} (hw : w ∈ encP l) :
    WordOK n w := by
  induction l with
  | nil => simp at hw
  | cons p l ih =>
    simp only [encP_cons, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · trivial
    · trivial
    · exact ih hw

lemma wordOK_of_mem_encW {n : ℕ} {l : List (V × ℕ)} (hl : ∀ p ∈ l, p.2 ≤ n + 3) {w : Word V}
    (hw : w ∈ encW l) : WordOK n w := by
  induction l with
  | nil => simp at hw
  | cons p l ih =>
    simp only [encW_cons, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · trivial
    · exact hl p (by simp)
    · exact ih (fun q hq => hl q (by simp [hq])) hw

/-! ## The protocol -/

/-- the degree of a node, read from its local view -/
noncomputable def suDeg (c : NCtx V) : ℕ :=
  match c.view (.inl c.me) with
  | some f => (univ.filter (fun e : Sym2 V => f e ≠ 0)).card
  | none => 0

/-- the ports of the node, read from its local view (its incident edges of non-zero weight) -/
noncomputable def suPorts (c : NCtx V) : Finset (Port V) :=
  match c.view (.inl c.me) with
  | some f => (univ.filter (fun e : Sym2 V => f e ≠ 0)).image (fun e => (c.me, e))
  | none => ∅

/-- initial state -/
noncomputable def suInit (c : NCtx V) : SetupSt V :=
  ⟨0, c.me, suIdx c.me, none, fun _ => 0, 0, {(c.me, suDeg c)}, fun _ => [], suPorts c⟩

/-- `u` is a neighbour of the node by its local view: the edge to `u` has a non-zero weight -/
def suNb (c : NCtx V) (u : V) : Prop :=
  match c.view (.inl c.me) with
  | some f => f s(c.me, u) ≠ 0
  | none => False

/-- the message to `u`, before the neighbour test (in phases F and B it is the same word for
every `u`; in phases G and H a node sends to its parent and its children only) -/
noncomputable def suSend (D : ℕ) (s : SetupSt V) (u : V) : Option (Word V) :=
  if s.r < D then some (.num s.m)
  else if s.r < 2 * D + 1 then (if s.par = some u then some (.num (1 + ∑ w, s.lat w)) else none)
  else if s.r < 3 * D + 1 then some (.num s.nc)
  else if s.r < tG D s.nc then
    (if s.par = some u ∨ s.lat u ≠ 0 then
      (encW s.S.toList)[(s.r - (3 * D + 1)) % (2 * s.nc)]? else none)
  else if s.r = tG D s.nc then none
  else if s.par = some u ∨ s.lat u ≠ 0 then
    (encP s.PS.toList)[(s.r - (tG D s.nc + 1)) % (4 * s.nc)]?
  else none

/-- phase F: flood the largest index, adopt a parent when it increases -/
noncomputable def recvF (s : SetupSt V) (inb : V → Option (Word V)) : SetupSt V :=
  if s.m < univ.sup (fun u => numOf (inb u)) then
    { s with
      r := s.r + 1
      m := univ.sup (fun u => numOf (inb u))
      par := suPick (univ.filter (fun u => inb u = some (.num (univ.sup (fun u => numOf (inb u)))))) }
  else { s with r := s.r + 1 }

/-- phase C: record the counts of the children -/
noncomputable def recvC (s : SetupSt V) (inb : V → Option (Word V)) : SetupSt V :=
  { s with
    r := s.r + 1
    lat := fun u => numOf (inb u)
    nc := if s.par = none then 1 + ∑ u, numOf (inb u) else 0 }

/-- phase B: flood `n_C` -/
noncomputable def recvB (s : SetupSt V) (inb : V → Option (Word V)) : SetupSt V :=
  { s with r := s.r + 1, nc := max s.nc (univ.sup (fun u => numOf (inb u))) }

/-- phase G: record the words received; at the end of a window, add the pairs received -/
noncomputable def recvG (D : ℕ) (s : SetupSt V) (inb : V → Option (Word V)) : SetupSt V :=
  if (s.r - (3 * D + 1)) % (2 * s.nc) + 1 = 2 * s.nc then
    { s with
      r := s.r + 1
      S := s.S ∪ univ.biUnion (fun u => (decW (s.rcv u ++ (inb u).toList)).toFinset)
      rcv := fun _ => [] }
  else { s with r := s.r + 1, rcv := fun u => s.rcv u ++ (inb u).toList }

/-- phase A: compute `A(C)` from the table; a node of `A(C)` keeps its own ports, the others
start phase H with no port -/
noncomputable def recvA (s : SetupSt V) : SetupSt V :=
  { s with r := s.r + 1, PS := if s.me ∈ aggT s.S then s.PS else ∅ }

/-- phase H: record the words received; at the end of a window, add the ports received -/
noncomputable def recvH (D : ℕ) (s : SetupSt V) (inb : V → Option (Word V)) : SetupSt V :=
  if (s.r - (tG D s.nc + 1)) % (4 * s.nc) + 1 = 4 * s.nc then
    { s with
      r := s.r + 1
      PS := s.PS ∪ univ.biUnion (fun u => (decP (s.rcv u ++ (inb u).toList)).toFinset)
      rcv := fun _ => [] }
  else { s with r := s.r + 1, rcv := fun u => s.rcv u ++ (inb u).toList }

/-- the state transition -/
noncomputable def suRecv (D : ℕ) (s : SetupSt V) (inb : V → Option (Word V)) : SetupSt V :=
  if s.r < D then recvF s inb
  else if s.r < 2 * D + 1 then recvC s inb
  else if s.r < 3 * D + 1 then recvB s inb
  else if s.r < tG D s.nc then recvG D s inb
  else if s.r = tG D s.nc then recvA s
  else recvH D s inb

/-- the output: leader, parent, all pairs, the ports of `A(C)`; at round `tH D n_C` (at once for
a node of degree `0`, which knows the pair `(me, 0)`) -/
noncomputable def suOut (D : ℕ) (s : SetupSt V) : Option (Agent V → Option Mem) :=
  if (s.me, 0) ∈ s.S ∨ tH D s.nc ≤ s.r then
    some (fun _ => some ⟨SetupOut V, ((suDec s.m).getD s.me, s.par, s.S, s.PS)⟩)
  else none

open Classical in
/-- the message to `u`: sent only to neighbours (proper sends) -/
noncomputable def suSendG (D : ℕ) (c : NCtx V) (s : SetupSt V) (u : V) : Option (Word V) :=
  if suNb c u then suSend D s u else none

/-- **The cluster-setup protocol** with public diameter bound `D`. -/
@[reducible] noncomputable def setupProto (V : Type) [Fintype V] [DecidableEq V] (D : ℕ) : Proto V where
  S := SetupSt V
  Ω := Unit
  init c _ _ := suInit c
  send c s u := suSendG D c s u
  recv _ s inb := suRecv D s inb
  out s := suOut D s

/-! ## Reduction lemmas -/

lemma suSendG_of_nb {D : ℕ} {c : NCtx V} {u : V} (h : suNb c u) (s : SetupSt V) :
    suSendG D c s u = suSend D s u := by
  classical
  unfold suSendG; rw [ite_eq_left h]

lemma suSendG_isSome {D : ℕ} {c : NCtx V} {s : SetupSt V} {u : V}
    (h : (suSendG D c s u).isSome) : suNb c u ∧ (suSend D s u).isSome := by
  classical
  unfold suSendG at h
  by_cases hn : suNb c u
  · rw [ite_eq_left hn] at h; exact ⟨hn, h⟩
  · rw [ite_eq_right hn] at h; simp at h

lemma suRecv_F {D : ℕ} {s : SetupSt V} (h : s.r < D) (inb : V → Option (Word V)) :
    suRecv D s inb = recvF s inb := by
  simp [suRecv, h]

lemma suRecv_C {D : ℕ} {s : SetupSt V} (h1 : D ≤ s.r) (h2 : s.r < 2 * D + 1)
    (inb : V → Option (Word V)) : suRecv D s inb = recvC s inb := by
  simp [suRecv, h2, not_lt.2 h1]

lemma suRecv_B {D : ℕ} {s : SetupSt V} (h1 : 2 * D + 1 ≤ s.r) (h2 : s.r < 3 * D + 1)
    (inb : V → Option (Word V)) : suRecv D s inb = recvB s inb := by
  simp [suRecv, h2, not_lt.2 h1, show ¬ s.r < D by omega]

lemma suRecv_G {D : ℕ} {s : SetupSt V} (h1 : 3 * D + 1 ≤ s.r) (h2 : s.r < tG D s.nc)
    (inb : V → Option (Word V)) : suRecv D s inb = recvG D s inb := by
  simp [suRecv, not_lt.2 h1, h2, show ¬ s.r < D by omega, show ¬ s.r < 2 * D + 1 by omega]

lemma suRecv_A {D : ℕ} {s : SetupSt V} (h : s.r = tG D s.nc) (inb : V → Option (Word V)) :
    suRecv D s inb = recvA s := by
  simp [suRecv, h, show ¬ tG D s.nc < D by unfold tG; omega,
    show ¬ tG D s.nc < 2 * D + 1 by unfold tG; omega,
    show ¬ tG D s.nc < 3 * D + 1 by unfold tG; omega]

lemma suRecv_H {D : ℕ} {s : SetupSt V} (h : tG D s.nc < s.r) (inb : V → Option (Word V)) :
    suRecv D s inb = recvH D s inb := by
  have h1 : 3 * D + 1 ≤ tG D s.nc := by unfold tG; omega
  simp [suRecv, show ¬ s.r < D by omega, show ¬ s.r < 2 * D + 1 by omega,
    show ¬ s.r < 3 * D + 1 by omega, show ¬ s.r < tG D s.nc by omega, show s.r ≠ tG D s.nc by omega]

lemma suSend_F {D : ℕ} {s : SetupSt V} (h : s.r < D) (u : V) :
    suSend D s u = some (.num s.m) := by
  simp [suSend, h]

lemma suSend_C {D : ℕ} {s : SetupSt V} (h1 : D ≤ s.r) (h2 : s.r < 2 * D + 1) (u : V) :
    suSend D s u = if s.par = some u then some (.num (1 + ∑ w, s.lat w)) else none := by
  simp [suSend, h2, not_lt.2 h1]

lemma suSend_B {D : ℕ} {s : SetupSt V} (h1 : 2 * D + 1 ≤ s.r) (h2 : s.r < 3 * D + 1) (u : V) :
    suSend D s u = some (.num s.nc) := by
  simp [suSend, h2, not_lt.2 h1, show ¬ s.r < D by omega]

lemma suSend_G {D : ℕ} {s : SetupSt V} (h1 : 3 * D + 1 ≤ s.r) (h2 : s.r < tG D s.nc) (u : V) :
    suSend D s u = if s.par = some u ∨ s.lat u ≠ 0 then
      (encW s.S.toList)[(s.r - (3 * D + 1)) % (2 * s.nc)]? else none := by
  simp [suSend, not_lt.2 h1, h2, show ¬ s.r < D by omega, show ¬ s.r < 2 * D + 1 by omega]

lemma suSend_A {D : ℕ} {s : SetupSt V} (h : s.r = tG D s.nc) (u : V) : suSend D s u = none := by
  simp [suSend, h, show ¬ tG D s.nc < D by unfold tG; omega,
    show ¬ tG D s.nc < 2 * D + 1 by unfold tG; omega,
    show ¬ tG D s.nc < 3 * D + 1 by unfold tG; omega]

lemma suSend_H {D : ℕ} {s : SetupSt V} (h : tG D s.nc < s.r) (u : V) :
    suSend D s u = if s.par = some u ∨ s.lat u ≠ 0 then
      (encP s.PS.toList)[(s.r - (tG D s.nc + 1)) % (4 * s.nc)]? else none := by
  have h1 : 3 * D + 1 ≤ tG D s.nc := by unfold tG; omega
  simp [suSend, show ¬ s.r < D by omega, show ¬ s.r < 2 * D + 1 by omega,
    show ¬ s.r < 3 * D + 1 by omega, show ¬ s.r < tG D s.nc by omega, show s.r ≠ tG D s.nc by omega]

/-! ## Runs on a cluster instance -/

section Run

variable (N : WNet V) (C : Finset (Sym2 V)) (D : ℕ)

/-- The communication graph of a cluster task is the graph of the cluster when `C ⊆ E(G)`. -/
lemma clG_eq (hCG : C ⊆ N.G.edgeFinset) : clG N C = clGraph C := by
  ext u v
  simp only [clG, SimpleGraph.inf_adj]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := hCG h.2
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this

lemma clInst0_adj (hCG : C ⊆ N.G.edgeFinset) {u v : V} :
    (clInst0 N C).G.Adj u v ↔ (clGraph C).Adj u v := by
  show (clG N C).Adj u v ↔ _
  rw [clG_eq N C hCG]

lemma noLoops_of_sub (hCG : C ⊆ N.G.edgeFinset) : NoLoops C := by
  intro e he hd
  have := hCG he
  rw [SimpleGraph.mem_edgeFinset] at this
  exact N.G.not_isDiag_of_mem_edgeSet this hd

/-- In a cluster instance, a node's neighbours by its local view are its neighbours in `C`. -/
lemma suNb_clInst0 (hCG : C ⊆ N.G.edgeFinset) {u v : V} :
    suNb ((clInst0 N C).ctx u) v ↔ (clGraph C).Adj u v := by
  classical
  have h2 : ((clInst0 N C).ctx u).view (.inl u) = some (clView N C u) := by
    simp [clInst0, clInstP]
  unfold suNb
  rw [show ((clInst0 N C).ctx u).me = u from rfl, h2]
  show clView N C u s(u, v) ≠ 0 ↔ _
  unfold clView
  split_ifs with h
  · have hw := N.wpos _ (by have := hCG h.1; rwa [SimpleGraph.mem_edgeFinset] at this)
    exact ⟨fun _ => clGraph_adj_of_mem (noLoops_of_sub N C hCG) h.1, fun _ => by omega⟩
  · exact ⟨fun h' => absurd rfl h', fun h' => absurd ⟨h'.2, Sym2.mem_mk_left u v⟩ h⟩

variable {N C D}

/-- A message is the word sent, if the sender is active and adjacent and the word is valid. -/
lemma msg_setup_of_adj (hCG : C ⊆ N.G.edgeFinset) (σ : V → SetupSt V) {u v : V}
    (hadj : (clGraph C).Adj u v) (hout : suOut D (σ u) = none)
    (hok : ∀ w, suSend D (σ u) v = some w → WordOK (Fintype.card V) w) :
    msg (setupProto V D) (clInst0 N C) σ u v = suSend D (σ u) v := by
  classical
  have hadj' : (clInst0 N C).G.Adj u v := (clInst0_adj N C hCG).2 hadj
  unfold msg
  rw [ite_eq_left ⟨hadj', hout⟩]
  show (match suSendG D ((clInst0 N C).ctx u) (σ u) v with
    | some w => if WordOK (Fintype.card V) w then some w else none
    | none => none) = _
  rw [suSendG_of_nb ((suNb_clInst0 N C hCG).2 hadj)]
  show (match suSend D (σ u) v with
    | some w => if WordOK (Fintype.card V) w then some w else none
    | none => none) = _
  cases h : suSend D (σ u) v with
  | none => rfl
  | some w => simp [hok w h]

lemma msg_setup_of_not_adj (hCG : C ⊆ N.G.edgeFinset) (σ : V → SetupSt V) {u v : V}
    (hadj : ¬ (clGraph C).Adj u v) : msg (setupProto V D) (clInst0 N C) σ u v = none := by
  classical
  have hadj' : ¬ (clInst0 N C).G.Adj u v := fun h => hadj ((clInst0_adj N C hCG).1 h)
  unfold msg
  rw [ite_eq_right (fun h => hadj' h.1)]

/-- **One round of the run**, given the states of all nodes of `C`. -/
lemma st_setup_succ (hCG : C ⊆ N.G.edgeFinset) {x : Agent V → Mem} {ω : V → Unit} {t : ℕ}
    (E : V → SetupSt V) (hE : ∀ u ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω t u = E u)
    (hout : ∀ u ∈ nodes C, suOut D (E u) = none)
    (hok : ∀ u v, (clGraph C).Adj u v → ∀ w, suSend D (E u) v = some w →
      WordOK (Fintype.card V) w)
    {v : V} (hv : v ∈ nodes C) :
    st (setupProto V D) (clInst0 N C) x ω (t + 1) v =
      suRecv D (E v) (fun u => if (clGraph C).Adj u v then suSend D (E u) v else none) := by
  rw [st_succ]
  unfold step
  have h1 : (setupProto V D).out (st (setupProto V D) (clInst0 N C) x ω t v) = none := by
    show suOut D _ = none
    rw [hE v hv]; exact hout v hv
  rw [h1]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
  show suRecv D _ _ = _
  rw [hE v hv]
  congr 1
  funext u
  by_cases hadj : (clGraph C).Adj u v
  · have hu : u ∈ nodes C := mem_nodes_of_adj hadj
    rw [ite_eq_left hadj, msg_setup_of_adj hCG _ hadj (by rw [hE u hu]; exact hout u hu)
      (by rw [hE u hu]; exact hok u v hadj), hE u hu]
  · rw [ite_eq_right hadj, msg_setup_of_not_adj hCG _ hadj]

/-- The initial state of a node. -/
lemma st_setup_zero {x : Agent V → Mem} {ω : V → Unit} (v : V) :
    st (setupProto V D) (clInst0 N C) x ω 0 v = suInit ((clInst0 N C).ctx v) := rfl

/-! ### Counting messages -/

/-- At most two directed pairs give the same edge. -/
lemma card_filter_sym2_le_two (e : Sym2 V) (A : Finset (V × V)) :
    (A.filter (fun uv => s(uv.1, uv.2) = e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    calc (A.filter (fun uv => s(uv.1, uv.2) = s(a, b))).card ≤ ({(a, b), (b, a)} : Finset (V × V)).card := by
          apply card_le_card
          intro uv huv
          rw [mem_filter, Sym2.eq_iff] at huv
          rcases huv.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp [Prod.ext_iff, h1, h2]
          · simp [Prod.ext_iff, h1, h2]
      _ ≤ 2 := card_le_two

/-- Messages travel along edges of `C` only. -/
lemma mem_sentSet_setup (hCG : C ⊆ N.G.edgeFinset) {σ : V → SetupSt V} {uv : V × V}
    (h : uv ∈ sentSet (setupProto V D) (clInst0 N C) σ) : (clGraph C).Adj uv.1 uv.2 := by
  classical
  unfold sentSet at h
  rw [mem_filter] at h
  by_contra hadj
  have := h.2
  rw [msg_setup_of_not_adj hCG σ hadj] at this
  exact absurd this (by simp)

/-- At most `2|C|` messages per round. -/
lemma card_sentSet_le (hCG : C ⊆ N.G.edgeFinset) (σ : V → SetupSt V) :
    (sentSet (setupProto V D) (clInst0 N C) σ).card ≤ 2 * C.card := by
  classical
  set A := sentSet (setupProto V D) (clInst0 N C) σ
  have h1 := card_le_mul_card_image (f := fun uv : V × V => s(uv.1, uv.2)) A 2
    (fun e _ => card_filter_sym2_le_two e A)
  refine h1.trans (Nat.mul_le_mul_left _ (card_le_card ?_))
  intro e he
  obtain ⟨uv, huv, rfl⟩ := mem_image.1 he
  exact (mem_sentSet_setup hCG huv).2

/-- At most two messages per round over an edge of `C`, none over other edges. -/
lemma card_sentSet_filter_le (hCG : C ⊆ N.G.edgeFinset) (σ : V → SetupSt V) (e : Sym2 V) :
    ((sentSet (setupProto V D) (clInst0 N C) σ).filter (fun uv => s(uv.1, uv.2) = e)).card ≤
      if e ∈ C then 2 else 0 := by
  classical
  split_ifs with he
  · exact card_filter_sym2_le_two e _
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    intro uv huv heq
    exact he (heq ▸ (mem_sentSet_setup hCG huv).2)

lemma loadUpTo_setup_le (hCG : C ⊆ N.G.edgeFinset) {x : Agent V → Mem} {ω : V → Unit} (t : ℕ)
    (e : Sym2 V) :
    loadUpTo (setupProto V D) (clInst0 N C) x ω t e ≤ if e ∈ C then 2 * t else 0 := by
  classical
  unfold loadUpTo
  calc ∑ s ∈ range t, ((sentSet (setupProto V D) (clInst0 N C)
          (st (setupProto V D) (clInst0 N C) x ω s)).filter (fun uv => s(uv.1, uv.2) = e)).card
      ≤ ∑ _s ∈ range t, (if e ∈ C then 2 else 0) := by
        refine sum_le_sum (fun s _ => ?_)
        convert card_sentSet_filter_le hCG (st (setupProto V D) (clInst0 N C) x ω s) e
    _ = if e ∈ C then 2 * t else 0 := by
        split_ifs <;> simp [mul_comm]

end Run

end APSP.Stoc.Congest
