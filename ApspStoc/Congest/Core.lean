import ApspStoc.Defs

/-!
# An executable synchronous CONGEST semantics

This file gives the abstract judgement `Impl` of `Toolkit.lean` a concrete meaning.

* **Nodes and rounds.** The nodes are the elements of `V`. Computation proceeds in synchronous
  rounds: in every round each node that has not halted sends at most one message to each
  neighbour, then receives the messages sent to it and updates its state. A halted node neither
  sends nor changes its state.
* **Bandwidth.** A message is a single `Word V` (an ID, an edge, or a number), and numbers are at
  most `n + 3`, so a message has `O(log n)` bits. A word that violates the bound is dropped by the
  network.
* **Proper sends.** A participant may send only along edges of the instance's communication graph
  (`ProperUpTo`): a run in which a participant that has not halted tries to send to any other node
  *fails*. (The network still delivers only along edges, `msg`.) This matters for composite runs:
  a sub-protocol run on a sub-instance inside a larger run must not reach nodes outside its
  instance, which are idle or run other copies; in a successful run it does not.
* **Uniformity.** A protocol (`Proto V`) is one program for all nodes. Its transition functions see
  only the node's local context `NCtx V`. It never sees the network. An algorithm (`CAlg`, in
  `Comb.lean`) is a protocol for every node set `V`, so it does not depend on the network either;
  knowing `V` means knowing the set of all IDs (and `n`).
* **Knowledge** (`NCtx V`). A node knows its identifier, the local weight view of the agents it
  simulates, the public numbers of the task, its cluster slices `C ∩ inc(v)` (`sl`), and the
  embedded aggregator paths through it (`emb`). Nodes cannot know a cluster as a whole edge set
  (establishing that would cost `Σ_C n_C·m_C` messages), so embedded paths are keyed by their
  source `u` and a *key edge* `k`: `emb j u k = some path` iff the node lies on the path `path` of
  `u` to the aggregator in overlay `j` of a cluster `C ∋ u` whose key edge at `u` is `k`
  (`k = (srcPort C u).2`; distinct clusters have distinct key edges, as they are edge-disjoint).
* **Randomness.** Every node draws a private seed uniformly from a finite type `Ω`, independently of
  the other nodes. A run is a deterministic function of the seeds.
* **Agents.** Data is attached to *agents*: the physical nodes and the virtual aggregators. An agent
  is simulated by its *host* (a node), which holds the agent's data. Agent data is dynamically
  typed (`Mem := Σ T : Type, T`).
* **Instances.** An instance `Inst V` fixes the communication graph, the *participants* (the nodes
  taking part; non-participants have no incident edges), the hosts of the agents, and every node's
  local context.
* **Success.** A run *succeeds* within a cost profile `p` and postcondition `Q` if, for some round
  `t ≤ p.rounds`:
  - all participants halt at round `t` exactly, none earlier;
  - before round `t`, every participant sends only to its neighbours in the instance's graph;
  - at most `p.msgs` messages were sent, and at most `p.load e` over every edge `e`;
  - the outputs of the simulated agents satisfy `Q`.

  Simultaneous halting is what makes sequential composition meaningful: the next protocol starts
  at all nodes in the same round. It forces round budgets to be computable from what the nodes know.

`ImplI P I x Q p δ` says that the probability over the seeds that the run of `P` on instance `I`
from inputs `x` does not succeed is at most `δ`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

/-- Dynamically typed data held by an agent. -/
abbrev Mem : Type 1 := Σ T : Type, T

/-- Local knowledge of a node when a protocol starts. -/
structure NCtx (V : Type) where
  /-- the node's identifier -/
  me : V
  /-- local weight view of each agent the node simulates (`none` for the others) -/
  view : Agent V → Option (Sym2 V → ℕ)
  /-- public numbers of the task (known to every node) -/
  pub : List ℕ
  /-- embedded aggregator paths known to the node, keyed by source and key edge:
  `emb j u k = some path`: `path` is the path of `u` to the aggregator of its cluster `C` in
  overlay `j`, where `k = (srcPort C u).2` is `C`'s key edge at `u`, if the node lies on it
  (`none` otherwise) -/
  emb : ℕ → V → Sym2 V → Option (List (Sym2 V))
  /-- the node's cluster slices `C ∩ inc(v)` -/
  sl : Finset (Finset (Sym2 V))

/-- Bandwidth: a message is a single word; numbers are at most `n + 3` (`O(log n)` bits). -/
def WordOK {V : Type} (n : ℕ) : Word V → Prop
  | .num k => k ≤ n + 3
  | _ => True

/-- A uniform randomized protocol on node set `V`: one program, run by every node. -/
structure Proto (V : Type) : Type 2 where
  /-- local states -/
  S : Type 1
  /-- the seed space of a node -/
  Ω : Type
  [fΩ : Fintype Ω]
  [nΩ : Nonempty Ω]
  /-- initial state from the local context, the data of the agents the node simulates, a seed -/
  init : NCtx V → (Agent V → Option Mem) → Ω → S
  /-- the message to a neighbour -/
  send : NCtx V → S → V → Option (Word V)
  /-- the next state after receiving the messages of a round -/
  recv : NCtx V → S → (V → Option (Word V)) → S
  /-- `some` iff halted: then the outputs of the simulated agents -/
  out : S → Option (Agent V → Option Mem)

attribute [instance] Proto.fΩ Proto.nΩ

/-- An instance: communication graph, participants, hosts of the agents, local contexts. -/
structure Inst (V : Type) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  [dec : DecidableRel G.Adj]
  /-- the participating nodes -/
  part : V → Prop
  /-- the host of an agent (`none`: the agent is not simulated) -/
  host : Agent V → Option V
  /-- local contexts -/
  ctx : V → NCtx V
  /-- only participants have incident edges -/
  adj_part : ∀ u v, G.Adj u v → part u
  /-- hosts are participants -/
  host_part : ∀ g v, host g = some v → part v

attribute [instance] Inst.dec

variable {V : Type} [Fintype V] [DecidableEq V] (P : Proto V) (I : Inst V)

/-- The data of the agents hosted by `v`. -/
def inpAt (x : Agent V → Mem) (v : V) : Agent V → Option Mem :=
  fun g => if I.host g = some v then some (x g) else none

/-- The message from `u` to `v` in a round where the states are `σ`. -/
noncomputable def msg (σ : V → P.S) (u v : V) : Option (Word V) := by
  classical exact
  if I.G.Adj u v ∧ P.out (σ u) = none then
    match P.send (I.ctx u) (σ u) v with
    | some w => if WordOK (Fintype.card V) w then some w else none
    | none => none
  else none

/-- One synchronous round. -/
noncomputable def step (σ : V → P.S) : V → P.S := fun v =>
  if (P.out (σ v)).isSome then σ v else P.recv (I.ctx v) (σ v) (fun u => msg P I σ u v)

/-- The initial states. -/
noncomputable def st0 (x : Agent V → Mem) (ω : V → P.Ω) : V → P.S :=
  fun v => P.init (I.ctx v) (inpAt I x v) (ω v)

/-- The states after `t` rounds. -/
noncomputable def st (x : Agent V → Mem) (ω : V → P.Ω) : ℕ → V → P.S
  | 0 => st0 P I x ω
  | t + 1 => step P I (st x ω t)

/-- The (directed) messages sent in a round with states `σ`. -/
noncomputable def sentSet (σ : V → P.S) : Finset (V × V) := by
  classical exact univ.filter (fun uv => (msg P I σ uv.1 uv.2).isSome)

/-- Number of messages sent in the first `t` rounds. -/
noncomputable def msgsUpTo (x : Agent V → Mem) (ω : V → P.Ω) (t : ℕ) : ℕ :=
  ∑ s ∈ range t, (sentSet P I (st P I x ω s)).card

/-- Number of messages sent over the edge `e` (both directions) in the first `t` rounds. -/
noncomputable def loadUpTo (x : Agent V → Mem) (ω : V → P.Ω) (t : ℕ) (e : Sym2 V) : ℕ := by
  classical exact ∑ s ∈ range t, ((sentSet P I (st P I x ω s)).filter (fun uv => s(uv.1, uv.2) = e)).card

/-- All participants halt at round `t`, and none earlier. -/
def HaltsAt (x : Agent V → Mem) (ω : V → P.Ω) (t : ℕ) : Prop :=
  (∀ v, I.part v → (P.out (st P I x ω t v)).isSome) ∧
  ∀ s < t, ∀ v, I.part v → P.out (st P I x ω s v) = none

/-- **Proper sends** up to round `t`: in every round `s < t`, a participant that has not halted
tries to send only to its neighbours in the communication graph of the instance. -/
def ProperUpTo (x : Agent V → Mem) (ω : V → P.Ω) (t : ℕ) : Prop :=
  ∀ s < t, ∀ u, I.part u → P.out (st P I x ω s u) = none →
    ∀ v, (P.send (I.ctx u) (st P I x ω s u) v).isSome → I.G.Adj u v

/-- The output of agent `g` at round `t` (read at its host). -/
noncomputable def outAt (x : Agent V → Mem) (ω : V → P.Ω) (t : ℕ) (g : Agent V) : Option Mem :=
  match I.host g with
  | some v => (P.out (st P I x ω t v)).bind (fun m => m g)
  | none => none

/-- The run with seeds `ω` succeeds within cost `p` with postcondition `Q`: all participants
halt together at some round `t ≤ p.rounds`, sending only along edges of the instance before, within
the message and load budgets, and the outputs of the simulated agents satisfy `Q`. -/
def Succ (x : Agent V → Mem) (Q : (Agent V → Mem) → Prop) (p : Prof V) (ω : V → P.Ω) : Prop :=
  ∃ t, HaltsAt P I x ω t ∧ ProperUpTo P I x ω t ∧ t ≤ p.rounds ∧ msgsUpTo P I x ω t ≤ p.msgs ∧
    (∀ e, loadUpTo P I x ω t e ≤ p.load e) ∧
    ∃ y : Agent V → Mem, (∀ g, (I.host g).isSome → outAt P I x ω t g = some (y g)) ∧ Q y

/-- The probability (uniform independent seeds) that the run does not succeed. -/
noncomputable def failProb (x : Agent V → Mem) (Q : (Agent V → Mem) → Prop) (p : Prof V) : ℝ := by
  classical exact
  ((univ.filter (fun ω : V → P.Ω => ¬ Succ P I x Q p ω)).card : ℝ) / (Fintype.card (V → P.Ω) : ℝ)

/-- The concrete judgement on one instance. -/
def ImplI (x : Agent V → Mem) (Q : (Agent V → Mem) → Prop) (p : Prof V) (δ : ℝ) : Prop :=
  failProb P I x Q p ≤ δ

/-! ## Basic facts -/

lemma st_succ (x : Agent V → Mem) (ω : V → P.Ω) (t : ℕ) :
    st P I x ω (t + 1) = step P I (st P I x ω t) := rfl

/-- Proper sends up to a later round imply proper sends up to an earlier one. -/
lemma ProperUpTo.mono {x : Agent V → Mem} {ω : V → P.Ω} {t t' : ℕ} (h : ProperUpTo P I x ω t)
    (ht : t' ≤ t) : ProperUpTo P I x ω t' := fun s hs => h s (lt_of_lt_of_le hs ht)

/-- Nothing is required up to round `0`. -/
lemma properUpTo_zero (x : Agent V → Mem) (ω : V → P.Ω) : ProperUpTo P I x ω 0 :=
  fun s hs => absurd hs (Nat.not_lt_zero s)

lemma card_pos_fun : 0 < (Fintype.card (V → P.Ω) : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma failProb_nonneg (x : Agent V → Mem) (Q : (Agent V → Mem) → Prop) (p : Prof V) :
    0 ≤ failProb P I x Q p := by
  unfold failProb; positivity

lemma failProb_le_one (x : Agent V → Mem) (Q : (Agent V → Mem) → Prop) (p : Prof V) :
    failProb P I x Q p ≤ 1 := by
  classical
  unfold failProb
  rw [div_le_one (card_pos_fun P)]
  exact_mod_cast card_le_univ _

lemma ImplI.nonneg {x : Agent V → Mem} {Q : (Agent V → Mem) → Prop} {p : Prof V} {δ : ℝ}
    (h : ImplI P I x Q p δ) : 0 ≤ δ := le_trans (failProb_nonneg P I x Q p) h

/-- A judgement with failure bound `≥ 1` holds trivially. -/
lemma ImplI.of_one_le {x : Agent V → Mem} {Q : (Agent V → Mem) → Prop} {p : Prof V} {δ : ℝ}
    (h : 1 ≤ δ) : ImplI P I x Q p δ := le_trans (failProb_le_one P I x Q p) h

/-- Success is monotone in the cost profile and the postcondition. -/
lemma Succ.mono {x : Agent V → Mem} {Q Q' : (Agent V → Mem) → Prop} {p p' : Prof V}
    {ω : V → P.Ω} (h : Succ P I x Q p ω) (hp : p ≤ p') (hQ : ∀ y, Q y → Q' y) :
    Succ P I x Q' p' ω := by
  obtain ⟨t, ht, hpr, hr, hm, hl, y, hy, hQy⟩ := h
  rw [Prof.le_iff] at hp
  exact ⟨t, ht, hpr, hr.trans hp.1, hm.trans hp.2.2, fun e => (hl e).trans (hp.2.1 e), y, hy,
    hQ y hQy⟩

/-- Comparison of failure probabilities when success events are nested. -/
lemma failProb_le_of_imp (x x' : Agent V → Mem) (Q Q' : (Agent V → Mem) → Prop) (p p' : Prof V)
    (h : ∀ ω, Succ P I x Q p ω → Succ P I x' Q' p' ω) :
    failProb P I x' Q' p' ≤ failProb P I x Q p := by
  classical
  unfold failProb
  refine div_le_div_of_nonneg_right ?_ (le_of_lt (card_pos_fun P))
  exact_mod_cast card_le_card (fun ω => by
    simp only [mem_filter, mem_univ, true_and]
    exact fun h1 h2 => h1 (h ω h2))

lemma ImplI.mono {x : Agent V → Mem} {Q Q' : (Agent V → Mem) → Prop} {p p' : Prof V}
    {δ δ' : ℝ} (h : ImplI P I x Q p δ) (hp : p ≤ p') (hδ : δ ≤ δ') (hQ : ∀ y, Q y → Q' y) :
    ImplI P I x Q' p' δ' :=
  le_trans (failProb_le_of_imp P I x x Q Q' p p' (fun _ hω => hω.mono P I hp hQ)) (h.trans hδ)

/-- A run that succeeds for every choice of seeds has failure probability `0`. -/
lemma ImplI.of_forall {x : Agent V → Mem} {Q : (Agent V → Mem) → Prop} {p : Prof V} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ ω, Succ P I x Q p ω) : ImplI P I x Q p δ := by
  classical
  unfold ImplI failProb
  rw [filter_false_of_mem (fun ω _ => not_not.2 (h ω))]
  simpa using hδ

/-! ## Runs depend only on the data of simulated agents -/

lemma inpAt_congr {x x' : Agent V → Mem} (hx : ∀ g, (I.host g).isSome → x g = x' g) (v : V) :
    inpAt I x v = inpAt I x' v := by
  funext g
  unfold inpAt
  split_ifs with h
  · rw [hx g (by simp [h])]
  · rfl

lemma st_congr {x x' : Agent V → Mem} (hx : ∀ g, (I.host g).isSome → x g = x' g)
    (ω : V → P.Ω) (t : ℕ) : st P I x ω t = st P I x' ω t := by
  induction t with
  | zero => funext v; simp only [st, st0, inpAt_congr I hx]
  | succ t ih => simp only [st_succ, ih]

lemma Succ.congr {x x' : Agent V → Mem} (hx : ∀ g, (I.host g).isSome → x g = x' g)
    {Q : (Agent V → Mem) → Prop} {p : Prof V} {ω : V → P.Ω} :
    Succ P I x Q p ω ↔ Succ P I x' Q p ω := by
  have h : st P I x ω = st P I x' ω := funext (st_congr P I hx ω)
  simp only [Succ, HaltsAt, ProperUpTo, msgsUpTo, loadUpTo, outAt, h]

lemma ImplI.congr {x x' : Agent V → Mem} (hx : ∀ g, (I.host g).isSome → x g = x' g)
    {Q : (Agent V → Mem) → Prop} {p : Prof V} {δ : ℝ} :
    ImplI P I x Q p δ ↔ ImplI P I x' Q p δ := by
  classical
  unfold ImplI failProb
  simp only [Succ.congr P I hx]

end APSP.Stoc.Congest
