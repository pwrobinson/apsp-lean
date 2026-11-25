import ApspStoc.Congest.KTGraph

/-!
# The gather phase: the protocol and its schedule

The protocol `gatherP n U` lets every node of `S` learn `S`, deterministically. It is a
full-information protocol (`histP`): a node keeps the history of the messages it received, and
what it sends is a function of its context and history. All phase boundaries are functions of `n`
(the algorithm's index, `n = |S|`) and of `B = nB U = lg |U|`, which every node knows.

* **Windows `0, …, B - 1` (`n` rounds each): binary search for the least index.** Every node keeps
  the search interval `[lo, lo + 2^(B-b))` (`loL`), the same at all nodes. In window `b`, the
  nodes whose index is in the lower half are the sources: they flood a token (`floodSend`: a node
  sends to all its neighbours once, in round `0` of the window if it is a source, otherwise in the
  round after it first receives a token). As the network is connected, every node has received a
  token by the end of the window iff there is a source; then the upper half is dropped, otherwise
  the lower half. Messages: one per directed edge per window.
* **Window `B` (`n` rounds): BFS from the leader**, the node of least index (the only source).
  A node sends `num 1` to its parent (the sender of least index among those of the first round in
  which it heard the token) and `num 0` to its other neighbours, so after the window every node
  knows its depth, its parent and its children.
* **Window SZ (`n` rounds): subtree sizes.** A node of depth `d ≥ 1` sends the size of its subtree
  (`1 +` the sizes received from its children) to its parent in round `n - 1 - d` of the window.
* **Window PRE (`n` rounds): preorder numbers.** A node of depth `d` sends to each child `c` (in
  round `d`) the number `pre + 1 + Σ` (sizes of the children of smaller index than `c`).
* **Window PP (`3n` rounds): pipelined upcast and broadcast of all IDs.** In round `j`, a non-root
  node `u` sends to its parent the ID of the node `w` of its subtree with `pre w + n = j + dep u`
  (its own ID, or the one it received from a child in the previous round); a node `u` sends to its
  children the ID of the node `w` with `pre w + n + dep u = j` (the root: what it sends up; the
  others: what they received from their parent in the previous round). As preorder numbers are
  injective, there are no collisions, and every ID reaches every node.
* **Output** at round `tFin = (B + 6) n`: the own ID and all IDs received in window PP, which is
  `S`.

The global schedule `gM` (built from the objects of `KTGraph.lean`) is what the run does; it is
proved in `KTGather.lean`.
-/

namespace APSP.Stoc.Congest

namespace KT

open APSP Finset

set_option linter.unusedSectionVars false

variable {U : Type} [Fintype U] [DecidableEq U]

/-! ## The timeline -/

/-- the start of window SZ -/
def tSZ (n B : ℕ) : ℕ := (B + 1) * n

/-- the start of window PRE -/
def tPRE (n B : ℕ) : ℕ := tSZ n B + n

/-- the start of window PP -/
def tPP (n B : ℕ) : ℕ := tPRE n B + n

/-- the halting round -/
def tFin (n B : ℕ) : ℕ := tPP n B + 3 * n

/-! ## Local computations -/

/-- the senders of round `i` of a history -/
def sendersH (h : Hist U) (i : ℕ) : Finset U := univ.filter (fun w => (hget h i w).isSome)

open Classical in
/-- the first round `j < L` of the window starting at `W` in which a word was received -/
noncomputable def firstR (h : Hist U) (W L : ℕ) : Option ℕ :=
  if hh : ∃ j, j < L ∧ (sendersH h (W + j)).Nonempty then some (Nat.find hh) else none

/-- the lower end of the search interval after `b` windows, computed locally -/
noncomputable def loL (n B : ℕ) (me : U) (h : Hist U) : ℕ → ℕ
  | 0 => 0
  | b + 1 => if idx me < loL n B me h b + 2 ^ (B - b - 1) ∨ (firstR h (b * n) n).isSome
      then loL n B me h b else loL n B me h b + 2 ^ (B - b - 1)

/-- the round of window `b` in which the node sends the token (`none`: not yet) -/
noncomputable def actL (n B : ℕ) (me : U) (h : Hist U) (b : ℕ) : Option ℕ :=
  if idx me < loL n B me h b + 2 ^ (B - b - 1) then some 0 else (firstR h (b * n) n).map (· + 1)

/-- the parent chosen in window `b` -/
noncomputable def parL (n B : ℕ) (me : U) (h : Hist U) (b : ℕ) : Option U :=
  if idx me < loL n B me h b + 2 ^ (B - b - 1) then none
  else (firstR h (b * n) n).bind (fun j => argminIdx (sendersH h (b * n + j)))

/-- the message to `v` in round `j` of window `b` -/
noncomputable def floodSend (n B : ℕ) (c : NCtx U) (h : Hist U) (b j : ℕ) (v : U) :
    Option (Word U) :=
  if actL n B c.me h b = some j ∧ kv c s(c.me, v) ≠ 0 then
    some (if parL n B c.me h b = some v then .num 1 else .num 0)
  else none

/-- the depth in the BFS tree -/
noncomputable def depL (n B : ℕ) (me : U) (h : Hist U) : ℕ := (actL n B me h B).getD 0

/-- the parent in the BFS tree -/
noncomputable def parTL (n B : ℕ) (me : U) (h : Hist U) : Option U := parL n B me h B

open Classical in
/-- the children in the BFS tree: the neighbours that sent `num 1` in window `B` -/
noncomputable def kidsL (n B : ℕ) (h : Hist U) : Finset U :=
  univ.filter (fun w => ∃ j < n, hget h (B * n + j) w = some (.num 1))

/-- the sum of the numbers received from `w` in the window `[W, W + L)` -/
def rcvNum (h : Hist U) (W L : ℕ) (w : U) : ℕ :=
  ∑ j ∈ range L, wnum ((hget h (W + j) w).getD (.num 0))

/-- the size of the subtree: one plus the numbers received in window SZ -/
def szL (n B : ℕ) (h : Hist U) : ℕ := 1 + ∑ w, rcvNum h (tSZ n B) n w

/-- the message to `v` in round `j` of window SZ -/
noncomputable def szSend (n B : ℕ) (c : NCtx U) (h : Hist U) (j : ℕ) (v : U) : Option (Word U) :=
  if parTL n B c.me h = some v ∧ j + 1 + depL n B c.me h = n then some (.num (szL n B h)) else none

/-- the preorder number: the number received in window PRE -/
def preL (n B : ℕ) (h : Hist U) : ℕ := ∑ w, rcvNum h (tPRE n B) n w

/-- the message to `v` in round `j` of window PRE -/
noncomputable def preSend (n B : ℕ) (c : NCtx U) (h : Hist U) (j : ℕ) (v : U) : Option (Word U) :=
  if v ∈ kidsL n B h ∧ j = depL n B c.me h then
    some (.num (preL n B h + 1 +
      ∑ c' ∈ (kidsL n B h).filter (fun c' => idx c' < idx v), rcvNum h (tSZ n B) n c'))
  else none

open Classical in
/-- the ID received in round `i` from a node other than `ex` -/
noncomputable def rcvIdEx (h : Hist U) (i : ℕ) (ex : Option U) : Option U :=
  argminIdx (univ.filter (fun x => ∃ w, some w ≠ ex ∧ hget h i w = some (.id x)))

/-- the ID in a word -/
def idOf : Option (Word U) → Option U
  | some (.id x) => some x
  | _ => none

/-- the ID sent up in round `j` of window PP -/
noncomputable def upL (n B : ℕ) (me : U) (h : Hist U) (j : ℕ) : Option U :=
  if preL n B h + n = j + depL n B me h then some me
  else if j = 0 then none else rcvIdEx h (tPP n B + j - 1) (parTL n B me h)

/-- the ID sent down in round `j` of window PP -/
noncomputable def downL (n B : ℕ) (me : U) (h : Hist U) (j : ℕ) : Option U :=
  match parTL n B me h with
  | none => upL n B me h j
  | some p => if j = 0 then none else idOf (hget h (tPP n B + j - 1) p)

/-- the message to `v` in round `j` of window PP -/
noncomputable def ppSend (n B : ℕ) (c : NCtx U) (h : Hist U) (j : ℕ) (v : U) : Option (Word U) :=
  if parTL n B c.me h = some v then (upL n B c.me h j).map .id
  else if v ∈ kidsL n B h then (downL n B c.me h j).map .id else none

/-- the message to `v` in the round `|h|` -/
noncomputable def gSend (n B : ℕ) (c : NCtx U) (h : Hist U) (v : U) : Option (Word U) :=
  if h.length < tSZ n B then floodSend n B c h (h.length / n) (h.length % n) v
  else if h.length < tPRE n B then szSend n B c h (h.length - tSZ n B) v
  else if h.length < tPP n B then preSend n B c h (h.length - tPRE n B) v
  else if h.length < tFin n B then ppSend n B c h (h.length - tPP n B) v
  else none

open Classical in
/-- the output: the own ID and all IDs received in window PP -/
noncomputable def outSet (n B : ℕ) (me : U) (h : Hist U) : Finset U :=
  insert me (univ.filter (fun x => ∃ j < 3 * n, ∃ w, hget h (tPP n B + j) w = some (.id x)))

/-- **The gather protocol** for networks with `n` nodes: halts in round `(nB U + 6) n` with
output `S` at every node. -/
noncomputable def gatherP (n : ℕ) (U : Type) [Fintype U] [DecidableEq U] : Proto U :=
  histP (fun c _ h v => gSend n (nB U) c h v) (fun _ => tFin n (nB U))
    (fun c _ h g => if g = .inl c.me then some ⟨Finset U, outSet n (nB U) c.me h⟩ else none)

/-! ## The global schedule -/

section Sched

variable (S : Finset U) (N : WNet S)

open Classical in
/-- round `j` of window `b`: the flood from `srcB S b` -/
noncomputable def gFlood (b j : ℕ) (w u : U) : Option (Word U) :=
  if (srcB S b).Nonempty ∧ (ktInst S N).G.Adj w u ∧ dA S N (srcB S b) w = j then
    some (if parA S N (srcB S b) w = some u then .num 1 else .num 0)
  else none

open Classical in
/-- round `j` of window SZ -/
noncomputable def gSZ (j : ℕ) (w u : U) : Option (Word U) :=
  if kpar S N w = some u ∧ j + 1 + kdep S N w = S.card then some (.num (ksz S N w)) else none

open Classical in
/-- round `j` of window PRE -/
noncomputable def gPRE (j : ℕ) (w u : U) : Option (Word U) :=
  if kpar S N u = some w ∧ j = kdep S N w then some (.num (kpre S N u)) else none

/-- the IDs sent up by `u` in round `j` of window PP (at most one) -/
noncomputable def upSet (u : U) (j : ℕ) : Finset U :=
  (desc S (kpar S N) u).filter (fun w => kpre S N w + S.card = j + kdep S N u)

/-- the IDs sent down by `u` in round `j` of window PP (at most one) -/
noncomputable def downSet (u : U) (j : ℕ) : Finset U :=
  S.filter (fun w => kpre S N w + S.card + kdep S N u = j)

open Classical in
/-- round `j` of window PP -/
noncomputable def gPP (j : ℕ) (w u : U) : Option (Word U) :=
  if kpar S N w = some u then (argminIdx (upSet S N w j)).map .id
  else if kpar S N u = some w then (argminIdx (downSet S N w j)).map .id else none

/-- **The schedule of the gather phase**: the message from `w` to `u` in round `s` -/
noncomputable def gM (w u : U) (s : ℕ) : Option (Word U) :=
  if s < tSZ S.card (nB U) then gFlood S N (s / S.card) (s % S.card) w u
  else if s < tPRE S.card (nB U) then gSZ S N (s - tSZ S.card (nB U)) w u
  else if s < tPP S.card (nB U) then gPRE S N (s - tPRE S.card (nB U)) w u
  else if s < tFin S.card (nB U) then gPP S N (s - tPP S.card (nB U)) w u
  else none

end Sched

end KT

end APSP.Stoc.Congest
