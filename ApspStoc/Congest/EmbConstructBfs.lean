import ApspStoc.Congest.EmbConstructPar

/-!
# A BFS tree by flooding

All nodes know `V`, hence `n` and the node `rootOf` of smallest index (`Fintype.equivFin`). The
protocol `bfsP` is a full-information protocol of `n` rounds: the root sends in round `0` to all
its neighbours; a node first reached in round `d - 1` (its distance to the root is `d`) chooses as
parent one of the nodes it heard from in that round (`pickPar`, a fixed choice from the set of
senders) and sends in round `d` to all its neighbours: `num 1` to its parent, `num 0` to the
others. The children of a node are the neighbours from which it received `num 1`. Since the
network is connected, every distance is `< n`, so every node is reached within `n` rounds.
Messages: one per directed edge (`2m ≤ n²`), two per edge. The output is the depth (distance to
the root), the parent and the children; they form a rooted spanning tree (`TreeH`).
-/

namespace APSP.Stoc.Congest

namespace EmbC

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The protocol -/

/-- the node of smallest index (computable by every node from `V`) -/
noncomputable def rootOf (me : V) : V :=
  (Fintype.equivFin V).symm ⟨0, Fintype.card_pos_iff.2 ⟨me⟩⟩

open Classical in
/-- the first round in which the node received a word -/
noncomputable def anyIdx (h : Hist V) : Option ℕ :=
  if hh : ∃ i, i < h.length ∧ ∃ w, (hget h i w).isSome then some (Nat.find hh) else none

open Classical in
/-- a fixed choice among the senders of round `i` -/
noncomputable def pickPar (h : Hist V) (i : ℕ) : Option V :=
  if hh : ∃ w, (hget h i w).isSome then some hh.choose else none

/-- the round in which the node is reached (`0` at the root) -/
noncomputable def joinR (me : V) (h : Hist V) : Option ℕ :=
  if me = rootOf me then some 0 else (anyIdx h).map (· + 1)

/-- the chosen parent -/
noncomputable def bfsParH (me : V) (h : Hist V) : Option V :=
  if me = rootOf me then none else
    match anyIdx h with
    | some i => pickPar h i
    | none => none

open Classical in
/-- the BFS message to `u` in the current round -/
noncomputable def bfsSend (c : NCtx V) (h : Hist V) (u : V) : Option (Word V) :=
  if joinR c.me h = some h.length ∧ ownVw c s(c.me, u) ≠ 0 then
    (if bfsParH c.me h = some u then some (.num 1) else some (.num 0))
  else none

open Classical in
/-- the BFS output: depth, parent, children -/
noncomputable def bfsRes (me : V) (h : Hist V) : BfsOut V :=
  ((joinR me h).getD 0, bfsParH me h,
    univ.filter (fun w => ∃ i, i < h.length ∧ hget h i w = some (.num 1)))

open Classical in
/-- **The BFS protocol** (`n` rounds). -/
noncomputable def bfsP (V : Type) [Fintype V] [DecidableEq V] : Proto V :=
  histP (fun c _ h u => bfsSend c h u) (fun _ => Fintype.card V)
    (fun c _ h g => if g = .inl c.me then some ⟨BfsOut V, bfsRes c.me h⟩ else none)

/-! ## The BFS tree -/

section Tree

variable (N : WNet V)

/-- the depth: the distance to the root -/
noncomputable def bfsDep (ρ : V) (v : V) : ℕ := N.G.dist ρ v

open Classical in
/-- the parent: a fixed choice among the neighbours one step closer to the root -/
noncomputable def bfsPar (ρ : V) (v : V) : Option V :=
  if v = ρ then none else
    if hh : ∃ w, N.G.Adj w v ∧ N.G.dist ρ w = N.G.dist ρ v - 1 then some hh.choose else none

variable {N}

lemma dist_adj_le {ρ u w : V} (h : N.G.Adj u w) : N.G.dist ρ u ≤ N.G.dist ρ w + 1 := by
  obtain ⟨p, hp⟩ := N.conn.exists_walk_length_eq_dist ρ w
  have := SimpleGraph.dist_le (p.concat h.symm)
  rw [SimpleGraph.Walk.length_concat, hp] at this
  exact this

lemma exists_closer {ρ v : V} (hv : v ≠ ρ) :
    ∃ w, N.G.Adj w v ∧ N.G.dist ρ w = N.G.dist ρ v - 1 ∧ 1 ≤ N.G.dist ρ v := by
  obtain ⟨p, hp⟩ := N.conn.exists_walk_length_eq_dist v ρ
  obtain ⟨w, hadj, q, rfl⟩ := p.exists_eq_cons_of_ne hv
  have h1 := SimpleGraph.dist_le q.reverse
  rw [SimpleGraph.Walk.length_reverse] at h1
  have h2 := dist_adj_le (ρ := ρ) hadj
  simp only [SimpleGraph.Walk.length_cons] at hp
  rw [SimpleGraph.dist_comm] at hp
  refine ⟨w, hadj.symm, by omega, by omega⟩

lemma dist_lt_card (ρ v : V) : N.G.dist ρ v < Fintype.card V := by
  obtain ⟨p, hp, hl⟩ := N.conn.exists_path_of_dist ρ v
  rw [← hl]; exact hp.length_lt

lemma bfsPar_spec {ρ v p : V} (h : bfsPar N ρ v = some p) :
    N.G.Adj v p ∧ N.G.dist ρ v = N.G.dist ρ p + 1 := by
  classical
  unfold bfsPar at h
  by_cases h1 : v = ρ
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : ∃ w, N.G.Adj w v ∧ N.G.dist ρ w = N.G.dist ρ v - 1
    · rw [dif_pos h2] at h
      have hp : h2.choose = p := Option.some.inj h
      obtain ⟨hadj, hd⟩ := h2.choose_spec
      rw [hp] at hadj hd
      obtain ⟨-, -, -, hd1⟩ := exists_closer (N := N) h1
      exact ⟨hadj.symm, by omega⟩
    · rw [dif_neg h2] at h; cases h

/-- the BFS tree is a rooted spanning tree with depths -/
theorem bfs_tree (ρ : V) : TreeH N ρ (bfsPar N ρ) (bfsDep N ρ) where
  root := by unfold bfsPar; rw [if_pos rfl]
  dep_root := SimpleGraph.dist_self
  par_ne v hv := by
    classical
    unfold bfsPar
    rw [if_neg hv]
    obtain ⟨w, h1, h2, -⟩ := exists_closer (N := N) hv
    rw [dif_pos ⟨w, h1, h2⟩]
    simp
  adj v p h := (bfsPar_spec h).1
  dep_par v p h := (bfsPar_spec h).2
  dep_lt v := dist_lt_card ρ v

end Tree

/-! ## The schedule -/

section Sched

variable (N : WNet V) (ρ : V)

open Classical in
/-- the schedule: `w` sends in round `dist ρ w` to all its neighbours -/
noncomputable def bfsSched (w v : V) (s : ℕ) : Option (Word V) :=
  if s = N.G.dist ρ w ∧ N.G.Adj w v then
    (if bfsPar N ρ w = some v then some (.num 1) else some (.num 0))
  else none

variable {N ρ}

lemma bfsSched_isSome {w v : V} {s : ℕ} :
    (bfsSched N ρ w v s).isSome ↔ s = N.G.dist ρ w ∧ N.G.Adj w v := by
  unfold bfsSched
  split_ifs with h1 h2 <;> simp_all

lemma anyIdx_sched {u : V} (hu : u ≠ ρ) (s : ℕ) :
    anyIdx (schedHist (bfsSched N ρ) u s) =
      if N.G.dist ρ u - 1 < s then some (N.G.dist ρ u - 1) else none := by
  classical
  obtain ⟨w₀, hw₀, hd₀, hpos⟩ := exists_closer (N := N) hu
  unfold anyIdx
  have hP : ∀ i, i < s → ((∃ w, (hget (schedHist (bfsSched N ρ) u s) i w).isSome) ↔
      ∃ w, N.G.Adj w u ∧ N.G.dist ρ w = i) := by
    intro i hi
    simp only [hget_schedHist _ u hi, bfsSched_isSome]
    exact ⟨fun ⟨w, h1, h2⟩ => ⟨w, h2, h1.symm⟩, fun ⟨w, h1, h2⟩ => ⟨w, h2.symm, h1⟩⟩
  by_cases hs : N.G.dist ρ u - 1 < s
  · have hex : ∃ i, i < (schedHist (bfsSched N ρ) u s).length ∧
        ∃ w, (hget (schedHist (bfsSched N ρ) u s) i w).isSome := by
      rw [length_schedHist]
      exact ⟨_, hs, (hP _ hs).2 ⟨w₀, hw₀, hd₀⟩⟩
    rw [dif_pos hex, if_pos hs]
    congr 1
    rw [Nat.find_eq_iff]
    refine ⟨⟨by rw [length_schedHist]; exact hs, (hP _ hs).2 ⟨w₀, hw₀, hd₀⟩⟩, ?_⟩
    rintro i hi ⟨hi', hw⟩
    rw [length_schedHist] at hi'
    obtain ⟨w, hw1, hw2⟩ := (hP i hi').1 hw
    have := dist_adj_le (ρ := ρ) hw1.symm
    omega
  · rw [if_neg hs, dif_neg]
    rintro ⟨i, hi, hw⟩
    rw [length_schedHist] at hi
    obtain ⟨w, hw1, hw2⟩ := (hP i hi).1 hw
    have := dist_adj_le (ρ := ρ) hw1.symm
    omega

lemma joinR_sched (hρ : ∀ u : V, rootOf u = ρ) (u : V) (s : ℕ) :
    joinR u (schedHist (bfsSched N ρ) u s) =
      if N.G.dist ρ u ≤ s then some (N.G.dist ρ u) else none := by
  unfold joinR
  rw [hρ u]
  by_cases hu : u = ρ
  · subst hu
    rw [if_pos rfl, SimpleGraph.dist_self, if_pos (Nat.zero_le _)]
  · rw [if_neg hu, anyIdx_sched hu]
    obtain ⟨-, -, -, hpos⟩ := exists_closer (N := N) hu
    by_cases hs : N.G.dist ρ u - 1 < s
    · rw [if_pos hs, if_pos (by omega)]
      simp only [Option.map_some]
      congr 1; omega
    · rw [if_neg hs, if_neg (by omega)]; rfl

lemma bfsParH_sched (hρ : ∀ u : V, rootOf u = ρ) (u : V) {s : ℕ} (hs : N.G.dist ρ u ≤ s) :
    bfsParH u (schedHist (bfsSched N ρ) u s) = bfsPar N ρ u := by
  classical
  unfold bfsParH bfsPar
  rw [hρ u]
  by_cases hu : u = ρ
  · rw [if_pos hu, if_pos hu]
  · rw [if_neg hu, if_neg hu, anyIdx_sched hu]
    obtain ⟨w₀, hw₀, hd₀, hpos⟩ := exists_closer (N := N) hu
    rw [if_pos (by omega)]
    simp only
    unfold pickPar
    have hi : N.G.dist ρ u - 1 < s := by omega
    have hpred : (fun w => (hget (schedHist (bfsSched N ρ) u s) (N.G.dist ρ u - 1) w).isSome = true) =
        (fun w => N.G.Adj w u ∧ N.G.dist ρ w = N.G.dist ρ u - 1) := by
      funext w
      simp only [hget_schedHist _ u hi, bfsSched_isSome, eq_iff_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩⟩
    have hex : ∃ w, (hget (schedHist (bfsSched N ρ) u s) (N.G.dist ρ u - 1) w).isSome := by
      rw [hpred]; exact ⟨w₀, hw₀, hd₀⟩
    have hex' : ∃ w, N.G.Adj w u ∧ N.G.dist ρ w = N.G.dist ρ u - 1 := ⟨w₀, hw₀, hd₀⟩
    rw [dif_pos hex, dif_pos hex']
    congr 1
    exact choose_congr hpred hex hex'

lemma ownVw_base (v u : V) :
    ownVw ((baseInst N).ctx v) s(v, u) ≠ 0 ↔ N.G.Adj v u := by
  classical
  have h0 : ownVw ((baseInst N).ctx v) = lview N (.inl v) := by simp [ownVw, baseInst]
  rw [h0]
  simp only [lview]
  by_cases h : s(v, u) ∈ N.G.edgeFinset ∧ v ∈ s(v, u)
  · rw [if_pos h]
    have := N.wpos _ (SimpleGraph.mem_edgeFinset.1 h.1)
    have h1 := h.1
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h1
    exact ⟨fun _ => h1, fun _ => by omega⟩
  · rw [if_neg h]
    simp only [ne_eq, not_true_eq_false, false_iff]
    intro hadj
    exact h ⟨by simpa using hadj, Sym2.mem_mk_left v u⟩

lemma bfsSched_eq (w v : V) (s : ℕ) : bfsSched N ρ w v s =
    if s = N.G.dist ρ w ∧ N.G.Adj w v then
      (if bfsPar N ρ w = some v then some (.num 1) else some (.num 0))
    else none := rfl

lemma bfsSend_sched (hρ : ∀ u : V, rootOf u = ρ) (u v : V) (s : ℕ) :
    bfsSend ((baseInst N).ctx u) (schedHist (bfsSched N ρ) u s) v = bfsSched N ρ u v s := by
  classical
  have hme : ((baseInst N).ctx u).me = u := rfl
  have hj := joinR_sched (N := N) hρ u s
  have hl := length_schedHist (bfsSched N ρ) u s
  unfold bfsSend
  rw [hme, bfsSched_eq]
  by_cases h : s = N.G.dist ρ u ∧ N.G.Adj u v
  · rw [if_pos ⟨by rw [hj, hl, if_pos (by omega), h.1], (ownVw_base u v).2 h.2⟩, if_pos h,
      bfsParH_sched hρ u (by omega)]
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2⟩
    apply h
    rw [hj, hl] at h1
    split_ifs at h1 with h3
    exact ⟨(Option.some.inj h1).symm, (ownVw_base u v).1 h2⟩

end Sched

/-! ## Success -/

/-- **The BFS phase** builds the BFS tree of `G` from the root, in `n` rounds, with at most two
messages per edge and `n²` messages, deterministically. -/
theorem bfs_implI (N : WNet V) (ρ : V) (hρ : ∀ u : V, rootOf u = ρ) {α : Type}
    (x : Agent V → α) :
    ImplI (bfsP V) (baseInst N) (inOf x)
      (postOf (baseInst N) (fun z : Agent V → BfsOut V => ∀ v, z (.inl v) =
        (bfsDep N ρ v, bfsPar N ρ v, univ.filter (fun c => bfsPar N ρ c = some v))))
      (Prof.mk (Fintype.card V) (fun _ => 2) (Fintype.card V ^ 2)) 0 := by
  classical
  refine ImplI.of_forall _ _ le_rfl (fun ω => ?_)
  have hM : ∀ s < Fintype.card V, ∀ u v,
      ((baseInst N).part u → bfsSend ((baseInst N).ctx u) (schedHist (bfsSched N ρ) u s) v =
        bfsSched N ρ u v s) ∧
      (¬ (baseInst N).G.Adj u v → bfsSched N ρ u v s = none) ∧
      ∀ w, bfsSched N ρ u v s = some w → WordOK (Fintype.card V) w := by
    intro s _ u v
    refine ⟨fun _ => bfsSend_sched hρ u v s, fun hadj => ?_, fun w hw => ?_⟩
    · unfold bfsSched; rw [if_neg (fun h => hadj h.2)]
    · unfold bfsSched at hw
      split_ifs at hw <;> cases hw <;> show _ ≤ _ <;> omega
  refine succ_histP (F := fun c _ h u => bfsSend c h u) (Tf := fun _ => Fintype.card V)
    (O := fun c _ h g => if g = .inl c.me then some ⟨BfsOut V, bfsRes c.me h⟩ else none)
    (I := baseInst N) (x := inOf x) (fun _ => rfl) (bfsSched N ρ) hM le_rfl ?_ ?_
    (fun g => match g with
      | .inl v => ⟨BfsOut V, (bfsDep N ρ v, bfsPar N ρ v,
          univ.filter (fun c => bfsPar N ρ c = some v))⟩
      | .inr _ => ⟨BfsOut V, (0, none, ∅)⟩) ?_ ?_
  · -- messages: each directed edge once
    simp only [Prof.msgs_mk]
    rw [sum_card_filter_swap]
    calc ∑ uv : V × V, ((range (Fintype.card V)).filter
          (fun s => (bfsSched N ρ uv.1 uv.2 s).isSome)).card
        ≤ ∑ _uv : V × V, 1 := by
          refine sum_le_sum (fun uv _ => card_le_one.2 (fun a ha b hb => ?_))
          simp only [mem_filter, bfsSched_isSome] at ha hb
          omega
      _ = Fintype.card V ^ 2 := by simp [sq]
  · intro e
    simp only [Prof.load_mk]
    have := sum_card_filter_swap (Fintype.card V)
      (fun s (uv : V × V) => (bfsSched N ρ uv.1 uv.2 s).isSome ∧ s(uv.1, uv.2) = e)
    calc ∑ s ∈ range (Fintype.card V), ((univ.filter
          (fun uv : V × V => (bfsSched N ρ uv.1 uv.2 s).isSome)).filter
            (fun uv => s(uv.1, uv.2) = e)).card
        = ∑ s ∈ range (Fintype.card V), (univ.filter
          (fun uv : V × V => (bfsSched N ρ uv.1 uv.2 s).isSome ∧ s(uv.1, uv.2) = e)).card := by
          refine sum_congr rfl (fun s _ => ?_)
          rw [filter_filter]
      _ = ∑ uv : V × V, ((range (Fintype.card V)).filter
          (fun s => (bfsSched N ρ uv.1 uv.2 s).isSome ∧ s(uv.1, uv.2) = e)).card := this
      _ ≤ ∑ uv : V × V, (if s(uv.1, uv.2) = e then 1 else 0) := by
          refine sum_le_sum (fun uv _ => ?_)
          split_ifs with he
          · refine card_le_one.2 (fun a ha b hb => ?_)
            simp only [mem_filter, bfsSched_isSome] at ha hb
            omega
          · simp [he]
      _ = (univ.filter (fun uv : V × V => s(uv.1, uv.2) = e)).card := by
          rw [card_filter]
      _ ≤ 2 := card_sym2_fiber e
  · -- outputs
    intro g v hg
    cases g with
    | inr C => simp [baseInst, physHost] at hg
    | inl u =>
      simp only [baseInst, physHost, Option.some.injEq] at hg
      subst hg
      show (if (Sum.inl u : Agent V) = Sum.inl u then
        some (⟨BfsOut V, bfsRes u (schedHist (bfsSched N ρ) u (Fintype.card V))⟩ : Mem)
        else none) = _
      rw [if_pos rfl]
      congr 2
      unfold bfsRes
      have hd := dist_lt_card (N := N) ρ u
      rw [joinR_sched hρ, if_pos hd.le, bfsParH_sched hρ u hd.le, Option.getD_some]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      ext w
      simp only [mem_filter, mem_univ, true_and, length_schedHist]
      constructor
      · rintro ⟨i, hi, hw⟩
        rw [hget_schedHist _ u hi] at hw
        unfold bfsSched at hw
        split_ifs at hw with h1 h2
        · exact h2
        · cases hw
      · intro hw
        have hadj := (bfsPar_spec hw).1
        refine ⟨N.G.dist ρ w, dist_lt_card ρ w, ?_⟩
        rw [hget_schedHist _ u (dist_lt_card ρ w)]
        unfold bfsSched
        rw [if_pos ⟨rfl, hadj⟩, if_pos hw]
  · exact ⟨fun g => match g with
      | .inl v => (bfsDep N ρ v, bfsPar N ρ v, univ.filter (fun c => bfsPar N ρ c = some v))
      | .inr _ => (0, none, ∅), fun g _ => by cases g <;> rfl, fun v => rfl⟩

end EmbC

end APSP.Stoc.Congest
