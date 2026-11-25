import ApspStoc.Congest.EmbConstructDefs

/-!
# The parallel composition with termination detection (`mainP`)

`par_run` is the **generic parallel-composition lemma**: run a protocol `P` in every cluster `C` of
a family `cl` of pairwise edge-disjoint edge sets of `G` covering all edges, simultaneously
inside `baseInst N` (the copies are keyed at each node by its slice `C ∩ inc(v)`; the copy of
`C` at `v` uses the seed component of its slice). If every standalone run of `P` on
`clInst0 N C` (with the seeds `seedC ω C`) halts (in round `T C`), then:
* every copy follows its standalone run (`st_main`): the copies of different clusters use
  different edges, a copy only sends over the edges of its slice, and the messages over an edge
  go to the copy of the edge's cluster as long as it runs (all copies of a cluster halt in the
  same round, so sender and receiver agree);
* the termination detection follows the explicit schedule `mSched` (reports up the BFS tree in
  rounds `R u, …, R u + L - 1` with `R u = max (D u) (max_c (R c + L))`, `D u` the round in which
  all clusters of `u` have halted; broadcast down in rounds `B u, …` with
  `B u = R ρ + L · dep u`); it only uses tree edges whose copies have halted;
* all nodes halt in round `H = R ρ + L · n ≤ max_C T C + 2 L n`, the messages and loads are those
  of the standalone runs plus `≤ 2 L n` messages (`≤ 2 L` per edge) of the tree, and every node
  outputs `finF` of the final states of its copies and of the global maxima of the local values
  `valF`.

The union bound over the seeds is in `EmbConstruct.lean` (`card_proj_filter`).
-/

namespace APSP.Stoc.Congest

namespace EmbC

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `card_proj_filter` for a predicate given up to equivalence. -/
lemma card_proj_filter' {K Ω₀ : Type} [Fintype K] [DecidableEq K] [Fintype Ω₀] [Nonempty Ω₀]
    (κ : V → K) (p : (V → Ω₀) → Prop) [DecidablePred p] (q : (V → K → Ω₀) → Prop)
    [DecidablePred q] (hq : ∀ ω, q ω ↔ p (fun v => ω v (κ v))) :
    ((univ.filter q).card : ℝ) / (Fintype.card (V → K → Ω₀) : ℝ) =
      ((univ.filter p).card : ℝ) / (Fintype.card (V → Ω₀) : ℝ) := by
  rw [Finset.filter_congr (fun ω _ => hq ω)]
  exact card_proj_filter κ p

/-! ## Maxima over subtrees -/

section TMax

variable (par : V → Option V) (rk : V → ℕ)

/-- `tmax f L u = max (f u) (max_c (tmax f L c + L))` over the children `c` of `u` -/
noncomputable def tmax (f : V → ℕ) (L : ℕ) (u : V) : ℕ :=
  max (f u) ((kidsOf univ par u).sup
    (fun c => if _h : mu univ rk c < mu univ rk u then tmax f L c + L else 0))
termination_by mu univ rk u

variable {par rk}
variable (hrk : ∀ v ∈ (univ : Finset V), ∀ u, par v = some u → rk u < rk v)
include hrk

lemma tmax_eq (f : V → ℕ) (L : ℕ) (u : V) :
    tmax par rk f L u = max (f u) ((kidsOf univ par u).sup (fun c => tmax par rk f L c + L)) := by
  rw [tmax]
  congr 1
  exact Finset.sup_congr rfl (fun c hc => dite_eq_left_iff.2 (fun h => absurd (mu_lt hrk hc) h))

lemma le_tmax (f : V → ℕ) (L : ℕ) (u : V) : f u ≤ tmax par rk f L u := by
  rw [tmax_eq hrk]; exact le_max_left _ _

lemma tmax_kid (f : V → ℕ) (L : ℕ) {u c : V} (h : par c = some u) :
    tmax par rk f L c + L ≤ tmax par rk f L u := by
  rw [tmax_eq hrk f L u]
  refine le_trans ?_ (le_max_right _ _)
  exact le_sup (f := fun c => tmax par rk f L c + L) (mem_kidsOf.2 ⟨mem_univ _, h⟩)

lemma tmax_le (f : V → ℕ) (L : ℕ) (B : V → ℕ) (hB : ∀ u, f u ≤ B u)
    (hBk : ∀ u c, par c = some u → B c + L ≤ B u) (u : V) : tmax par rk f L u ≤ B u := by
  induction u using kid_induction hrk with
  | _ u ih =>
    rw [tmax_eq hrk]
    refine max_le (hB u) (Finset.sup_le (fun c hc => ?_))
    have := ih c hc
    have := hBk u c (mem_kidsOf.1 hc).2
    omega

end TMax

/-! ## Tree hypotheses -/

/-- a rooted spanning tree of `G` with depths -/
structure TreeH (N : WNet V) (ρ : V) (par : V → Option V) (dep : V → ℕ) : Prop where
  root : par ρ = none
  dep_root : dep ρ = 0
  par_ne : ∀ v, v ≠ ρ → par v ≠ none
  adj : ∀ v p, par v = some p → N.G.Adj v p
  dep_par : ∀ v p, par v = some p → dep v = dep p + 1
  dep_lt : ∀ v, dep v < Fintype.card V

section TreeFacts

variable {N : WNet V} {ρ : V} {par : V → Option V} {dep : V → ℕ}

lemma TreeH.rk (h : TreeH N ρ par dep) : ∀ v ∈ (univ : Finset V), ∀ u, par v = some u → dep u < dep v :=
  fun v _ u hu => by rw [h.dep_par v u hu]; omega

/-- every value at a node is bounded by the value at the root, if values grow towards the root -/
lemma TreeH.le_root (h : TreeH N ρ par dep) (g : V → ℕ) (hg : ∀ c p, par c = some p → g c ≤ g p)
    (v : V) : g v ≤ g ρ := by
  induction hn : dep v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    by_cases hv : v = ρ
    · rw [hv]
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 (h.par_ne v hv)
      have hd := h.dep_par v p hp
      exact (hg v p hp).trans (ih (dep p) (by omega) p rfl)

lemma TreeH.not_par_par (h : TreeH N ρ par dep) {u v : V} (huv : par u = some v) :
    par v ≠ some u := by
  intro hvu
  have h1 := h.dep_par u v huv
  have h2 := h.dep_par v u hvu
  omega

end TreeFacts

/-! ## The schedule of the tree words -/

section Sched

variable (n Dg : ℕ) (ρ : V) (par : V → Option V) (dep : V → ℕ) (R : V → ℕ) (Ag : V → ℕ × ℕ)

/-- the round in which `u` starts its broadcast -/
def bB (u : V) : ℕ := R ρ + 2 * Dg * dep u

open Classical in
/-- **The schedule of the tree words** from `u` to `v` in round `t`: `u` reports to its parent in
rounds `R u, …, R u + L - 1`, and broadcasts the root's aggregate to its children in rounds
`bB u, …, bB u + L - 1` (`L = 2 Dg`). -/
noncomputable def mSched (u v : V) (t : ℕ) : Option (Word V) :=
  if par u = some v ∧ R u ≤ t ∧ t < R u + 2 * Dg then some (repWord (n + 4) Dg (Ag u) (t - R u))
  else if par v = some u ∧ bB Dg ρ dep R u ≤ t ∧ t < bB Dg ρ dep R u + 2 * Dg then
    some (repWord (n + 4) Dg (Ag ρ) (t - bB Dg ρ dep R u))
  else none

variable {n Dg ρ par dep R Ag}

lemma mSched_isSome {u v : V} {t : ℕ} (h : (mSched n Dg ρ par dep R Ag u v t).isSome) :
    (par u = some v ∧ R u ≤ t ∧ t < R u + 2 * Dg) ∨
      (par v = some u ∧ bB Dg ρ dep R u ≤ t ∧ t < bB Dg ρ dep R u + 2 * Dg) := by
  unfold mSched at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · simp at h

end Sched

/-! ## Clusters and slices -/

/-- hypotheses on the cluster family -/
structure ClH (N : WNet V) (cl : Finset (Finset (Sym2 V))) : Prop where
  sub : ∀ C ∈ cl, C ⊆ N.G.edgeFinset
  ne : ∀ C ∈ cl, C.Nonempty
  cover : ∀ e ∈ N.G.edgeFinset, ∃ C ∈ cl, e ∈ C
  disj : ∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C'

/-- the seeds of the copies of `C`: the component of the slice `C ∩ inc(v)` at every node -/
def seedC {Ω₀ : Type} (ω : V → Finset (Sym2 V) → Ω₀) (C : Finset (Sym2 V)) : V → Ω₀ :=
  fun v => ω v (C.filter (fun e => v ∈ e))

/-- the (trivial) input of a copy -/
def x0 : Agent V → Mem := inOf (fun _ : Agent V => ())

open Classical in
/-- the cluster of the slice `s` at `v` -/
noncomputable def clOf (cl : Finset (Finset (Sym2 V))) (v : V) (s : Finset (Sym2 V)) :
    Finset (Sym2 V) :=
  if h : ∃ C ∈ cl, C.filter (fun e => v ∈ e) = s then h.choose else ∅

section Slices

variable {N : WNet V} {cl : Finset (Finset (Sym2 V))}

lemma mem_clLoc {v : V} {s : Finset (Sym2 V)} :
    s ∈ clLoc cl v ↔ ∃ C ∈ cl, C.filter (fun e => v ∈ e) = s ∧ s.Nonempty := by
  unfold clLoc
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, hne⟩; exact ⟨C, hC, rfl, hne⟩
  · rintro ⟨C, hC, rfl, hne⟩; exact ⟨⟨C, hC, rfl⟩, hne⟩

lemma slice_nonempty {C : Finset (Sym2 V)} {v : V} (hv : v ∈ nodes C) :
    (C.filter (fun e => v ∈ e)).Nonempty := by
  obtain ⟨e, he, hve⟩ := mem_nodes.1 hv
  exact ⟨e, mem_filter.2 ⟨he, hve⟩⟩

lemma slice_mem_clLoc {C : Finset (Sym2 V)} (hC : C ∈ cl) {v : V} (hv : v ∈ nodes C) :
    C.filter (fun e => v ∈ e) ∈ clLoc cl v :=
  mem_clLoc.2 ⟨C, hC, rfl, slice_nonempty hv⟩

lemma eq_of_slice (hcl : ClH N cl) {C C' : Finset (Sym2 V)} (hC : C ∈ cl) (hC' : C' ∈ cl)
    {e : Sym2 V} (he : e ∈ C) (he' : e ∈ C') : C = C' := by
  by_contra hne
  exact disjoint_left.1 (hcl.disj C hC C' hC' hne) he he'

lemma clOf_spec (_hcl : ClH N cl) {v : V} {s : Finset (Sym2 V)} (hs : s ∈ clLoc cl v) :
    clOf cl v s ∈ cl ∧ (clOf cl v s).filter (fun e => v ∈ e) = s := by
  have h : ∃ C ∈ cl, C.filter (fun e => v ∈ e) = s := by
    obtain ⟨C, hC, h1, -⟩ := mem_clLoc.1 hs; exact ⟨C, hC, h1⟩
  unfold clOf
  rw [dif_pos h]
  exact h.choose_spec

lemma clOf_slice (hcl : ClH N cl) {C : Finset (Sym2 V)} (hC : C ∈ cl) {v : V}
    (hv : v ∈ nodes C) : clOf cl v (C.filter (fun e => v ∈ e)) = C := by
  obtain ⟨h1, h2⟩ := clOf_spec hcl (slice_mem_clLoc hC hv)
  obtain ⟨e, he⟩ := slice_nonempty hv
  have he' := he
  rw [← h2] at he'
  exact eq_of_slice hcl h1 hC (mem_filter.1 he').1 (mem_filter.1 he).1

lemma mem_clOf (hcl : ClH N cl) {v : V} {s : Finset (Sym2 V)} (hs : s ∈ clLoc cl v)
    {e : Sym2 V} (he : e ∈ s) : e ∈ clOf cl v s ∧ v ∈ e := by
  have h2 := (clOf_spec hcl hs).2
  rw [← h2] at he
  exact mem_filter.1 he

lemma mem_nodes_clOf (hcl : ClH N cl) {v : V} {s : Finset (Sym2 V)} (hs : s ∈ clLoc cl v) :
    v ∈ nodes (clOf cl v s) := by
  obtain ⟨C, hC, h1, ⟨e, he⟩⟩ := mem_clLoc.1 hs
  obtain ⟨h3, h4⟩ := mem_clOf hcl hs he
  exact mem_nodes.2 ⟨e, h3, h4⟩

/-- the slice of `v` containing an edge `e ∈ C` is that of `C` -/
lemma slice_eq_of_mem (hcl : ClH N cl) {v : V} {s : Finset (Sym2 V)} (hs : s ∈ clLoc cl v)
    {C : Finset (Sym2 V)} (hC : C ∈ cl) {e : Sym2 V} (he : e ∈ s) (heC : e ∈ C) :
    s = C.filter (fun e => v ∈ e) := by
  have h := clOf_spec hcl hs
  have := eq_of_slice hcl h.1 hC (mem_clOf hcl hs he).1 heC
  rw [← h.2, this]

lemma card_clLoc_le (hcl : ClH N cl) (v : V) : (clLoc cl v).card ≤ Fintype.card V := by
  classical
  -- each slice contains an edge `s(v, u)`; the map slice ↦ `u` is injective
  have key : ∀ s ∈ clLoc cl v, ∃ u, s(v, u) ∈ s := by
    intro s hs
    obtain ⟨C, hC, h1, ⟨e, he⟩⟩ := mem_clLoc.1 hs
    have hve := (mem_clOf hcl hs he).2
    exact ⟨Sym2.Mem.other hve, by rw [Sym2.other_spec hve]; exact he⟩
  let f : Finset (Sym2 V) → V := fun s => if h : ∃ u, s(v, u) ∈ s then h.choose else v
  have hinj : Set.InjOn f (clLoc cl v) := by
    intro s hs s' hs' hf
    have h1 := key s hs
    have h2 := key s' hs'
    simp only [f, dif_pos h1, dif_pos h2] at hf
    have e1 := h1.choose_spec
    have e2 := h2.choose_spec
    rw [hf] at e1
    have c1 := clOf_spec hcl hs
    have c2 := clOf_spec hcl hs'
    have := eq_of_slice hcl c1.1 c2.1 (mem_clOf hcl hs e1).1 (mem_clOf hcl hs' e2).1
    rw [← c1.2, ← c2.2, this]
  calc (clLoc cl v).card ≤ (univ : Finset V).card :=
        card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj
    _ = Fintype.card V := card_univ

/-- the context of a copy is that of the cluster instance -/
lemma cctx_base (hcl : ClH N cl) {C : Finset (Sym2 V)} (hC : C ∈ cl) {v : V} :
    cctx ((baseInst N).ctx v) (C.filter (fun e => v ∈ e)) = (clInst0 N C).ctx v := by
  classical
  have hv1 : ((baseInst N).ctx v).me = v := rfl
  have hv2 : ((baseInst N).ctx v).view (.inl v) = some (lview N (.inl v)) := by simp [baseInst]
  unfold cctx
  rw [hv1, hv2]
  simp only [Option.getD_some, clInst0, clInstP]
  congr 1
  funext g
  by_cases hg : g = .inl v
  · simp only [if_pos hg]
    congr 1
    funext e
    simp only [clView, lview, mem_filter]
    by_cases he : e ∈ C ∧ v ∈ e
    · simp only [if_pos he, if_pos (show e ∈ N.G.edgeFinset ∧ v ∈ e from ⟨hcl.sub C hC he.1, he.2⟩)]
    · simp only [if_neg he]
  · simp only [if_neg hg]

lemma cinp_base {C : Finset (Sym2 V)} {v : V} (hv : v ∈ nodes C) :
    cinp ((baseInst N).ctx v) = inpAt (clInst0 N C) x0 v := by
  classical
  funext g
  have hv1 : ((baseInst N).ctx v).me = v := rfl
  unfold cinp inpAt
  rw [hv1]
  cases g with
  | inl u =>
    by_cases hu : u = v
    · subst hu
      have h1 : (clInst0 N C).host (.inl u) = some u := by simp [clInst0, clInstP, clHost, hv]
      rw [if_pos rfl, if_pos h1]
      rfl
    · have h1 : (clInst0 N C).host (.inl u) ≠ some v := by
        simp only [clInst0, clInstP, clHost]
        split_ifs <;> simp [hu]
      have h2 : (Sum.inl u : Agent V) ≠ Sum.inl v := fun h => hu (Sum.inl_injective h)
      rw [if_neg h2, if_neg h1]
  | inr C' =>
    have h1 : (clInst0 N C).host (.inr C') = none := by simp [clInst0, clInstP, clHost]
    rw [if_neg (by simp), h1]
    simp

end Slices

lemma out_min_none {P : Proto V} {I : Inst V} {x : Agent V → Mem} {ω : V → P.Ω} {T : ℕ}
    (hH : HaltsAt P I x ω T) {v : V} (hv : I.part v) (t : ℕ) :
    P.out (st P I x ω (min t T) v) = none ↔ t < T := by
  by_cases ht : t < T
  · rw [min_eq_left ht.le]; exact ⟨fun _ => ht, fun _ => hH.2 t ht v hv⟩
  · rw [min_eq_right (by omega)]
    have := hH.1 v hv
    constructor
    · intro h; rw [h] at this; exact absurd this (by simp)
    · intro h; exact absurd h ht

/-! ## Unfolding the main phase -/

section MainUnfold

variable (P : Proto V) (Dg : ℕ)
  (valF : NCtx V → (Agent V → Option Mem) → (Finset (Sym2 V) → P.S) → ℕ × ℕ)
  (finF : NCtx V → (Agent V → Option Mem) → (Finset (Sym2 V) → P.S) → ℕ × ℕ →
    Agent V → Option Mem)

lemma mainP_init (c : NCtx V) (inp : Agent V → Option Mem) (ω : Finset (Sym2 V) → P.Ω) :
    (mainP P Dg valF finF).init c inp ω =
      (⟨c, inp, fun s => P.init (cctx c s) (cinp c) (ω s), none, []⟩ : MainS V P) := rfl

open Classical in
lemma mainP_send (c : NCtx V) (st : MainS V P) (u : V) :
    (mainP P Dg valF finF).send c st u =
      if h : runSl P st u then
        P.send (cctx st.c (Exists.choose h)) (st.cp (Exists.choose h)) u
      else tSend (Fintype.card V) Dg (valF st.c st.inp st.cp) (mPar st.inp st.c.me)
        (mKids st.inp st.c.me) (effDt P st) st.th u := rfl

open Classical in
lemma mainP_recv (c : NCtx V) (st : MainS V P) (m : V → Option (Word V)) :
    (mainP P Dg valF finF).recv c st m =
      (⟨st.c, st.inp, fun s => if s ∈ mSl st.inp st.c.me ∧ P.out (st.cp s) = none then
        P.recv (cctx st.c s) (st.cp s) (fun u => if s(st.c.me, u) ∈ s then m u else none)
        else st.cp s, effDt P st, st.th ++ [fun u => if runSl P st u then none else m u]⟩ :
          MainS V P) := rfl

open Classical in
lemma mainP_out (st : MainS V P) :
    (mainP P Dg valF finF).out st =
      if tHalt (Fintype.card V) Dg (mDep st.inp st.c.me) (mPar st.inp st.c.me)
        (mKids st.inp st.c.me) (effDt P st) st.th then
      some (finF st.c st.inp st.cp (gVal (Fintype.card V + 4) Dg (valF st.c st.inp st.cp)
        (mPar st.inp st.c.me) (mKids st.inp st.c.me) st.th)) else none := rfl

end MainUnfold

lemma MainS.ext' {P : Proto V} (a b : MainS V P) (h1 : a.c = b.c) (h2 : a.inp = b.inp)
    (h3 : a.cp = b.cp) (h4 : a.dt = b.dt) (h5 : a.th = b.th) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-! ## The data of a run of the main phase -/

/-- the data of a run of the main phase: the protocol and its parameters, the network, the
clusters, the BFS tree, the input, the seeds, and the halting rounds `T C` of the standalone runs
of the copies -/
structure PD (V : Type) [Fintype V] [DecidableEq V] where
  P : Proto V
  Dg : ℕ
  valF : NCtx V → (Agent V → Option Mem) → (Finset (Sym2 V) → P.S) → ℕ × ℕ
  finF : NCtx V → (Agent V → Option Mem) → (Finset (Sym2 V) → P.S) → ℕ × ℕ →
    Agent V → Option Mem
  N : WNet V
  cl : Finset (Finset (Sym2 V))
  ρ : V
  par : V → Option V
  dep : V → ℕ
  x' : Agent V → Mem
  ω : V → Finset (Sym2 V) → P.Ω
  T : Finset (Sym2 V) → ℕ

namespace PD

variable (d : PD V)

/-- the main-phase protocol -/
noncomputable abbrev run : Proto V := mainP d.P d.Dg d.valF d.finF

/-- the state of the composite run -/
noncomputable def stM (t : ℕ) : V → MainS V d.P := st d.run (baseInst d.N) d.x' d.ω t

/-- the state of the standalone run of `C` -/
noncomputable def stC (C : Finset (Sym2 V)) (t : ℕ) : V → d.P.S :=
  st d.P (clInst0 d.N C) x0 (seedC d.ω C) t

open Classical in
/-- the expected copy states at round `t` -/
noncomputable def cpE (t : ℕ) (v : V) (s : Finset (Sym2 V)) : d.P.S :=
  if s ∈ clLoc d.cl v then d.stC (clOf d.cl v s) (min t (d.T (clOf d.cl v s))) v
  else d.P.init (cctx ((baseInst d.N).ctx v) s) (cinp ((baseInst d.N).ctx v)) (d.ω v s)

/-- the round in which all clusters of `v` have halted -/
noncomputable def D (v : V) : ℕ := (d.cl.filter (fun C => v ∈ nodes C)).sup d.T

/-- the final copy states -/
noncomputable def cpF (v : V) : Finset (Sym2 V) → d.P.S := d.cpE (d.cl.sup d.T) v

/-- the local values -/
noncomputable def val (v : V) : ℕ × ℕ :=
  d.valF ((baseInst d.N).ctx v) (inpAt (baseInst d.N) d.x' v) (d.cpF v)

/-- the report rounds -/
noncomputable def R : V → ℕ := tmax d.par d.dep d.D (2 * d.Dg)

/-- the aggregates over subtrees -/
noncomputable def Ag (u : V) : ℕ × ℕ :=
  (tmax d.par d.dep (fun v => (d.val v).1) 0 u, tmax d.par d.dep (fun v => (d.val v).2) 0 u)

/-- the schedule of the tree words -/
noncomputable def M : V → V → ℕ → Option (Word V) :=
  mSched (Fintype.card V) d.Dg d.ρ d.par d.dep d.R d.Ag

/-- the halting round -/
noncomputable def H : ℕ := d.R d.ρ + 2 * d.Dg * Fintype.card V

/-- the done round as known at round `t` -/
noncomputable def edAt (v : V) (t : ℕ) : Option ℕ := if d.D v ≤ t then some (d.D v) else none

/-- the expected state of the composite run at round `t` -/
noncomputable def expS (t : ℕ) (v : V) : MainS V d.P :=
  ⟨(baseInst d.N).ctx v, inpAt (baseInst d.N) d.x' v, d.cpE t v,
    if d.D v < t then some (d.D v) else none, schedHist d.M v t⟩

/-- the hypotheses of the parallel-composition lemma -/
structure Ok : Prop where
  cl : ClH d.N d.cl
  tree : TreeH d.N d.ρ d.par d.dep
  sl : ∀ v, mSl (inpAt (baseInst d.N) d.x' v) v = clLoc d.cl v
  pa : ∀ v, mPar (inpAt (baseInst d.N) d.x' v) v = d.par v
  ki : ∀ v, mKids (inpAt (baseInst d.N) d.x' v) v = univ.filter (fun c => d.par c = some v)
  de : ∀ v, mDep (inpAt (baseInst d.N) d.x' v) v = d.dep v
  halts : ∀ C ∈ d.cl, HaltsAt d.P (clInst0 d.N C) x0 (seedC d.ω C) (d.T C)
  dg : 1 ≤ d.Dg
  vb : ∀ v, (d.val v).1 < (Fintype.card V + 4) ^ d.Dg ∧ (d.val v).2 < (Fintype.card V + 4) ^ d.Dg

lemma cpE_slice' (hcl : ClH d.N d.cl) {C : Finset (Sym2 V)} (hC : C ∈ d.cl) {v : V}
    (hv : v ∈ nodes C) (t : ℕ) :
    d.cpE t v (C.filter (fun e => v ∈ e)) = d.stC C (min t (d.T C)) v := by
  classical
  unfold PD.cpE
  rw [if_pos (slice_mem_clLoc hC hv), clOf_slice hcl hC hv]

lemma cpF_slice (hcl : ClH d.N d.cl) {C : Finset (Sym2 V)} (hC : C ∈ d.cl) {v : V}
    (hv : v ∈ nodes C) : d.cpF v (C.filter (fun e => v ∈ e)) = d.stC C (d.T C) v := by
  unfold PD.cpF
  rw [d.cpE_slice' hcl hC hv, min_eq_right (le_sup (f := d.T) hC)]

end PD

namespace PD.Ok

variable {d : PD V} (h : d.Ok)
include h

/-! ### The schedule -/

lemma R_kid {u c : V} (hc : d.par c = some u) : d.R c + 2 * d.Dg ≤ d.R u :=
  tmax_kid h.tree.rk d.D _ hc

lemma D_le_R (u : V) : d.D u ≤ d.R u := le_tmax h.tree.rk d.D _ u

lemma R_le_root (u : V) : d.R u ≤ d.R d.ρ :=
  h.tree.le_root d.R (fun _ _ hc => le_trans (Nat.le_add_right _ _) (h.R_kid hc)) u

lemma R_eq (u : V) : d.R u = max (d.D u) ((kidsOf univ d.par u).sup (fun c => d.R c + 2 * d.Dg)) :=
  tmax_eq h.tree.rk d.D _ u

lemma Ag_eq (u : V) : d.Ag u = (max (d.val u).1 ((kidsOf univ d.par u).sup (fun c => (d.Ag c).1)),
    max (d.val u).2 ((kidsOf univ d.par u).sup (fun c => (d.Ag c).2))) := by
  simp only [PD.Ag]
  rw [tmax_eq h.tree.rk _ 0 u, tmax_eq h.tree.rk (fun v => (d.val v).2) 0 u]
  simp

lemma tmax0_root (f : V → ℕ) : tmax d.par d.dep f 0 d.ρ = univ.sup f := by
  apply le_antisymm
  · exact tmax_le h.tree.rk f 0 (fun _ => univ.sup f) (fun u => le_sup (mem_univ u))
      (fun _ _ _ => le_rfl) d.ρ
  · refine Finset.sup_le (fun w _ => le_trans (le_tmax h.tree.rk f 0 w) ?_)
    exact h.tree.le_root _ (fun c p hc => by
      have := tmax_kid h.tree.rk f 0 hc; omega) w

lemma Ag_root : d.Ag d.ρ = (univ.sup (fun w => (d.val w).1), univ.sup (fun w => (d.val w).2)) := by
  simp only [PD.Ag, h.tmax0_root]

lemma Ag_lt (u : V) : (d.Ag u).1 < (Fintype.card V + 4) ^ d.Dg ∧
    (d.Ag u).2 < (Fintype.card V + 4) ^ d.Dg := by
  have hpos : 0 < (Fintype.card V + 4) ^ d.Dg := by positivity
  constructor
  · refine lt_of_le_of_lt (tmax_le h.tree.rk _ 0
      (fun _ => univ.sup (fun w => (d.val w).1)) (fun u => le_sup (f := fun w => (d.val w).1)
        (mem_univ u)) (fun _ _ _ => le_rfl) u) ?_
    rcases (univ : Finset V).eq_empty_or_nonempty with he | hne
    · simp [he, hpos]
    · obtain ⟨w, _, hw⟩ := exists_mem_eq_sup _ hne (fun w => (d.val w).1)
      rw [hw]; exact (h.vb w).1
  · refine lt_of_le_of_lt (tmax_le h.tree.rk _ 0
      (fun _ => univ.sup (fun w => (d.val w).2)) (fun u => le_sup (f := fun w => (d.val w).2)
        (mem_univ u)) (fun _ _ _ => le_rfl) u) ?_
    rcases (univ : Finset V).eq_empty_or_nonempty with he | hne
    · simp [he, hpos]
    · obtain ⟨w, _, hw⟩ := exists_mem_eq_sup _ hne (fun w => (d.val w).2)
      rw [hw]; exact (h.vb w).2

lemma R_bound (u : V) : d.R u + 2 * d.Dg * d.dep u ≤
    univ.sup d.D + 2 * d.Dg * (Fintype.card V - 1) := by
  have key := tmax_le h.tree.rk d.D (2 * d.Dg)
    (fun u => univ.sup d.D + 2 * d.Dg * (Fintype.card V - 1) - 2 * d.Dg * d.dep u)
    (fun u => by
      have h1 : d.D u ≤ univ.sup d.D := le_sup (mem_univ u)
      have h2 : 2 * d.Dg * d.dep u ≤ 2 * d.Dg * (Fintype.card V - 1) :=
        Nat.mul_le_mul_left _ (by have := h.tree.dep_lt u; omega)
      omega)
    (fun u c hc => by
      have h1 := h.tree.dep_par c u hc
      have h2 := h.tree.dep_lt c
      have h3 : 2 * d.Dg * d.dep c ≤ 2 * d.Dg * (Fintype.card V - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [h1, Nat.mul_add, mul_one] at h3 ⊢
      omega) u
  have h2 : 2 * d.Dg * d.dep u ≤ 2 * d.Dg * (Fintype.card V - 1) :=
    Nat.mul_le_mul_left _ (by have := h.tree.dep_lt u; omega)
  change d.R u ≤ _ - _ at key
  omega

lemma D_le_sup (v : V) : d.D v ≤ d.cl.sup d.T :=
  Finset.sup_le (fun _ hC => le_sup (mem_filter.1 hC).1)

lemma H_bound : d.H ≤ d.cl.sup d.T + 2 * (2 * d.Dg) * Fintype.card V := by
  have h1 := h.R_bound d.ρ
  rw [h.tree.dep_root, mul_zero, add_zero] at h1
  have h2 : univ.sup d.D ≤ d.cl.sup d.T := Finset.sup_le (fun v _ => h.D_le_sup v)
  have h3 : 2 * d.Dg * (Fintype.card V - 1) ≤ 2 * d.Dg * Fintype.card V :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  unfold PD.H
  nlinarith

lemma M_up {u v : V} (huv : d.par u = some v) (t : ℕ) :
    d.M u v t = if d.R u ≤ t ∧ t < d.R u + 2 * d.Dg then
      some (repWord (Fintype.card V + 4) d.Dg (d.Ag u) (t - d.R u)) else none := by
  unfold PD.M mSched
  have hvu := h.tree.not_par_par huv
  by_cases h1 : d.R u ≤ t ∧ t < d.R u + 2 * d.Dg
  · rw [if_pos ⟨huv, h1⟩, if_pos h1]
  · rw [if_neg (fun h' => h1 h'.2), if_neg h1, if_neg (fun h' => hvu h'.1)]

lemma M_down {u v : V} (hvu : d.par v = some u) (t : ℕ) :
    d.M u v t = if bB d.Dg d.ρ d.dep d.R u ≤ t ∧ t < bB d.Dg d.ρ d.dep d.R u + 2 * d.Dg then
      some (repWord (Fintype.card V + 4) d.Dg (d.Ag d.ρ) (t - bB d.Dg d.ρ d.dep d.R u))
      else none := by
  unfold PD.M mSched
  have huv := h.tree.not_par_par hvu
  rw [if_neg (fun h' => huv h'.1)]
  by_cases h1 : bB d.Dg d.ρ d.dep d.R u ≤ t ∧ t < bB d.Dg d.ρ d.dep d.R u + 2 * d.Dg
  · rw [if_pos ⟨hvu, h1⟩, if_pos h1]
  · rw [if_neg (fun h' => h1 h'.2), if_neg h1]

lemma M_none {u v : V} (h1 : d.par u ≠ some v) (h2 : d.par v ≠ some u) (t : ℕ) :
    d.M u v t = none := by
  unfold PD.M mSched
  rw [if_neg (fun h' => h1 h'.1), if_neg (fun h' => h2 h'.1)]

lemma M_cases {u v : V} {t : ℕ} (hM : (d.M u v t).isSome) :
    (d.par u = some v ∧ d.R u ≤ t ∧ t < d.R u + 2 * d.Dg) ∨
      (d.par v = some u ∧ bB d.Dg d.ρ d.dep d.R u ≤ t ∧
        t < bB d.Dg d.ρ d.dep d.R u + 2 * d.Dg) :=
  mSched_isSome hM

lemma M_adj {u v : V} {t : ℕ} (hM : (d.M u v t).isSome) : d.N.G.Adj u v := by
  rcases h.M_cases hM with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h.tree.adj u v h1
  · exact (h.tree.adj v u h1).symm

lemma bB_kid {u v : V} (hvu : d.par v = some u) :
    bB d.Dg d.ρ d.dep d.R u + 2 * d.Dg = bB d.Dg d.ρ d.dep d.R v := by
  unfold bB; rw [h.tree.dep_par v u hvu]; ring

lemma bB_le_H (u : V) : bB d.Dg d.ρ d.dep d.R u + 2 * d.Dg ≤ d.H := by
  unfold bB PD.H
  have := h.tree.dep_lt u
  have : 2 * d.Dg * d.dep u + 2 * d.Dg ≤ 2 * d.Dg * Fintype.card V := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
  omega

lemma root_le_bB (u : V) : d.R d.ρ ≤ bB d.Dg d.ρ d.dep d.R u := by
  unfold bB; omega

lemma M_lt_H {u v : V} {t : ℕ} (hM : (d.M u v t).isSome) : t < d.H := by
  rcases h.M_cases hM with ⟨h1, -, h3⟩ | ⟨-, -, h3⟩
  · have := h.R_kid h1
    have := h.R_le_root v
    have : d.R d.ρ ≤ d.H := Nat.le_add_right _ _
    omega
  · have := h.bB_le_H u; omega

lemma M_ge_T {u v : V} {t : ℕ} (hM : (d.M u v t).isSome) {C : Finset (Sym2 V)} (hC : C ∈ d.cl)
    (he : s(u, v) ∈ C) : d.T C ≤ t := by
  have hu : u ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_left u v⟩
  have hv : v ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_right u v⟩
  have hTu : d.T C ≤ d.D u := le_sup (f := d.T) (mem_filter.2 ⟨hC, hu⟩)
  have hTv : d.T C ≤ d.D v := le_sup (f := d.T) (mem_filter.2 ⟨hC, hv⟩)
  rcases h.M_cases hM with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
  · have := h.D_le_R u; omega
  · have := h.D_le_R v; have := h.R_le_root v; have := h.root_le_bB u; omega

lemma repWord_ok (Dg : ℕ) (a : ℕ × ℕ) (j : ℕ) :
    WordOK (Fintype.card V) (repWord (V := V) (Fintype.card V + 4) Dg a j) := by
  unfold repWord
  split_ifs
  · show _ ≤ _; have := Nat.mod_lt (a.1 / (Fintype.card V + 4) ^ j) (show 0 < Fintype.card V + 4 by omega); omega
  · show _ ≤ _; have := Nat.mod_lt (a.2 / (Fintype.card V + 4) ^ (j - Dg)) (show 0 < Fintype.card V + 4 by omega); omega

lemma M_ok {u v : V} {t : ℕ} {w : Word V} (hM : d.M u v t = some w) :
    WordOK (Fintype.card V) w := by
  unfold PD.M mSched at hM
  split_ifs at hM
  · cases hM; exact repWord_ok h _ _ _
  · cases hM; exact repWord_ok h _ _ _

end PD.Ok

/-! ## Histories of a schedule -/

section HistLemmas

lemma fstIdx_sched (M : V → V → ℕ → Option (Word V)) (v c : V) (t a L : ℕ) (hL : 1 ≤ L)
    (hM : ∀ i, (M c v i).isSome ↔ a ≤ i ∧ i < a + L) :
    fstIdx (schedHist M v t) c = if a < t then some a else none := by
  classical
  unfold fstIdx
  have hex : (∃ i, i < (schedHist M v t).length ∧ (hget (schedHist M v t) i c).isSome) ↔ a < t := by
    rw [length_schedHist]
    constructor
    · rintro ⟨i, hi, h⟩
      rw [hget_schedHist M v hi, hM] at h
      omega
    · intro ha
      exact ⟨a, ha, by rw [hget_schedHist M v ha, hM]; omega⟩
  by_cases ha : a < t
  · have hh := hex.2 ha
    rw [dif_pos hh, if_pos ha]
    congr 1
    rw [Nat.find_eq_iff]
    refine ⟨⟨by rw [length_schedHist]; exact ha, by rw [hget_schedHist M v ha, hM]; omega⟩, ?_⟩
    rintro i hi ⟨hi1, hi2⟩
    rw [length_schedHist] at hi1
    rw [hget_schedHist M v hi1, hM] at hi2
    omega
  · rw [dif_neg (fun hh => ha (hex.1 hh)), if_neg ha]

lemma decRep_sched (M : V → V → ℕ → Option (Word V)) (v c : V) (t a β Dg : ℕ) (X : ℕ × ℕ)
    (hM : ∀ j < 2 * Dg, M c v (a + j) = some (repWord β Dg X j)) (ht : a + 2 * Dg ≤ t)
    (hX : X.1 < β ^ Dg ∧ X.2 < β ^ Dg) :
    decRep β Dg (schedHist M v t) c a = X := by
  unfold decRep
  have hf : ∀ j < 2 * Dg, (hget (schedHist M v t) (a + j) c).getD (.num 0) = repWord β Dg X j := by
    intro j hj
    rw [hget_schedHist M v (by omega), hM j hj]; rfl
  refine Prod.ext ?_ ?_
  · dsimp only
    refine decD_digits β Dg X.1 a _ (fun j hj => ?_) hX.1
    rw [hf j (by omega)]; unfold repWord; rw [if_pos hj]
  · dsimp only
    refine decD_digits β Dg X.2 (a + Dg) _ (fun j hj => ?_) hX.2
    rw [add_assoc, hf (Dg + j) (by omega)]; unfold repWord
    rw [if_neg (by omega), Nat.add_sub_cancel_left]

end HistLemmas

namespace PD.Ok

variable {d : PD V} (h : d.Ok)
include h

/-- the history of `v` after `t` rounds of the schedule -/
local notation "HS" v:max t:max => schedHist d.M v t

lemma kids_iff {u c : V} : c ∈ univ.filter (fun c => d.par c = some u) ↔ d.par c = some u := by
  simp

lemma M_kid_iff {u c : V} (hc : d.par c = some u) (i : ℕ) :
    (d.M c u i).isSome ↔ d.R c ≤ i ∧ i < d.R c + 2 * d.Dg := by
  rw [h.M_up hc]; split_ifs with h1 <;> simp [h1]

lemma M_par_iff {v p : V} (hp : d.par v = some p) (i : ℕ) :
    (d.M p v i).isSome ↔ bB d.Dg d.ρ d.dep d.R p ≤ i ∧ i < bB d.Dg d.ρ d.dep d.R p + 2 * d.Dg := by
  rw [h.M_down hp]; split_ifs with h1 <;> simp [h1]

lemma fstIdx_kid {u c : V} (hc : d.par c = some u) (t : ℕ) :
    fstIdx (HS u t) c = if d.R c < t then some (d.R c) else none :=
  fstIdx_sched d.M u c t (d.R c) (2 * d.Dg) (by have := h.dg; omega) (h.M_kid_iff hc)

lemma fstIdx_par {v p : V} (hp : d.par v = some p) (t : ℕ) :
    fstIdx (HS v t) p = if bB d.Dg d.ρ d.dep d.R p < t then some (bB d.Dg d.ρ d.dep d.R p)
      else none :=
  fstIdx_sched d.M v p t _ (2 * d.Dg) (by have := h.dg; omega) (h.M_par_iff hp)

lemma decRep_kid {u c : V} (hc : d.par c = some u) {t : ℕ} (ht : d.R c + 2 * d.Dg ≤ t) :
    decRep (Fintype.card V + 4) d.Dg (HS u t) c (d.R c) = d.Ag c := by
  refine decRep_sched d.M u c t (d.R c) _ d.Dg (d.Ag c) (fun j hj => ?_) ht (h.Ag_lt c)
  rw [h.M_up hc, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

lemma decRep_par {v p : V} (hp : d.par v = some p) {t : ℕ}
    (ht : bB d.Dg d.ρ d.dep d.R p + 2 * d.Dg ≤ t) :
    decRep (Fintype.card V + 4) d.Dg (HS v t) p (bB d.Dg d.ρ d.dep d.R p) = d.Ag d.ρ := by
  refine decRep_sched d.M v p t _ _ d.Dg (d.Ag d.ρ) (fun j hj => ?_) ht (h.Ag_lt d.ρ)
  rw [h.M_down hp, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

lemma repSt_sched (u : V) (t : ℕ) :
    (∀ R', repSt (2 * d.Dg) (univ.filter (fun c => d.par c = some u)) (d.edAt u t) (HS u t) =
      some R' → R' = d.R u) ∧
    (d.R u ≤ t → repSt (2 * d.Dg) (univ.filter (fun c => d.par c = some u)) (d.edAt u t)
      (HS u t) = some (d.R u)) := by
  classical
  have hsup : ∀ (hall : ∀ c ∈ univ.filter (fun c => d.par c = some u), d.R c < t),
      max (d.D u) ((univ.filter (fun c => d.par c = some u)).sup
        (fun c => (fstIdx (HS u t) c).getD 0 + 2 * d.Dg)) = d.R u := by
    intro hall
    rw [h.R_eq u]
    congr 1
    refine Finset.sup_congr rfl (fun c hc => ?_)
    have hc' := (mem_filter.1 hc).2
    rw [h.fstIdx_kid hc' t, if_pos (hall c hc)]
    rfl
  have hiff : (∀ c ∈ univ.filter (fun c => d.par c = some u), (fstIdx (HS u t) c).isSome) ↔
      ∀ c ∈ univ.filter (fun c => d.par c = some u), d.R c < t := by
    refine forall₂_congr (fun c hc => ?_)
    rw [h.fstIdx_kid (mem_filter.1 hc).2 t]
    split_ifs with h1 <;> simp [h1]
  constructor
  · intro R' hR
    unfold repSt PD.edAt at hR
    split_ifs at hR with h1 h2
    · simp only [Option.some.injEq] at hR
      rw [← hR]; exact hsup (hiff.1 h2)
  · intro hR
    have hD : d.D u ≤ t := le_trans (h.D_le_R u) hR
    have hall : ∀ c ∈ univ.filter (fun c => d.par c = some u), d.R c < t := by
      intro c hc
      have := h.R_kid (mem_filter.1 hc).2
      have := h.dg
      omega
    unfold repSt PD.edAt
    rw [if_pos hD]
    dsimp only
    rw [if_pos (hiff.2 hall), hsup hall]

lemma ecAgg_sched (u : V) {t : ℕ} (ht : d.R u ≤ t) :
    ecAgg (Fintype.card V + 4) d.Dg (d.val u) (univ.filter (fun c => d.par c = some u)) (HS u t) =
      d.Ag u := by
  have hk : ∀ c ∈ univ.filter (fun c => d.par c = some u),
      decRep (Fintype.card V + 4) d.Dg (HS u t) c ((fstIdx (HS u t) c).getD 0) = d.Ag c := by
    intro c hc
    have hc' := (mem_filter.1 hc).2
    have h1 := h.R_kid hc'
    have := h.dg
    rw [h.fstIdx_kid hc' t, if_pos (by omega)]
    exact h.decRep_kid hc' (by omega)
  rw [h.Ag_eq u]
  unfold ecAgg
  have hfil : kidsOf univ d.par u = univ.filter (fun c => d.par c = some u) := by
    ext c; simp [mem_kidsOf]
  rw [hfil]
  refine Prod.ext ?_ ?_
  · simp only
    congr 1
    exact Finset.sup_congr rfl (fun c hc => by rw [hk c hc])
  · simp only
    congr 1
    exact Finset.sup_congr rfl (fun c hc => by rw [hk c hc])

lemma root_iff (u : V) : d.par u = none ↔ u = d.ρ :=
  ⟨fun hu => by_contra (fun hne => h.tree.par_ne u hne hu), fun hu => hu ▸ h.tree.root⟩

lemma bB_root : bB d.Dg d.ρ d.dep d.R d.ρ = d.R d.ρ := by
  unfold bB; rw [h.tree.dep_root, mul_zero, add_zero]

/-- **The tree words follow the schedule.** -/
lemma tSend_sched (u v : V) (t : ℕ) (vl : ℕ × ℕ) (hvl : d.D u ≤ t → vl = d.val u) :
    tSend (Fintype.card V) d.Dg vl (d.par u) (univ.filter (fun c => d.par c = some u))
      (d.edAt u t) (HS u t) v = d.M u v t := by
  classical
  have hL := h.dg
  have hlen : (HS u t).length = t := length_schedHist _ _ _
  have hmy : d.R u ≤ t → ecAgg (Fintype.card V + 4) d.Dg vl
      (univ.filter (fun c => d.par c = some u)) (HS u t) = d.Ag u := by
    intro hR
    rw [hvl (le_trans (h.D_le_R u) hR)]
    exact h.ecAgg_sched u hR
  -- the report branch, shared by the parent and the root's broadcast
  have hrep : ∀ (X : ℕ × ℕ), (d.R u ≤ t → X = d.Ag u) →
      (match repSt (2 * d.Dg) (univ.filter (fun c => d.par c = some u)) (d.edAt u t) (HS u t) with
       | some R => if R ≤ t ∧ t < R + 2 * d.Dg then
           some (repWord (V := V) (Fintype.card V + 4) d.Dg X (t - R)) else none
       | none => none) =
      if d.R u ≤ t ∧ t < d.R u + 2 * d.Dg then
        some (repWord (V := V) (Fintype.card V + 4) d.Dg (d.Ag u) (t - d.R u)) else none := by
    intro X hX
    obtain ⟨h1, h2⟩ := h.repSt_sched u t
    by_cases hR : d.R u ≤ t
    · rw [h2 hR, hX hR]
    · cases hr : repSt (2 * d.Dg) (univ.filter (fun c => d.par c = some u)) (d.edAt u t)
        (HS u t) with
      | none => rw [if_neg (fun h' => hR h'.1)]
      | some R' =>
        rw [h1 R' hr]
        simp only
        rw [if_neg (fun h' => hR h'.1), if_neg (fun h' => hR h'.1)]
  unfold tSend
  rw [hlen]
  by_cases hp : d.par u = some v
  · rw [if_pos hp, h.M_up hp]
    exact hrep _ hmy
  · rw [if_neg hp]
    by_cases hk : v ∈ univ.filter (fun c => d.par c = some u)
    · rw [if_pos hk]
      have hvu : d.par v = some u := (mem_filter.1 hk).2
      rw [h.M_down hvu]
      cases hpu : d.par u with
      | none =>
        have hu := (h.root_iff u).1 hpu
        subst hu
        simp only [bSt]
        rw [h.bB_root]
        have := hrep _ hmy
        -- the root's broadcast uses the same start as its report
        revert this
        cases repSt (2 * d.Dg) (univ.filter (fun c => d.par c = some d.ρ)) (d.edAt d.ρ t)
          (HS d.ρ t) with
        | none => intro this; exact this
        | some R' =>
          intro this
          simp only at this ⊢
          by_cases hc : R' ≤ t ∧ t < R' + 2 * d.Dg
          · rw [if_pos hc] at this ⊢; exact this
          · rw [if_neg hc] at this ⊢; exact this
      | some p =>
        simp only [bSt]
        rw [h.fstIdx_par hpu t]
        have hb := h.bB_kid hpu
        by_cases hpt : bB d.Dg d.ρ d.dep d.R p < t
        · rw [if_pos hpt]
          simp only [Option.map_some]
          rw [hb]
          by_cases hc : bB d.Dg d.ρ d.dep d.R u ≤ t ∧ t < bB d.Dg d.ρ d.dep d.R u + 2 * d.Dg
          · rw [if_pos hc, if_pos hc]
            rw [hget_schedHist d.M u (by omega), h.M_down hpu, if_pos ⟨by omega, by omega⟩]
            congr 2
            omega
          · rw [if_neg hc, if_neg hc]
        · rw [if_neg hpt]
          simp only [Option.map_none]
          rw [if_neg (by omega)]
    · rw [if_neg hk]
      have hvu : d.par v ≠ some u := fun h' => hk (mem_filter.2 ⟨mem_univ _, h'⟩)
      rw [h.M_none hp hvu]

lemma tHalt_sched (v : V) (t : ℕ) :
    tHalt (Fintype.card V) d.Dg (d.dep v) (d.par v) (univ.filter (fun c => d.par c = some v))
      (d.edAt v t) (HS v t) ↔ d.H ≤ t := by
  have hL := h.dg
  have hlen : (HS v t).length = t := length_schedHist _ _ _
  unfold tHalt
  rw [hlen]
  cases hpv : d.par v with
  | none =>
    have hv := (h.root_iff v).1 hpv
    subst hv
    simp only [bSt]
    obtain ⟨h1, h2⟩ := h.repSt_sched d.ρ t
    rw [h.tree.dep_root, Nat.sub_zero]
    constructor
    · rintro ⟨B, hB, hBt⟩
      rw [h1 B hB] at hBt
      exact hBt
    · intro hH
      exact ⟨d.R d.ρ, h2 (by unfold PD.H at hH; omega), hH⟩
  | some p =>
    simp only [bSt]
    rw [h.fstIdx_par hpv t]
    have hb := h.bB_kid hpv
    have hdv := h.tree.dep_lt v
    have hdp := h.tree.dep_par v p hpv
    have hH : bB d.Dg d.ρ d.dep d.R p + 2 * d.Dg + 2 * d.Dg * (Fintype.card V - d.dep v) = d.H := by
      rw [hb]; unfold bB PD.H
      rw [add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hdv.le]
    constructor
    · rintro ⟨B, hB, hBt⟩
      split_ifs at hB with h1
      · simp only [Option.map_some, Option.some.injEq] at hB
        omega
      · simp at hB
    · intro hHt
      have h1 : bB d.Dg d.ρ d.dep d.R p < t := by
        have : 0 < 2 * d.Dg := by omega
        omega
      exact ⟨bB d.Dg d.ρ d.dep d.R p + 2 * d.Dg, by rw [if_pos h1]; rfl, by omega⟩

lemma gVal_sched (v : V) {t : ℕ} (ht : d.H ≤ t) (vl : ℕ × ℕ) (hvl : d.D v ≤ t → vl = d.val v) :
    gVal (Fintype.card V + 4) d.Dg vl (d.par v) (univ.filter (fun c => d.par c = some v)) (HS v t) =
      d.Ag d.ρ := by
  cases hpv : d.par v with
  | none =>
    have hv := (h.root_iff v).1 hpv
    subst hv
    simp only [gVal]
    have hR : d.R d.ρ ≤ t := by unfold PD.H at ht; omega
    rw [hvl (le_trans (h.D_le_R _) hR)]
    exact h.ecAgg_sched d.ρ hR
  | some p =>
    simp only [gVal]
    have := h.bB_le_H p
    have hb := h.bB_kid hpv
    have hv := h.bB_le_H v
    have hL := h.dg
    rw [h.fstIdx_par hpv t, if_pos (by omega)]
    exact h.decRep_par hpv (by omega)

end PD.Ok

/-! ## Messages -/

open Classical in
lemma msg_eq_send {P : Proto V} {I : Inst V} {σ : V → P.S} {u v : V} (hadj : I.G.Adj u v)
    (hout : P.out (σ u) = none) :
    msg P I σ u v = (P.send (I.ctx u) (σ u) v).bind
      (fun w => if WordOK (Fintype.card V) w then some w else none) := by
  classical
  unfold msg
  rw [if_pos ⟨hadj, hout⟩]
  cases P.send (I.ctx u) (σ u) v <;> rfl

lemma msg_eq_none {P : Proto V} {I : Inst V} {σ : V → P.S} {u v : V} (hadj : ¬ I.G.Adj u v) :
    msg P I σ u v = none := by
  classical
  unfold msg
  rw [if_neg (fun h => hadj h.1)]

namespace PD.Ok

variable {d : PD V} (h : d.Ok)
include h

/-! ### The expected states -/

omit h in
@[simp] lemma expS_c (t : ℕ) (v : V) : (d.expS t v).c = (baseInst d.N).ctx v := rfl
omit h in
@[simp] lemma expS_inp (t : ℕ) (v : V) : (d.expS t v).inp = inpAt (baseInst d.N) d.x' v := rfl
omit h in
@[simp] lemma expS_cp (t : ℕ) (v : V) : (d.expS t v).cp = d.cpE t v := rfl
omit h in
@[simp] lemma expS_th (t : ℕ) (v : V) : (d.expS t v).th = schedHist d.M v t := rfl
omit h in
@[simp] lemma base_me (v : V) : ((baseInst d.N).ctx v).me = v := rfl

lemma mSl_expS (t : ℕ) (v : V) : mSl (d.expS t v).inp (d.expS t v).c.me = clLoc d.cl v := h.sl v

lemma cpE_slice {C : Finset (Sym2 V)} (hC : C ∈ d.cl) {v : V} (hv : v ∈ nodes C) (t : ℕ) :
    d.cpE t v (C.filter (fun e => v ∈ e)) = d.stC C (min t (d.T C)) v :=
  d.cpE_slice' h.cl hC hv t

lemma out_cpE {C : Finset (Sym2 V)} (hC : C ∈ d.cl) {v : V} (hv : v ∈ nodes C) (t : ℕ) :
    d.P.out (d.cpE t v (C.filter (fun e => v ∈ e))) = none ↔ t < d.T C := by
  rw [h.cpE_slice hC hv]
  exact out_min_none (h.halts C hC) (show (clInst0 d.N C).part v from hv) t

lemma allH_expS (t : ℕ) (v : V) : allH d.P (d.expS t v) ↔ d.D v ≤ t := by
  unfold allH
  rw [h.mSl_expS]
  constructor
  · intro hall
    refine Finset.sup_le (fun C hC => ?_)
    obtain ⟨hC, hv⟩ := mem_filter.1 hC
    have h1 := hall _ (slice_mem_clLoc hC hv)
    have h2 := h.out_cpE hC hv t
    by_contra hlt
    rw [expS_cp, h2.2 (by omega)] at h1
    exact absurd h1 (by simp)
  · intro hD s hs
    obtain ⟨hC, hsl⟩ := clOf_spec h.cl hs
    have hv := mem_nodes_clOf h.cl hs
    have hT : d.T (clOf d.cl v s) ≤ t := le_trans (le_sup (f := d.T) (mem_filter.2 ⟨hC, hv⟩)) hD
    have h2 := h.out_cpE hC hv t
    rw [hsl] at h2
    rw [expS_cp, Option.isSome_iff_ne_none]
    intro hn; exact absurd (h2.1 hn) (by omega)

lemma effDt_expS (t : ℕ) (v : V) : effDt d.P (d.expS t v) = d.edAt v t := by
  classical
  unfold effDt PD.edAt
  show (match (if d.D v < t then some (d.D v) else none) with
    | some d' => some d'
    | none => if allH d.P (d.expS t v) then some (schedHist d.M v t).length else none) = _
  by_cases h1 : d.D v < t
  · rw [if_pos h1, if_pos h1.le]
  · rw [if_neg h1]
    simp only
    rw [length_schedHist]
    by_cases h2 : d.D v = t
    · rw [if_pos ((h.allH_expS t v).2 h2.le), if_pos h2.le, h2]
    · rw [if_neg (fun h' => by have := (h.allH_expS t v).1 h'; omega), if_neg (by omega)]

lemma cpE_final {v : V} {t : ℕ} (hD : d.D v ≤ t) : d.cpE t v = d.cpF v := by
  classical
  funext s
  unfold PD.cpF PD.cpE
  split_ifs with hs
  · obtain ⟨hC, -⟩ := clOf_spec h.cl hs
    have hv := mem_nodes_clOf h.cl hs
    have hT : d.T (clOf d.cl v s) ≤ d.D v := le_sup (f := d.T) (mem_filter.2 ⟨hC, hv⟩)
    rw [min_eq_right (by omega), min_eq_right (le_sup (f := d.T) hC)]
  · rfl


lemma valF_expS {v : V} {t : ℕ} (hD : d.D v ≤ t) :
    d.valF ((baseInst d.N).ctx v) (inpAt (baseInst d.N) d.x' v) (d.cpE t v) = d.val v := by
  rw [h.cpE_final hD]; rfl

lemma runSl_expS (t : ℕ) (u v : V) :
    runSl d.P (d.expS t u) v ↔ ∃ C ∈ d.cl, s(u, v) ∈ C ∧ t < d.T C := by
  unfold runSl
  rw [h.mSl_expS]
  simp only [expS_c, base_me, expS_cp]
  constructor
  · rintro ⟨s, hs, he, hout⟩
    obtain ⟨hC, hsl⟩ := clOf_spec h.cl hs
    have hv := mem_nodes_clOf h.cl hs
    refine ⟨clOf d.cl u s, hC, (mem_clOf h.cl hs he).1, ?_⟩
    have h2 := h.out_cpE hC hv t
    rw [hsl] at h2
    exact h2.1 hout
  · rintro ⟨C, hC, he, ht⟩
    have hu : u ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_left u v⟩
    exact ⟨_, slice_mem_clLoc hC hu, mem_filter.2 ⟨he, Sym2.mem_mk_left u v⟩,
      (h.out_cpE hC hu t).2 ht⟩

lemma runSl_choose {t : ℕ} {u v : V} (hr : runSl d.P (d.expS t u) v) {C : Finset (Sym2 V)}
    (hC : C ∈ d.cl) (he : s(u, v) ∈ C) : Exists.choose hr = C.filter (fun e => u ∈ e) := by
  have hspec := Exists.choose_spec hr
  generalize Exists.choose hr = s at hspec ⊢
  obtain ⟨hs, he', -⟩ := hspec
  have hs' : s ∈ clLoc d.cl u := by rw [← h.mSl_expS t u]; exact hs
  exact slice_eq_of_mem h.cl hs' hC (by simpa using he') he

lemma out_expS (t : ℕ) (v : V) : d.run.out (d.expS t v) = if d.H ≤ t then
    some (d.finF ((baseInst d.N).ctx v) (inpAt (baseInst d.N) d.x' v) (d.cpE t v)
      (gVal (Fintype.card V + 4) d.Dg
        (d.valF ((baseInst d.N).ctx v) (inpAt (baseInst d.N) d.x' v) (d.cpE t v))
        (d.par v) (univ.filter (fun c => d.par c = some v)) (schedHist d.M v t))) else none := by
  classical
  have hT := h.tHalt_sched v t
  rw [mainP_out]
  simp only [expS_c, expS_inp, expS_cp, expS_th, base_me, h.de, h.pa, h.ki, h.effDt_expS]
  by_cases hH : d.H ≤ t
  · rw [if_pos (hT.2 hH), if_pos hH]
  · rw [if_neg (fun h' => hH (hT.1 h')), if_neg hH]

lemma out_expS_none {t : ℕ} (ht : t < d.H) (v : V) : d.run.out (d.expS t v) = none := by
  rw [h.out_expS, if_neg (by omega)]

/-! ### Messages of the composite run -/

/-- Over an edge of `C` whose copies run, the composite sends what the standalone run sends. -/
lemma msg_copy {C : Finset (Sym2 V)} (hC : C ∈ d.cl) {u v : V} (he : s(u, v) ∈ C) {t : ℕ}
    (ht : t < d.T C) (htH : t < d.H) :
    msg d.run (baseInst d.N) (d.expS t) u v = msg d.P (clInst0 d.N C) (d.stC C t) u v := by
  have hu : u ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_left u v⟩
  have hG : d.N.G.Adj u v := by
    have := h.cl.sub C hC he
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
  have hadjC : (clInst0 d.N C).G.Adj u v := by
    show (clGraph C ⊓ d.N.G).Adj u v
    rw [SimpleGraph.inf_adj]
    exact ⟨⟨hG.ne, he⟩, hG⟩
  have houtC : d.P.out (d.stC C t u) = none := (h.halts C hC).2 t ht u hu
  rw [msg_eq_send (I := baseInst d.N) hG (h.out_expS_none htH u), msg_eq_send hadjC houtC]
  congr 1
  have hr : runSl d.P (d.expS t u) v := (h.runSl_expS t u v).2 ⟨C, hC, he, ht⟩
  rw [mainP_send, dif_pos hr, h.runSl_choose hr hC he, expS_c, cctx_base h.cl hC, expS_cp,
    h.cpE_slice hC hu, min_eq_left ht.le]

/-- Over an edge whose copies have halted, the composite sends the tree words of the schedule. -/
lemma msg_tree {u v : V} {t : ℕ} (hall : ∀ C ∈ d.cl, s(u, v) ∈ C → d.T C ≤ t) (htH : t < d.H) :
    msg d.run (baseInst d.N) (d.expS t) u v = d.M u v t := by
  by_cases hG : d.N.G.Adj u v
  · rw [msg_eq_send (I := baseInst d.N) hG (h.out_expS_none htH u)]
    have hr : ¬ runSl d.P (d.expS t u) v := fun hr => by
      obtain ⟨C, hC, he, ht⟩ := (h.runSl_expS t u v).1 hr
      have := hall C hC he; omega
    rw [mainP_send, dif_neg hr]
    simp only [expS_c, expS_inp, expS_cp, expS_th, base_me, h.pa, h.ki, h.effDt_expS]
    rw [h.tSend_sched u v t _ (fun hD => h.valF_expS hD)]
    cases hM : d.M u v t with
    | none => rfl
    | some w => simp [h.M_ok hM]
  · rw [msg_eq_none (I := baseInst d.N) hG]
    cases hM : d.M u v t with
    | none => rfl
    | some w => exact absurd (h.M_adj (by rw [hM]; rfl)) hG

omit h in
lemma schedHist_succ (M : V → V → ℕ → Option (Word V)) (v : V) (t : ℕ) :
    schedHist M v (t + 1) = schedHist M v t ++ [fun w => M w v t] := by
  unfold schedHist
  rw [List.range_succ, List.map_append]
  rfl

/-- **The composite run follows the expected states** (copies = standalone runs, tree history =
schedule). -/
theorem st_eq : ∀ t ≤ d.H, d.stM t = d.expS t := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    funext v
    show d.run.init ((baseInst d.N).ctx v) (inpAt (baseInst d.N) d.x' v) (d.ω v) = d.expS 0 v
    rw [mainP_init]
    refine MainS.ext' _ _ rfl rfl ?_ ?_ rfl
    · dsimp only
      rw [expS_cp]
      funext s
      unfold PD.cpE
      split_ifs with hs
      · obtain ⟨C, hC, rfl, hne⟩ := mem_clLoc.1 hs
        have hv : v ∈ nodes C := by
          obtain ⟨e, he⟩ := hne
          exact mem_nodes.2 ⟨e, (mem_filter.1 he).1, (mem_filter.1 he).2⟩
        rw [clOf_slice h.cl hC hv, Nat.zero_min]
        show _ = d.P.init ((clInst0 d.N C).ctx v) (inpAt (clInst0 d.N C) x0 v) (seedC d.ω C v)
        rw [cctx_base h.cl hC, cinp_base hv]
        rfl
      · rfl
    · show none = if d.D v < 0 then some (d.D v) else none
      rw [if_neg (Nat.not_lt_zero _)]
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    funext v
    unfold PD.stM at ih' ⊢
    rw [st_succ, ih']
    unfold step
    rw [h.out_expS_none (by omega)]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    refine MainS.ext' _ _ rfl rfl ?_ ?_ ?_
    · -- the copies
      dsimp only
      simp only [expS_cp, expS_c, expS_inp, base_me, h.sl]
      funext s
      by_cases hs : s ∈ clLoc d.cl v
      · obtain ⟨C, hC, rfl, hne⟩ := mem_clLoc.1 hs
        have hv : v ∈ nodes C := by
          obtain ⟨e, he⟩ := hne
          exact mem_nodes.2 ⟨e, (mem_filter.1 he).1, (mem_filter.1 he).2⟩
        by_cases ht' : t < d.T C
        · rw [if_pos ⟨hs, (h.out_cpE hC hv t).2 ht'⟩, h.cpE_slice hC hv, h.cpE_slice hC hv,
            min_eq_left ht'.le, min_eq_left (show t + 1 ≤ d.T C by omega), cctx_base h.cl hC]
          show _ = st d.P (clInst0 d.N C) x0 (seedC d.ω C) (t + 1) v
          rw [st_succ]
          unfold step
          have hn : d.P.out (d.stC C t v) = none := (h.halts C hC).2 t ht' v hv
          unfold PD.stC at hn
          rw [hn]
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          congr 1
          funext u
          show (if s(v, u) ∈ C.filter (fun e => v ∈ e) then msg d.run (baseInst d.N) (d.expS t) u v
            else none) = msg d.P (clInst0 d.N C) (st d.P (clInst0 d.N C) x0 (seedC d.ω C) t) u v
          by_cases hu : s(v, u) ∈ C.filter (fun e => v ∈ e)
          · rw [if_pos hu]
            have he : s(u, v) ∈ C := by rw [Sym2.eq_swap]; exact (mem_filter.1 hu).1
            exact h.msg_copy hC he ht' (by omega)
          · rw [if_neg hu]
            refine (msg_eq_none ?_).symm
            intro hadj
            have hadj' : (clGraph C ⊓ d.N.G).Adj u v := hadj
            rw [SimpleGraph.inf_adj] at hadj'
            apply hu
            rw [mem_filter, Sym2.eq_swap]
            exact ⟨hadj'.1.2, Sym2.mem_mk_right u v⟩
        · have hT : d.T C ≤ t := by omega
          rw [if_neg (show ¬ (C.filter (fun e => v ∈ e) ∈ clLoc d.cl v ∧
              d.P.out (d.cpE t v (C.filter (fun e => v ∈ e))) = none) from
              fun h' => ht' ((h.out_cpE hC hv t).1 h'.2)), h.cpE_slice hC hv,
            h.cpE_slice hC hv, min_eq_right hT, min_eq_right (show d.T C ≤ t + 1 by omega)]
      · rw [if_neg (show ¬ (s ∈ clLoc d.cl v ∧ d.P.out (d.cpE t v s) = none) from
          fun h' => hs h'.1)]
        unfold PD.cpE
        rw [if_neg hs, if_neg hs]
    · -- the done round
      show effDt d.P (d.expS t v) = if d.D v < t + 1 then some (d.D v) else none
      rw [PD.Ok.effDt_expS h t v]
      unfold PD.edAt
      by_cases hD : d.D v ≤ t
      · rw [if_pos hD, if_pos (by omega)]
      · rw [if_neg hD, if_neg (by omega)]
    · -- the tree history
      dsimp only
      simp only [expS_th]
      rw [schedHist_succ]
      show schedHist d.M v t ++ _ = schedHist d.M v t ++ _
      congr 2
      funext u
      by_cases hr : runSl d.P (d.expS t v) u
      · rw [if_pos hr]
        obtain ⟨C, hC, he, ht'⟩ := (h.runSl_expS t v u).1 hr
        cases hM : d.M u v t with
        | none => rfl
        | some w =>
          have := PD.Ok.M_ge_T h (u := u) (v := v) (t := t) (by simp [hM]) hC
            (by rw [Sym2.eq_swap]; exact he)
          omega
      · rw [if_neg hr]
        refine h.msg_tree (fun C hC he => ?_) (by omega)
        by_contra hlt
        exact hr ((h.runSl_expS t v u).2 ⟨C, hC, by rw [Sym2.eq_swap]; exact he, by omega⟩)

lemma stM_lt {t : ℕ} (ht : t ≤ d.H) :
    st d.run (baseInst d.N) d.x' d.ω t = d.expS t := h.st_eq t ht

/-! ### Success of the composite run -/

theorem haltsAt : HaltsAt d.run (baseInst d.N) d.x' d.ω d.H := by
  refine ⟨fun v _ => ?_, fun s hs v _ => ?_⟩
  · rw [h.stM_lt le_rfl, h.out_expS, if_pos le_rfl]; rfl
  · rw [h.stM_lt hs.le, h.out_expS_none hs]

theorem properUpTo : ProperUpTo d.run (baseInst d.N) d.x' d.ω d.H := by
  classical
  intro s hs u _ _ v hv
  rw [h.stM_lt hs.le] at hv
  rw [mainP_send] at hv
  split_ifs at hv with hr
  · obtain ⟨C, hC, he, -⟩ := (h.runSl_expS s u v).1 hr
    have := h.cl.sub C hC he
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
  · simp only [expS_c, expS_inp, expS_cp, expS_th, base_me, h.pa, h.ki, h.effDt_expS] at hv
    rw [h.tSend_sched u v s _ (fun hD => h.valF_expS hD)] at hv
    exact h.M_adj hv

lemma sentSet_sub {t : ℕ} (ht : t < d.H) :
    sentSet d.run (baseInst d.N) (d.expS t) ⊆
      (d.cl.filter (fun C => t < d.T C)).biUnion
        (fun C => sentSet d.P (clInst0 d.N C) (d.stC C t)) ∪
      univ.filter (fun uv : V × V => (d.M uv.1 uv.2 t).isSome) := by
  classical
  intro uv huv
  simp only [sentSet, mem_filter, mem_univ, true_and] at huv
  by_cases hc : ∃ C ∈ d.cl, s(uv.1, uv.2) ∈ C ∧ t < d.T C
  · obtain ⟨C, hC, he, htC⟩ := hc
    refine mem_union_left _ (mem_biUnion.2 ⟨C, mem_filter.2 ⟨hC, htC⟩, ?_⟩)
    simp only [sentSet, mem_filter, mem_univ, true_and]
    rw [← h.msg_copy hC he htC ht]; exact huv
  · refine mem_union_right _ ?_
    simp only [mem_filter, mem_univ, true_and]
    rw [← h.msg_tree (fun C hC he => by by_contra hlt; exact hc ⟨C, hC, he, by omega⟩) ht]
    exact huv

lemma M_count (uv : V × V) :
    ((range d.H).filter (fun t => (d.M uv.1 uv.2 t).isSome)).card ≤
      if (uv.1 ∈ (univ : Finset V) ∧ d.par uv.1 = some uv.2) ∨
        (uv.2 ∈ (univ : Finset V) ∧ d.par uv.2 = some uv.1) then 2 * d.Dg else 0 := by
  classical
  obtain ⟨u, v⟩ := uv
  simp only [mem_univ, true_and]
  by_cases h1 : d.par u = some v
  · rw [if_pos (Or.inl h1)]
    calc _ ≤ (Ico (d.R u) (d.R u + 2 * d.Dg)).card := by
          apply card_le_card
          intro t ht
          simp only [mem_filter, mem_range] at ht
          rw [h.M_up h1] at ht
          rw [mem_Ico]
          split_ifs at ht with h2
          · exact h2
          · simp at ht
      _ = 2 * d.Dg := by simp
  · by_cases h2 : d.par v = some u
    · rw [if_pos (Or.inr h2)]
      calc _ ≤ (Ico (bB d.Dg d.ρ d.dep d.R u) (bB d.Dg d.ρ d.dep d.R u + 2 * d.Dg)).card := by
            apply card_le_card
            intro t ht
            simp only [mem_filter, mem_range] at ht
            rw [h.M_down h2] at ht
            rw [mem_Ico]
            split_ifs at ht with h3
            · exact h3
            · simp at ht
        _ = 2 * d.Dg := by simp
    · rw [if_neg (by tauto)]
      simp [h.M_none h1 h2]

theorem msgs_le : msgsUpTo d.run (baseInst d.N) d.x' d.ω d.H ≤
    ∑ C ∈ d.cl, msgsUpTo d.P (clInst0 d.N C) x0 (seedC d.ω C) (d.T C) +
      2 * (2 * d.Dg) * Fintype.card V := by
  classical
  unfold msgsUpTo
  have step1 : ∀ t ∈ range d.H, (sentSet d.run (baseInst d.N) (st d.run (baseInst d.N) d.x' d.ω t)).card ≤
      ∑ C ∈ d.cl, (if t < d.T C then (sentSet d.P (clInst0 d.N C) (d.stC C t)).card else 0) +
        (univ.filter (fun uv : V × V => (d.M uv.1 uv.2 t).isSome)).card := by
    intro t ht
    have ht' := mem_range.1 ht
    rw [h.stM_lt ht'.le]
    refine (card_le_card (h.sentSet_sub ht')).trans ((card_union_le _ _).trans ?_)
    refine Nat.add_le_add_right (card_biUnion_le.trans (le_of_eq ?_)) _
    rw [sum_filter]
  refine (sum_le_sum step1).trans ?_
  rw [sum_add_distrib, sum_comm]
  refine Nat.add_le_add (sum_le_sum (fun C _ => ?_)) ?_
  · rw [← sum_filter]
    refine sum_le_sum_of_subset (fun t ht => ?_)
    simp only [mem_filter, mem_range] at ht ⊢
    exact ht.2
  · rw [sum_card_filter_swap]
    refine (sum_le_mul_card _ _ (2 * d.Dg) h.M_count).trans ?_
    have := card_treePairs (univ : Finset V) d.par
    rw [card_univ] at this
    nlinarith

theorem loads_le (e : Sym2 V) : loadUpTo d.run (baseInst d.N) d.x' d.ω d.H e ≤
    ∑ C ∈ d.cl, loadUpTo d.P (clInst0 d.N C) x0 (seedC d.ω C) (d.T C) e + 2 * (2 * d.Dg) := by
  classical
  unfold loadUpTo
  have step1 : ∀ t ∈ range d.H,
      ((sentSet d.run (baseInst d.N) (st d.run (baseInst d.N) d.x' d.ω t)).filter
        (fun uv => s(uv.1, uv.2) = e)).card ≤
      ∑ C ∈ d.cl, (if t < d.T C then ((sentSet d.P (clInst0 d.N C) (d.stC C t)).filter
          (fun uv => s(uv.1, uv.2) = e)).card else 0) +
        (univ.filter (fun uv : V × V => (d.M uv.1 uv.2 t).isSome ∧ s(uv.1, uv.2) = e)).card := by
    intro t ht
    have ht' := mem_range.1 ht
    rw [h.stM_lt ht'.le]
    refine (card_le_card (filter_subset_filter _ (h.sentSet_sub ht'))).trans ?_
    rw [filter_union, filter_biUnion]
    refine (card_union_le _ _).trans (Nat.add_le_add ?_ (le_of_eq ?_))
    · refine card_biUnion_le.trans (le_of_eq ?_)
      rw [sum_filter]
    · congr 1; ext uv; simp
  refine (sum_le_sum step1).trans ?_
  rw [sum_add_distrib, sum_comm]
  refine Nat.add_le_add (sum_le_sum (fun C _ => ?_)) ?_
  · rw [← sum_filter]
    refine sum_le_sum_of_subset (fun t ht => ?_)
    simp only [mem_filter, mem_range] at ht ⊢
    exact ht.2
  · rw [sum_card_filter_swap]
    have hb : ∀ uv : V × V, ((range d.H).filter
        (fun t => (d.M uv.1 uv.2 t).isSome ∧ s(uv.1, uv.2) = e)).card ≤
        if s(uv.1, uv.2) = e then 2 * d.Dg else 0 := by
      intro uv
      split_ifs with he
      · refine (card_le_card (fun t ht => ?_)).trans ((h.M_count uv).trans ?_)
        · simp only [mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1⟩
        · split_ifs <;> omega
      · simp [he]
    refine (sum_le_mul_card _ _ (2 * d.Dg) hb).trans ?_
    have := card_sym2_fiber e
    nlinarith

theorem outAt_eq (v : V) : outAt d.run (baseInst d.N) d.x' d.ω d.H (.inl v) =
    d.finF ((baseInst d.N).ctx v) (inpAt (baseInst d.N) d.x' v) (d.cpF v)
      (univ.sup (fun w => (d.val w).1), univ.sup (fun w => (d.val w).2)) (.inl v) := by
  have hD : d.D v ≤ d.H := by
    have := h.D_le_R v; have := h.R_le_root v; unfold PD.H; omega
  show (match (baseInst d.N).host (.inl v) with
    | some w => (d.run.out (st d.run (baseInst d.N) d.x' d.ω d.H w)).bind (fun m => m (.inl v))
    | none => none) = _
  show (d.run.out (st d.run (baseInst d.N) d.x' d.ω d.H v)).bind (fun m => m (.inl v)) = _
  rw [h.stM_lt le_rfl, h.out_expS, if_pos le_rfl, Option.bind_some,
    h.gVal_sched v le_rfl _ (fun hD' => h.valF_expS hD'), h.Ag_root, h.cpE_final hD]

/-- **The generic parallel composition** (summary). -/
theorem par_run : HaltsAt d.run (baseInst d.N) d.x' d.ω d.H ∧
    ProperUpTo d.run (baseInst d.N) d.x' d.ω d.H ∧
    d.H ≤ d.cl.sup d.T + 2 * (2 * d.Dg) * Fintype.card V ∧
    msgsUpTo d.run (baseInst d.N) d.x' d.ω d.H ≤
      ∑ C ∈ d.cl, msgsUpTo d.P (clInst0 d.N C) x0 (seedC d.ω C) (d.T C) +
        2 * (2 * d.Dg) * Fintype.card V ∧
    (∀ e, loadUpTo d.run (baseInst d.N) d.x' d.ω d.H e ≤
      ∑ C ∈ d.cl, loadUpTo d.P (clInst0 d.N C) x0 (seedC d.ω C) (d.T C) e + 2 * (2 * d.Dg)) ∧
    ∀ v, outAt d.run (baseInst d.N) d.x' d.ω d.H (.inl v) =
      d.finF ((baseInst d.N).ctx v) (inpAt (baseInst d.N) d.x' v) (d.cpF v)
        (univ.sup (fun w => (d.val w).1), univ.sup (fun w => (d.val w).2)) (.inl v) :=
  ⟨h.haltsAt, h.properUpTo, h.H_bound, h.msgs_le, h.loads_le, h.outAt_eq⟩

end PD.Ok

end EmbC

end APSP.Stoc.Congest
