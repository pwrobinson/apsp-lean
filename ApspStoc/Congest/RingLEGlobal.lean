import ApspStoc.Congest.RingLEBase

/-!
# Ring orientation in CONGEST: the global schedule (`ringLE_congest`, part 2)

For a fixed instance (`RS`: network, overlays, overlay index, size bound, participants, the node
set `S` and the ring data `r`) this file defines the *global* execution of the protocol, following
the mathematical election of `RingComb.lean`:

* the probes in flight at link step `k` of phase `i` are `flightA r i k` (origin ends); the probe
  with origin `a` crosses the link of its departure end `x = depEnd r a k`, whose entry is
  `(e, w, e') = (r x.1)[x.2]` in the cluster `C ∋ e`: up the path of `x.1` in `C` to the host of
  `C`'s aggregator (hops `0 … D-1`), then down the path of `w` in `C` (hops `D … 2D-1`), arriving at
  the partner end `segPartner r x` (`RS.pk`, `RS.pos`, `RS.moves`);
* `RS.held i k h u`: the packets at node `u` at the start of hop `h`;
* `RS.M u w s`: the message from `u` to `w` in round `s` (the node sends, in slot `σ` of a hop,
  the word `t` of its held packet of rank `σ` if that packet moves to `w`).

The main lemmas: `RS.linkF` (the facts about a link), `RS.step_pk` (a node holding a packet moves
it as the schedule says, using only its context), `RS.adj_pk` (the host turns it to the partner's
path), `RS.held_succ` (the held packets evolve by the local rules), `RS.M_adj`/`RS.M_ok` (the
schedule only uses edges of the instance and valid words).
-/

namespace APSP.Stoc.Congest
namespace RingLE

open APSP Finset APSP.Stoc.RingComb

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The setting of the ring orientation task. -/
structure RS (V : Type) [Fintype V] [DecidableEq V] where
  /-- the network -/
  N : WNet V
  /-- the overlays and their embedding -/
  E : Overlays V
  /-- the overlay index -/
  j : ℕ
  /-- the public size bound -/
  sz : ℕ
  /-- the participants -/
  Pt : Finset V
  /-- the nodes with segment ends -/
  S : Finset V
  /-- the ring data -/
  r : V → RingIn V

/-- The hypotheses of the contract. -/
structure RS.OK (Z : RS V) : Prop where
  emb : EmbValid Z.N.G Z.E
  hj : Z.j < Fintype.card V
  wf : RingWF Z.E.cl Z.S Z.r
  hsz : Z.S.card ≤ Z.sz
  fp : footprint Z.E Z.j Z.S ⊆ Z.Pt

namespace RS

variable (Z : RS V)

/-- the instance -/
noncomputable def I : Inst V := ioInst Z.N Z.E Z.j Z.sz Z.Pt

/-- half the hops of a link step -/
noncomputable def D : ℕ := Z.E.dil + 1

/-- the bound on the number of elements -/
noncomputable def B : ℕ := Z.E.ov * min Z.sz (Fintype.card V)

lemma ctx_eq (u : V) : Z.I.ctx u =
    ⟨u, ioView Z.N Z.E Z.j Z.Pt u, [Z.j, Z.sz, Z.E.dil, Z.E.ov], ioEmb Z.E u, clLoc Z.E.cl u⟩ := rfl

@[simp] lemma rJ_ctx (u : V) : rJ (Z.I.ctx u) = Z.j := rfl
@[simp] lemma hD_ctx (u : V) : hD (Z.I.ctx u) = Z.D := rfl
@[simp] lemma bnd_ctx (u : V) : bnd (Z.I.ctx u) = Z.B := rfl
@[simp] lemma me_ctx (u : V) : (Z.I.ctx u).me = u := rfl

/-- the entry of the end `x` -/
def ent (x : V × ℕ) : Sym2 V × V × Sym2 V := (Z.r x.1).getD x.2 (s(x.1, x.1), x.1, s(x.1, x.1))

/-- the cluster of the link of `x` -/
noncomputable def cl (x : V × ℕ) : Finset (Sym2 V) := Cof Z.E.cl (Z.ent x).1

/-- the path up: from the departure node to the host -/
noncomputable def pUp (x : V × ℕ) : List (Sym2 V) := Z.E.path Z.j x.1 (Z.cl x)

/-- the path down: from the partner node to the host (travelled in reverse) -/
noncomputable def pDn (x : V × ℕ) : List (Sym2 V) := Z.E.path Z.j (Z.ent x).2.1 (Z.cl x)

/-- the packet of the probe with origin `a` crossing the link of `x`, at hop `h` -/
noncomputable def pk (a x : V × ℕ) (h : ℕ) : Pk V :=
  ⟨a.1, a.2, x.1, (Z.ent x).1, (Z.ent x).2.2, (Z.ent x).2.1,
    if h < Z.D then (srcPort (Z.cl x) x.1).2 else (srcPort (Z.cl x) (Z.ent x).2.1).2⟩

/-- the position of a packet crossing the link of `x` at the start of hop `h` -/
noncomputable def pos (x : V × ℕ) (h : ℕ) : V :=
  if h ≤ Z.D then wnode (Z.pUp x) x.1 h else wnode (Z.pDn x) (Z.ent x).2.1 (2 * Z.D - h)

/-- the packet crossing the link of `x` moves at hop `h` -/
noncomputable def moves (x : V × ℕ) (h : ℕ) : Prop :=
  if h < Z.D then h < (Z.pUp x).length else 2 * Z.D - 1 - h < (Z.pDn x).length

/-- moving is decidable -/
noncomputable instance (x : V × ℕ) (h : ℕ) : Decidable (Z.moves x h) := by
  unfold moves; infer_instance

open Classical in
/-- the packets held by `u` at the start of hop `h` of link step `k` of phase `i` -/
noncomputable def held (i k h : ℕ) (u : V) : Finset (Pk V) :=
  ((flightA Z.r i k).filter (fun a => Z.pos (depEnd Z.r a k) h = u)).image
    (fun a => Z.pk a (depEnd Z.r a k) h)

open Classical in
/-- the packets moving to `u` at hop `h` -/
noncomputable def recv (i k h : ℕ) (u : V) : Finset (Pk V) :=
  ((flightA Z.r i k).filter (fun a => Z.moves (depEnd Z.r a k) h ∧
    Z.pos (depEnd Z.r a k) (h + 1) = u)).image (fun a => Z.pk a (depEnd Z.r a k) h)

/-- **The global schedule**: the message from `u` to `w` in round `s`. -/
noncomputable def M (u w : V) (s : ℕ) : Option (Word V) :=
  match tq Z.D Z.B s with
  | some q => sendFrom (Z.I.ctx u) q.h q.σ q.t (Z.held q.i q.k q.h u) w
  | none => none

/-! ## Facts about a link -/

/-- The facts about the link of an end `x`, with the host `hN` of its cluster. -/
structure LinkF (x : V × ℕ) (hN : V) : Prop where
  ent : (Z.r x.1)[x.2]? = some (Z.ent x)
  clC : Z.cl x ∈ Z.E.cl
  eC : (Z.ent x).1 ∈ Z.cl x
  e'C : (Z.ent x).2.2 ∈ Z.cl x
  vS : x.1 ∈ Z.S
  wS : (Z.ent x).2.1 ∈ Z.S
  vC : x.1 ∈ nodes (Z.cl x)
  wC : (Z.ent x).2.1 ∈ nodes (Z.cl x)
  ve : x.1 ∈ (Z.ent x).1
  wUp : IsEdgeWalk (Z.pUp x) x.1 hN
  wDn : IsEdgeWalk (Z.pDn x) (Z.ent x).2.1 hN
  lUp : (Z.pUp x).length ≤ Z.E.dil
  lDn : (Z.pDn x).length ≤ Z.E.dil
  part : segPartner Z.r x =
    ((Z.ent x).2.1, (Z.r (Z.ent x).2.1).idxOf ((Z.ent x).2.2, x.1, (Z.ent x).1))
  hostAll : ∀ u ∈ nodes (Z.cl x), IsEdgeWalk (Z.E.path Z.j u (Z.cl x)) u hN

variable {Z}

/-- the cluster of an edge of a cluster of the family -/
lemma cof_eq (hZ : Z.OK) {C : Finset (Sym2 V)} (hC : C ∈ Z.E.cl) {e : Sym2 V} (he : e ∈ C) :
    Cof Z.E.cl e = C := by
  classical
  have hex : ∃ C ∈ Z.E.cl, e ∈ C := ⟨C, hC, he⟩
  unfold Cof
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  by_contra hne
  exact disjoint_left.1 (hZ.emb.disj _ h1 C hC hne) h2 he

lemma ent_eq {x : V × ℕ} (hx : x ∈ ringDarts Z.r) : (Z.r x.1)[x.2]? = some (Z.ent x) := by
  rw [mem_ringDarts] at hx
  unfold ent
  rw [List.getD_eq_getElem _ _ hx, List.getElem?_eq_getElem hx]

lemma ent_mem {x : V × ℕ} (hx : x ∈ ringDarts Z.r) : Z.ent x ∈ Z.r x.1 :=
  List.mem_of_getElem? (ent_eq hx)

/-- **The link of an end** -/
lemma linkF (hZ : Z.OK) {x : V × ℕ} (hx : x ∈ ringDarts Z.r) : ∃ hN, Z.LinkF x hN := by
  have hent := ent_eq hx
  have hmem : ((Z.ent x).1, (Z.ent x).2.1, (Z.ent x).2.2) ∈ Z.r x.1 := ent_mem hx
  obtain ⟨C, hC, heC, he'C, hvC, hwC⟩ := hZ.wf.clus _ _ _ _ hmem
  have hcl : Z.cl x = C := cof_eq hZ hC heC
  obtain ⟨hN, -, hwalk⟩ := hZ.emb.walk Z.j hZ.hj C hC
  have hsym := hZ.wf.symm _ _ _ _ hmem
  have hvS : x.1 ∈ Z.S := by
    by_contra h
    rw [hZ.wf.out _ h] at hmem
    simp at hmem
  have hwS : (Z.ent x).2.1 ∈ Z.S := by
    by_contra h
    rw [hZ.wf.out _ h] at hsym
    simp at hsym
  refine ⟨hN, ⟨hent, hcl ▸ hC, hcl ▸ heC, hcl ▸ he'C, hvS, hwS, hcl ▸ hvC, hcl ▸ hwC,
    hZ.wf.inc _ _ _ _ hmem, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold pUp; rw [hcl]; exact hwalk _ hvC
  · unfold pDn; rw [hcl]; exact hwalk _ hwC
  · unfold pUp; rw [hcl]; exact Z.E.path_le_dil hZ.hj _ hC
  · unfold pDn; rw [hcl]; exact Z.E.path_le_dil hZ.hj _ hC
  · exact segPartner_of hent
  · rw [hcl]; exact hwalk

/-! ## Positions -/

lemma pos_zero (x : V × ℕ) : Z.pos x 0 = x.1 := by
  unfold pos; simp

lemma pos_dn {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) {h : ℕ} (h1 : Z.D ≤ h) (h2 : h ≤ 2 * Z.D) :
    Z.pos x h = wnode (Z.pDn x) (Z.ent x).2.1 (2 * Z.D - h) := by
  unfold pos
  split_ifs with hh
  · have hD : h = Z.D := le_antisymm hh h1
    subst hD
    rw [wnode_ge hL.wUp (by unfold D at *; have := hL.lUp; omega),
      wnode_ge hL.wDn (by unfold D at *; have := hL.lDn; omega)]
  · rfl

lemma pos_end {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) : Z.pos x (2 * Z.D) = (Z.ent x).2.1 := by
  rw [pos_dn hL (h := 2 * Z.D) (by omega) le_rfl]; simp

lemma pos_D {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) : Z.pos x Z.D = hN := by
  unfold pos
  rw [ite_eq_left le_rfl]
  exact wnode_ge hL.wUp (by unfold D; have := hL.lUp; omega)

/-- positions lie on the walks of the link -/
lemma pos_onWalk {x : V × ℕ} (h : ℕ) :
    OnWalk (Z.pUp x) x.1 (Z.pos x h) ∨ OnWalk (Z.pDn x) (Z.ent x).2.1 (Z.pos x h) := by
  unfold pos
  split_ifs
  · exact Or.inl (wnode_onWalk _ _ _)
  · exact Or.inr (wnode_onWalk _ _ _)

lemma pos_not_moves {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) {h : ℕ} (hh : h < 2 * Z.D)
    (hm : ¬ Z.moves x h) : Z.pos x (h + 1) = Z.pos x h := by
  unfold moves at hm
  split_ifs at hm with h1
  · -- up: the packet has arrived at the host
    push Not at hm
    unfold pos
    rw [ite_eq_left (show h + 1 ≤ Z.D by omega), ite_eq_left (show h ≤ Z.D by omega),
      wnode_ge hL.wUp (by omega), wnode_ge hL.wUp hm]
  · push Not at hm
    rw [pos_dn hL (h := h + 1) (by omega) (by omega), pos_dn hL (h := h) (by omega) (by omega),
      wnode_ge hL.wDn (by omega), wnode_ge hL.wDn (by omega)]

/-! ## The local rules follow the schedule -/

/-- The key edge chosen locally by the departure node is the key edge of the link's cluster. -/
lemma keyL_eq (hZ : Z.OK) {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) :
    keyL (Z.I.ctx x.1) (Z.ent x).1 = (srcPort (Z.cl x) x.1).2 := by
  classical
  have hdisj := hZ.emb.disj
  have hks := srcPort_snd_mem hL.vC
  have hex : ∃ k, ((Z.I.ctx x.1).emb (rJ (Z.I.ctx x.1)) (Z.I.ctx x.1).me k).isSome ∧
      ∃ s ∈ (Z.I.ctx x.1).sl, (Z.ent x).1 ∈ s ∧ k ∈ s := by
    refine ⟨(srcPort (Z.cl x) x.1).2, ?_, (Z.cl x).filter (fun e => x.1 ∈ e), ?_, ?_, ?_⟩
    · show (ioEmb Z.E x.1 Z.j x.1 (srcPort (Z.cl x) x.1).2).isSome
      rw [ioEmb_eq_some hdisj hL.clC hL.vC (Or.inl rfl)]; rfl
    · show _ ∈ clLoc Z.E.cl x.1
      unfold clLoc
      simp only [mem_filter, mem_image]
      exact ⟨⟨Z.cl x, hL.clC, rfl⟩, ⟨(Z.ent x).1, mem_filter.2 ⟨hL.eC, hL.ve⟩⟩⟩
    · exact mem_filter.2 ⟨hL.eC, hL.ve⟩
    · exact mem_filter.2 hks
  unfold keyL
  rw [dite_eq_left hex]
  obtain ⟨h1, s, hs, hes, hks'⟩ := hex.choose_spec
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨C', hC', hvC', hk', -, -⟩ :=
    ioEmb_spec (show ioEmb Z.E x.1 Z.j x.1 hex.choose = some l from hl)
  have hs' : s ∈ clLoc Z.E.cl x.1 := hs
  unfold clLoc at hs'
  simp only [mem_filter, mem_image] at hs'
  obtain ⟨⟨C'', hC'', rfl⟩, -⟩ := hs'
  have e1 : C'' = Z.cl x := by
    by_contra hne
    exact disjoint_left.1 (hdisj _ hC'' _ hL.clC hne) (mem_filter.1 hes).1 hL.eC
  subst e1
  have e2 : C' = Z.cl x := by
    by_contra hne
    have hk1 := (srcPort_snd_mem hvC').1
    rw [hk'] at hk1
    exact disjoint_left.1 (hdisj _ hC' _ hL.clC hne) hk1 (mem_filter.1 hks').1
  subst e2
  exact hk'.symm

/-- The host of the link's cluster identifies the cluster from the link's edge. -/
lemma hostC_eq (hZ : Z.OK) {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) :
    hostC (Z.I.ctx hN) (Z.ent x).1 = Z.cl x := by
  classical
  have hvS := hL.vS
  -- the host of the cluster in the instance
  have hagg : aggHost Z.E Z.j (Z.cl x) = some hN := by
    have hex : Z.cl x ∈ Z.E.cl ∧ (nodes (Z.cl x)).Nonempty ∧ ∃ hv : V, ∀ v ∈ nodes (Z.cl x),
        IsEdgeWalk (Z.E.path Z.j v (Z.cl x)) v hv := ⟨hL.clC, ⟨x.1, hL.vC⟩, hN, hL.hostAll⟩
    unfold aggHost
    rw [dite_eq_left hex]
    congr 1
    exact isEdgeWalk_unique (Classical.choose_spec hex.2.2 x.1 hL.vC) (hL.hostAll x.1 hL.vC)
  have hNPt : hN ∈ Z.Pt := by
    apply hZ.fp
    rw [mem_footprint]
    have hw := hL.wUp
    cases hp : Z.pUp x with
    | nil =>
      rw [hp] at hw
      left; rw [← (show x.1 = hN from hw)]; exact hvS
    | cons e l =>
      right
      refine ⟨x.1, hvS, Z.cl x, mem_filter.2 ⟨hL.clC, hL.vC⟩, ?_⟩
      have hlen : (Z.pUp x).length - 1 < (Z.pUp x).length := by rw [hp]; simp
      refine ⟨(Z.pUp x)[(Z.pUp x).length - 1]'hlen, List.getElem_mem _, ?_⟩
      rw [wnode_get hw hlen, Nat.sub_add_cancel (by rw [hp]; simp), wnode_ge hw le_rfl]
      exact Sym2.mem_mk_right _ _
  have hhost : ioHost Z.E Z.j Z.Pt (.inr (Z.cl x)) = some hN := by
    simp only [ioHost, hagg, hNPt, ite_true]
  have hex : ∃ C' : Finset (Sym2 V), ((Z.I.ctx hN).view (.inr C')).isSome ∧
      (Z.ent x).1 ∈ C' := by
    refine ⟨Z.cl x, ?_, hL.eC⟩
    show (ioView Z.N Z.E Z.j Z.Pt hN (.inr (Z.cl x))).isSome
    unfold ioView
    rw [ite_eq_left hhost]; rfl
  unfold hostC
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h1' : (ioView Z.N Z.E Z.j Z.Pt hN (.inr hex.choose)).isSome := h1
  unfold ioView at h1'
  by_cases hh : ioHost Z.E Z.j Z.Pt (.inr hex.choose) = some hN
  · have hC' : hex.choose ∈ Z.E.cl := by
      cases hag : aggHost Z.E Z.j hex.choose with
      | none => simp [ioHost, hag] at hh
      | some h0 =>
        unfold aggHost at hag
        by_contra hc
        rw [dite_eq_right (fun h => hc h.1)] at hag
        cases hag
    by_contra hne
    exact disjoint_left.1 (hZ.emb.disj _ hC' _ hL.clC hne) h2 hL.eC
  · rw [ite_eq_right hh] at h1'; simp at h1'

/-- positions are participants -/
lemma pos_mem (hZ : Z.OK) {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) (h : ℕ) :
    Z.pos x h ∈ Z.Pt := by
  apply hZ.fp
  rw [mem_footprint]
  rcases pos_onWalk (Z := Z) (x := x) h with hw | hw
  · rcases hw with hw | ⟨e, he, hxe⟩
    · left; rw [hw]; exact hL.vS
    · right; exact ⟨x.1, hL.vS, Z.cl x, mem_filter.2 ⟨hL.clC, hL.vC⟩, e, he, hxe⟩
  · rcases hw with hw | ⟨e, he, hxe⟩
    · left; rw [hw]; exact hL.wS
    · right; exact ⟨_, hL.wS, Z.cl x, mem_filter.2 ⟨hL.clC, hL.wC⟩, e, he, hxe⟩

lemma moves_up {x : V × ℕ} {h : ℕ} (h1 : h < Z.D) : Z.moves x h ↔ h < (Z.pUp x).length := by
  unfold moves; rw [ite_eq_left h1]

lemma moves_dn {x : V × ℕ} {h : ℕ} (h1 : ¬ h < Z.D) :
    Z.moves x h ↔ 2 * Z.D - 1 - h < (Z.pDn x).length := by
  unfold moves; rw [ite_eq_right h1]

/-- **The relay rule**: a node holding the packet of a link moves it as the schedule says. -/
lemma step_pk (hZ : Z.OK) {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) (a : V × ℕ) {h : ℕ}
    (hh : h < 2 * Z.D) :
    stepL (Z.I.ctx (Z.pos x h)) h (Z.pk a x h) =
      if Z.moves x h then some (Z.pos x (h + 1)) else none := by
  have hdisj := hZ.emb.disj
  unfold stepL
  simp only [hD_ctx, rJ_ctx, me_ctx]
  by_cases h1 : h < Z.D
  · simp only [h1, ↓reduceIte]
    have hpk : (Z.pk a x h).key = (srcPort (Z.cl x) x.1).2 := by simp [pk, h1]
    have e1 : Z.pos x h = wnode (Z.pUp x) x.1 h := by unfold pos; rw [ite_eq_left h1.le]
    have hemb : (Z.I.ctx (Z.pos x h)).emb Z.j (Z.pk a x h).v (Z.pk a x h).key =
        some (Z.pUp x) := by
      rw [hpk]
      show ioEmb Z.E (Z.pos x h) Z.j x.1 _ = _
      rw [e1]
      exact ioEmb_eq_some hdisj hL.clC hL.vC (wnode_onWalk _ _ _)
    rw [hemb, Option.bind_some]
    by_cases h2 : h < (Z.pUp x).length
    · rw [ite_eq_left ((moves_up h1).2 h2), List.getElem?_eq_getElem h2, Option.map_some]
      have e2 : Z.pos x (h + 1) = wnode (Z.pUp x) x.1 (h + 1) := by
        unfold pos; rw [ite_eq_left (by omega)]
      rw [e1, e2, oth_wnode hL.wUp h2]
    · rw [ite_eq_right (fun hm => h2 ((moves_up h1).1 hm)), List.getElem?_eq_none (by omega)]
      rfl
  · simp only [h1, ↓reduceIte]
    have hpk : (Z.pk a x h).key = (srcPort (Z.cl x) (Z.ent x).2.1).2 := by simp [pk, h1]
    have hp : Z.pos x h = wnode (Z.pDn x) (Z.ent x).2.1 (2 * Z.D - h) :=
      pos_dn hL (by omega) (by omega)
    have hemb : (Z.I.ctx (Z.pos x h)).emb Z.j (Z.pk a x h).w (Z.pk a x h).key =
        some (Z.pDn x) := by
      rw [hpk]
      show ioEmb Z.E (Z.pos x h) Z.j (Z.ent x).2.1 _ = _
      rw [hp]
      exact ioEmb_eq_some hdisj hL.clC hL.wC (wnode_onWalk _ _ _)
    rw [hemb, Option.bind_some]
    by_cases h2 : 2 * Z.D - 1 - h < (Z.pDn x).length
    · rw [ite_eq_left ((moves_dn h1).2 h2), List.getElem?_eq_getElem h2, Option.map_some]
      have e2 : Z.pos x (h + 1) = wnode (Z.pDn x) (Z.ent x).2.1 (2 * Z.D - 1 - h) := by
        rw [pos_dn hL (h := h + 1) (by omega) (by omega)]; congr 1; omega
      rw [hp, e2, show 2 * Z.D - h = 2 * Z.D - 1 - h + 1 by omega, oth_wnode' hL.wDn h2]
    · rw [ite_eq_right (fun hm => h2 ((moves_dn h1).1 hm)), List.getElem?_eq_none (by omega)]
      rfl

/-- **The turn**: entering hop `h + 1`, the packet is updated by the local rule `adjL`. -/
lemma adj_pk (hZ : Z.OK) {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) (a : V × ℕ) (h : ℕ) :
    adjL (Z.I.ctx (Z.pos x (h + 1))) (h + 1) (Z.pk a x h) = Z.pk a x (h + 1) := by
  by_cases h1 : h + 1 = Z.D
  · have e : adjL (Z.I.ctx (Z.pos x (h + 1))) (h + 1) (Z.pk a x h) =
        turnL (Z.I.ctx (Z.pos x (h + 1))) (Z.pk a x h) := by
      unfold adjL; simp only [hD_ctx, h1, ↓reduceIte]
    rw [e, h1, pos_D hL]
    unfold turnL
    rw [show (Z.pk a x h).e = (Z.ent x).1 from rfl, hostC_eq hZ hL]
    simp [pk, show h < Z.D by omega]
  · have e : adjL (Z.I.ctx (Z.pos x (h + 1))) (h + 1) (Z.pk a x h) = Z.pk a x h := by
      unfold adjL; simp only [hD_ctx, h1, ↓reduceIte]
    rw [e]
    simp only [pk]
    congr 1
    by_cases h2 : h < Z.D
    · simp only [h2, show h + 1 < Z.D by omega, ↓reduceIte]
    · simp only [h2, show ¬ (h + 1 < Z.D) by omega, ↓reduceIte]

/-- a moving packet crosses an edge of the instance -/
lemma moves_adj (hZ : Z.OK) {x : V × ℕ} {hN : V} (hL : Z.LinkF x hN) {h : ℕ} (hh : h < 2 * Z.D)
    (hm : Z.moves x h) : (Z.I.G).Adj (Z.pos x h) (Z.pos x (h + 1)) ∧
      s(Z.pos x h, Z.pos x (h + 1)) ∈ Z.cl x := by
  -- the crossed edge is an edge of the path
  have hedge : ∃ e ∈ Z.E.path Z.j x.1 (Z.cl x) ++ Z.E.path Z.j (Z.ent x).2.1 (Z.cl x),
      e = s(Z.pos x h, Z.pos x (h + 1)) := by
    unfold moves at hm
    split_ifs at hm with h1
    · refine ⟨(Z.pUp x)[h], List.mem_append_left _ (List.getElem_mem _), ?_⟩
      have e1 : Z.pos x h = wnode (Z.pUp x) x.1 h := by unfold pos; rw [ite_eq_left h1.le]
      have e2 : Z.pos x (h + 1) = wnode (Z.pUp x) x.1 (h + 1) := by
        unfold pos; rw [ite_eq_left (by omega)]
      rw [e1, e2]; exact wnode_get hL.wUp hm
    · refine ⟨(Z.pDn x)[2 * Z.D - 1 - h], List.mem_append_right _ (List.getElem_mem _), ?_⟩
      rw [pos_dn hL (h := h) (by omega) (by omega), pos_dn hL (h := h + 1) (by omega) (by omega),
        show 2 * Z.D - h = 2 * Z.D - 1 - h + 1 by omega, show 2 * Z.D - (h + 1) = 2 * Z.D - 1 - h
          by omega, wnode_get hL.wDn hm, Sym2.eq_swap]
  obtain ⟨e, he, rfl⟩ := hedge
  have heC : s(Z.pos x h, Z.pos x (h + 1)) ∈ Z.cl x := by
    rcases List.mem_append.1 he with he | he
    · exact hZ.emb.local_ _ _ _ _ he
    · exact hZ.emb.local_ _ _ _ _ he
  have hG : Z.N.G.Adj (Z.pos x h) (Z.pos x (h + 1)) := by
    have := hZ.emb.sub _ hL.clC heC
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
  exact ⟨⟨hG, pos_mem hZ hL h, pos_mem hZ hL (h + 1)⟩, heC⟩

end RS

end RingLE
end APSP.Stoc.Congest
