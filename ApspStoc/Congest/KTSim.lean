import ApspStoc.Congest.KTDefs
import ApspStoc.Congest.Comb

/-!
# Simulating an algorithm on the node set inside the KT1 model

Once every node of `S` knows `S` (as a `Finset U`, from the gather phase, `KTGather.lean`), the
nodes can run any algorithm `Ain : ℕ → CAlg` of the model with known node set on the node set
`↥S`. The protocol `simP Ain n U : Proto U` does this:

* **Start.** A node reads the set `S'` from its input (the output of the gather phase) and, if it
  belongs to `S'`, starts `Ain n ↥S'` as the node `⟨me, _⟩ : ↥S'` with the context of the instance
  `baseInst` on `↥S'` rebuilt from its own context (`ctxIn`: its incident edges, viewed through
  `Subtype.val`), and with the coordinate `S'` of its seed. The seed space is the finite product
  `∀ S' : Finset U, (Ain n ↥S').Ω`, so the protocol does not depend on `S`.
* **Rounds.** Words are translated along `Subtype.val` (`liftW`) when sent and back (`lowW`) when
  received. A word that the inner run would drop (bandwidth `WordOK |S'|`) is not sent; the others
  pass the bandwidth check `WordOK |U|` of the outer run.
* **Halting.** A node halts when its inner run halts; its outputs (distances and next hops over
  `↥S'`) are translated to `U` (`liftMem`).

`st_sim`: in the run of `simP` on `ktInst S N` from inputs carrying `S`, every node `v ∈ S` holds
exactly the state of `v` in the run of `Ain n ↥S` on `baseInst N`, with seeds
`fun v => ω v.1 S`. Hence a successful inner run gives a successful outer run with the same
rounds and messages (`succ_sim`), and since the projection of the seeds has fibres of equal size,
the failure probability of the outer run is at most that of the inner run (`implI_sim`).
-/

namespace APSP.Stoc.Congest

namespace KT

open APSP Finset

set_option linter.unusedSectionVars false

variable {U : Type} [Fintype U] [DecidableEq U]

/-- algorithms with the type `CAlg` unfolded (so that applications are visibly functions) -/
abbrev CAlg' : Type 2 := ∀ (V : Type) [Fintype V] [DecidableEq V], Proto V

/-- the bandwidth check is decidable -/
instance instDecWordOK {V : Type} (k : ℕ) : DecidablePred (WordOK (V := V) k) := fun w =>
  match w with
  | .num j => inferInstanceAs (Decidable (j ≤ k + 3))
  | .id _ => isTrue trivial
  | .edge _ => isTrue trivial

/-! ## Translations -/

/-- a word over `↥S'` as a word over `U` -/
def liftW (S' : Finset U) : Word S' → Word U
  | .id v => .id v.1
  | .num k => .num k
  | .edge e => .edge (Sym2.map Subtype.val e)

open Classical in
/-- a word over `U` as a word over `↥S'` (`none` if it mentions an ID outside `S'`) -/
noncomputable def lowW (S' : Finset U) : Word U → Option (Word S')
  | .id v => if h : v ∈ S' then some (.id ⟨v, h⟩) else none
  | .num k => some (.num k)
  | .edge e => if h : ∃ e' : Sym2 S', Sym2.map Subtype.val e' = e then some (.edge h.choose)
      else none

lemma lowW_liftW (S' : Finset U) (w : Word S') : lowW S' (liftW S' w) = some w := by
  classical
  cases w with
  | id v => simp [liftW, lowW, v.2]
  | num k => rfl
  | edge e =>
    have hex : ∃ e' : Sym2 S', Sym2.map Subtype.val e' = Sym2.map Subtype.val e := ⟨e, rfl⟩
    simp only [liftW, lowW, dite_eq_left hex]
    rw [Sym2.map.injective Subtype.val_injective hex.choose_spec]

lemma card_sub_le (S' : Finset U) : Fintype.card S' ≤ Fintype.card U := by
  rw [Fintype.card_coe]; exact card_le_univ S'

lemma wordOK_liftW {S' : Finset U} {w : Word S'} (h : WordOK (Fintype.card S') w) :
    WordOK (Fintype.card U) (liftW S' w) := by
  cases w with
  | num k =>
    have := card_sub_le S'
    show k ≤ Fintype.card U + 3
    exact le_trans h (by omega)
  | id v => trivial
  | edge e => trivial

/-- the own weight view of a node, read from its context -/
noncomputable def kv (c : NCtx U) : Sym2 U → ℕ := (c.view (.inl c.me)).getD (fun _ => 0)

open Classical in
/-- the context of the node `me` in the instance `baseInst` on `↥S'`, rebuilt from the context
`c` of the node in the KT1 instance -/
noncomputable def ctxIn (S' : Finset U) (c : NCtx U) (me : S') : NCtx S' :=
  ⟨me, fun g => if g = .inl me then some (fun e => kv c (Sym2.map Subtype.val e)) else none, [],
    fun _ _ _ => none, ∅⟩

open Classical in
/-- the input of the node `me` in the instance `baseInst` on `↥S'` (no data) -/
noncomputable def inpIn (S' : Finset U) (me : S') : Agent S' → Option Mem :=
  fun g => if g = .inl me then some ⟨Unit, ()⟩ else none

open Classical in
/-- the node set read from the input (the output of the gather phase, paired with `()`) -/
noncomputable def getS : Option Mem → Finset U
  | some m => if h : m.1 = (Unit × Finset U) then (cast h m.2).2 else ∅
  | none => ∅

open Classical in
/-- an output of the inner run (distances and next hops over `↥S'`) as an output over `U` -/
noncomputable def liftMem (S' : Finset U) (v : U) (m : Mem) : Mem :=
  if h : m.1 = (S' → ℕ × S') then
    ⟨U → ℕ × U, fun u => if hu : u ∈ S' then
      (((cast h m.2) ⟨u, hu⟩).1, ((cast h m.2) ⟨u, hu⟩).2.1) else (0, v)⟩
  else m

/-- the outputs of the agents of a node, over `U` -/
noncomputable def liftOut (S' : Finset U) (o : Agent S' → Option Mem) : Agent U → Option Mem
  | .inl v => if hv : v ∈ S' then (o (.inl ⟨v, hv⟩)).map (liftMem S' v) else none
  | .inr _ => none

/-! ## The simulating protocol -/

variable (Ain : ℕ → CAlg') (n : ℕ)

/-- states of the simulation: `none` (a node outside the node set it read), or the node set `S'`,
the inner context and the inner state -/
abbrev SimSt (U : Type) [Fintype U] [DecidableEq U] : Type 1 :=
  Option (Σ S' : Finset U, NCtx S' × (Ain n S').S)

/-- the initial state of the simulation, from the node set `S'` read from the input -/
noncomputable def simInit (c : NCtx U) (S' : Finset U) (ω : ∀ S' : Finset U, (Ain n S').Ω) :
    SimSt Ain n U :=
  if h : c.me ∈ S' then
    some ⟨S', ctxIn S' c ⟨c.me, h⟩, (Ain n S').init (ctxIn S' c ⟨c.me, h⟩) (inpIn S' ⟨c.me, h⟩) (ω S')⟩
  else none

/-- **The simulation protocol**: run `Ain n ↥S'` on the node set `S'` read from the input. -/
@[reducible] noncomputable def simP (U : Type) [Fintype U] [DecidableEq U] : Proto U where
  S := SimSt Ain n U
  Ω := ∀ S' : Finset U, (Ain n S').Ω
  init c inp ω := simInit Ain n c (getS (inp (.inl c.me))) ω
  send _ s u := match s with
    | none => none
    | some ⟨S', ci, σ⟩ => if hu : u ∈ S' then
        ((Ain n S').send ci σ ⟨u, hu⟩).bind
          (fun w => if WordOK (Fintype.card S') w then some (liftW S' w) else none)
      else none
  recv _ s m := match s with
    | none => none
    | some ⟨S', ci, σ⟩ => some ⟨S', ci, (Ain n S').recv ci σ (fun u => (m u.1).bind (lowW S'))⟩
  out s := match s with
    | none => some (fun _ => none)
    | some ⟨S', _, σ⟩ => ((Ain n S').out σ).map (liftOut S')

/-! ## Counting seeds -/

lemma card_filter_equiv_fst {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (e : X ≃ Y × Z)
    (P : Y → Prop) [DecidablePred P] :
    (univ.filter (fun x => P (e x).1)).card = (univ.filter P).card * Fintype.card Z := by
  classical
  rw [card_filter, card_filter]
  rw [← Equiv.sum_comp e.symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl (fun y _ => ?_)
  split_ifs <;> simp

/-- the seeds of the simulation as the seeds of the inner run and the rest -/
noncomputable def seedEquiv (S : Finset U) :
    (U → ∀ S' : Finset U, (Ain n S').Ω) ≃ (S → (Ain n S).Ω) ×
      (({u // u ∉ S} → (Ain n S).Ω) × (U → ∀ S' : {S' : Finset U // S' ≠ S}, (Ain n S'.1).Ω)) :=
  ((Equiv.piCongrRight (fun _ => Equiv.piSplitAt S (fun S' : Finset U => (Ain n S').Ω))).trans
    ((Equiv.arrowProdEquivProdArrow U _ _).trans
      (Equiv.prodCongr (Equiv.piEquivPiSubtypeProd (· ∈ S) _) (Equiv.refl _)))).trans
    (Equiv.prodAssoc _ _ _)

lemma seedEquiv_fst (S : Finset U) (ω : U → ∀ S' : Finset U, (Ain n S').Ω) :
    (seedEquiv Ain n S ω).1 = fun v => ω v.1 S := rfl

/-! ## The run of the simulation -/

section Run

variable {Ain n} {S : Finset U} {N : WNet S}

lemma simP_out (ci : NCtx S) (σ : (Ain n S).S) :
    (simP Ain n U).out (some ⟨S, ci, σ⟩) = ((Ain n S).out σ).map (liftOut S) := rfl

lemma simP_send (c : NCtx U) (ci : NCtx S) (σ : (Ain n S).S) (v : S) :
    (simP Ain n U).send c (some ⟨S, ci, σ⟩) v.1 = ((Ain n S).send ci σ v).bind
      (fun w => if WordOK (Fintype.card S) w then some (liftW S w) else none) := by
  show (if hu : v.1 ∈ S then _ else _) = _
  rw [dite_eq_left v.2]

lemma simP_send_isSome {c : NCtx U} {ci : NCtx S} {σ : (Ain n S).S} {v : U}
    (h : ((simP Ain n U).send c (some ⟨S, ci, σ⟩) v).isSome) :
    ∃ hv : v ∈ S, ((Ain n S).send ci σ ⟨v, hv⟩).isSome := by
  by_cases hv : v ∈ S
  · refine ⟨hv, ?_⟩
    have h' := simP_send (Ain := Ain) (n := n) c ci σ ⟨v, hv⟩
    change ((simP Ain n U).send c (some ⟨S, ci, σ⟩) (⟨v, hv⟩ : S).1).isSome at h
    rw [h'] at h
    cases hs : (Ain n S).send ci σ ⟨v, hv⟩ with
    | none => rw [hs] at h; simp at h
    | some w => rfl
  · exfalso
    have : (simP Ain n U).send c (some ⟨S, ci, σ⟩) v = none := by
      show (if hu : v ∈ S then _ else _) = _
      rw [dite_eq_right hv]
    rw [this] at h; simp at h

lemma simP_recv (c : NCtx U) (ci : NCtx S) (σ : (Ain n S).S) (m : U → Option (Word U)) :
    (simP Ain n U).recv c (some ⟨S, ci, σ⟩) m =
      some ⟨S, ci, (Ain n S).recv ci σ (fun u => (m u.1).bind (lowW S))⟩ := rfl

/-- a message is sent only along an edge -/
lemma adj_of_msg {V : Type} [Fintype V] [DecidableEq V] {P : Proto V} {I : Inst V}
    {σ : V → P.S} {u v : V} (h : (msg P I σ u v).isSome) : I.G.Adj u v := by
  classical
  unfold msg at h
  by_contra hadj
  rw [ite_eq_right (fun h' => hadj h'.1)] at h
  simp at h

/-- the messages of the simulation are the translated inner messages -/
lemma msg_sim {σo : U → (simP Ain n U).S} {σi : S → (Ain n S).S}
    (hσ : ∀ u : S, σo u.1 = some ⟨S, (baseInst N).ctx u, σi u⟩) (u v : S) :
    msg (simP Ain n U) (ktInst S N) σo u.1 v.1 = (msg (Ain n S) (baseInst N) σi u v).map (liftW S) := by
  classical
  unfold msg
  by_cases hadj : N.G.Adj u v
  · have hadj' : (ktInst S N).G.Adj u.1 v.1 := ktInst_adj_sub.2 hadj
    have hadjb : (baseInst N).G.Adj u v := hadj
    rw [hσ u, simP_out]
    by_cases ho : (Ain n S).out (σi u) = none
    · rw [ite_eq_left ⟨hadj', by rw [ho]; rfl⟩, ite_eq_left ⟨hadjb, ho⟩, simP_send]
      cases hs : (Ain n S).send ((baseInst N).ctx u) (σi u) v with
      | none => rfl
      | some w =>
        simp only [Option.bind_some]
        by_cases hw : WordOK (Fintype.card S) w
        · rw [ite_eq_left hw, ite_eq_left hw]
          simp only [Option.map_some]
          rw [ite_eq_left (wordOK_liftW hw)]
        · rw [ite_eq_right hw, ite_eq_right hw]; rfl
    · rw [ite_eq_right (fun h => ho (Option.map_eq_none_iff.1 h.2)), ite_eq_right (fun h => ho h.2)]
      rfl
  · rw [ite_eq_right (fun h => hadj (ktInst_adj_sub.1 h.1)), ite_eq_right (fun h => hadj h.1)]
    rfl

variable {x : Agent U → Mem}

lemma getS_inp (hx : ∀ v ∈ S, x (.inl v) = ⟨Unit × Finset U, ((), S)⟩) (v : S) :
    getS (inpAt (ktInst S N) x v.1 (.inl v.1)) = S := by
  classical
  have h1 : inpAt (ktInst S N) x v.1 (.inl v.1) = some (x (.inl v.1)) := by
    unfold inpAt
    rw [ite_eq_left (ktInst_host_eq.2 ⟨rfl, v.2⟩)]
  rw [h1, hx v.1 v.2]
  simp only [getS]
  rw [dite_eq_left trivial]
  rfl

lemma ctxIn_eq (v : S) : ctxIn S ((ktInst S N).ctx v.1) v = (baseInst N).ctx v := by
  classical
  have hk : kv ((ktInst S N).ctx v.1) = ktView S N v.1 := by
    simp [kv, ktInst_ctx]
  simp only [ctxIn, baseInst, hk]
  congr 1
  funext g
  by_cases hg : g = .inl v
  · subst hg
    rw [ite_eq_left rfl, ite_eq_left rfl]
    congr 1
    funext e
    exact ktView_map v e
  · rw [ite_eq_right hg, ite_eq_right hg]

lemma inpIn_eq (v : S) : inpIn S v = inpAt (baseInst N) (inOf (fun _ => ())) v := by
  classical
  funext g
  unfold inpIn inpAt
  cases g with
  | inl u =>
    by_cases hu : u = v
    · subst hu; simp [baseInst, physHost, inOf]
    · simp [baseInst, physHost, hu]
  | inr C => simp [baseInst, physHost]

/-- **The run of the simulation** follows the inner run at every node of `S`. -/
theorem st_sim (hx : ∀ v ∈ S, x (.inl v) = ⟨Unit × Finset U, ((), S)⟩)
    (ω : U → (simP Ain n U).Ω) : ∀ t (v : S),
    st (simP Ain n U) (ktInst S N) x ω t v.1 = some ⟨S, (baseInst N).ctx v,
      st (Ain n S) (baseInst N) (inOf (fun _ => ())) (fun v => ω v.1 S) t v⟩ := by
  intro t
  induction t with
  | zero =>
    intro v
    show simInit Ain n ((ktInst S N).ctx v.1) (getS (inpAt (ktInst S N) x v.1 (.inl v.1))) (ω v.1) = _
    rw [getS_inp hx v]
    unfold simInit
    rw [dite_eq_left (show ((ktInst S N).ctx v.1).me ∈ S from v.2)]
    have h1 : (⟨((ktInst S N).ctx v.1).me, v.2⟩ : S) = v := rfl
    rw [h1, ctxIn_eq v, inpIn_eq v]
    rfl
  | succ t ih =>
    intro v
    rw [st_succ, st_succ]
    unfold step
    rw [ih v, simP_out]
    by_cases ho : ((Ain n S).out (st (Ain n S) (baseInst N) (inOf fun _ => ())
        (fun v => ω v.1 S) t v)).isSome
    · rw [ite_eq_left (by simpa using ho), ite_eq_left ho]
    · rw [ite_eq_right (by simpa using ho), ite_eq_right ho, simP_recv]
      have hm : (fun u : S => (msg (simP Ain n U) (ktInst S N) (st (simP Ain n U) (ktInst S N) x ω t)
          u.1 v.1).bind (lowW S)) = fun u => msg (Ain n S) (baseInst N)
            (st (Ain n S) (baseInst N) (inOf fun _ => ()) (fun v => ω v.1 S) t) u v := by
        funext u
        rw [msg_sim (fun u => ih u) u v, Option.bind_map]
        cases (msg (Ain n S) (baseInst N) (st (Ain n S) (baseInst N) (inOf fun _ => ())
          (fun v => ω v.1 S) t) u v) with
        | none => rfl
        | some w => exact lowW_liftW S w
      rw [hm]

/-- the postcondition of the inner run: APSP on `N` -/
def postIn (N : WNet S) : (Agent S → Mem) → Prop :=
  postOf (baseInst N) (fun z : Agent S → (S → ℕ × S) => APSPSpec N (fun v => z (.inl v)))

/-- the postcondition of the KT1 run: APSP on `N`, read through `ktOut` -/
def postKT (N : WNet S) : (Agent U → Mem) → Prop :=
  postOf (ktInst S N) (fun z : Agent U → (U → ℕ × U) => APSPSpec N (ktOut S z))

lemma liftMem_mk (v : U) (f : S → ℕ × S) :
    liftMem S v ⟨S → ℕ × S, f⟩ = ⟨U → ℕ × U, fun u => if hu : u ∈ S then
      ((f ⟨u, hu⟩).1, (f ⟨u, hu⟩).2.1) else (0, v)⟩ := by
  classical
  unfold liftMem
  rw [dite_eq_left rfl]
  rfl

lemma sentSet_sim_card {σo : U → (simP Ain n U).S} {σi : S → (Ain n S).S}
    (hσ : ∀ u : S, σo u.1 = some ⟨S, (baseInst N).ctx u, σi u⟩) :
    (sentSet (simP Ain n U) (ktInst S N) σo).card ≤ (sentSet (Ain n S) (baseInst N) σi).card := by
  classical
  let f : S × S → U × U := fun uv => (uv.1.1, uv.2.1)
  have hsub : sentSet (simP Ain n U) (ktInst S N) σo ⊆ (sentSet (Ain n S) (baseInst N) σi).image f := by
    intro uv huv
    unfold sentSet at huv
    simp only [mem_filter, mem_univ, true_and] at huv
    have hadj := adj_of_msg huv
    obtain ⟨hu, hv, -⟩ := ktInst_adj.1 hadj
    rw [mem_image]
    refine ⟨(⟨uv.1, hu⟩, ⟨uv.2, hv⟩), ?_, rfl⟩
    unfold sentSet
    simp only [mem_filter, mem_univ, true_and]
    have := msg_sim (N := N) hσ ⟨uv.1, hu⟩ ⟨uv.2, hv⟩
    simp only at this
    rw [this] at huv
    simpa using huv
  exact (card_le_card hsub).trans card_image_le

lemma loadUpTo_le_msgsUpTo {V : Type} [Fintype V] [DecidableEq V] (P : Proto V) (I : Inst V)
    (x : Agent V → Mem) (ω : V → P.Ω) (t : ℕ) (e : Sym2 V) :
    loadUpTo P I x ω t e ≤ msgsUpTo P I x ω t := by
  classical
  unfold loadUpTo msgsUpTo
  exact sum_le_sum (fun s _ => card_filter_le _ _)

/-- **A successful inner run gives a successful run of the simulation**, with the same rounds and
messages (and at most all messages over any edge). -/
theorem succ_sim (hx : ∀ v ∈ S, x (.inl v) = ⟨Unit × Finset U, ((), S)⟩)
    {q : Prof S} (ω : U → (simP Ain n U).Ω)
    (hs : Succ (Ain n S) (baseInst N) (inOf (fun _ => ())) (postIn N) q (fun v => ω v.1 S)) :
    Succ (simP Ain n U) (ktInst S N) x (postKT N) (Prof.mk q.rounds (fun _ => q.msgs) q.msgs) ω := by
  classical
  obtain ⟨t, hH, hP, hr, hm, -, y, hy, z, hz, hQ⟩ := hs
  have hst := st_sim (N := N) hx ω
  have hmsg : msgsUpTo (simP Ain n U) (ktInst S N) x ω t ≤ q.msgs := by
    refine le_trans ?_ hm
    unfold msgsUpTo
    exact sum_le_sum (fun s _ => sentSet_sim_card (fun u => hst s u))
  -- the outputs
  let zo : Agent U → (U → ℕ × U) := fun g => match g with
    | .inl v => if h : v ∈ S then (fun u => if hu : u ∈ S then
        ((z (.inl ⟨v, h⟩) ⟨u, hu⟩).1, (z (.inl ⟨v, h⟩) ⟨u, hu⟩).2.1) else (0, v)) else fun u => (0, u)
    | .inr _ => fun u => (0, u)
  refine ⟨t, ⟨fun v hv => ?_, fun s hs v hv => ?_⟩, ?_, hr, hmsg,
    fun e => (loadUpTo_le_msgsUpTo _ _ _ _ _ e).trans hmsg,
    fun g => ⟨U → ℕ × U, zo g⟩, fun g hg => ?_, ⟨zo, fun g _ => rfl, ?_⟩⟩
  · rw [hst t ⟨v, hv⟩, simP_out, Option.isSome_map]
    exact hH.1 ⟨v, hv⟩ trivial
  · rw [hst s ⟨v, hv⟩, simP_out, hH.2 s hs ⟨v, hv⟩ trivial]
    rfl
  · intro s hs u hu hout v hv
    rw [hst s ⟨u, hu⟩] at hout hv
    rw [simP_out, Option.map_eq_none_iff] at hout
    obtain ⟨hv', hsend⟩ := simP_send_isSome hv
    exact ktInst_adj_sub.2 (hP s hs ⟨u, hu⟩ trivial hout ⟨v, hv'⟩ hsend)
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hg
    obtain ⟨rfl, hvS⟩ := ktInst_host_eq.1 hv
    have hout : outAt (simP Ain n U) (ktInst S N) x ω t (.inl v) =
        ((simP Ain n U).out (st (simP Ain n U) (ktInst S N) x ω t v)).bind (fun m => m (.inl v)) := by
      unfold outAt; rw [hv]
    rw [hout, hst t ⟨v, hvS⟩, simP_out]
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (hH.1 ⟨v, hvS⟩ trivial)
    have hyi : o (.inl ⟨v, hvS⟩) = some (y (.inl ⟨v, hvS⟩)) := by
      have := hy (.inl ⟨v, hvS⟩) rfl
      unfold outAt at this
      rw [show (baseInst N).host (.inl ⟨v, hvS⟩) = some ⟨v, hvS⟩ from rfl] at this
      dsimp only at this
      rw [ho] at this
      exact this
    rw [ho]
    simp only [Option.map_some, Option.bind_some, liftOut, dite_eq_left hvS]
    rw [hyi, Option.map_some, hz (.inl ⟨v, hvS⟩) rfl, liftMem_mk]
    simp only [zo, dite_eq_left hvS]
  · convert hQ using 1
    funext v u
    simp only [ktOut, zo, dite_eq_left v.2, dite_eq_left u.2]
    rw [dite_eq_left (z (.inl v) u).2.2]

/-- **The simulation fails at most as often as the inner run.** -/
theorem implI_sim (hx : ∀ v ∈ S, x (.inl v) = ⟨Unit × Finset U, ((), S)⟩)
    {q : Prof S} {δ : ℝ}
    (h : ImplI (Ain n S) (baseInst N) (inOf (fun _ => ())) (postIn N) q δ) :
    ImplI (simP Ain n U) (ktInst S N) x (postKT N) (Prof.mk q.rounds (fun _ => q.msgs) q.msgs) δ := by
  classical
  refine le_trans ?_ h
  unfold failProb
  have hc := card_filter_equiv_fst (seedEquiv Ain n S)
    (fun ω' => ¬ Succ (Ain n S) (baseInst N) (inOf (fun _ => ())) (postIn N) q ω')
  have hX : Fintype.card (U → (simP Ain n U).Ω) = Fintype.card (S → (Ain n S).Ω) *
      Fintype.card (({u // u ∉ S} → (Ain n S).Ω) ×
        (U → ∀ S' : {S' : Finset U // S' ≠ S}, (Ain n S'.1).Ω)) := by
    rw [Fintype.card_congr (seedEquiv Ain n S), Fintype.card_prod]
  have hle : (univ.filter (fun ω : U → (simP Ain n U).Ω =>
      ¬ Succ (simP Ain n U) (ktInst S N) x (postKT N)
        (Prof.mk q.rounds (fun _ => q.msgs) q.msgs) ω)).card ≤
      (univ.filter (fun ω : U → (simP Ain n U).Ω =>
        ¬ Succ (Ain n S) (baseInst N) (inOf (fun _ => ())) (postIn N) q
          (seedEquiv Ain n S ω).1)).card := by
    refine card_le_card (fun ω => ?_)
    simp only [mem_filter, mem_univ, true_and]
    intro h1 h2
    exact h1 (succ_sim hx ω (by rw [← seedEquiv_fst]; exact h2))
  have hZ : 0 < Fintype.card (({u // u ∉ S} → (Ain n S).Ω) ×
      (U → ∀ S' : {S' : Finset U // S' ≠ S}, (Ain n S'.1).Ω)) := Fintype.card_pos
  have hY : 0 < Fintype.card (S → (Ain n S).Ω) := Fintype.card_pos
  rw [hX]
  calc ((univ.filter (fun ω : U → (simP Ain n U).Ω =>
      ¬ Succ (simP Ain n U) (ktInst S N) x (postKT N)
        (Prof.mk q.rounds (fun _ => q.msgs) q.msgs) ω)).card : ℝ) / _
      ≤ ((univ.filter (fun ω : U → (simP Ain n U).Ω =>
        ¬ Succ (Ain n S) (baseInst N) (inOf (fun _ => ())) (postIn N) q
          (seedEquiv Ain n S ω).1)).card : ℝ) / _ := by
        gcongr
    _ = _ := by
        rw [hc]
        push_cast
        rw [mul_div_mul_right _ _ (by exact_mod_cast hZ.ne')]

end Run

end KT

end APSP.Stoc.Congest
