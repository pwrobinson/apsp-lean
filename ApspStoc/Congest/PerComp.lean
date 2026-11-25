import ApspStoc.Congest.PerCompTrav
import ApspStoc.Congest.Rules
import ApspStoc.Congest.TreeCast
import ApspStoc.Congest.Notify

/-!
# Sequential execution on the components of a subset: `perCompR` in the CONGEST semantics

`perCompR_congest : PerCompRC` is the concrete version of the toolkit field `perCompR`
(`Toolkit.lean`, as repaired: type families `A`, `Bt`, `EmbValid`, `j < n`, `K₀·aggLen`), with the
algorithm `perCompC A Bt Am B` and the constant `K₀ = 60`.

## The protocol (`perCompC`)
All phases run on the footprint of `P`; each one starts in the round where the previous one ends.
1. `Am` on `P` (local call extracting the flag `v ∈ P`): a rooted spanning tree of `P`.
2. `Am` on `S` (flag `v ∈ S`): a rooted spanning forest of `G[S]`, one tree per component `K`,
   rooted at its leader.
3. `|K|` by convergecast and broadcast on the trees of the forest (`tcProto`, `TreeCast.lean`,
   with the capped addition `capAdd`).
4. Two notification rounds (`notify_congest`): every node learns its children in the tree of `P`
   and in the forest of `S`.
5. The traversal (`travA`, `PerCompTrav.lean`): a token traverses the tree of `P` depth-first; at
   the first visit of the leader of a component `K`, the phase of `K` broadcasts the start on `K`'s
   tree and announces it (with `|K|` and the leader) along the aggregator paths of the nodes of
   `K` (hop-synchronised, `PerCompPath.lean`), so that the whole footprint of `K` starts `B` in the
   same round, with the context and the inputs of the instance of `K`; by proper sends, `B` sends
   nothing outside this footprint, and the run of `B` inside the traversal is its standalone run
   (`PerCompEmb.lean`); when `B` halts, the token moves on. At the end, the root announces the end
   in the same way on the tree of `P` and along the paths of `P`, and all of the footprint halts.

## The proof
The preparation phases are composed by `c_bind`/`c_callR` from their contracts (`Am`; `tc_succ`;
`notify_congest`); the traversal is `trav_implI` (its own costs: `O((dil+1)(sz+1))` rounds,
load `≤ 18ρ`, messages `≤ 12|P| + 6·aggLen j P`, plus those of the sub-runs; failure: union bound
over the components).
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The preparation -/

/-- capped addition of one-word counters -/
def capAdd (n : ℕ) (m m' : Msg V) : Msg V := [Word.num (min n (numW (some m) + numW (some m')))]

/-- the data after the first `Am` -/
abbrev X1 (A : Type → Type) (V : Type) : Type := ((Bool × Bool) × A V) × (Option V × V)
/-- the data after the second `Am` -/
abbrev X2 (A : Type → Type) (V : Type) : Type := X1 A V × (Option V × V)
/-- the data after the component sizes -/
abbrev X3 (A : Type → Type) (V : Type) : Type := X2 A V × Option (Msg V)
/-- the data after the children in the tree of `P` -/
abbrev X4 (A : Type → Type) (V : Type) : Type := X3 A V × Finset V

/-- the flag `v ∈ P` -/
def pcF1 (A : Type → Type) : LocFn := ⟨fun V => (Bool × Bool) × A V, fun _ => Bool,
  fun _ _ _ _ _ x => x.1.1⟩

/-- the flag `v ∈ S` -/
def pcF2 (A : Type → Type) : LocFn := ⟨X1 A, fun _ => Bool, fun _ _ _ _ _ x => x.1.1.2⟩

/-- the input of the size computation: parent, root, the value `1`, capped addition -/
def pcF3 (A : Type → Type) : LocFn := ⟨X2 A, TCIn, fun V _ _ g _ x => match g with
  | .inl _ => if x.1.1.1.2 = true then
      some (x.2.1, x.2.2, [Word.num 1], capAdd (Fintype.card V)) else none
  | .inr _ => none⟩

/-- the parent, as a set (empty at a root) -/
def optS {V : Type} : Option V → Finset V
  | some p => {p}
  | none => ∅

/-- notify the parent in the tree of `P` -/
def pcF4 (A : Type → Type) : LocFn := ⟨X3 A, fun V => Finset V, fun _ _ _ g _ x => match g with
  | .inl _ => if x.1.1.1.1.1 = true then optS x.1.1.2.1 else ∅
  | .inr _ => ∅⟩

/-- notify the parent in the forest of `S` -/
def pcF5 (A : Type → Type) : LocFn := ⟨X4 A, fun V => Finset V, fun _ _ _ g _ x => match g with
  | .inl _ => if x.1.1.1.1.1.2 = true then optS x.1.1.2.1 else ∅
  | .inr _ => ∅⟩

/-- the convergecast/broadcast algorithm of `TreeCast.lean` (one-word values, `Bw = 0`) -/
noncomputable def tcA : CAlg := fun V _ _ => tcProto 0 1 V

/-- the notification algorithm of `Notify.lean` -/
noncomputable def ntA : CAlg := Classical.choose notify_congest

/-- **The algorithm**: `perCompC A Bt Am B`. -/
noncomputable def perCompC (A Bt : Type → Type) (Am B : CAlg) : CAlg :=
  cseq (ccall (pcF1 A) Am) (cseq (ccall (pcF2 A) Am) (cseq (ccall (pcF3 A) tcA)
    (cseq (ccall (pcF4 A) ntA) (cseq (ccall (pcF5 A) ntA) (travA A Bt B)))))

/-- The toolkit field `perCompR` for the CONGEST semantics (the field of `Toolkit.lean` with
`CImplT` for `Impl`, `CAlg` for `Alg`, and the algorithm `perCompC`; `toToolkit` in `Model.lean`
checks that the two agree). -/
def PerCompRC : Prop :=
  ∃ K₀ : ℕ, ∀ (A Bt : Type → Type) (Am B : CAlg) {V : Type} [Fintype V] [DecidableEq V]
    [Nonempty (Bt V)] (N : WNet V) (E : Overlays V) (j sz : ℕ) (P S : Finset V)
    (z : Agent V → A V) (R : Finset V → (Agent V → Bt V) → Prop) (pm pm' : Prof V) (δm δm' : ℝ)
    (p : Finset V → Prof V) (δ : Finset V → ℝ),
    EmbValid N.G E → j < Fintype.card V →
    S ⊆ P → ConnSet N.G P → P.card ≤ sz →
    (∀ K y y', (∀ v ∈ K, y (.inl v) = y' (.inl v)) → R K y → R K y') →
    CImplT Am N (.mst E j sz (footprint E j P) P) pm δm →
    CImplT Am N (.mst E j sz (footprint E j P) S) pm' δm' →
    (∀ K ∈ comps N.G S, CImplT B N (.io E j K.card (footprint E j K) (Bool × A V) (Bt V)
      (fun g => (memAg K g, z g)) (R K)) (p K) (δ K)) →
    CImplT (perCompC A Bt Am B) N (.io E j sz (footprint E j P) ((Bool × Bool) × A V) (Bt V)
        (fun g => ((memAg P g, memAg S g), z g)) (fun y => ∀ K ∈ comps N.G S, R K y))
      (pm + pm' + ∑ K ∈ comps N.G S, p K +
        Prof.mk (K₀ * (E.dil + 1) ^ 2 * (sz + 1)) (fun e => K₀ * E.rho N.G j P e)
          (K₀ * (P.card + 1) + K₀ * E.aggLen j P))
      (δm + δm' + ∑ K ∈ comps N.G S, δ K)

/-! ## Component sizes -/

lemma numW_capAdd (n : ℕ) (m m' : Msg V) :
    numW (some (capAdd n m m')) = min n (numW (some m) + numW (some m')) := rfl

lemma aggOf_capAdd {n : ℕ} : ∀ {s : Multiset (Msg V)} {Y : Msg V}, AggOf (capAdd n) s Y →
    (∀ m ∈ s, m = [Word.num 1]) → Multiset.card s ≤ n → Y = [Word.num (Multiset.card s)]
  | _, _, .single a, h, _ => by rw [h a (by simp)]; simp
  | _, _, .comb (s := s) (t := t) (a := a) (b := b) ha hb, h, hn => by
    rw [Multiset.card_add] at hn ⊢
    have h1 := aggOf_capAdd ha (fun m hm => h m (Multiset.mem_add.2 (Or.inl hm))) (by omega)
    have h2 := aggOf_capAdd hb (fun m hm => h m (Multiset.mem_add.2 (Or.inr hm))) (by omega)
    subst h1; subst h2
    simp only [capAdd, numW, Nat.min_eq_right hn]

/-- the edges of a rooted forest -/
noncomputable def treeE (Q : Finset V) (par : V → Option V) : Finset (Sym2 V) :=
  (Q.filter (fun v => (par v).isSome)).image (fun v => s(v, (par v).getD v))

lemma mem_treeE {Q : Finset V} {par : V → Option V} {v u : V} (hv : v ∈ Q) (hu : par v = some u) :
    s(v, u) ∈ treeE Q par := by
  unfold treeE
  rw [mem_image]
  exact ⟨v, mem_filter.2 ⟨hv, by rw [hu]; rfl⟩, by rw [hu]; rfl⟩

lemma card_treeE (Q : Finset V) (par : V → Option V) : (treeE Q par).card ≤ Q.card :=
  card_image_le.trans (card_filter_le _ _)

lemma treeE_sub {G : SimpleGraph V} [DecidableRel G.Adj] {Q : Finset V} {par : V → Option V}
    (h : ∀ v ∈ Q, ∀ u, par v = some u → G.Adj v u) {e : Sym2 V} (he : e ∈ treeE Q par) :
    e ∈ G.edgeFinset ∧ ∃ v ∈ Q, v ∈ e := by
  unfold treeE at he
  obtain ⟨v, hv, rfl⟩ := mem_image.1 he
  obtain ⟨hvQ, hs⟩ := mem_filter.1 hv
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hs
  rw [hu]
  exact ⟨SimpleGraph.mem_edgeFinset.2 (h v hvQ u hu), v, hvQ, Sym2.mem_mk_left _ _⟩

/-! ## The preparation phases -/

section Prep

variable {A : Type → Type} {N : WNet V} {E : Overlays V} {j sz : ℕ} {P S : Finset V}

/-- **The component sizes** by convergecast and broadcast on the forest of `S`. -/
lemma tc_implI (hSP : S ⊆ P) (hsz : P.card ≤ sz) (x2 : Agent V → X2 A V)
    (hx2 : ∀ v, (x2 (.inl v)).1.1.1.2 = decide (v ∈ S))
    (hF : SpanForest S (inducedEdges N.G S) (fun v => (x2 (.inl v)).2.1)
      (fun v => (x2 (.inl v)).2.2)) :
    CImplT tcA N (.io E j sz (footprint E j P) (TCIn V) (Option (Msg V))
      (fun g => (pcF3 A).f V g (lview N g) (x2 g))
      (fun y => ∀ v ∈ S, numW (y (.inl v)) =
        (S.filter (fun u => (x2 (.inl u)).2.2 = (x2 (.inl v)).2.2)).card))
      (Prof.mk (tcK 0 * (1 + 1) * (sz + 1)) (onEdges (inducedEdges N.G S) (tcK 0 * (1 + 1)))
        (tcK 0 * (1 + 1) * (S.card + 1))) 0 := by
  classical
  set par := fun v => (x2 (.inl v)).2.1
  set root := fun v => (x2 (.inl v)).2.2
  obtain ⟨rk, hrk⟩ := hF.rank
  have hT : TreeOK S par rk root := ⟨hF.mem, hrk, hF.root_par, hF.root_self⟩
  have hSn : S.card ≤ Fintype.card V := card_le_univ _
  have henc : ∀ c ∈ S, EncOK (Fintype.card V) 0 1
      (agg S par rk (fun _ => [Word.num 1]) (capAdd (Fintype.card V)) c) := by
    intro c hc
    have h := agg_pres hrk (fun _ => [Word.num 1]) (capAdd (Fintype.card V))
      (fun m => m.length ≤ 1 ∧ ∀ k, Word.num k ∈ m → k ≤ Fintype.card V)
      (fun v hv => ⟨by simp, fun k hk => by
        simp at hk
        have : 0 < S.card := card_pos.2 ⟨v, hv⟩
        omega⟩)
      (fun m m' _ _ => ⟨by simp [capAdd], fun k hk => by
        simp [capAdd] at hk; rw [hk]; exact min_le_left _ _⟩) c hc
    exact ⟨h.1, fun k hk => by have := h.2 k hk; simp only [zero_add, pow_one]; omega⟩
  show ImplI (tcProto 0 1 V) _ _ _ _ _
  refine ImplI.of_forall _ _ le_rfl (fun ω => ?_)
  refine (tc_succ 0 1 (ioInst N E j sz (footprint E j P)) _ S par rk (fun _ => [Word.num 1])
    (capAdd (Fintype.card V)) root sz (inducedEdges N.G S) hT ((card_le_card hSP).trans hsz)
    henc (fun v hv u hu => hF.edge v hv u hu) (fun v hv u hu => ?_) (fun v => ⟨rfl, rfl⟩)
    (fun v => ?_) (fun u v h => ?_) ω).mono _ _ le_rfl ?_
  · have := hF.edge v hv u hu
    rw [memIE] at this
    exact ⟨this.1, subset_footprint _ _ _ (hSP this.2.1), subset_footprint _ _ _ (hSP this.2.2)⟩
  · by_cases hv : v ∈ footprint E j P
    · have hinp : inpAt (ioInst N E j sz (footprint E j P))
          (inOf (α := TCIn V) (fun g => (pcF3 A).f V g (lview N g) (x2 g))) v (.inl v) =
          some ⟨TCIn V, (pcF3 A).f V (.inl v) (lview N (.inl v)) (x2 (.inl v))⟩ := by
        simp [inpAt, ioInst, ioHost, hv, inOf]
      simp only [myIn, hinp, dif_pos, cast_eq]
      simp only [pcF3, hx2 v]
      by_cases hvS : v ∈ S <;> simp [hvS] <;> exact ⟨rfl, rfl⟩
    · have hinp : inpAt (ioInst N E j sz (footprint E j P))
          (inOf (α := TCIn V) (fun g => (pcF3 A).f V g (lview N g) (x2 g))) v (.inl v) = none := by
        simp [inpAt, ioInst, ioHost, hv]
      simp only [myIn, hinp]
      have : v ∉ S := fun h => hv (subset_footprint _ _ _ (hSP h))
      simp [this]
  · simp only [ioInst, ioHost] at h; split_ifs at h; exact Option.some.inj h
  · rintro yy ⟨zz, hzz, hspec⟩
    refine ⟨zz, hzz, fun v hv => ?_⟩
    obtain ⟨Y, hY, hagg, -⟩ := hspec v hv
    rw [hY]
    have := aggOf_capAdd hagg (fun m hm => by
      rw [Multiset.mem_map] at hm; obtain ⟨_, _, rfl⟩ := hm; rfl)
      (by rw [Multiset.card_map, card_val]; exact (card_filter_le _ _).trans hSn)
    rw [this, Multiset.card_map, card_val]
    rfl

end Prep

/-! ## The theorem -/

lemma onEdges_le_rho {N : WNet V} {E : Overlays V} {j : ℕ} {P : Finset V} {F : Finset (Sym2 V)}
    (hF : ∀ e ∈ F, e ∈ N.G.edgeFinset ∧ ∃ v ∈ P, v ∈ e) (c : ℕ) (e : Sym2 V) :
    onEdges F c e ≤ c * E.rho N.G j P e := by
  classical
  unfold onEdges Overlays.rho
  split_ifs with h1 h2
  · nlinarith
  · exact absurd (hF e h1) h2
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- **`perCompR` in the CONGEST semantics**, with `K₀ = 60`. -/
theorem perCompR_congest : PerCompRC := by
  refine ⟨60, ?_⟩
  intro A Bt Am B V _ _ _ N E j sz P S z R pm pm' δm δm' p δ hE hj hSP hP hsz hloc hAm1 hAm2 hB
  classical
  have hδm' : 0 ≤ δm' := ImplI.nonneg _ _ hAm2
  have hδK : 0 ≤ ∑ K ∈ comps N.G S, δ K :=
    sum_nonneg (fun K hK => ImplI.nonneg _ _ (hB K hK))
  have hfp : P ⊆ footprint E j P := subset_footprint E j P
  let x0 : Agent V → (Bool × Bool) × A V := fun g => ((memAg P g, memAg S g), z g)
  -- the overhead of the preparation and of the traversal
  set ptc : Prof V := Prof.mk (tcK 0 * (1 + 1) * (sz + 1))
    (onEdges (inducedEdges N.G S) (tcK 0 * (1 + 1))) (tcK 0 * (1 + 1) * (S.card + 1)) with hptc
  set ptr : Prof V := ∑ K ∈ comps N.G S, p K + Prof.mk (30 * (E.dil + 1) * (sz + 1))
    (fun e => 18 * E.rho N.G j P e) (12 * P.card + 6 * E.aggLen j P) with hptr
  set pnt : Prof V := Prof.mk 1 (fun e => 2 * E.rho N.G j P e) (2 * P.card) with hpnt
  have hind : ∀ e, (if e ∈ N.G.edgeFinset ∧ ∃ v ∈ P, v ∈ e then 1 else 0) ≤ E.rho N.G j P e := by
    intro e; unfold Overlays.rho; omega
  refine c_mono (p := pm + (pm' + (ptc + (pnt + (pnt + ptr)))))
    (δ := δm + (δm' + (0 + (0 + (0 + ∑ K ∈ comps N.G S, δ K))))) ?_ ?_ ?_
  · -- phase 1: `Am` on `P`
    refine c_bind (c_callR (pcF1 A) x0 hAm1) (fun y1 hy1 => ?_) (by linarith)
    -- phase 2: `Am` on `S`
    let x1 : Agent V → X1 A V := fun g => (x0 g, y1 g)
    refine c_bind (c_callR (pcF2 A) x1 hAm2) (fun y2 hy2 => ?_) (by linarith)
    -- phase 3: the component sizes
    let x2 : Agent V → X2 A V := fun g => (x1 g, y2 g)
    refine c_bind (c_callR (pcF3 A) x2 (tc_implI hSP hsz x2 (fun v => rfl) hy2))
      (fun y3 hy3 => ?_) (by linarith)
    -- phase 4: the children in the tree of `P`
    let x3 : Agent V → X3 A V := fun g => (x2 g, y3 g)
    let parP : V → Option V := fun v => (y1 (.inl v)).1
    let parS : V → Option V := fun v => (y2 (.inl v)).1
    have hx4 : ∀ v, (pcF4 A).f V (.inl v) (lview N (.inl v)) (x3 (.inl v)) =
        if v ∈ P then optS (parP v) else ∅ := by
      intro v
      by_cases hv : v ∈ P <;> simp [pcF4, x3, x2, x1, x0, memAg, hv, parP]
    have hx5 : ∀ (y4 : Agent V → Finset V) v, (pcF5 A).f V (.inl v) (lview N (.inl v))
        ((x3 (.inl v), y4 (.inl v))) =
        if v ∈ S then optS (parS v) else ∅ := by
      intro y4 v
      by_cases hv : v ∈ S <;> simp [pcF5, x3, x2, x1, x0, memAg, hv, parS]
    have hmatch : ∀ (Q : Finset V) (par : V → Option V) (v u : V),
        u ∈ (if v ∈ Q then optS (par v) else ∅) ↔ v ∈ Q ∧ par v = some u := by
      intro Q par v u
      by_cases hv : v ∈ Q
      · rw [if_pos hv]
        cases par v with
        | none => simp [optS]
        | some w => simp [optS, hv, eq_comm]
      · simp [hv]
    have H4 := Classical.choose_spec notify_congest N E j sz (footprint E j P) P (treeE P parP)
      (fun g => (pcF4 A).f V g (lview N g) (x3 g))
      (fun v u hu => by
        rw [hx4 v, hmatch] at hu
        have he := hy1.edge v hu.1 u hu.2
        rw [memIE] at he
        exact ⟨hu.1, he.1, mem_treeE hu.1 hu.2⟩)
      (fun v u hu => by
        rw [hx4 v, hmatch] at hu
        exact hfp (hy1.mem v hu.1 u hu.2))
      hfp
    refine c_bind (c_callR (pcF4 A) x3 (c_mono H4 ?_ le_rfl)) (fun y4 hy4 => ?_) (by linarith)
    · refine Prof.le_mk _ _ _ _ le_rfl (fun e => ?_) ?_
      · exact onEdges_le_rho (fun e he => treeE_sub (fun v hv u hu => by
          have := hy1.edge v hv u hu; rw [memIE] at this; exact this.1) he) 2 e
      · simp only [Prof.msgs_mk]; have := card_treeE P parP; omega
    -- phase 5: the children in the forest of `S`
    let x4 : Agent V → X4 A V := fun g => (x3 g, y4 g)
    have H5 := Classical.choose_spec notify_congest N E j sz (footprint E j P) S (treeE S parS)
      (fun g => (pcF5 A).f V g (lview N g) (x4 g))
      (fun v u hu => by
        rw [show x4 (.inl v) = (x3 (.inl v), y4 (.inl v)) from rfl, hx5 y4 v, hmatch] at hu
        have he := hy2.edge v hu.1 u hu.2
        rw [memIE] at he
        exact ⟨hu.1, he.1, mem_treeE hu.1 hu.2⟩)
      (fun v u hu => by
        rw [show x4 (.inl v) = (x3 (.inl v), y4 (.inl v)) from rfl, hx5 y4 v, hmatch] at hu
        exact hfp (hSP (hy2.mem v hu.1 u hu.2)))
      (hSP.trans hfp)
    refine c_bind (c_callR (pcF5 A) x4 (c_mono H5 ?_ le_rfl)) (fun y5 hy5 => ?_) (by linarith)
    · refine Prof.le_mk _ _ _ _ le_rfl (fun e => ?_) ?_
      · exact onEdges_le_rho (fun e he => by
          obtain ⟨h1, v, hv, hve⟩ := treeE_sub (fun v hv u hu => by
            have := hy2.edge v hv u hu; rw [memIE] at this; exact this.1) he
          exact ⟨h1, v, hSP hv, hve⟩) 2 e
      · simp only [Prof.msgs_mk]
        have := card_treeE S parS; have := card_le_card hSP; omega
    -- phase 6: the traversal
    have H : TravH A Bt B N E j sz P S z R p δ y1 y2 y3 y4 y5 := {
      hE := hE, hj := hj, SP := hSP, conn := hP, Psz := hsz, loc := hloc, hB := hB,
      h1 := hy1, h2 := hy2, h3 := hy3
      h4 := fun v => by
        rw [hy4 v]
        ext u
        simp only [mem_filter, mem_univ, true_and, mem_kidsOf]
        rw [hx4 u, hmatch]
      h5 := fun v => by
        rw [hy5 v]
        ext u
        simp only [mem_filter, mem_univ, true_and, mem_kidsOf]
        rw [show x4 (.inl u) = (x3 (.inl u), y4 (.inl u)) from rfl, hx5 y4 u, hmatch] }
    exact trav_implI H
  · -- the costs
    have h20 : tcK 0 * (1 + 1) = 20 := rfl
    rw [Prof.le_iff]
    refine ⟨?_, fun e => ?_, ?_⟩
    · simp only [hptc, hpnt, hptr, Prof.rounds_add, Prof.rounds_mk, h20]
      have a1 : sz + 1 ≤ (E.dil + 1) * (sz + 1) := Nat.le_mul_of_pos_left _ (by omega)
      have a2 : (E.dil + 1) * (sz + 1) ≤ (E.dil + 1) ^ 2 * (sz + 1) := by
        rw [pow_two, mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
      have e1 : 30 * (E.dil + 1) * (sz + 1) = 30 * ((E.dil + 1) * (sz + 1)) := by ring
      have e2 : 60 * (E.dil + 1) ^ 2 * (sz + 1) = 60 * ((E.dil + 1) ^ 2 * (sz + 1)) := by ring
      rw [e1, e2]
      omega
    · simp only [hptc, hpnt, hptr, Prof.load_add, Prof.load_mk, Pi.add_apply, h20]
      have := onEdges_le_rho (E := E) (j := j) (P := P) (F := inducedEdges N.G S) (fun e he => by
        induction e using Sym2.ind with
        | _ a b =>
          rw [memIE] at he
          exact ⟨SimpleGraph.mem_edgeFinset.2 he.1, a, hSP he.2.1, Sym2.mem_mk_left _ _⟩) 20 e
      omega
    · simp only [hptc, hpnt, hptr, Prof.msgs_add, Prof.msgs_mk, h20]
      have := card_le_card hSP
      omega
  · -- the failure probability
    linarith

end APSP.Stoc.Congest
