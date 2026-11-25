import ApspStoc.Congest.TreeCastAux

/-!
# The depth-first traversal of a rooted tree (for `perCompR`)

The traversal of the tree of `P` by a token is the list of *segments* `segs v`: entering the
subtree of `v` (from its parent), the token first starts the phase of `v` if `v` is a leader
(`ph v`), then for every child `c` (in the order of `(kidsOf …).toList`) it moves to `c`
(`tk v c`), traverses the subtree of `c`, and comes back (`tk c v`).

The local rule of a node (`nxt`): after receiving the token from its parent, a node starts its
phase if it is a leader, otherwise it sends the token to its first child (or back to its parent);
after its phase, it sends the token to its first child (or back); after receiving the token from
child `c`, it sends it to the child after `c` (`nextIn`), or back to its parent. The root has no
parent: "back" means the end of the traversal.

* `segs_chain`: consecutive segments follow the local rule (`List.IsChain`), the first segment
  is the start of the subtree and the last one leads back to the parent;
* `mem_segs`, `segs_nodup`: the segments of `segs v` are the phases of the leaders of the subtree
  and the two moves over every tree edge of the subtree, each exactly once.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

/-- a segment of the traversal: a token move, or the phase of a leader -/
inductive TSg (V : Type) where
  | tk (u w : V)
  | ph (l : V)
  deriving DecidableEq

/-- the element after `c` in a list -/
def nextIn {V : Type} [DecidableEq V] : List V → V → Option V
  | a :: b :: l, c => if a = c then some b else nextIn (b :: l) c
  | _, _ => none

/-- the node holding the token at the end of a segment -/
def TSg.tgt {V : Type} : TSg V → V
  | .tk _ w => w
  | .ph l => l

section NextIn
variable {V : Type} [DecidableEq V]

lemma nextIn_mid : ∀ (pre : List V) (c c' : V) (rest : List V),
    (pre ++ c :: c' :: rest).Nodup → nextIn (pre ++ c :: c' :: rest) c = some c'
  | [], c, c', rest, _ => by simp [nextIn]
  | a :: pre, c, c', rest, hnd => by
    have hac : a ≠ c := by
      intro h; subst h
      simp at hnd
    have ih := nextIn_mid pre c c' rest (List.nodup_cons.1 hnd).2
    obtain ⟨b, l, hbl⟩ : ∃ b l, pre ++ c :: c' :: rest = b :: l := by
      cases pre <;> simp
    rw [List.cons_append, hbl]
    show (if a = c then some b else nextIn (b :: l) c) = some c'
    rw [if_neg hac, ← hbl]
    exact ih

lemma nextIn_last : ∀ (pre : List V) (c : V), (pre ++ [c]).Nodup → nextIn (pre ++ [c]) c = none
  | [], c, _ => by simp [nextIn]
  | a :: pre, c, hnd => by
    have hac : a ≠ c := by
      intro h; subst h
      simp at hnd
    have ih := nextIn_last pre c (List.nodup_cons.1 hnd).2
    obtain ⟨b, l, hbl⟩ : ∃ b l, pre ++ [c] = b :: l := by
      cases pre <;> simp
    rw [List.cons_append, hbl]
    show (if a = c then some b else nextIn (b :: l) c) = none
    rw [if_neg hac, ← hbl]
    exact ih

end NextIn

variable {V : Type} [Fintype V] [DecidableEq V] (Pp : Finset V) (par : V → Option V)
  (rk : V → ℕ) (isL : V → Bool)

/-- The segments of the traversal of the subtree of `v`. -/
noncomputable def segs (v : V) : List (TSg V) :=
  (if isL v then [TSg.ph v] else []) ++
    (kidsOf Pp par v).toList.flatMap (fun c =>
      if _h : mu Pp rk c < mu Pp rk v then [TSg.tk v c] ++ segs c ++ [TSg.tk c v] else [])
termination_by mu Pp rk v

/-- the children of `v`, in traversal order -/
noncomputable def kl (v : V) : List V := (kidsOf Pp par v).toList

/-- the move back to the parent (`none` at the root: the end) -/
def upA (v : V) : Option (TSg V) := (par v).map (TSg.tk v)

/-- the move after the token arrived from the parent (or after the phase) -/
noncomputable def aParA (v : V) : Option (TSg V) :=
  match (kl Pp par v).head? with
  | some c => some (TSg.tk v c)
  | none => upA par v

/-- the move after the token came back from child `c` -/
noncomputable def aKidA (v c : V) : Option (TSg V) :=
  match nextIn (kl Pp par v) c with
  | some c' => some (TSg.tk v c')
  | none => upA par v

/-- **The local rule**: the segment after a segment. -/
noncomputable def nxt : TSg V → Option (TSg V)
  | .tk u v => if par v = some u then (if isL v then some (.ph v) else aParA Pp par v)
      else aKidA Pp par v u
  | .ph v => aParA Pp par v

/-- the first segment of the subtree of `v` -/
noncomputable def startA (v : V) : Option (TSg V) :=
  if isL v then some (.ph v) else aParA Pp par v

variable {Pp par rk isL}

section Props

variable (hS : ∀ v ∈ Pp, ∀ u, par v = some u → u ∈ Pp)
  (hrk : ∀ v ∈ Pp, ∀ u, par v = some u → rk u < rk v)

/-- the block of a child -/
noncomputable def blk (Pp : Finset V) (par : V → Option V) (rk : V → ℕ) (isL : V → Bool)
    (v c : V) : List (TSg V) := [TSg.tk v c] ++ segs Pp par rk isL c ++ [TSg.tk c v]

include hrk in
lemma segs_eq (v : V) : segs Pp par rk isL v =
    (if isL v then [TSg.ph v] else []) ++ (kl Pp par v).flatMap (blk Pp par rk isL v) := by
  rw [segs]
  congr 1
  simp only [List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [dif_pos (mu_lt hrk (Finset.mem_toList.1 hc))]
  rfl

include hrk in
lemma par_ne_kid {v c : V} (hv : v ∈ Pp) (hc : c ∈ kidsOf Pp par v) : par v ≠ some c := by
  intro h
  rw [mem_kidsOf] at hc
  have h1 := hrk c hc.1 v hc.2
  have h2 := hrk v hv c h
  omega

lemma kl_nodup (v : V) : (kl Pp par v).Nodup := Finset.nodup_toList _

/-- the properties of the traversal of a subtree -/
structure SegOK (v : V) : Prop where
  chain : List.IsChain (fun a b => nxt Pp par isL a = some b) (segs Pp par rk isL v)
  head : (segs Pp par rk isL v).head? = startA Pp par isL v ∨
    (segs Pp par rk isL v = [] ∧ startA Pp par isL v = upA par v)
  last : ∀ z ∈ (segs Pp par rk isL v).getLast?, nxt Pp par isL z = upA par v

lemma head_blocks (v : V) : ∀ l : List V,
    (l.flatMap (blk Pp par rk isL v)).head? = l.head?.map (TSg.tk v)
  | [] => rfl
  | c :: l => by simp [blk]

lemma getLast_blk (v c : V) : (blk Pp par rk isL v c).getLast? = some (TSg.tk c v) := by
  unfold blk
  rw [List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

lemma getLast_blocks (v : V) (l : List V) (z : TSg V)
    (hz : z ∈ (l.flatMap (blk Pp par rk isL v)).getLast?) : ∃ c ∈ l.getLast?, z = TSg.tk c v := by
  rcases l.eq_nil_or_concat with rfl | ⟨l', c', rfl⟩
  · simp at hz
  · rw [List.concat_eq_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.getLast?_append_of_ne_nil _ (by simp [blk]), getLast_blk] at hz
    refine ⟨c', by simp, ?_⟩
    simp only [Option.mem_def, Option.some.injEq] at hz
    exact hz.symm

include hS hrk in
/-- **The traversal follows the local rule.** -/
theorem segOK (v : V) : v ∈ Pp → SegOK (Pp := Pp) (par := par) (rk := rk) (isL := isL) v := by
  induction v using kid_induction hrk with
  | _ v ih =>
    intro hv
    -- the blocks of the children
    have hblk : ∀ c ∈ kidsOf Pp par v,
        List.IsChain (fun a b => nxt Pp par isL a = some b) (blk Pp par rk isL v c) := by
      intro c hc
      have hcS := (mem_kidsOf.1 hc).1
      have hcp := (mem_kidsOf.1 hc).2
      obtain ⟨hch, hhd, hlst⟩ := ih c hc hcS
      unfold blk
      have hup : upA par c = some (TSg.tk c v) := by simp [upA, hcp]
      have hfst : nxt Pp par isL (TSg.tk v c) = startA Pp par isL c := by
        simp only [nxt]
        rw [if_pos hcp]
        rfl
      rcases hhd with hhd | ⟨hnil, hst⟩
      · rcases hnil' : segs Pp par rk isL c with _ | ⟨a, l⟩
        · rw [hnil'] at hhd
          have : (startA Pp par isL c).isSome := by
            unfold startA aParA
            split
            · rfl
            · split
              · rfl
              · simp [upA, hcp]
          rw [← hhd] at this
          simp at this
        · rw [hnil'] at hhd hch hlst
          refine List.IsChain.append (List.IsChain.append (List.isChain_singleton _) hch ?_)
            (List.isChain_singleton _) ?_
          · intro x hx y hy
            simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            subst hx; subst hy
            rw [hfst, ← hhd]; rfl
          · intro x hx y hy
            simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hy
            subst hy
            have hx' : x ∈ (a :: l).getLast? := by
              rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil a l)] at hx
              exact hx
            rw [hlst x hx', hup]
      · rw [hnil]
        simp only [List.append_nil, List.singleton_append]
        refine List.isChain_pair.2 ?_
        rw [hfst, hst, hup]
    have hchain : List.IsChain (fun a b => nxt Pp par isL a = some b)
        ((kl Pp par v).flatMap (blk Pp par rk isL v)) := by
      have key : ∀ (pre l : List V), pre ++ l = kl Pp par v →
          List.IsChain (fun a b => nxt Pp par isL a = some b) (l.flatMap (blk Pp par rk isL v)) := by
        intro pre l
        induction l generalizing pre with
        | nil => intro _; exact List.isChain_nil
        | cons c l ihl =>
          intro hpre
          have hcmem : c ∈ kidsOf Pp par v := by
            rw [← Finset.mem_toList, ← kl, ← hpre]; simp
          rw [List.flatMap_cons]
          refine List.IsChain.append (hblk c hcmem) (ihl (pre ++ [c]) (by simpa using hpre)) ?_
          intro x hx y hy
          simp only [blk, List.getLast?_append, List.getLast?_singleton, Option.some_or,
            Option.mem_def, Option.some.injEq] at hx
          subst hx
          rw [head_blocks] at hy
          cases l with
          | nil => simp at hy
          | cons c' l =>
            simp only [List.head?_cons, Option.map_some, Option.mem_def,
              Option.some.injEq] at hy
            subst hy
            have hnd := kl_nodup (Pp := Pp) (par := par) v
            rw [← hpre] at hnd
            have := nextIn_mid pre c c' l hnd
            show (if par v = some c then _ else _) = _
            rw [if_neg (par_ne_kid hrk hv hcmem)]
            unfold aKidA
            rw [← hpre, this]
      exact key [] _ rfl
    have hlastb : ∀ z ∈ ((kl Pp par v).flatMap (blk Pp par rk isL v)).getLast?,
        nxt Pp par isL z = upA par v := by
      intro z hz
      obtain ⟨c, hc, rfl⟩ := getLast_blocks v _ z hz
      have hcmem : c ∈ kidsOf Pp par v := by
        rw [← Finset.mem_toList, ← kl]; exact List.mem_of_getLast? hc
      obtain ⟨pre, hpre⟩ : ∃ pre, kl Pp par v = pre ++ [c] := by
        rcases (kl Pp par v).eq_nil_or_concat with h | ⟨l', c', h⟩
        · rw [h] at hc; simp at hc
        · rw [h, List.concat_eq_append] at hc; simp at hc; subst hc
          exact ⟨l', by rw [h, List.concat_eq_append]⟩
      have hnd := kl_nodup (Pp := Pp) (par := par) v
      rw [hpre] at hnd
      show (if par v = some c then _ else _) = _
      rw [if_neg (par_ne_kid hrk hv hcmem)]
      unfold aKidA
      rw [hpre, nextIn_last pre c hnd]
    have hseq := segs_eq (isL := isL) hrk v
    have hgoal : SegOK (Pp := Pp) (par := par) (rk := rk) (isL := isL) v ↔
        (List.IsChain (fun a b => nxt Pp par isL a = some b)
          ((if isL v then [TSg.ph v] else []) ++ (kl Pp par v).flatMap (blk Pp par rk isL v)) ∧
        ((((if isL v then [TSg.ph v] else []) ++
            (kl Pp par v).flatMap (blk Pp par rk isL v)).head? = startA Pp par isL v ∨
          ((if isL v then [TSg.ph v] else []) ++ (kl Pp par v).flatMap (blk Pp par rk isL v) = [] ∧
            startA Pp par isL v = upA par v)) ∧
        ∀ z ∈ ((if isL v then [TSg.ph v] else []) ++
          (kl Pp par v).flatMap (blk Pp par rk isL v)).getLast?, nxt Pp par isL z = upA par v)) := by
      rw [← hseq]
      exact ⟨fun h => ⟨h.chain, h.head, h.last⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
    rw [hgoal]
    refine ⟨?_, ?_, ?_⟩
    · by_cases hL : isL v = true
      · rw [if_pos hL]
        refine List.IsChain.append (List.isChain_singleton _) hchain ?_
        intro x hx y hy
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        subst hx
        rw [head_blocks] at hy
        cases hk : kl Pp par v with
        | nil => rw [hk] at hy; simp at hy
        | cons c l =>
          rw [hk] at hy
          simp only [List.head?_cons, Option.map_some, Option.mem_def, Option.some.injEq] at hy
          subst hy
          simp [nxt, aParA, hk]
      · rw [if_neg hL]
        simpa using hchain
    · by_cases hL : isL v = true
      · left
        rw [if_pos hL]
        simp [startA, hL]
      · rw [if_neg hL, List.nil_append, head_blocks]
        cases hk : kl Pp par v with
        | nil =>
          right
          simp [startA, hL, aParA, hk]
        | cons c l =>
          left
          simp [startA, hL, aParA, hk]
    · intro z hz
      by_cases hL : isL v = true
      · rw [if_pos hL] at hz
        cases hk : kl Pp par v with
        | nil =>
          rw [hk] at hz
          simp at hz
          subst hz
          simp [nxt, aParA, hk]
        | cons c l =>
          rw [List.getLast?_append_of_ne_nil] at hz
          · exact hlastb z hz
          · rw [hk]; simp [blk]
      · rw [if_neg hL, List.nil_append] at hz
        exact hlastb z hz

/-! ### The segments of a subtree -/

/-- the node of a segment that is not the parent of the other one -/
def TSg.low (par : V → Option V) : TSg V → V
  | .tk a b => if par b = some a then b else a
  | .ph w => w

include hS in
lemma desc_kid_mem {a b u : V} (ha : a ∈ desc Pp par u) (hb : b ∈ Pp) (hba : par b = some a) :
    b ∈ desc Pp par u := by
  rw [mem_desc] at ha ⊢
  exact ⟨hb, ReflTransGen.head hba ha.2⟩

include hS hrk in
/-- **The segments of a subtree**: the phases of its leaders, and the moves over its tree edges
(in both directions). -/
lemma mem_segs (v : V) : v ∈ Pp → ∀ x : TSg V, x ∈ segs Pp par rk isL v ↔
    (∃ w, x = .ph w ∧ isL w = true ∧ w ∈ desc Pp par v) ∨
    (∃ a b, x = .tk a b ∧ ((b ∈ Pp ∧ par b = some a ∧ a ∈ desc Pp par v) ∨
      (a ∈ Pp ∧ par a = some b ∧ b ∈ desc Pp par v))) := by
  induction v using kid_induction hrk with
  | _ v ih =>
    intro hv x
    rw [segs_eq hrk, List.mem_append, List.mem_flatMap]
    have hd := desc_eq hS hrk hv
    constructor
    · rintro (hx | ⟨c, hc, hx⟩)
      · split_ifs at hx with hL
        · simp only [List.mem_singleton] at hx
          subst hx
          exact Or.inl ⟨v, rfl, hL, by rw [hd]; exact mem_insert_self _ _⟩
        · simp at hx
      · have hc' : c ∈ kidsOf Pp par v := Finset.mem_toList.1 hc
        have hcS := (mem_kidsOf.1 hc').1
        have hcp := (mem_kidsOf.1 hc').2
        have hsub : desc Pp par c ⊆ desc Pp par v := by
          intro w hw; rw [hd]; exact mem_insert_of_mem (mem_biUnion.2 ⟨c, hc', hw⟩)
        have hvd : v ∈ desc Pp par v := by rw [hd]; exact mem_insert_self _ _
        simp only [blk, List.mem_append, List.mem_singleton] at hx
        rcases hx with (rfl | hx) | rfl
        · exact Or.inr ⟨v, c, rfl, Or.inl ⟨hcS, hcp, hvd⟩⟩
        · rcases (ih c hc' hcS x).1 hx with ⟨w, rfl, hL, hw⟩ | ⟨a, b, rfl, h1 | h1⟩
          · exact Or.inl ⟨w, rfl, hL, hsub hw⟩
          · exact Or.inr ⟨a, b, rfl, Or.inl ⟨h1.1, h1.2.1, hsub h1.2.2⟩⟩
          · exact Or.inr ⟨a, b, rfl, Or.inr ⟨h1.1, h1.2.1, hsub h1.2.2⟩⟩
        · exact Or.inr ⟨c, v, rfl, Or.inr ⟨hcS, hcp, hvd⟩⟩
    · rintro (⟨w, rfl, hL, hw⟩ | ⟨a, b, rfl, h1 | h1⟩)
      · rw [hd, mem_insert, mem_biUnion] at hw
        rcases hw with rfl | ⟨c, hc, hw⟩
        · left; rw [if_pos hL]; simp
        · right
          refine ⟨c, Finset.mem_toList.2 hc, ?_⟩
          simp only [blk, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inr ((ih c hc (mem_kidsOf.1 hc).1 _).2 (Or.inl ⟨w, rfl, hL, hw⟩)))
      · obtain ⟨hb, hba, ha⟩ := h1
        rw [hd, mem_insert, mem_biUnion] at ha
        rcases ha with rfl | ⟨c, hc, ha⟩
        · right
          refine ⟨b, Finset.mem_toList.2 (mem_kidsOf.2 ⟨hb, hba⟩), ?_⟩
          simp [blk]
        · right
          refine ⟨c, Finset.mem_toList.2 hc, ?_⟩
          simp only [blk, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inr ((ih c hc (mem_kidsOf.1 hc).1 _).2
            (Or.inr ⟨a, b, rfl, Or.inl ⟨hb, hba, ha⟩⟩)))
      · obtain ⟨ha, hab, hb⟩ := h1
        rw [hd, mem_insert, mem_biUnion] at hb
        rcases hb with rfl | ⟨c, hc, hb⟩
        · right
          refine ⟨a, Finset.mem_toList.2 (mem_kidsOf.2 ⟨ha, hab⟩), ?_⟩
          simp [blk]
        · right
          refine ⟨c, Finset.mem_toList.2 hc, ?_⟩
          simp only [blk, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inr ((ih c hc (mem_kidsOf.1 hc).1 _).2
            (Or.inr ⟨a, b, rfl, Or.inr ⟨ha, hab, hb⟩⟩)))

include hS hrk in
lemma low_mem {v : V} (hv : v ∈ Pp) {x : TSg V} (hx : x ∈ segs Pp par rk isL v) :
    x.low par ∈ desc Pp par v := by
  rcases (mem_segs hS hrk v hv x).1 hx with ⟨w, rfl, -, hw⟩ | ⟨a, b, rfl, h1 | h1⟩
  · exact hw
  · rw [TSg.low, if_pos h1.2.1]
    exact desc_kid_mem hS h1.2.2 h1.1 h1.2.1
  · have hne : par b ≠ some a := by
      intro h
      have hbS := hS a h1.1 b h1.2.1
      have := hrk a h1.1 b h1.2.1
      have := hrk b hbS a h
      omega
    rw [TSg.low, if_neg hne]
    exact desc_kid_mem hS h1.2.2 h1.1 h1.2.1

include hS hrk in
/-- Every segment occurs at most once. -/
lemma segs_nodup (v : V) : v ∈ Pp → (segs Pp par rk isL v).Nodup := by
  induction v using kid_induction hrk with
  | _ v ih =>
    intro hv
    rw [segs_eq hrk, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · split_ifs <;> simp
    · rw [List.nodup_flatMap]
      refine ⟨fun c hc => ?_, ?_⟩
      · have hc' : c ∈ kidsOf Pp par v := Finset.mem_toList.1 hc
        have hcS := (mem_kidsOf.1 hc').1
        have hcp := (mem_kidsOf.1 hc').2
        have hvc : v ∉ desc Pp par c := not_mem_desc_kid hS hrk hc'
        have hpv : par v ≠ some c := par_ne_kid hrk hv hc'
        have hcv : v ≠ c := fun h => by subst h; exact hvc (by rw [mem_desc]; exact ⟨hcS, .refl⟩)
        have h1 : TSg.tk v c ∉ segs Pp par rk isL c := by
          intro h
          rcases (mem_segs hS hrk c hcS _).1 h with ⟨w, hw, -⟩ | ⟨a, b, hab, h2 | h2⟩
          · cases hw
          · cases hab; exact hvc h2.2.2
          · cases hab; exact hpv h2.2.1
        have h2 : TSg.tk c v ∉ segs Pp par rk isL c := by
          intro h
          rcases (mem_segs hS hrk c hcS _).1 h with ⟨w, hw, -⟩ | ⟨a, b, hab, h2 | h2⟩
          · cases hw
          · cases hab; exact hpv h2.2.1
          · cases hab; exact hvc h2.2.2
        unfold blk
        rw [List.nodup_append, List.nodup_append]
        refine ⟨⟨by simp, ih c hc' hcS, ?_⟩, by simp, ?_⟩
        · intro a ha b hb hab; simp at ha; subst ha; subst hab; exact h1 hb
        · intro a ha b hb hab
          simp at hb; subst hb; subst hab
          simp only [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | ha
          · cases ha; exact hcv rfl
          · exact h2 ha
      · refine List.Pairwise.imp_of_mem (R := fun a b => a ≠ b) ?_ (kl_nodup v)
        intro c c' hc hc' hne
        rw [Function.onFun, List.disjoint_left]
        intro x hx hx'
        have hcK : c ∈ kidsOf Pp par v := Finset.mem_toList.1 hc
        have hcK' : c' ∈ kidsOf Pp par v := Finset.mem_toList.1 hc'
        have hlow : ∀ d ∈ kidsOf Pp par v, x ∈ blk Pp par rk isL v d → x.low par ∈ desc Pp par d := by
          intro d hd hxd
          have hdS := (mem_kidsOf.1 hd).1
          have hdp := (mem_kidsOf.1 hd).2
          simp only [blk, List.mem_append, List.mem_singleton] at hxd
          rcases hxd with (rfl | hxd) | rfl
          · rw [TSg.low, if_pos hdp, mem_desc]; exact ⟨hdS, .refl⟩
          · exact low_mem hS hrk hdS hxd
          · rw [TSg.low, if_neg (par_ne_kid hrk hv hd), mem_desc]; exact ⟨hdS, .refl⟩
        have := desc_disj hS hrk v (mem_coe.2 hcK) (mem_coe.2 hcK') hne
        exact Finset.disjoint_left.1 this (hlow c hcK hx) (hlow c' hcK' hx')
    · intro a ha b hb hab
      split_ifs at ha with hL
      · simp at ha; subst ha; subst hab
        obtain ⟨c, hc, hb⟩ := List.mem_flatMap.1 hb
        have hc' : c ∈ kidsOf Pp par v := Finset.mem_toList.1 hc
        have hcS := (mem_kidsOf.1 hc').1
        simp only [blk, List.mem_append, List.mem_singleton] at hb
        rcases hb with (hb | hb) | hb
        · cases hb
        · have := low_mem hS hrk hcS hb
          exact not_mem_desc_kid hS hrk hc' this
        · cases hb
      · simp at ha

end Props

end APSP.Stoc.Congest
