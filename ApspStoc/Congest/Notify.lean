import ApspStoc.Congest.Tasks

/-!
# Notification in one round

The concrete CONGEST version of the toolkit field `notify`: every node `v` sends the word `num 0`
to each `u ∈ x v` (a set of `F`-neighbours, which are neighbours in the instance, so the sends are
proper), and at the end of round `0 → 1` every node records the set of nodes it heard from and
halts.
-/

namespace APSP.Stoc.Congest

open APSP Finset

/-- Local state of the notification protocol: own identifier, the nodes to notify, and (once
halted) the set of senders. -/
structure NotifyS (V : Type) : Type 1 where
  me : V
  tgt : Finset V
  rcv : Option (Finset V)

open Classical in
/-- The nodes to notify, read from the node's own data (`∅` if it has the wrong type). -/
noncomputable def notifyTgt {V : Type} (me : V) (inp : Agent V → Option Mem) : Finset V :=
  match inp (.inl me) with
  | some m => if h : m.1 = Finset V then cast h m.2 else ∅
  | none => ∅

/-- The one-round notification protocol. -/
noncomputable def notifyP (V : Type) [Fintype V] [DecidableEq V] : Proto V where
  S := NotifyS V
  Ω := Unit
  init c inp _ := ⟨c.me, notifyTgt c.me inp, none⟩
  send _ s u := if u ∈ s.tgt then some (.num 0) else none
  recv _ s m := ⟨s.me, s.tgt, some (univ.filter (fun u => (m u).isSome))⟩
  out s := s.rcv.map (fun r g => some (if g = .inl s.me then ⟨Finset V, r⟩ else ⟨Finset V, ∅⟩))

section

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- At most two directed pairs give the same undirected edge. -/
lemma notify_card_filter_sym2_le_two (D : Finset (V × V)) (e : Sym2 V) :
    (D.filter (fun uv => s(uv.1, uv.2) = e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    calc (D.filter (fun uv => s(uv.1, uv.2) = s(a, b))).card ≤ ({(a, b), (b, a)} : Finset _).card := by
          apply card_le_card
          intro uv huv
          obtain ⟨u, v⟩ := uv
          simp only [mem_filter, Sym2.eq_iff] at huv
          rcases huv.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      _ ≤ 2 := card_le_two

lemma notify_st0 (N : WNet V) (E : Overlays V) (j sz : ℕ) (Pt : Finset V)
    (x : Agent V → Finset V) (hx0 : ∀ v, v ∉ Pt → x (.inl v) = ∅) (ω : V → (notifyP V).Ω) :
    st (notifyP V) (ioInst N E j sz Pt) (inOf x) ω 0 = fun v => ⟨v, x (.inl v), none⟩ := by
  funext v
  show (⟨v, notifyTgt v (inpAt (ioInst N E j sz Pt) (inOf x) v), none⟩ : NotifyS V) = _
  by_cases hv : v ∈ Pt
  · have h : inpAt (ioInst N E j sz Pt) (inOf x) v (.inl v) = some ⟨Finset V, x (.inl v)⟩ := by
      simp [inpAt, ioInst, ioHost, inOf, hv]
    simp only [notifyTgt, h]
    rfl
  · have h : inpAt (ioInst N E j sz Pt) (inOf x) v (.inl v) = none := by
      simp [inpAt, ioInst, ioHost, hv]
    simp only [notifyTgt, h, hx0 v hv]

lemma notify_msg0 (N : WNet V) (E : Overlays V) (j sz : ℕ) (Pt S : Finset V)
    (F : Finset (Sym2 V)) (x : Agent V → Finset V)
    (hx : ∀ v, ∀ u ∈ x (.inl v), v ∈ S ∧ N.G.Adj v u ∧ s(v, u) ∈ F)
    (hxPt : ∀ v, ∀ u ∈ x (.inl v), u ∈ Pt) (hS : S ⊆ Pt) (ω : V → (notifyP V).Ω) (u v : V) :
    (msg (notifyP V) (ioInst N E j sz Pt) (st (notifyP V) (ioInst N E j sz Pt) (inOf x) ω 0) u v).isSome
      ↔ v ∈ x (.inl u) := by
  have hx0 : ∀ v, v ∉ Pt → x (.inl v) = ∅ := fun v hv =>
    eq_empty_of_forall_notMem fun u hu => hv (hS (hx v u hu).1)
  rw [notify_st0 N E j sz Pt x hx0]
  by_cases hv : v ∈ x (.inl u)
  · have hadj : (ioG N Pt).Adj u v := ⟨(hx u v hv).2.1, hS (hx u v hv).1, hxPt u v hv⟩
    have hw : WordOK (Fintype.card V) (Word.num 0 : Word V) := by
      show 0 ≤ Fintype.card V + 3; omega
    simp only [msg, notifyP, ioInst, hv, iff_true]
    simp [hadj, hw]
  · simp only [msg, notifyP, ioInst, hv, iff_false]
    split_ifs <;> first | contradiction | simp

end

/-- **Notification** in the concrete CONGEST semantics. -/
theorem notify_congest : ∃ A : CAlg, ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V)
    (E : Overlays V) (j sz : ℕ) (Pt S : Finset V) (F : Finset (Sym2 V)) (x : Agent V → Finset V),
    (∀ v, ∀ u ∈ x (.inl v), v ∈ S ∧ N.G.Adj v u ∧ s(v, u) ∈ F) →
    (∀ v, ∀ u ∈ x (.inl v), u ∈ Pt) → S ⊆ Pt →
    CImplT A N (.io E j sz Pt (Finset V) (Finset V) x
      (fun y => ∀ v, y (.inl v) = univ.filter (fun u => v ∈ x (.inl u))))
      (Prof.mk 1 (onEdges F 2) (2 * F.card)) 0 := by
  refine ⟨fun V _ _ => notifyP V, ?_⟩
  intro V _ _ N E j sz Pt S F x hx hxPt hS
  show ImplI (notifyP V) (ioInst N E j sz Pt) (inOf x) _ _ 0
  refine ImplI.of_forall _ _ le_rfl (fun ω => ?_)
  have hx0 : ∀ v, v ∉ Pt → x (.inl v) = ∅ := fun v hv =>
    eq_empty_of_forall_notMem fun u hu => hv (hS (hx v u hu).1)
  have h0 := notify_st0 N E j sz Pt x hx0 ω
  have hm := notify_msg0 N E j sz Pt S F x hx hxPt hS ω
  have h1 : st (notifyP V) (ioInst N E j sz Pt) (inOf x) ω 1 =
      fun v => ⟨v, x (.inl v), some (univ.filter (fun u => v ∈ x (.inl u)))⟩ := by
    funext v
    rw [st_succ]
    have hn : ¬ ((notifyP V).out (st (notifyP V) (ioInst N E j sz Pt) (inOf x) ω 0 v)).isSome := by
      rw [h0]; simp [notifyP]
    simp only [step, hn, Bool.false_eq_true, ↓reduceIte]
    show (⟨_, _, some (univ.filter fun u => (msg (notifyP V) (ioInst N E j sz Pt)
      (st (notifyP V) (ioInst N E j sz Pt) (inOf x) ω 0) u v).isSome)⟩ : NotifyS V) = _
    simp only [hm]
    rw [h0]
  have hD : ∀ uv ∈ sentSet (notifyP V) (ioInst N E j sz Pt)
      (st (notifyP V) (ioInst N E j sz Pt) (inOf x) ω 0), s(uv.1, uv.2) ∈ F := by
    intro uv huv
    simp only [sentSet, mem_filter, mem_univ, true_and, hm] at huv
    exact (hx _ _ huv).2.2
  refine ⟨1, ⟨fun v _ => by rw [h1]; rfl, fun s hs v _ => ?_⟩, ?_, le_rfl, ?_, fun e => ?_, ?_⟩
  · obtain rfl : s = 0 := by omega
    rw [h0]; rfl
  · -- proper sends: only to the targets, which are neighbours in the instance
    intro s hs u _ _ v hv
    obtain rfl : s = 0 := by omega
    rw [h0] at hv
    have hvx : v ∈ x (.inl u) := by
      by_contra h
      simp [notifyP, h] at hv
    exact (show (ioG N Pt).Adj u v from ⟨(hx u v hvx).2.1, hS (hx u v hvx).1, hxPt u v hvx⟩)
  · simp only [msgsUpTo, sum_range_one, Prof.msgs_mk]
    exact card_le_mul_card_image_of_maps_to hD 2 (fun e _ => notify_card_filter_sym2_le_two _ e)
  · simp only [loadUpTo, sum_range_one, Prof.load_mk, onEdges]
    split_ifs with he
    · exact notify_card_filter_sym2_le_two _ e
    · refine Nat.le_zero.2 (card_eq_zero.2 (filter_eq_empty_iff.2 fun uv huv heq => he ?_))
      rw [← heq]; exact hD uv huv
  · refine ⟨fun g => match g with
      | .inl v => ⟨Finset V, univ.filter (fun u => v ∈ x (.inl u))⟩
      | .inr _ => ⟨Finset V, ∅⟩, fun g hg => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hg
      unfold outAt
      rw [hw]
      dsimp only
      rw [h1]
      cases g with
      | inl v =>
        have hwv : w = v := by
          have hw' : ioHost E j Pt (.inl v) = some w := hw
          simp only [ioHost] at hw'
          split_ifs at hw' with hv
          exact (Option.some.inj hw').symm
        subst hwv
        simp [notifyP]
      | inr C => simp [notifyP]
    · exact ⟨fun g => match g with
        | .inl v => univ.filter (fun u => v ∈ x (.inl u))
        | .inr _ => ∅, fun g _ => by cases g <;> rfl, fun v => rfl⟩

end APSP.Stoc.Congest
