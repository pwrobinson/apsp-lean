import ApspStoc.Congest.TreeCast

/-!
# Auxiliary material for the aggregator exchanges (`AggUpDown.lean`)

* **Walks.** `oth e a` is the other endpoint of the edge `e` seen from `a`; `wv l a i` is the
  `i`-th vertex of the edge walk `l` started at `a`. For an edge walk (`IsEdgeWalk l a b`), the
  `i`-th edge is `s(wv l a i, wv l a (i + 1))` (`walk_get`), the last vertex is `b` (`walk_end`),
  and the reversed list is an edge walk from `b` to `a` (`isEdgeWalk_reverse`).
* **Ranks.** `rkIn s u` is the rank of `u` in the finite set `s` for the fixed enumeration
  `Fintype.equivFin V` of the IDs (known to every node, since every node knows `V`), and
  `pickR s q` the element of rank `q`. Ranks of distinct elements differ and are `< |s|`.
* **Slots.** A round `s` of a schedule with sub-phases of `B = sz * L` rounds and slots of `L`
  rounds decomposes as `s = h * B + q * L + r` (`slot_decomp`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Walks -/

/-- the other endpoint of the edge `e` seen from `a` (`a` itself if `a ∉ e`) -/
def oth (e : Sym2 V) (a : V) : V := if h : a ∈ e then Sym2.Mem.other' h else a

lemma oth_mk (a b : V) : oth s(a, b) a = b := by
  unfold oth
  rw [dite_eq_left (Sym2.mem_mk_left a b)]
  exact Sym2.congr_right.1 (Sym2.other_spec' _)

lemma oth_mk' (a b : V) : oth s(a, b) b = a := by
  rw [Sym2.eq_swap]; exact oth_mk b a

/-- the `i`-th vertex of the edge walk `l` started at `a` -/
def wv : List (Sym2 V) → V → ℕ → V
  | [], a, _ => a
  | _ :: _, a, 0 => a
  | e :: l, a, i + 1 => wv l (oth e a) i

@[simp] lemma wv_zero (l : List (Sym2 V)) (a : V) : wv l a 0 = a := by cases l <;> rfl

lemma wv_cons_succ (e : Sym2 V) (l : List (Sym2 V)) (a : V) (i : ℕ) :
    wv (e :: l) a (i + 1) = wv l (oth e a) i := rfl

/-- The `i`-th edge of an edge walk joins its `i`-th and `(i+1)`-st vertex. -/
lemma walk_get : ∀ (l : List (Sym2 V)) (a b : V), IsEdgeWalk l a b →
    ∀ i (hi : i < l.length), l[i] = s(wv l a i, wv l a (i + 1))
  | [], _, _, _, i, hi => absurd hi (by simp)
  | e :: l, a, b, ⟨x, he, hw⟩, 0, _ => by
      simp only [List.getElem_cons_zero, wv_zero, wv_cons_succ, he, oth_mk]
  | e :: l, a, b, ⟨x, he, hw⟩, i + 1, hi => by
      rw [List.getElem_cons_succ, wv_cons_succ, wv_cons_succ, he, oth_mk]
      exact walk_get l x b hw i (by simp at hi; omega)

/-- The `i`-th edge of an edge walk, as an optional lookup. -/
lemma walk_get? {l : List (Sym2 V)} {a b : V} (hw : IsEdgeWalk l a b) {i : ℕ}
    (hi : i < l.length) : l[i]? = some s(wv l a i, wv l a (i + 1)) := by
  rw [List.getElem?_eq_getElem hi, walk_get l a b hw i hi]

/-- The last vertex of an edge walk is its end. -/
lemma walk_end : ∀ (l : List (Sym2 V)) (a b : V), IsEdgeWalk l a b → wv l a l.length = b
  | [], _, _, h => h
  | e :: l, a, b, ⟨x, he, hw⟩ => by
      rw [List.length_cons, wv_cons_succ, he, oth_mk]
      exact walk_end l x b hw

/-- The end of an edge walk is determined by its start and its edges. -/
lemma walk_end_unique {l : List (Sym2 V)} {a b b' : V} (h : IsEdgeWalk l a b)
    (h' : IsEdgeWalk l a b') : b = b' := by
  rw [← walk_end l a b h, walk_end l a b' h']

lemma isEdgeWalk_append : ∀ (l₁ l₂ : List (Sym2 V)) (a c : V),
    IsEdgeWalk (l₁ ++ l₂) a c ↔ ∃ b, IsEdgeWalk l₁ a b ∧ IsEdgeWalk l₂ b c
  | [], l₂, a, c => by
      simp only [List.nil_append, IsEdgeWalk]
      exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨b, hab, h⟩ => hab ▸ h⟩
  | e :: l₁, l₂, a, c => by
      simp only [List.cons_append, IsEdgeWalk]
      constructor
      · rintro ⟨x, he, h⟩
        obtain ⟨b, h1, h2⟩ := (isEdgeWalk_append l₁ l₂ x c).1 h
        exact ⟨b, ⟨x, he, h1⟩, h2⟩
      · rintro ⟨b, ⟨x, he, h1⟩, h2⟩
        exact ⟨x, he, (isEdgeWalk_append l₁ l₂ x c).2 ⟨b, h1, h2⟩⟩

/-- The reversed edge list of a walk from `a` to `b` is a walk from `b` to `a`. -/
lemma isEdgeWalk_reverse : ∀ (l : List (Sym2 V)) (a b : V), IsEdgeWalk l a b →
    IsEdgeWalk l.reverse b a
  | [], a, b, h => by simp only [List.reverse_nil, IsEdgeWalk] at h ⊢; exact h.symm
  | e :: l, a, b, ⟨x, he, hw⟩ => by
      rw [List.reverse_cons, isEdgeWalk_append]
      refine ⟨x, isEdgeWalk_reverse l x b hw, a, ?_, rfl⟩
      rw [he, Sym2.eq_swap]

/-- Every vertex of a non-empty edge walk lies on one of its edges. -/
lemma wv_mem_edge {l : List (Sym2 V)} {a b : V} (hw : IsEdgeWalk l a b) (hne : l ≠ [])
    {i : ℕ} (hi : i ≤ l.length) : ∃ e ∈ l, wv l a i ∈ e := by
  rcases Nat.lt_or_ge i l.length with h | h
  · refine ⟨l[i], List.getElem_mem h, ?_⟩
    rw [walk_get l a b hw i h]; exact Sym2.mem_mk_left _ _
  · have hl : 0 < l.length := List.length_pos_iff.2 hne
    have hi' : i = l.length - 1 + 1 := by omega
    refine ⟨l[l.length - 1], List.getElem_mem (by omega), ?_⟩
    rw [walk_get l a b hw _ (by omega), ← hi']; exact Sym2.mem_mk_right _ _

/-- number of positions of `e` in a list -/
lemma card_filter_getElem?_eq_count (e : Sym2 V) : ∀ l : List (Sym2 V),
    ((range l.length).filter (fun h => l[h]? = some e)).card = l.count e
  | [] => by simp
  | f :: l => by
      rw [card_filter, List.length_cons, sum_range_succ', List.count_cons]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      rw [← card_filter, card_filter_getElem?_eq_count e l]
      by_cases hf : f = e <;> simp [hf]

/-! ## Ranks -/

/-- the rank of `u` in `s` for the enumeration `Fintype.equivFin V` -/
noncomputable def rkIn (s : Finset V) (u : V) : ℕ :=
  (s.filter (fun w => Fintype.equivFin V w < Fintype.equivFin V u)).card

open Classical in
/-- the element of rank `q` of `s` (if any) -/
noncomputable def pickR (s : Finset V) (q : ℕ) : Option V :=
  if h : ∃ u ∈ s, rkIn s u = q then some h.choose else none

lemma rkIn_lt {s : Finset V} {u : V} (hu : u ∈ s) : rkIn s u < s.card := by
  unfold rkIn
  refine card_lt_card ⟨filter_subset _ _, fun h => ?_⟩
  have := h hu
  simp at this

lemma rkIn_inj {s : Finset V} {u w : V} (hu : u ∈ s) (hw : w ∈ s) (h : rkIn s u = rkIn s w) :
    u = w := by
  by_contra hne
  have hne' : Fintype.equivFin V u ≠ Fintype.equivFin V w :=
    fun h' => hne ((Fintype.equivFin V).injective h')
  have key : ∀ a b, a ∈ s → Fintype.equivFin V a < Fintype.equivFin V b →
      rkIn s a < rkIn s b := by
    intro a b ha hab
    unfold rkIn
    refine card_lt_card ⟨fun c hc => ?_, fun hsub => ?_⟩
    · rw [mem_filter] at hc ⊢; exact ⟨hc.1, lt_trans hc.2 hab⟩
    · have := hsub (mem_filter.2 ⟨ha, hab⟩)
      simp at this
  rcases lt_or_gt_of_ne hne' with h1 | h1
  · have := key u w hu h1; omega
  · have := key w u hw h1; omega

lemma pickR_eq_some {s : Finset V} {q : ℕ} {u : V} :
    pickR s q = some u ↔ u ∈ s ∧ rkIn s u = q := by
  classical
  unfold pickR
  constructor
  · intro h
    split_ifs at h with hex
    cases h
    exact hex.choose_spec
  · rintro ⟨hu, hq⟩
    have hex : ∃ u ∈ s, rkIn s u = q := ⟨u, hu, hq⟩
    rw [dite_eq_left hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    rw [rkIn_inj h1 hu (h2.trans hq.symm)]

lemma pickR_rkIn {s : Finset V} {u : V} (hu : u ∈ s) : pickR s (rkIn s u) = some u :=
  pickR_eq_some.2 ⟨hu, rfl⟩

lemma mem_of_pickR {s : Finset V} {q : ℕ} {u : V} (h : pickR s q = some u) : u ∈ s :=
  (pickR_eq_some.1 h).1

/-! ## Slots -/

/-- Decomposition of a round into sub-phase, slot and position. -/
lemma slot_decomp {h q r sz L : ℕ} (hq : q < sz) (hr : r < L) :
    (h * (sz * L) + q * L + r) / (sz * L) = h ∧
      (h * (sz * L) + q * L + r) % (sz * L) / L = q ∧
      (h * (sz * L) + q * L + r) % (sz * L) % L = r := by
  have hL : 0 < L := by omega
  have hB : q * L + r < sz * L := by
    calc q * L + r < q * L + L := by omega
      _ = (q + 1) * L := by ring
      _ ≤ sz * L := Nat.mul_le_mul_right _ hq
  have h1 : (h * (sz * L) + q * L + r) % (sz * L) = q * L + r := by
    rw [add_assoc, Nat.mul_comm h, Nat.mul_add_mod, Nat.mod_eq_of_lt hB]
  refine ⟨?_, ?_, ?_⟩
  · rw [add_assoc, Nat.mul_comm h, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hB, add_zero]
  · rw [h1, Nat.mul_comm q, Nat.mul_add_div hL, Nat.div_eq_of_lt hr, add_zero]
  · rw [h1, Nat.mul_comm q, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- Every round decomposes into sub-phase, slot and position. -/
lemma slot_recomp (s B L : ℕ) : s = s / B * B + s % B / L * L + s % B % L := by
  have h1 := Nat.div_add_mod s B
  have h2 := Nat.div_add_mod (s % B) L
  rw [Nat.mul_comm] at h1 h2
  omega

lemma slot_q_lt {s sz L : ℕ} : s % (sz * L) / L < sz ∨ sz * L = 0 := by
  rcases Nat.eq_zero_or_pos (sz * L) with h | h
  · right; exact h
  · left
    have hL : 0 < L := Nat.pos_of_mul_pos_left h
    rw [Nat.div_lt_iff_lt_mul hL]
    exact Nat.mod_lt _ h

end APSP.Stoc.Congest
