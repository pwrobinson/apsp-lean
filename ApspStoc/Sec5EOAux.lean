import ApspStoc.Statements

/-!
# Combinatorics of the proof of Lemma 5.3 (physical case)

* `exists_pairing`: the edges at a node can be paired, leaving at most one edge (exactly one iff
  their number is odd).
* `dart_orient`: the pairings at the nodes of a cluster decompose its edges into closed trails and
  segments (trails between two left-over edges). There is a choice `o` of the other end of every
  segment, and whenever the directions prescribed at the two ends of every segment are opposite,
  there is a consistent orientation (a colouring of the darts: `true` = the edge leaves the node).
-/

namespace APSP.Stoc

open APSP Finset

/-! ## Pairings -/

theorem exists_pairing {α : Type*} [DecidableEq α] (s : Finset α) :
    ∃ σ : α → α, (∀ a ∈ s, σ a ∈ s ∧ σ (σ a) = a) ∧
      (∀ a ∈ s, ∀ b ∈ s, σ a = a → σ b = b → a = b) ∧
      (Even s.card ↔ ∀ a ∈ s, σ a ≠ a) := by
  suffices H : ∀ n (s : Finset α), s.card = n → ∃ σ : α → α, (∀ a ∈ s, σ a ∈ s ∧ σ (σ a) = a) ∧
      (∀ a ∈ s, ∀ b ∈ s, σ a = a → σ b = b → a = b) ∧
      (Even s.card ↔ ∀ a ∈ s, σ a ≠ a) from H _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn
  by_cases h2 : s.card ≤ 1
  · refine ⟨id, fun a ha => ⟨ha, rfl⟩, fun a ha b hb _ _ => Finset.card_le_one.1 h2 a ha b hb, ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h0 | h1
    · rw [h0]; simp [Finset.card_eq_zero.1 h0]
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
      simp
  · push_neg at h2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
    have hbs : b ∈ s.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hb⟩
    have hc : ((s.erase a).erase b).card = n - 2 := by
      rw [Finset.card_erase_of_mem hbs, Finset.card_erase_of_mem ha, hn]; omega
    obtain ⟨σ', h1, h2', h3⟩ := ih (n - 2) (by omega) _ hc
    have mem' : ∀ x, x ∈ (s.erase a).erase b ↔ x ≠ b ∧ x ≠ a ∧ x ∈ s := by
      intro x; simp only [Finset.mem_erase]
    refine ⟨fun x => if x = a then b else if x = b then a else σ' x, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxa : x = a
      · subst hxa; simp [hb, Ne.symm hab]
      · by_cases hxb : x = b
        · subst hxb; simp [hxa, ha]
        · have hx' : x ∈ (s.erase a).erase b := (mem' x).2 ⟨hxb, hxa, hx⟩
          obtain ⟨hs1, hs2⟩ := h1 x hx'
          have := (mem' _).1 hs1
          simp [hxa, hxb, this.1, this.2.1, hs2, this.2.2]
    · intro x hx y hy hfx hfy
      have key : ∀ z ∈ s, (if z = a then b else if z = b then a else σ' z) = z →
          z ∈ (s.erase a).erase b ∧ σ' z = z := by
        intro z hz hfz
        by_cases hza : z = a
        · rw [if_pos hza] at hfz; exact absurd (hfz.trans hza) (Ne.symm hab)
        · by_cases hzb : z = b
          · rw [if_neg hza, if_pos hzb] at hfz; exact absurd (hfz.trans hzb) hab
          · rw [if_neg hza, if_neg hzb] at hfz; exact ⟨(mem' z).2 ⟨hzb, hza, hz⟩, hfz⟩
      obtain ⟨hx1, hx2⟩ := key x hx hfx
      obtain ⟨hy1, hy2⟩ := key y hy hfy
      exact h2' x hx1 y hy1 hx2 hy2
    · have hcs : s.card = ((s.erase a).erase b).card + 2 := by omega
      rw [hcs, Nat.even_add, h3]
      simp only [even_two, iff_true]
      constructor
      · intro H x hx
        by_cases hxa : x = a
        · rw [if_pos hxa]; exact fun h => hab (hxa ▸ h.symm)
        · by_cases hxb : x = b
          · rw [if_neg hxa, if_pos hxb]; exact fun h => hab (hxb ▸ h)
          · rw [if_neg hxa, if_neg hxb]; exact H x ((mem' x).2 ⟨hxb, hxa, hx⟩)
      · intro H x hx
        have := (mem' x).1 hx
        have h' := H x this.2.2
        rwa [if_neg this.2.1, if_neg this.1] at h'

/-! ## Segments and orientations of a pairing structure -/

/-- Darts `δ` (node–edge incidences), the edge involution `ε` (the two darts of an edge), the
pairing involution `π` (fixed points: left-over darts). -/
theorem dart_orient {δ : Type*} [DecidableEq δ] (π : δ → δ) (D : Finset δ) (ε : δ → δ)
    (hε : ∀ d ∈ D, ε d ∈ D ∧ ε (ε d) = d ∧ ε d ≠ d)
    (hπ : ∀ d ∈ D, π d ∈ D ∧ π (π d) = d) :
    ∃ o : δ → δ, (∀ d ∈ D, π d = d → o d ∈ D ∧ π (o d) = o d ∧ o (o d) = d ∧ o d ≠ d) ∧
      ∀ dir : δ → Bool, (∀ d ∈ D, π d = d → dir (o d) ≠ dir d) →
        ∃ c : δ → Bool, (∀ d ∈ D, c (ε d) ≠ c d) ∧ (∀ d ∈ D, π d ≠ d → c (π d) ≠ c d) ∧
          (∀ d ∈ D, π d = d → c d = dir d) := by
  suffices H : ∀ n (D : Finset δ) (ε : δ → δ), D.card = n →
      (∀ d ∈ D, ε d ∈ D ∧ ε (ε d) = d ∧ ε d ≠ d) → (∀ d ∈ D, π d ∈ D ∧ π (π d) = d) →
      ∃ o : δ → δ, (∀ d ∈ D, π d = d → o d ∈ D ∧ π (o d) = o d ∧ o (o d) = d ∧ o d ≠ d) ∧
      ∀ dir : δ → Bool, (∀ d ∈ D, π d = d → dir (o d) ≠ dir d) →
        ∃ c : δ → Bool, (∀ d ∈ D, c (ε d) ≠ c d) ∧ (∀ d ∈ D, π d ≠ d → c (π d) ≠ c d) ∧
          (∀ d ∈ D, π d = d → c d = dir d) from H _ D ε rfl hε hπ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D ε hn hε hπ
  by_cases hall : ∀ d ∈ D, π d = d
  · refine ⟨ε, fun d hd _ => ⟨(hε d hd).1, hall _ (hε d hd).1, (hε d hd).2.1, (hε d hd).2.2⟩,
      fun dir hdir => ⟨dir, fun d hd => hdir d hd (hall d hd), fun d hd h => absurd (hall d hd) h,
        fun d _ _ => rfl⟩⟩
  push_neg at hall
  obtain ⟨d0, hd0, hpd0⟩ := hall
  obtain ⟨d1, hd1def⟩ : ∃ d1, π d0 = d1 := ⟨_, rfl⟩
  have hd1 : d1 ∈ D := hd1def ▸ (hπ d0 hd0).1
  have hpd1 : π d1 = d0 := hd1def ▸ (hπ d0 hd0).2
  have h10 : d1 ≠ d0 := hd1def ▸ hpd0
  have hmem' : ∀ d, d ∈ (D.erase d0).erase d1 ↔ d ≠ d1 ∧ d ≠ d0 ∧ d ∈ D := by
    intro d; simp only [Finset.mem_erase]
  have hd1' : d1 ∈ D.erase d0 := Finset.mem_erase.2 ⟨h10, hd1⟩
  have hc' : ((D.erase d0).erase d1).card = n - 2 := by
    rw [Finset.card_erase_of_mem hd1', Finset.card_erase_of_mem hd0, hn]; omega
  have hn2 : 2 ≤ n := by
    have : 1 < D.card := Finset.one_lt_card.2 ⟨d0, hd0, d1, hd1, h10.symm⟩
    omega
  have hπ' : ∀ d ∈ (D.erase d0).erase d1, π d ∈ (D.erase d0).erase d1 ∧ π (π d) = d := by
    intro d hd
    obtain ⟨h1, h0, hD⟩ := (hmem' d).1 hd
    refine ⟨(hmem' _).2 ⟨?_, ?_, (hπ d hD).1⟩, (hπ d hD).2⟩
    · intro h; apply h0; rw [← (hπ d hD).2, h, hpd1]
    · intro h; apply h1; rw [← (hπ d hD).2, h, hd1def]
  have hfix : ∀ d ∈ D, π d = d → d ∈ (D.erase d0).erase d1 := by
    intro d hd hpd
    refine (hmem' d).2 ⟨?_, ?_, hd⟩
    · rintro rfl; exact h10 (hpd.symm.trans hpd1)
    · rintro rfl; exact hpd0 hpd
  by_cases hB1 : ε d0 = d1
  · -- the two darts form a closed trail of length 2: remove them
    have hεd1 : ε d1 = d0 := by rw [← hB1]; exact (hε d0 hd0).2.1
    have hε' : ∀ d ∈ (D.erase d0).erase d1, ε d ∈ (D.erase d0).erase d1 ∧ ε (ε d) = d ∧
        ε d ≠ d := by
      intro d hd
      obtain ⟨h1, h0, hD⟩ := (hmem' d).1 hd
      refine ⟨(hmem' _).2 ⟨?_, ?_, (hε d hD).1⟩, (hε d hD).2.1, (hε d hD).2.2⟩
      · intro h; apply h0; rw [← (hε d hD).2.1, h, hεd1]
      · intro h; apply h1; rw [← (hε d hD).2.1, h, hB1]
    obtain ⟨o, ho1, ho2⟩ := ih (n - 2) (by omega) _ ε hc' hε' hπ'
    refine ⟨o, fun d hd hpd => ?_, fun dir hdir => ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := ho1 d (hfix d hd hpd) hpd
      exact ⟨((hmem' _).1 a1).2.2, a2, a3, a4⟩
    · obtain ⟨c, hc1, hc2, hc3⟩ := ho2 dir (fun d hd hpd => hdir d ((hmem' d).1 hd).2.2 hpd)
      refine ⟨fun d => if d = d0 then true else if d = d1 then false else c d, ?_, ?_, ?_⟩
      · intro d hd
        by_cases h0 : d = d0
        · rw [h0]; simp [hB1, h10]
        · by_cases h1 : d = d1
          · rw [h1]; simp [hεd1, h10]
          · have hd' := (hmem' d).2 ⟨h1, h0, hd⟩
            have he := ((hmem' _).1 (hε' d hd').1)
            simp only [if_neg h0, if_neg h1, if_neg he.1, if_neg he.2.1]
            exact hc1 d hd'
      · intro d hd hpd
        by_cases h0 : d = d0
        · rw [h0, hd1def]; simp [h10]
        · by_cases h1 : d = d1
          · rw [h1, hpd1]; simp [h10]
          · have hd' := (hmem' d).2 ⟨h1, h0, hd⟩
            have he := ((hmem' _).1 (hπ' d hd').1)
            simp only [if_neg h0, if_neg h1, if_neg he.1, if_neg he.2.1]
            exact hc2 d hd' hpd
      · intro d hd hpd
        have hd' := hfix d hd hpd
        have := (hmem' d).1 hd'
        simp only [if_neg this.1, if_neg this.2.1]
        exact hc3 d hd' hpd
  · -- contract the pair `(d0, d1)`: link `ε d0` and `ε d1` directly
    obtain ⟨a, ha⟩ : ∃ a, ε d0 = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, ε d1 = b := ⟨_, rfl⟩
    have haD : a ∈ D := ha ▸ (hε d0 hd0).1
    have hbD : b ∈ D := hb ▸ (hε d1 hd1).1
    have hεa : ε a = d0 := ha ▸ (hε d0 hd0).2.1
    have hεb : ε b = d1 := hb ▸ (hε d1 hd1).2.1
    have ha0 : a ≠ d0 := ha ▸ (hε d0 hd0).2.2
    have ha1 : a ≠ d1 := ha ▸ hB1
    have hb1 : b ≠ d1 := hb ▸ (hε d1 hd1).2.2
    have hb0 : b ≠ d0 := by
      intro h; apply hB1
      have := (hε d1 hd1).2.1
      rw [hb, h] at this; exact this
    have hab : a ≠ b := by intro h; apply h10; rw [← hεb, ← h, hεa]
    have haD' : a ∈ (D.erase d0).erase d1 := (hmem' a).2 ⟨ha1, ha0, haD⟩
    have hbD' : b ∈ (D.erase d0).erase d1 := (hmem' b).2 ⟨hb1, hb0, hbD⟩
    let ε' : δ → δ := fun d => if d = a then b else if d = b then a else ε d
    have hε' : ∀ d ∈ (D.erase d0).erase d1, ε' d ∈ (D.erase d0).erase d1 ∧ ε' (ε' d) = d ∧
        ε' d ≠ d := by
      intro d hd
      obtain ⟨h1, h0, hD⟩ := (hmem' d).1 hd
      by_cases hda : d = a
      · subst hda; simp [ε', Ne.symm hab, hbD']
      · by_cases hdb : d = b
        · subst hdb; simp [ε', hab, haD', hda]
        · have hed : ε d ∈ D := (hε d hD).1
          have he0 : ε d ≠ d0 := by intro h; apply hda; rw [← ha, ← h, (hε d hD).2.1]
          have he1 : ε d ≠ d1 := by intro h; apply hdb; rw [← hb, ← h, (hε d hD).2.1]
          have hea : ε d ≠ a := by intro h; apply h0; rw [← (hε d hD).2.1, h, hεa]
          have heb : ε d ≠ b := by intro h; apply h1; rw [← (hε d hD).2.1, h, hεb]
          simp only [ε', if_neg hda, if_neg hdb, if_neg hea, if_neg heb]
          exact ⟨(hmem' _).2 ⟨he1, he0, hed⟩, (hε d hD).2.1, (hε d hD).2.2⟩
    obtain ⟨o, ho1, ho2⟩ := ih (n - 2) (by omega) _ ε' hc' hε' hπ'
    refine ⟨o, fun d hd hpd => ?_, fun dir hdir => ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := ho1 d (hfix d hd hpd) hpd
      exact ⟨((hmem' _).1 a1).2.2, a2, a3, a4⟩
    · obtain ⟨c, hc1, hc2, hc3⟩ := ho2 dir (fun d hd hpd => hdir d ((hmem' d).1 hd).2.2 hpd)
      have hca : c b ≠ c a := by
        have := hc1 a haD'; simpa [ε'] using this
      refine ⟨fun d => if d = d0 then !c a else if d = d1 then c a else c d, ?_, ?_, ?_⟩
      · intro d hd
        by_cases h0 : d = d0
        · rw [h0, ha]; simp [ha0, ha1]
        · by_cases h1 : d = d1
          · rw [h1, hb]; simpa [hb0, hb1, h10] using hca
          · by_cases hda : d = a
            · rw [hda, hεa]; simp [ha0, ha1]
            · by_cases hdb : d = b
              · rw [hdb, hεb]; simpa [hb0, hb1, h10] using Ne.symm hca
              · have hd' := (hmem' d).2 ⟨h1, h0, hd⟩
                have hed : ε' d = ε d := by simp [ε', hda, hdb]
                have he := ((hmem' _).1 (hε' d hd').1)
                rw [hed] at he
                simp only [if_neg h0, if_neg h1, if_neg he.1, if_neg he.2.1]
                have := hc1 d hd'
                rwa [hed] at this
      · intro d hd hpd
        by_cases h0 : d = d0
        · rw [h0, hd1def]; simp [h10]
        · by_cases h1 : d = d1
          · rw [h1, hpd1]; simp [h10]
          · have hd' := (hmem' d).2 ⟨h1, h0, hd⟩
            have he := ((hmem' _).1 (hπ' d hd').1)
            simp only [if_neg h0, if_neg h1, if_neg he.1, if_neg he.2.1]
            exact hc2 d hd' hpd
      · intro d hd hpd
        have hd' := hfix d hd hpd
        have := (hmem' d).1 hd'
        simp only [if_neg this.1, if_neg this.2.1]
        exact hc3 d hd' hpd

/-! ## Generic list / multiset facts -/

lemma card_filter_invol {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] (τ : α → α) (h : ∀ a ∈ s, τ a ∈ s ∧ τ (τ a) = a ∧ (P (τ a) ↔ ¬ P a)) :
    (s.filter P).card = (s.filter (fun a => ¬ P a)).card := by
  refine Finset.card_bij' (fun a _ => τ a) (fun a _ => τ a) ?_ ?_ ?_ ?_
  · intro a ha; rw [Finset.mem_filter] at ha ⊢
    exact ⟨(h a ha.1).1, fun hp => ((h a ha.1).2.2.1 hp) ha.2⟩
  · intro a ha; rw [Finset.mem_filter] at ha ⊢
    exact ⟨(h a ha.1).1, (h a ha.1).2.2.2 ha.2⟩
  · intro a ha; exact (h a (Finset.mem_filter.1 ha).1).2.1
  · intro a ha; exact (h a (Finset.mem_filter.1 ha).1).2.1

lemma multiset_card_filterMap {α β : Type*} (f : α → Option β) (s : Multiset α) :
    Multiset.card (s.filterMap f) = Multiset.card (s.filter (fun a => (f a).isSome)) := by
  refine Multiset.induction_on s (by simp) (fun a s ih => ?_)
  cases h : f a with
  | none =>
    rw [Multiset.filterMap_cons_none _ _ h, Multiset.filter_cons_of_neg _ (by simp [h]), ih]
  | some b =>
    rw [Multiset.filterMap_cons_some _ _ _ h, Multiset.filter_cons_of_pos _ (by simp [h]),
      Multiset.card_cons, Multiset.card_cons, ih]

lemma multiset_filterMap_congr {α β : Type*} {f g : α → Option β} (s : Multiset α)
    (h : ∀ a ∈ s, f a = g a) : s.filterMap f = s.filterMap g := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.filterMap_cons, Multiset.filterMap_cons, h a (Multiset.mem_cons_self a s),
      ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))]

lemma list_length_le_one {α : Type*} {l : List α} (hn : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a = b) : l.length ≤ 1 := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp
  · simp
  · exfalso
    have hab := h a (by simp) b (by simp)
    rw [List.nodup_cons] at hn
    exact hn.1 (by simp [hab])

/-- the partner position of `i` in the pairing `(0,1), (2,3), …` -/
def pidx (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

lemma pidx_pidx (i : ℕ) : pidx (pidx i) = i := by
  unfold pidx; split_ifs <;> omega

lemma pidx_lt {i L : ℕ} (hi : i < L) (hL : Even L) : pidx i < L := by
  obtain ⟨k, hk⟩ := hL
  unfold pidx; split_ifs <;> omega

/-! ## Darts of a cluster -/

section Cluster

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the other endpoint of `e`, seen from `v` -/
noncomputable def oth (v : V) (e : Sym2 V) : V := if h : v ∈ e then Sym2.Mem.other h else v

lemma oth_mem {v : V} {e : Sym2 V} (h : v ∈ e) : oth v e ∈ e := by
  unfold oth; rw [dif_pos h]; exact Sym2.other_mem h

lemma oth_oth {v : V} {e : Sym2 V} (h : v ∈ e) : oth (oth v e) e = v := by
  unfold oth; rw [dif_pos h, dif_pos (Sym2.other_mem h)]; exact Sym2.other_invol h _

lemma oth_ne {v : V} {e : Sym2 V} (h : v ∈ e) (hd : ¬ e.IsDiag) : oth v e ≠ v := by
  unfold oth; rw [dif_pos h]; exact Sym2.other_ne hd h

lemma eq_or_eq_oth {v u : V} {e : Sym2 V} (h : v ∈ e) (hu : u ∈ e) : u = v ∨ u = oth v e := by
  have := Sym2.other_spec h
  rw [← this, Sym2.mem_iff] at hu
  unfold oth; rw [dif_pos h]; exact hu

/-- the darts (node–edge incidences) of the edge set `F` -/
def darts (F : Finset (Sym2 V)) : Finset (V × Sym2 V) :=
  (univ ×ˢ F).filter (fun p => p.1 ∈ p.2 ∧ ¬ p.2.IsDiag)

lemma mem_darts {F : Finset (Sym2 V)} {p : V × Sym2 V} :
    p ∈ darts F ↔ p.2 ∈ F ∧ p.1 ∈ p.2 ∧ ¬ p.2.IsDiag := by
  simp [darts]

/-- the other dart of the same edge -/
noncomputable def flipD (p : V × Sym2 V) : V × Sym2 V := (oth p.1 p.2, p.2)

/-- the edges of `F` at `v` -/
def atV (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) := F.filter (fun e => v ∈ e ∧ ¬ e.IsDiag)

lemma mem_atV {F : Finset (Sym2 V)} {v : V} {e : Sym2 V} : e ∈ atV F v ↔ (v, e) ∈ darts F := by
  simp [atV, mem_darts]

/-- the pairing of the edges of `F` at `v` (fixed points: left-over edges) -/
noncomputable def pairAt (F : Finset (Sym2 V)) (v : V) : Sym2 V → Sym2 V :=
  Classical.choose (exists_pairing (atV F v))

lemma pairAt_spec (F : Finset (Sym2 V)) (v : V) :
    (∀ a ∈ atV F v, pairAt F v a ∈ atV F v ∧ pairAt F v (pairAt F v a) = a) ∧
    (∀ a ∈ atV F v, ∀ b ∈ atV F v, pairAt F v a = a → pairAt F v b = b → a = b) ∧
    (Even (atV F v).card ↔ ∀ a ∈ atV F v, pairAt F v a ≠ a) :=
  Classical.choose_spec (exists_pairing (atV F v))

/-- the pairing as an involution on darts -/
noncomputable def piD (F : Finset (Sym2 V)) (p : V × Sym2 V) : V × Sym2 V :=
  (p.1, pairAt F p.1 p.2)

lemma piD_fix_iff {F : Finset (Sym2 V)} {v : V} {e : Sym2 V} :
    piD F (v, e) = (v, e) ↔ pairAt F v e = e := by
  simp [piD]

lemma flipD_props (F : Finset (Sym2 V)) :
    ∀ d ∈ darts F, flipD d ∈ darts F ∧ flipD (flipD d) = d ∧ flipD d ≠ d := by
  rintro ⟨v, e⟩ hd
  rw [mem_darts] at hd
  obtain ⟨he, hv, hnd⟩ := hd
  refine ⟨mem_darts.2 ⟨he, oth_mem hv, hnd⟩, ?_, ?_⟩
  · simp only [flipD, oth_oth hv]
  · intro h; simp only [flipD, Prod.mk.injEq] at h; exact oth_ne hv hnd h.1

lemma piD_props (F : Finset (Sym2 V)) :
    ∀ d ∈ darts F, piD F d ∈ darts F ∧ piD F (piD F d) = d := by
  rintro ⟨v, e⟩ hd
  have he : e ∈ atV F v := mem_atV.2 hd
  obtain ⟨h1, h2⟩ := (pairAt_spec F v).1 e he
  exact ⟨mem_atV.1 h1, by simp only [piD, h2]⟩

/-- the other end of the segment starting at a left-over dart -/
noncomputable def oend (F : Finset (Sym2 V)) : V × Sym2 V → V × Sym2 V :=
  Classical.choose (dart_orient (piD F) (darts F) flipD (flipD_props F) (piD_props F))

lemma oend_spec (F : Finset (Sym2 V)) :
    (∀ d ∈ darts F, piD F d = d → oend F d ∈ darts F ∧ piD F (oend F d) = oend F d ∧
      oend F (oend F d) = d ∧ oend F d ≠ d) ∧
    ∀ dir : V × Sym2 V → Bool, (∀ d ∈ darts F, piD F d = d → dir (oend F d) ≠ dir d) →
      ∃ c : V × Sym2 V → Bool, (∀ d ∈ darts F, c (flipD d) ≠ c d) ∧
        (∀ d ∈ darts F, piD F d ≠ d → c (piD F d) ≠ c d) ∧
        (∀ d ∈ darts F, piD F d = d → c d = dir d) :=
  Classical.choose_spec (dart_orient (piD F) (darts F) flipD (flipD_props F) (piD_props F))

/-- a consistent orientation of `F` (`true` = the edge leaves the node), agreeing with `dir` at
the left-over darts -/
def GoodCol (F : Finset (Sym2 V)) (dir c : V × Sym2 V → Bool) : Prop :=
  (∀ d ∈ darts F, c (flipD d) ≠ c d) ∧ (∀ d ∈ darts F, piD F d ≠ d → c (piD F d) ≠ c d) ∧
  (∀ d ∈ darts F, piD F d = d → c d = dir d)

noncomputable def colorOf (F : Finset (Sym2 V)) (dir : V × Sym2 V → Bool) :
    V × Sym2 V → Bool := by
  classical exact if h : ∃ c, GoodCol F dir c then Classical.choose h else fun _ => false

lemma colorOf_good (F : Finset (Sym2 V)) (dir : V × Sym2 V → Bool)
    (h : ∀ d ∈ darts F, piD F d = d → dir (oend F d) ≠ dir d) :
    GoodCol F dir (colorOf F dir) := by
  have hex : ∃ c, GoodCol F dir c := (oend_spec F).2 dir h
  unfold colorOf; rw [dif_pos hex]; exact Classical.choose_spec hex

lemma exists_mem_sym2 (e : Sym2 V) : ∃ u, u ∈ e :=
  Sym2.ind (f := fun e => ∃ u, u ∈ e) (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) e

/-- the head of `e` in the orientation `colorOf F dir` -/
noncomputable def headOf (F : Finset (Sym2 V)) (dir : V × Sym2 V → Bool) (e : Sym2 V) : V := by
  classical
  exact if h : ∃ u, u ∈ e ∧ colorOf F dir (u, e) = false then Classical.choose h
    else Classical.choose (exists_mem_sym2 e)

lemma headOf_spec {F : Finset (Sym2 V)} {dir : V × Sym2 V → Bool}
    (hg : GoodCol F dir (colorOf F dir)) {v : V} {e : Sym2 V} (hd : (v, e) ∈ darts F) :
    headOf F dir e ∈ e ∧ (headOf F dir e = v ↔ colorOf F dir (v, e) = false) := by
  have hv := (mem_darts.1 hd).2.1
  have hfl := hg.1 (v, e) hd
  simp only [flipD] at hfl
  have hex : ∃ u, u ∈ e ∧ colorOf F dir (u, e) = false := by
    cases hc : colorOf F dir (v, e)
    · exact ⟨v, hv, hc⟩
    · refine ⟨oth v e, oth_mem hv, ?_⟩
      rw [hc] at hfl; simpa using hfl
  have hh : headOf F dir e = Classical.choose hex := by unfold headOf; rw [dif_pos hex]
  obtain ⟨hu1, hu2⟩ := Classical.choose_spec hex
  rw [hh]
  refine ⟨hu1, ⟨fun h => h ▸ hu2, fun h => ?_⟩⟩
  rcases eq_or_eq_oth hv hu1 with h' | h'
  · exact h'
  · exfalso; rw [h'] at hu2; rw [hu2, h] at hfl; exact hfl rfl

/-- the left-over edge of `F` at `v`, if any -/
noncomputable def lo (F : Finset (Sym2 V)) (v : V) : Option (Sym2 V) := by
  classical
  exact if h : ∃ e, (v, e) ∈ darts F ∧ piD F (v, e) = (v, e) then some (Classical.choose h)
    else none

lemma lo_eq_some {F : Finset (Sym2 V)} {v : V} {e : Sym2 V} :
    lo F v = some e ↔ (v, e) ∈ darts F ∧ piD F (v, e) = (v, e) := by
  unfold lo
  split_ifs with h
  · have hs := Classical.choose_spec h
    constructor
    · intro he; rw [← Option.some.inj he]; exact hs
    · intro he
      congr 1
      rw [piD_fix_iff] at hs he
      exact (pairAt_spec F v).2.1 _ (mem_atV.2 hs.1) _ (mem_atV.2 he.1) hs.2 he.2
  · constructor
    · intro he; cases he
    · intro he; exact absurd ⟨e, he⟩ h

lemma lo_eq_none_iff {F : Finset (Sym2 V)} {v : V} : lo F v = none ↔ Even (atV F v).card := by
  rw [(pairAt_spec F v).2.2]
  constructor
  · intro h e he hfix
    have := lo_eq_some.2 ⟨mem_atV.1 he, piD_fix_iff.2 hfix⟩
    rw [h] at this; cases this
  · intro h
    cases hl : lo F v with
    | none => rfl
    | some e =>
      obtain ⟨h1, h2⟩ := lo_eq_some.1 hl
      exact absurd (piD_fix_iff.1 h2) (h e (mem_atV.2 h1))

/-! ## Messages -/

/-- the segment end of `v` in the cluster with physical edges `F`: (own edge, partner node,
partner edge) -/
noncomputable def segEnd (F : Finset (Sym2 V)) (v : V) : Option (Sym2 V × V × Sym2 V) :=
  (lo F v).map (fun e => (e, oend F (v, e)))

lemma segEnd_eq_some {F : Finset (Sym2 V)} {v x : V} {e e' : Sym2 V} :
    segEnd F v = some (e, x, e') ↔ lo F v = some e ∧ oend F (v, e) = (x, e') := by
  unfold segEnd
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hae⟩
    simp only [Prod.mk.injEq] at hae
    obtain ⟨rfl, h2⟩ := hae
    exact ⟨ha, by rw [h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, h1, by rw [h2]⟩

/-- the message of the aggregator to `v` (step 2) -/
noncomputable def segMsg (F : Finset (Sym2 V)) (v : V) : Option (Msg V) :=
  (segEnd F v).map (fun t => [Word.edge t.1, Word.id t.2.1, Word.edge t.2.2])

def parseEnd : Msg V → Option (Sym2 V × V × Sym2 V)
  | [Word.edge e, Word.id x, Word.edge e'] => some (e, x, e')
  | _ => none

lemma segMsg_bind (F : Finset (Sym2 V)) (v : V) : (segMsg F v).bind parseEnd = segEnd F v := by
  unfold segMsg
  cases segEnd F v with
  | none => rfl
  | some t => rfl

lemma segMsg_small (F : Finset (Sym2 V)) (v : V) (m : Msg V) (B : ℕ) (h : segMsg F v = some m) :
    m.Small 3 B := by
  unfold segMsg at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨t, _, rfl⟩ := h
  refine ⟨by simp, fun k hk => ?_⟩
  simp at hk

/-- the ring data of a node: its segment ends, from the received messages -/
noncomputable def ringOf (M : Multiset (Msg V)) : RingIn V := M.toList.filterMap parseEnd

/-- the message of a node to its aggregators (step 5): the edges of its ends directed outwards -/
def outMsg (l : RingIn V) (b : List Bool) : Msg V :=
  (List.range l.length).filterMap
    (fun k => if b.getD k false = true then (l[k]?).map (fun t => Word.edge t.1) else none)

lemma mem_outMsg {l : RingIn V} {b : List Bool} {e : Sym2 V} :
    Word.edge e ∈ outMsg l b ↔ ∃ k t, l[k]? = some t ∧ t.1 = e ∧ b.getD k false = true := by
  unfold outMsg
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, _, hk⟩
    split_ifs at hk with hb
    rw [Option.map_eq_some_iff] at hk
    obtain ⟨t, ht, hte⟩ := hk
    exact ⟨k, t, ht, Word.edge.inj hte, hb⟩
  · rintro ⟨k, t, ht, hte, hb⟩
    obtain ⟨hk, _⟩ := List.getElem?_eq_some_iff.1 ht
    refine ⟨k, List.mem_range.2 hk, ?_⟩
    rw [if_pos hb, ht]; simp [hte]

lemma outMsg_small (l : RingIn V) (b : List Bool) (B : ℕ) : (outMsg l b).Small l.length B := by
  refine ⟨?_, fun k hk => ?_⟩
  · exact (List.length_filterMap_le _ _).trans (by simp)
  · unfold outMsg at hk
    rw [List.mem_filterMap] at hk
    obtain ⟨i, _, hi⟩ := hk
    split_ifs at hi
    rw [Option.map_eq_some_iff] at hi
    obtain ⟨t, _, ht⟩ := hi
    cases ht

end Cluster

/-! ## The ring structure of a cluster family -/

section Family

variable {V : Type} [Fintype V] [DecidableEq V]

lemma decide_eq_of_iff {P : Prop} [Decidable P] {b : Bool} (h : P ↔ b = true) : decide P = b := by
  cases b <;> simp_all

lemma mem_clustersOf' {cl : Finset (Finset (Sym2 V))} {v : V} {C : Finset (Sym2 V)} :
    C ∈ clustersOf cl v ↔ C ∈ cl ∧ v ∈ nodes C := by
  simp [clustersOf]

/-- The setting of the proof: disjoint clusters `cl`, physical edges `Hp` (no loops, inside `S`,
covered by the clusters, even degrees at the nodes of `S`), and the physical edges `FF C` of each
cluster as known by its aggregator. -/
structure FamOK (cl : Finset (Finset (Sym2 V))) (FF : Finset (Sym2 V) → Finset (Sym2 V))
    (Hp : Finset (Sym2 V)) (S : Finset V) : Prop where
  disj : ∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C'
  ff : ∀ C e, e ∈ FF C ↔ e ∈ C ∧ e ∈ Hp
  cov : ∀ e ∈ Hp, ∃ C ∈ cl, e ∈ C
  nd : ∀ e ∈ Hp, ¬ e.IsDiag
  inS : ∀ e ∈ Hp, ∀ v ∈ e, v ∈ S
  ev : ∀ v ∈ S, Even (Hp.filter (fun e => v ∈ e)).card

/-- the ring data of node `v`, as computed from the messages of its aggregators -/
noncomputable def ringFam (cl : Finset (Finset (Sym2 V))) (FF : Finset (Sym2 V) → Finset (Sym2 V))
    (v : V) : RingIn V :=
  ringOf ((clustersOf cl v).val.filterMap (fun C => segMsg (FF C) v))

variable {cl : Finset (Finset (Sym2 V))} {FF : Finset (Sym2 V) → Finset (Sym2 V)}
  {Hp : Finset (Sym2 V)} {S : Finset V}

lemma ringFam_coe (v : V) : ((ringFam cl FF v : List _) : Multiset _) =
    (clustersOf cl v).val.filterMap (fun C => segEnd (FF C) v) := by
  unfold ringFam ringOf
  rw [← Multiset.filterMap_coe, Multiset.coe_toList, Multiset.filterMap_filterMap]
  simp only [segMsg_bind]

lemma mem_ringFam {v : V} {t : Sym2 V × V × Sym2 V} :
    t ∈ ringFam cl FF v ↔ ∃ C ∈ clustersOf cl v, segEnd (FF C) v = some t := by
  rw [← Multiset.mem_coe, ringFam_coe, Multiset.mem_filterMap]
  simp only [Finset.mem_val]

namespace FamOK

lemma unique (h : FamOK cl FF Hp S) {C C' : Finset (Sym2 V)} (hC : C ∈ cl) (hC' : C' ∈ cl)
    {e : Sym2 V} (he : e ∈ C) (he' : e ∈ C') : C = C' := by
  by_contra hne; exact Finset.disjoint_left.1 (h.disj C hC C' hC' hne) he he'

lemma mem_ring (h : FamOK cl FF Hp S) {v x : V} {e e' : Sym2 V}
    (ht : (e, x, e') ∈ ringFam cl FF v) :
    ∃ C ∈ cl, v ∈ nodes C ∧ segEnd (FF C) v = some (e, x, e') ∧ (v, e) ∈ darts (FF C) ∧
      piD (FF C) (v, e) = (v, e) ∧ oend (FF C) (v, e) = (x, e') ∧ e ∈ C ∧ e ∈ Hp := by
  obtain ⟨C, hC, hs⟩ := mem_ringFam.1 ht
  obtain ⟨hlo, ho⟩ := segEnd_eq_some.1 hs
  obtain ⟨hd, hfix⟩ := lo_eq_some.1 hlo
  have he := (h.ff C e).1 (mem_darts.1 hd).1
  obtain ⟨hC1, hC2⟩ := mem_clustersOf'.1 hC
  exact ⟨C, hC1, hC2, hs, hd, hfix, ho, he.1, he.2⟩

lemma fst_inj (h : FamOK cl FF Hp S) {v : V} {t t' : Sym2 V × V × Sym2 V}
    (ht : t ∈ ringFam cl FF v) (ht' : t' ∈ ringFam cl FF v) (he : t.1 = t'.1) : t = t' := by
  rcases t with ⟨e, x, e'⟩
  rcases t' with ⟨f, y, f'⟩
  obtain ⟨C, hC, _, hs, -, -, -, heC, -⟩ := h.mem_ring ht
  obtain ⟨C', hC', _, hs', -, -, -, heC', -⟩ := h.mem_ring ht'
  simp only at he
  subst he
  have := h.unique hC hC' heC heC'
  subst this
  rw [hs] at hs'; exact Option.some.inj hs'

lemma ring_of_fix (h : FamOK cl FF Hp S) {C : Finset (Sym2 V)} (hC : C ∈ cl) {v : V}
    {e : Sym2 V} (hd : (v, e) ∈ darts (FF C)) (hfix : piD (FF C) (v, e) = (v, e)) :
    (e, oend (FF C) (v, e)) ∈ ringFam cl FF v := by
  rw [mem_ringFam]
  have hd' := mem_darts.1 hd
  refine ⟨C, mem_clustersOf'.2 ⟨hC, mem_nodes.2 ⟨e, ((h.ff C e).1 hd'.1).1, hd'.2.1⟩⟩, ?_⟩
  unfold segEnd; rw [lo_eq_some.2 ⟨hd, hfix⟩]; rfl

lemma nodup (h : FamOK cl FF Hp S) (v : V) : (ringFam cl FF v).Nodup := by
  rw [← Multiset.coe_nodup, ringFam_coe,
    multiset_filterMap_congr (g := fun C => if C ∈ cl then segEnd (FF C) v else none) _
      (fun C hC => by rw [if_pos (mem_clustersOf'.1 hC).1])]
  refine Multiset.Nodup.filterMap _ ?_ (clustersOf cl v).nodup
  intro C C' t hC hC'
  simp only [Option.mem_def] at hC hC'
  by_cases h1 : C ∈ cl
  · by_cases h2 : C' ∈ cl
    · rw [if_pos h1] at hC; rw [if_pos h2] at hC'
      rcases t with ⟨e, x, e'⟩
      have a1 := mem_darts.1 (lo_eq_some.1 (segEnd_eq_some.1 hC).1).1
      have a2 := mem_darts.1 (lo_eq_some.1 (segEnd_eq_some.1 hC').1).1
      exact h.unique h1 h2 ((h.ff C e).1 a1.1).1 ((h.ff C' e).1 a2.1).1
    · rw [if_neg h2] at hC'; cases hC'
  · rw [if_neg h1] at hC; cases hC

lemma length_eq (_h : FamOK cl FF Hp S) (v : V) : (ringFam cl FF v).length =
    ((clustersOf cl v).filter (fun C => Odd (atV (FF C) v).card)).card := by
  rw [← Multiset.coe_card, ringFam_coe, multiset_card_filterMap, Finset.card_def,
    Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro C _
  simp only [segEnd, Option.isSome_map]
  rw [← Nat.not_even_iff_odd, ← lo_eq_none_iff]
  cases lo (FF C) v <;> simp

lemma sum_atV (h : FamOK cl FF Hp S) (v : V) :
    ∑ C ∈ clustersOf cl v, (atV (FF C) v).card = (Hp.filter (fun e => v ∈ e)).card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_filter, mem_atV, mem_darts, mem_clustersOf']
    constructor
    · rintro ⟨C, ⟨hC, _⟩, he, hv, _⟩
      exact ⟨((h.ff C e).1 he).2, hv⟩
    · rintro ⟨he, hv⟩
      obtain ⟨C, hC, heC⟩ := h.cov e he
      exact ⟨C, ⟨hC, mem_nodes.2 ⟨e, heC, hv⟩⟩, (h.ff C e).2 ⟨heC, he⟩, hv, h.nd e he⟩
  · intro C hC C' hC' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [mem_atV, mem_darts] at he he'
    exact Finset.disjoint_left.1 (h.disj C (mem_clustersOf'.1 (Finset.mem_coe.1 hC)).1 C'
      (mem_clustersOf'.1 (Finset.mem_coe.1 hC')).1 hne) ((h.ff C e).1 he.1).1
      ((h.ff C' e).1 he'.1).1

/-- The ring data is well formed (`RingWF`). -/
theorem ringWF (h : FamOK cl FF Hp S) : RingWF cl S (ringFam cl FF) := by
  have hout : ∀ v ∉ S, ringFam cl FF v = [] := by
    intro v hv
    rw [List.eq_nil_iff_forall_not_mem]
    rintro ⟨e, x, e'⟩ ht
    obtain ⟨C, _, _, _, hd, _, _, _, hHp⟩ := h.mem_ring ht
    exact hv (h.inS _ hHp v (mem_darts.1 hd).2.1)
  refine ⟨hout, ?_, h.nodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ S
    · rw [h.length_eq, ← Finset.even_sum_iff_even_card_odd, h.sum_atV]; exact h.ev v hv
    · rw [hout v hv]; simp
  · intro v e x e' ht
    obtain ⟨C, hC, _, _, hd, hfix, ho, _, _⟩ := h.mem_ring ht
    obtain ⟨o1, o2, o3, _⟩ := (oend_spec (FF C)).1 _ hd hfix
    rw [ho] at o1 o2 o3
    have := h.ring_of_fix hC o1 o2
    rw [o3] at this
    exact this
  · intro v e x e' ht
    obtain ⟨C, hC, hvC, _, hd, hfix, ho, heC, _⟩ := h.mem_ring ht
    obtain ⟨o1, _⟩ := (oend_spec (FF C)).1 _ hd hfix
    rw [ho] at o1
    have o1' := mem_darts.1 o1
    exact ⟨C, hC, heC, ((h.ff C _).1 o1'.1).1, hvC,
      mem_nodes.2 ⟨e', ((h.ff C _).1 o1'.1).1, o1'.2.1⟩⟩
  · intro v C hC
    apply list_length_le_one ((h.nodup v).filter _)
    rintro ⟨a, ax, a'⟩ ha ⟨b, bx, b'⟩ hb
    rw [List.mem_filter] at ha hb
    obtain ⟨C1, hC1, _, hs1, _, _, _, he1, _⟩ := h.mem_ring ha.1
    obtain ⟨C2, hC2, _, hs2, _, _, _, he2, _⟩ := h.mem_ring hb.1
    have e1 := h.unique hC1 hC he1 (by simpa using ha.2)
    have e2 := h.unique hC2 hC he2 (by simpa using hb.2)
    subst e1; subst e2
    rw [hs1] at hs2; exact Option.some.inj hs2
  · -- the two ends of a segment are different ends
    intro v e x e' ht
    obtain ⟨C, hC, _, _, hd, hfix, ho, _, _⟩ := h.mem_ring ht
    obtain ⟨_, _, _, o4⟩ := (oend_spec (FF C)).1 _ hd hfix
    rw [ho] at o4
    exact fun h' => o4 h'.symm
  · -- segment ends are darts: the own edge is incident to the node
    intro v e x e' ht
    obtain ⟨C, _, _, _, hd, _, _, _, _⟩ := h.mem_ring ht
    exact (mem_darts.1 hd).2.1

end FamOK

/-- the cluster containing `e` -/
noncomputable def Cof (cl : Finset (Finset (Sym2 V))) (e : Sym2 V) : Finset (Sym2 V) := by
  classical
  exact if h : ∃ C ∈ cl, e ∈ C then Classical.choose h else ∅

/-- the orientation of all physical edges: each edge oriented by the aggregator of its cluster -/
noncomputable def gHead (cl : Finset (Finset (Sym2 V))) (FF : Finset (Sym2 V) → Finset (Sym2 V))
    (dir : Finset (Sym2 V) → V × Sym2 V → Bool) (e : Sym2 V) : V :=
  headOf (FF (Cof cl e)) (dir (Cof cl e)) e

lemma ringSpec_pidx {r : V → RingIn V} {d : V → List Bool} (hd : RingSpec r d) (v : V) {i : ℕ}
    (hi : pidx i < (r v).length) (hi' : i < (r v).length) :
    (d v).getD i false ≠ (d v).getD (pidx i) false := by
  by_cases h0 : i % 2 = 0
  · have hp : pidx i = i + 1 := by unfold pidx; rw [if_pos h0]
    rw [hp] at hi ⊢
    have := hd.2.1 v (i / 2) (by omega)
    have e1 : 2 * (i / 2) = i := by omega
    rwa [e1] at this
  · have hp : pidx i = i - 1 := by unfold pidx; rw [if_neg h0]
    rw [hp] at hi ⊢
    have := hd.2.1 v (i / 2) (by omega)
    have e1 : 2 * (i / 2) = i - 1 := by omega
    have e2 : i - 1 + 1 = i := by omega
    rw [e1, e2] at this; exact Ne.symm this

namespace FamOK

lemma Cof_eq (h : FamOK cl FF Hp S) {C : Finset (Sym2 V)} (hC : C ∈ cl) {e : Sym2 V}
    (he : e ∈ C) : Cof cl e = C := by
  have hex : ∃ C ∈ cl, e ∈ C := ⟨C, hC, he⟩
  unfold Cof; rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  exact h.unique h1 hC h2 he

lemma Cof_mem (h : FamOK cl FF Hp S) {e : Sym2 V} (he : e ∈ Hp) : Cof cl e ∈ cl ∧ e ∈ Cof cl e := by
  obtain ⟨C, hC, heC⟩ := h.cov e he
  rw [h.Cof_eq hC heC]; exact ⟨hC, heC⟩

/-- **Correctness**: if the aggregator of every cluster `C` orients its edges with directions `dir C`
at the left-over darts read off the nodes' messages (the ring orientation `d`), the result is an
Eulerian orientation. -/
theorem orient (h : FamOK cl FF Hp S) (d : V → List Bool) (hd : RingSpec (ringFam cl FF) d)
    (dir : Finset (Sym2 V) → V × Sym2 V → Bool)
    (hdir : ∀ C ∈ cl, ∀ v e, (v, e) ∈ darts (FF C) → piD (FF C) (v, e) = (v, e) →
      dir C (v, e) = decide (Word.edge e ∈ outMsg (ringFam cl FF v) (d v))) :
    (∀ e ∈ Hp, gHead cl FF dir e ∈ e) ∧
    (∀ C ∈ cl, ∀ e ∈ Hp, e ∈ C → headOf (FF C) (dir C) e = gHead cl FF dir e) ∧
    (∀ v, (Hp.filter (fun e => v ∈ e ∧ gHead cl FF dir e = v)).card =
      (Hp.filter (fun e => v ∈ e ∧ gHead cl FF dir e ≠ v)).card) := by
  -- the direction of the end at position `i`
  have hidx : ∀ v i (t : Sym2 V × V × Sym2 V), (ringFam cl FF v)[i]? = some t →
      (Word.edge t.1 ∈ outMsg (ringFam cl FF v) (d v) ↔ (d v).getD i false = true) := by
    intro v i t hi
    rw [mem_outMsg]
    constructor
    · rintro ⟨k, t', hk, hte, hb⟩
      have := h.fst_inj (List.mem_of_getElem? hk) (List.mem_of_getElem? hi) hte
      rw [this, ← hi] at hk
      have hkl : k < (ringFam cl FF v).length := (List.getElem?_eq_some_iff.1 (hk.trans hi)).1
      rw [(h.nodup v).getElem?_inj hkl] at hk
      rw [← hk]; exact hb
    · intro hb; exact ⟨i, t, hi, rfl, hb⟩
  -- the orientations chosen by the aggregators are consistent
  have hgood : ∀ C ∈ cl, GoodCol (FF C) (dir C) (colorOf (FF C) (dir C)) := by
    intro C hC
    apply colorOf_good
    rintro ⟨v, e⟩ hdv hfix
    obtain ⟨o1, o2, o3, _⟩ := (oend_spec (FF C)).1 _ hdv hfix
    have m1 := h.ring_of_fix hC hdv hfix
    rcases hxe : oend (FF C) (v, e) with ⟨x, e'⟩
    rw [hxe] at o1 o2 o3 m1
    have m2 := h.ring_of_fix hC o1 o2
    rw [o3] at m2
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 m1
    obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.1 m2
    have hne := hd.2.2 v x e e' i i' hi hi'
    rw [hdir C hC x e' o1 o2, hdir C hC v e hdv hfix]
    rw [decide_eq_of_iff (hidx v i _ hi), decide_eq_of_iff (hidx x i' _ hi')]
    exact Ne.symm hne
  have hhead : ∀ e ∈ Hp, ∀ v ∈ e, gHead cl FF dir e ∈ e ∧ (gHead cl FF dir e = v ↔
      colorOf (FF (Cof cl e)) (dir (Cof cl e)) (v, e) = false) := by
    intro e he v hv
    obtain ⟨hC, heC⟩ := h.Cof_mem he
    exact headOf_spec (hgood _ hC) (mem_darts.2 ⟨(h.ff _ e).2 ⟨heC, he⟩, hv, h.nd e he⟩)
  refine ⟨fun e he => ?_, fun C hC e he heC => ?_, fun v => ?_⟩
  · obtain ⟨v, hv⟩ := exists_mem_sym2 e
    exact (hhead e he v hv).1
  · unfold gHead; rw [h.Cof_eq hC heC]
  -- counting at `v`
  let m : List (Sym2 V) := (ringFam cl FF v).map Prod.fst
  have hmn : m.Nodup := (h.nodup v).map_on (fun a ha b hb hab => h.fst_inj ha hb hab)
  have hml : Even m.length := by
    simp only [m, List.length_map]; exact h.ringWF.even v
  have hm_left : ∀ b ∈ m, b ∈ Hp ∧ v ∈ b ∧ pairAt (FF (Cof cl b)) v b = b := by
    intro b hb
    obtain ⟨⟨e, x, e'⟩, ht, rfl⟩ := List.mem_map.1 hb
    obtain ⟨C, hC, _, _, hdd, hfix, _, heC, heH⟩ := h.mem_ring ht
    refine ⟨heH, (mem_darts.1 hdd).2.1, ?_⟩
    simp only
    rw [h.Cof_eq hC heC]; exact piD_fix_iff.1 hfix
  have hfixP : ∀ e ∈ Hp, v ∈ e → pairAt (FF (Cof cl e)) v e = e → ∀ i, m[i]? = some e →
      (gHead cl FF dir e = v ↔ (d v).getD i false = false) := by
    intro e he hv hfix i hi
    obtain ⟨hC, heC⟩ := h.Cof_mem he
    have hdart : (v, e) ∈ darts (FF (Cof cl e)) :=
      mem_darts.2 ⟨(h.ff _ e).2 ⟨heC, he⟩, hv, h.nd e he⟩
    rw [(hhead e he v hv).2, (hgood _ hC).2.2 (v, e) hdart (piD_fix_iff.2 hfix),
      hdir _ hC v e hdart (piD_fix_iff.2 hfix)]
    simp only [m, List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    rw [decide_eq_of_iff (hidx v i t ht)]
  let τ : Sym2 V → Sym2 V := fun e => if pairAt (FF (Cof cl e)) v e = e then
    (m[pidx (m.idxOf e)]?).getD e else pairAt (FF (Cof cl e)) v e
  have key := card_filter_invol (Hp.filter (fun e => v ∈ e)) (fun e => gHead cl FF dir e = v) τ
    (by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haH, hva⟩ := ha
      obtain ⟨hC, haC⟩ := h.Cof_mem haH
      obtain ⟨C, hCdef⟩ : ∃ C, Cof cl a = C := ⟨_, rfl⟩
      rw [hCdef] at hC haC
      have hda : (v, a) ∈ darts (FF C) := mem_darts.2 ⟨(h.ff C a).2 ⟨haC, haH⟩, hva, h.nd a haH⟩
      by_cases hfix : pairAt (FF C) v a = a
      · have ham : a ∈ m := List.mem_map.2 ⟨_, h.ring_of_fix hC hda (piD_fix_iff.2 hfix), rfl⟩
        have hi : m.idxOf a < m.length := List.idxOf_lt_length_of_mem ham
        have hmi : m[m.idxOf a] = a := List.getElem_idxOf hi
        have hj : pidx (m.idxOf a) < m.length := pidx_lt hi hml
        have hτa : τ a = m[pidx (m.idxOf a)] := by
          simp only [τ, hCdef]; rw [if_pos hfix, List.getElem?_eq_getElem hj]; rfl
        have hbm : m[pidx (m.idxOf a)] ∈ m := List.getElem_mem hj
        obtain ⟨hbH, hvb, hfixb⟩ := hm_left _ hbm
        have hidxb : m.idxOf m[pidx (m.idxOf a)] = pidx (m.idxOf a) := hmn.idxOf_getElem _ hj
        have hτb : τ m[pidx (m.idxOf a)] = a := by
          simp only [τ]; rw [if_pos hfixb, hidxb, pidx_pidx, List.getElem?_eq_getElem hi, hmi]
          rfl
        refine ⟨hτa ▸ Finset.mem_filter.2 ⟨hbH, hvb⟩, by rw [hτa, hτb], ?_⟩
        rw [hτa, hfixP _ hbH hvb hfixb _ (List.getElem?_eq_getElem hj),
          hfixP a haH hva (by rw [hCdef]; exact hfix) (m.idxOf a)
            (by rw [List.getElem?_eq_getElem hi, hmi])]
        have hlen : m.length = (ringFam cl FF v).length := List.length_map _
        have hne := ringSpec_pidx hd v (hlen ▸ hj) (hlen ▸ hi)
        cases h1 : (d v).getD (m.idxOf a) false <;>
          cases h2 : (d v).getD (pidx (m.idxOf a)) false <;> simp_all
      · have hb := (pairAt_spec (FF C) v).1 a (mem_atV.2 hda)
        have hbd := mem_atV.1 hb.1
        have hb' := mem_darts.1 hbd
        have hbC := (h.ff C _).1 hb'.1
        have hCb : Cof cl (pairAt (FF C) v a) = C := h.Cof_eq hC hbC.1
        have hτa : τ a = pairAt (FF C) v a := by simp only [τ, hCdef]; rw [if_neg hfix]
        have hfixb : pairAt (FF C) v (pairAt (FF C) v a) ≠ pairAt (FF C) v a := by
          rw [hb.2]; exact fun h' => hfix h'.symm
        have hτb : τ (pairAt (FF C) v a) = a := by
          simp only [τ, hCb]; rw [if_neg hfixb, hb.2]
        refine ⟨hτa ▸ Finset.mem_filter.2 ⟨hbC.2, hb'.2.1⟩, by rw [hτa, hτb], ?_⟩
        rw [hτa, (hhead _ hbC.2 v hb'.2.1).2, (hhead a haH v hva).2, hCb, hCdef]
        have hne := (hgood C hC).2.1 (v, a) hda (by rw [Ne, piD_fix_iff]; exact hfix)
        simp only [piD] at hne
        cases h1 : colorOf (FF C) (dir C) (v, a) <;>
          cases h2 : colorOf (FF C) (dir C) (v, pairAt (FF C) v a) <;> simp_all)
  simpa only [Finset.filter_filter] using key

end FamOK

end Family

end APSP.Stoc
