import ApspStoc.Realizability

/-!
# Ring combinatorics for the ring-orientation protocol (`ringLE`, DESIGN7 §C.2)

Setting: ring data `r : V → RingIn V` with `RingWF cl S r`.

* An *end* is a pair `(v, i)` with `i < (r v).length` (the finset `ringDarts r`).
* `pairD (v, i) = (v, i xor 1)`: positions `2k, 2k+1` are paired at a node.
* `segPartner r (v, i)` (from `Realizability.lean`): the other end of the segment (link) at `(v, i)`.
* The *ring map* `sig r x = pairD (segPartner r x)`: a probe leaving through end `x` crosses the
  link, arrives at `segPartner r x` and leaves again through `sig r x`.
* An *element* is `E = (v, k)` with ends `evE E = (v, 2k)` and `odE E = (v, 2k+1)`
  (the finset `ringElems r`); `elemOf (v, i) = (v, i / 2)`. Elements are compared by their ID
  `eid E = (index of v, k)` (lexicographic).

Everything is stated for functions on `V × ℕ` (no subtypes), so that a protocol node, which only
knows its own ends, the entries `r v` and the probes it receives, can follow it step by step.

Main results:
* ring structure: `sigPerm` (σ is a permutation of the ends), `iter_pairD_iter` (σ from the two
  ends of an element runs around the ring in opposite directions), `iter_ne_pairD_iter` (the two
  directions are disjoint orbits), `per` (orbit length = ring length, `card_ringOf`), `rdist`
  (ring distance, `rdist_add_rdist_pairD`);
* the phased election `cand`, probes `hops`, `depEnd`, `arrEnd`, `flight`, `departs`, `Reach`,
  `Active`, `flightA`; local rules `forward_iff`, `reach_self_iff`, `active_iff_not_returned`,
  `mem_cand_succ_active`;
* bounds: `cand_sep` / `cand_sep_rdist` (3a), `card_departs_le_two` (3b),
  `card_flightA_mul` (3c, in the clean form `#probes · 2^i ≤ 4R`), `mem_cand_succ_of_decided`,
  `cand_final` (3d);
* orientation: `ringDir_spec : RingSpec r (ringDir r)`, `dir_crossed`, `max_probe_crosses`,
  `dir_of_max_probe`, `probe_le_ringMax`.
-/

namespace APSP.Stoc
namespace RingComb

open Finset Function

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Ends, pairing, partner and the ring map -/

/-- The end paired with `x = (v, i)` at its node: `(v, i xor 1)` (positions `2k`, `2k+1` form an
element). -/
def pairD (x : V × ℕ) : V × ℕ := (x.1, pairIdx x.2)

/-- The ring map on ends: a probe leaving through end `x` crosses the link to the partner end
`segPartner r x` and leaves again through the paired end `sig r x = pairD (segPartner r x)`. -/
def sig (r : V → RingIn V) (x : V × ℕ) : V × ℕ := pairD (segPartner r x)

/-- The element `(v, k)` of the end `(v, i)`: `k = i / 2`. -/
def elemOf (x : V × ℕ) : V × ℕ := (x.1, x.2 / 2)

/-- The even end `(v, 2k)` of the element `E = (v, k)`. -/
def evE (E : V × ℕ) : V × ℕ := (E.1, 2 * E.2)

/-- The odd end `(v, 2k+1)` of the element `E = (v, k)`. -/
def odE (E : V × ℕ) : V × ℕ := (E.1, 2 * E.2 + 1)

/-- All elements (node pairs) of the ring data. -/
noncomputable def ringElems (r : V → RingIn V) : Finset (V × ℕ) := (ringDarts r).image elemOf

/-- The ID of an element `E = (v, k)`: the pair `(index of v, k)`, ordered lexicographically. -/
noncomputable def eid (E : V × ℕ) : ℕ ×ₗ ℕ := toLex (((Fintype.equivFin V E.1 : Fin _) : ℕ), E.2)

section Basic

omit [Fintype V] [DecidableEq V]

@[simp] lemma pairD_fst (x : V × ℕ) : (pairD x).1 = x.1 := rfl

@[simp] lemma pairD_pairD (x : V × ℕ) : pairD (pairD x) = x := by
  simp [pairD, pairIdx_pairIdx]

lemma pairD_ne (x : V × ℕ) : pairD x ≠ x := by
  intro h; exact pairIdx_ne x.2 (congrArg Prod.snd h)

lemma pairD_injective : Injective (pairD : V × ℕ → V × ℕ) := fun x y h => by
  rw [← pairD_pairD x, h, pairD_pairD]

@[simp] lemma elemOf_pairD (x : V × ℕ) : elemOf (pairD x) = elemOf x := by
  simp only [elemOf, pairD, pairIdx, Prod.mk.injEq, true_and]; split_ifs <;> omega

@[simp] lemma elemOf_evE (E : V × ℕ) : elemOf (evE E) = E := by
  simp only [elemOf, evE]; ext <;> simp

@[simp] lemma elemOf_odE (E : V × ℕ) : elemOf (odE E) = E := by
  simp only [elemOf, odE]; ext <;> simp only; omega

lemma odE_eq_pairD (E : V × ℕ) : odE E = pairD (evE E) := by
  refine Prod.ext rfl ?_
  show 2 * E.2 + 1 = pairIdx (2 * E.2)
  unfold pairIdx; split_ifs <;> omega

lemma evE_eq_pairD (E : V × ℕ) : evE E = pairD (odE E) := by
  rw [odE_eq_pairD, pairD_pairD]

lemma evE_ne_odE (E : V × ℕ) : evE E ≠ odE E := by
  rw [odE_eq_pairD]; exact (pairD_ne _).symm

/-- the two ends of an element -/
lemma eq_evE_or_odE {x E : V × ℕ} (h : elemOf x = E) : x = evE E ∨ x = odE E := by
  subst h; obtain ⟨v, i⟩ := x
  simp only [evE, elemOf, odE, Prod.mk.injEq, true_and]; omega

lemma elemOf_eq_iff {x y : V × ℕ} : elemOf x = elemOf y ↔ x = y ∨ x = pairD y := by
  constructor
  · intro h
    obtain ⟨E, hE⟩ : ∃ E, elemOf y = E := ⟨_, rfl⟩
    rw [hE] at h
    rcases eq_evE_or_odE h with rfl | rfl <;> rcases eq_evE_or_odE hE with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (evE_eq_pairD E)
    · exact Or.inr (odE_eq_pairD E)
    · exact Or.inl rfl
  · rintro (h | h) <;> simp [h]

/-- the parity of an end: `evE` ends are even, `odE` ends are odd -/
lemma evE_snd_mod (E : V × ℕ) : (evE E).2 % 2 = 0 := by
  show (2 * E.2) % 2 = 0; omega

lemma odE_snd_mod (E : V × ℕ) : (odE E).2 % 2 = 1 := by
  show (2 * E.2 + 1) % 2 = 1; omega

end Basic

omit [DecidableEq V] in
lemma eid_injective : Injective (eid : V × ℕ → ℕ ×ₗ ℕ) := by
  intro E F h
  simp only [eid, toLex_inj, Prod.mk.injEq, Fin.val_inj] at h
  exact Prod.ext ((Fintype.equivFin V).injective h.1) h.2

variable {cl : Finset (Finset (Sym2 V))} {S : Finset V} {r : V → RingIn V}

/-- The segment partner is a fixed-point-free involution of the ends. -/
lemma part_props (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    segPartner r x ∈ ringDarts r ∧ segPartner r (segPartner r x) = x ∧ segPartner r x ≠ x := by
  obtain ⟨v, i⟩ := x
  rw [mem_ringDarts] at hx
  rcases hrv : (r v)[i] with ⟨e, x, e'⟩
  have hget : (r v)[i]? = some (e, x, e') := by rw [List.getElem?_eq_getElem hx, hrv]
  have hmem : (e, x, e') ∈ r v := hrv ▸ List.getElem_mem hx
  have hsym := hr.symm v e x e' hmem
  have hlt : (r x).idxOf (e', v, e) < (r x).length := List.idxOf_lt_length_of_mem hsym
  have hgetx : (r x)[(r x).idxOf (e', v, e)] = (e', v, e) := List.getElem_idxOf hlt
  rw [segPartner_of hget]
  refine ⟨mem_ringDarts.2 hlt, ?_, ?_⟩
  · rw [segPartner_of (by rw [List.getElem?_eq_getElem hlt, hgetx])]
    have := List.Nodup.idxOf_getElem (hr.nodup v) i hx
    rw [hrv] at this
    rw [this]
  · intro heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hxv, hidx⟩ := heq
    subst hxv
    have h1 : (r x)[i] = (e', x, e) := by
      have : (r x)[(r x).idxOf (e', x, e)] = (e', x, e) := hgetx
      simpa [hidx] using this
    have h2 : (r x)[i] = (e, x, e') := hrv
    rw [h1] at h2
    simp only [Prod.mk.injEq] at h2
    exact hr.ne x e x e' hmem (by rw [h2.1])

lemma part_mem (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    segPartner r x ∈ ringDarts r := (part_props hr hx).1

lemma part_part (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    segPartner r (segPartner r x) = x := (part_props hr hx).2.1

lemma part_ne (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    segPartner r x ≠ x := (part_props hr hx).2.2

/-- The partner is determined by the entries `r v`: if `(r v)[i] = (e, x, e')` and
`(r x)[i'] = (e', v, e)` then `segPartner r (v, i) = (x, i')`. -/
lemma segPartner_eq (hr : RingWF cl S r) {v x : V} {e e' : Sym2 V} {i i' : ℕ}
    (hv : (r v)[i]? = some (e, x, e')) (hx : (r x)[i']? = some (e', v, e)) :
    segPartner r (v, i) = (x, i') := by
  have hi' : i' < (r x).length := (List.getElem?_eq_some_iff.1 hx).1
  have hidx : (r x).idxOf (e', v, e) = i' := by
    obtain ⟨_, hxi⟩ := List.getElem?_eq_some_iff.1 hx
    rw [← hxi]; exact List.Nodup.idxOf_getElem (hr.nodup x) i' hi'
  rw [segPartner_of hv, hidx]

lemma pairD_mem (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    pairD x ∈ ringDarts r := mem_ringDarts.2 (pairIdx_lt (hr.even x.1) (mem_ringDarts.1 hx))

lemma pairD_mem_iff (hr : RingWF cl S r) {x : V × ℕ} :
    pairD x ∈ ringDarts r ↔ x ∈ ringDarts r :=
  ⟨fun h => pairD_pairD x ▸ pairD_mem hr h, pairD_mem hr⟩

lemma evE_mem_iff (hr : RingWF cl S r) {E : V × ℕ} :
    evE E ∈ ringDarts r ↔ odE E ∈ ringDarts r := by
  rw [odE_eq_pairD, pairD_mem_iff hr]

lemma mem_ringElems (hr : RingWF cl S r) {E : V × ℕ} :
    E ∈ ringElems r ↔ evE E ∈ ringDarts r := by
  unfold ringElems
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases eq_evE_or_odE (rfl : elemOf x = elemOf x) with h | h
    · rwa [← h]
    · rw [evE_mem_iff hr, ← h]; exact hx
  · intro h; exact ⟨_, h, elemOf_evE E⟩

/-- An element `(v, k)` exists iff `2k + 1 < (r v).length`. -/
lemma mem_ringElems' (hr : RingWF cl S r) {E : V × ℕ} :
    E ∈ ringElems r ↔ 2 * E.2 + 1 < (r E.1).length := by
  rw [mem_ringElems hr, mem_ringDarts]
  obtain ⟨m, hm⟩ := hr.even E.1
  simp only [evE]; omega

lemma elemOf_mem {x : V × ℕ} (hx : x ∈ ringDarts r) :
    elemOf x ∈ ringElems r := mem_image_of_mem _ hx

lemma mem_darts_of_elemOf (hr : RingWF cl S r) {x : V × ℕ} (hx : elemOf x ∈ ringElems r) :
    x ∈ ringDarts r := by
  rw [mem_ringElems hr] at hx
  rcases eq_evE_or_odE (rfl : elemOf x = elemOf x) with h | h
  · rwa [h]
  · rw [h, ← evE_mem_iff hr]; exact hx

omit [Fintype V] in
/-- the partner end in terms of the ring map -/
lemma part_eq_pairD_sig (x : V × ℕ) : segPartner r x = pairD (sig r x) := by
  simp [sig]

lemma sig_mem (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) : sig r x ∈ ringDarts r :=
  pairD_mem hr (part_mem hr hx)

lemma sig_inj (hr : RingWF cl S r) {x y : V × ℕ} (hx : x ∈ ringDarts r) (hy : y ∈ ringDarts r)
    (h : sig r x = sig r y) : x = y := by
  have := congrArg (segPartner r) (pairD_injective h)
  rwa [part_part hr hx, part_part hr hy] at this

/-- `σ ∘ pair ∘ σ = pair` on ends: the key identity behind the two directions of a ring. -/
lemma sig_pairD_sig (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    sig r (pairD (sig r x)) = pairD x := by
  simp only [sig, pairD_pairD, part_part hr hx]

/-- The arrival end of a link crossing determines the next departure end:
`sig r (segPartner r x) = pairD x`. -/
lemma sig_part (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    sig r (segPartner r x) = pairD x := by
  rw [part_eq_pairD_sig]; exact sig_pairD_sig hr hx

/-- **σ is a permutation of the ends** (inverse: `x ↦ segPartner r (pairD x)`). -/
noncomputable def sigPerm (hr : RingWF cl S r) : Equiv.Perm {x // x ∈ ringDarts r} where
  toFun x := ⟨sig r x.1, sig_mem hr x.2⟩
  invFun x := ⟨segPartner r (pairD x.1), part_mem hr (pairD_mem hr x.2)⟩
  left_inv x := Subtype.ext (by simp only [sig, pairD_pairD, part_part hr x.2])
  right_inv x := Subtype.ext (by
    simp only [sig, part_part hr (pairD_mem hr x.2), pairD_pairD])

@[simp] lemma sigPerm_apply (hr : RingWF cl S r) (x : {x // x ∈ ringDarts r}) :
    (sigPerm hr x).1 = sig r x.1 := rfl

lemma iter_mem (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (k : ℕ) :
    (sig r)^[k] x ∈ ringDarts r :=
  Set.MapsTo.iterate (f := sig r) (s := (ringDarts r : Set (V × ℕ)))
    (fun _ h => sig_mem hr h) k hx

lemma iter_inj (hr : RingWF cl S r) {x y : V × ℕ} (hx : x ∈ ringDarts r) (hy : y ∈ ringDarts r)
    {k : ℕ} (h : (sig r)^[k] x = (sig r)^[k] y) : x = y :=
  Set.InjOn.iterate (f := sig r) (s := (ringDarts r : Set (V × ℕ)))
    (fun _ ha _ hb h => sig_inj hr ha hb h) (fun _ h => sig_mem hr h) k hx hy h

lemma iter_perm (hr : RingWF cl S r) (x : {x // x ∈ ringDarts r}) (k : ℕ) :
    ((sigPerm hr ^ k) x).1 = (sig r)^[k] x.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, sigPerm_apply, ih, iterate_succ_apply']

/-- **Reversal**: `σ^k (pair (σ^k x)) = pair x`. Going `k` steps from the paired end of
`σ^k x` returns to the paired end of `x`: σ run from the two ends of an element traverses the ring
in opposite directions. -/
lemma iter_pairD_iter (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (k : ℕ) :
    (sig r)^[k] (pairD ((sig r)^[k] x)) = pairD x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : (sig r)^[k + 1] x = sig r ((sig r)^[k] x) := iterate_succ_apply' _ _ _
    rw [h1, iterate_succ_apply, sig_pairD_sig hr (iter_mem hr hx k), ih]

/-- Every end is a periodic point of σ. -/
lemma mem_periodicPts (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    x ∈ periodicPts (sig r) := by
  obtain ⟨m, n, hmn, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨(sig r)^[k] x, iter_mem hr hx k⟩ : {x // x ∈ ringDarts r}))
  simp only [Subtype.mk.injEq] at h
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · refine ⟨n - m, by omega, ?_⟩
    have : (sig r)^[m] ((sig r)^[n - m] x) = (sig r)^[m] x := by
      rw [← iterate_add_apply, show m + (n - m) = n by omega, h]
    exact iter_inj hr (iter_mem hr hx _) hx this
  · refine ⟨m - n, by omega, ?_⟩
    have : (sig r)^[n] ((sig r)^[m - n] x) = (sig r)^[n] x := by
      rw [← iterate_add_apply, show n + (m - n) = m by omega, h]
    exact iter_inj hr (iter_mem hr hx _) hx this


/-! ## Orbits: ring length, the two directions -/

/-- The orbit length of the end `x` under σ. It is the number of elements on the ring of `x`
(`card_ringOf`), the same for both directions (`per_pairD`). -/
noncomputable def per (r : V → RingIn V) (x : V × ℕ) : ℕ := minimalPeriod (sig r) x

lemma per_pos (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) : 0 < per r x :=
  minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts hr hx)

omit [Fintype V] in
lemma iter_per (r : V → RingIn V) (x : V × ℕ) : (sig r)^[per r x] x = x := iterate_minimalPeriod

omit [Fintype V] in
lemma iter_mod (r : V → RingIn V) (x : V × ℕ) (k : ℕ) :
    (sig r)^[k % per r x] x = (sig r)^[k] x := iterate_mod_minimalPeriod_eq

omit [Fintype V] in
lemma iter_eq_self_iff {x : V × ℕ} {k : ℕ} : (sig r)^[k] x = x ↔ per r x ∣ k :=
  isPeriodicPt_iff_minimalPeriod_dvd

omit [Fintype V] in
lemma iter_eq_iter_iff {x : V × ℕ} {j l : ℕ} (hj : j < per r x) (hl : l < per r x) :
    (sig r)^[j] x = (sig r)^[l] x ↔ j = l :=
  iterate_eq_iterate_iff_of_lt_minimalPeriod hj hl

lemma per_iter (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (k : ℕ) :
    per r ((sig r)^[k] x) = per r x :=
  minimalPeriod_apply_iterate (mem_periodicPts hr hx) k

/-- going back: `σ^k x` returns to `x` after some further steps -/
lemma iter_back (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (k : ℕ) :
    (sig r)^[per r x * k - k] ((sig r)^[k] x) = x := by
  have hp := per_pos hr hx
  rw [← iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k hp)]
  exact iter_eq_self_iff.2 (dvd_mul_right _ _)

/-- Both ends of an element have the same orbit length (the ring length). -/
lemma per_pairD (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    per r (pairD x) = per r x := by
  unfold per
  rw [minimalPeriod_eq_minimalPeriod_iff]
  have key : ∀ y ∈ ringDarts r, ∀ n, IsPeriodicPt (sig r) n y →
      IsPeriodicPt (sig r) n (pairD y) := by
    intro y hy n h
    have h' : (sig r)^[n] y = y := h
    have := iter_pairD_iter hr hy n
    rw [h'] at this
    exact this
  intro n
  exact ⟨fun h => by simpa using key _ (pairD_mem hr hx) n h, key x hx n⟩

/-- **The two directions are disjoint**: the orbit of an end never contains its paired end. -/
lemma iter_ne_pairD (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (k : ℕ) :
    (sig r)^[k] x ≠ pairD x := by
  intro h
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h1 := iter_pairD_iter hr hx m
    rw [← h, two_mul, iterate_add_apply (sig r) m m x] at h1
    exact pairD_ne _ (iter_inj hr (pairD_mem hr (iter_mem hr hx m)) (iter_mem hr hx m) h1)
  · have h1 := iter_pairD_iter hr hx (m + 1)
    rw [← h, show 2 * m + 1 = (m + 1) + m by ring, iterate_add_apply (sig r) (m + 1) m x] at h1
    have h2 := iter_inj hr (pairD_mem hr (iter_mem hr hx _)) (iter_mem hr hx m) h1
    rw [iterate_succ_apply', ← part_eq_pairD_sig] at h2
    exact part_ne hr (iter_mem hr hx m) h2

lemma iter_ne_pairD_iter (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (j l : ℕ) :
    (sig r)^[j] x ≠ pairD ((sig r)^[l] x) := by
  intro h
  rcases le_total l j with hlj | hjl
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlj
    rw [add_comm, iterate_add_apply] at h
    exact iter_ne_pairD hr (iter_mem hr hx l) d h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjl
    rw [add_comm, iterate_add_apply] at h
    have := congrArg pairD h
    rw [pairD_pairD] at this
    exact iter_ne_pairD hr (iter_mem hr hx j) d this.symm

/-- Along one direction, an element is visited through one end only. -/
lemma elemOf_iter_eq_iff (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (j l : ℕ) :
    elemOf ((sig r)^[j] x) = elemOf ((sig r)^[l] x) ↔ (sig r)^[j] x = (sig r)^[l] x := by
  rw [elemOf_eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (iter_ne_pairD_iter hr hx j l)
  · exact Or.inl

/-- **The other direction**: `j` steps from the paired end of `x` = the paired end of
`per - j` steps from `x`. -/
lemma iter_pairD (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) {j : ℕ}
    (hj : j ≤ per r x) : (sig r)^[j] (pairD x) = pairD ((sig r)^[per r x - j] x) := by
  have := iter_pairD_iter hr (iter_mem hr hx (per r x - j)) j
  rwa [← iterate_add_apply, show j + (per r x - j) = per r x by omega, iter_per] at this

/-- The elements visited from the odd end of `E` are those visited from the even end, in the
reverse order. -/
lemma elemOf_iter_odE (hr : RingWF cl S r) {E : V × ℕ} (hE : evE E ∈ ringDarts r) {j : ℕ}
    (hj : j ≤ per r (evE E)) :
    elemOf ((sig r)^[j] (odE E)) = elemOf ((sig r)^[per r (evE E) - j] (evE E)) := by
  rw [odE_eq_pairD, iter_pairD hr hE hj, elemOf_pairD]

/-! ## Rings -/

/-- The elements on the ring of the end `x` (those visited by σ from `x`). -/
noncomputable def ringOf (r : V → RingIn V) (x : V × ℕ) : Finset (V × ℕ) :=
  (range (per r x)).image (fun j => elemOf ((sig r)^[j] x))

lemma mem_ringOf (hr : RingWF cl S r) {x F : V × ℕ} (hx : x ∈ ringDarts r) :
    F ∈ ringOf r x ↔ ∃ j, elemOf ((sig r)^[j] x) = F := by
  unfold ringOf
  rw [mem_image]
  constructor
  · rintro ⟨j, -, h⟩; exact ⟨j, h⟩
  · rintro ⟨j, h⟩
    exact ⟨j % per r x, mem_range.2 (Nat.mod_lt _ (per_pos hr hx)), by rw [iter_mod]; exact h⟩

/-- **The ring length is the orbit length**: the ring of `x` has `per r x` elements. -/
lemma card_ringOf (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    (ringOf r x).card = per r x := by
  unfold ringOf
  rw [card_image_of_injOn, card_range]
  intro j hj l hl h
  simp only [coe_range, Set.mem_Iio] at hj hl
  exact (iter_eq_iter_iff hj hl).1 ((elemOf_iter_eq_iff hr hx j l).1 h)

lemma ringOf_subset (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    ringOf r x ⊆ ringElems r :=
  image_subset_iff.2 (fun j _ => elemOf_mem (iter_mem hr hx j))

/-- Finiteness: a ring has at most `R` elements. -/
lemma per_le_card (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    per r x ≤ (ringElems r).card :=
  card_ringOf hr hx ▸ card_le_card (ringOf_subset hr hx)

lemma self_mem_ringOf (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    elemOf x ∈ ringOf r x := (mem_ringOf hr hx).2 ⟨0, rfl⟩

lemma ringOf_iter (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) (k : ℕ) :
    ringOf r ((sig r)^[k] x) = ringOf r x := by
  ext F
  rw [mem_ringOf hr (iter_mem hr hx k), mem_ringOf hr hx]
  constructor
  · rintro ⟨j, h⟩; exact ⟨j + k, by rwa [iterate_add_apply]⟩
  · rintro ⟨j, h⟩
    exact ⟨j + (per r x * k - k), by rw [iterate_add_apply, iter_back hr hx]; exact h⟩

lemma ringOf_pairD_sub (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    ringOf r (pairD x) ⊆ ringOf r x := by
  intro F hF
  rw [mem_ringOf hr (pairD_mem hr hx)] at hF
  obtain ⟨j, rfl⟩ := hF
  rw [mem_ringOf hr hx]
  have hp := per_pos hr hx
  refine ⟨per r x - j % per r x, ?_⟩
  rw [← iter_mod r (pairD x) j, per_pairD hr hx, iter_pairD hr hx (Nat.mod_lt _ hp).le,
    elemOf_pairD]

/-- Both ends of an element lie on the same ring. -/
lemma ringOf_pairD (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    ringOf r (pairD x) = ringOf r x := by
  refine (ringOf_pairD_sub hr hx).antisymm ?_
  have := ringOf_pairD_sub hr (pairD_mem hr hx)
  rwa [pairD_pairD] at this

lemma ringOf_eq_of_mem (hr : RingWF cl S r) {x y : V × ℕ} (hx : x ∈ ringDarts r)
    (hy : y ∈ ringDarts r) (h : elemOf y ∈ ringOf r x) : ringOf r y = ringOf r x := by
  rw [mem_ringOf hr hx] at h
  obtain ⟨j, hj⟩ := h
  rcases elemOf_eq_iff.1 hj with h | h
  · rw [← h, ringOf_iter hr hx]
  · rw [← ringOf_pairD hr hy, ← h, ringOf_iter hr hx]

/-- The ring of the element `E` (the elements visited by σ from either end of `E`). -/
noncomputable def ringE (r : V → RingIn V) (E : V × ℕ) : Finset (V × ℕ) := ringOf r (evE E)

lemma ringOf_eq_ringE (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    ringOf r x = ringE r (elemOf x) := by
  unfold ringE
  obtain ⟨E, hE⟩ : ∃ E, elemOf x = E := ⟨_, rfl⟩
  rw [hE]
  rcases eq_evE_or_odE hE with rfl | rfl
  · rfl
  · rw [odE_eq_pairD, ringOf_pairD hr (by rwa [evE_mem_iff hr])]

lemma ringE_subset (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) :
    ringE r E ⊆ ringElems r := ringOf_subset hr ((mem_ringElems hr).1 hE)

lemma self_mem_ringE (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) :
    E ∈ ringE r E := by
  have := self_mem_ringOf hr ((mem_ringElems hr).1 hE)
  rwa [elemOf_evE] at this

/-- Membership in a ring is an equivalence: the rings partition the elements. -/
lemma ringE_eq (hr : RingWF cl S r) {E F : V × ℕ} (hE : E ∈ ringElems r) (hF : F ∈ ringE r E) :
    ringE r F = ringE r E :=
  ringOf_eq_of_mem hr ((mem_ringElems hr).1 hE)
    ((mem_ringElems hr).1 (ringE_subset hr hE hF)) (by rwa [elemOf_evE])

lemma mem_ringE_comm (hr : RingWF cl S r) {E F : V × ℕ} (hE : E ∈ ringElems r)
    (hF : F ∈ ringE r E) : E ∈ ringE r F := by
  rw [ringE_eq hr hE hF]; exact self_mem_ringE hr hE

/-- The ring length of the element `E` (number of elements on its ring). -/
lemma card_ringE (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) :
    (ringE r E).card = per r (evE E) := card_ringOf hr ((mem_ringElems hr).1 hE)

/-! ## Ring distance -/

/-- The ring distance from the end `a` to the element `F`, in the direction of `a`: the number of
links a probe leaving through `a` crosses until it arrives at `F` (`0` if `F` is the element of
`a`; meaningless if `F` is not on the ring of `a`). -/
noncomputable def rdist (r : V → RingIn V) (a F : V × ℕ) : ℕ :=
  sInf {j | elemOf ((sig r)^[j] a) = F}

lemma rdist_spec (hr : RingWF cl S r) {a F : V × ℕ} (ha : a ∈ ringDarts r)
    (hF : F ∈ ringOf r a) : elemOf ((sig r)^[rdist r a F] a) = F :=
  Nat.sInf_mem ((mem_ringOf hr ha).1 hF)

omit [Fintype V] in
lemma rdist_le {a F : V × ℕ} {j : ℕ} (h : elemOf ((sig r)^[j] a) = F) : rdist r a F ≤ j :=
  Nat.sInf_le h

lemma rdist_lt_per (hr : RingWF cl S r) {a F : V × ℕ} (ha : a ∈ ringDarts r)
    (hF : F ∈ ringOf r a) : rdist r a F < per r a := by
  have h := rdist_spec hr ha hF
  rw [← iter_mod] at h
  exact (rdist_le h).trans_lt (Nat.mod_lt _ (per_pos hr ha))

lemma rdist_eq (hr : RingWF cl S r) {a F : V × ℕ} (ha : a ∈ ringDarts r) {j : ℕ}
    (hj : j < per r a) (h : elemOf ((sig r)^[j] a) = F) : rdist r a F = j := by
  subst h
  have hF : elemOf ((sig r)^[j] a) ∈ ringOf r a := (mem_ringOf hr ha).2 ⟨j, rfl⟩
  have h2 := rdist_spec hr ha hF
  rw [elemOf_iter_eq_iff hr ha] at h2
  exact (iter_eq_iter_iff (rdist_lt_per hr ha hF) hj).1 h2

lemma rdist_eq_zero_iff (hr : RingWF cl S r) {a F : V × ℕ} (ha : a ∈ ringDarts r)
    (hF : F ∈ ringOf r a) : rdist r a F = 0 ↔ F = elemOf a := by
  constructor
  · intro h; have := rdist_spec hr ha hF; rw [h] at this; exact this.symm
  · rintro rfl; exact rdist_eq hr ha (per_pos hr ha) rfl

/-- **The two distances around a ring add up to the ring length.** -/
lemma rdist_add_rdist_pairD (hr : RingWF cl S r) {a F : V × ℕ} (ha : a ∈ ringDarts r)
    (hF : F ∈ ringOf r a) (hne : F ≠ elemOf a) :
    rdist r a F + rdist r (pairD a) F = per r a := by
  have h1 := rdist_lt_per hr ha hF
  have h0 : rdist r a F ≠ 0 := fun h => hne ((rdist_eq_zero_iff hr ha hF).1 h)
  have h2 : rdist r (pairD a) F = per r a - rdist r a F := by
    refine rdist_eq hr (pairD_mem hr ha) (by rw [per_pairD hr ha]; omega) ?_
    rw [iter_pairD hr ha (by omega), elemOf_pairD, show per r a - (per r a - rdist r a F) =
      rdist r a F by omega, rdist_spec hr ha hF]
  omega


/-! ## Ring maximum -/

/-- The element of `s` with the largest ID (`d` if `s` is empty). -/
noncomputable def maxEl (s : Finset (V × ℕ)) (d : V × ℕ) : V × ℕ :=
  if h : s.Nonempty then Classical.choose (s.exists_max_image eid h) else d

omit [DecidableEq V] in
lemma maxEl_spec {s : Finset (V × ℕ)} (h : s.Nonempty) (d : V × ℕ) :
    maxEl s d ∈ s ∧ ∀ F ∈ s, eid F ≤ eid (maxEl s d) := by
  unfold maxEl; rw [dite_eq_left h]; exact Classical.choose_spec (s.exists_max_image eid h)

omit [DecidableEq V] in
lemma maxEl_congr {s : Finset (V × ℕ)} (h : s.Nonempty) (d d' : V × ℕ) :
    maxEl s d = maxEl s d' := by
  unfold maxEl; rw [dite_eq_left h, dite_eq_left h]

/-- The maximum (largest ID) element of the ring of `E`. -/
noncomputable def ringMax (r : V → RingIn V) (E : V × ℕ) : V × ℕ := maxEl (ringE r E) E

lemma ringMax_mem (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) :
    ringMax r E ∈ ringE r E := (maxEl_spec ⟨E, self_mem_ringE hr hE⟩ E).1

lemma le_ringMax (hr : RingWF cl S r) {E F : V × ℕ} (hE : E ∈ ringElems r)
    (hF : F ∈ ringE r E) : eid F ≤ eid (ringMax r E) := (maxEl_spec ⟨E, self_mem_ringE hr hE⟩ E).2 F hF

lemma ringMax_eq (hr : RingWF cl S r) {E F : V × ℕ} (hE : E ∈ ringElems r) (hF : F ∈ ringE r E) :
    ringMax r F = ringMax r E := by
  unfold ringMax
  rw [ringE_eq hr hE hF]
  exact maxEl_congr ⟨E, self_mem_ringE hr hE⟩ F E

lemma ringMax_mem_elems (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) :
    ringMax r E ∈ ringElems r := ringE_subset hr hE (ringMax_mem hr hE)

lemma ringMax_ringMax (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) :
    ringMax r (ringMax r E) = ringMax r E := ringMax_eq hr hE (ringMax_mem hr hE)

lemma ringE_ringMax (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) :
    ringE r (ringMax r E) = ringE r E := ringE_eq hr hE (ringMax_mem hr hE)

/-- `F` is the maximum of its ring iff no element of the ring has a larger ID. -/
lemma eq_ringMax_iff (hr : RingWF cl S r) {E F : V × ℕ} (hE : E ∈ ringElems r)
    (hF : F ∈ ringE r E) : F = ringMax r E ↔ ∀ G ∈ ringE r E, eid G ≤ eid F := by
  constructor
  · rintro rfl G hG; exact le_ringMax hr hE hG
  · intro h
    exact eid_injective (le_antisymm (le_ringMax hr hE hF) (h _ (ringMax_mem hr hE)))

/-! ## Probes and the phased election

In phase `i`, every candidate `E` sends one probe out of each of its ends `a ∈ {evE E, odE E}`.
The probe from `a` crosses `hops r i a = min (2^i) (per r a)` links: at *link step* `k`
(`k < hops r i a`) it departs from the end `(sig r)^[k] a` and arrives at the end
`segPartner r ((sig r)^[k] a)`, from where it departs again (at step `k+1`) through the paired end
(`iter_succ_eq`). It stops after `2^i` links or when it is back at its originator (after `per`
links, arriving at the other end of the originator, `part_iter_pred`). A node can decide locally
whether to forward (`forward_iff`). -/

/-- The number of links the phase-`i` probe from the end `a` crosses: `min (2^i) (per r a)`. -/
noncomputable def hops (r : V → RingIn V) (i : ℕ) (a : V × ℕ) : ℕ := min (2 ^ i) (per r a)

/-- The phase-`i` probe leaving through `a` arrives (at some link step) at an end of the element
`F`. -/
def Reach (r : V → RingIn V) (i : ℕ) (a F : V × ℕ) : Prop :=
  ∃ k < hops r i a, elemOf (segPartner r ((sig r)^[k] a)) = F

open Classical in
/-- The candidates of phase `i`: all elements in phase `0`; a candidate of phase `i` remains a
candidate in phase `i + 1` iff it receives no phase-`i` probe of a candidate with a larger ID. -/
noncomputable def cand (r : V → RingIn V) : ℕ → Finset (V × ℕ)
  | 0 => ringElems r
  | i + 1 => (cand r i).filter (fun F => ∀ E ∈ cand r i, eid F < eid E →
      ¬ Reach r i (evE E) F ∧ ¬ Reach r i (odE E) F)

/-- The departure end of the probe with origin end `a` at link step `k`: `σ^k a`. -/
abbrev depEnd (r : V → RingIn V) (a : V × ℕ) (k : ℕ) : V × ℕ := (sig r)^[k] a

/-- The arrival end of the probe with origin end `a` at link step `k`: the partner of its
departure end. -/
abbrev arrEnd (r : V → RingIn V) (a : V × ℕ) (k : ℕ) : V × ℕ := segPartner r (depEnd r a k)

/-- The probes in flight at link step `k` of phase `i`, identified by their origin end `a` (the
probe departs from `depEnd r a k = (sig r)^[k] a` and arrives at
`arrEnd r a k = segPartner r ((sig r)^[k] a)`). -/
noncomputable def flight (r : V → RingIn V) (i k : ℕ) : Finset (V × ℕ) :=
  open Classical in (ringDarts r).filter (fun a => elemOf a ∈ cand r i ∧ k < hops r i a)

/-- The origins of the phase-`i` probes that depart from the end `x` (at some link step), i.e.
that cross the link of `x` in the direction `x → segPartner r x`. -/
noncomputable def departs (r : V → RingIn V) (i : ℕ) (x : V × ℕ) : Finset (V × ℕ) :=
  open Classical in (ringDarts r).filter (fun a => elemOf a ∈ cand r i ∧
    ∃ k < hops r i a, (sig r)^[k] a = x)

/-- The ring of the end `a` is not yet decided before phase `i` (it is decided after phase `j`
iff `per r a ≤ 2^j`, see `active_iff`): candidates of decided rings send nothing. -/
def Active (r : V → RingIn V) (i : ℕ) (a : V × ℕ) : Prop := i = 0 ∨ 2 ^ (i - 1) < per r a

/-- The probes in flight at link step `k` of phase `i` when candidates of decided rings stop. -/
noncomputable def flightA (r : V → RingIn V) (i k : ℕ) : Finset (V × ℕ) :=
  open Classical in (flight r i k).filter (Active r i)

omit [Fintype V] in
/-- The next departure end is the end paired with the arrival end. -/
lemma iter_succ_eq (a : V × ℕ) (k : ℕ) :
    (sig r)^[k + 1] a = pairD (segPartner r ((sig r)^[k] a)) := iterate_succ_apply' _ _ _

omit [Fintype V] in
lemma depEnd_zero (a : V × ℕ) : depEnd r a 0 = a := rfl

omit [Fintype V] in
/-- Forwarding: the departure end at step `k + 1` is the end paired with the arrival end at step
`k` (at the same node). -/
lemma depEnd_succ (a : V × ℕ) (k : ℕ) : depEnd r a (k + 1) = pairD (arrEnd r a k) :=
  iter_succ_eq a k

lemma depEnd_mem (hr : RingWF cl S r) {a : V × ℕ} (ha : a ∈ ringDarts r) (k : ℕ) :
    depEnd r a k ∈ ringDarts r := iter_mem hr ha k

lemma arrEnd_mem (hr : RingWF cl S r) {a : V × ℕ} (ha : a ∈ ringDarts r) (k : ℕ) :
    arrEnd r a k ∈ ringDarts r := part_mem hr (iter_mem hr ha k)

omit [Fintype V] in
lemma elemOf_part_iter (a : V × ℕ) (k : ℕ) :
    elemOf (segPartner r ((sig r)^[k] a)) = elemOf ((sig r)^[k + 1] a) := by
  rw [iter_succ_eq, elemOf_pairD]

/-- After `per` links the probe arrives at the other end of its originator. -/
lemma part_iter_pred (hr : RingWF cl S r) {a : V × ℕ} (ha : a ∈ ringDarts r) :
    segPartner r ((sig r)^[per r a - 1] a) = pairD a := by
  have h := iter_succ_eq (r := r) a (per r a - 1)
  rw [Nat.sub_add_cancel (per_pos hr ha), iter_per] at h
  have := congrArg pairD h
  rw [pairD_pairD] at this
  exact this.symm

lemma hops_pos (hr : RingWF cl S r) {a : V × ℕ} (ha : a ∈ ringDarts r) (i : ℕ) :
    0 < hops r i a := lt_min (Nat.two_pow_pos i) (per_pos hr ha)

omit [Fintype V] in
lemma hops_le_per (i : ℕ) (a : V × ℕ) : hops r i a ≤ per r a := min_le_right _ _

omit [Fintype V] in
lemma hops_le_pow (i : ℕ) (a : V × ℕ) : hops r i a ≤ 2 ^ i := min_le_left _ _

lemma hops_pairD (hr : RingWF cl S r) {a : V × ℕ} (ha : a ∈ ringDarts r) (i : ℕ) :
    hops r i (pairD a) = hops r i a := by simp only [hops, per_pairD hr ha]

/-- **Local forwarding rule.** The probe from `a` that arrived at link step `k` at the end
`y = segPartner r ((sig r)^[k] a)` is forwarded (from `pairD y`, at step `k + 1`) iff
`k + 1 < 2^i` and `y` is not an end of the originator. -/
lemma forward_iff (hr : RingWF cl S r) {a : V × ℕ} (ha : a ∈ ringDarts r) {i k : ℕ}
    (hk : k < hops r i a) :
    k + 1 < hops r i a ↔
      k + 1 < 2 ^ i ∧ elemOf (segPartner r ((sig r)^[k] a)) ≠ elemOf a := by
  have hkp : k < per r a := hk.trans_le (hops_le_per i a)
  rw [elemOf_part_iter, Ne, show elemOf a = elemOf ((sig r)^[0] a) from rfl,
    elemOf_iter_eq_iff hr ha, iterate_zero_apply, iter_eq_self_iff]
  unfold hops
  rw [lt_min_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases Nat.lt_or_ge (k + 1) (per r a) with h | h
    · exact h
    · exact absurd (by rw [show k + 1 = per r a by omega]) h2

omit [Fintype V] in
/-- `Reach` in terms of the visited elements: the probe from `a` visits the elements
`elemOf ((sig r)^[j] a)` for `1 ≤ j ≤ hops`. -/
lemma reach_iff {i : ℕ} {a F : V × ℕ} :
    Reach r i a F ↔ ∃ j, 1 ≤ j ∧ j ≤ hops r i a ∧ elemOf ((sig r)^[j] a) = F := by
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k + 1, by omega, hk, by rw [← elemOf_part_iter]; exact h⟩
  · rintro ⟨j, hj1, hj2, h⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj1
    exact ⟨k, hj2, by rw [elemOf_part_iter]; exact h⟩

/-- Probes stay on their ring. -/
lemma reach_mem_ringOf (hr : RingWF cl S r) {i : ℕ} {a F : V × ℕ} (ha : a ∈ ringDarts r)
    (h : Reach r i a F) : F ∈ ringOf r a := by
  obtain ⟨j, -, -, h⟩ := reach_iff.1 h
  exact (mem_ringOf hr ha).2 ⟨j, h⟩

/-- An element `F ≠ elemOf a` within distance `2^i` of `a` (in the direction of `a`) is reached
by the phase-`i` probe from `a`. -/
lemma reach_of (hr : RingWF cl S r) {i : ℕ} {a F : V × ℕ} (ha : a ∈ ringDarts r) {j : ℕ}
    (hj2 : j ≤ 2 ^ i) (h : elemOf ((sig r)^[j] a) = F) (hne : F ≠ elemOf a) : Reach r i a F := by
  have hp := per_pos hr ha
  refine reach_iff.2 ⟨j % per r a, ?_, ?_, by rw [iter_mod]; exact h⟩
  · by_contra h0
    have : j % per r a = 0 := by omega
    rw [← iter_mod, this] at h
    exact hne h.symm
  · exact le_min ((Nat.mod_le _ _).trans hj2) (Nat.mod_lt _ hp).le

/-- **Return**: the phase-`i` probe of `a` returns to its originator iff `per r a ≤ 2^i`. -/
lemma reach_self_iff (hr : RingWF cl S r) {i : ℕ} {a : V × ℕ} (ha : a ∈ ringDarts r) :
    Reach r i a (elemOf a) ↔ per r a ≤ 2 ^ i := by
  constructor
  · intro h
    obtain ⟨j, hj1, hj2, h⟩ := reach_iff.1 h
    rw [show elemOf a = elemOf ((sig r)^[0] a) from rfl, elemOf_iter_eq_iff hr ha,
      iterate_zero_apply, iter_eq_self_iff] at h
    exact (Nat.le_of_dvd (by omega) h).trans (hj2.trans (hops_le_pow i a))
  · intro h
    exact reach_iff.2 ⟨per r a, per_pos hr ha, le_min h le_rfl, by rw [iter_per]⟩

/-- symmetry of visits: if `F` is `j` steps from `a`, then the element of `a` is `j` steps from the
end `pairD ((sig r)^[j] a)` of `F` -/
lemma visit_symm (hr : RingWF cl S r) {a : V × ℕ} (ha : a ∈ ringDarts r) (j : ℕ) :
    elemOf (pairD ((sig r)^[j] a)) = elemOf ((sig r)^[j] a) ∧
      elemOf ((sig r)^[j] (pairD ((sig r)^[j] a))) = elemOf a := by
  rw [iter_pairD_iter hr ha, elemOf_pairD, elemOf_pairD]; exact ⟨rfl, rfl⟩


/-! ## Candidates -/

lemma cand_zero : cand r 0 = ringElems r := rfl

lemma mem_cand_succ {i : ℕ} {F : V × ℕ} :
    F ∈ cand r (i + 1) ↔ F ∈ cand r i ∧ ∀ E ∈ cand r i, eid F < eid E →
      ¬ Reach r i (evE E) F ∧ ¬ Reach r i (odE E) F := by
  simp only [cand, mem_filter]

lemma cand_succ_subset (i : ℕ) : cand r (i + 1) ⊆ cand r i :=
  fun _ hF => (mem_cand_succ.1 hF).1

/-- The candidate sets decrease. -/
lemma cand_anti {i j : ℕ} (h : i ≤ j) : cand r j ⊆ cand r i := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (cand_succ_subset _).trans ih

lemma cand_subset (i : ℕ) : cand r i ⊆ ringElems r := cand_anti (Nat.zero_le i)

/-- **Survival rule, distance form.** `F` survives phase `i` iff no larger phase-`i` candidate lies
within ring distance `2^i` of `F` in either direction (`b` ranges over both ends of `F`). -/
lemma mem_cand_succ_iff (hr : RingWF cl S r) {i : ℕ} {F : V × ℕ} :
    F ∈ cand r (i + 1) ↔ F ∈ cand r i ∧ ∀ E ∈ cand r i, eid F < eid E →
      ∀ b, elemOf b = F → ∀ j, 1 ≤ j → j ≤ 2 ^ i → elemOf ((sig r)^[j] b) ≠ E := by
  rw [mem_cand_succ]
  refine and_congr_right fun hF => forall₂_congr fun E hE => imp_congr_right fun hlt => ?_
  have hFE : F ≠ E := fun h => lt_irrefl _ (h ▸ hlt)
  constructor
  · rintro ⟨h1, h2⟩ b hb j hj1 hj2 hj
    have hbm : b ∈ ringDarts r := mem_darts_of_elemOf hr (hb ▸ cand_subset i hF)
    obtain ⟨hs1, hs2⟩ := visit_symm hr hbm j
    have hreach : Reach r i (pairD ((sig r)^[j] b)) F := by
      refine reach_of hr (pairD_mem hr (iter_mem hr hbm j)) hj2 (by rw [hs2, hb]) ?_
      rw [hs1, hj]; exact hFE
    rcases eq_evE_or_odE (hs1.trans hj) with h | h
    · rw [h] at hreach; exact h1 hreach
    · rw [h] at hreach; exact h2 hreach
  · intro h
    have key : ∀ a, elemOf a = E → ¬ Reach r i a F := by
      intro a ha hre
      obtain ⟨j, hj1, hj2, hj⟩ := reach_iff.1 hre
      have ham : a ∈ ringDarts r := mem_darts_of_elemOf hr (ha ▸ cand_subset i hE)
      obtain ⟨hs1, hs2⟩ := visit_symm hr ham j
      exact h _ (hs1.trans hj) j hj1 (hj2.trans (hops_le_pow i a)) (hs2.trans ha)
    exact ⟨key _ (elemOf_evE E), key _ (elemOf_odE E)⟩

/-- **The maximum of a ring is a candidate in every phase.** -/
lemma ringMax_mem_cand (hr : RingWF cl S r) {E : V × ℕ} (hE : E ∈ ringElems r) (i : ℕ) :
    ringMax r E ∈ cand r i := by
  induction i with
  | zero => exact ringMax_mem_elems hr hE
  | succ i ih =>
    rw [mem_cand_succ]
    refine ⟨ih, fun G hG hlt => ?_⟩
    have hGe := cand_subset i hG
    have key : ∀ a, elemOf a = G → ¬ Reach r i a (ringMax r E) := by
      intro a ha hre
      have ham : a ∈ ringDarts r := mem_darts_of_elemOf hr (ha ▸ hGe)
      have h1 := reach_mem_ringOf hr ham hre
      rw [ringOf_eq_ringE hr ham, ha] at h1
      have h2 := mem_ringE_comm hr hGe h1
      rw [ringE_ringMax hr hE] at h2
      exact absurd (le_ringMax hr hE h2) (not_le.2 hlt)
    exact ⟨key _ (elemOf_evE G), key _ (elemOf_odE G)⟩

/-- **(3a) Separation.** For `i ≥ 1`, no phase-`i` candidate `F` lies within ring distance
`2^(i-1)` of another phase-`i` candidate `E`, in either direction (`a` is either end of `E`). -/
theorem cand_sep (hr : RingWF cl S r) {i : ℕ} (hi : 1 ≤ i) {E F : V × ℕ} (hE : E ∈ cand r i)
    (hF : F ∈ cand r i) (hEF : E ≠ F) {a : V × ℕ} (ha : elemOf a = E) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j ≤ 2 ^ (i - 1)) : elemOf ((sig r)^[j] a) ≠ F := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  simp only [Nat.add_sub_cancel] at hj2
  intro hj
  rcases lt_or_gt_of_ne (fun h => hEF (eid_injective h) : eid E ≠ eid F) with hlt | hlt
  · exact ((mem_cand_succ_iff hr).1 hE).2 F (cand_succ_subset i hF) hlt a ha j hj1 hj2 hj
  · have ham : a ∈ ringDarts r := mem_darts_of_elemOf hr (ha ▸ cand_subset _ hE)
    have hre : Reach r i a F := reach_of hr ham hj2 hj (by rw [ha]; exact hEF.symm)
    have := (mem_cand_succ.1 hF).2 E (cand_succ_subset i hE) hlt
    rcases eq_evE_or_odE ha with rfl | rfl
    · exact this.1 hre
    · exact this.2 hre

/-- **(3a) Separation, distance form**: two distinct phase-`i` candidates (`i ≥ 1`) on the same
ring are at ring distance `> 2^(i-1)` in both directions. -/
theorem cand_sep_rdist (hr : RingWF cl S r) {i : ℕ} (hi : 1 ≤ i) {E F : V × ℕ}
    (hE : E ∈ cand r i) (hF : F ∈ cand r i) (hEF : E ≠ F) (hring : F ∈ ringE r E) {a : V × ℕ}
    (ha : elemOf a = E) : 2 ^ (i - 1) < rdist r a F := by
  have ham : a ∈ ringDarts r := mem_darts_of_elemOf hr (ha ▸ cand_subset _ hE)
  have hFa : F ∈ ringOf r a := by rw [ringOf_eq_ringE hr ham, ha]; exact hring
  by_contra hle
  push Not at hle
  have h0 : rdist r a F ≠ 0 := fun h => hEF (((rdist_eq_zero_iff hr ham hFa).1 h).trans ha).symm
  exact cand_sep hr hi hE hF hEF ha (by omega) hle (rdist_spec hr ham hFa)

/-! ## (3b) Probes per end -/

lemma mem_departs {i : ℕ} {x a : V × ℕ} :
    a ∈ departs r i x ↔ a ∈ ringDarts r ∧ elemOf a ∈ cand r i ∧
      ∃ k < hops r i a, (sig r)^[k] a = x := by
  simp only [departs, mem_filter]

lemma mem_flight {i k : ℕ} {a : V × ℕ} :
    a ∈ flight r i k ↔ a ∈ ringDarts r ∧ elemOf a ∈ cand r i ∧ k < hops r i a := by
  simp only [flight, mem_filter]

/-- At a single link step, every end is the departure end of at most one probe. -/
lemma flight_dep_inj (hr : RingWF cl S r) {i k : ℕ} {a b : V × ℕ} (ha : a ∈ flight r i k)
    (hb : b ∈ flight r i k) (h : (sig r)^[k] a = (sig r)^[k] b) : a = b :=
  iter_inj hr (mem_flight.1 ha).1 (mem_flight.1 hb).1 h

omit [Fintype V] in
/-- A probe departs from a given end at most once per phase. -/
lemma dep_step_unique {i : ℕ} {a x : V × ℕ} {k l : ℕ} (hk : k < hops r i a) (hl : l < hops r i a)
    (h1 : (sig r)^[k] a = x) (h2 : (sig r)^[l] a = x) : k = l :=
  (iter_eq_iter_iff (hk.trans_le (hops_le_per i a)) (hl.trans_le (hops_le_per i a))).1
    (h1.trans h2.symm)

/-- Two distinct probes departing from the same end in phase `i ≥ 1` do so at link steps more than
`2^(i-1)` apart. -/
lemma departs_sep (hr : RingWF cl S r) {i : ℕ} (hi : 1 ≤ i) {x a b : V × ℕ}
    (ha : a ∈ departs r i x) (hb : b ∈ departs r i x) (hab : a ≠ b) {k l : ℕ}
    (hka : (sig r)^[k] a = x) (hlb : (sig r)^[l] b = x) (hkl : k ≤ l) : k + 2 ^ (i - 1) < l := by
  obtain ⟨ham, haC, -⟩ := mem_departs.1 ha
  obtain ⟨hbm, hbC, -⟩ := mem_departs.1 hb
  have hba : (sig r)^[l - k] b = a := by
    apply iter_inj hr (iter_mem hr hbm _) ham (k := k)
    rw [← iterate_add_apply, show k + (l - k) = l by omega, hlb, hka]
  have hd : l - k ≠ 0 := fun h => hab (by rw [← hba, h]; rfl)
  have hne : elemOf b ≠ elemOf a := by
    intro h
    rcases elemOf_eq_iff.1 h with h | h
    · exact hab h.symm
    · apply iter_ne_pairD hr hbm (l - k)
      rw [hba, h, pairD_pairD]
  by_contra hcon
  exact cand_sep hr hi hbC haC hne rfl (j := l - k) (by omega) (by omega) (by rw [hba])

/-- **(3b) At most two probes per end and phase**: in phase `i`, every end is the departure end of
at most two probes, i.e. every link carries at most two probes per direction and phase. -/
theorem card_departs_le_two (hr : RingWF cl S r) (i : ℕ) (x : V × ℕ) :
    (departs r i x).card ≤ 2 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine (card_le_one.2 ?_).trans (by norm_num)
    intro a ha b hb
    obtain ⟨-, -, k, hk, hka⟩ := mem_departs.1 ha
    obtain ⟨-, -, l, hl, hlb⟩ := mem_departs.1 hb
    have h1 := hops_le_pow (r := r) 0 a
    have h2 := hops_le_pow (r := r) 0 b
    rw [pow_zero] at h1 h2
    have hk0 : k = 0 := by omega
    have hl0 : l = 0 := by omega
    subst hk0 hl0
    exact hka.trans hlb.symm
  · by_contra hcon
    rw [not_le, two_lt_card] at hcon
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hcon
    have sep : ∀ {a b}, a ∈ departs r i x → b ∈ departs r i x → a ≠ b → ∀ {k l : ℕ},
        (sig r)^[k] a = x → (sig r)^[l] b = x → k + 2 ^ (i - 1) < l ∨ l + 2 ^ (i - 1) < k := by
      intro a b ha hb hab k l hka hlb
      rcases le_total k l with h | h
      · exact Or.inl (departs_sep hr hi ha hb hab hka hlb h)
      · exact Or.inr (departs_sep hr hi hb ha hab.symm hlb hka h)
    obtain ⟨-, -, k1, hk1, h1⟩ := mem_departs.1 ha
    obtain ⟨-, -, k2, hk2, h2⟩ := mem_departs.1 hb
    obtain ⟨-, -, k3, hk3, h3⟩ := mem_departs.1 hc
    have b1 := hk1.trans_le (hops_le_pow i a)
    have b2 := hk2.trans_le (hops_le_pow i b)
    have b3 := hk3.trans_le (hops_le_pow i c)
    have s12 := sep ha hb hab h1 h2
    have s13 := sep ha hc hac h1 h3
    have s23 := sep hb hc hbc h2 h3
    have hpow : 2 ^ i = 2 * 2 ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- The probes arriving at the end `y` (in phase `i`, at some link step) are exactly those
departing from its partner. -/
lemma arrive_iff (hr : RingWF cl S r) {y z : V × ℕ} (hy : y ∈ ringDarts r)
    (hz : z ∈ ringDarts r) : segPartner r z = y ↔ z = segPartner r y :=
  ⟨fun h => by rw [← h, part_part hr hz], fun h => by rw [h, part_part hr hy]⟩

/-- **(3b) for arrivals**: at most two phase-`i` probes arrive at any end. -/
theorem card_arrives_le_two (hr : RingWF cl S r) (i : ℕ) {y : V × ℕ} (hy : y ∈ ringDarts r) :
    ((ringDarts r).filter (fun a => elemOf a ∈ cand r i ∧
      ∃ k < hops r i a, segPartner r ((sig r)^[k] a) = y)).card ≤ 2 := by
  refine le_trans (card_le_card ?_) (card_departs_le_two hr i (segPartner r y))
  intro a ha
  simp only [mem_filter] at ha
  obtain ⟨ham, hc, k, hk, h⟩ := ha
  exact mem_departs.2 ⟨ham, hc, k, hk, (arrive_iff hr hy (iter_mem hr ham k)).1 h⟩

/-! ## (3c) Probes in flight -/

omit [Fintype V] in
/-- `Active` = no earlier phase decided the ring. -/
lemma active_iff {i : ℕ} {a : V × ℕ} : Active r i a ↔ ∀ j < i, 2 ^ j < per r a := by
  unfold Active
  constructor
  · rintro (rfl | h) j hj
    · omega
    · exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) h
  · intro h
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (h _ (by omega))

/-- `Active` in protocol terms: the originator's probe did not return in an earlier phase. -/
lemma active_iff_not_returned (hr : RingWF cl S r) {i : ℕ} {a : V × ℕ} (ha : a ∈ ringDarts r) :
    Active r i a ↔ ∀ j < i, ¬ Reach r j a (elemOf a) := by
  rw [active_iff]
  exact forall₂_congr fun j _ => by rw [reach_self_iff hr ha, not_le]

lemma active_pairD (hr : RingWF cl S r) {i : ℕ} {a : V × ℕ} (ha : a ∈ ringDarts r) :
    Active r i (pairD a) ↔ Active r i a := by
  simp only [Active, per_pairD hr ha]

/-- The ends of active candidates: the origins of the probes of phase `i` when the candidates of
rings decided before phase `i` send nothing. -/
noncomputable def activeEnds (r : V → RingIn V) (i : ℕ) : Finset (V × ℕ) :=
  open Classical in (ringDarts r).filter (fun a => elemOf a ∈ cand r i ∧ Active r i a)

lemma mem_activeEnds {i : ℕ} {a : V × ℕ} :
    a ∈ activeEnds r i ↔ a ∈ ringDarts r ∧ elemOf a ∈ cand r i ∧ Active r i a := by
  simp only [activeEnds, mem_filter]

lemma flightA_subset (i k : ℕ) : flightA r i k ⊆ activeEnds r i := by
  intro a ha
  simp only [flightA, mem_filter] at ha
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h1, h3, -⟩ := mem_flight.1 h1
  exact mem_activeEnds.2 ⟨h1, h3, h2⟩

/-- Every element has exactly two ends: `#ends = 2 R`. -/
lemma card_darts (hr : RingWF cl S r) : (ringDarts r).card = 2 * (ringElems r).card := by
  rw [card_eq_sum_card_fiberwise (f := elemOf) (t := ringElems r) (fun x hx => elemOf_mem hx)]
  rw [sum_const_nat (m := 2), mul_comm]
  intro E hE
  have h1 := (mem_ringElems hr).1 hE
  have h2 := (evE_mem_iff hr).1 h1
  have : (ringDarts r).filter (fun x => elemOf x = E) = {evE E, odE E} := by
    ext x
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨-, h⟩; exact eq_evE_or_odE h
    · rintro (rfl | rfl)
      · exact ⟨h1, elemOf_evE E⟩
      · exact ⟨h2, elemOf_odE E⟩
  rw [this, card_pair (evE_ne_odE E)]

/-- the windows of length `2^(i-1)` in front of distinct active candidate ends are disjoint -/
lemma active_window_disj (hr : RingWF cl S r) {i : ℕ} {a b : V × ℕ} (ha : a ∈ activeEnds r i)
    (hb : b ∈ activeEnds r i) {j l : ℕ} (hj : j < 2 ^ (i - 1)) (h : (sig r)^[j] a = (sig r)^[l] b)
    (hlj : l ≤ j) : a = b := by
  obtain ⟨ham, haC, -⟩ := mem_activeEnds.1 ha
  obtain ⟨hbm, hbC, -⟩ := mem_activeEnds.1 hb
  have hab : (sig r)^[j - l] a = b := by
    apply iter_inj hr (iter_mem hr ham _) hbm (k := l)
    rw [← iterate_add_apply, show l + (j - l) = j by omega, h]
  by_cases hd : j - l = 0
  · rw [hd] at hab; exact hab
  have hi : 1 ≤ i := by
    by_contra h0
    have : i = 0 := by omega
    subst this
    simp at hj
    omega
  by_contra hne
  have hne' : elemOf a ≠ elemOf b := by
    intro h
    rcases elemOf_eq_iff.1 h with h | h
    · exact hne h
    · apply iter_ne_pairD hr ham (j - l)
      rw [hab, h, pairD_pairD]
  exact cand_sep hr hi haC hbC hne' rfl (j := j - l) (by omega) (by omega) (by rw [hab])

lemma card_activeEnds_mul (hr : RingWF cl S r) (i : ℕ) :
    (activeEnds r i).card * 2 ^ (i - 1) ≤ (ringDarts r).card := by
  set P := 2 ^ (i - 1) with hPdef
  let W : V × ℕ → Finset (V × ℕ) := fun a => (range P).image (fun j => (sig r)^[j] a)
  have hW : ∀ a ∈ activeEnds r i, (W a).card = P := by
    intro a ha
    obtain ⟨ham, -, hact⟩ := mem_activeEnds.1 ha
    have hP : P ≤ per r a := by
      rcases hact with h0 | h
      · subst h0; have := per_pos hr ham; simp only [hPdef, zero_tsub, pow_zero]; omega
      · exact h.le
    rw [card_image_of_injOn, card_range]
    intro j hj l hl h
    simp only [coe_range, Set.mem_Iio] at hj hl
    exact (iter_eq_iter_iff (by omega) (by omega)).1 h
  have hdisj : (activeEnds r i : Set (V × ℕ)).PairwiseDisjoint W := by
    intro a ha b hb hab
    rw [Function.onFun, disjoint_left]
    intro y hya hyb
    simp only [W, mem_image, mem_range] at hya hyb
    obtain ⟨j, hj, rfl⟩ := hya
    obtain ⟨l, hl, hjl⟩ := hyb
    rcases le_total l j with h | h
    · exact hab (active_window_disj hr ha hb hj hjl.symm h)
    · exact hab (active_window_disj hr hb ha hl hjl h).symm
  have hsub : (activeEnds r i).biUnion W ⊆ ringDarts r := by
    intro y hy
    simp only [mem_biUnion] at hy
    obtain ⟨a, ha, hy⟩ := hy
    simp only [W, mem_image] at hy
    obtain ⟨j, -, rfl⟩ := hy
    exact iter_mem hr (mem_activeEnds.1 ha).1 j
  calc (activeEnds r i).card * P = ∑ a ∈ activeEnds r i, (W a).card := by
        rw [sum_congr rfl hW, sum_const, smul_eq_mul]
    _ = ((activeEnds r i).biUnion W).card := (card_biUnion hdisj).symm
    _ ≤ _ := card_le_card hsub

/-- **(3c) Number of probes (active candidates).** If the candidates of rings decided before
phase `i` send nothing, there are at most `4 R / 2^i` probe origins in phase `i`
(`R` = number of elements): `#probes · 2^i ≤ 4 R`. -/
theorem card_activeEnds_mul_pow (hr : RingWF cl S r) (i : ℕ) :
    (activeEnds r i).card * 2 ^ i ≤ 4 * (ringElems r).card := by
  have h1 := card_activeEnds_mul hr i
  rw [card_darts hr] at h1
  have h2 : 2 ^ i ≤ 2 * 2 ^ (i - 1) := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp
    · rw [← pow_succ']; exact le_of_eq (by congr 1; omega)
  calc (activeEnds r i).card * 2 ^ i ≤ (activeEnds r i).card * (2 * 2 ^ (i - 1)) :=
        Nat.mul_le_mul_left _ h2
    _ = 2 * ((activeEnds r i).card * 2 ^ (i - 1)) := by ring
    _ ≤ 2 * (2 * (ringElems r).card) := Nat.mul_le_mul_left _ h1
    _ = 4 * (ringElems r).card := by ring

/-- **(3c) Probes in flight.** If the candidates of rings decided before phase `i` send nothing,
then at every link step `k` of phase `i` at most `4 R / 2^i` probes are in flight. -/
theorem card_flightA_mul (hr : RingWF cl S r) (i k : ℕ) :
    (flightA r i k).card * 2 ^ i ≤ 4 * (ringElems r).card :=
  (Nat.mul_le_mul_right _ (card_le_card (flightA_subset i k))).trans
    (card_activeEnds_mul_pow hr i)

theorem card_flightA_le (hr : RingWF cl S r) (i k : ℕ) :
    (flightA r i k).card ≤ 4 * (ringElems r).card / 2 ^ i :=
  (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).2 (card_flightA_mul hr i k)

/-! ## (3d) Decided rings -/

/-- **(3d) A ring of length `≤ 2^i` is decided after phase `i`**: its only candidate in phase
`i + 1` is its maximum. -/
theorem mem_cand_succ_of_decided (hr : RingWF cl S r) {i : ℕ} {F : V × ℕ}
    (hF : F ∈ ringElems r) (hd : per r (evE F) ≤ 2 ^ i) :
    F ∈ cand r (i + 1) ↔ F = ringMax r F := by
  constructor
  · intro hc
    by_contra hne
    have hMc : ringMax r F ∈ cand r i := ringMax_mem_cand hr hF i
    have hlt : eid F < eid (ringMax r F) :=
      lt_of_le_of_ne (le_ringMax hr hF (self_mem_ringE hr hF)) (fun h => hne (eid_injective h))
    have hFM : F ∈ ringE r (ringMax r F) := mem_ringE_comm hr hF (ringMax_mem hr hF)
    have hMe : evE (ringMax r F) ∈ ringDarts r := (mem_ringElems hr).1 (ringMax_mem_elems hr hF)
    have hper : per r (evE (ringMax r F)) = per r (evE F) := by
      rw [← card_ringE hr (ringMax_mem_elems hr hF), ← card_ringE hr hF, ringE_ringMax hr hF]
    obtain ⟨j, hj⟩ := (mem_ringOf hr hMe).1 hFM
    have hre : Reach r i (evE (ringMax r F)) F := by
      refine reach_of hr hMe (j := j % per r (evE (ringMax r F))) ?_
        (by rw [iter_mod]; exact hj) (by rw [elemOf_evE]; exact hne)
      have := Nat.mod_lt j (per_pos hr hMe)
      omega
    exact ((mem_cand_succ.1 hc).2 _ hMc hlt).1 hre
  · intro h
    rw [h]
    exact ringMax_mem_cand hr hF _

/-- Once decided, a ring keeps its maximum as its only candidate. -/
theorem mem_cand_of_decided (hr : RingWF cl S r) {i i' : ℕ} (hii' : i < i') {F : V × ℕ}
    (hF : F ∈ ringElems r) (hd : per r (evE F) ≤ 2 ^ i) :
    F ∈ cand r i' ↔ F = ringMax r F := by
  constructor
  · intro h
    exact (mem_cand_succ_of_decided hr hF hd).1 (cand_anti (by omega) h)
  · intro h
    rw [h]
    exact ringMax_mem_cand hr hF _

/-- On a decided ring the maximum sees both of its probes return. -/
theorem ringMax_returns (hr : RingWF cl S r) {i : ℕ} {F : V × ℕ} (hF : F ∈ ringElems r)
    (hd : per r (evE F) ≤ 2 ^ i) :
    Reach r i (evE (ringMax r F)) (ringMax r F) ∧ Reach r i (odE (ringMax r F)) (ringMax r F) := by
  have hMe : evE (ringMax r F) ∈ ringDarts r := (mem_ringElems hr).1 (ringMax_mem_elems hr hF)
  have hper : per r (evE (ringMax r F)) = per r (evE F) := by
    rw [← card_ringE hr (ringMax_mem_elems hr hF), ← card_ringE hr hF, ringE_ringMax hr hF]
  have h1 := (reach_self_iff hr hMe (i := i)).2 (hper ▸ hd)
  have h2 := (reach_self_iff hr (pairD_mem hr hMe) (i := i)).2
    (by rw [per_pairD hr hMe, hper]; exact hd)
  rw [elemOf_evE] at h1
  rw [elemOf_pairD, elemOf_evE, ← odE_eq_pairD] at h2
  exact ⟨h1, h2⟩

/-- **(3d) Final phase**: if `R ≤ 2^Φ`, every ring is decided after phase `Φ`, and its unique
candidate in phase `Φ + 1` is its maximum. -/
theorem cand_final (hr : RingWF cl S r) {Φ : ℕ} (hΦ : (ringElems r).card ≤ 2 ^ Φ) {F : V × ℕ}
    (hF : F ∈ ringElems r) : F ∈ cand r (Φ + 1) ↔ F = ringMax r F :=
  mem_cand_succ_of_decided hr hF ((per_le_card hr ((mem_ringElems hr).1 hF)).trans hΦ)

/-- Stopping decided rings does not change the election: the survival rule may ignore probes of
candidates whose ring was decided before phase `i`. -/
theorem mem_cand_succ_active (hr : RingWF cl S r) {i : ℕ} {F : V × ℕ} :
    F ∈ cand r (i + 1) ↔ F ∈ cand r i ∧ ∀ E ∈ cand r i, Active r i (evE E) → eid F < eid E →
      ¬ Reach r i (evE E) F ∧ ¬ Reach r i (odE E) F := by
  rw [mem_cand_succ]
  refine and_congr_right fun hF => forall₂_congr fun E hE => ⟨fun h _ => h, fun h hlt => ?_⟩
  by_cases hact : Active r i (evE E)
  · exact h hact hlt
  have hE' := cand_subset i hE
  unfold Active at hact
  push Not at hact
  obtain ⟨hi0, hle⟩ := hact
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hle
  have hEM : E = ringMax r E := (mem_cand_succ_of_decided hr hE' hle).1 hE
  have key : ∀ a, elemOf a = E → ¬ Reach r (i' + 1) a F := by
    intro a ha hre
    have ham : a ∈ ringDarts r := mem_darts_of_elemOf hr (ha ▸ hE')
    have h1 : F ∈ ringE r E := by
      have := reach_mem_ringOf hr ham hre
      rwa [ringOf_eq_ringE hr ham, ha] at this
    have hFd : per r (evE F) ≤ 2 ^ i' := by
      rw [← card_ringE hr (cand_subset _ hF), ringE_eq hr hE' h1, card_ringE hr hE']
      exact hle
    have hFM := (mem_cand_succ_of_decided hr (cand_subset _ hF) hFd).1 hF
    rw [ringMax_eq hr hE' h1, ← hEM] at hFM
    exact lt_irrefl _ (hFM ▸ hlt)
  exact ⟨key _ (elemOf_evE E), key _ (elemOf_odE E)⟩

/-- The deciding phase of a ring: the first phase `i` with `per ≤ 2^i`; the ring is still active
in it, and `i ≤ Φ` whenever `R ≤ 2^Φ`. -/
theorem exists_deciding_phase (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    ∃ i, per r x ≤ 2 ^ i ∧ Active r i x ∧
      ∀ Φ, (ringElems r).card ≤ 2 ^ Φ → i ≤ Φ := by
  have hex : ∃ i, per r x ≤ 2 ^ i := ⟨per r x, (Nat.lt_two_pow_self).le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, fun Φ hΦ =>
    Nat.find_min' hex ((per_le_card hr hx).trans hΦ)⟩
  rw [active_iff]
  intro j hj
  exact not_le.1 (Nat.find_min hex hj)


/-! ## (4) Orientation -/

/-- `InDir r x`: the end `x` lies on the σ-orbit of the even end `evE M` of the maximum `M` of
its ring, i.e. `x` is a departure end of `M`'s even-end probe (in the deciding phase). -/
def InDir (r : V → RingIn V) (x : V × ℕ) : Prop :=
  ∃ j, (sig r)^[j] (evE (ringMax r (elemOf x))) = x

open Classical in
/-- The orientation of an end: `true` (out) iff `InDir r x`. -/
noncomputable def dir (r : V → RingIn V) (x : V × ℕ) : Bool := decide (InDir r x)

/-- The orientation output of node `v`: `dir` of its ends `(v, 0), …, (v, len - 1)`. -/
noncomputable def ringDir (r : V → RingIn V) (v : V) : List Bool :=
  (List.range (r v).length).map (fun i => dir r (v, i))

open Classical in
lemma dir_eq_true {x : V × ℕ} : dir r x = true ↔ InDir r x := by
  unfold dir; exact decide_eq_true_iff

lemma inDir_iff_of_ringMax {y M : V × ℕ} (h : ringMax r (elemOf y) = M) :
    InDir r y ↔ ∃ j, (sig r)^[j] (evE M) = y := by
  unfold InDir; rw [h]

lemma ringMax_elemOf_pairD (x : V × ℕ) : ringMax r (elemOf (pairD x)) = ringMax r (elemOf x) := by
  rw [elemOf_pairD]

/-- The even end of the maximum of the ring of `x`, and `x`'s element on its orbit. -/
lemma evE_ringMax_mem (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    evE (ringMax r (elemOf x)) ∈ ringDarts r ∧
      elemOf x ∈ ringOf r (evE (ringMax r (elemOf x))) := by
  have hE := elemOf_mem hx
  refine ⟨(mem_ringElems hr).1 (ringMax_mem_elems hr hE), ?_⟩
  exact mem_ringE_comm hr hE (ringMax_mem hr hE)

/-- The orbit of the maximum's even end has the length of the ring of `x`. -/
lemma per_evE_ringMax (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    per r (evE (ringMax r (elemOf x))) = per r x := by
  have hE := elemOf_mem hx
  rw [← card_ringE hr (ringMax_mem_elems hr hE), ringE_ringMax hr hE, ← ringOf_eq_ringE hr hx,
    card_ringOf hr hx]

/-- Every end or its paired end is on the orbit of the maximum's even end ... -/
lemma inDir_or (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    InDir r x ∨ InDir r (pairD x) := by
  obtain ⟨ham, hmem⟩ := evE_ringMax_mem hr hx
  obtain ⟨j, hj⟩ := (mem_ringOf hr ham).1 hmem
  rw [inDir_iff_of_ringMax rfl, inDir_iff_of_ringMax (ringMax_elemOf_pairD x)]
  rcases elemOf_eq_iff.1 hj with h | h
  · exact Or.inl ⟨j, h⟩
  · exact Or.inr ⟨j, h⟩

/-- ... but not both. -/
lemma not_inDir_and (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    ¬ (InDir r x ∧ InDir r (pairD x)) := by
  obtain ⟨ham, -⟩ := evE_ringMax_mem hr hx
  rw [inDir_iff_of_ringMax rfl, inDir_iff_of_ringMax (ringMax_elemOf_pairD x)]
  rintro ⟨⟨j, hj⟩, ⟨l, hl⟩⟩
  exact iter_ne_pairD_iter hr ham l j (by rw [hl, hj])

/-- The two ends of an element have opposite orientations. -/
lemma inDir_pairD (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    InDir r (pairD x) ↔ ¬ InDir r x := by
  have h1 := inDir_or hr hx
  have h2 := not_inDir_and hr hx
  tauto

/-- The orientation is invariant under σ. -/
lemma inDir_sig (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    InDir r (sig r x) ↔ InDir r x := by
  have hE := elemOf_mem hx
  have hsx : elemOf (sig r x) ∈ ringE r (elemOf x) := by
    rw [← ringOf_eq_ringE hr hx]; exact (mem_ringOf hr hx).2 ⟨1, rfl⟩
  rw [inDir_iff_of_ringMax (ringMax_eq hr hE hsx), inDir_iff_of_ringMax rfl]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨per r x * 1 - 1 + j, ?_⟩
    rw [iterate_add_apply, hj]
    exact iter_back hr hx 1
  · rintro ⟨j, hj⟩
    exact ⟨j + 1, by rw [iterate_succ_apply', hj]⟩

/-- The two ends of a link have opposite orientations. -/
lemma inDir_part (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    InDir r (segPartner r x) ↔ ¬ InDir r x := by
  rw [part_eq_pairD_sig, inDir_pairD hr (sig_mem hr hx), inDir_sig hr hx]

lemma dir_ne_of_iff {x y : V × ℕ} (h : InDir r y ↔ ¬ InDir r x) : dir r x ≠ dir r y := by
  intro heq
  have h1 := (dir_eq_true (r := r) (x := x))
  have h2 := (dir_eq_true (r := r) (x := y))
  rw [heq] at h1
  tauto

/-- **(4) Orientation**: `ringDir` satisfies `RingSpec`. -/
theorem ringDir_spec (hr : RingWF cl S r) : RingSpec r (ringDir r) := by
  refine ⟨fun v => by simp [ringDir], ?_, ?_⟩
  · intro v i hi
    rw [List.getD_eq_getElem _ _ (by simp [ringDir]; omega),
      List.getD_eq_getElem _ _ (by simp [ringDir]; omega)]
    simp only [ringDir, List.getElem_map, List.getElem_range]
    have hx : (v, 2 * i) ∈ ringDarts r := mem_ringDarts.2 (by simp only; omega)
    have hp : pairD (v, 2 * i) = (v, 2 * i + 1) := (odE_eq_pairD (v, i)).symm
    rw [← hp]
    exact dir_ne_of_iff (inDir_pairD hr hx)
  · intro v x e e' i i' hv hx
    have hi : i < (r v).length := (List.getElem?_eq_some_iff.1 hv).1
    have hi' : i' < (r x).length := (List.getElem?_eq_some_iff.1 hx).1
    have hs : segPartner r (v, i) = (x, i') := segPartner_eq hr hv hx
    rw [List.getD_eq_getElem _ _ (by simpa [ringDir] using hi),
      List.getD_eq_getElem _ _ (by simpa [ringDir] using hi')]
    simp only [ringDir, List.getElem_map, List.getElem_range]
    have := inDir_part hr (mem_ringDarts.2 hi : (v, i) ∈ ringDarts r)
    rw [hs] at this
    exact dir_ne_of_iff this

/-- **(4) The maximum's even-end probe crosses every end in a deciding phase.** Let `M` be the
maximum of the ring of the end `x` and `i` a phase with `per r x ≤ 2^i` (the ring is decided
after phase `i`). Then `M` is a phase-`i` candidate, and at some link step `k` its probe from
`evE M` departs from `x` (and `dir x = true`) or arrives at `x` (and `dir x = false`). -/
theorem dir_crossed (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) {i : ℕ}
    (hd : per r x ≤ 2 ^ i) :
    ringMax r (elemOf x) ∈ cand r i ∧ ∃ k < hops r i (evE (ringMax r (elemOf x))),
      ((sig r)^[k] (evE (ringMax r (elemOf x))) = x ∧ dir r x = true) ∨
      (segPartner r ((sig r)^[k] (evE (ringMax r (elemOf x)))) = x ∧ dir r x = false) := by
  have hE := elemOf_mem hx
  refine ⟨ringMax_mem_cand hr hE i, ?_⟩
  obtain ⟨ham, hmem⟩ := evE_ringMax_mem hr hx
  set a := evE (ringMax r (elemOf x)) with ha_def
  have hper : per r a = per r x := per_evE_ringMax hr hx
  have hhops : hops r i a = per r a := by unfold hops; rw [hper]; exact min_eq_right hd
  have hp := per_pos hr ham
  obtain ⟨j0, hj0⟩ := (mem_ringOf hr ham).1 hmem
  set j := j0 % per r a with hj_def
  have hjlt : j < per r a := Nat.mod_lt _ hp
  have hj : elemOf ((sig r)^[j] a) = elemOf x := by rw [hj_def, iter_mod]; exact hj0
  rw [hhops]
  rcases elemOf_eq_iff.1 hj with h | h
  · refine ⟨j, hjlt, Or.inl ⟨h, dir_eq_true.2 ((inDir_iff_of_ringMax rfl).2 ⟨j, h⟩)⟩⟩
  · have hnd : dir r x = false := by
      have h1 : InDir r (pairD x) :=
        (inDir_iff_of_ringMax (ringMax_elemOf_pairD x)).2 ⟨j, h⟩
      have h2 := (inDir_pairD hr hx).1 h1
      cases hdx : dir r x
      · rfl
      · exact absurd (dir_eq_true.1 hdx) h2
    have hx' : x = pairD ((sig r)^[j] a) := by rw [h, pairD_pairD]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · refine ⟨per r a - 1, by omega, Or.inr ⟨?_, hnd⟩⟩
      rw [part_iter_pred hr ham, hx', h0, iterate_zero_apply]
    · refine ⟨j - 1, by omega, Or.inr ⟨?_, hnd⟩⟩
      have e : (j - 1).succ = j := by omega
      rw [hx', part_eq_pairD_sig, ← iterate_succ_apply' (sig r), e]

/-- **Every probe passing an end comes from its ring**, so its originator's ID is at most the
ring maximum's. -/
theorem probe_le_ringMax (hr : RingWF cl S r) {x b : V × ℕ} (hb : b ∈ ringDarts r) {k : ℕ}
    (h : (sig r)^[k] b = x ∨ segPartner r ((sig r)^[k] b) = x) :
    eid (elemOf b) ≤ eid (ringMax r (elemOf x)) := by
  have hmem : elemOf x ∈ ringE r (elemOf b) := by
    rw [← ringOf_eq_ringE hr hb, mem_ringOf hr hb]
    rcases h with h | h
    · exact ⟨k, by rw [h]⟩
    · exact ⟨k + 1, by rw [← h, elemOf_part_iter]⟩
  have hbE := elemOf_mem hb
  have h1 := mem_ringE_comm hr hbE hmem
  exact le_ringMax hr (ringE_subset hr hbE hmem) h1

/-- **The direction induced by a probe of the ring maximum.** Let `b` be an end of the maximum
`M` of the ring of `x` (`b = evE M`: even start, `b = odE M`: odd start). If the probe from `b`
departs from `x` then `dir x = true ↔ b` is even; if it arrives at `x` then `dir x = true ↔ b` is
odd. So both probes of `M` induce `dir`, and "record the direction induced by the largest-ID probe
passing you" (departure = out for an even start, arrival = out for an odd start) computes `dir`. -/
theorem dir_of_max_probe (hr : RingWF cl S r) {x b : V × ℕ} (hx : x ∈ ringDarts r)
    (hb : elemOf b = ringMax r (elemOf x)) (k : ℕ) :
    ((sig r)^[k] b = x → (dir r x = true ↔ b.2 % 2 = 0)) ∧
      (segPartner r ((sig r)^[k] b) = x → (dir r x = true ↔ b.2 % 2 = 1)) := by
  obtain ⟨ham, -⟩ := evE_ringMax_mem hr hx
  set M := ringMax r (elemOf x) with hM
  have hInx : InDir r x ↔ ∃ j, (sig r)^[j] (evE M) = x := inDir_iff_of_ringMax rfl
  have hInpx : InDir r (pairD x) ↔ ∃ j, (sig r)^[j] (evE M) = pairD x :=
    inDir_iff_of_ringMax (ringMax_elemOf_pairD x)
  have hpx := inDir_pairD hr hx
  have hp := per_pos hr ham
  rw [dir_eq_true]
  rcases eq_evE_or_odE hb with rfl | rfl
  · rw [evE_snd_mod]
    refine ⟨fun h => ⟨fun _ => rfl, fun _ => hInx.2 ⟨k, h⟩⟩, fun h => ?_⟩
    have : InDir r (pairD x) := hInpx.2 ⟨k + 1, by rw [iter_succ_eq, h]⟩
    constructor
    · intro hx'; exact absurd hx' (hpx.1 this)
    · intro h'; omega
  · rw [odE_snd_mod, odE_eq_pairD]
    -- `σ^k (pair a) = pair (σ^m a)` with `m = per - k % per`
    have hk : ∀ k, ∃ m, (sig r)^[k] (pairD (evE M)) = pairD ((sig r)^[m] (evE M)) := by
      intro k
      refine ⟨per r (evE M) - k % per r (evE M), ?_⟩
      rw [← iter_mod r (pairD (evE M)) k, per_pairD hr ham,
        iter_pairD hr ham (Nat.mod_lt _ hp).le]
    refine ⟨fun h => ?_, fun h => ⟨fun _ => rfl, fun _ => ?_⟩⟩
    · obtain ⟨m, hm⟩ := hk k
      have : InDir r (pairD x) := hInpx.2 ⟨m, by rw [← h, hm, pairD_pairD]⟩
      constructor
      · intro hx'; exact absurd hx' (hpx.1 this)
      · intro h'; omega
    · obtain ⟨m, hm⟩ := hk (k + 1)
      refine hInx.2 ⟨m, ?_⟩
      rw [← h, ← pairD_pairD ((sig r)^[m] (evE M)), ← hm, iter_succ_eq, pairD_pairD]


/-- **(4) In the deciding phase the maximum's even-end probe is sent (also when the candidates of
decided rings stop) and crosses every end of the ring**, in a phase `i ≤ Φ` whenever `R ≤ 2^Φ`. -/
theorem max_probe_crosses (hr : RingWF cl S r) {x : V × ℕ} (hx : x ∈ ringDarts r) :
    ∃ i, (∀ Φ, (ringElems r).card ≤ 2 ^ Φ → i ≤ Φ) ∧
      ∃ k, evE (ringMax r (elemOf x)) ∈ flightA r i k ∧
        ((depEnd r (evE (ringMax r (elemOf x))) k = x ∧ dir r x = true) ∨
          (arrEnd r (evE (ringMax r (elemOf x))) k = x ∧ dir r x = false)) := by
  obtain ⟨i, hd, hact, hΦ⟩ := exists_deciding_phase hr hx
  obtain ⟨hc, k, hk, h⟩ := dir_crossed hr hx hd
  obtain ⟨ham, -⟩ := evE_ringMax_mem hr hx
  refine ⟨i, hΦ, k, ?_, h⟩
  simp only [flightA, mem_filter]
  refine ⟨mem_flight.2 ⟨ham, by rw [elemOf_evE]; exact hc, hk⟩, ?_⟩
  unfold Active at hact ⊢
  rw [per_evE_ringMax hr hx]
  exact hact

end RingComb
end APSP.Stoc
