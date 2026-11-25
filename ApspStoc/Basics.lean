import ApspStoc.Polylog

/-!
# Basic cost lemmas and Observation 2.3
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Observation 2.3 -/

/-- **Observation 2.3**: if an algorithm sends `Mdir` messages directly over the edges of `G`
(at most `bdir e` over edge `e`), and, over an overlay `H` embedded with congestion `c` and dilation
`d`, sends `msg h ≤ bov` messages over every overlay edge `h` (whose embedded path is `path h`), then
the physical load of `e` is at most `bdir e + c · bov` and the number of physical message
transmissions is at most `Mdir + d · ∑_h msg h`. -/
theorem observation_2_3 {ι : Type*} (H : Finset ι) (path : ι → List (Sym2 V)) (c d bov : ℕ)
    (msg : ι → ℕ) (bdir : Sym2 V → ℕ) (Mdir : ℕ)
    (hc : ∀ e, (H.filter (fun h => e ∈ path h)).card ≤ c) (hd : ∀ h ∈ H, (path h).length ≤ d)
    (hb : ∀ h ∈ H, msg h ≤ bov) :
    (∀ e, bdir e + ∑ h ∈ H, msg h * (path h).count e ≤ bdir e + c * (bov * d)) ∧
    Mdir + ∑ h ∈ H, msg h * (path h).length ≤ Mdir + d * ∑ h ∈ H, msg h := by
  refine ⟨fun e => Nat.add_le_add_left ?_ _, Nat.add_le_add_left ?_ _⟩
  · rw [← sum_filter_add_sum_filter_not H (fun h => e ∈ path h)]
    have h0 : ∑ h ∈ H.filter (fun h => ¬ e ∈ path h), msg h * (path h).count e = 0 :=
      sum_eq_zero (fun h hh => by
        rw [List.count_eq_zero.2 (mem_filter.1 hh).2, mul_zero])
    rw [h0, add_zero]
    calc ∑ h ∈ H.filter (fun h => e ∈ path h), msg h * (path h).count e
        ≤ ∑ h ∈ H.filter (fun h => e ∈ path h), bov * d :=
          sum_le_sum (fun h hh => Nat.mul_le_mul (hb h (mem_filter.1 hh).1)
            ((List.count_le_length).trans (hd h (mem_filter.1 hh).1)))
      _ = _ * (bov * d) := by rw [sum_const, smul_eq_mul]
      _ ≤ c * (bov * d) := Nat.mul_le_mul_right _ (hc e)
  · rw [mul_sum]
    exact sum_le_sum (fun h hh => by rw [mul_comm d]; exact Nat.mul_le_mul_left _ (hd h hh))

/-! ## Cost shapes -/

/-- Shape of the cost bounds of the subset procedures: `Õ(|S|)` rounds and messages and
`Õ(1) · ρ^S_j` load (direct edges of `G[S]`-incident edges plus embedded aggregator paths). -/
def subsetProf (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ) (S : Finset V)
    (Q : ℕ) : Prof V :=
  Prof.mk (Q * (S.card + 1)) (fun e => Q * E.rho G j S e) (Q * (S.card + 1))

lemma subsetProf_add (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)
    (S : Finset V) (a b : ℕ) :
    subsetProf G E j S a + subsetProf G E j S b = subsetProf G E j S (a + b) := by
  unfold subsetProf Prof.mk
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show a * (S.card + 1) + b * (S.card + 1) = (a + b) * (S.card + 1); ring
  · funext e; show a * E.rho G j S e + b * E.rho G j S e = (a + b) * E.rho G j S e; ring
  · show a * (S.card + 1) + b * (S.card + 1) = (a + b) * (S.card + 1); ring

lemma subsetProf_smul (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)
    (S : Finset V) (k a : ℕ) : k • subsetProf G E j S a = subsetProf G E j S (k * a) := by
  unfold subsetProf Prof.mk
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show k * (a * (S.card + 1)) = k * a * (S.card + 1); ring
  · funext e; show k * (a * E.rho G j S e) = k * a * E.rho G j S e; ring
  · show k * (a * (S.card + 1)) = k * a * (S.card + 1); ring

lemma subsetProf_mono_Q (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)
    (S : Finset V) {Q Q' : ℕ} (h : Q ≤ Q') : subsetProf G E j S Q ≤ subsetProf G E j S Q' := by
  unfold subsetProf
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_ <;> simp only [Prof.rounds_mk, Prof.load_mk,
    Prof.msgs_mk] <;> exact Nat.mul_le_mul_right _ h

lemma subsetProf_mono (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)
    {S S' : Finset V} (h : S' ⊆ S) (Q : ℕ) : subsetProf G E j S' Q ≤ subsetProf G E j S Q := by
  unfold subsetProf
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_ <;> simp only [Prof.rounds_mk, Prof.load_mk,
    Prof.msgs_mk]
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (card_le_card h) 1)
  · exact Nat.mul_le_mul_left _ (rho_mono E j h e)
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (card_le_card h) 1)

/-- Cost shape with a public size bound `sz ≥ |S|`: the round budget `Q·(sz+1)` is known to all
participants; load `Q·ρ^S_j` and messages `Q·(|S|+1)` are actual. -/
def szProf (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j sz : ℕ) (S : Finset V)
    (Q : ℕ) : Prof V :=
  Prof.mk (Q * (sz + 1)) (fun e => Q * E.rho G j S e) (Q * (S.card + 1))

lemma szProf_card (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)
    (S : Finset V) (Q : ℕ) : szProf G E j S.card S Q = subsetProf G E j S Q := rfl

lemma szProf_add (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j sz : ℕ)
    (S : Finset V) (a b : ℕ) :
    szProf G E j sz S a + szProf G E j sz S b = szProf G E j sz S (a + b) := by
  unfold szProf Prof.mk
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show a * (sz + 1) + b * (sz + 1) = (a + b) * (sz + 1); ring
  · funext e; show a * E.rho G j S e + b * E.rho G j S e = (a + b) * E.rho G j S e; ring
  · show a * (S.card + 1) + b * (S.card + 1) = (a + b) * (S.card + 1); ring

lemma szProf_smul (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j sz : ℕ)
    (S : Finset V) (k a : ℕ) : k • szProf G E j sz S a = szProf G E j sz S (k * a) := by
  unfold szProf Prof.mk
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show k * (a * (sz + 1)) = k * a * (sz + 1); ring
  · funext e; show k * (a * E.rho G j S e) = k * a * E.rho G j S e; ring
  · show k * (a * (S.card + 1)) = k * a * (S.card + 1); ring

lemma szProf_mono_Q (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j sz : ℕ)
    (S : Finset V) {Q Q' : ℕ} (h : Q ≤ Q') : szProf G E j sz S Q ≤ szProf G E j sz S Q' := by
  unfold szProf
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_ <;> simp only [Prof.rounds_mk, Prof.load_mk,
    Prof.msgs_mk] <;> exact Nat.mul_le_mul_right _ h

lemma szProf_mono (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)
    {sz sz' : ℕ} {S S' : Finset V} (hsz : sz' ≤ sz) (h : S' ⊆ S) (Q : ℕ) :
    szProf G E j sz' S' Q ≤ szProf G E j sz S Q := by
  unfold szProf
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_ <;> simp only [Prof.rounds_mk, Prof.load_mk,
    Prof.msgs_mk]
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hsz 1)
  · exact Nat.mul_le_mul_left _ (rho_mono E j h e)
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (card_le_card h) 1)

lemma subsetProf_le_szProf (G : SimpleGraph V) [DecidableRel G.Adj] (E : Overlays V) (j sz : ℕ)
    (S : Finset V) (Q : ℕ) (h : S.card ≤ sz) : subsetProf G E j S Q ≤ szProf G E j sz S Q := by
  rw [← szProf_card]; exact szProf_mono G E j h subset_rfl Q

/-! ## Public parameters of the embedding -/

lemma _root_.APSP.Overlays.path_le_dil (E : Overlays V) {j : ℕ} (hj : j < Fintype.card V) (v : V)
    {C : Finset (Sym2 V)} (hC : C ∈ E.cl) : (E.path j v C).length ≤ E.dil := by
  unfold Overlays.dil
  exact le_trans (le_trans (Finset.le_sup (f := fun C => (E.path j v C).length) hC)
    (Finset.le_sup (f := fun v => E.cl.sup (fun C => (E.path j v C).length)) (mem_univ v)))
    (Finset.le_sup (f := fun j => univ.sup (fun v => E.cl.sup (fun C => (E.path j v C).length)))
      (mem_range.2 hj))

lemma _root_.APSP.Overlays.card_clustersOf_le_ov (E : Overlays V) (v : V) :
    (clustersOf E.cl v).card ≤ E.ov :=
  Finset.le_sup (f := fun v => (clustersOf E.cl v).card) (mem_univ v)

lemma dil_le_of_props {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V} {ov d X : ℕ}
    (hE : OverlayProps G E ov d X) : E.dil ≤ d := by
  unfold Overlays.dil
  exact Finset.sup_le (fun j _ => Finset.sup_le (fun v _ => Finset.sup_le
    (fun C _ => hE.len j v C)))

lemma ov_le_of_props {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V} {ov d X : ℕ}
    (hE : OverlayProps G E ov d X) : E.ov ≤ ov := by
  unfold Overlays.ov
  exact Finset.sup_le (fun v _ => hE.overlap v)

/-- Subset congestion in terms of the public dilation: `rhoAgg ≤ dil · |S|`. -/
lemma rhoAgg_le_dil {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V}
    (hE : EmbValid G E) {j : ℕ} (hj : j < Fintype.card V) (S : Finset V) (e : Sym2 V) :
    E.rhoAgg j S e ≤ E.dil * S.card := by
  unfold Overlays.rhoAgg
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum; intro v _
  have hzero : ∀ C ∈ clustersOf E.cl v, C ∉ (clustersOf E.cl v).filter (fun C => e ∈ C) →
      (E.path j v C).count e = 0 := by
    intro C _ hnot
    rw [List.count_eq_zero]
    intro hmem
    exact hnot (mem_filter.2 ⟨by assumption, hE.local_ j v C e hmem⟩)
  rw [← sum_subset (filter_subset _ _) hzero]
  have h1 : ((clustersOf E.cl v).filter (fun C => e ∈ C)).card ≤ 1 := by
    rw [card_le_one]
    intro C hC C' hC'
    rw [mem_filter] at hC hC'
    by_contra hne
    exact disjoint_left.1 (hE.disj C (mem_filter.1 hC.1).1 C' (mem_filter.1 hC'.1).1 hne) hC.2 hC'.2
  calc ∑ C ∈ (clustersOf E.cl v).filter (fun C => e ∈ C), (E.path j v C).count e
      ≤ ∑ C ∈ (clustersOf E.cl v).filter (fun C => e ∈ C), E.dil :=
        sum_le_sum (fun C hC => (List.count_le_length).trans
          (E.path_le_dil hj v (mem_filter.1 (mem_filter.1 hC).1).1))
    _ = _ * E.dil := by rw [sum_const, smul_eq_mul]
    _ ≤ 1 * E.dil := Nat.mul_le_mul_right _ h1
    _ = E.dil := one_mul _

/-- Total aggregator-path length in terms of the public overlap and dilation. -/
lemma aggLen_le_dil (E : Overlays V) {j : ℕ} (hj : j < Fintype.card V) (S : Finset V) :
    E.aggLen j S ≤ E.ov * E.dil * S.card := by
  unfold Overlays.aggLen
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum; intro v _
  calc ∑ C ∈ clustersOf E.cl v, (E.path j v C).length ≤ ∑ C ∈ clustersOf E.cl v, E.dil :=
        sum_le_sum (fun C hC => E.path_le_dil hj v (mem_filter.1 hC).1)
    _ = (clustersOf E.cl v).card * E.dil := by rw [sum_const, smul_eq_mul]
    _ ≤ E.ov * E.dil := Nat.mul_le_mul_right _ (E.card_clustersOf_le_ov v)

/-! ## Miscellaneous -/

lemma onEdges_add (F : Finset (Sym2 V)) (x y : ℕ) :
    onEdges F x + onEdges F y = onEdges F (x + y) := by
  funext e; simp only [onEdges, Pi.add_apply]; split_ifs <;> simp

lemma onEdges_mono (F : Finset (Sym2 V)) {x y : ℕ} (h : x ≤ y) (e : Sym2 V) :
    onEdges F x e ≤ onEdges F y e := by
  simp only [onEdges]; split_ifs <;> simp [h]

lemma onEdges_le_rho {G : SimpleGraph V} [DecidableRel G.Adj] (E : Overlays V) (j : ℕ)
    {S : Finset V} {F : Finset (Sym2 V)} (hF : F ⊆ G.edgeFinset) (hFS : ∀ e ∈ F, ∀ v ∈ e, v ∈ S)
    (x : ℕ) (e : Sym2 V) : onEdges F x e ≤ x * E.rho G j S e := by
  unfold onEdges
  split_ifs with he
  · induction e using Sym2.ind with
    | _ a b =>
      have := le_rho_of_mem E j (hF he) (hFS _ he a (Sym2.mem_mk_left a b)) (Sym2.mem_mk_left a b)
      exact Nat.le_mul_of_pos_right x this
  · exact Nat.zero_le _

lemma whp_add (a b c ν : ℕ) : whp a c ν + whp b c ν = whp (a + b) c ν := by
  unfold whp; push_cast; ring

lemma RoutesOK.mono {C : Finset (Sym2 V)} {D : Demand V} {r : Routes V} {d B d' B' : ℕ}
    (h : RoutesOK C D r d B) (hd : d ≤ d') (hB : B ≤ B') : RoutesOK C D r d' B' :=
  ⟨h.walk, h.local_, fun pq hpq => (h.len pq hpq).trans hd, fun e => (h.cong e).trans hB⟩


lemma Prof.list_sum_rounds {α : Type*} (l : List α) (f : α → Prof V) :
    ((l.map f).sum).rounds = (l.map (fun a => (f a).rounds)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, APSP.Prof.rounds_add, ih]

lemma Prof.list_sum_load {α : Type*} (l : List α) (f : α → Prof V) (e : Sym2 V) :
    ((l.map f).sum).load e = (l.map (fun a => (f a).load e)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, APSP.Prof.load_add, Pi.add_apply, ih]

lemma Prof.list_sum_msgs {α : Type*} (l : List α) (f : α → Prof V) :
    ((l.map f).sum).msgs = (l.map (fun a => (f a).msgs)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, APSP.Prof.msgs_add, ih]

/-! ## Local calls on data of the shape `Γ V × A V` -/

/-- The uniform projection to the second component of data of the shape `Γ V × A V`. -/
def sndF (Γ A : Type → Type) : LocFn := ⟨fun V => Γ V × A V, A, fun _ _ _ _ _ p => p.2⟩

/-- The frame rule for local calls: if `P` solves a task from `x`, then `call (sndF Γ A) P` solves
it from the data `(z g, x g)` (it first drops `z` locally). This plays the role of the former
frame rule of the toolkit, for data of the explicit shape `Γ V × A V`. -/
theorem Toolkit.frameCall (T : Toolkit) {Γ A : Type → Type} {P : T.Alg} {V : Type} [Fintype V]
    [DecidableEq V] {N : WNet V} {E : Overlays V} {j sz : ℕ} {Pt : Finset V} {β : Type}
    {x : Agent V → A V} {R : (Agent V → β) → Prop} {p : Prof V} {δ : ℝ} (z : Agent V → Γ V)
    (h : T.Impl P N (.io E j sz Pt (A V) β x R) p δ) :
    T.Impl (T.call (sndF Γ A) P) N (.io E j sz Pt (Γ V × A V) β (fun g => (z g, x g)) R) p δ :=
  T.callR (sndF Γ A) (fun g => (z g, x g)) h

end APSP.Stoc
