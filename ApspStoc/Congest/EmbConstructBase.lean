import ApspStoc.Congest.TreeCastAux

/-!
# Auxiliary material for `embedConstruct` (`EmbConstruct.lean`)

* `rdIn T inp me`: the data of the node's own physical agent, read as a value of type `T`.
* `digW β D k` / `decD`: a number as `D` little-endian base-`β` digit words, and its decoding.
* `ctxP gf P` (**local re-contextualisation**): every node computes, from its context and its data,
  a new context and new data, and runs `P` with them. `ctxI`: if on every participant the computed
  context and data are those of an instance `withCtx I c'` (same graph, participants and hosts,
  contexts `c'`) and an input `x'`, then `ctxP gf P` behaves on `I` from `x` as `P` on
  `withCtx I c'` from `x'` (same run, same costs, same outputs). This is how a cluster protocol
  switches from the setup instance `clInst0 N C` to the routing instance `clInst N C` (whose
  public numbers `n_C, m_C` the nodes compute from the setup output).
* `card_proj_filter`: if every node holds an independent uniform seed for every *key* (seeds
  `V → K → Ω₀`), then reading at every node `v` the seed of one key `κ v` gives uniform seeds
  `V → Ω₀`. This is the probabilistic core of the parallel composition (each cluster copy at a
  node uses the seed of its slice).
-/

namespace APSP.Stoc.Congest

namespace EmbC

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Reading typed data -/

open Classical in
/-- the data of the physical agent `.inl me`, read as a value of type `T` (`none` if absent or of
another type) -/
noncomputable def rdIn (T : Type) (inp : Agent V → Option Mem) (me : V) : Option T :=
  match inp (.inl me) with
  | some m => if h : m.1 = T then some (cast h m.2) else none
  | none => none

lemma rdIn_of {T : Type} {inp : Agent V → Option Mem} {me : V} {a : T}
    (h : inp (.inl me) = some ⟨T, a⟩) : rdIn T inp me = some a := by
  unfold rdIn; rw [h]; simp

/-- `Classical.choose` only depends on the predicate. -/
lemma choose_congr {α : Sort*} {p q : α → Prop} (h : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    hp.choose = hq.choose := by
  subst h; rfl

/-! ## Digits -/

/-- the `D` little-endian base-`β` digits of `k`, as words -/
def digW (β D k : ℕ) : List (Word V) := (List.range D).map (fun i => .num (k / β ^ i % β))

/-- decoding of `D` digits read from positions `a, a + 1, …` of a stream -/
def decD (β D : ℕ) (f : ℕ → Word V) (a : ℕ) : ℕ := digVal β (fun j => f (a + j)) D

lemma length_digW (β D k : ℕ) : (digW (V := V) β D k).length = D := by simp [digW]

lemma decD_digits (β D k a : ℕ) (f : ℕ → Word V) (hf : ∀ j < D, f (a + j) = .num (k / β ^ j % β))
    (hk : k < β ^ D) : decD β D f a = k := by
  unfold decD
  rw [digVal_congr β D _ (fun j => .num (k / β ^ j % β)) hf, digVal_digits, Nat.mod_eq_of_lt hk]

lemma digW_ok (n D k : ℕ) : ∀ w ∈ digW (V := V) (n + 4) D k, WordOK n w := by
  intro w hw
  simp only [digW, List.mem_map, List.mem_range] at hw
  obtain ⟨i, _, rfl⟩ := hw
  show k / (n + 4) ^ i % (n + 4) ≤ n + 3
  have := Nat.mod_lt (k / (n + 4) ^ i) (show 0 < n + 4 by omega)
  omega

lemma getD_digW (β D k : ℕ) {j : ℕ} (hj : j < D) (d : Word V) :
    (digW (V := V) β D k).getD j d = .num (k / β ^ j % β) := by
  simp [digW, List.getD_eq_getElem?_getD, List.getElem?_range hj]

lemma lt_pow_of_le_pow {n a k : ℕ} (h : k ≤ n ^ a) : k < (n + 4) ^ (a + 1) := by
  calc k ≤ n ^ a := h
    _ ≤ (n + 4) ^ a := Nat.pow_le_pow_left (by omega) a
    _ < (n + 4) ^ a * (n + 4) := by
        have : 0 < (n + 4) ^ a := by positivity
        nlinarith
    _ = (n + 4) ^ (a + 1) := (pow_succ _ _).symm

/-! ## Local re-contextualisation -/

/-- Run `P` with a context and data computed locally (by `gf`) from the given ones. -/
@[reducible] def ctxP (gf : NCtx V → (Agent V → Option Mem) → NCtx V × (Agent V → Option Mem))
    (P : Proto V) : Proto V where
  S := NCtx V × P.S
  Ω := P.Ω
  init c inp ω := ((gf c inp).1, P.init (gf c inp).1 (gf c inp).2 ω)
  send _ s u := P.send s.1 s.2 u
  recv _ s m := (s.1, P.recv s.1 s.2 m)
  out s := P.out s.2

/-- the instance `I` with the local contexts `c` -/
def withCtx (I : Inst V) (c : V → NCtx V) : Inst V := { I with ctx := c }

section CtxRun

variable (gf : NCtx V → (Agent V → Option Mem) → NCtx V × (Agent V → Option Mem)) (P : Proto V)
  (I : Inst V) (c' : V → NCtx V) {x x' : Agent V → Mem}

lemma inpAt_withCtx (x : Agent V → Mem) (v : V) : inpAt (withCtx I c') x v = inpAt I x v := rfl

lemma msg_ctxP {σ : V → (ctxP gf P).S} {σ' : V → P.S}
    (hσ : ∀ u, I.part u → σ u = (c' u, σ' u)) (u v : V) :
    msg (ctxP gf P) I σ u v = msg P (withCtx I c') σ' u v := by
  classical
  unfold msg
  by_cases hadj : I.G.Adj u v
  · have hu := I.adj_part u v hadj
    simp only [hσ u hu]
    rfl
  · rw [ite_eq_right (fun h => absurd h.1 hadj)]
    exact (ite_eq_right (fun h => absurd h.1 hadj)).symm

variable {gf P I c'}

lemma st_ctxP (hg : ∀ v, I.part v → gf (I.ctx v) (inpAt I x v) = (c' v, inpAt I x' v))
    (ω : V → P.Ω) : ∀ t v, I.part v →
      st (ctxP gf P) I x ω t v = (c' v, st P (withCtx I c') x' ω t v) := by
  intro t
  induction t with
  | zero =>
    intro v hv
    show ((gf (I.ctx v) (inpAt I x v)).1,
      P.init (gf (I.ctx v) (inpAt I x v)).1 (gf (I.ctx v) (inpAt I x v)).2 (ω v)) = _
    rw [hg v hv]
    rfl
  | succ t ih =>
    intro v hv
    rw [st_succ, st_succ]
    unfold step
    rw [ih v hv]
    have hm := msg_ctxP gf P I c' ih
    show (if (P.out (st P (withCtx I c') x' ω t v)).isSome then _ else _) = _
    split_ifs with h
    · rfl
    · simp only [hm]
      rfl

lemma msg_ctxP_run (hg : ∀ v, I.part v → gf (I.ctx v) (inpAt I x v) = (c' v, inpAt I x' v))
    (ω : V → P.Ω) (t : ℕ) (u v : V) :
    msg (ctxP gf P) I (st (ctxP gf P) I x ω t) u v =
      msg P (withCtx I c') (st P (withCtx I c') x' ω t) u v :=
  msg_ctxP gf P I c' (st_ctxP hg ω t) u v

lemma succ_ctxP (hg : ∀ v, I.part v → gf (I.ctx v) (inpAt I x v) = (c' v, inpAt I x' v))
    {Q : (Agent V → Mem) → Prop} {p : Prof V} (ω : V → P.Ω) :
    Succ (ctxP gf P) I x Q p ω ↔ Succ P (withCtx I c') x' Q p ω := by
  have hst := st_ctxP hg ω
  have hmsg := msg_ctxP_run hg ω
  have hsent : ∀ t, sentSet (ctxP gf P) I (st (ctxP gf P) I x ω t) =
      sentSet P (withCtx I c') (st P (withCtx I c') x' ω t) := by
    intro t; unfold sentSet; simp only [hmsg]
  have hH : ∀ t, HaltsAt (ctxP gf P) I x ω t ↔ HaltsAt P (withCtx I c') x' ω t := by
    intro t
    unfold HaltsAt
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, fun s hs v hv => ?_⟩
      · have := h1 v hv; rw [hst t v hv] at this; exact this
      · have := h2 s hs v hv; rw [hst s v hv] at this; exact this
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, fun s hs v hv => ?_⟩
      · rw [hst t v hv]; exact h1 v hv
      · rw [hst s v hv]; exact h2 s hs v hv
  have hP : ∀ t, ProperUpTo (ctxP gf P) I x ω t ↔ ProperUpTo P (withCtx I c') x' ω t := by
    intro t
    unfold ProperUpTo
    constructor
    · intro h s hs u hu hout v hv
      have := h s hs u hu (by rw [hst s u hu]; exact hout) v (by rw [hst s u hu]; exact hv)
      exact this
    · intro h s hs u hu hout v hv
      rw [hst s u hu] at hout hv
      exact h s hs u hu hout v hv
  have hO : ∀ t g, outAt (ctxP gf P) I x ω t g = outAt P (withCtx I c') x' ω t g := by
    intro t g
    unfold outAt
    show (match I.host g with
      | some v => ((ctxP gf P).out (st (ctxP gf P) I x ω t v)).bind (fun m => m g)
      | none => none) = (match I.host g with
      | some v => (P.out (st P (withCtx I c') x' ω t v)).bind (fun m => m g)
      | none => none)
    cases hg' : I.host g with
    | none => rfl
    | some v =>
      dsimp only
      rw [hst t v (I.host_part g v hg')]
  unfold Succ
  simp only [hH, hP, msgsUpTo, loadUpTo, hsent, hO]
  rfl

/-- **Local re-contextualisation**: `ctxP gf P` on `I` from `x` behaves as `P` on `withCtx I c'`
from `x'` if every participant computes its context in `c'` and its data from `x'`. -/
theorem ctxI (hg : ∀ v, I.part v → gf (I.ctx v) (inpAt I x v) = (c' v, inpAt I x' v))
    {Q : (Agent V → Mem) → Prop} {p : Prof V} {δ : ℝ}
    (h : ImplI P (withCtx I c') x' Q p δ) : ImplI (ctxP gf P) I x Q p δ := by
  classical
  unfold ImplI failProb at *
  convert h using 4
  ext ω
  simp only [mem_filter, mem_univ, true_and]
  exact not_congr (succ_ctxP (gf := gf) (P := P) hg ω)

end CtxRun

/-! ## Seeds indexed by keys -/

/-- Reading at every node `v` the seed of the key `κ v` from independent uniform seeds for all
keys gives independent uniform seeds. -/
lemma card_proj_filter {K Ω₀ : Type} [Fintype K] [DecidableEq K] [Fintype Ω₀] [Nonempty Ω₀]
    (κ : V → K)
    (p : (V → Ω₀) → Prop) [DecidablePred p] :
    ((univ.filter (fun ω : V → K → Ω₀ => p (fun v => ω v (κ v)))).card : ℝ) /
        (Fintype.card (V → K → Ω₀) : ℝ) =
      ((univ.filter p).card : ℝ) / (Fintype.card (V → Ω₀) : ℝ) := by
  classical
  let R := ∀ v, {k // k ≠ κ v} → Ω₀
  let e : (V → K → Ω₀) ≃ (V → Ω₀) × R :=
    (Equiv.piCongrRight (fun v => Equiv.piSplitAt (κ v) (fun _ => Ω₀))).trans
      (Equiv.arrowProdEquivProdArrow V (fun _ => Ω₀) (fun v => {k // k ≠ κ v} → Ω₀))
  have he : ∀ ω, (e ω).1 = fun v => ω v (κ v) := fun ω => rfl
  have h1 : (univ.filter (fun ω : V → K → Ω₀ => p (fun v => ω v (κ v)))).card =
      (univ.filter p).card * Fintype.card R := by
    rw [← card_univ (α := R), ← card_product]
    refine card_bij (fun ω _ => e ω) ?_ ?_ ?_
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      simp only [mem_product, mem_filter, mem_univ, true_and, and_true, he]
      exact hω
    · intro ω₁ _ ω₂ _ h; exact e.injective h
    · intro z hz
      refine ⟨e.symm z, ?_, by simp⟩
      simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hz
      simp only [mem_filter, mem_univ, true_and]
      have : (e (e.symm z)).1 = z.1 := by simp
      rw [he] at this; rw [this]; exact hz
  have h2 : Fintype.card (V → K → Ω₀) = Fintype.card (V → Ω₀) * Fintype.card R := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [h1, h2]
  have hR : (0 : ℝ) < Fintype.card R := by
    have : Nonempty R := ⟨fun _ _ => Classical.arbitrary Ω₀⟩
    exact_mod_cast Fintype.card_pos
  push_cast
  rw [mul_div_mul_right _ _ (ne_of_gt hR)]

end EmbC

end APSP.Stoc.Congest
