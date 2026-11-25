import ApspStoc.Congest.RWLinkCost
import ApspStoc.Congest.RWLinkOut

/-!
# The random-walk construction of `G₀` in the CONGEST semantics (toolkit field `rwLink`)

`rwLink_congest : RWLinkC` proves the toolkit field `rwLink` (in the CONGEST semantics, with
`rwAlg := rwAlgC`) for the algorithm `rwAlgC Rf ℓ tf gf` (`RWLinkProto.lean`), with
`Kc = 48 (kB + 2)`.

## The protocol
A seeded packet protocol (`RWLinkPkt.lean`): every node draws a table
`τ_y : Port V → Fin Rmax → Fin (2ℓ) → Fin Dmax` (`Rmax = max_{a ≤ n, b ≤ n²} Rf a b`,
`Dmax = 2 (n!)ⁿ`); a packet (a token or a report) has `5` words and is sent in a macro-round of
`L = 6 (Bw + 2)` rounds (`Bw = log_{n+4}(R + 2ℓ + 2) ≤ kB`). Phases: `R` macro-rounds of first
crossings, `2ℓ` steps of `t` slots (a walk's lazy step is taken at its current node `y` by
`lazyStepD` with `y`'s seed), `2ℓ` reversed steps of `t` slots returning the survival reports
(start port, index, end port) along the walks, and `R` macro-rounds returning the reports of the
first crossings. All nodes halt after `T = 2R + 4ℓt` macro-rounds and output `gf n_C m_C` and, for
the surviving walks visiting them, (start port, end port) and their hops.

## The proof
For seed tables `τ`, let `σ = rwSeedMap C P hR τ` (`RWCouple.lean`). If the walks under `σ` do not
overflow (`rwOverflow … t σ`) and `TrueParams … σ (gf n_C m_C)` holds, the run follows the global
schedule `schedG` (`succ_pktP`), it sends only along edges of `C` (`schedG_adj`), encodable packets
(`schedG_small`), at most `|P| R (4ℓ + 2)` packets (`sum_schedG_le`), and every node outputs its
`G₀`-knowledge `g0At C P R ℓ σ (gf n_C m_C)` (`outMS_eq`). So the run fails only on the event
`rwOverflow … ∨ ¬ TrueParams …` of `σ = rwSeedMap … τ`, whose probability over uniform `τ` is
`rwProb …` (`rwSeedMap_prob`, measure preservation).

## Contract repair
A token must carry its walk index `i < R` (to select its seed at each node) and the path position
of its crossing (`< 2ℓ + 1`, for the hop lists of `g0At`); with words of `O(log n)` bits this takes
`Θ(log_n (R + ℓ))` words per crossing, so no constant `Kc` works for all `Rf` and `ℓ`. The field
`rwLink` therefore takes an exponent `kB` first (`∀ kB, ∃ Kc`) and the premise
`Rf n_C m_C + 2ℓ + 2 ≤ (n + 4)^kB` (in Theorem 3.3, `R` and `ℓ` are polynomial in `n`).
-/

namespace APSP.Stoc.Congest

open APSP Finset

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

lemma pget_pschedHist_eq (MP : V → V → ℕ → Option (Msg V)) (v : V) (s : ℕ) :
    pget (pschedHist MP v s) = fun s' w => if s' < s then MP w v s' else none := by
  funext s' w
  split_ifs with h
  · exact pget_pschedHist MP v h w
  · exact pget_pschedHist_ge MP v (by omega) w

section Env

variable (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) {N : WNet V} {C : Finset (Sym2 V)}
  {P : Finset (Port V)}

lemma viewE_clInst (hCN : C ⊆ N.G.edgeFinset) (u : V) :
    viewE ((clInst N C).ctx u) = C.filter (fun e => u ∈ e) := by
  classical
  have hv : ((clInst N C).ctx u).view (.inl ((clInst N C).ctx u).me) = some (clView N C u) := by
    simp [clInst, clInstP]
  unfold viewE
  rw [hv]
  show univ.filter (fun e => clView N C u e ≠ 0) = _
  ext e
  rw [mem_filter, mem_filter]
  by_cases h : e ∈ C ∧ u ∈ e
  · have hw : clView N C u e = N.w e := if_pos h
    have := N.wpos e (by have := hCN h.1; simpa using this)
    rw [hw]
    exact ⟨fun _ => h, fun _ => ⟨mem_univ _, by omega⟩⟩
  · have hw : clView N C u e = 0 := if_neg h
    rw [hw]
    exact ⟨fun h' => absurd rfl h'.2, fun h' => absurd h' h⟩

lemma myPorts_clInst (hP : P ⊆ allPorts C) (pl : Multiset (PktP V)) (lam : ℕ) (u : V) :
    myPortsOf u (inpAt (clInst N C) (inOf (rinAt P pl lam)) u) = P.filter (fun p => p.1 = u) := by
  classical
  by_cases hu : u ∈ nodes C
  · have h : inpAt (clInst N C) (inOf (rinAt P pl lam)) u (.inl u) =
        some ⟨RIn V, rinAt P pl lam (.inl u)⟩ := by
      simp [inpAt, clInst, clInstP, clHost, hu, inOf]
    have h2 : myPortsOf u (inpAt (clInst N C) (inOf (rinAt P pl lam)) u) =
        (rinAt P pl lam (.inl u)).1 := by
      unfold myPortsOf
      rw [h]
      exact dif_pos rfl
    rw [h2]
    ext p
    simp [rinAt]
  · have h : inpAt (clInst N C) (inOf (rinAt P pl lam)) u (.inl u) = none := by
      simp [inpAt, clInst, clInstP, clHost, hu]
    unfold myPortsOf
    rw [h]
    show (∅ : Finset (Port V)) = _
    symm
    rw [filter_eq_empty_iff]
    intro p hp hpu
    apply hu
    have := hP hp
    unfold allPorts portsOf at this
    obtain ⟨v, hv, hpv⟩ := mem_biUnion.1 this
    rw [← hpu, (mem_portsAt.1 hpv).1]
    exact hv

lemma envOf_clInst (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C) (pl : Multiset (PktP V))
    (lam : ℕ) {R t : ℕ} (hRe : Rf (nodes C).card C.card = R) (hte : tf (nodes C).card C.card = t)
    (τ : V → RWΩ V Rf ℓ) (u : V) :
    envOf Rf ℓ tf ((clInst N C).ctx u) (inpAt (clInst N C) (inOf (rinAt P pl lam)) u) (τ u) =
      envG C P R t τ u := by
  subst hRe hte
  unfold envOf envG
  rw [show ((clInst N C).ctx u).me = u from rfl, viewE_clInst hCN, myPorts_clInst hP]
  rfl

end Env

/-- The digit bound: `Bw ≤ kB` when `R + 2ℓ + 2 ≤ (n + 4)^kB`. -/
lemma log_le_of (n x kB : ℕ) (h : x ≤ (n + 4) ^ kB) : Nat.log (n + 4) x ≤ kB := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have : x < (n + 4) ^ (kB + 1) :=
      lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by omega))
    have := Nat.log_lt_of_lt_pow (by omega) this
    omega

/-- **Success on the good event**: if the walks under `rwSeedMap C P hR τ` do not overflow and
meet the public parameters, the run succeeds. -/
theorem rw_succ (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data)
    (N : WNet V) (C : Finset (Sym2 V)) (P : Finset (Port V)) (Good : G0Data → Prop)
    (pl : Multiset (PktP V)) (lam : ℕ)
    (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C) (hG : Good (gf (nodes C).card C.card))
    {R t kB : ℕ} (hRe : Rf (nodes C).card C.card = R) (hte : tf (nodes C).card C.card = t)
    (hkB : R + 2 * ℓ + 2 ≤ (Fintype.card V + 4) ^ kB)
    (hR : R ≤ rwRmax Rf (Fintype.card V)) (τ : V → RWΩ V Rf ℓ)
    (hgood : ¬ (rwOverflow C P R ℓ t (rwSeedMap C P hR τ) ∨
      ¬ TrueParams C P R ℓ (rwSeedMap C P hR τ) (gf (nodes C).card C.card))) :
    Succ (rwProto Rf ℓ tf gf V) (clInst N C) (inOf (rinAt P pl lam))
      (postOf (clInst N C) (fun z : Agent V → G0K V =>
        ∃ (R ℓ : ℕ) (ω : RWSeeds C P R ℓ) (g : G0Data), TrueParams C P R ℓ ω g ∧ Good g ∧
          ∀ v ∈ nodes C, z (.inl v) = g0At C P R ℓ ω g (.inl v)))
      (Prof.mk (48 * (kB + 2) * (R + ℓ * t + 1)) (onEdges C (48 * (kB + 2) * (R + ℓ * t + 1)))
        (48 * (kB + 2) * (P.card * R * (ℓ + 1)))) τ := by
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  have hD : seedRange C ∣ rwDmax (Fintype.card V) := seedRange_dvd_rwDmax C hC
  have hpos : 0 < rwDmax (Fintype.card V) := rwDmax_pos _
  rw [not_or, not_not] at hgood
  obtain ⟨hov, hTP⟩ := hgood
  obtain ⟨Bw, hBw⟩ : ∃ Bw, Nat.log (Fintype.card V + 4) (R + 2 * ℓ + 2) = Bw := ⟨_, rfl⟩
  have hBwlt : R + 2 * ℓ + 2 < (Fintype.card V + 4) ^ (Bw + 1) := by
    rw [← hBw]; exact Nat.lt_pow_succ_log_self (by omega) _
  have hBwk : Bw ≤ kB := hBw ▸ log_le_of _ _ kB hkB
  have hL : encLen Bw 5 ≤ 6 * (kB + 2) := by unfold encLen; omega
  have hOK : PktSchedOK (RWΩ V Rf ℓ) 5
      (fun c inp τy h v => sendL (envOf Rf ℓ tf c inp τy) (pget h) h.length v)
      (clInst N C) (inOf (rinAt P pl lam)) τ (tEndRW R t ℓ) Bw
      (fun u v s => schedG C P R t τ s u v) := by
    refine ⟨fun s _ u v _ => ?_, fun s u v hadj => ?_, fun u v s m h => ?_⟩
    · dsimp only
      rw [length_pschedHist, pget_pschedHist_eq, envOf_clInst Rf ℓ tf hCN hP pl lam hRe hte]
      exact (schedG_eq_trunc C P R t τ s u v).symm
    · by_contra h
      exact hadj (schedG_adj τ hCN hP s u v (Option.ne_none_iff_isSome.1 h))
    · obtain ⟨hl, hnum⟩ := schedG_small τ N hCN hP hD hpos hov s u v m h
      exact ⟨hl, fun k hk => by have := hnum k hk; omega⟩
  have hcount := sum_schedG_le τ N hCN hP hD hpos hov
  have hT4 : tEndRW R t ℓ ≤ 4 * (R + ℓ * t + 1) := by unfold tEndRW; nlinarith
  have hT : ∀ v, tEndOf Rf ℓ tf ((clInst N C).ctx v) = tEndRW R t ℓ := fun v => by
    rw [← hRe, ← hte]; rfl
  have hB : ∀ v, bwOf Rf ℓ ((clInst N C).ctx v) = Bw := fun v => by
    rw [← hBw, ← hRe]; rfl
  unfold rwProto
  refine succ_pktP (T := tEndRW R t ℓ) (Bw := Bw) hT hB (fun u v s => schedG C P R t τ s u v) hOK
    ?_ ?_ ?_ (fun g => match g with
      | .inl v => ⟨G0K V, (gf (nodes C).card C.card,
          outMS (envG C P R t τ v) (fullO C P R t τ v))⟩
      | .inr _ => ⟨G0K V, (gf (nodes C).card C.card, 0)⟩) ?_ ?_
  · -- rounds
    simp only [Prof.rounds_mk]
    calc tEndRW R t ℓ * encLen Bw 5 ≤ (4 * (R + ℓ * t + 1)) * (6 * (kB + 2)) :=
          Nat.mul_le_mul hT4 hL
      _ ≤ 48 * (kB + 2) * (R + ℓ * t + 1) := by nlinarith
  · -- messages
    simp only [Prof.msgs_mk]
    calc encLen Bw 5 * ∑ s ∈ range (tEndRW R t ℓ),
          (univ.filter (fun uv : V × V => (schedG C P R t τ s uv.1 uv.2).isSome)).card
        ≤ (6 * (kB + 2)) * (P.card * R * (4 * ℓ + 2)) := Nat.mul_le_mul hL hcount
      _ ≤ 48 * (kB + 2) * (P.card * R * (ℓ + 1)) := by
          have h0 : P.card * R * (4 * ℓ + 2) ≤ 4 * (P.card * R * (ℓ + 1)) := by
            have : 4 * ℓ + 2 ≤ 4 * (ℓ + 1) := by omega
            calc P.card * R * (4 * ℓ + 2) ≤ P.card * R * (4 * (ℓ + 1)) :=
                  Nat.mul_le_mul_left _ this
              _ = 4 * (P.card * R * (ℓ + 1)) := by ring
          have h1 := Nat.mul_le_mul_left (6 * (kB + 2)) h0
          have h2 : 6 * (kB + 2) * (4 * (P.card * R * (ℓ + 1))) ≤
              48 * (kB + 2) * (P.card * R * (ℓ + 1)) := by
            have := Nat.mul_le_mul_right (P.card * R * (ℓ + 1))
              (show 6 * (kB + 2) * 4 ≤ 48 * (kB + 2) by omega)
            calc _ = 6 * (kB + 2) * 4 * (P.card * R * (ℓ + 1)) := by ring
              _ ≤ _ := this
          exact h1.trans h2
  · -- load
    intro e
    simp only [Prof.load_mk, onEdges]
    split_ifs with he
    · have h2 : ∀ s, ((univ.filter (fun uv : V × V => (schedG C P R t τ s uv.1 uv.2).isSome)).filter
          (fun uv => s(uv.1, uv.2) = e)).card ≤ 2 := fun s =>
        le_trans (card_le_card (fun uv huv => by
          simp only [mem_filter, mem_univ, true_and] at huv ⊢; exact huv.2))
          (card_sym2_fiber e)
      have h3 := Nat.mul_le_mul_left (12 * (kB + 2)) hT4
      calc encLen Bw 5 * ∑ s ∈ range (tEndRW R t ℓ), ((univ.filter (fun uv : V × V =>
            (schedG C P R t τ s uv.1 uv.2).isSome)).filter (fun uv => s(uv.1, uv.2) = e)).card
          ≤ (6 * (kB + 2)) * ∑ _s ∈ range (tEndRW R t ℓ), 2 :=
            Nat.mul_le_mul hL (sum_le_sum (fun s _ => h2 s))
        _ = (6 * (kB + 2)) * (2 * tEndRW R t ℓ) := by
            rw [sum_const, card_range, smul_eq_mul]; ring
        _ ≤ 48 * (kB + 2) * (R + ℓ * t + 1) := by nlinarith
    · have h0 : ∀ s, ((univ.filter (fun uv : V × V => (schedG C P R t τ s uv.1 uv.2).isSome)).filter
          (fun uv => s(uv.1, uv.2) = e)).card = 0 := by
        intro s
        rw [card_eq_zero, filter_eq_empty_iff]
        intro uv huv heq
        rw [mem_filter] at huv
        have hadj := schedG_adj (N := N) τ hCN hP s uv.1 uv.2 huv.2
        exact he (heq ▸ hadj.1.2)
      simp [h0]
  · -- outputs
    intro g v hg
    cases g with
    | inr Cc => simp [clInst, clInstP, clHost] at hg
    | inl u =>
      have huv : u = v := by
        simp only [clInst, clInstP, clHost] at hg
        by_cases hu : u ∈ nodes C
        · rw [if_pos hu] at hg; exact Option.some.inj hg
        · rw [if_neg hu] at hg; exact absurd hg (by simp)
      subst huv
      dsimp only
      rw [if_pos (show (Sum.inl u : Agent V) = Sum.inl ((clInst N C).ctx u).me from rfl),
        envOf_clInst Rf ℓ tf hCN hP pl lam hRe hte, pget_pschedHist_eq,
        outMS_congr _ (H' := fullO C P R t τ u) (fun s hs => by
          funext w
          simp only [envG_R, envG_t, envG_ℓ] at hs
          simp [hs, fullO])]
      rfl
  · -- the postcondition
    refine ⟨fun g => match g with
      | .inl v => (gf (nodes C).card C.card, outMS (envG C P R t τ v) (fullO C P R t τ v))
      | .inr _ => (gf (nodes C).card C.card, 0), fun g _ => by cases g <;> rfl,
      R, ℓ, rwSeedMap C P hR τ, gf (nodes C).card C.card, hTP, hG, fun v _ => ?_⟩
    exact outMS_eq hD hpos N hCN hP t hov v (gf (nodes C).card C.card)

/-- **The random-walk construction** in the CONGEST semantics. -/
theorem rwLink_impl (kB : ℕ) (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data)
    (N : WNet V) (C : Finset (Sym2 V)) (P : Finset (Port V)) (Good : G0Data → Prop)
    (hCN : C ⊆ N.G.edgeFinset) (hP : P ⊆ allPorts C) (hG : Good (gf (nodes C).card C.card))
    (hkB : Rf (nodes C).card C.card + 2 * ℓ + 2 ≤ (Fintype.card V + 4) ^ kB) :
    CImplT (rwAlgC Rf ℓ tf gf) N (.buildG0 C P Good)
      (Prof.mk (48 * (kB + 2) * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1))
        (onEdges C (48 * (kB + 2) *
          (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1)))
        (48 * (kB + 2) * (P.card * Rf (nodes C).card C.card * (ℓ + 1))))
      (rwProb C P (Rf (nodes C).card C.card) ℓ (fun ω =>
        rwOverflow C P (Rf (nodes C).card C.card) ℓ (tf (nodes C).card C.card) ω ∨
        ¬ TrueParams C P (Rf (nodes C).card C.card) ℓ ω (gf (nodes C).card C.card))) := by
  intro pl lam
  have hC : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  have hR : Rf (nodes C).card C.card ≤ rwRmax Rf (Fintype.card V) := by
    refine le_rwRmax Rf (card_le_univ _) ?_
    calc C.card ≤ Fintype.card (Sym2 V) := card_le_univ _
      _ ≤ Fintype.card V ^ 2 := by
          have := Fintype.card_le_of_surjective _ (Sym2.mk_surjective (α := V))
          rwa [Fintype.card_prod, ← pow_two] at this
  have hD : seedRange C ∣ rwDmax (Fintype.card V) := seedRange_dvd_rwDmax C hC
  have hpos : 0 < rwDmax (Fintype.card V) := rwDmax_pos _
  have hsucc := fun τ h => rw_succ (kB := kB) Rf ℓ tf gf N C P Good pl lam hCN hP hG rfl rfl hkB
    hR τ h
  show failProb (rwProto Rf ℓ tf gf V) (clInst N C) (inOf (rinAt P pl lam)) _ _ ≤ _
  classical
  rw [← rwSeedMap_prob hD hpos hR (fun ω =>
    rwOverflow C P (Rf (nodes C).card C.card) ℓ (tf (nodes C).card C.card) ω ∨
    ¬ TrueParams C P (Rf (nodes C).card C.card) ℓ ω (gf (nodes C).card C.card))]
  unfold failProb
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast card_le_card (fun τ hτ => by
    have hτ' := (mem_filter.1 hτ).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    by_contra h
    exact hτ' (hsucc τ h))

/-- The toolkit field `rwLink` for the CONGEST semantics, for a given algorithm constructor
(the field `rwLink` of `Toolkit.lean` with `Impl := CImplT`). -/
def RWLinkFor (rwAlg : (ℕ → ℕ → ℕ) → ℕ → (ℕ → ℕ → ℕ) → (ℕ → ℕ → G0Data) → CAlg) : Prop :=
  ∀ kB : ℕ, ∃ Kc : ℕ, ∀ (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data)
    {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (C : Finset (Sym2 V)) (P : Finset (Port V))
    (Good : G0Data → Prop),
    C ⊆ N.G.edgeFinset → C.Nonempty → P ⊆ allPorts C → Good (gf (nodes C).card C.card) →
    Rf (nodes C).card C.card + 2 * ℓ + 2 ≤ (Fintype.card V + 4) ^ kB →
    CImplT (rwAlg Rf ℓ tf gf) N (.buildG0 C P Good)
      (Prof.mk (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1))
        (onEdges C (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1)))
        (Kc * (P.card * Rf (nodes C).card C.card * (ℓ + 1))))
      (rwProb C P (Rf (nodes C).card C.card) ℓ (fun ω =>
        rwOverflow C P (Rf (nodes C).card C.card) ℓ (tf (nodes C).card C.card) ω ∨
        ¬ TrueParams C P (Rf (nodes C).card C.card) ℓ ω (gf (nodes C).card C.card)))

/-- **The toolkit field `rwLink`** for the CONGEST semantics, with `rwAlg := rwAlgC` (`Model.lean`
checks that it is the toolkit's field: `toToolkit` sets `rwAlg := rwAlgC`,
`rwLink := rwLink_congest`). -/
def RWLinkC : Prop :=
  ∀ kB : ℕ, ∃ Kc : ℕ, ∀ (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data)
    {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (C : Finset (Sym2 V)) (P : Finset (Port V))
    (Good : G0Data → Prop),
    C ⊆ N.G.edgeFinset → C.Nonempty → P ⊆ allPorts C → Good (gf (nodes C).card C.card) →
    Rf (nodes C).card C.card + 2 * ℓ + 2 ≤ (Fintype.card V + 4) ^ kB →
    CImplT (rwAlgC Rf ℓ tf gf) N (.buildG0 C P Good)
      (Prof.mk (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1))
        (onEdges C (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1)))
        (Kc * (P.card * Rf (nodes C).card C.card * (ℓ + 1))))
      (rwProb C P (Rf (nodes C).card C.card) ℓ (fun ω =>
        rwOverflow C P (Rf (nodes C).card C.card) ℓ (tf (nodes C).card C.card) ω ∨
        ¬ TrueParams C P (Rf (nodes C).card C.card) ℓ ω (gf (nodes C).card C.card)))

/-- `RWLinkC` is `RWLinkFor rwAlgC`. -/
example : RWLinkC = RWLinkFor rwAlgC := rfl

/-- **The field `rwLink`** for the concrete algorithm `rwAlgC` (used in `Model.lean`:
`rwAlg := rwAlgC`, `rwLink := rwLink_congest`). -/
theorem rwLink_congest : RWLinkC :=
  fun kB => ⟨48 * (kB + 2), fun Rf ℓ tf gf _ _ _ N C P Good hCN _ hP hG hkB =>
    rwLink_impl kB Rf ℓ tf gf N C P Good hCN hP hG hkB⟩

/-- The same statement, written out. -/
theorem rwLink_congest' : ∀ kB : ℕ, ∃ Kc : ℕ, ∀ (Rf : ℕ → ℕ → ℕ) (ℓ : ℕ) (tf : ℕ → ℕ → ℕ) (gf : ℕ → ℕ → G0Data)
    {V : Type} [Fintype V]
    [DecidableEq V] (N : WNet V) (C : Finset (Sym2 V)) (P : Finset (Port V))
    (Good : G0Data → Prop),
    C ⊆ N.G.edgeFinset → C.Nonempty → P ⊆ allPorts C → Good (gf (nodes C).card C.card) →
    Rf (nodes C).card C.card + 2 * ℓ + 2 ≤ (Fintype.card V + 4) ^ kB →
    CImplT (rwAlgC Rf ℓ tf gf) N (.buildG0 C P Good)
      (Prof.mk (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1))
        (onEdges C (Kc * (Rf (nodes C).card C.card + ℓ * tf (nodes C).card C.card + 1)))
        (Kc * (P.card * Rf (nodes C).card C.card * (ℓ + 1))))
      (rwProb C P (Rf (nodes C).card C.card) ℓ (fun ω =>
        rwOverflow C P (Rf (nodes C).card C.card) ℓ (tf (nodes C).card C.card) ω ∨
        ¬ TrueParams C P (Rf (nodes C).card C.card) ℓ ω (gf (nodes C).card C.card))) :=
  rwLink_congest

end APSP.Stoc.Congest
