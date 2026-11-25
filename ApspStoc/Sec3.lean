import ApspStoc.Basics
import ApspStoc.G0

/-!
# Section 3: Theorem 3.3, Lemmas 3.8 and 3.9, Lemma 2.10 and Theorem 3.10

Theorem 3.3 is derived from Claims 3.4/3.5 (`buildG0_of`, proved in `G0.lean` from the
random-walk link and `Mixing`) and Lemma 3.2 (`routeG0`).
-/

namespace APSP.Stoc

open APSP Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Arithmetic of Theorem 3.3. -/
lemma thm33_arith (a A1 A2 nC lam mC : ℕ) (hn : 1 ≤ nC) (hm : mC ≤ nC ^ 2) :
    A1 * (mC / nC + 1) + 2 * ((a + 1) * A1 * A2) * (nC + lam) ≤
        4 * (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) * (nC + lam) ∧
    (∀ dil, dil ≤ A1 → A2 * dil ≤ 4 * (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1)) ∧
    2 * ((a + 1) * A1 * A2) ≤ 4 * (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) ∧
    (∀ sz, A1 * mC + A2 * (A1 * (a * nC) * (a * nC) + sz) ≤
        4 * (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) * (nC ^ 2 + sz)) ∧
    A2 ≤ 4 * (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) := by
  have hX : 4 * (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) = 4 * ((a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1)) := by
    ring
  rw [hX]
  generalize hXd : (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) = X
  have h1 : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : A1 + 1 ≤ (A1 + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1' : a + 1 ≤ (a + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hA1X : A1 + 1 ≤ X := by
    rw [← hXd]
    calc A1 + 1 = 1 * (A1 + 1) * 1 := by ring
      _ ≤ (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (by omega)
  have hA12X : (a + 1) * A1 * A2 ≤ X := by
    rw [← hXd]; exact Nat.mul_le_mul (Nat.mul_le_mul h1' (by omega)) (by omega)
  have hA12X' : A1 * A2 * (a * a) ≤ X := by
    rw [← hXd]
    calc A1 * A2 * (a * a) ≤ ((A1 + 1) * (A1 + 1)) * (A2 + 1) * ((a + 1) * (a + 1)) := by
          gcongr <;> nlinarith
      _ = (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) := by ring
  have hA21X : A2 * A1 ≤ X := by
    have : A2 * A1 ≤ (a + 1) * A1 * A2 := by
      rw [show (a + 1) * A1 * A2 = A2 * A1 + a * (A1 * A2) by ring]; omega
    omega
  have hA2X : A2 ≤ X := by
    rw [← hXd]
    calc A2 ≤ 1 * 1 * (A2 + 1) := by omega
      _ ≤ (a + 1) ^ 2 * (A1 + 1) ^ 2 * (A2 + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 (Nat.one_le_pow _ _ (by omega))) le_rfl
  have hdiv : mC / nC ≤ nC := Nat.div_le_of_le_mul (by nlinarith)
  refine ⟨?_, fun dil hdil => ?_, by omega, fun sz => ?_, by omega⟩
  · have t1 : A1 * (mC / nC + 1) ≤ X * (2 * nC) := Nat.mul_le_mul (by omega) (by omega)
    have t2 : 2 * ((a + 1) * A1 * A2) * (nC + lam) ≤ 2 * X * (nC + lam) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · have : A2 * dil ≤ A2 * A1 := Nat.mul_le_mul_left _ hdil
    omega
  · have t1 : A1 * mC ≤ X * nC ^ 2 := Nat.mul_le_mul (by omega) hm
    have t2 : A2 * (A1 * (a * nC) * (a * nC) + sz) =
        (A1 * A2 * (a * a)) * nC ^ 2 + A2 * sz := by ring
    have t3 : (A1 * A2 * (a * a)) * nC ^ 2 ≤ X * nC ^ 2 := Nat.mul_le_mul_right _ hA12X'
    have t4 : A2 * sz ≤ X * sz := Nat.mul_le_mul_right _ hA2X
    nlinarith

/-- Lifting a polylog bound `K·lg^k` to the larger `(K + K')·lg^(k + k')`. -/
lemma le_lgpow_add_left {a K K' k k' ν : ℕ} (h : a ≤ K * lg ν ^ k) :
    a ≤ (K + K') * lg ν ^ (k + k') :=
  h.trans (Nat.mul_le_mul (Nat.le_add_right K K')
    (Nat.pow_le_pow_right (lg_pos ν) (Nat.le_add_right k k')))

/-- Lifting a polylog bound `K'·lg^k'` to the larger `(K + K')·lg^(k + k')`. -/
lemma le_lgpow_add_right {a K K' k k' ν : ℕ} (h : a ≤ K' * lg ν ^ k') :
    a ≤ (K + K') * lg ν ^ (k + k') :=
  h.trans (Nat.mul_le_mul (Nat.le_add_left K' K)
    (Nat.pow_le_pow_right (lg_pos ν) (Nat.le_add_left k' k)))

set_option maxHeartbeats 1000000 in
/-- **Theorem 3.3** (message-efficient expander routing), derived from Claims 3.4/3.5 and
Lemma 3.2 + Lemma 2.2: in a `1/polylog`-expander cluster `C`, a demand supported on a port set
`P` with `n_C ≤ |P| ≤ a·n_C` and load `λ`, whose packets carry payloads of at most `pw` words, is
routed (preprocessing included) in `Õ(n_C + λ)` rounds and `Õ(n_C² + M)` messages, along recorded
routes of polylog length inside `C` (the polylog factor depends on `pw`). -/
theorem thm_3_3 (T : Toolkit) (hmix : Mixing) (c a Kφ kφ pw : ℕ) :
    ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
      (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
      ∀ (C : Finset (Sym2 V)) (P : Finset (Port V)) (φinv : ℕ) (D : Demand V) (lam : ℕ),
      C ⊆ N.G.edgeFinset → C.Nonempty → IsExpander C φinv → φinv ≤ Kφ * lg ν ^ kφ → P ⊆ allPorts C → (nodes C).card ≤ P.card →
      P.card ≤ a * (nodes C).card → D.SupportedOn P → (∀ x, D.load x ≤ lam) →
      T.Impl (A ν) N (.route C P D lam pw (fun r => RoutesOK C D r (q ν)
          (2 * (q ν * ((nodes C).card + lam)))))
        (Prof.mk (q ν * ((nodes C).card + lam)) (onEdges C (2 * (q ν * ((nodes C).card + lam))))
          (q ν * ((nodes C).card ^ 2 + D.size)))
        (whp Kδ c ν) := by
  obtain ⟨K1, k1, Kδ1, AB, hB⟩ := buildG0_of T (rwLink_of_toolkit T) hmix c a Kφ kφ
  -- `G₀` has polynomial size (`n₀ ≤ a·n_C ≤ a·n`), so `routeG0` applies with `Kφ ≥ a`
  obtain ⟨K2, k2, Kδ2, h, Kb, kb, Kτ, AR, hR⟩ := T.routeG0 c (K1 + Kφ + a) (k1 + kφ) pw
  let B1 : ℕ → ℕ := fun ν => K1 * lg ν ^ k1 + 1
  -- the length bound `dil·τ·(1 + (2b + 1)^h (b + 1))` of the routes of `routeG0` (`dil ≤ A1`,
  -- `φ(G₀)⁻¹ ≤ A1`); it is polylog since `h` is a constant
  let BL : ℕ → ℕ := fun ν => K1 * lg ν ^ k1 * (Kτ * (K1 * lg ν ^ k1 + 1) ^ 2 * lg ν) *
    (1 + (2 * (Kb * lg ν ^ kb) + 1) ^ h * (Kb * lg ν ^ kb + 1))
  let B2 : ℕ → ℕ := fun ν => K2 * lg ν ^ k2 * (K1 * lg ν ^ k1 + 1) ^ 2 + BL ν + 1
  have hB1 : IsPL B1 := ((IsPL.const K1).mul (IsPL.lgpow k1)).add (IsPL.const 1)
  have hb : IsPL (fun ν => Kb * lg ν ^ kb) := (IsPL.const Kb).mul (IsPL.lgpow kb)
  have hBL : IsPL BL :=
    (((IsPL.const K1).mul (IsPL.lgpow k1)).mul (((IsPL.const Kτ).mul (hB1.pow 2)).mul IsPL.lg')).mul
      ((IsPL.const 1).add ((((IsPL.const 2).mul hb).add (IsPL.const 1)).pow h |>.mul
        (hb.add (IsPL.const 1))))
  have hB2 : IsPL B2 :=
    ((((IsPL.const K2).mul (IsPL.lgpow k2)).mul (hB1.pow 2)).add hBL).add (IsPL.const 1)
  refine ⟨fun ν => 4 * (a + 1) ^ 2 * B1 ν ^ 2 * B2 ν,
    (((IsPL.const (4 * (a + 1) ^ 2)).mul (hB1.pow 2)).mul hB2), Kδ1 + Kδ2,
    fun ν => T.seq (AB ν) (AR ν), ?_⟩
  intro V _ _ N ν hν hνn C P φinv D lam hC hne hexp hφ hP hP1 hP2 hD hlam
  have hnl : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hC he)
  have hn2 := two_le_card_nodes hnl hne
  have hm : C.card ≤ (nodes C).card ^ 2 := card_le_sq hnl
  set nC := (nodes C).card with hnC
  set A1 := K1 * lg ν ^ k1
  set A2 := K2 * lg ν ^ k2
  set L := BL ν
  -- the routing constant absorbs the factors `(dil + 1)` of `routeG0` (`dil ≤ A1`) and the
  -- length bound `L` of its routes
  set A2' := A2 * (A1 + 1) ^ 2 + L with hA2'
  have hA2le0 : A2 ≤ A2 * (A1 + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hA2le : A2 ≤ A2' := hA2le0.trans (Nat.le_add_right _ _)
  have hAr := thm33_arith a A1 A2' nC lam C.card (by omega) hm
  have h1 := hB N ν hν hνn C P φinv hC hne hexp hφ hP hP1 hP2
  obtain ⟨q2, hq2⟩ : ∃ q2 : Prof V, q2 = Prof.mk (2 * ((a + 1) * A1 * A2') * (nC + lam))
      (onEdges C (2 * (2 * ((a + 1) * A1 * A2') * (nC + lam))))
      (A2' * (A1 * (a * nC) * (a * nC) + D.size)) := ⟨_, rfl⟩
  have hfail : whp Kδ1 c ν + whp Kδ2 c ν ≤ whp (Kδ1 + Kδ2) c ν := by rw [whp_add]
  refine T.mono (T.g0Then (q := q2) (δ' := whp Kδ2 c ν) h1 (fun g hg => ?_)
    (whp_nonneg _ _ _)) ?_ hfail
  · -- route through any `G₀` satisfying the guarantees of Claims 3.4/3.5
    obtain ⟨hn0, hn0', hm0, hφ0, hc0, hd0⟩ := hg
    have hKφ : K1 + Kφ ≤ K1 + Kφ + a := Nat.le_add_right _ _
    have hnν : g.n0 ≤ (K1 + Kφ + a) * ν :=
      hn0'.trans (Nat.mul_le_mul (Nat.le_add_left _ _) ((card_le_univ _).trans hν))
    have h2 := hR N ν hν hνn C P φinv g D lam hC hexp
      ((le_lgpow_add_right hφ).trans (Nat.mul_le_mul_right _ hKφ)) hP hn0 hnν
      (hm0.trans (Nat.mul_le_mul_right _ ((le_lgpow_add_left le_rfl).trans
        (Nat.mul_le_mul_right _ hKφ))))
      ((le_lgpow_add_left hφ0).trans (Nat.mul_le_mul_right _ hKφ)) hD hlam
    have hR1 : A2 * (g.n0 + lam) * (g.cong + g.dil) ≤ 2 * ((a + 1) * A1 * A2) * (nC + lam) := by
      have e1 : g.n0 + lam ≤ (a + 1) * (nC + lam) := by nlinarith
      have e2 : g.cong + g.dil ≤ A1 + A1 := Nat.add_le_add hc0 hd0
      calc A2 * (g.n0 + lam) * (g.cong + g.dil) ≤ A2 * ((a + 1) * (nC + lam)) * (A1 + A1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) e2
        _ = 2 * ((a + 1) * A1 * A2) * (nC + lam) := by ring
    have hR2 : A2 * (g.n0 + lam) * (g.cong + g.dil) * (g.dil + 1) ≤
        2 * ((a + 1) * A1 * A2') * (nC + lam) := by
      have hd1 : g.dil + 1 ≤ (A1 + 1) ^ 2 :=
        (Nat.succ_le_succ hd0).trans (Nat.le_self_pow (by norm_num) _)
      calc A2 * (g.n0 + lam) * (g.cong + g.dil) * (g.dil + 1)
          ≤ 2 * ((a + 1) * A1 * A2) * (nC + lam) * (A1 + 1) ^ 2 := Nat.mul_le_mul hR1 hd1
        _ = 2 * ((a + 1) * A1 * (A2 * (A1 + 1) ^ 2)) * (nC + lam) := by ring
        _ ≤ 2 * ((a + 1) * A1 * A2') * (nC + lam) := by
            rw [hA2']; gcongr; exact Nat.le_add_right _ _
    rw [hq2]
    refine T.mono (T.routeViaWeaken (fun r hr => ?_) h2) (Prof.le_mk _ _ _ _ hR2
      (fun e => onEdges_mono C (Nat.mul_le_mul_left 2 hR2) e) ?_) le_rfl
    · -- the length bound is derived from the structure of the routes
      have hlen : g.dil * (Kτ * (g.φinv + 1) ^ 2 * lg ν) *
          (1 + (2 * (Kb * lg ν ^ kb) + 1) ^ h * (Kb * lg ν ^ kb + 1)) ≤ A2' := by
        have hφ1 : g.φinv + 1 ≤ A1 + 1 := Nat.succ_le_succ hφ0
        calc _ ≤ A1 * (Kτ * (A1 + 1) ^ 2 * lg ν) *
              (1 + (2 * (Kb * lg ν ^ kb) + 1) ^ h * (Kb * lg ν ^ kb + 1)) := by gcongr
          _ = L := rfl
          _ ≤ A2' := Nat.le_add_left _ _
      refine hr.routesOK.mono (hlen.trans hAr.2.2.2.2) ?_
      have h3 : 2 * ((a + 1) * A1 * A2) ≤ 2 * ((a + 1) * A1 * A2') :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hA2le)
      exact Nat.mul_le_mul_left 2 (hR1.trans (Nat.mul_le_mul_right _ (h3.trans hAr.2.2.1) |>.trans
        (le_of_eq (by ring))))
    · show A2 * (g.m0 * g.n0 + D.size) * (g.dil + 1) ^ 2 ≤ A2' * (A1 * (a * nC) * (a * nC) + D.size)
      have hm0' : g.m0 ≤ A1 * (a * nC) := hm0.trans (Nat.mul_le_mul_left _ hn0')
      have hd1 : g.dil + 1 ≤ A1 + 1 := Nat.succ_le_succ hd0
      rw [hA2']
      calc A2 * (g.m0 * g.n0 + D.size) * (g.dil + 1) ^ 2
          ≤ A2 * (A1 * (a * nC) * (a * nC) + D.size) * (A1 + 1) ^ 2 := by gcongr
        _ = A2 * (A1 + 1) ^ 2 * (A1 * (a * nC) * (a * nC) + D.size) := by ring
        _ ≤ (A2 * (A1 + 1) ^ 2 + L) * (A1 * (a * nC) * (a * nC) + D.size) := by
            gcongr; exact Nat.le_add_right _ _
  · -- combine the costs
    rw [hq2]
    refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
    · exact hAr.1
    · simp only [Prof.load_add, Prof.load_mk, Pi.add_apply]
      rw [← Pi.add_apply (onEdges C _), onEdges_add]
      apply onEdges_mono
      have := Nat.mul_le_mul_left 2 hAr.1
      rw [mul_add] at this
      exact this
    · exact hAr.2.2.2.1 D.size



lemma portsA_subset_allPorts {C : Finset (Sym2 V)} (hC : NoLoops C) (hne : C.Nonempty) :
    portsA C ⊆ allPorts C := by
  unfold portsA allPorts portsOf
  exact biUnion_subset_biUnion_of_subset_left _ (aggSet_spec hC hne).top.1

lemma srcPort_mem_allPorts {C : Finset (Sym2 V)} {v : V} (hv : v ∈ nodes C) :
    srcPort C v ∈ allPorts C :=
  mem_allPorts.2 ⟨by rw [srcPort_fst]; exact hv, by rw [srcPort_fst]; exact srcPort_mem C hv⟩

lemma dummyRoutesOK_of_routesOK {C : Finset (Sym2 V)} {r : Routes V} {d B : ℕ}
    (h : RoutesOK C (portsDemand C) r d B) : DummyRoutesOK C r d B := by
  have hmem : ∀ v ∈ nodes C, ∀ p ∈ portsA C, (srcPort C v, p) ∈ portsDemand C :=
    fun v hv p hp => Multiset.mem_map.2 ⟨(v, p), by rw [mem_val]; exact mem_product.2 ⟨hv, hp⟩, rfl⟩
  refine ⟨fun v hv p hp => ?_, fun v hv p hp => h.local_ _ (hmem v hv p hp),
    fun v hv p hp => h.len _ (hmem v hv p hp), fun e => ?_⟩
  · have := h.walk _ (hmem v hv p hp); rwa [srcPort_fst] at this
  have := h.cong e
  unfold portsDemand at this
  rw [Multiset.map_map] at this
  rw [sum_eq_multiset_sum]; exact this

/-- **Lemma 3.9**: every node of `C` sends one packet (without payload) to every port of `A(C)` in
`Õ(n_C)` rounds and `Õ(n_C²)` messages; the recorded routes have polylog length and congestion
`Õ(n_C)`. -/
theorem lemma_3_9 (T : Toolkit) (hmix : Mixing) (c Kφ kφ : ℕ) :
    ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
      (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
      ∀ (C : Finset (Sym2 V)) (φinv : ℕ),
      C ⊆ N.G.edgeFinset → C.Nonempty → IsExpander C φinv → φinv ≤ Kφ * lg ν ^ kφ →
      T.Impl (A ν) N (.route C (portsP C) (portsDemand C) (3 * (nodes C).card) 0
          (fun r => DummyRoutesOK C r (q ν) (q ν * (nodes C).card)))
        (Prof.mk (q ν * (nodes C).card) (onEdges C (q ν * (nodes C).card))
          (q ν * (nodes C).card ^ 2))
        (whp Kδ c ν) := by
  obtain ⟨q₀, hq₀, Kδ, A, h⟩ := thm_3_3 T hmix c 3 Kφ kφ 0
  refine ⟨fun ν => 8 * q₀ ν, (IsPL.const 8).mul hq₀, Kδ, A, ?_⟩
  intro V _ _ N ν hν hνn C φinv hC hne hexp hφ
  have hnl : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hC he)
  have hb := card_portsA_bounds hnl hne
  set nC := (nodes C).card
  have hsub : portsP C ⊆ allPorts C := by
    intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact portsA_subset_allPorts hnl hne hx
    · obtain ⟨v, hv, rfl⟩ := mem_image.1 hx; exact srcPort_mem_allPorts hv
  have hP1 : nC ≤ (portsP C).card := hb.1.trans (card_le_card portsA_subset_portsP)
  have hP2 : (portsP C).card ≤ 3 * nC := by have := portsP_card_le (C := C); omega
  have hload : ∀ x, (portsDemand C).load x ≤ 3 * nC := fun x => by
    have := portsDemand_load (C := C) x; omega
  have hsize : (portsDemand C).size ≤ 2 * nC ^ 2 := by
    rw [portsDemand_size]; nlinarith
  have h1 := h N ν hν hνn C (portsP C) φinv (portsDemand C) (3 * nC) hC hne hexp hφ hsub hP1 hP2
    portsDemand_supported hload
  refine T.mono (T.routeWeaken (fun r hr => dummyRoutesOK_of_routesOK
    (hr.mono (by nlinarith) (by nlinarith))) h1) (Prof.le_mk _ _ _ _ ?_ ?_ ?_) le_rfl
  · simp only [Prof.rounds_mk]; nlinarith
  · intro e; exact onEdges_mono C (by nlinarith) e
  · simp only [Prof.msgs_mk]; nlinarith

/-- **Lemma 3.8**: the topology of `C` can be collected at `A(C)` in `Õ(n_C)` rounds and
`Õ(n_C²)` messages. Every topology packet carries its edge and the edge's weight (`wexp + 2` words
for weights at most `n^wexp`). -/
theorem lemma_3_8 (T : Toolkit) (hmix : Mixing) (wexp c Kφ kφ : ℕ) :
    ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V] [DecidableEq V]
      (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
      ∀ (C : Finset (Sym2 V)) (φinv : ℕ),
      C ⊆ N.G.edgeFinset → C.Nonempty → IsExpander C φinv → φinv ≤ Kφ * lg ν ^ kφ →
      T.Impl (A ν) N (.route C (topoP C) (topoDemand C) (6 * (nodes C).card) (wexp + 2)
          (fun _ => True))
        (Prof.mk (q ν * (nodes C).card) (onEdges C (q ν * (nodes C).card))
          (q ν * (nodes C).card ^ 2))
        (whp Kδ c ν) := by
  obtain ⟨q₀, hq₀, Kδ, A, h⟩ := thm_3_3 T hmix c 7 Kφ kφ (wexp + 2)
  refine ⟨fun ν => 14 * q₀ ν, (IsPL.const 14).mul hq₀, Kδ, A, ?_⟩
  intro V _ _ N ν hν hνn C φinv hC hne hexp hφ
  have hnl : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hC he)
  have hb := card_portsA_bounds hnl hne
  have hn2 := two_le_card_nodes hnl hne
  have hA := aggSet_spec hnl hne
  have hqm := aggSet_card_mul_lt hA (fun v hv => degIn_succ_le hnl hv) (sum_degIn hnl)
  set nC := (nodes C).card
  have hsub : topoP C ⊆ allPorts C := by
    intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact portsA_subset_allPorts hnl hne hx
    · obtain ⟨v, hv, hx'⟩ := mem_biUnion.1 hx
      have h' := srcSet_sub C v hx'
      exact mem_allPorts.2 ⟨by rw [(mem_portsAt.1 h').1]; exact hv,
        by rw [(mem_portsAt.1 h').1]; exact h'⟩
  have hP1 : nC ≤ (topoP C).card := hb.1.trans (card_le_card portsA_subset_topoP)
  have hP2 : (topoP C).card ≤ 7 * nC := topoP_card_le hnl hne
  have hload : ∀ x, (topoDemand C).load x ≤ 6 * nC := fun x => by
    have := topoDemand_load hnl hne x; omega
  have hsize : (topoDemand C).size ≤ 2 * nC ^ 2 := by
    rw [topoDemand_size hnl]; nlinarith
  have h1 := h N ν hν hνn C (topoP C) φinv (topoDemand C) (6 * nC) hC hne hexp hφ hsub hP1 hP2
    (topoDemand_supported hnl hne) hload
  refine T.mono (T.routeWeaken (fun _ _ => trivial) h1) (Prof.le_mk _ _ _ _ ?_ ?_ ?_) le_rfl
  · simp only [Prof.rounds_mk]; nlinarith
  · intro e; exact onEdges_mono C (by nlinarith) e
  · simp only [Prof.msgs_mk]; nlinarith



lemma disjoint_of_disjoint_nodes {C C' : Finset (Sym2 V)} (h : Disjoint (nodes C) (nodes C')) :
    Disjoint C C' := by
  rw [disjoint_left]; intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
    have h1 : a ∈ nodes C := mem_nodes.2 ⟨_, he, Sym2.mem_mk_left a b⟩
    have h2 : a ∈ nodes C' := mem_nodes.2 ⟨_, he', Sym2.mem_mk_left a b⟩
    exact disjoint_left.1 h h1 h2

/-- Invariant of the iteration in the proof of Lemma 2.10 (`t` iterations remain). -/
structure DecompInv (G : SimpleGraph V) [DecidableRel G.Adj] (φ ovB : ℕ) (F : Finset (Sym2 V))
    (acc : Finset (Finset (Sym2 V))) (t : ℕ) : Prop where
  clus : ∀ C ∈ acc, C ⊆ G.edgeFinset ∧ C.Nonempty ∧ IsExpander C φ
  disj : ∀ C ∈ acc, ∀ C' ∈ acc, C ≠ C' → Disjoint C C'
  disjF : ∀ C ∈ acc, Disjoint C F
  cover : ∀ e ∈ G.edgeFinset, e ∈ F ∨ ∃ C ∈ acc, e ∈ C
  overlap : ∀ v, (clustersOf acc v).card + t ≤ ovB

lemma decompInv_step {G : SimpleGraph V} [DecidableRel G.Adj] {φ ovB : ℕ} {F : Finset (Sym2 V)}
    {acc P : Finset (Finset (Sym2 V))} {t : ℕ} (hI : DecompInv G φ ovB F acc (t + 1))
    (hP1 : ∀ C ∈ P, C ⊆ F ∧ C.Nonempty ∧ IsExpander C φ)
    (hP2 : ∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint (nodes C) (nodes C'))
    (hF : F ⊆ G.edgeFinset) :
    DecompInv G φ ovB (F \ P.biUnion id) (acc ∪ P) t := by
  have hPdisjF : ∀ C ∈ P, Disjoint C (F \ P.biUnion id) := fun C hC => by
    rw [disjoint_left]; intro e he he'
    exact (mem_sdiff.1 he').2 (mem_biUnion.2 ⟨C, hC, he⟩)
  refine ⟨fun C hC => ?_, fun C hC C' hC' hne => ?_, fun C hC => ?_, fun e he => ?_, fun v => ?_⟩
  · rcases mem_union.1 hC with h | h
    · exact hI.clus C h
    · obtain ⟨h1, h2, h3⟩ := hP1 C h; exact ⟨h1.trans hF, h2, h3⟩
  · rcases mem_union.1 hC with h | h <;> rcases mem_union.1 hC' with h' | h'
    · exact hI.disj C h C' h' hne
    · exact disjoint_of_subset_right (hP1 C' h').1 (hI.disjF C h)
    · exact (disjoint_of_subset_right (hP1 C h).1 (hI.disjF C' h')).symm
    · exact disjoint_of_disjoint_nodes (hP2 C h C' h' hne)
  · rcases mem_union.1 hC with h | h
    · exact disjoint_of_subset_right sdiff_subset (hI.disjF C h)
    · exact hPdisjF C h
  · rcases hI.cover e he with h | ⟨C, hC, heC⟩
    · by_cases hu : e ∈ P.biUnion id
      · obtain ⟨C, hC, heC⟩ := mem_biUnion.1 hu
        exact Or.inr ⟨C, mem_union_right _ hC, heC⟩
      · exact Or.inl (mem_sdiff.2 ⟨h, hu⟩)
    · exact Or.inr ⟨C, mem_union_left _ hC, heC⟩
  · have h1 : clustersOf (acc ∪ P) v ⊆ clustersOf acc v ∪ clustersOf P v := by
      intro C hC; unfold clustersOf at *; rw [mem_filter, mem_union] at hC
      rcases hC.1 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨h, hC.2⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨h, hC.2⟩)
    have h2 : (clustersOf P v).card ≤ 1 := by
      rw [card_le_one]; intro C hC C' hC'
      unfold clustersOf at hC hC'; rw [mem_filter] at hC hC'
      by_contra hne
      exact disjoint_left.1 (hP2 C hC.1 C' hC'.1 hne) hC.2 hC'.2
    have := (card_le_card h1).trans (card_union_le _ _)
    have := hI.overlap v
    omega

/-- `t` steps of the iterative decomposition, each running `A` (`dstep`), then nothing. -/
def iterAlg (T : Toolkit) (A : T.Alg) : ℕ → T.Alg
  | 0 => T.skip
  | t + 1 => T.dstep A (iterAlg T A t)

/-- **Lemma 2.10**: an expander edge decomposition with conductance `1/polylog(n)` and overlap
`O(log n)` in `polylog(n)` rounds and `Õ(m)` messages. -/
theorem lemma_2_10 (T : Toolkit) (c : ℕ) :
    ∃ K k : ℕ, ∃ q : ℕ → ℕ, IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg), ∀ {V : Type} [Fintype V]
      [DecidableEq V] (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν → ν ≤ Fintype.card V →
      T.Impl (A ν) N (.decompose (fun cl => DecompOK N.G cl (2 * K * lg ν ^ k + 1) (lg (ν ^ 2))))
        (Prof.mk (q ν) (fun _ => q ν) (q ν * ν ^ 2)) ((lg (ν ^ 2) : ℝ) * whp Kδ c ν) := by
  obtain ⟨K, k, Kδ, AX, hX⟩ := T.expDecomp c
  refine ⟨K, k, fun ν => lg (ν ^ 2) * (2 * K * lg ν ^ k * (2 * K * lg ν ^ k + 1) ^ 4), ?_, Kδ,
    fun ν => T.dstart (iterAlg T (AX ν (2 * K * lg ν ^ k + 1)) (lg (ν ^ 2))), ?_⟩
  · have hA : IsPL (fun ν => 2 * K * lg ν ^ k) := (IsPL.const (2 * K)).mul (IsPL.lgpow k)
    exact (IsPL.lg_pow_succ 1).mul (hA.mul ((hA.add (IsPL.const 1)).pow 4))
  intro V _ _ N ν hν hνn
  beta_reduce
  have hφ1 : 1 ≤ 2 * K * lg ν ^ k + 1 := by omega
  generalize hφ : 2 * K * lg ν ^ k + 1 = φ at hφ1 ⊢
  have hφA : φ = 2 * (K * lg ν ^ k) + 1 := by rw [← hφ]; ring
  obtain ⟨pstep, hps⟩ : ∃ p : Prof V, p = Prof.mk (K * lg ν ^ k * φ ^ 4)
      (fun _ => 2 * K * lg ν ^ k * φ ^ 4) (K * lg ν ^ k * φ ^ 4 * N.G.edgeFinset.card) := ⟨_, rfl⟩
  let Good : Finset (Finset (Sym2 V)) → Prop := fun cl => DecompOK N.G cl φ (lg (ν ^ 2))
  -- the iteration
  have iter : ∀ t, ∀ F acc, F ⊆ N.G.edgeFinset → F.card < 2 ^ t →
      DecompInv N.G φ (lg (ν ^ 2)) F acc t →
      T.Impl (iterAlg T (AX ν φ) t) N (.decompRest F acc Good) (t • pstep)
        ((t : ℝ) * whp Kδ c ν) := by
    intro t
    induction t with
    | zero =>
      intro F acc _ hcard hI
      have hF : F = ∅ := card_eq_zero.1 (by simpa using hcard)
      subst hF
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      apply T.decompBase
      refine ⟨fun C hC => (hI.clus C hC).1, fun C hC => (hI.clus C hC).2.1,
        fun C hC => (hI.clus C hC).2.2, hI.disj, fun e he => ?_, fun v => ?_⟩
      · rcases hI.cover e he with h | h
        · simp at h
        · exact h
      · have := hI.overlap v; omega
    | succ t ih =>
      intro F acc hF hcard hI
      have hstep := hX N ν hν hνn F φ hF hφ1
      have h2 := T.decompStep (acc := acc) (Good := Good) hstep (fun P hP => by
        obtain ⟨hP1, hP2, hP3⟩ := hP
        refine ih _ _ (sdiff_subset.trans hF) ?_ (decompInv_step hI hP1 hP2 hF)
        -- geometric decrease: at most half of the edges are crossing
        have h3 : 2 * (F \ P.biUnion id).card ≤ F.card := by
          rw [hφA] at hP3
          generalize K * lg ν ^ k = A at hP3
          rcases Nat.eq_zero_or_pos A with h0 | h0
          · subst h0; nlinarith
          · nlinarith
        rw [pow_succ] at hcard
        omega) (by exact mul_nonneg (Nat.cast_nonneg _) (whp_nonneg _ _ _))
      refine T.mono h2 ?_ ?_
      · rw [succ_nsmul, add_comm (t • pstep)]
        refine add_le_add_left ?_ _
        rw [hps]
        refine Prof.le_mk _ _ _ _ le_rfl (fun e => ?_) ?_
        · simp only [Prof.load_mk, onEdges]; split_ifs <;> simp
        · simp only [Prof.msgs_mk]
          exact Nat.mul_le_mul_left _ (card_le_card hF)
      · push_cast; linarith
  -- start the iteration with all edges; `lg(ν²)` iterations suffice for every network
  set m := N.G.edgeFinset.card with hmdef
  have hmν : m ≤ ν ^ 2 := by
    have h1 := N.G.card_edgeFinset_le_card_choose_two
    have h2 : (Fintype.card V).choose 2 ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
    exact h1.trans (h2.trans (Nat.pow_le_pow_left hν 2))
  have hm : m < 2 ^ lg (ν ^ 2) := lt_of_le_of_lt hmν (lt_two_pow_lg _)
  have hstart := iter (lg (ν ^ 2)) N.G.edgeFinset ∅ subset_rfl hm
    ⟨by simp, by simp, by simp, fun e he => Or.inl he, fun v => by simp [clustersOf]⟩
  have hA0 : K * lg ν ^ k * φ ^ 4 ≤ 2 * K * lg ν ^ k * φ ^ 4 := by
    have : 2 * K * lg ν ^ k * φ ^ 4 = 2 * (K * lg ν ^ k * φ ^ 4) := by ring
    omega
  refine T.mono (T.decompStart hstart) ?_ le_rfl
  rw [hps]
  refine Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_
  · simp only [Prof.rounds_smul, Prof.rounds_mk]
    exact Nat.mul_le_mul_left _ hA0
  · simp only [Prof.load_smul, Prof.load_mk, Pi.smul_apply, smul_eq_mul]; exact le_rfl
  · simp only [Prof.msgs_smul, Prof.msgs_mk]
    calc lg (ν ^ 2) * (K * lg ν ^ k * φ ^ 4 * m) ≤ lg (ν ^ 2) * (K * lg ν ^ k * φ ^ 4 * ν ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmν)
      _ ≤ lg (ν ^ 2) * (2 * K * lg ν ^ k * φ ^ 4 * ν ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA0)
      _ = _ := by ring



lemma sum_onEdges_le (cl : Finset (Finset (Sym2 V)))
    (hdisj : ∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C') (x : Finset (Sym2 V) → ℕ) (B : ℕ)
    (hB : ∀ C ∈ cl, x C ≤ B) (e : Sym2 V) : ∑ C ∈ cl, onEdges C (x C) e ≤ B := by
  rw [← sum_subset (filter_subset (fun C => e ∈ C) cl) (fun C _ hC => by
    simp only [onEdges]; rw [if_neg]; intro he; exact hC (mem_filter.2 ⟨by assumption, he⟩))]
  have h1 : (cl.filter (fun C => e ∈ C)).card ≤ 1 := by
    rw [card_le_one]; intro C hC C' hC'; rw [mem_filter] at hC hC'
    by_contra hne; exact disjoint_left.1 (hdisj C hC.1 C' hC'.1 hne) hC.2 hC'.2
  calc ∑ C ∈ cl.filter (fun C => e ∈ C), onEdges C (x C) e
      ≤ ∑ C ∈ cl.filter (fun C => e ∈ C), B :=
        sum_le_sum (fun C hC => by simp only [onEdges]; split_ifs
                                   · exact hB C (mem_filter.1 hC).1
                                   · exact Nat.zero_le _)
    _ = _ * B := by rw [sum_const, smul_eq_mul]
    _ ≤ 1 * B := Nat.mul_le_mul_right _ h1
    _ = B := one_mul B

lemma card_clusters_le (G : SimpleGraph V) [DecidableRel G.Adj] (cl : Finset (Finset (Sym2 V)))
    (hsub : ∀ C ∈ cl, C ⊆ G.edgeFinset) (hne : ∀ C ∈ cl, C.Nonempty)
    (hdisj : ∀ C ∈ cl, ∀ C' ∈ cl, C ≠ C' → Disjoint C C') : cl.card ≤ G.edgeFinset.card := by
  have h1 : cl.card ≤ ∑ C ∈ cl, C.card := by
    have := card_nsmul_le_sum cl card 1 (fun C hC => card_pos.2 (hne C hC)); simpa using this
  have h2 : ∑ C ∈ cl, C.card = (cl.biUnion id).card :=
    (card_biUnion (s := cl) (t := id) (fun C hC C' hC' h => hdisj C hC C' hC' h)).symm
  have h3 : cl.biUnion id ⊆ G.edgeFinset := biUnion_subset.2 (fun C hC => hsub C hC)
  exact h1.trans (h2 ▸ card_le_card h3)

lemma _root_.APSP.OverlayProps.mono_X {G : SimpleGraph V} [DecidableRel G.Adj] {E : Overlays V}
    {ov d X X' : ℕ} (h : OverlayProps G E ov d X) (hX : X ≤ X') : OverlayProps G E ov d X' :=
  ⟨h.valid, h.sub, h.disj, h.overlap, h.len, h.local_, fun e => (h.total e).trans hX⟩

/-- **Theorem 3.10**: on a network with edge weights at most `n^wexp`, the overlays `{L_j}_{j<n}`
can be computed and algorithmically embedded in `Õ(n)` rounds and `Õ(n²)` messages, such that
embedded paths have polylog length, each node is in `O(log n)` clusters, every edge carries `Õ(n)`
embedded paths over all overlays, and (via `rhoAgg_le`) the paths of the edges incident to `S` in
one overlay have congestion `Õ(|S|)`. -/
theorem thm_3_10 (T : Toolkit) (hmix : Mixing) (wexp c : ℕ) :
    ∃ fov fd fX q : ℕ → ℕ, IsPL fov ∧ IsPL fd ∧ IsPL fX ∧ IsPL q ∧ ∃ (Kδ : ℕ) (A : ℕ → T.Alg),
      ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V) (ν : ℕ), Fintype.card V ≤ ν →
      ν ≤ Fintype.card V → 1 ≤ ν → (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp) →
      ∃ p : Prof V,
        T.Impl (A ν) N (.embedOverlays (fun E => OverlayProps N.G E (fov ν) (fd ν) (fX ν * ν))) p
          ((((lg (ν ^ 2) + 1) * ν ^ 2 : ℕ) : ℝ) * whp Kδ c ν) ∧
        p.rounds ≤ q ν * ν ∧ p.msgs ≤ q ν * ν ^ 2 := by
  obtain ⟨K, k, qD, hqD, KδD, AD, hD⟩ := lemma_2_10 T c
  obtain ⟨Ks, ks, AS, hS⟩ := T.clusterSetup (2 * K + 1) k
  obtain ⟨q8, hq8, Kδ8, A8, h8⟩ := lemma_3_8 T hmix wexp c (2 * K + 1) k
  obtain ⟨q9, hq9, Kδ9, A9, h9⟩ := lemma_3_9 T hmix c (2 * K + 1) k
  -- the public exponent `Lb = Cq + kq` of the route length bound: `q9 ν ≤ ν ^ Lb` for `ν ≥ 2`
  obtain ⟨Cq, kq, hCq⟩ := hq9.le_pow
  obtain ⟨Kc, hEC⟩ := T.embedConstruct (Cq + kq) wexp
  have hov : IsPL (fun ν => lg (ν ^ 2)) := IsPL.lg_pow_succ 1
  let x : ℕ → ℕ := fun ν => 2 * Ks * lg ν ^ ks + q8 ν + q9 ν
  have hx : IsPL x := (((IsPL.const (2 * Ks)).mul (IsPL.lgpow ks)).add hq8).add hq9
  refine ⟨fun ν => lg (ν ^ 2), q9, fun ν => 1 + 2 * q9 ν,
    fun ν => qD ν + (x ν + Kc) * (lg (ν ^ 2) + 1),
    hov, hq9, (IsPL.const 1).add ((IsPL.const 2).mul hq9),
    hqD.add ((hx.add (IsPL.const Kc)).mul (hov.add (IsPL.const 1))), KδD + Kδ8 + Kδ9,
    fun ν => T.seq (AD ν) (T.clusterPar (Cq + kq) wexp (AS ν) (A8 ν) (A9 ν)), ?_⟩
  intro V _ _ N ν hν hνn hν1 hw
  set φ := 2 * K * lg ν ^ k + 1
  have hφb : φ ≤ (2 * K + 1) * lg ν ^ k := by
    have : 1 ≤ lg ν ^ k := Nat.one_le_pow _ _ (lg_pos ν)
    show 2 * K * lg ν ^ k + 1 ≤ (2 * K + 1) * lg ν ^ k; nlinarith
  -- the uniform cost of the cluster phase
  let U : Prof V := Prof.mk (x ν * ν + Kc * ν) (fun _ => x ν * ν + Kc * ν)
    (x ν * (lg (ν ^ 2) * ν ^ 2) + Kc * ν ^ 2)
  have hU : ∀ cl, DecompOK N.G cl φ (lg (ν ^ 2)) →
      T.Impl (T.clusterPar (Cq + kq) wexp (AS ν) (A8 ν) (A9 ν)) N (.embedFrom cl (fun E => OverlayProps N.G E (lg (ν ^ 2)) (q9 ν) ((1 + 2 * q9 ν) * ν)))
        U (((ν ^ 2 : ℕ) : ℝ) * whp (Kδ8 + Kδ9) c ν) := by
    intro cl hcl
    have hnl : ∀ C ∈ cl, NoLoops C := fun C hC e he =>
      N.G.not_isDiag_of_mem_edgeSet (by simpa using hcl.sub C hC he)
    -- the recorded dummy routes have length `≤ q9 ν ≤ n ^ (Cq + kq)` (a cluster has `≥ 2` nodes)
    have hLb : ∀ C ∈ cl, q9 ν ≤ Fintype.card V ^ (Cq + kq) := by
      intro C hC
      have hν2 : 2 ≤ ν := (two_le_card_nodes (hnl C hC) (hcl.ne C hC)).trans
        ((card_le_univ _).trans hν)
      have h2C : Cq ≤ ν ^ Cq :=
        (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hν2 Cq)
      rw [show Fintype.card V = ν by omega, pow_add]
      exact (hCq ν hν1).trans (Nat.mul_le_mul_right _ h2C)
    have hE := hEC (AS ν) (A8 ν) (A9 ν) (N := N) cl
      (fun C => Prof.mk (Ks * lg ν ^ ks * (nodes C).card)
        (onEdges C (2 * (Ks * lg ν ^ ks * (nodes C).card))) (Ks * lg ν ^ ks * (nodes C).card ^ 2))
      (fun C => Prof.mk (q8 ν * (nodes C).card) (onEdges C (q8 ν * (nodes C).card))
        (q8 ν * (nodes C).card ^ 2))
      (fun C => Prof.mk (q9 ν * (nodes C).card) (onEdges C (q9 ν * (nodes C).card))
        (q9 ν * (nodes C).card ^ 2))
      (fun _ => 0) (fun _ => whp Kδ8 c ν) (fun _ => whp Kδ9 c ν)
      (fun C r => DummyRoutesOK C r (q9 ν) (q9 ν * (nodes C).card))
      (fun E => OverlayProps N.G E (lg (ν ^ 2)) (q9 ν) ((1 + 2 * q9 ν) * ν)) hw hcl.cover
      (fun C hC => ⟨hcl.sub C hC, hcl.ne C hC⟩) hcl.disj
      (fun C hC => hS N ν C φ hν hνn (hcl.sub C hC) (hcl.ne C hC) (hcl.exp C hC) hφb)
      (fun C hC => h8 N ν hν hνn C φ (hcl.sub C hC) (hcl.ne C hC) (hcl.exp C hC) hφb)
      (fun C hC => h9 N ν hν hνn C φ (hcl.sub C hC) (hcl.ne C hC) (hcl.exp C hC) hφb)
      (fun C _ e he => by simp [onEdges, he])
      (fun C hC r hr v hv p hp => ⟨hr.walk v hv p hp, hr.local_ v hv p hp,
        (hr.len v hv p hp).trans (hLb C hC)⟩)
      (fun r hr => (construct_props cl r (lg (ν ^ 2)) (q9 ν) (q9 ν) hcl.sub hcl.ne hcl.cover
        hcl.disj hcl.overlap hr).mono_X (by nlinarith))
    refine T.mono hE (Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_) ?_
    · simp only [Prof.rounds_mk, Prof.rounds_add]
      refine Nat.add_le_add ?_ (Nat.mul_le_mul_left _ hν)
      apply Finset.sup_le; intro C _
      have : (nodes C).card ≤ ν := (card_le_univ _).trans hν
      show Ks * lg ν ^ ks * _ + q8 ν * _ + q9 ν * _ ≤ (2 * Ks * lg ν ^ ks + q8 ν + q9 ν) * ν
      nlinarith [Nat.mul_le_mul_left (Ks * lg ν ^ ks) this, Nat.mul_le_mul_left (q8 ν) this,
        Nat.mul_le_mul_left (q9 ν) this, Nat.zero_le (Ks * lg ν ^ ks * ν)]
    · simp only [Prof.load_mk, Prof.load_add, Finset.sum_apply, Pi.add_apply]
      refine Nat.add_le_add ?_ (Nat.mul_le_mul_left _ hν)
      have : ∀ C ∈ cl, onEdges C (2 * (Ks * lg ν ^ ks * (nodes C).card)) e +
          onEdges C (q8 ν * (nodes C).card) e +
          onEdges C (q9 ν * (nodes C).card) e = onEdges C (x ν * (nodes C).card) e := by
        intro C _
        rw [← Pi.add_apply (onEdges C _), onEdges_add, ← Pi.add_apply (onEdges C _), onEdges_add]
        congr 1; show _ = (2 * Ks * lg ν ^ ks + q8 ν + q9 ν) * _; ring
      rw [sum_congr rfl this]
      exact sum_onEdges_le cl hcl.disj _ _ (fun C _ =>
        Nat.mul_le_mul_left _ ((card_le_univ _).trans hν)) e
    · simp only [Prof.msgs_mk, Prof.msgs_add]
      refine Nat.add_le_add ?_ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hν 2))
      have h1 : ∀ C ∈ cl, Ks * lg ν ^ ks * (nodes C).card ^ 2 + q8 ν * (nodes C).card ^ 2 +
          q9 ν * (nodes C).card ^ 2 ≤ x ν * ν * (nodes C).card := by
        intro C _
        have : (nodes C).card ≤ ν := (card_le_univ _).trans hν
        show _ ≤ (2 * Ks * lg ν ^ ks + q8 ν + q9 ν) * ν * _
        have b : (nodes C).card ^ 2 ≤ ν * (nodes C).card := by
          rw [sq]; exact Nat.mul_le_mul_right _ this
        nlinarith [Nat.mul_le_mul_left (Ks * lg ν ^ ks) b, Nat.mul_le_mul_left (q8 ν) b,
          Nat.mul_le_mul_left (q9 ν) b, Nat.zero_le (Ks * lg ν ^ ks * (ν * (nodes C).card))]
      have h2 := sum_card_nodes_le cl _ hcl.overlap
      calc _ ≤ ∑ C ∈ cl, x ν * ν * (nodes C).card := sum_le_sum h1
        _ = x ν * ν * ∑ C ∈ cl, (nodes C).card := by rw [mul_sum]
        _ ≤ x ν * ν * (lg (ν ^ 2) * ν) :=
          Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ hν))
        _ = x ν * (lg (ν ^ 2) * ν ^ 2) := by ring
    · have hcard := card_clusters_le N.G cl hcl.sub hcl.ne hcl.disj
      have hm : N.G.edgeFinset.card ≤ ν ^ 2 :=
        N.G.card_edgeFinset_le_card_choose_two.trans ((Nat.choose_le_pow _ _).trans
          (Nat.pow_le_pow_left hν 2))
      simp only [zero_add, sum_const, nsmul_eq_mul]
      rw [whp_add]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard.trans hm) (whp_nonneg _ _ _)
  have hTot := T.decompThen (hD N ν hν hνn) hU (mul_nonneg (Nat.cast_nonneg _) (whp_nonneg _ _ _))
  refine ⟨_, T.mono hTot le_rfl ?_, ?_, ?_⟩
  · have h1 := whp_mono_K (show KδD ≤ KδD + Kδ8 + Kδ9 by omega) c ν
    have h2 := whp_mono_K (show Kδ8 + Kδ9 ≤ KδD + Kδ8 + Kδ9 by omega) c ν
    have hw := whp_nonneg (KδD + Kδ8 + Kδ9) c ν
    have hl : (lg (ν ^ 2) : ℝ) ≤ (lg (ν ^ 2) : ℝ) * (ν ^ 2 : ℝ) := by
      have : (1 : ℝ) ≤ (ν : ℝ) ^ 2 := by exact_mod_cast Nat.one_le_pow _ _ hν1
      nlinarith [(Nat.cast_nonneg (lg (ν ^ 2)) : (0:ℝ) ≤ _)]
    push_cast
    nlinarith [whp_nonneg KδD c ν, whp_nonneg (Kδ8 + Kδ9) c ν,
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (lg (ν ^ 2))),
      mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (ν:ℝ) ^ 2),
      mul_le_mul_of_nonneg_right hl hw]
  · simp only [Prof.rounds_add, Prof.rounds_mk, U]
    have a1 : qD ν ≤ qD ν * ν := Nat.le_mul_of_pos_right _ hν1
    nlinarith [Nat.zero_le (x ν * ν * lg (ν ^ 2)), Nat.zero_le (Kc * ν * lg (ν ^ 2))]
  · simp only [Prof.msgs_add, Prof.msgs_mk, U]
    have : 1 ≤ ν ^ 2 := Nat.one_le_pow _ _ hν1
    nlinarith [Nat.zero_le (x ν * ν ^ 2), Nat.zero_le (Kc * ν ^ 2 * lg (ν ^ 2))]


end APSP.Stoc
