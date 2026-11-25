import ApspStoc.Sec3
import ApspStoc.Statements

/-!
# Theorem 5.6 (= Theorem 1.1) from Theorem 5.5

> There is a randomized Monte-Carlo distributed algorithm solving weighted undirected APSP in
> `Õ(n)` rounds and `Õ(n²)` messages w.h.p.

Formally: for every weight exponent `wexp` (weights are integers in `[1, n^wexp]`) and every
confidence exponent `c`, there is an algorithm `A` (a family indexed by the publicly known number of
nodes `n`, not depending on the network otherwise) and constants `C, k, K` such that on every
connected weighted network with `n` nodes, `A n` achieves the APSP output specification (every node
learns its distance and next hop to every other node) in at most `C · lg(n)^k · n` rounds and
`C · lg(n)^k · n²` messages, except with probability at most `K / n^c`.
-/

namespace APSP.Stoc

open APSP Finset

/-- A constant times a power of `ν` is at most a power of `ν + 4`. -/
lemma mul_pow_le_add_four_pow (A d ν : ℕ) : A * ν ^ d ≤ (ν + 4) ^ (A + d) := by
  rw [pow_add]
  exact Nat.mul_le_mul ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _))
    (Nat.pow_le_pow_left (by omega) _)

/-- **Theorem 5.6** from Theorem 5.5 (Theorem 3.10 and random-delay scheduling [17]). -/
theorem thm_5_6_of (T : Toolkit) (hmix : Mixing) (h55 : Thm_5_5 T) (wexp c : ℕ) :
    ∃ (A : ℕ → T.Alg) (C k K : ℕ), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V),
      1 ≤ Fintype.card V → (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp) →
      ∃ (p : Prof V) (δ : ℝ),
        T.Impl (A (Fintype.card V)) N (.compute none (V → ℕ × V) (APSPSpec N)) p δ ∧
        p.rounds ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ∧
        p.msgs ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ^ 2 ∧
        δ ≤ (K : ℝ) / (Fintype.card V : ℝ) ^ c := by
  -- the number of failure events of one SSSP instance (independent of the confidence `c'`)
  obtain ⟨qδS, hqδS, h65⟩ := h55 wexp
  obtain ⟨Cq, kq, hCq⟩ := hqδS.le_pow
  -- confidence used for all subroutines
  let c' := c + (kq + 4)
  obtain ⟨fov, fd, fX, qE, hfov, hfd, hfX, hqE, KδE, AE, hEmb⟩ := thm_3_10 T hmix wexp c'
  obtain ⟨q6, hq6, Kδ6, AS, hSSSP⟩ := h65 c' hfov hfd
  -- the scheduler's parameters `R = q6 ν · ν` and `Cg = q6 ν · fX ν · ν` are polynomial in `ν`
  obtain ⟨C6, k6, hC6⟩ := hq6.le_pow
  obtain ⟨CX, kX, hCX⟩ := hfX.le_pow
  have hRC : ∀ ν, 1 ≤ ν → q6 ν * ν + q6 ν * (fX ν * ν) ≤
      (ν + 4) ^ (C6 * (1 + CX) + (k6 + 1 + kX)) := by
    intro ν hν
    have h1 : 1 ≤ ν ^ kX := Nat.one_le_pow _ _ hν
    have h2 : 1 + fX ν ≤ (1 + CX) * ν ^ kX := by nlinarith [hCX ν hν]
    calc q6 ν * ν + q6 ν * (fX ν * ν) = q6 ν * ν * (1 + fX ν) := by ring
      _ ≤ (C6 * ν ^ k6) * ν * ((1 + CX) * ν ^ kX) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (hC6 ν hν)) h2
      _ = C6 * (1 + CX) * ν ^ (k6 + 1 + kX) := by ring
      _ ≤ _ := mul_pow_le_add_four_pow _ _ _
  obtain ⟨Ks, ks, Kδs, hsch⟩ := T.schedule c' (C6 * (1 + CX) + (k6 + 1 + kX))
  -- the final polylog factor
  have hF : IsPL (fun ν => qE ν + Ks * lg ν ^ ks * (q6 ν * (fX ν + 1) + 1) + q6 ν) :=
    (hqE.add (((IsPL.const Ks).mul (IsPL.lgpow ks)).mul
      ((hq6.mul (hfX.add (IsPL.const 1))).add (IsPL.const 1)))).add hq6
  obtain ⟨C, k, hCk⟩ := hF
  -- the scheduler gets public bounds on the rounds (`q6 ν · ν`) and on the congestion
  -- (`q6 ν · fX ν · ν`, from `OverlayProps.total`) of the `n` SSSP instances: functions of `ν`
  refine ⟨fun ν => T.seq (AE ν) (T.sched c' ν (q6 ν * ν) (q6 ν * (fX ν * ν)) (AS ν)), C, k,
    (3 + Cq) * (KδE + Kδ6 + Kδs), ?_⟩
  intro V _ _ N hn hw
  set ν := Fintype.card V with hνdef
  obtain ⟨pE, hE, hEr, hEm⟩ := hEmb N ν le_rfl le_rfl hn hw
  -- index of the overlay used by the SSSP instance rooted at `s`
  let idx : V → ℕ := fun s => (Fintype.equivFin V s : ℕ)
  have hsum_idx : ∀ (E : Overlays V) (e : Sym2 V),
      ∑ s, E.rho N.G (idx s) univ e = ∑ j ∈ range ν, E.rho N.G j univ e := by
    intro E e
    rw [← Fin.sum_univ_eq_sum_range (fun j => E.rho N.G j univ e) ν]
    exact Equiv.sum_comp (Fintype.equivFin V) (fun i : Fin ν => E.rho N.G i univ e)
  -- the uniform cost of running all `n` SSSP instances simultaneously
  let U : Prof V := Prof.mk (Ks * lg ν ^ ks * (q6 ν * (fX ν * ν) + q6 ν * ν + ν))
    (fun _ => Ks * lg ν ^ ks * (q6 ν * (fX ν * ν) + ν))
    (Ks * lg ν ^ ks * (ν * (q6 ν * ν) + ν ^ 2))
  let δU : ℝ := ((ν * (qδS ν * ν) : ℕ) : ℝ) * whp Kδ6 c' ν + whp Kδs c' ν
  have hall : ∀ E, OverlayProps N.G E (fov ν) (fd ν) (fX ν * ν) →
      T.Impl (T.sched c' ν (q6 ν * ν) (q6 ν * (fX ν * ν)) (AS ν)) N
        (.compute (some E) (V → ℕ × V) (APSPSpec N)) U δU := by
    intro E hE'
    have hs : ∀ s, T.Impl (AS ν) N (.io E (Fintype.equivFin V s : ℕ) (Fintype.card V) univ V
        (ℕ × V) (fun _ => s)
        (fun y => SSSPSpec N s (fun v => y (.inl v))))
        (Prof.mk (q6 ν * ν) (fun e => q6 ν * E.rho N.G (idx s) univ e) (q6 ν * ν))
        (((qδS ν * ν : ℕ) : ℝ) * whp Kδ6 c' ν) :=
      fun s => hSSSP N ν le_rfl le_rfl hw E (fX ν * ν) hE' s
    have hload : ∀ e, ∑ s, q6 ν * E.rho N.G (idx s) univ e ≤ q6 ν * (fX ν * ν) := by
      intro e
      rw [← mul_sum, hsum_idx]
      exact Nat.mul_le_mul_left _ (hE'.total e)
    have h1 := hsch (AS ν) N ν le_rfl le_rfl E (ℕ × V) (q6 ν * ν) (q6 ν * (fX ν * ν))
      (fun s => SSSPSpec N s) _ _ (hRC ν hn) hs (fun s => le_rfl) hload
    have h2 := T.weaken (fun o ho => apsp_of_sssp N o ho) h1
    refine T.mono h2 (Prof.le_mk _ _ _ _ ?_ (fun e => ?_) ?_) (le_of_eq ?_)
    · exact le_rfl
    · simp only [Prof.load_mk, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (hload e) _)
    · simp only [Prof.msgs_mk, sum_const, card_univ, smul_eq_mul]; rfl
    · simp only [sum_const, card_univ, nsmul_eq_mul, δU]; push_cast; ring
  have hTot := T.embThen hE hall
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (whp_nonneg _ _ _)) (whp_nonneg _ _ _))
  refine ⟨_, _, hTot, ?_, ?_, ?_⟩
  · -- rounds
    simp only [Prof.rounds_add, U, Prof.rounds_mk]
    have := hCk ν
    calc pE.rounds + Ks * lg ν ^ ks * (q6 ν * (fX ν * ν) + q6 ν * ν + ν)
        ≤ qE ν * ν + Ks * lg ν ^ ks * (q6 ν * (fX ν + 1) + 1) * ν := by
          apply Nat.add_le_add hEr (le_of_eq (by ring))
      _ ≤ (qE ν + Ks * lg ν ^ ks * (q6 ν * (fX ν + 1) + 1) + q6 ν) * ν := by
          nlinarith [Nat.zero_le (q6 ν * ν)]
      _ ≤ C * lg ν ^ k * ν := Nat.mul_le_mul_right _ this
  · -- messages
    simp only [Prof.msgs_add, U, Prof.msgs_mk]
    have := hCk ν
    have hq : Ks * lg ν ^ ks * (q6 ν + 1) ≤ Ks * lg ν ^ ks * (q6 ν * (fX ν + 1) + 1) :=
      Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le (q6 ν * fX ν)])
    calc pE.msgs + Ks * lg ν ^ ks * (ν * (q6 ν * ν) + ν ^ 2)
        = pE.msgs + Ks * lg ν ^ ks * (q6 ν + 1) * ν ^ 2 := by ring
      _ ≤ qE ν * ν ^ 2 + Ks * lg ν ^ ks * (q6 ν * (fX ν + 1) + 1) * ν ^ 2 :=
          Nat.add_le_add hEm (Nat.mul_le_mul_right _ hq)
      _ ≤ (qE ν + Ks * lg ν ^ ks * (q6 ν * (fX ν + 1) + 1) + q6 ν) * ν ^ 2 := by
          nlinarith [Nat.zero_le (q6 ν * ν ^ 2)]
      _ ≤ C * lg ν ^ k * ν ^ 2 := Nat.mul_le_mul_right _ this
  · -- failure probability: union bound over polynomially many events
    have hν1 : 1 ≤ ν := hn
    set M : ℕ := (lg (ν ^ 2) + 1) * ν ^ 2 + ν * (qδS ν * ν) + 1 with hM
    have hMb : M ≤ (3 + Cq) * ν ^ (kq + 4) := by
      have h1 : lg (ν ^ 2) ≤ ν ^ 2 := lg_le_self (Nat.one_le_pow _ _ hν1)
      have h2 : qδS ν ≤ Cq * ν ^ kq := hCq ν hν1
      have h3 : ν ^ 2 ≤ ν ^ (kq + 4) := Nat.pow_le_pow_right hν1 (by omega)
      have h4 : ν ^ 4 ≤ ν ^ (kq + 4) := Nat.pow_le_pow_right hν1 (by omega)
      have h5 : 1 ≤ ν ^ (kq + 4) := Nat.one_le_pow _ _ hν1
      have h6 : ν * (qδS ν * ν) ≤ Cq * ν ^ (kq + 4) := by
        calc ν * (qδS ν * ν) ≤ ν * (Cq * ν ^ kq * ν) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
          _ = Cq * (ν ^ kq * ν ^ 2) := by ring
          _ ≤ Cq * ν ^ (kq + 4) := by
            apply Nat.mul_le_mul_left
            rw [← pow_add]; exact Nat.pow_le_pow_right hν1 (by omega)
      have h7 : (lg (ν ^ 2) + 1) * ν ^ 2 ≤ 2 * ν ^ (kq + 4) := by
        have : (lg (ν ^ 2) + 1) * ν ^ 2 ≤ (ν ^ 2 + ν ^ 2) * ν ^ 2 :=
          Nat.mul_le_mul_right _ (by have := Nat.one_le_pow 2 ν hν1; omega)
        calc _ ≤ (ν ^ 2 + ν ^ 2) * ν ^ 2 := this
          _ = 2 * ν ^ 4 := by ring
          _ ≤ 2 * ν ^ (kq + 4) := Nat.mul_le_mul_left _ h4
      rw [hM]; nlinarith
    have hU := whp_union (3 + Cq) (kq + 4) (KδE + Kδ6 + Kδs) c ν hν1 M hMb
    have hwE := whp_mono_K (show KδE ≤ KδE + Kδ6 + Kδs by omega) c' ν
    have hw6 := whp_mono_K (show Kδ6 ≤ KδE + Kδ6 + Kδs by omega) c' ν
    have hws := whp_mono_K (show Kδs ≤ KδE + Kδ6 + Kδs by omega) c' ν
    have hw0 := whp_nonneg (KδE + Kδ6 + Kδs) c' ν
    have hsplit : (M : ℝ) * whp (KδE + Kδ6 + Kδs) c' ν =
        (((lg (ν ^ 2) + 1) * ν ^ 2 : ℕ) : ℝ) * whp (KδE + Kδ6 + Kδs) c' ν +
        ((ν * (qδS ν * ν) : ℕ) : ℝ) * whp (KδE + Kδ6 + Kδs) c' ν + whp (KδE + Kδ6 + Kδs) c' ν := by
      rw [hM]; push_cast; ring
    have hfin : whp ((3 + Cq) * (KδE + Kδ6 + Kδs)) c ν =
        (((3 + Cq) * (KδE + Kδ6 + Kδs) : ℕ) : ℝ) / (ν : ℝ) ^ c := rfl
    rw [← hfin]
    refine le_trans ?_ hU
    rw [hsplit]
    simp only [δU]
    have a1 := mul_le_mul_of_nonneg_left hwE (Nat.cast_nonneg (α := ℝ) ((lg (ν ^ 2) + 1) * ν ^ 2))
    have a2 := mul_le_mul_of_nonneg_left hw6 (Nat.cast_nonneg (α := ℝ) (ν * (qδS ν * ν)))
    linarith

end APSP.Stoc
