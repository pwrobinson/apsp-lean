import ApspStoc.G0Stmt
import ApspStoc.G0AuxProb

/-!
# Claims 3.4 and 3.5: proof

Parameters (for confidence `c`, port ratio `a` and expansion `φinv ≤ Kφ lg^kφ ν`, with the mixing
constant `Km`):
* walk length `2ℓ` with `ℓ = Km (Kφ lg^kφ ν + 1)² lg ν + 1` (so that both halves of every walk mix);
* `R = c' (m/n + 1) lg ν` tokens per port, `c' = 32 (K₀ + 1)`, `K₀ = c + 2kφ + 5`;
* `t = 2R + K₀ lg ν` rounds per step.
The constructed `G₀` has at most `H lg ν` surviving walks starting and ending at every port
(`H = 5ac' + K₀`), hence at most `H lg ν |P|` edges; every `A ⊆ P` with `|A| ≤ |P|/2` sends at
least `|A| lg ν` surviving walks out of `A`, hence conductance `≥ 1/(2H)`; congestion
`≤ 2H lg ν + 2ℓ H lg ν`; dilation `2ℓ + 1`. The nodes cannot compute these true parameters, so
they output the public parameters `g0gf` (size bound `a·n_C ≥ |P|`, edge bound `H lg ν · a n_C`,
and the other three bounds above), which bound the true parameters unless a bad event occurs.
-/

namespace APSP.Stoc

open APSP Finset

/-- tokens per port -/
def g0R (c' ν n m : ℕ) : ℕ := c' * (m / n + 1) * lg ν

/-- rounds per lazy step -/
def g0t (c' K₀ ν n m : ℕ) : ℕ := 2 * g0R c' ν n m + K₀ * lg ν

/-- half the walk length -/
def g0ℓ (Km Kφ kφ ν : ℕ) : ℕ := Km * (Kφ * lg ν ^ kφ + 1) ^ 2 * lg ν + 1

lemma g0ℓ_le (Km Kφ kφ ν : ℕ) :
    g0ℓ Km Kφ kφ ν ≤ (Km * (Kφ + 1) ^ 2 + 1) * lg ν ^ (2 * kφ + 1) := by
  unfold g0ℓ
  have hL : 1 ≤ lg ν := one_le_lg ν
  have hX : 1 ≤ lg ν ^ kφ := Nat.one_le_pow _ _ hL
  have h1 : Kφ * lg ν ^ kφ + 1 ≤ (Kφ + 1) * lg ν ^ kφ := by nlinarith
  have h2 : 1 ≤ lg ν ^ (2 * kφ + 1) := Nat.one_le_pow _ _ hL
  calc Km * (Kφ * lg ν ^ kφ + 1) ^ 2 * lg ν + 1
      ≤ Km * ((Kφ + 1) * lg ν ^ kφ) ^ 2 * lg ν + 1 := by gcongr
    _ = Km * (Kφ + 1) ^ 2 * lg ν ^ (2 * kφ + 1) + 1 := by ring
    _ ≤ Km * (Kφ + 1) ^ 2 * lg ν ^ (2 * kφ + 1) + lg ν ^ (2 * kφ + 1) := by omega
    _ = (Km * (Kφ + 1) ^ 2 + 1) * lg ν ^ (2 * kφ + 1) := by ring

/-- `m ≤ (m/n + 1) n`. -/
lemma le_div_succ_mul (m n : ℕ) (hn : 0 < n) : m ≤ (m / n + 1) * n := by
  have h1 := Nat.div_add_mod m n
  have h2 := Nat.mod_lt m hn
  nlinarith

/-- The cost of the construction: rounds. -/
lemma g0_rounds_le (Kc c' K₀ Kℓ kℓ Lg ℓ q : ℕ) (hLg : 1 ≤ Lg) (hℓ : ℓ ≤ Kℓ * Lg ^ kℓ) :
    Kc * (c' * (q + 1) * Lg + ℓ * (2 * (c' * (q + 1) * Lg) + K₀ * Lg) + 1) ≤
      Kc * (c' + Kℓ * (2 * c' + K₀) + 1) * Lg ^ (kℓ + 1) * (q + 1) := by
  set X := Lg ^ kℓ with hXdef
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hLg
  have hQ : 1 ≤ q + 1 := by omega
  have t1 : c' * (q + 1) * Lg ≤ c' * (X * Lg * (q + 1)) := by
    calc c' * (q + 1) * Lg = c' * (1 * Lg * (q + 1)) := by ring
      _ ≤ c' * (X * Lg * (q + 1)) := by gcongr
  have t2 : Kℓ * K₀ * (X * Lg) ≤ Kℓ * K₀ * (X * Lg * (q + 1)) := by
    calc Kℓ * K₀ * (X * Lg) = Kℓ * K₀ * (X * Lg * 1) := by ring
      _ ≤ Kℓ * K₀ * (X * Lg * (q + 1)) := by gcongr
  have t3 : 1 ≤ X * Lg * (q + 1) := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hX hLg) hQ
    simpa using this
  calc Kc * (c' * (q + 1) * Lg + ℓ * (2 * (c' * (q + 1) * Lg) + K₀ * Lg) + 1)
      ≤ Kc * (c' * (q + 1) * Lg + (Kℓ * X) * (2 * (c' * (q + 1) * Lg) + K₀ * Lg) + 1) := by
        gcongr
    _ = Kc * (c' * (q + 1) * Lg + 2 * Kℓ * c' * (X * Lg * (q + 1)) + Kℓ * K₀ * (X * Lg) + 1) := by
        ring
    _ ≤ Kc * (c' * (X * Lg * (q + 1)) + 2 * Kℓ * c' * (X * Lg * (q + 1)) +
          Kℓ * K₀ * (X * Lg * (q + 1)) + X * Lg * (q + 1)) := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add t1 le_rfl) t2) t3
    _ = Kc * (c' + Kℓ * (2 * c' + K₀) + 1) * Lg ^ (kℓ + 1) * (q + 1) := by
        rw [pow_succ, ← hXdef]; ring

/-- The cost of the construction: messages. -/
lemma g0_msgs_le (Kc c' Kℓ kℓ Lg ℓ a n m p : ℕ) (hLg : 1 ≤ Lg) (hℓ : ℓ ≤ Kℓ * Lg ^ kℓ)
    (hn : 0 < n) (hnm : n ≤ 2 * m) (hp : p ≤ a * n) :
    Kc * (p * (c' * (m / n + 1) * Lg) * (ℓ + 1)) ≤
      3 * Kc * a * c' * (Kℓ + 1) * Lg ^ (kℓ + 1) * m := by
  have hX : 1 ≤ Lg ^ kℓ := Nat.one_le_pow _ _ hLg
  have h1 : p * (m / n + 1) ≤ 3 * a * m := by
    have := Nat.div_mul_le_self m n
    calc p * (m / n + 1) ≤ a * n * (m / n + 1) := Nat.mul_le_mul_right _ hp
      _ = a * (m / n * n + n) := by ring
      _ ≤ a * (m + 2 * m) := by gcongr
      _ = 3 * a * m := by ring
  have h2 : ℓ + 1 ≤ (Kℓ + 1) * Lg ^ kℓ := by nlinarith
  calc Kc * (p * (c' * (m / n + 1) * Lg) * (ℓ + 1))
      = Kc * c' * Lg * (p * (m / n + 1)) * (ℓ + 1) := by ring
    _ ≤ Kc * c' * Lg * (3 * a * m) * ((Kℓ + 1) * Lg ^ kℓ) := by gcongr
    _ = 3 * Kc * a * c' * (Kℓ + 1) * Lg ^ (kℓ + 1) * m := by rw [pow_succ]; ring

lemma lg_le_self' {ν : ℕ} (h : 1 ≤ ν) : lg ν ≤ ν := by
  unfold lg
  have := Nat.log_lt_self 2 (show ν ≠ 0 by omega)
  omega

lemma card_sym2_le (V : Type) [Fintype V] [DecidableEq V] :
    Fintype.card (Sym2 V) ≤ Fintype.card V ^ 2 := by
  have := Fintype.card_le_of_surjective _ (Sym2.mk_surjective (α := V))
  rwa [Fintype.card_prod, ← pow_two] at this

/-- The sum over the subsets in the expansion union bound. -/
lemma sum_powerset_pow_le {α : Type*} (P : Finset α) (y : ℝ) (hy : 0 ≤ y)
    (hPy : (P.card : ℝ) * y ≤ 1) :
    ∑ A ∈ P.powerset.filter (fun A => A.Nonempty), y ^ A.card ≤
      ((P.card + 1 : ℕ) : ℝ) * (P.card * y) := by
  rw [Finset.sum_filter]
  have : ∀ A ∈ P.powerset, (if A.Nonempty then y ^ A.card else 0) =
      if A.card = 0 then (0 : ℝ) else y ^ A.card := by
    intro A _
    by_cases h : A.Nonempty
    · rw [if_pos h, if_neg (Finset.card_pos.2 h).ne']
    · rw [if_neg h, if_pos (by rw [Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.1 h)]
  rw [Finset.sum_congr rfl this,
    Finset.sum_powerset_apply_card (fun k => if k = 0 then (0 : ℝ) else y ^ k)]
  calc ∑ k ∈ range (P.card + 1), (P.card.choose k) • (if k = 0 then (0 : ℝ) else y ^ k)
      ≤ ∑ k ∈ range (P.card + 1), (P.card * y) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [nsmul_eq_mul]
        split_ifs with hk
        · rw [mul_zero]; positivity
        · have h1 : ((P.card.choose k : ℕ) : ℝ) ≤ (P.card : ℝ) ^ k := by
            exact_mod_cast Nat.choose_le_pow P.card k
          calc ((P.card.choose k : ℕ) : ℝ) * y ^ k ≤ (P.card : ℝ) ^ k * y ^ k := by gcongr
            _ = (P.card * y) ^ k := by rw [mul_pow]
            _ ≤ P.card * y := pow_le_of_le_one (by positivity) hPy hk
    _ = ((P.card + 1 : ℕ) : ℝ) * (P.card * y) := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]

/-- The public parameters of the constructed `G₀` output by the nodes (the argument `gf` of the
random-walk construction), computed from `(n_C, m_C)` and `ν` (through `lg ν` and the half walk
length `ℓ`): size bound `a·n_C`, edge bound `H lg ν · a n_C`, inverse conductance `2H`, congestion
`2H lg ν + 2ℓ H lg ν` and dilation `2ℓ + 1`. They do not depend on `m_C`. -/
def g0gf (a H ℓ ν n _m : ℕ) : G0Data :=
  ⟨a * n, H * lg ν * (a * n), 2 * H, 2 * (H * lg ν) + 2 * ℓ * (H * lg ν), 2 * ℓ + 1⟩

/-- `TrueParams` is monotone in the claimed parameters. -/
lemma trueParams_mono {V : Type} [Fintype V] [DecidableEq V] {C : Finset (Sym2 V)}
    {P : Finset (Port V)} {R ℓ : ℕ} {ω : RWSeeds C P R ℓ} {g g' : G0Data}
    (h : TrueParams C P R ℓ ω g) (h1 : g.n0 ≤ g'.n0) (h2 : g.m0 ≤ g'.m0) (h3 : g.φinv ≤ g'.φinv)
    (h4 : g.cong ≤ g'.cong) (h5 : g.dil ≤ g'.dil) : TrueParams C P R ℓ ω g' := by
  obtain ⟨a1, a2, ⟨a3, a3'⟩, a4, a5⟩ := h
  exact ⟨a1.trans h1, a2.trans h2,
    ⟨a3, fun A hA => (a3' A hA).trans (Nat.mul_le_mul_right _ h3)⟩, a4.trans h4, a5.trans h5⟩

/-- The numbers carried by the tokens of the random-walk construction (walk indices `< R` and path
positions `≤ 2ℓ`) are polynomial in `ν`: `R + 2ℓ + 2 ≤ (ν + 4)^(c' + Kℓ + kℓ + 4)`. -/
lemma g0_digits_le (c' Kℓ kℓ ν n m ℓ : ℕ) (hν1 : 1 ≤ ν) (hm : m ≤ ν ^ 2)
    (hℓ : ℓ ≤ Kℓ * lg ν ^ kℓ) :
    g0R c' ν n m + 2 * ℓ + 2 ≤ (ν + 4) ^ (c' + Kℓ + kℓ + 4) := by
  obtain ⟨X, hX⟩ : ∃ X, X = ν + 4 := ⟨_, rfl⟩
  rw [← hX]
  have hX5 : 5 ≤ X := by omega
  have hc : c' ≤ X ^ c' :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
  have hK : Kℓ ≤ X ^ Kℓ :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
  have hlg : lg ν ≤ X := (lg_le_self' hν1).trans (by omega)
  have hmn : m / n + 1 ≤ X ^ 2 := by
    have := Nat.div_le_self m n
    have : ν ^ 2 + 1 ≤ X ^ 2 := by rw [hX]; nlinarith
    omega
  have hR : g0R c' ν n m ≤ X ^ (c' + 3) := by
    unfold g0R
    calc c' * (m / n + 1) * lg ν ≤ X ^ c' * X ^ 2 * X :=
          Nat.mul_le_mul (Nat.mul_le_mul hc hmn) hlg
      _ = X ^ (c' + 3) := by ring
  have hl : ℓ ≤ X ^ (Kℓ + kℓ) := by
    calc ℓ ≤ Kℓ * lg ν ^ kℓ := hℓ
      _ ≤ X ^ Kℓ * X ^ kℓ := Nat.mul_le_mul hK (Nat.pow_le_pow_left hlg _)
      _ = X ^ (Kℓ + kℓ) := by ring
  have e1 : X ^ (c' + 3) ≤ X ^ (c' + Kℓ + kℓ + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : X ^ (Kℓ + kℓ) ≤ X ^ (c' + Kℓ + kℓ + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : 1 ≤ X ^ (c' + Kℓ + kℓ + 3) := Nat.one_le_pow _ _ (by omega)
  have e4 : X ^ (c' + Kℓ + kℓ + 4) = X ^ (c' + Kℓ + kℓ + 3) * X := by ring
  rw [e4]
  nlinarith

/-- **Claims 3.4 and 3.5**, from the random-walk link and the mixing bound. The nodes output the
public parameters `g0gf` (computed from `(n_C, m_C)` and `ν`); the event that the constructed `G₀`
does not meet them is contained in the bad events of `rw_fail_le` (unless one of them occurs, the
true parameters are bounded by those of `trueParams_of_good`, which are at most the public ones),
so it has the same failure bound. -/
theorem buildG0_of (T : Toolkit) (hrw : RWLink T) (hmix : Mixing) : BuildG0Stmt T := by
  obtain ⟨alg, hrw⟩ := hrw
  obtain ⟨Km, hmix⟩ := hmix
  intro c a Kφ kφ
  -- constants
  obtain ⟨kℓ, hkℓ⟩ : ∃ kℓ, kℓ = 2 * kφ + 1 := ⟨_, rfl⟩
  obtain ⟨Kℓ, hKℓ⟩ : ∃ Kℓ, Kℓ = Km * (Kφ + 1) ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = c + kℓ + 4 := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = 32 * (K₀ + 1) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = 5 * a * c' + K₀ := ⟨_, rfl⟩
  obtain ⟨Kc, hrw⟩ := hrw (c' + Kℓ + kℓ + 4)
  obtain ⟨K, hK⟩ : ∃ K, K = Kc * (c' + Kℓ * (2 * c' + K₀) + 1) + 3 * Kc * a * c' * (Kℓ + 1) +
      2 * H + 2 * Kℓ * H + 2 * Kℓ + 1 := ⟨_, rfl⟩
  refine ⟨K, kℓ + 1, 4 * Kℓ + 10, fun ν => alg (g0R c' ν) (g0ℓ Km Kφ kφ ν) (g0t c' K₀ ν)
    (g0gf a H (g0ℓ Km Kφ kφ ν) ν), ?_⟩
  intro V _ _ N ν hν hν' C P φinv hCN hCne hexp hφ hPA hnP hPa
  -- basic facts about the cluster
  have hCL : NoLoops C := fun e he => N.G.not_isDiag_of_mem_edgeSet (by simpa using hCN he)
  have hn2 : 2 ≤ (nodes C).card := two_le_card_nodes hCL hCne
  have hnV : (nodes C).card ≤ Fintype.card V := card_le_univ _
  have hν2 : 2 ≤ ν := by omega
  have hν1 : 1 ≤ ν := by omega
  have hm1 : 1 ≤ C.card := hCne.card_pos
  have hnm : (nodes C).card ≤ 2 * C.card := card_nodes_le_sum_degIn hCL
  have h2P : 2 ≤ P.card := le_trans hn2 hnP
  have hPm : P.card ≤ 2 * C.card := by
    rw [← card_allPorts hCL]; exact card_le_card hPA
  have hmν : C.card ≤ ν ^ 2 := by
    have := card_le_sq hCL
    exact this.trans (Nat.pow_le_pow_left (hnV.trans hν) 2)
  have hPν : P.card ≤ 2 * ν ^ 2 := by omega
  have hLg1 : 1 ≤ lg ν := one_le_lg ν
  have hLgν : lg ν ≤ ν := lg_le_self' hν1
  have hℓK : g0ℓ Km Kφ kφ ν ≤ Kℓ * lg ν ^ kℓ := by rw [hKℓ, hkℓ]; exact g0ℓ_le Km Kφ kφ ν
  have hTℓ : Km * (φinv + 1) ^ 2 * lg ν + 1 ≤ g0ℓ Km Kφ kφ ν := by
    show _ ≤ Km * (Kφ * lg ν ^ kφ + 1) ^ 2 * lg ν + 1
    have h1 : (φinv + 1) ^ 2 ≤ (Kφ * lg ν ^ kφ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have := Nat.mul_le_mul_right (lg ν) (Nat.mul_le_mul_left Km h1)
    omega
  have hM : MixAt C (Km * (φinv + 1) ^ 2 * lg ν) := hmix C φinv ν hCL hCne hexp hν
  set n := (nodes C).card with hn
  set m := C.card with hm
  set ℓ := g0ℓ Km Kφ kφ ν with hℓdef
  set R := g0R c' ν n m with hRdef
  set t := g0t c' K₀ ν n m with htdef
  -- the public parameters meet the guarantees of Claims 3.4/3.5
  have hgood : P.card ≤ a * n ∧ H * lg ν * (a * n) ≤ K * lg ν ^ (kℓ + 1) * (a * n) ∧
      2 * H ≤ K * lg ν ^ (kℓ + 1) ∧ 2 * (H * lg ν) + 2 * ℓ * (H * lg ν) ≤ K * lg ν ^ (kℓ + 1) ∧
      2 * ℓ + 1 ≤ K * lg ν ^ (kℓ + 1) := by
    have hHK : H ≤ K := by rw [hK]; omega
    have h2HK : 2 * H + 2 * Kℓ * H ≤ K := by rw [hK]; omega
    have h2KK : 2 * Kℓ + 1 ≤ K := by rw [hK]; omega
    have hX1 : 1 ≤ lg ν ^ (kℓ + 1) := Nat.one_le_pow _ _ hLg1
    have hLpow : lg ν ≤ lg ν ^ (kℓ + 1) := Nat.le_self_pow (by omega) _
    have hXk : lg ν ^ kℓ ≤ lg ν ^ (kℓ + 1) := Nat.pow_le_pow_right hLg1 (by omega)
    refine ⟨hPa, ?_, ?_, ?_, ?_⟩
    · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hHK hLpow)
    · calc 2 * H ≤ K * 1 := by omega
        _ ≤ K * lg ν ^ (kℓ + 1) := Nat.mul_le_mul_left _ hX1
    · calc 2 * (H * lg ν) + 2 * ℓ * (H * lg ν)
          ≤ 2 * (H * lg ν) + 2 * (Kℓ * lg ν ^ kℓ) * (H * lg ν) :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hℓK)) _
        _ = (2 * H) * lg ν + (2 * Kℓ * H) * lg ν ^ (kℓ + 1) := by ring
        _ ≤ (2 * H) * lg ν ^ (kℓ + 1) + (2 * Kℓ * H) * lg ν ^ (kℓ + 1) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hLpow) _
        _ = (2 * H + 2 * Kℓ * H) * lg ν ^ (kℓ + 1) := by ring
        _ ≤ K * lg ν ^ (kℓ + 1) := Nat.mul_le_mul_right _ h2HK
    · calc 2 * ℓ + 1 ≤ 2 * (Kℓ * lg ν ^ kℓ) + lg ν ^ kℓ := by
            have := Nat.one_le_pow kℓ (lg ν) hLg1
            omega
        _ = (2 * Kℓ + 1) * lg ν ^ kℓ := by ring
        _ ≤ K * lg ν ^ (kℓ + 1) := Nat.mul_le_mul h2KK hXk
  -- the algorithm and its guarantee
  have h := hrw (g0R c' ν) ℓ (g0t c' K₀ ν) (g0gf a H ℓ ν) N C P
    (fun g => P.card ≤ g.n0 ∧ g.n0 ≤ a * n ∧ g.m0 ≤ K * lg ν ^ (kℓ + 1) * g.n0 ∧
      g.φinv ≤ K * lg ν ^ (kℓ + 1) ∧ g.cong ≤ K * lg ν ^ (kℓ + 1) ∧
      g.dil ≤ K * lg ν ^ (kℓ + 1)) hCN hCne hPA
    ⟨hgood.1, le_rfl, hgood.2.1, hgood.2.2.1, hgood.2.2.2.1, hgood.2.2.2.2⟩
    (by rw [show Fintype.card V = ν from le_antisymm hν hν']
        exact g0_digits_le c' Kℓ kℓ ν n m ℓ hν1 hmν hℓK)
  refine T.mono h ?_ ?_
  all_goals clear h
  · -- cost
    have hround : Kc * (R + ℓ * t + 1) ≤ K * lg ν ^ (kℓ + 1) * (m / n + 1) := by
      have := g0_rounds_le Kc c' K₀ Kℓ kℓ (lg ν) ℓ (m / n) hLg1 hℓK
      refine this.trans ?_
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; rw [hK]; omega
    apply Prof.le_mk
    · simp only [Prof.rounds_mk]; exact hround
    · intro e
      simp only [Prof.load_mk, onEdges]
      split_ifs
      · exact hround.trans (Nat.le_mul_of_pos_left _ (by norm_num))
      · exact le_rfl
    · simp only [Prof.msgs_mk]
      have := g0_msgs_le Kc c' Kℓ kℓ (lg ν) ℓ a n m P.card hLg1 hℓK (by omega) hnm hPa
      refine this.trans ?_
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; rw [hK]; omega
  · -- failure probability
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have hνR : (0 : ℝ) < ν := by exact_mod_cast hν1
    -- `R |P| / m ∈ [c' lg ν, 3 a c' lg ν]`
    have hRlo : (c' : ℝ) * lg ν * m ≤ R * P.card := by
      have h1 := le_div_succ_mul m n (by omega)
      have h2 : c' * lg ν * m ≤ R * P.card := by
        show _ ≤ c' * (m / n + 1) * lg ν * P.card
        calc c' * lg ν * m ≤ c' * lg ν * ((m / n + 1) * n) := Nat.mul_le_mul_left _ h1
          _ ≤ c' * lg ν * ((m / n + 1) * P.card) := by gcongr
          _ = c' * (m / n + 1) * lg ν * P.card := by ring
      exact_mod_cast h2
    have hRhi : (R : ℝ) * P.card ≤ 3 * a * c' * lg ν * m := by
      have h2 : R * P.card ≤ 3 * a * c' * lg ν * m := by
        show c' * (m / n + 1) * lg ν * P.card ≤ _
        have := Nat.div_mul_le_self m n
        calc c' * (m / n + 1) * lg ν * P.card ≤ c' * (m / n + 1) * lg ν * (a * n) := by gcongr
          _ = c' * lg ν * a * (m / n * n + n) := by ring
          _ ≤ c' * lg ν * a * (m + 2 * m) := by gcongr
          _ = 3 * a * c' * lg ν * m := by ring
      exact_mod_cast h2
    set y : ℝ := 1 / (ν : ℝ) ^ K₀ with hy
    have hy0 : 0 ≤ y := by positivity
    have hexpy : Real.exp (-((K₀ : ℝ) * lg ν)) ≤ y := exp_neg_lg_le K₀ ν hν1
    have hM2 : 2 * (3 * (R : ℝ) * P.card / (4 * m)) ≤ 5 * a * c' * lg ν := by
      have h3 : (R : ℝ) * P.card / m ≤ 3 * a * c' * lg ν := by
        rw [div_le_iff₀ hmR]; exact hRhi
      have h0 : (0 : ℝ) ≤ a * c' * lg ν := by positivity
      have e : 2 * (3 * (R : ℝ) * P.card / (4 * m)) = (3 / 2) * ((R : ℝ) * P.card / m) := by
        field_simp; ring
      rw [e]; nlinarith
    have hHi : ((H * lg ν : ℕ) : ℝ) = (5 * a * c' : ℝ) * lg ν + K₀ * lg ν := by
      rw [hH]; push_cast; ring
    have h1 : Real.exp (2 * (R : ℝ) - ((t : ℝ) + 1)) ≤ y := by
      refine le_trans (Real.exp_le_exp.2 ?_) hexpy
      have : (t : ℝ) = 2 * R + K₀ * lg ν := by
        have ht' : t = 2 * R + K₀ * lg ν := rfl
        rw [ht']; push_cast; ring
      rw [this]; linarith
    have h2 : Real.exp (2 * (3 * (R : ℝ) * P.card / (4 * m)) - (((H * lg ν : ℕ) : ℝ) + 1)) ≤ y := by
      refine le_trans (Real.exp_le_exp.2 ?_) hexpy
      rw [hHi]; linarith
    have h4 : ∀ A ⊆ P, A.Nonempty →
        Real.exp ((A.card : ℝ) * lg ν - ((R : ℝ) * A.card * P.card / (16 * m)) / 2) ≤
          y ^ A.card := by
      intro A _ hne
      have hAc : (1 : ℝ) ≤ A.card := by exact_mod_cast hne.card_pos
      have hge : (A.card : ℝ) * ((K₀ : ℝ) + 1) * lg ν ≤ ((R : ℝ) * A.card * P.card / (16 * m)) / 2 := by
        rw [div_div, le_div_iff₀ (by positivity)]
        have : (c' : ℝ) = 32 * (K₀ + 1) := by rw [hc']; push_cast; ring
        rw [this] at hRlo
        nlinarith [mul_le_mul_of_nonneg_left hRlo (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)]
      calc Real.exp ((A.card : ℝ) * lg ν - ((R : ℝ) * A.card * P.card / (16 * m)) / 2)
          ≤ Real.exp (A.card * (-((K₀ : ℝ) * lg ν))) := by
            apply Real.exp_le_exp.2; nlinarith
        _ = Real.exp (-((K₀ : ℝ) * lg ν)) ^ A.card := by rw [Real.exp_nat_mul]
        _ ≤ y ^ A.card := by gcongr
    -- the claimed parameters `g` of the bad-event analysis are at most the public ones
    have hbound := rw_fail_le R ℓ hCne hPA hM hTℓ h2P t (H * lg ν) (H * lg ν) (lg ν) (2 * H) hLg1
      (le_of_eq (by ring))
      (fun g => g.n0 ≤ a * n ∧ g.m0 ≤ H * lg ν * (a * n) ∧ g.φinv ≤ 2 * H ∧
        g.cong ≤ 2 * (H * lg ν) + 2 * ℓ * (H * lg ν) ∧ g.dil ≤ 2 * ℓ + 1)
      ⟨hPa, Nat.mul_le_mul_left _ hPa, le_rfl, le_rfl, le_rfl⟩ y hy0 h1 h2 h2 h4
    have hsub : ∀ ω, (rwOverflow C P R ℓ t ω ∨ ¬ TrueParams C P R ℓ ω (g0gf a H ℓ ν n m)) →
        rwOverflow C P R ℓ t ω ∨ ¬ ∃ g, TrueParams C P R ℓ ω g ∧ (g.n0 ≤ a * n ∧
          g.m0 ≤ H * lg ν * (a * n) ∧ g.φinv ≤ 2 * H ∧
          g.cong ≤ 2 * (H * lg ν) + 2 * ℓ * (H * lg ν) ∧ g.dil ≤ 2 * ℓ + 1) := by
      rintro ω (hov | hT)
      · exact Or.inl hov
      · refine Or.inr fun ⟨g, hg, g1, g2, g3, g4, g5⟩ => hT ?_
        exact trueParams_mono hg g1 g2 g3 g4 g5
    -- the final sum
    refine (rwProb_mono C P R ℓ hsub).trans (hbound.trans ?_)
    have hPy : (P.card : ℝ) * y ≤ 1 := by
      rw [hy, mul_one_div, div_le_one (by positivity)]
      have : P.card ≤ ν ^ K₀ := by
        calc P.card ≤ 2 * ν ^ 2 := hPν
          _ ≤ ν * ν ^ 2 := Nat.mul_le_mul_right _ hν2
          _ = ν ^ 3 := by ring
          _ ≤ ν ^ K₀ := Nat.pow_le_pow_right hν1 (by omega)
      exact_mod_cast this
    have hsum := sum_powerset_pow_le P y hy0 hPy
    have hS := card_sym2_le V
    have hVν : Fintype.card V ^ 2 ≤ ν ^ 2 := Nat.pow_le_pow_left hν 2
    have hℓν : ℓ ≤ Kℓ * ν ^ kℓ := hℓK.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLgν _))
    have hN : 2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
        Fintype.card (Sym2 V) * (2 * ℓ) + (P.card + 1) * P.card ≤
        (4 * Kℓ + 10) * ν ^ (kℓ + 4) := by
      obtain ⟨X, hX⟩ : ∃ X, X = ν ^ (kℓ + 4) := ⟨_, rfl⟩
      rw [← hX]
      have p1 : ν ^ 2 ≤ X := by rw [hX]; exact Nat.pow_le_pow_right hν1 (by omega)
      have p3 : ν ^ (kℓ + 3) ≤ X := by rw [hX]; exact Nat.pow_le_pow_right hν1 (by omega)
      have p4 : ν ^ (kℓ + 2) ≤ X := by rw [hX]; exact Nat.pow_le_pow_right hν1 (by omega)
      have p5 : ν ^ 4 ≤ X := by rw [hX]; exact Nat.pow_le_pow_right hν1 (by omega)
      have hS' : Fintype.card (Sym2 V) ≤ ν ^ 2 := hS.trans hVν
      have e1 : 2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) ≤ 2 * (Kℓ * X) := by
        calc 2 * ℓ * Fintype.card V * Fintype.card (Sym2 V)
            ≤ 2 * (Kℓ * ν ^ kℓ) * ν * ν ^ 2 :=
              Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hℓν) hν) hS'
          _ = 2 * (Kℓ * ν ^ (kℓ + 3)) := by ring
          _ ≤ 2 * (Kℓ * X) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left Kℓ p3)
      have e2 : Fintype.card (Sym2 V) * (2 * ℓ) ≤ 2 * (Kℓ * X) := by
        calc Fintype.card (Sym2 V) * (2 * ℓ) ≤ ν ^ 2 * (2 * (Kℓ * ν ^ kℓ)) :=
              Nat.mul_le_mul hS' (Nat.mul_le_mul_left 2 hℓν)
          _ = 2 * (Kℓ * ν ^ (kℓ + 2)) := by ring
          _ ≤ 2 * (Kℓ * X) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left Kℓ p4)
      have e3 : (P.card + 1) * P.card ≤ 6 * X := by
        have : 1 ≤ ν ^ 2 := Nat.one_le_pow _ _ hν1
        calc (P.card + 1) * P.card ≤ (2 * ν ^ 2 + ν ^ 2) * (2 * ν ^ 2) :=
              Nat.mul_le_mul (by omega) hPν
          _ = 6 * ν ^ 4 := by ring
          _ ≤ 6 * X := Nat.mul_le_mul_left 6 p5
      calc 2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
            Fintype.card (Sym2 V) * (2 * ℓ) + (P.card + 1) * P.card
          ≤ 2 * (Kℓ * X) + 4 * X + 2 * (Kℓ * X) + 6 * X := by omega
        _ = (4 * Kℓ + 10) * X := by ring
    have hNR : ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
        Fintype.card (Sym2 V) * (2 * ℓ) : ℕ) : ℝ) * y +
        ((P.card + 1 : ℕ) : ℝ) * (P.card * y) ≤ ((4 * Kℓ + 10) * ν ^ (kℓ + 4) : ℕ) * y := by
      calc ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
            Fintype.card (Sym2 V) * (2 * ℓ) : ℕ) : ℝ) * y +
            ((P.card + 1 : ℕ) : ℝ) * (P.card * y)
          = ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
            Fintype.card (Sym2 V) * (2 * ℓ) + (P.card + 1) * P.card : ℕ) : ℝ) * y := by
            push_cast; ring
        _ ≤ ((4 * Kℓ + 10) * ν ^ (kℓ + 4) : ℕ) * y :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hy0
    calc _ ≤ ((2 * ℓ * Fintype.card V * Fintype.card (Sym2 V) + 2 * P.card +
          Fintype.card (Sym2 V) * (2 * ℓ) : ℕ) : ℝ) * y +
          ((P.card + 1 : ℕ) : ℝ) * (P.card * y) := by linarith
      _ ≤ ((4 * Kℓ + 10) * ν ^ (kℓ + 4) : ℕ) * y := hNR
      _ = whp (4 * Kℓ + 10) c ν := by
          unfold whp
          rw [hy, hK₀]
          push_cast
          rw [show c + kℓ + 4 = c + (kℓ + 4) by ring, pow_add]
          have hν0 : (ν : ℝ) ≠ 0 := hνR.ne'
          field_simp
          ring
end APSP.Stoc
