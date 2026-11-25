import ApspStoc.Statements

/-!
# Lemma 5.3, Lemma 5.4 and MST on a subset, from Lemma 4.2 and the physical case of Lemma 5.3
-/

namespace APSP.Stoc

open APSP Finset

/-- MST / leader election on (the components of) `G[S]`: `O(log n)` Minor-Aggregation rounds
([16, 38]) executed by Lemma 4.2. -/
theorem lemma_mst_of (T : Toolkit) (h42 : Lemma_4_2 T) : LemmaMST T := by
  obtain ⟨Km, hMst⟩ := T.mstRed
  refine ⟨fun ν => Km * lg ν, (IsPL.const Km).mul IsPL.lg', fun c fov fd hov hd => ?_⟩
  obtain ⟨qm, hqm, Kδm, Am, hM⟩ := h42 c Km hov hd
  refine ⟨fun ν => Km * lg ν * (qm ν * (Km + 1)),
    ((IsPL.const Km).mul IsPL.lg').mul (hqm.mul (IsPL.const (Km + 1))), Kδm,
    fun ν => T.mstAlg ν (Am ν Km), ?_⟩
  intro V _ _ N ν hν hνn E X hE j sz S hj hS Pt hPt
  have h := hMst (Am ν Km) ν hν hνn E j sz Pt S (szProf N.G E j sz S (qm ν * (Km + 1)))
    (whp Kδm c ν) hS hPt
    (fun I hI hsm => T.mono (hM N ν hν hνn E X hE j sz I Km hj ((card_le_card hI).trans hS) hsm
        Pt ((footprint_mono E j hI).trans hPt))
      (szProf_mono _ _ _ le_rfl hI _) le_rfl)
  rw [szProf_smul] at h
  exact T.mono h (le_of_eq (by ring_nf)) le_rfl

lemma szProf_one (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V] [DecidableEq V]
    (E : Overlays V) (j sz : ℕ) (S : Finset V) :
    Prof.mk (sz + 1) (fun e => E.rho G j S e) (S.card + 1) = szProf G E j sz S 1 := by
  unfold szProf; simp

/-- **Lemma 5.3** (Eulerian orientation on a connected subset with `polylog` virtual nodes):
the virtual nodes are handled by the technique of [37] (`eoVirt`), using Lemma 4.2 for the
Minor-Aggregation rounds; the remaining physical instance is solved by the paper's procedure
(`EOPhys`). -/
theorem lemma_5_3_of (T : Toolkit) (h42 : Lemma_4_2 T) (heo : EOPhys T) : Lemma_5_3 T := by
  intro kv hkv
  obtain ⟨Ke, ke, hEV⟩ := T.eoVirt
  let B : ℕ → ℕ := fun ν => Ke * lg ν ^ ke * (kv ν + 1) ^ 2
  have hB : IsPL B := ((IsPL.const Ke).mul (IsPL.lgpow ke)).mul ((hkv.add (IsPL.const 1)).pow 2)
  refine ⟨fun ν => B ν + 1, hB.add (IsPL.const 1), fun c fov fd hov hd => ?_⟩
  obtain ⟨qm, hqm, Kδm, Am, hM⟩ := h42 c Ke hov hd
  obtain ⟨qe, hqe, Kδe, Ae, hP⟩ := heo c hov hd
  refine ⟨fun ν => B ν * (qm ν * (B ν + 1) + 1) + qe ν,
    (hB.mul ((hqm.mul (hB.add (IsPL.const 1))).add (IsPL.const 1))).add hqe, Kδm + Kδe,
    fun ν => T.eoAlg ν (kv ν) (Am ν (B ν)) (Ae ν), ?_⟩
  intro V _ _ N ν hν hνn E X hE j sz H hj hS hconn hwf hk Pt hPt
  set b := Ke * lg ν ^ ke * (kv ν + 1) ^ 2 with hbdef
  have hbB : b ≤ B ν := le_rfl
  -- the virtual nodes are handled with the public bound `kv ν ≥ H.k`, and the MA rounds run
  -- Lemma 4.2 with the public value size `B ν`
  have h := hEV (Am ν (B ν)) (Ae ν) ν hν hνn E j sz Pt H (kv ν)
    (szProf N.G E j sz H.S (qm ν * (B ν + 1)))
    (szProf N.G E j sz H.S (qe ν)) (whp Kδm c ν) (whp Kδe c ν) hconn hwf hS hk hPt
    (fun I hI hsm => T.mono (hM N ν hν hνn E X hE j sz I (B ν) hj ((card_le_card hI).trans hS)
        (hsm (B ν) hbB) Pt ((footprint_mono E j hI).trans hPt))
      (szProf_mono _ _ _ le_rfl hI _) le_rfl)
    (fun H' hS' _ _ _ => by
      have := hP N ν hν hνn E X hE j sz H' hj (hS' ▸ hS) (by assumption) (by assumption) Pt
        (hS' ▸ hPt)
      rw [hS'] at this; exact this)
  rw [szProf_one, szProf_add, szProf_smul, szProf_add] at h
  refine T.mono h (szProf_mono_Q _ _ _ _ _ ?_) ?_
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hbB) _
  · have hw1 := whp_mono_K (Nat.le_add_right Kδm Kδe) c ν
    have hw2 := whp_mono_K (Nat.le_add_left Kδe Kδm) c ν
    have hw0 := whp_nonneg (Kδm + Kδe) c ν
    have hbB' : (b : ℝ) ≤ (B ν : ℝ) := by exact_mod_cast hbB
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
    have h1 : (b : ℝ) * whp Kδm c ν ≤ (B ν : ℝ) * whp (Kδm + Kδe) c ν :=
      mul_le_mul hbB' hw1 (whp_nonneg _ _ _) (Nat.cast_nonneg _)
    show ((b : ℕ) : ℝ) * whp Kδm c ν + whp Kδe c ν ≤ ((B ν + 1 : ℕ) : ℝ) * whp (Kδm + Kδe) c ν
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- **Lemma 5.4** (approximate SSSP on a subset): the algorithm of [37] (Lemma 5.1), whose
Minor-Aggregation rounds are executed by Lemma 4.2 and whose Eulerian-orientation instances are
solved by Lemma 5.3. -/
theorem lemma_5_4_of (T : Toolkit) (h42 : Lemma_4_2 T) (h53 : Lemma_5_3 T) : Lemma_5_4 T := by
  intro Bw
  obtain ⟨Kx, kx, hX⟩ := T.approxRed Bw
  have hm : IsPL (fun ν => Kx * lg ν ^ kx) := (IsPL.const Kx).mul (IsPL.lgpow kx)
  obtain ⟨qδe, hqδe, h53'⟩ := h53 hm
  refine ⟨fun ν => Kx * lg ν ^ kx * (1 + qδe ν), hm.mul ((IsPL.const 1).add hqδe),
    fun c fov fd hov hd => ?_⟩
  obtain ⟨qm, hqm, Kδm, Am, hM⟩ := h42 c (Kx * (Bw + 1)) hov hd
  obtain ⟨qe, hqe, Kδe, Ae, hEO⟩ := h53' c hov hd
  refine ⟨fun ν => Kx * lg ν ^ kx * (qm ν * (Kx * lg ν ^ kx + 1) + qe ν),
    hm.mul ((hqm.mul (hm.add (IsPL.const 1))).add hqe), Kδm + Kδe,
    fun ν => T.approxAlg ν (Am ν (Kx * lg ν ^ kx)) (Ae ν), ?_⟩
  intro V _ _ N ν hν hνn hwt E X hE j sz S w0 hj hS hconn hw0 Pt hPt
  have h := hX (Am ν (Kx * lg ν ^ kx)) (Ae ν) ν hν hνn E j sz Pt S w0
    (szProf N.G E j sz S (qm ν * (Kx * lg ν ^ kx + 1)))
    (szProf N.G E j sz S (qe ν)) (whp Kδm c ν) ((qδe ν : ℝ) * whp Kδe c ν) hconn hS hPt hwt hw0
    (fun I hI hsm => T.mono (hM N ν hν hνn E X hE j sz I _ hj ((card_le_card hI).trans hS) hsm
        Pt ((footprint_mono E j hI).trans hPt))
      (szProf_mono _ _ _ le_rfl hI _) le_rfl)
    (fun H hS' hwf hk => by
      have := hEO N ν hν hνn E X hE j sz H hj (hS' ▸ hS) (hS' ▸ hconn) hwf hk Pt (hS' ▸ hPt)
      rw [hS'] at this; exact this)
  rw [szProf_add, szProf_smul] at h
  refine T.mono h le_rfl ?_
  have hw1 := whp_mono_K (Nat.le_add_right Kδm Kδe) c ν
  have hw2 := whp_mono_K (Nat.le_add_left Kδe Kδm) c ν
  have hq0 : (0:ℝ) ≤ (qδe ν : ℝ) := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ ((Kx * lg ν ^ kx : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : (qδe ν : ℝ) * whp Kδe c ν ≤ (qδe ν : ℝ) * whp (Kδm + Kδe) c ν :=
    mul_le_mul_of_nonneg_left hw2 hq0
  have h4 : whp Kδm c ν + (qδe ν : ℝ) * whp Kδe c ν ≤
      (1 + (qδe ν : ℝ)) * whp (Kδm + Kδe) c ν := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 hm0
  push_cast at h5 ⊢
  linarith

end APSP.Stoc
