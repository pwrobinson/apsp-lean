import ApspStoc.Congest.SetupTree

/-!
# Cluster setup in CONGEST: the run

The states of the nodes of `C` in the run of `setupProto V D` on `clInst0 N C`, phase by phase:
`EF t` (flooding, rounds `t ≤ D`), `EC j` (counting, rounds `D + j`, `j ≤ D + 1`), `EB j`
(broadcast of `n_C`, rounds `2D + 1 + j`, `j ≤ D`), `EG k j` (gossip of the degree table, window
`k`, offset `j`), then one round of phase A (computing `A(C)` from the table), and `EH k j` (gossip
of the ports of `A(C)`, window `k`, offset `j`).
-/

namespace APSP.Stoc.Congest

open APSP Finset SimpleGraph

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The expected states -/

section Sched

variable (C : Finset (Sym2 V)) (D : ℕ) (ℓ : V)

/-- the parent after `t` flooding rounds -/
noncomputable def parF (t : ℕ) (v : V) : Option V :=
  (suDec (ballSup C suIdx t v)).bind (fun M => parOf C M v)

/-- the `n_C` field during counting -/
noncomputable def ncC (j : ℕ) (v : V) : ℕ :=
  if j = 0 then 0 else if parOf C ℓ v = none then ccz C ℓ (j + 1) v else 0

/-- the values flooded in phase B -/
noncomputable def yB (v : V) : ℕ := if v = ℓ then (nodes C).card else 0

/-- state after `t ≤ D` flooding rounds -/
noncomputable def EF (t : ℕ) (v : V) : SetupSt V :=
  ⟨t, v, ballSup C suIdx t v, parF C t v, fun _ => 0, 0, {(v, degIn C v)}, fun _ => [],
    portsAt C v⟩

/-- state after `j ≤ D + 1` counting rounds -/
noncomputable def EC (j : ℕ) (v : V) : SetupSt V :=
  ⟨D + j, v, suIdx ℓ, parOf C ℓ v, latC C ℓ j v, ncC C ℓ j v, {(v, degIn C v)}, fun _ => [],
    portsAt C v⟩

/-- state after `j ≤ D` broadcast rounds -/
noncomputable def EB (j : ℕ) (v : V) : SetupSt V :=
  ⟨2 * D + 1 + j, v, suIdx ℓ, parOf C ℓ v, latC C ℓ (D + 1) v, ballSup C (yB C ℓ) j v,
    {(v, degIn C v)}, fun _ => [], portsAt C v⟩

/-- state at offset `j` of gossip window `k` -/
noncomputable def EG (k j : ℕ) (v : V) : SetupSt V :=
  ⟨3 * D + 1 + k * (2 * (nodes C).card) + j, v, suIdx ℓ, parOf C ℓ v, latC C ℓ (D + 1) v,
    (nodes C).card, Sg C ℓ k v,
    fun u => if u ∈ nodes C ∧ tnb C ℓ u v then (encW (Sg C ℓ k u).toList).take j else [],
    portsAt C v⟩

/-- state at offset `j` of window `k` of phase H -/
noncomputable def EH (k j : ℕ) (v : V) : SetupSt V :=
  ⟨tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j, v, suIdx ℓ, parOf C ℓ v,
    latC C ℓ (D + 1) v, (nodes C).card, truePairs C,
    fun u => if u ∈ nodes C ∧ tnb C ℓ u v then (encP (Pg C ℓ k u).toList).take j else [],
    Pg C ℓ k v⟩

end Sched

/-- the arithmetic of windows -/
lemma win_lt {k j w K : ℕ} (hk : k < K) (hj : j < w) : k * w + j < K * w := by
  have : (k + 1) * w ≤ K * w := Nat.mul_le_mul_right _ hk
  rw [add_mul, one_mul] at this
  omega

/-! ## Transitions -/

lemma SetupSt.ext' {s t : SetupSt V} (h1 : s.r = t.r) (h2 : s.me = t.me) (h3 : s.m = t.m)
    (h4 : s.par = t.par) (h5 : s.lat = t.lat) (h6 : s.nc = t.nc) (h7 : s.S = t.S)
    (h8 : s.rcv = t.rcv) (h9 : s.PS = t.PS) : s = t := by
  cases s; cases t; simp_all

section Trans

variable {C : Finset (Sym2 V)} {D : ℕ} {ℓ : V}

lemma suOut_none {s : SetupSt V} (h0 : (s.me, 0) ∉ s.S)
    (h : s.r < tH D s.nc) : suOut D s = none := by
  unfold suOut; rw [ite_eq_right (not_or.2 ⟨h0, by omega⟩)]

/-- in phases F, C, B no node of `C` halts -/
lemma suOut_none_lt {s : SetupSt V} (h0 : (s.me, 0) ∉ s.S)
    (h : s.r < 3 * D + 1) : suOut D s = none :=
  suOut_none h0 (by unfold tH tG; omega)

lemma not_mem_single_zero {v : V} (hv : v ∈ nodes C) :
    (v, 0) ∉ ({(v, degIn C v)} : Finset (V × ℕ)) := by
  rw [mem_singleton, Prod.mk.injEq]
  have := degIn_pos hv
  omega

lemma not_mem_Sg_zero {k : ℕ} {v : V} (hv : v ∈ nodes C) : (v, 0) ∉ Sg C ℓ k v := fun h => by
  obtain ⟨u, hu, he⟩ := mem_image.1 (Sg_sub k v hv h)
  rw [Prod.mk.injEq] at he
  have := degIn_pos hu
  omega

lemma tnb_adj {u v : V} (h : tnb C ℓ u v) : (clGraph C).Adj u v := by
  rcases h with h | ⟨_, h⟩
  · exact (parOf_spec h).1
  · exact (parOf_spec h).1.symm

/-! ### Phase F -/

lemma recvF_EF (t : ℕ) (v : V) :
    recvF (EF C t v) (fun u => if (clGraph C).Adj u v then
      some (Word.num (V := V) (ballSup C suIdx t u)) else none) = EF C (t + 1) v := by
  set inb : V → Option (Word V) := fun u => if (clGraph C).Adj u v then
      some (Word.num (V := V) (ballSup C suIdx t u)) else none with hinb
  have hK : univ.sup (fun u => numOf (inb u)) =
      (univ.filter (fun u => (clGraph C).Adj u v)).sup (fun u => ballSup C suIdx t u) :=
    sup_numOf_adj _ v
  have hsucc := ballSup_succ (C := C) suIdx t v
  set K := (univ.filter (fun u => (clGraph C).Adj u v)).sup (fun u => ballSup C suIdx t u)
    with hKdef
  unfold recvF
  rw [hK]
  by_cases hlt : (EF C t v).m < K
  · rw [ite_eq_left hlt]
    change ballSup C suIdx t v < K at hlt
    refine SetupSt.ext' rfl rfl ?_ ?_ rfl rfl rfl rfl rfl
    · show K = ballSup C suIdx (t + 1) v
      rw [hsucc, max_eq_right hlt.le]
    · show _ = parF C (t + 1) v
      obtain ⟨M, hM, hMeq⟩ := exists_ballSup (C := C) suIdx (t + 1) v
      have hKM : K = suIdx M := by rw [← hMeq, hsucc, max_eq_right hlt.le]
      have hvM : v ≠ M := by
        intro h
        subst h
        have := le_ballSup (C := C) suIdx (self_mem_clBall (C := C) (u := v) (r := t))
        omega
      have hMt : M ∉ clBall C v t := fun h => by
        have := le_ballSup (C := C) suIdx h
        omega
      unfold parF
      rw [hMeq, suDec_suIdx, Option.bind_some]
      unfold parOf
      rw [ite_eq_right hvM]
      apply congrArg suPick
      ext u
      simp only [mem_filter, mem_univ, true_and, hinb]
      by_cases hadj : (clGraph C).Adj u v
      · rw [ite_eq_left hadj]
        simp only [Option.some.injEq, Word.num.injEq]
        rw [← mem_clBall_iff_dist_pred hM hMt hadj]
        constructor
        · intro h
          refine ⟨hadj.symm, ?_⟩
          obtain ⟨w, hw, hweq⟩ := exists_ballSup (C := C) suIdx t u
          have : w = M := suIdx_inj (by rw [← hweq, h, hKM])
          exact this ▸ hw
        · rintro ⟨_, hMu⟩
          apply le_antisymm
          · rw [hKM, ← hMeq]; exact ballSup_mono_ball suIdx hadj
          · rw [hKM]; exact le_ballSup suIdx hMu
      · rw [ite_eq_right hadj]
        simp only [reduceCtorEq, false_iff, not_and]
        exact fun h => absurd h.symm hadj
  · rw [ite_eq_right hlt]
    change ¬ ballSup C suIdx t v < K at hlt
    have hm : ballSup C suIdx (t + 1) v = ballSup C suIdx t v := by
      rw [hsucc, max_eq_left (not_lt.1 hlt)]
    refine SetupSt.ext' rfl rfl hm.symm ?_ rfl rfl rfl rfl rfl
    show parF C t v = parF C (t + 1) v
    unfold parF; rw [hm]

/-! ### Phase C -/

lemma suSend_EC {j : ℕ} (hj : j ≤ D) (u v : V) :
    suSend D (EC C D ℓ j u) v =
      if parOf C ℓ u = some v then some (.num (ccz C ℓ (j + 1) u)) else none := by
  rw [suSend_C (by simp [EC]) (by simp [EC]; omega)]
  simp only [EC]
  rw [sum_latC, ← ccz_succ]
  rfl

lemma recvC_EC {j : ℕ} (hj : j ≤ D) (v : V) :
    recvC (EC C D ℓ j v) (fun u => if (clGraph C).Adj u v then suSend D (EC C D ℓ j u) v
      else none) = EC C D ℓ (j + 1) v := by
  have hlat : (fun u => numOf (if (clGraph C).Adj u v then suSend D (EC C D ℓ j u) v
      else none)) = latC C ℓ (j + 1) v := by
    funext u
    unfold latC
    by_cases hadj : (clGraph C).Adj u v
    · rw [ite_eq_left hadj, suSend_EC hj]
      have hu : u ∈ nodes C := mem_nodes_of_adj hadj
      by_cases hp : parOf C ℓ u = some v
      · rw [ite_eq_left hp, ite_eq_left ⟨hu, hp⟩]; rfl
      · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.2)]; rfl
    · rw [ite_eq_right hadj, ite_eq_right (fun h => hadj (parOf_spec h.2).1)]; rfl
  unfold recvC
  refine SetupSt.ext' rfl rfl rfl rfl hlat ?_ rfl rfl rfl
  show (if parOf C ℓ v = none then _ else 0) = ncC C ℓ (j + 1) v
  have hsum : ∑ u, numOf (if (clGraph C).Adj u v then suSend D (EC C D ℓ j u) v else none) =
      ∑ u, latC C ℓ (j + 1) v u := by
    rw [← hlat]
  rw [hsum, sum_latC, ← ccz_succ]
  simp [ncC]

/-! ### Phase B -/

lemma recvB_EB (j : ℕ) (v : V) :
    recvB (EB C D ℓ j v) (fun u => if (clGraph C).Adj u v then
      some (Word.num (V := V) (ballSup C (yB C ℓ) j u)) else none) = EB C D ℓ (j + 1) v := by
  unfold recvB
  refine SetupSt.ext' rfl rfl rfl rfl rfl ?_ rfl rfl rfl
  exact ballSup_succ_numOf _ j v

/-! ### Phase G -/

lemma suSend_EG {k j : ℕ} (hk : k < 2 * D) (hj : j < 2 * (nodes C).card) (u v : V) :
    suSend D (EG C D ℓ k j u) v =
      if parOf C ℓ u = some v ∨ latC C ℓ (D + 1) u v ≠ 0 then
        (encW (Sg C ℓ k u).toList)[j]? else none := by
  have hw := win_lt hk hj
  rw [suSend_G (by simp [EG]; omega) (by
    show 3 * D + 1 + k * (2 * (nodes C).card) + j < tG D (nodes C).card
    unfold tG; omega)]
  simp only [EG]
  have : (3 * D + 1 + k * (2 * (nodes C).card) + j - (3 * D + 1)) % (2 * (nodes C).card) = j := by
    rw [show 3 * D + 1 + k * (2 * (nodes C).card) + j - (3 * D + 1) =
      k * (2 * (nodes C).card) + j by omega, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [this]
  rfl

variable (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C)
include hd hℓ

lemma inbox_EG {k j : ℕ} (hk : k < 2 * D) (hj : j < 2 * (nodes C).card) (v : V) :
    (fun u => if (clGraph C).Adj u v then suSend D (EG C D ℓ k j u) v else none) =
      fun u => if u ∈ nodes C ∧ tnb C ℓ u v then (encW (Sg C ℓ k u).toList)[j]? else none := by
  funext u
  by_cases hadj : (clGraph C).Adj u v
  · have hu : u ∈ nodes C := mem_nodes_of_adj hadj
    rw [ite_eq_left hadj, suSend_EG hk hj]
    have : (parOf C ℓ u = some v ∨ latC C ℓ (D + 1) u v ≠ 0) ↔ (u ∈ nodes C ∧ tnb C ℓ u v) := by
      rw [latC_ne_zero_iff]
      exact ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩
    by_cases h : u ∈ nodes C ∧ tnb C ℓ u v
    · rw [ite_eq_left (this.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (this.1 h')), ite_eq_right h]
  · rw [ite_eq_right hadj, ite_eq_right (fun h => hadj (tnb_adj h.2))]

lemma recvG_EG {k j : ℕ} (hk : k < 2 * D) (hj : j < 2 * (nodes C).card) (v : V) :
    recvG D (EG C D ℓ k j v) (fun u => if (clGraph C).Adj u v then suSend D (EG C D ℓ k j u) v
      else none) = if j + 1 = 2 * (nodes C).card then EG C D ℓ (k + 1) 0 v
        else EG C D ℓ k (j + 1) v := by
  rw [inbox_EG hd hℓ hk hj]
  have hoff : ((EG C D ℓ k j v).r - (3 * D + 1)) % (2 * (EG C D ℓ k j v).nc) = j := by
    simp only [EG]
    rw [show 3 * D + 1 + k * (2 * (nodes C).card) + j - (3 * D + 1) =
      k * (2 * (nodes C).card) + j by omega, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
  have hrcv : ∀ u, (EG C D ℓ k j v).rcv u ++ (if u ∈ nodes C ∧ tnb C ℓ u v then
      (encW (Sg C ℓ k u).toList)[j]? else none).toList =
      if u ∈ nodes C ∧ tnb C ℓ u v then (encW (Sg C ℓ k u).toList).take (j + 1) else [] := by
    intro u
    simp only [EG]
    split_ifs
    · rw [List.take_add_one]
    · rfl
  have hnc : (EG C D ℓ k j v).nc = (nodes C).card := rfl
  unfold recvG
  rw [hoff, hnc]
  by_cases hW : j + 1 = 2 * (nodes C).card
  · have hlen : ∀ u, u ∈ nodes C → (encW (Sg C ℓ k u).toList).length ≤ j + 1 := by
      intro u hu
      rw [length_encW, length_toList]
      have := (card_le_card (Sg_sub (ℓ := ℓ) k u hu)).trans (card_truePairs_le (C := C))
      omega
    rw [ite_eq_left hW, ite_eq_left hW]
    refine SetupSt.ext' ?_ rfl rfl rfl rfl rfl ?_ ?_ rfl
    · show 3 * D + 1 + k * (2 * (nodes C).card) + j + 1 =
        3 * D + 1 + (k + 1) * (2 * (nodes C).card) + 0
      rw [add_mul]; omega
    · show Sg C ℓ k v ∪ _ = Sg C ℓ (k + 1) v
      simp only [hrcv]
      rw [Sg_succ]
      congr 1
      ext q
      simp only [mem_biUnion, mem_univ, true_and, mem_filter]
      constructor
      · rintro ⟨u, hu⟩
        split_ifs at hu with h
        · refine ⟨u, h, ?_⟩
          rwa [List.take_of_length_le (hlen u h.1), decW_encW, toList_toFinset] at hu
        · simp [decW] at hu
      · rintro ⟨u, h, hq⟩
        refine ⟨u, ?_⟩
        rwa [ite_eq_left h, List.take_of_length_le (hlen u h.1), decW_encW, toList_toFinset]
    · funext u
      show [] = (if u ∈ nodes C ∧ tnb C ℓ u v then (encW (Sg C ℓ k u).toList).take 0 else [])
      simp
  · rw [ite_eq_right hW, ite_eq_right hW]
    refine SetupSt.ext' rfl rfl rfl rfl rfl rfl rfl ?_ rfl
    funext u
    exact hrcv u

end Trans

/-! ### Phase A -/

section PhaseA

variable {C : Finset (Sym2 V)} {D : ℕ} {ℓ : V}

/-- the last state of phase G is at round `tG` -/
lemma r_EG_last (v : V) : (EG C D ℓ (2 * D) 0 v).r = tG D (EG C D ℓ (2 * D) 0 v).nc := rfl

lemma not_mem_truePairs_zero {v : V} : (v, 0) ∉ truePairs C := fun h => by
  obtain ⟨u, hu, he⟩ := mem_image.1 h
  rw [Prod.mk.injEq] at he
  have := degIn_pos hu
  omega

/-- Phase A turns the last state of phase G into the first state of phase H: the table is
complete, so every node computes `A(C)` (`aggT_truePairs`), and exactly the nodes of `A(C)` keep
their ports. -/
lemma recvA_EG (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C) {v : V} (hv : v ∈ nodes C) :
    recvA (EG C D ℓ (2 * D) 0 v) = EH C D ℓ 0 0 v := by
  unfold recvA
  refine SetupSt.ext' ?_ rfl rfl rfl rfl rfl ?_ ?_ ?_
  · show 3 * D + 1 + 2 * D * (2 * (nodes C).card) + 0 + 1 =
      tG D (nodes C).card + 1 + 0 * (4 * (nodes C).card) + 0
    unfold tG
    omega
  · exact Sg_full hd hℓ hv
  · funext u
    show (if u ∈ nodes C ∧ tnb C ℓ u v then (encW (Sg C ℓ (2 * D) u).toList).take 0 else []) =
      (if u ∈ nodes C ∧ tnb C ℓ u v then (encP (Pg C ℓ 0 u).toList).take 0 else [])
    simp
  · show (if v ∈ aggT (Sg C ℓ (2 * D) v) then portsAt C v else ∅) = Pg C ℓ 0 v
    rw [Sg_full hd hℓ hv, aggT_truePairs]
    rfl

end PhaseA

/-! ### Phase H -/

section PhaseH

variable {C : Finset (Sym2 V)} {D : ℕ} {ℓ : V}

lemma suSend_EH {k j : ℕ} (hj : j < 4 * (nodes C).card) (u v : V) :
    suSend D (EH C D ℓ k j u) v =
      if parOf C ℓ u = some v ∨ latC C ℓ (D + 1) u v ≠ 0 then
        (encP (Pg C ℓ k u).toList)[j]? else none := by
  rw [suSend_H (by
    show tG D (nodes C).card < tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j
    omega)]
  simp only [EH]
  have : (tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j - (tG D (nodes C).card + 1)) %
      (4 * (nodes C).card) = j := by
    rw [show tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j - (tG D (nodes C).card + 1) =
      k * (4 * (nodes C).card) + j by omega, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [this]
  rfl

lemma inbox_EH {k j : ℕ} (hj : j < 4 * (nodes C).card) (v : V) :
    (fun u => if (clGraph C).Adj u v then suSend D (EH C D ℓ k j u) v else none) =
      fun u => if u ∈ nodes C ∧ tnb C ℓ u v then (encP (Pg C ℓ k u).toList)[j]? else none := by
  funext u
  by_cases hadj : (clGraph C).Adj u v
  · have hu : u ∈ nodes C := mem_nodes_of_adj hadj
    rw [ite_eq_left hadj, suSend_EH hj]
    have : (parOf C ℓ u = some v ∨ latC C ℓ (D + 1) u v ≠ 0) ↔ (u ∈ nodes C ∧ tnb C ℓ u v) := by
      rw [latC_ne_zero_iff]
      exact ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩
    by_cases h : u ∈ nodes C ∧ tnb C ℓ u v
    · rw [ite_eq_left (this.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (this.1 h')), ite_eq_right h]
  · rw [ite_eq_right hadj, ite_eq_right (fun h => hadj (tnb_adj h.2))]

lemma recvH_EH (hP : (portsA C).card < 2 * (nodes C).card) {k j : ℕ}
    (hj : j < 4 * (nodes C).card) (v : V) :
    recvH D (EH C D ℓ k j v) (fun u => if (clGraph C).Adj u v then suSend D (EH C D ℓ k j u) v
      else none) = if j + 1 = 4 * (nodes C).card then EH C D ℓ (k + 1) 0 v
        else EH C D ℓ k (j + 1) v := by
  rw [inbox_EH hj]
  have hoff : ((EH C D ℓ k j v).r - (tG D (EH C D ℓ k j v).nc + 1)) %
      (4 * (EH C D ℓ k j v).nc) = j := by
    simp only [EH]
    rw [show tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j - (tG D (nodes C).card + 1) =
      k * (4 * (nodes C).card) + j by omega, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
  have hrcv : ∀ u, (EH C D ℓ k j v).rcv u ++ (if u ∈ nodes C ∧ tnb C ℓ u v then
      (encP (Pg C ℓ k u).toList)[j]? else none).toList =
      if u ∈ nodes C ∧ tnb C ℓ u v then (encP (Pg C ℓ k u).toList).take (j + 1) else [] := by
    intro u
    simp only [EH]
    split_ifs
    · rw [List.take_add_one]
    · rfl
  have hnc : (EH C D ℓ k j v).nc = (nodes C).card := rfl
  unfold recvH
  rw [hoff, hnc]
  by_cases hW : j + 1 = 4 * (nodes C).card
  · have hlen : ∀ u, u ∈ nodes C → (encP (Pg C ℓ k u).toList).length ≤ j + 1 := by
      intro u hu
      rw [length_encP, length_toList]
      have := card_le_card (Pg_sub (ℓ := ℓ) k u hu)
      omega
    rw [ite_eq_left hW, ite_eq_left hW]
    refine SetupSt.ext' ?_ rfl rfl rfl rfl rfl rfl ?_ ?_
    · show tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j + 1 =
        tG D (nodes C).card + 1 + (k + 1) * (4 * (nodes C).card) + 0
      rw [add_mul]; omega
    · funext u
      show [] = (if u ∈ nodes C ∧ tnb C ℓ u v then (encP (Pg C ℓ (k + 1) u).toList).take 0 else [])
      simp
    · show Pg C ℓ k v ∪ _ = Pg C ℓ (k + 1) v
      simp only [hrcv]
      rw [Pg_succ]
      congr 1
      ext q
      simp only [mem_biUnion, mem_univ, true_and, mem_filter]
      constructor
      · rintro ⟨u, hu⟩
        split_ifs at hu with h
        · refine ⟨u, h, ?_⟩
          rwa [List.take_of_length_le (hlen u h.1), decP_encP, toList_toFinset] at hu
        · simp [decP] at hu
      · rintro ⟨u, h, hq⟩
        refine ⟨u, ?_⟩
        rwa [ite_eq_left h, List.take_of_length_le (hlen u h.1), decP_encP, toList_toFinset]
  · rw [ite_eq_right hW, ite_eq_right hW]
    refine SetupSt.ext' rfl rfl rfl rfl rfl rfl rfl ?_ rfl
    funext u
    exact hrcv u

end PhaseH

/-! ## The run, phase by phase -/

section RunLemmas

variable {N : WNet V} {C : Finset (Sym2 V)} {D : ℕ} {ℓ : V}
  (hCG : C ⊆ N.G.edgeFinset) (hd : DiamLe C D) (hℓ : ℓ ∈ nodes C)
  (hmax : ∀ u ∈ nodes C, suIdx u ≤ suIdx ℓ) (x : Agent V → Mem) (ω : V → Unit)

include hCG in
/-- the incident edges of non-zero weight in the local view are the incident edges of `C` -/
lemma filter_clView (v : V) :
    univ.filter (fun e => clView N C v e ≠ 0) = C.filter (fun e => v ∈ e) := by
  ext e
  simp only [mem_filter, mem_univ, true_and]
  unfold clView
  split_ifs with h
  · have hw := N.wpos e (by have := hCG h.1; rwa [SimpleGraph.mem_edgeFinset] at this)
    simp only [h, and_self, iff_true]
    omega
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact fun h' => h ⟨h'.1, h'.2⟩

include hCG in
lemma suDeg_ctx (v : V) : suDeg ((clInst0 N C).ctx v) = degIn C v := by
  have h2 : ((clInst0 N C).ctx v).view (.inl v) = some (clView N C v) := by
    simp [clInst0, clInstP]
  unfold suDeg
  rw [show ((clInst0 N C).ctx v).me = v from rfl, h2]
  show (univ.filter (fun e => clView N C v e ≠ 0)).card = degIn C v
  rw [filter_clView hCG]
  rfl

include hCG in
/-- a node reads its ports in `C` from its local view -/
lemma suPorts_ctx (v : V) : suPorts ((clInst0 N C).ctx v) = portsAt C v := by
  have h2 : ((clInst0 N C).ctx v).view (.inl v) = some (clView N C v) := by
    simp [clInst0, clInstP]
  unfold suPorts
  rw [show ((clInst0 N C).ctx v).me = v from rfl, h2]
  show (univ.filter (fun e => clView N C v e ≠ 0)).image (fun e => (v, e)) = portsAt C v
  rw [filter_clView hCG]
  rfl

include hCG in
/-- **Phase F.** -/
lemma runF : ∀ t ≤ D, ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω t v = EF C t v := by
  intro t
  induction t with
  | zero =>
    intro _ v _
    rw [st_setup_zero]
    refine SetupSt.ext' rfl rfl ?_ ?_ rfl rfl ?_ rfl (suPorts_ctx hCG v)
    · show suIdx v = ballSup C suIdx 0 v
      rw [ballSup_zero]
    · show none = parF C 0 v
      simp [parF, ballSup_zero, suDec_suIdx, parOf_self]
    · show {(v, suDeg ((clInst0 N C).ctx v))} = {(v, degIn C v)}
      rw [suDeg_ctx hCG]
  | succ t ih =>
    intro ht v hv
    have hE := ih (by omega)
    have hr : ∀ u, (EF C t u).r < D := fun u => by show t < D; omega
    rw [st_setup_succ hCG (EF C t) hE
      (fun u hu => suOut_none_lt (not_mem_single_zero hu) (by show t < _; omega)) ?_ hv]
    · rw [suRecv_F (hr v)]
      have : (fun u => if (clGraph C).Adj u v then suSend D (EF C t u) v else none) =
          fun u => if (clGraph C).Adj u v then
            some (Word.num (V := V) (ballSup C suIdx t u)) else none := by
        funext u; rw [suSend_F (hr u)]; rfl
      rw [this, recvF_EF]
    · intro u v' _ w hw
      rw [suSend_F (hr u)] at hw
      cases hw
      show ballSup C suIdx t u ≤ Fintype.card V + 3
      have := ballSup_le (C := C) (y := suIdx) (j := t) (v := u) (b := Fintype.card V)
        (fun x _ => (suIdx_lt x).le)
      omega

include hCG hd hℓ hmax in
/-- **Phase C.** -/
lemma runC : ∀ j ≤ D + 1, ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω (D + j) v = EC C D ℓ j v := by
  intro j
  induction j with
  | zero =>
    intro _ v hv
    rw [Nat.add_zero, runF hCG x ω D le_rfl v hv]
    have hb : ballSup C suIdx D v = suIdx ℓ := by
      unfold ballSup
      rw [clBall_eq_nodes hd hv]
      exact le_antisymm (Finset.sup_le hmax) (le_sup hℓ)
    refine SetupSt.ext' rfl rfl hb ?_ ?_ rfl rfl rfl rfl
    · show parF C D v = parOf C ℓ v
      unfold parF; rw [hb, suDec_suIdx]; rfl
    · show (fun _ => 0) = latC C ℓ 0 v
      rw [latC_zero]
  | succ j ih =>
    intro hj v hv
    have hE := ih (by omega)
    rw [← Nat.add_assoc, st_setup_succ hCG (EC C D ℓ j) hE
      (fun u hu => suOut_none_lt (not_mem_single_zero hu) (by show D + j < _; omega)) ?_ hv]
    · rw [suRecv_C (show D ≤ D + j by omega) (show D + j < 2 * D + 1 by omega), recvC_EC (by omega)]
    · intro u v' hadj w hw
      rw [suSend_EC (by omega)] at hw
      split_ifs at hw
      cases hw
      show ccz C ℓ (j + 1) u ≤ Fintype.card V + 3
      have := ccz_le_card hd hℓ (j + 1) (mem_nodes_of_adj hadj)
      have := card_le_univ (nodes C)
      omega

lemma yB_le (v : V) : yB C ℓ v ≤ (nodes C).card := by
  unfold yB; split_ifs <;> omega

include hCG hd hℓ hmax in
/-- **Phase B.** -/
lemma runB : ∀ j ≤ D, ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω (2 * D + 1 + j) v = EB C D ℓ j v := by
  intro j
  induction j with
  | zero =>
    intro _ v hv
    rw [show 2 * D + 1 + 0 = D + (D + 1) by omega, runC hCG hd hℓ hmax x ω (D + 1) le_rfl v hv]
    refine SetupSt.ext' (by show D + (D + 1) = 2 * D + 1 + 0; omega) rfl rfl rfl rfl ?_ rfl rfl
      rfl
    show ncC C ℓ (D + 1) v = ballSup C (yB C ℓ) 0 v
    rw [ballSup_zero]
    unfold ncC yB
    rw [ite_eq_right (Nat.add_one_ne_zero D)]
    by_cases hvl : v = ℓ
    · subst hvl
      rw [parOf_self, ite_eq_left rfl, ite_eq_left rfl]
      exact ccz_root hd hℓ
    · rw [ite_eq_right (fun h => hvl ((parOf_eq_none_iff hd hℓ hv).1 h)), ite_eq_right hvl]
  | succ j ih =>
    intro hj v hv
    have hE := ih (by omega)
    have hr1 : ∀ u, 2 * D + 1 ≤ (EB C D ℓ j u).r := fun u => by show 2 * D + 1 ≤ 2 * D + 1 + j; omega
    have hr2 : ∀ u, (EB C D ℓ j u).r < 3 * D + 1 := fun u => by show 2 * D + 1 + j < _; omega
    rw [← Nat.add_assoc, st_setup_succ hCG (EB C D ℓ j) hE
      (fun u hu => suOut_none_lt (not_mem_single_zero hu) (by show 2 * D + 1 + j < _; omega)) ?_ hv]
    · rw [suRecv_B (hr1 v) (hr2 v)]
      have : (fun u => if (clGraph C).Adj u v then suSend D (EB C D ℓ j u) v else none) =
          fun u => if (clGraph C).Adj u v then
            some (Word.num (V := V) (ballSup C (yB C ℓ) j u)) else none := by
        funext u; rw [suSend_B (hr1 u) (hr2 u)]; rfl
      rw [this, recvB_EB]
    · intro u v' _ w hw
      rw [suSend_B (hr1 u) (hr2 u)] at hw
      cases hw
      show ballSup C (yB C ℓ) j u ≤ Fintype.card V + 3
      have := ballSup_le (C := C) (y := yB C ℓ) (j := j) (v := u) (b := (nodes C).card)
        (fun x _ => yB_le x)
      have := card_le_univ (nodes C)
      omega

include hCG hd hℓ hmax in
lemma runG0 : ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω (3 * D + 1) v = EG C D ℓ 0 0 v := by
  intro v hv
  rw [show 3 * D + 1 = 2 * D + 1 + D by omega, runB hCG hd hℓ hmax x ω D le_rfl v hv]
  refine SetupSt.ext' (by show 2 * D + 1 + D = 3 * D + 1 + 0 * _ + 0; omega) rfl rfl rfl rfl
    ?_ rfl ?_ rfl
  · show ballSup C (yB C ℓ) D v = (nodes C).card
    unfold ballSup
    rw [clBall_eq_nodes hd hv]
    apply le_antisymm (Finset.sup_le (fun x _ => yB_le x))
    calc (nodes C).card = yB C ℓ ℓ := by simp [yB]
      _ ≤ _ := le_sup hℓ
  · funext u
    show [] = (if u ∈ nodes C ∧ tnb C ℓ u v then (encW (Sg C ℓ 0 u).toList).take 0 else [])
    simp

include hCG hd hℓ in
/-- **Phase G**, one round. -/
lemma runG_step {k j : ℕ} (hk : k < 2 * D) (hj : j < 2 * (nodes C).card)
    (hE : ∀ u ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω
      (3 * D + 1 + k * (2 * (nodes C).card) + j) u = EG C D ℓ k j u)
    {v : V} (hv : v ∈ nodes C) :
    st (setupProto V D) (clInst0 N C) x ω (3 * D + 1 + k * (2 * (nodes C).card) + j + 1) v =
      if j + 1 = 2 * (nodes C).card then EG C D ℓ (k + 1) 0 v else EG C D ℓ k (j + 1) v := by
  have hwl := win_lt hk hj
  have hout : ∀ u ∈ nodes C, suOut D (EG C D ℓ k j u) = none := by
    intro u hu
    apply suOut_none (not_mem_Sg_zero hu)
    show 3 * D + 1 + k * (2 * (nodes C).card) + j < tH D (nodes C).card
    unfold tH tG
    omega
  rw [st_setup_succ hCG (EG C D ℓ k j) hE hout ?_ hv]
  · rw [suRecv_G (show 3 * D + 1 ≤ 3 * D + 1 + k * (2 * (nodes C).card) + j by omega)
      (show 3 * D + 1 + k * (2 * (nodes C).card) + j < tG D (nodes C).card by unfold tG; omega),
      recvG_EG hd hℓ hk hj]
  · intro u v' hadj w hw
    rw [suSend_EG hk hj] at hw
    split_ifs at hw
    · have hmem : w ∈ encW (Sg C ℓ k u).toList := List.mem_of_getElem? hw
      refine wordOK_of_mem_encW (fun p hp => ?_) hmem
      rw [mem_toList] at hp
      have hu := mem_nodes_of_adj hadj
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (Sg_sub k u hu hp)
      have := degIn_succ_le (noLoops_of_sub N C hCG) ha
      have := card_le_univ (nodes C)
      show degIn C a ≤ Fintype.card V + 3
      omega

include hCG hd hℓ in
lemma runG_window {k : ℕ} (hk : k < 2 * D)
    (h0 : ∀ v ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω
      (3 * D + 1 + k * (2 * (nodes C).card)) v = EG C D ℓ k 0 v) :
    ∀ j < 2 * (nodes C).card, ∀ v ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω
      (3 * D + 1 + k * (2 * (nodes C).card) + j) v = EG C D ℓ k j v := by
  intro j
  induction j with
  | zero => intro _ v hv; exact h0 v hv
  | succ j ih =>
    intro hj v hv
    rw [← Nat.add_assoc, runG_step hCG hd hℓ x ω hk (by omega) (ih (by omega)) hv,
      ite_eq_right (by omega)]

include hCG hd hℓ hmax in
/-- **Phase G**, window by window. -/
lemma runG : ∀ k ≤ 2 * D, ∀ v ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω
    (3 * D + 1 + k * (2 * (nodes C).card)) v = EG C D ℓ k 0 v := by
  have hn : 0 < (nodes C).card := card_pos.2 ⟨ℓ, hℓ⟩
  intro k
  induction k with
  | zero => intro _ v hv; simpa using runG0 hCG hd hℓ hmax x ω v hv
  | succ k ih =>
    intro hk v hv
    have hwin := runG_window hCG hd hℓ x ω (by omega) (ih (by omega))
    have := runG_step hCG hd hℓ x ω (k := k) (j := 2 * (nodes C).card - 1) (by omega) (by omega)
      (hwin _ (by omega)) hv
    rw [ite_eq_left (by omega)] at this
    rw [show 3 * D + 1 + (k + 1) * (2 * (nodes C).card) =
      3 * D + 1 + k * (2 * (nodes C).card) + (2 * (nodes C).card - 1) + 1 by rw [add_mul]; omega]
    exact this

include hCG hd hℓ hmax in
lemma runG_at {i : ℕ} (hi : i < 2 * D * (2 * (nodes C).card)) : ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω (3 * D + 1 + i) v =
      EG C D ℓ (i / (2 * (nodes C).card)) (i % (2 * (nodes C).card)) v := by
  have hn : 0 < (nodes C).card := card_pos.2 ⟨ℓ, hℓ⟩
  have hk : i / (2 * (nodes C).card) < 2 * D :=
    Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi)
  intro v hv
  rw [← runG_window hCG hd hℓ x ω hk (runG hCG hd hℓ hmax x ω _ hk.le) _
    (Nat.mod_lt _ (by omega)) v hv]
  congr 1
  have := Nat.div_add_mod' i (2 * (nodes C).card)
  omega

include hCG hd hℓ hmax in
/-- **Phase A**: one round without messages; afterwards exactly the nodes of `A(C)` hold their
ports. -/
lemma runA : ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω (tG D (nodes C).card + 1) v = EH C D ℓ 0 0 v := by
  intro v hv
  have hE : ∀ u ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω (tG D (nodes C).card) u =
      EG C D ℓ (2 * D) 0 u :=
    fun u hu => runG hCG hd hℓ hmax x ω (2 * D) le_rfl u hu
  have hout : ∀ u ∈ nodes C, suOut D (EG C D ℓ (2 * D) 0 u) = none := by
    intro u hu
    apply suOut_none (not_mem_Sg_zero hu)
    show 3 * D + 1 + 2 * D * (2 * (nodes C).card) + 0 < tH D (nodes C).card
    unfold tH tG
    omega
  rw [st_setup_succ hCG (EG C D ℓ (2 * D) 0) hE hout ?_ hv]
  · rw [suRecv_A (r_EG_last v), recvA_EG hd hℓ hv]
  · intro u v' _ w hw
    rw [suSend_A (r_EG_last u)] at hw
    cases hw

include hCG in
/-- **Phase H**, one round. -/
lemma runH_step (hP : (portsA C).card < 2 * (nodes C).card) {k j : ℕ} (hk : k < 2 * D)
    (hj : j < 4 * (nodes C).card)
    (hE : ∀ u ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω
      (tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j) u = EH C D ℓ k j u)
    {v : V} (hv : v ∈ nodes C) :
    st (setupProto V D) (clInst0 N C) x ω
        (tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j + 1) v =
      if j + 1 = 4 * (nodes C).card then EH C D ℓ (k + 1) 0 v else EH C D ℓ k (j + 1) v := by
  have hwl := win_lt hk hj
  have hout : ∀ u ∈ nodes C, suOut D (EH C D ℓ k j u) = none := by
    intro u hu
    apply suOut_none (not_mem_truePairs_zero)
    show tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j < tH D (nodes C).card
    unfold tH
    omega
  rw [st_setup_succ hCG (EH C D ℓ k j) hE hout ?_ hv]
  · rw [suRecv_H (show tG D (nodes C).card <
      tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j by omega), recvH_EH hP hj]
  · intro u v' _ w hw
    rw [suSend_EH hj] at hw
    split_ifs at hw
    exact wordOK_of_mem_encP (List.mem_of_getElem? hw)

include hCG in
lemma runH_window (hP : (portsA C).card < 2 * (nodes C).card) {k : ℕ} (hk : k < 2 * D)
    (h0 : ∀ v ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω
      (tG D (nodes C).card + 1 + k * (4 * (nodes C).card)) v = EH C D ℓ k 0 v) :
    ∀ j < 4 * (nodes C).card, ∀ v ∈ nodes C, st (setupProto V D) (clInst0 N C) x ω
      (tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + j) v = EH C D ℓ k j v := by
  intro j
  induction j with
  | zero => intro _ v hv; exact h0 v hv
  | succ j ih =>
    intro hj v hv
    rw [← Nat.add_assoc, runH_step hCG x ω hP hk (by omega) (ih (by omega)) hv,
      ite_eq_right (by omega)]

include hCG hd hℓ hmax in
/-- **Phase H**, window by window. -/
lemma runH (hP : (portsA C).card < 2 * (nodes C).card) : ∀ k ≤ 2 * D, ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω
      (tG D (nodes C).card + 1 + k * (4 * (nodes C).card)) v = EH C D ℓ k 0 v := by
  have hn : 0 < (nodes C).card := card_pos.2 ⟨ℓ, hℓ⟩
  intro k
  induction k with
  | zero => intro _ v hv; simpa using runA hCG hd hℓ hmax x ω v hv
  | succ k ih =>
    intro hk v hv
    have hwin := runH_window hCG x ω hP (by omega) (ih (by omega))
    have := runH_step hCG x ω hP (k := k) (j := 4 * (nodes C).card - 1) (by omega) (by omega)
      (hwin _ (by omega)) hv
    rw [ite_eq_left (by omega)] at this
    rw [show tG D (nodes C).card + 1 + (k + 1) * (4 * (nodes C).card) =
      tG D (nodes C).card + 1 + k * (4 * (nodes C).card) + (4 * (nodes C).card - 1) + 1 by
        rw [add_mul]; omega]
    exact this

include hCG hd hℓ hmax in
lemma runH_at (hP : (portsA C).card < 2 * (nodes C).card) {i : ℕ}
    (hi : i < 2 * D * (4 * (nodes C).card)) : ∀ v ∈ nodes C,
    st (setupProto V D) (clInst0 N C) x ω (tG D (nodes C).card + 1 + i) v =
      EH C D ℓ (i / (4 * (nodes C).card)) (i % (4 * (nodes C).card)) v := by
  have hn : 0 < (nodes C).card := card_pos.2 ⟨ℓ, hℓ⟩
  have hk : i / (4 * (nodes C).card) < 2 * D :=
    Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi)
  intro v hv
  rw [← runH_window hCG x ω hP hk (runH hCG hd hℓ hmax x ω hP _ hk.le) _
    (Nat.mod_lt _ (by omega)) v hv]
  congr 1
  have := Nat.div_add_mod' i (4 * (nodes C).card)
  omega

end RunLemmas

end APSP.Stoc.Congest
