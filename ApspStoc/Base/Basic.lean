import Mathlib

/-!
# Basic definitions

Logarithms, failure probabilities, cost profiles, weighted networks, weighted distances, and the
(semantic) SSSP and APSP output specifications.
-/

namespace APSP

open Finset

/-! ## Logarithms -/

/-- `lg n = ⌊log₂ n⌋ + 1`, an everywhere-positive base-2 logarithm. -/
def lg (n : ℕ) : ℕ := Nat.log 2 n + 1

lemma one_le_lg (n : ℕ) : 1 ≤ lg n := Nat.le_add_left 1 _

lemma lg_pos (n : ℕ) : 0 < lg n := one_le_lg n

lemma lt_two_pow_lg (n : ℕ) : n < 2 ^ lg n := Nat.lt_pow_succ_log_self (by norm_num) n

lemma lg_mul_le (a b : ℕ) : lg (a * b) ≤ lg a + lg b := by
  unfold lg
  by_cases h : a * b = 0
  · rw [h]; simp only [Nat.log_zero_right]; omega
  · have h1 : a * b < 2 ^ (lg a + lg b) := by
      rw [pow_add]
      exact Nat.mul_lt_mul'' (lt_two_pow_lg a) (lt_two_pow_lg b)
    have := Nat.log_lt_of_lt_pow h h1
    unfold lg at this
    omega

lemma lg_pow_le (n k : ℕ) : lg (n ^ k) ≤ k * lg n + 1 := by
  induction k with
  | zero => simp [lg]
  | succ k ih =>
    calc lg (n ^ (k+1)) = lg (n ^ k * n) := by rw [pow_succ]
      _ ≤ lg (n ^ k) + lg n := lg_mul_le _ _
      _ ≤ (k + 1) * lg n + 1 := by nlinarith

lemma lg_pow_le_pow_max_left (ν a b : ℕ) : lg ν ^ a ≤ lg ν ^ max a b :=
  Nat.pow_le_pow_right (lg_pos ν) (le_max_left a b)

lemma lg_pow_le_pow_max_right (ν a b : ℕ) : lg ν ^ b ≤ lg ν ^ max a b :=
  Nat.pow_le_pow_right (lg_pos ν) (le_max_right a b)

/-! ## Failure probabilities -/

/-- The failure-probability bound `K / ν^c`. -/
noncomputable def whp (K c ν : ℕ) : ℝ := (K : ℝ) / (ν : ℝ) ^ c

lemma whp_nonneg (K c ν : ℕ) : 0 ≤ whp K c ν := by
  unfold whp; positivity

lemma whp_mono_K {K K' : ℕ} (h : K ≤ K') (c ν : ℕ) : whp K c ν ≤ whp K' c ν := by
  unfold whp; gcongr

/-- Union bound bookkeeping: `A · ν^a` events with failure `K / ν^(c+a)` each fail with
probability at most `A·K / ν^c`. -/
lemma whp_union (A a K c ν : ℕ) (hν : 1 ≤ ν) (M : ℕ) (hM : M ≤ A * ν ^ a) :
    (M : ℝ) * whp K (c + a) ν ≤ whp (A * K) c ν := by
  unfold whp
  have hν' : (0 : ℝ) < ν := by exact_mod_cast hν
  have hpow : (0 : ℝ) < (ν : ℝ) ^ c := by positivity
  have hpa : (0 : ℝ) < (ν : ℝ) ^ a := by positivity
  rw [pow_add, mul_div_assoc', div_le_div_iff₀ (by positivity) hpow]
  have : (M : ℝ) ≤ A * (ν : ℝ) ^ a := by exact_mod_cast hM
  push_cast
  calc (M : ℝ) * K * (ν : ℝ) ^ c ≤ (A * (ν : ℝ) ^ a) * K * (ν : ℝ) ^ c := by gcongr
    _ = (A * K) * ((ν : ℝ) ^ c * (ν : ℝ) ^ a) := by ring

/-! ## Cost profiles -/

/-- A cost profile of a (CONGEST) execution: `(rounds, per-edge message load, total messages)`.
All three components are *upper bounds* (the load and the total are bounded independently). -/
abbrev Prof (V : Type) := ℕ × (Sym2 V → ℕ) × ℕ

namespace Prof
variable {V : Type}
def rounds (p : Prof V) : ℕ := p.1
def load (p : Prof V) : Sym2 V → ℕ := p.2.1
def msgs (p : Prof V) : ℕ := p.2.2
def mk (r : ℕ) (l : Sym2 V → ℕ) (m : ℕ) : Prof V := (r, l, m)
@[simp] lemma rounds_mk (r l m) : (mk r l m : Prof V).rounds = r := rfl
@[simp] lemma load_mk (r l m) : (mk r l m : Prof V).load = l := rfl
@[simp] lemma msgs_mk (r l m) : (mk r l m : Prof V).msgs = m := rfl
@[simp] lemma rounds_add (p q : Prof V) : (p + q).rounds = p.rounds + q.rounds := rfl
@[simp] lemma load_add (p q : Prof V) : (p + q).load = p.load + q.load := rfl
@[simp] lemma msgs_add (p q : Prof V) : (p + q).msgs = p.msgs + q.msgs := rfl
@[simp] lemma rounds_smul (k : ℕ) (p : Prof V) : (k • p).rounds = k * p.rounds := rfl
@[simp] lemma load_smul (k : ℕ) (p : Prof V) : (k • p).load = k • p.load := rfl
@[simp] lemma msgs_smul (k : ℕ) (p : Prof V) : (k • p).msgs = k * p.msgs := rfl
@[simp] lemma rounds_zero : (0 : Prof V).rounds = 0 := rfl
@[simp] lemma load_zero : (0 : Prof V).load = 0 := rfl
@[simp] lemma msgs_zero : (0 : Prof V).msgs = 0 := rfl

lemma le_iff (p q : Prof V) :
    p ≤ q ↔ p.rounds ≤ q.rounds ∧ (∀ e, p.load e ≤ q.load e) ∧ p.msgs ≤ q.msgs := by
  obtain ⟨a, b, c⟩ := p; obtain ⟨a', b', c'⟩ := q
  simp [rounds, load, msgs, Prod.le_def, Pi.le_def]

lemma le_mk (p : Prof V) (r l m) (h1 : p.rounds ≤ r) (h2 : ∀ e, p.load e ≤ l e)
    (h3 : p.msgs ≤ m) : p ≤ mk r l m := (le_iff _ _).2 ⟨h1, h2, h3⟩

@[simp] lemma rounds_sum {ι : Type*} (s : Finset ι) (f : ι → Prof V) :
    (∑ i ∈ s, f i).rounds = ∑ i ∈ s, (f i).rounds := by
  unfold rounds; exact Prod.fst_sum
@[simp] lemma load_sum {ι : Type*} (s : Finset ι) (f : ι → Prof V) (e : Sym2 V) :
    (∑ i ∈ s, f i).load e = ∑ i ∈ s, (f i).load e := by
  unfold load; rw [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
@[simp] lemma msgs_sum {ι : Type*} (s : Finset ι) (f : ι → Prof V) :
    (∑ i ∈ s, f i).msgs = ∑ i ∈ s, (f i).msgs := by
  unfold msgs; rw [Prod.snd_sum, Prod.snd_sum]

end Prof

/-! ## Weighted networks -/

/-- A weighted, connected, undirected communication network (`n = |V|` processors). -/
structure WNet (V : Type) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  [dec : DecidableRel G.Adj]
  w : Sym2 V → ℕ
  conn : G.Connected
  wpos : ∀ e ∈ G.edgeSet, 1 ≤ w e

attribute [instance] WNet.dec

variable {V : Type} [Fintype V] [DecidableEq V]

namespace WNet
variable (N : WNet V)

/-- weighted length of a walk -/
def wlen {u v : V} (p : N.G.Walk u v) : ℕ := (p.edges.map N.w).sum

lemma wlen_reverse {u v : V} (p : N.G.Walk u v) : N.wlen p.reverse = N.wlen p := by
  unfold wlen; rw [SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]

/-- weighted shortest-path distance -/
noncomputable def wdist (u v : V) : ℕ := sInf (Set.range (fun p : N.G.Walk u v => N.wlen p))

lemma wdist_le {u v : V} (p : N.G.Walk u v) : N.wdist u v ≤ N.wlen p :=
  Nat.sInf_le ⟨p, rfl⟩

lemma exists_walk_wdist (u v : V) : ∃ p : N.G.Walk u v, N.wlen p = N.wdist u v := by
  have hne : (Set.range (fun p : N.G.Walk u v => N.wlen p)).Nonempty :=
    ⟨_, ⟨(N.conn.preconnected u v).some, rfl⟩⟩
  exact Nat.sInf_mem hne

lemma wdist_comm (u v : V) : N.wdist u v = N.wdist v u := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := N.exists_walk_wdist v u
    rw [← hp, ← N.wlen_reverse p]; exact N.wdist_le _
  · obtain ⟨p, hp⟩ := N.exists_walk_wdist u v
    rw [← hp, ← N.wlen_reverse p]; exact N.wdist_le _

end WNet

/-! ## Output specifications -/

/-- SSSP from `s`: every node `v` outputs `(d, x)` where `d = dist(s, v)` and, if `v ≠ s`, `x` is a
neighbour of `v` with `w(v,x) + dist(s,x) = dist(s,v)` (its parent in a shortest-path tree). -/
def SSSPSpec (N : WNet V) (s : V) (o : V → ℕ × V) : Prop :=
  ∀ v, (o v).1 = N.wdist s v ∧
    (v ≠ s → N.G.Adj v (o v).2 ∧ N.w s(v, (o v).2) + N.wdist s (o v).2 = N.wdist s v)

/-- APSP: every node `v` outputs, for every target `u`, the pair `(dist(v,u), nextHop)` where for
`u ≠ v` the next hop `x` is a neighbour of `v` on a shortest `v`–`u` path. This is the
distributed APSP problem of the paper ("each node learns its next hop and distance along a
shortest path to every other node"). -/
def APSPSpec (N : WNet V) (o : V → V → ℕ × V) : Prop :=
  ∀ v u, (o v u).1 = N.wdist v u ∧
    (u ≠ v → N.G.Adj v (o v u).2 ∧ N.w s(v, (o v u).2) + N.wdist (o v u).2 u = N.wdist v u)

/-- Solving SSSP from every source yields APSP (node `v`'s answer for target `u` is its output
in the SSSP instance rooted at `u`). -/
lemma apsp_of_sssp (N : WNet V) (o : V → V → ℕ × V)
    (h : ∀ s, SSSPSpec N s (fun v => o v s)) : APSPSpec N o := by
  intro v u
  obtain ⟨h1, h2⟩ := h u v
  refine ⟨by rw [h1, N.wdist_comm], fun hne => ?_⟩
  obtain ⟨ha, hw⟩ := h2 (Ne.symm hne)
  refine ⟨ha, ?_⟩
  rw [N.wdist_comm _ u, N.wdist_comm v u]; exact hw

end APSP
