import ApspStoc.MainOf
import ApspStoc.Sec4
import ApspStoc.Sec5EO
import ApspStoc.Sec5a
import ApspStoc.Sec5b

/-!
# The main theorem of the STOC submission: Theorem 5.6 (= Theorem 1.1)

Assembly of the proofs: Lemma 4.2 (`Sec4.lean`), the physical case of Lemma 5.3 (`Sec5EO.lean`),
Lemma 5.3, Lemma 5.4 and MST on a subset (`Sec5a.lean`), Theorem 5.5 (`Sec5b.lean`), Theorems 3.3
and 3.10 (`Sec3.lean`, with Claims 3.4/3.5 proved in `G0.lean`) and Theorem 5.6 from Theorem 5.5
(`MainOf.lean`).
-/

namespace APSP.Stoc

open APSP Finset

/-- **Lemma 5.3**. -/
theorem lemma_5_3 (T : Toolkit) : Lemma_5_3 T := lemma_5_3_of T (lemma_4_2 T) (eo_physical T)

/-- **Lemma 5.4**. -/
theorem lemma_5_4 (T : Toolkit) : Lemma_5_4 T := lemma_5_4_of T (lemma_4_2 T) (lemma_5_3 T)

/-- MST / leader election on a subset. -/
theorem lemma_mst (T : Toolkit) : LemmaMST T := lemma_mst_of T (lemma_4_2 T)

/-- **Theorem 5.5** (message-optimal exact SSSP). -/
theorem thm_5_5 (T : Toolkit) : Thm_5_5 T := thm_5_5_of T (lemma_5_4 T) (lemma_mst T)

/-- **Theorem 5.6** (Near-Singularly Optimal (Exact) APSP): there is a randomized Monte-Carlo
distributed algorithm solving weighted undirected APSP in `Õ(n)` rounds and `Õ(n²)` messages
w.h.p. The hypotheses are the toolkit `T`, whose fields are standard CONGEST facts [STD],
theorems of prior work [PRIOR], one prior theorem in a strengthened form [PRIOR+] and
implementation assumptions for the paper's own steps [IMPL] (see `Toolkit.lean`), and `Mixing`
(the mixing bound for lazy random walks on expanders, a theorem of prior work). The statement is
a derivation relative to these hypotheses. -/
theorem thm_5_6 (T : Toolkit) (hmix : Mixing) (wexp c : ℕ) :
    ∃ (A : ℕ → T.Alg) (C k K : ℕ), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V),
      1 ≤ Fintype.card V → (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp) →
      ∃ (p : Prof V) (δ : ℝ),
        T.Impl (A (Fintype.card V)) N (.compute none (V → ℕ × V) (APSPSpec N)) p δ ∧
        p.rounds ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ∧
        p.msgs ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ^ 2 ∧
        δ ≤ (K : ℝ) / (Fintype.card V : ℝ) ^ c :=
  thm_5_6_of T hmix (thm_5_5 T) wexp c

/-- **Theorem 1.1** (= Theorem 5.6). -/
theorem thm_1_1 (T : Toolkit) (hmix : Mixing) (wexp c : ℕ) :
    ∃ (A : ℕ → T.Alg) (C k K : ℕ), ∀ {V : Type} [Fintype V] [DecidableEq V] (N : WNet V),
      1 ≤ Fintype.card V → (∀ e ∈ N.G.edgeSet, N.w e ≤ Fintype.card V ^ wexp) →
      ∃ (p : Prof V) (δ : ℝ),
        T.Impl (A (Fintype.card V)) N (.compute none (V → ℕ × V) (APSPSpec N)) p δ ∧
        p.rounds ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ∧
        p.msgs ≤ C * lg (Fintype.card V) ^ k * Fintype.card V ^ 2 ∧
        δ ≤ (K : ℝ) / (Fintype.card V : ℝ) ^ c :=
  thm_5_6 T hmix wexp c

end APSP.Stoc
