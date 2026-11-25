import ApspStoc.Toolkit

/-!
# Polylogarithmically bounded functions
-/

namespace APSP.Stoc
open APSP

/-- `f` is bounded by a polylogarithm: `f ν ≤ C · lg(ν)^k`. -/
def IsPL (f : ℕ → ℕ) : Prop := ∃ C k : ℕ, ∀ ν, f ν ≤ C * lg ν ^ k

namespace IsPL

lemma const (c : ℕ) : IsPL (fun _ => c) := ⟨c, 0, fun _ => by simp⟩

lemma lg' : IsPL lg := ⟨1, 1, fun _ => by simp⟩

lemma lgpow (k : ℕ) : IsPL (fun ν => lg ν ^ k) := ⟨1, k, fun _ => by simp⟩

lemma mono {f g : ℕ → ℕ} (hg : IsPL g) (h : ∀ ν, f ν ≤ g ν) : IsPL f := by
  obtain ⟨C, k, hC⟩ := hg; exact ⟨C, k, fun ν => (h ν).trans (hC ν)⟩

lemma add {f g : ℕ → ℕ} (hf : IsPL f) (hg : IsPL g) : IsPL (fun ν => f ν + g ν) := by
  obtain ⟨C, k, hC⟩ := hf; obtain ⟨C', k', hC'⟩ := hg
  refine ⟨C + C', max k k', fun ν => ?_⟩
  have h1 := lg_pow_le_pow_max_left ν k k'
  have h2 := lg_pow_le_pow_max_right ν k k'
  calc f ν + g ν ≤ C * lg ν ^ k + C' * lg ν ^ k' := Nat.add_le_add (hC ν) (hC' ν)
    _ ≤ C * lg ν ^ max k k' + C' * lg ν ^ max k k' :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (C + C') * lg ν ^ max k k' := by ring

lemma mul {f g : ℕ → ℕ} (hf : IsPL f) (hg : IsPL g) : IsPL (fun ν => f ν * g ν) := by
  obtain ⟨C, k, hC⟩ := hf; obtain ⟨C', k', hC'⟩ := hg
  refine ⟨C * C', k + k', fun ν => ?_⟩
  calc f ν * g ν ≤ (C * lg ν ^ k) * (C' * lg ν ^ k') := Nat.mul_le_mul (hC ν) (hC' ν)
    _ = C * C' * lg ν ^ (k + k') := by rw [pow_add]; ring

lemma pow {f : ℕ → ℕ} (hf : IsPL f) (m : ℕ) : IsPL (fun ν => f ν ^ m) := by
  induction m with
  | zero => simpa using const 1
  | succ m ih => simpa [pow_succ] using ih.mul hf

lemma smul {f : ℕ → ℕ} (hf : IsPL f) (c : ℕ) : IsPL (fun ν => c * f ν) := (const c).mul hf

/-- `lg (ν^(a+1)) ` is polylogarithmic. -/
lemma lg_pow_succ (a : ℕ) : IsPL (fun ν => lg (ν ^ (a + 1))) :=
  mono ((lg'.smul (a + 1)).add (const 1)) (fun ν => lg_pow_le ν (a + 1))

end IsPL

lemma lg_le_self {ν : ℕ} (h : 1 ≤ ν) : lg ν ≤ ν := by
  unfold lg
  have := Nat.log_lt_self 2 (show ν ≠ 0 by omega)
  omega

/-- Polylog factors are absorbed by one power of `ν`. -/
lemma IsPL.le_pow {f : ℕ → ℕ} (hf : IsPL f) : ∃ C k : ℕ, ∀ ν, 1 ≤ ν → f ν ≤ C * ν ^ k := by
  obtain ⟨C, k, hC⟩ := hf
  exact ⟨C, k, fun ν hν => (hC ν).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lg_le_self hν) _))⟩

end APSP.Stoc
