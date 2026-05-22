
/-
import CcaInLean.MonomialIdeals.Monomial
import Mathlib

variable {σ R : Type*} [CommRing R] [Nontrivial R] [DecidableEq σ]


namespace Newton
open MvPolynomial

set_option linter.unusedDecidableInType false
theorem pow_support (p : MvPolynomial σ R) (n : ℕ) :
    (p ^ n).support ≤
    {x : σ →₀ ℕ | ∃ f : Fin n → (σ →₀ ℕ), (∀ i, f i ∈ p.support) ∧ ∑ i, f i = x} := by
  induction n with
  | zero =>
    rw [pow_zero, support_one]
    intro xi hxi
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hxi
    simp only [IsEmpty.forall_iff, Finset.univ_eq_empty, Finset.sum_empty,
      true_and, exists_const, Set.setOf_eq_eq_singleton', hxi, Set.mem_singleton_iff]
  | succ k hk =>
    intro xi hxi
    rw [Set.mem_setOf_eq]
    rw [pow_succ] at hxi
    apply support_mul at hxi
    rw [Finset.mem_add] at hxi
    rcases hxi with ⟨a, ha, b, hb, hab⟩
    rcases hk ha with ⟨f, hf⟩
    use Fin.snoc f b
    constructor
    · intro i
      cases i using Fin.lastCases
      · rwa [Fin.snoc_last]
      · rw [Fin.snoc_castSucc]
        exact hf.1 _
    · rw [@Fin.sum_snoc, hf.2, hab]

example (p q : MvPolynomial σ R) (n : ℕ)
    (mp : σ →₀ ℕ) (hmp : Minimal (· ∈ p.support) mp) :
    ∀ xi ∈ (p ^ 2).support, xi ≤ mp + mp → mp + mp ≤ xi := by
  intro xi hxi hxi2
  rw [pow_two] at hxi
  apply support_mul at hxi
  rcases Finset.mem_add.mp hxi with ⟨ma, hma, mb, hmb, hab⟩
  rw [← hab]



example (p : MvPolynomial σ R)
    (m : σ →₀ ℕ) (hm : Minimal (· ∈ p.support) m) (n : ℕ) :
    ∀ xi ∈ (p ^ n).support, n • m ≥ xi → n • m ≤ xi := by
  induction n with
  | zero => sorry
  | succ k hk =>
    intro pi hpi hksucc
    rw [pow_succ] at hpi
    apply support_mul at hpi
    rcases Finset.mem_add.mp hpi with ⟨m1, hm1, m2, hm2, hadd⟩
    by_cases h : k • m ≥ m1
    sorry
    sorry


example (p : MvPolynomial σ R)
    (m : σ →₀ ℕ) (hm : Minimal (· ∈ p.support) m) (n : ℕ) :
    (coeff m p) ^ n = coeff (n • m) (p ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, pow_zero, coeff_one, if_pos]
    rfl
  | succ k hk =>
    rw [pow_succ p, coeff_mul]
    have : {⟨k • m, m⟩} ⊆ Finset.antidiagonal ((k + 1) • m) := by
      rw [Finset.singleton_subset_iff, Finset.mem_antidiagonal, add_smul, one_smul]
    rw [← Finset.sum_subset this ?_, Finset.sum_singleton, pow_succ, hk]
    intro x hx hj
    rw [Finset.mem_antidiagonal] at hx
    have : x.1 ≤ k • m ∨ x.2 ≤ m := by sorry
    sorry




example [IsReduced R] (p : MvPolynomial σ R)
    (m : σ →₀ ℕ) (hm : Minimal (· ∈ p.support) m) (n : ℕ) :
    (n • m) ∈ (p ^ n).support := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero, support_one, Finset.mem_singleton]
  | succ k hk =>
    rw [pow_succ, AddMonoidAlgebra.mul_def, ← finsupp_support_eq_support]
    simp only [Finsupp.mem_support_iff]
    sorry

end Newton
-/
