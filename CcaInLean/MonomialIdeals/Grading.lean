import CcaInLean.MonomialIdeals.Monomial
import CcaInLean.MonomialIdeals.MinimalGenerators
import Mathlib
variable {σ R : Type*} [CommRing R] [Nontrivial R] [DecidableEq σ] [Field k]

open MvPolynomial
namespace Monomial

theorem monomial_ideal_homogeneous [DecidableEq R] (s : Set (σ →₀ ℕ)) :
    Ideal.IsHomogeneous (AddMonoidAlgebra.grade R) (MonomialIdeal σ R s) := by
  rw [Ideal.IsHomogeneous.iff_exists]
  use {x | ∃ m ∈ s,
    x = ⟨monomial m (1 : R), by
      use m
      intro n hn
      rw [MvPolynomial.finsupp_support_eq_support, MvPolynomial.support_monomial] at hn
      simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hn
      rwa [id]⟩}
  unfold MonomialIdeal
  congr
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Subtype.mk.injEq, exists_and_left,
    exists_prop, exists_eq_right_right]
  constructor <;> intro h
  · constructor
    · tauto
    · rcases h with ⟨a, ha⟩
      use a
      simp only [Submodule.mem_mk, id_eq, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      intro n hn
      rw [MvPolynomial.finsupp_support_eq_support, ← ha.2, MvPolynomial.support_monomial] at hn
      simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hn
      exact hn
  · tauto


lemma monomial_mem_monomial_ideal (s : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ s):
    (monomial m) r ∈ MonomialIdeal σ R s := by
  sorry

open Classical in
theorem homogeneous_implies_monomial_ideal {k : Type*} [Field k] (I : Ideal (MvPolynomial σ k)) :
    Ideal.IsHomogeneous (AddMonoidAlgebra.grade k) I →
    ∃ (s : Set (σ →₀ ℕ)), I = MonomialIdeal σ k s := by
  intro hHomI
  rcases (Ideal.IsHomogeneous.iff_exists _ _).mp hHomI with ⟨A, hA⟩
  unfold SetLike.homogeneousSubmonoid at A
  unfold SetLike.IsHomogeneousElem at A
  have : ∀ a ∈ A, ∃ (i : σ →₀ ℕ), ∃ (r : k),
    a.1 ≠ 0 → r ≠ 0 ∧ a = monomial i r := by
    intro a ha
    rcases a.2 with ⟨b, hb⟩
    simp only [Submodule.mem_mk, id_eq, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hb
    use b, (a.1 b)
    intro haneqzero
    have : a.1 = (monomial b) (a.1 b) := by
      ext x
      simp only [coeff_monomial]
      by_cases h : b = x
      · simp only [h, ↓reduceIte]
        rfl
      · simp only [h, ↓reduceIte, Finsupp.mem_support_iff] at hb ⊢
        apply byContradiction (fun b ↦ by apply h; rwa [hb x])
    exact ⟨fun hab ↦ by apply haneqzero; rw [this, hab, MvPolynomial.monomial_eq_zero], this⟩
  let B := {m : σ →₀ ℕ | ∃ a ∈ A, ∃ r : k, r ≠ 0 ∧ a = monomial m r}
  use B
  rw [hA]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    rcases hx with ⟨a, ha⟩
    rw [← ha.2]
    rcases this a ha.1 with ⟨c, r, hc⟩
    by_cases h : a.1 = 0
    · rw [h, SetLike.mem_coe]
      apply Ideal.zero_mem
    rw [(hc h).2, SetLike.mem_coe]
    apply monomial_mem_monomial_ideal
    · exact ⟨a, ha.1, r, hc h⟩
  · rw [Ideal.span_le]
    intro m hm
    rcases hm with ⟨a, ha⟩
    rw [← ha.2]
    simp only [SetLike.mem_coe]
    rcases ha.1 with ⟨c, hcA, d, hd⟩
    apply Ideal.span_mono
    · change {c.1} ⊆ Subtype.val '' A
      simpa only [Set.singleton_subset_iff, Set.mem_image, SetLike.coe_eq_coe, exists_eq_right,
        ne_eq, Subtype.forall, Submodule.mem_mk, Finsupp.mem_support_iff, id_eq,
        AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
        Submonoid.mem_mk, Subsemigroup.mem_mk, forall_exists_index]
    · rw [← Ideal.submodule_span_eq, Submodule.mem_span_singleton]
      use C d⁻¹
      rw [hd.2, monomial_eq, smul_eq_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀]
      · rw [← monomial_eq]
      · exact hd.1
