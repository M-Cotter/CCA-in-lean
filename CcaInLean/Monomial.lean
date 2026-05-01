import Mathlib

noncomputable section

variable {σ R : Type*} [CommRing R] [Nontrivial R]

#check Module.Basis

namespace MvPolynomial

/- Coercion from Monomial to MvPolynomial in the obvious sense -/
instance : Coe (σ →₀ ℕ) (MvPolynomial σ R) where
  coe x := MvPolynomial.monomial x 1

/- Coercion preserves equality. -/
@[simp]
lemma Monomial.coe_eq (a b : σ →₀ ℕ) :
    (a : MvPolynomial σ R) = b ↔ (a : σ →₀ ℕ) = b := by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, monomial_left_inj]

/- Coercion preserves one -/
@[simp]
lemma Monomial.coe_one {R : Type*} [CommRing R] :
    (1 : MvPolynomial σ R) = (0 : σ →₀ ℕ) := by rfl

/- Coercion is multiplcative -/
lemma Monomial.coe_add {R : Type*} [CommRing R] (a b : σ →₀ ℕ) :
   (a + b : σ →₀ ℕ) = (a : MvPolynomial σ R) * b := by
  rw [@MvPolynomial.monomial_mul, one_mul]

/- `a ≤ b` as maps to `ℕ` if and only if the `a ∣ b` as polynomials -/
lemma Monomial.coe_dvd (a b : σ →₀ ℕ) :
    a ≤ b ↔ (a : MvPolynomial σ R) ∣ b := by
  rw [MvPolynomial.monomial_one_dvd_monomial_one]

/- Shorthand for existing mathlib monomial ideal -/
abbrev MonomialIdeal (σ R : Type*) [CommRing R] [Nontrivial R]
  (s : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun exp ↦ monomial exp (1 : R)) '' s)

/- Auxiliary lemma that monomials are linearly independent on an ideal. -/
lemma monoms_lin_indep_on_ideal (I : Ideal (MvPolynomial σ R)) :
    LinearIndepOn R (fun (m : σ →₀ ℕ) ↦ monomial m (1 : R))
  ({m | monomial m (1 : R) ∈ I}) := by
  apply @LinearIndepOn.mono
  · refine LinearIndependent.linearIndepOn ?_ fun x ↦ True
    have := Module.Basis.linearIndependent (MvPolynomial.basisMonomials σ R)
    simpa only
  · exact Set.setOf_subset.mpr fun x a ↦ trivial

/- Monomials are linearly independent on a monomial ideal -/
theorem monoms_lin_indep_monomial_ideal
  (σ R : Type*) (s : Set (σ →₀ ℕ)) [CommRing R] [Nontrivial R] :
    LinearIndependent R
    fun x : {m : σ →₀ ℕ // monomial m (1 : R) ∈ MonomialIdeal σ R s}
      ↦ (⟨monomial x.1 (1 : R), x.2⟩ : MonomialIdeal σ R s) := by
    have h1 := LinearIndepOn.linearIndependent (monoms_lin_indep_on_ideal (MonomialIdeal σ R s))
    simp only [Set.coe_setOf, Set.mem_setOf_eq] at *
    sorry

/- Already in Mathlib -/
example (s : Set (σ →₀ ℕ)) (x : MvPolynomial σ R) :
    x ∈ MonomialIdeal σ R s ↔ ∀ xi ∈ x.support, ∃ si ∈ s, si ≤ xi :=
  mem_ideal_span_monomial_image

/- Monomial basis on a monomial ideal-/
def MonomialsBasisMonIdeal (s : Set (σ →₀ ℕ)) :
    Module.Basis {m : σ →₀ ℕ // monomial m (1 : R) ∈ MonomialIdeal σ R s}
    R (MonomialIdeal σ R s) := by
  refine @Module.Basis.mk _ _ _ _ _ _ ?_ ?_ ?_
  · exact fun x ↦ ⟨monomial x (1 : R), x.2⟩
  · exact monoms_lin_indep_monomial_ideal _ _ _
  · intro p _
    have : p.1 = ∑ v ∈ p.1.support, (monomial v) (coeff v p) := by
      simp only [support_sum_monomial_coeff]
    rw [@Finsupp.mem_span_iff_linearCombination]
    sorry

/- Exists finite monomial spanning set of any monomial ideal -/
example (s : Set (σ →₀ ℕ)) (I : MonomialIdeal σ R s) :
    ∃ (t : Finset (σ →₀ ℕ)), I =
  Ideal.span ((fun exp ↦ monomial exp (1 : R)) '' (t : Set (σ →₀ ℕ))) := sorry


end MvPolynomial
