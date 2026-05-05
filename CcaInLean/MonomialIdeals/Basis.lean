import CcaInLean.MonomialIdeals.Monomial
import Mathlib

noncomputable section

variable {σ R : Type*} [CommRing R] [Nontrivial R]

namespace Monomial

/- Auxiliary lemma that monomials are linearly independent on an ideal. -/
lemma monoms_lin_indep_on_ideal {R : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R)) :
    LinearIndepOn R (fun (m : σ →₀ ℕ) ↦ MvPolynomial.monomial m (1 : R))
  ({m | MvPolynomial.monomial m (1 : R) ∈ I}) := by
  apply @LinearIndepOn.mono
  · refine LinearIndependent.linearIndepOn ?_ fun x ↦ True
    exact Module.Basis.linearIndependent (MvPolynomial.basisMonomials σ R)
  · exact Set.setOf_subset.mpr fun x a ↦ trivial

/- Monomials are linearly independent on a monomial ideal -/
theorem monoms_lin_indep_monomial_ideal
  (σ R : Type*) (s : Set (σ →₀ ℕ)) [CommRing R] [Nontrivial R] :
    LinearIndependent R
    fun x : {m : σ →₀ ℕ // MvPolynomial.monomial m (1 : R) ∈ MonomialIdeal σ R s}
      ↦ (⟨monomial x.1 (1 : R), x.2⟩ : MonomialIdeal σ R s) := by
    have h1 := LinearIndepOn.linearIndependent (monoms_lin_indep_on_ideal (MonomialIdeal σ R s))
    simp only [Set.coe_setOf, Set.mem_setOf_eq] at *
    sorry

/- Monomial basis on a monomial ideal-/
def MonomialsBasisMonIdeal (s : Set (σ →₀ ℕ)) :
    Module.Basis {m : σ →₀ ℕ // monomial m (1 : R) ∈ MonomialIdeal σ R s}
    R (MonomialIdeal σ R s) := by
  refine @Module.Basis.mk _ _ _ _ _ _ ?_ ?_ ?_
  · exact fun x ↦ ⟨monomial x (1 : R), x.2⟩
  · exact monoms_lin_indep_monomial_ideal _ _ _
  · intro p _
    have peq : p.1 = ∑ v ∈ p.1.support, (monomial v) (coeff v p) := by
      simp only [support_sum_monomial_coeff]
    have : p.1 ∈ MonomialIdeal σ R s := sorry
    rw [mem_ideal_span_monomial_image] at this
    rw [Finsupp.mem_span_iff_linearCombination]
    use sorry
    sorry

end Monomial
end MvPolynomial
