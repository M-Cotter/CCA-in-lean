import CcaInLean.MonomialIdeals.Monomial
import Mathlib

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Nontrivial R]

theorem Monomial.MonomialIdeal_minimal_eq [Finite σ] (s : Set (σ →₀ ℕ)) :
    Monomial.MonomialIdeal σ R {m | Minimal (· ∈ s) m} = Monomial.MonomialIdeal σ R s := by
  apply le_antisymm
  · rw [← Monomial.monomial_ideal_le_monomial_ideal]
    intro m ms
    use m
    exact ⟨Set.mem_of_mem_inter_left ms, Std.le_refl _⟩
  · rw [← Monomial.monomial_ideal_le_monomial_ideal]
    intro m ms
    rcases Set.IsPWO.exists_le_minimal (Set.isPWO_of_wellQuasiOrderedLE s) ms with ⟨a, ha⟩
    use a
    simp only [Set.mem_setOf_eq, ha, and_self]

theorem Monomial.minimal_finite [Finite σ] (s : Set (σ →₀ ℕ)) :
    {m | Minimal (· ∈ s) m}.Finite := by
  have h : IsAntichain (· ≤ ·) {m | Minimal (· ∈ s) m} := by
    intro a ha b hb haneqb haleb
    simp only [minimal_iff, Set.mem_setOf_eq] at ha hb
    apply haneqb
    symm
    apply hb.2 ha.1 haleb
  exact WellQuasiOrderedLE.finite_of_isAntichain h
