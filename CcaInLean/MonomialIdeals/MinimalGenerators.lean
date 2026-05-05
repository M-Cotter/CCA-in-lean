import CcaInLean.MonomialIdeals.Monomial
import Mathlib

variable {σ R : Type*} [CommRing R] [Nontrivial R]

namespace Monomial
open MvPolynomial
open Monomial

theorem monomial_ideal_minimal_eq [Finite σ] (s : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R {m | Minimal (· ∈ s) m} = MonomialIdeal σ R s := by
  apply le_antisymm
  · rw [← monomial_ideal_le_monomial_ideal]
    intro m ms
    use m
    exact ⟨Set.mem_of_mem_inter_left ms, Std.le_refl _⟩
  · rw [← Monomial.monomial_ideal_le_monomial_ideal]
    intro m ms
    rcases Set.IsPWO.exists_le_minimal (Set.isPWO_of_wellQuasiOrderedLE s) ms with ⟨a, ha⟩
    use a
    simp only [Set.mem_setOf_eq, ha, and_self]

theorem minimal_finite [Finite σ] (s : Set (σ →₀ ℕ)) :
    {m | Minimal (· ∈ s) m}.Finite := by
  have h : IsAntichain (· ≤ ·) {m | Minimal (· ∈ s) m} := by
    intro a ha b hb haneqb haleb
    simp only [minimal_iff, Set.mem_setOf_eq] at ha hb
    apply haneqb
    symm
    apply hb.2 ha.1 haleb
  exact WellQuasiOrderedLE.finite_of_isAntichain h

theorem minimal_unique [Finite σ] (s : Set (σ →₀ ℕ)) (s1 : Finset (σ →₀ ℕ)) :
    MonomialIdeal σ R s = MonomialIdeal σ R s1 →
    Finset.card (Set.Finite.toFinset (minimal_finite s)) ≤ Finset.card s1 →
    s1 = {m | Minimal (· ∈ s) m} := by
  intro hMonoEq hCardEq
  rw [← monomial_ideal_minimal_eq] at hMonoEq
  rcases le_antisymm_iff.mp hMonoEq with ⟨h1, h2⟩
  rw [← monomial_ideal_le_monomial_ideal] at h1 h2
  let sf := Set.Finite.toFinset (minimal_finite s)
  rw [← Set.Finite.coe_toFinset (minimal_finite s), SetLike.coe_set_eq]
  symm
  have : Finset.card s1 ≤ Finset.card sf := by sorry
  apply (Finset.subset_iff_eq_of_card_le (this)).mp
  intro x hxsf
  simp only [Set.mem_setOf_eq, SetLike.mem_coe] at h1 h2
  have : Minimal (· ∈ s) x := by sorry
  rcases h1 x this with ⟨a, b⟩
  have : x = a := sorry
  rw [this]
  exact b.1

theorem minimal_union_subset_union_minimal (s t : Set (σ →₀ ℕ)) :
    {m | Minimal (· ∈ (s ∪ t)) m} ⊆
    {m | Minimal (· ∈ s) m} ∪ {m | Minimal (· ∈ t) m} := by
  intro x hx
  simp only [Set.mem_union, Set.mem_setOf_eq] at *
  exact Minimal.or hx

example (s t : Set (σ →₀ ℕ)) :
    {m | Minimal (· ∈ {z | ∃ x ∈ s, ∃ y ∈ t, x + y = z}) m} ⊆
    {z | ∃ x y, Minimal (· ∈ s) x ∧ Minimal (· ∈ t) y ∧ x + y = z} := by
  sorry

end Monomial
