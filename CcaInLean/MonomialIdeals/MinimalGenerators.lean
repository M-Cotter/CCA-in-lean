import CcaInLean.MonomialIdeals.Monomial
import Mathlib

variable {σ R : Type*} [CommRing R] [Nontrivial R]

namespace Monomial
open MvPolynomial
open Monomial

theorem monomial_ideal_minimal_eq (s : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R {m | Minimal (· ∈ s) m} = MonomialIdeal σ R s := by
  apply le_antisymm
  · rw [← monomial_ideal_le_monomial_ideal]
    intro m ms
    use m
    exact ⟨Set.mem_of_mem_inter_left ms, Std.le_refl _⟩
  · rw [← Monomial.monomial_ideal_le_monomial_ideal]
    intro m ms
    let sm := {x ∈ s | x ≤ m}
    obtain ⟨a, ha⟩ := WellFounded.has_min (Finsupp.lt_wf σ) sm ⟨m, ms, le_refl _⟩
    use a
    rw [Set.mem_setOf_eq]
    constructor
    · constructor
      · exact ha.1.1
      · intro y hy hya
        by_contra
        apply ha.2 y
        · rw [Set.mem_setOf_eq]
          exact ⟨hy, le_trans hya ha.1.2⟩
        rcases eq_or_lt_of_le hya with heq | hle
        · by_contra h
          apply this
          rw [heq]
        · exact hle
    · exact ha.1.2

example : @WellFounded (σ →₀ ℕ) (· < ·) := by
  exact Finsupp.lt_wf σ

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
    Finset.card s1 ≤ Finset.card (Set.Finite.toFinset (minimal_finite s)) →
    s1 = {m | Minimal (· ∈ s) m} := by
  intro hMonoEq hCardLe
  rw [← monomial_ideal_minimal_eq] at hMonoEq
  rcases le_antisymm_iff.mp hMonoEq with ⟨h1, h2⟩
  rw [← monomial_ideal_le_monomial_ideal] at h1 h2
  let sf := Set.Finite.toFinset (minimal_finite s)
  rw [← Set.Finite.coe_toFinset (minimal_finite s), SetLike.coe_set_eq]
  symm
  apply (Finset.subset_iff_eq_of_card_le (hCardLe)).mp
  intro x hxsf
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Set.Finite.mem_toFinset] at h1 h2 hxsf
  rcases h1 x hxsf with ⟨a, b⟩
  rcases h2 a b.1 with ⟨c, d⟩
  have : c = x := by
    apply le_antisymm
    apply le_trans d.2 b.2
    apply hxsf.2 d.1.1 (le_trans d.2 b.2)
  have : a = x := by
    apply le_antisymm
    exact b.2
    rw [← this]
    exact d.2
  rw [← this]
  exact b.1

example [Finite σ] (s t : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R s = MonomialIdeal σ R t →
    {m | Minimal (· ∈ s) m} = {m | Minimal (· ∈ t) m} := by
  rw [← monomial_ideal_minimal_eq, ← monomial_ideal_eq_monomial_ideal]
  intro ⟨ha, hb⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h
  · rcases ha x h with ⟨a, b⟩
    rcases hb a b.1 with ⟨c, d⟩
    have : c = x := by
      apply le_antisymm
      apply le_trans d.2 b.2
      apply h.2 d.1.1 (le_trans d.2 b.2)
    have : a = x := by
      apply le_antisymm
      exact b.2
      rw [← this]
      exact d.2
    rw [← this]
    constructor
    exact b.1
    intro y hy hyy
    sorry
  · sorry

theorem minimal_union_subset_union_minimal (s t : Set (σ →₀ ℕ)) :
    {m | Minimal (· ∈ (s ∪ t)) m} ⊆
    {m | Minimal (· ∈ s) m} ∪ {m | Minimal (· ∈ t) m} := by
  intro x hx
  simp only [Set.mem_union, Set.mem_setOf_eq] at *
  exact Minimal.or hx

end Monomial
