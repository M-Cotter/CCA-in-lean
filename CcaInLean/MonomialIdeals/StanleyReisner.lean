/-
Copyright (c) 2026 Matthew Cotter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Cotter
-/

import CcaInLean.MonomialIdeals.Monomial
import CcaInLean.MonomialIdeals.MinimalGenerators
import CcaInLean.MonomialIdeals.SquareFree

variable {σ R : Type*} [CommRing R] [Nontrivial R] [DecidableEq σ]

open MvPolynomial
namespace Monomial

def ComplexOfIdeal (S : Set (Finset σ)) : LowerSet (Finset σ) where
  carrier := {m : Finset σ | ¬(∃ x ∈ S, x ≤ m)}
  lower' := fun _ _ hst ha ⟨x, hx⟩ ↦ ha ⟨x, hx.1, le_trans hx.2 hst⟩

theorem mem_complex_of_faces_iff (S : Set (Finset σ)) (s : Finset σ) :
    s ∈ ComplexOfIdeal S ↔
    (SqFreeMono s : MvPolynomial σ R) ∉ SquareFreeIdeal σ R S := by
  unfold ComplexOfIdeal
  simp only [LowerSet.mem_mk, Set.mem_setOf_eq]
  rw [not_iff_not, ← sq_free_mono_mem_iff]

example (S : Set (Finset σ)) :
  SquareFreeIdeal σ R (ComplexOfIdeal S).carrierᶜ = SquareFreeIdeal σ R S := by
  rw [sq_free_mono_ideal_eq_iff]
  unfold ComplexOfIdeal
  simp only [Finset.le_eq_subset, not_exists, not_and, Set.mem_compl_iff, Set.mem_setOf_eq,
    not_forall, Decidable.not_not]
  constructor
  · exact fun _ ⟨b, hbs, hb⟩ ↦ ⟨b, hbs, hb⟩
  · exact fun t ht ↦ ⟨t, ⟨t, ht, subset_refl t⟩, subset_refl t⟩

def AlexDual [Fintype σ] (Δ : LowerSet (Finset σ)) : LowerSet (Finset σ) where
  carrier := {F | (⊤ \ F) ∉ Δ.carrier}
  lower' := by
    intro s t hst hs
    rw [LowerSet.carrier_eq_coe, Set.mem_setOf_eq, SetLike.mem_coe] at hs ⊢
    contrapose hs
    exact Δ.lower' (sdiff_le_sdiff (le_refl _) hst) hs

end Monomial
