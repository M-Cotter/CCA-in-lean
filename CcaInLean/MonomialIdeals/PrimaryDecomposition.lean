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

def toVar (i : σ) := fun (j : σ) ↦ if i = j then 1 else 0

theorem monomial_ideal_prime_iff [NoZeroDivisors R] (s : Set (σ →₀ ℕ)) :
    Ideal.IsPrime (MonomialIdeal σ R s) ↔
    (∀ m : σ →₀ ℕ, Minimal (· ∈ s) m → ∃ (i : σ), m = toVar i) := by
  constructor <;> intro h
  · contrapose! h
    rcases h with ⟨a, ha⟩
    rw [Ideal.not_isPrime_iff]
    by_cases haOne : a = 0 -- The Monomial one, but the exp vector 0
    · left
      rw [← top_le_iff, ← Ideal.span_one]
      apply Ideal.span_mono
      rw [Set.one_subset]
      use a
      constructor
      · exact ha.1.1
      · rw [haOne]
        dsimp
    · right
      sorry
  · rw [@Ideal.isPrime_iff]
    sorry

end Monomial
