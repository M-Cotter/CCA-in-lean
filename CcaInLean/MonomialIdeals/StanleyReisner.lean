import CcaInLean.MonomialIdeals.Monomial
import CcaInLean.MonomialIdeals.MinimalGenerators
import CcaInLean.MonomialIdeals.SquareFree

import Mathlib

variable {σ R : Type*} [CommRing R] [Nontrivial R] [DecidableEq σ]

open MvPolynomial

namespace Monomial

def src (S : Set (Finset σ)) : PreAbstractSimplicialComplex σ where
  faces := {m : Finset σ | ¬(∃ x ∈ S, x ⊆ m) ∧ m.Nonempty}
  isRelLowerSet_faces := by
    unfold IsRelLowerSet
    intro s hs
    constructor
    · exact hs.2
    · rintro b hbs hbn
      rw [Set.mem_setOf_eq]
      constructor
      · sorry
      · sorry


def sri (S : PreAbstractSimplicialComplex σ) :=
