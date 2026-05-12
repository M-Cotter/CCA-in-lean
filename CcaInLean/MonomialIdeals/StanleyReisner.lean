import CcaInLean.MonomialIdeals.Monomial
import CcaInLean.MonomialIdeals.MinimalGenerators
import CcaInLean.MonomialIdeals.SquareFree

import Mathlib

variable {σ R : Type*} [CommRing R] [Nontrivial R] [DecidableEq σ]

open MvPolynomial

namespace Monomial

def src (S : Set (Finset σ)) : PreAbstractSimplicialComplex σ where
  faces := {m : Finset σ | ¬(∃ s ∈ S, m ⊆ s)}
  isRelLowerSet_faces := sorry
