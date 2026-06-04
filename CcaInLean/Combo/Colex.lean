import CcaInLean.Combo.Cascade
import Mathlib.Order.Lex
import Mathlib.Combinatorics.Colex

#check Finset.Colex.toColex_le_toColex

namespace Finset.Colex

#check Finset.sort

example {n : ℕ} {f g : Fin (n + 1) → ℕ} (hf : StrictMono f) (hg : StrictMono g) :
    toColex (Finset.image f ⊤) ≤ toColex (Finset.image g ⊤) ↔
    f (Fin.last n) < g (Fin.last n) ∨
    f (Fin.last n) = g (Fin.last n) ∧
    toColex (Finset.image (Fin.init f) ⊤) ≤ toColex (Finset.image (Fin.init g) ⊤) := by
  constructor
  · intro h
    rw [toColex_le_toColex_iff_max'_mem]
    rw [toColex_le_toColex_iff_max'_mem] at h
    sorry
  · sorry
