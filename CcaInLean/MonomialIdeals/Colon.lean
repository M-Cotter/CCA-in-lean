import CcaInLean.MonomialIdeals.Monomial
import CcaInLean.MonomialIdeals.MinimalGenerators
import Mathlib

variable {σ R : Type*} [CommRing R] [Nontrivial R]

open MvPolynomial
open Monomial
namespace Monomial

theorem colon_eq_inf_minimal_colon [Finite σ] (s t : Set (σ →₀ ℕ)) :
    Submodule.colon (MonomialIdeal σ R s) (MonomialIdeal σ R t) =
    ⨅ v ∈ {m | Minimal (· ∈ t) m},
    Submodule.colon (MonomialIdeal σ R s) (MonomialIdeal σ R {v}) := by
  nth_rw 2 [← monomial_ideal_minimal_eq]
  ext x
  simp only [Submodule.colon_span, Set.mem_setOf_eq, Set.image_singleton, Submodule.mem_iInf,
    Submodule.mem_colon_singleton, smul_eq_mul]
  rw [Submodule.mem_colon]
  simp only [Set.mem_image, smul_eq_mul, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor <;> exact fun h m hm ↦ h m hm

end Monomial
