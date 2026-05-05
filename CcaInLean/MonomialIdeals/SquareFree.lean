import CcaInLean.MonomialIdeals.Monomial
import Mathlib

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Nontrivial R]

open MvPolynomial
namespace Monomial

open Classical in
noncomputable
def SqFreeMonoOf : Finset σ → (σ →₀ ℕ) :=
  fun s ↦
    {
      support := s
      toFun := Set.indicator s (fun x ↦ 1)
      mem_support_toFun := by simp only [ne_eq, Set.indicator_apply_eq_zero, SetLike.mem_coe,
        one_ne_zero, imp_false, Decidable.not_not, implies_true]
    }

noncomputable
def SquareFreeIdeal (σ R : Type*) (S : Set (Finset σ))
    [CommRing R] [Nontrivial R] : Ideal (MvPolynomial σ R) :=
  MonomialIdeal σ R (SqFreeMonoOf '' S)

noncomputable
def MonoRoot (m : σ →₀ ℕ) : σ →₀ ℕ :=
  {
    support := m.support
    toFun := fun x ↦ if m x = 0 then 0 else 1
    mem_support_toFun := by simp only [Finsupp.mem_support_iff, ne_eq, ite_eq_left_iff, one_ne_zero,
      imp_false, Decidable.not_not, implies_true]
  }

theorem mono_root_mono_root (m : σ →₀ ℕ) :
    MonoRoot (MonoRoot m) = MonoRoot m := by
  unfold MonoRoot
  simp only [Finsupp.coe_mk, ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not]

example (s : Finset σ) :
    MonoRoot (SqFreeMonoOf s) = SqFreeMonoOf s := by
  unfold MonoRoot SqFreeMonoOf Set.indicator
  simp only [SetLike.mem_coe, Finsupp.coe_mk, ite_eq_right_iff, one_ne_zero, imp_false,
    Finsupp.mk.injEq, true_and]
  ext x
  grind only

example (S : Set (Finset σ)) : (SquareFreeIdeal σ R S).IsRadical := sorry

example (s : Set (σ →₀ ℕ)) :
    Ideal.radical (MonomialIdeal σ R s) = MonomialIdeal σ R (MonoRoot '' s) := by
  sorry

/-
This is a corollary of primary decomposition, but that requires a ring to be
Lasker/Noetherian. Maybe we can do better???
Directly by basis of every polynomial?
More generally this holds for graded rings
-/
