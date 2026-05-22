/-
import CcaInLean.MonomialIdeal
import Mathlib

noncomputable section

variable {σ R : Type*} [CommRing R] [Nontrivial R]

/- Type of all square free monomials over `σ` -/
def squareFreeMonomial (σ : Type*) := {m : Monomial σ // ∀ x : σ, m x ≤ 1}

/- One, as a square free monomial subtype -/
def squareFreeMonomial.one : squareFreeMonomial σ :=
  ⟨Monomial.one σ, by intro x; simp only [Finsupp.coe_mk, zero_le]⟩

/- Two square free monomials are equal iff their values are (subtype triviality) -/
@[simp]
lemma sfmono_eq_iff_mon_eq (m n : squareFreeMonomial σ) : m = n ↔ m.val = n.val := by
  constructor <;> intro h
  · congr
  · exact Subtype.ext h

/- Mapping from a Finset of `σ` to a square free monomial, which is just the product of
  all elements over `σ →₀ ℕ` -/
open Classical in
def s : Finset σ → squareFreeMonomial σ :=
  fun S : Finset σ ↦
    ⟨
      {
        support := S
        toFun := fun s ↦ if s ∈ S then 1 else 0
        mem_support_toFun :=
          fun _ ↦ ⟨fun as ↦
            by simpa only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
              Decidable.not_not],
            by simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
              Decidable.not_not, imp_self]⟩
      },
    by
    intro x
    rw [Finsupp.coe_mk]
    by_cases h : x ∈ S
    · rw [if_pos h]
    · rw [if_neg h]
      norm_num
    ⟩

#check Finsupp.indicator
/-
def s1 : Finset σ → squareFreeMonomial σ :=
  fun S : Finset σ ↦
  ⟨
    {
      support := ⊥
      toFun := Finsupp.indicator
      mem_support_toFun := sorry
    },
    sorry
  ⟩
-/

/- Subtype then monomial coercion for squareFreeMonomials -/
instance : Coe (squareFreeMonomial σ) (MvPolynomial σ R) where
  coe x := MvPolynomial.monomial x.val 1

/- Support is definitionally the set for `s`. -/
@[simp]
lemma s_support_eq (S : Finset σ) : (s S).1.support = S := rfl

@[simp]
lemma s_eq_toFun (S : Finset σ) : (s S).1 = (s S).1.toFun := rfl

open Classical in
@[simp]
lemma s_to_fun_eq_fun (S : Finset σ) : (s S).1.toFun = fun w ↦ if w ∈ S then 1 else 0 := rfl

@[simp]
lemma s_eq_one_iff (S : Finset σ) (x : σ) : (s S).1 x = 1 ↔ x ∈ S := by
  simp only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_left_iff, zero_ne_one, imp_false, not_not]

@[simp]
lemma s_eq_zero_iff (S : Finset σ) (x : σ) : (s S).1 x = 0 ↔ x ∉ S := by
  simp only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_right_iff, one_ne_zero, imp_false]

@[simp]
lemma s_eq_zero_or_one (S : Finset σ) (x : σ) : (s S).1 x = 0 ∨ (s S).1 x = 1 := by
  simp only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff,
    zero_ne_one, not_not]
  exact em' _

@[simp]
lemma s_eq_iff_supp_eq (A B : Finset σ) : s A = s B ↔ A = B := by
  constructor <;> intro h
  · ext x
    constructor <;> intro hab
    · rwa [← s_eq_one_iff _, ← h, s_eq_one_iff]
    · rwa [← s_eq_one_iff _, h, s_eq_one_iff]
  · congr

/- Squarefree monomials divide if and only if their underlying subsets are contained. -/
lemma sfmono_dvd_iff_sub (m m' : squareFreeMonomial σ) :
  (m : MvPolynomial σ R) ∣ m' ↔ m.val ≤ m'.val := by
  rw [MvPolynomial.monomial_dvd_monomial]
  sorry

structure SquareFreeMonomialIdeal (σ R : Type*) [CommRing R] [Nontrivial R] where
  basis : Set (squareFreeMonomial σ)
  one_nelem : squareFreeMonomial.one ∉ basis

def SquareFreeMonomialIdeal.ideal (I : SquareFreeMonomialIdeal σ R) :=
  Ideal.span {m : MvPolynomial σ R | ∃ (i : I.basis), m = i}


theorem poly_supp_in_ideal_iff_monomial (I : Ideal (MvPolynomial σ R)) :
    ∃ (S : Set (σ →₀ ℕ)),
      I = Ideal.span {m : MvPolynomial σ R | ∃ (i : S), m = i}
    ↔ ∀ (p : MvPolynomial σ R), ∀ (m : p.support), (m : MvPolynomial) ∈ I := by
  sorry
-/
