/-
Copyright (c) 2026 Matthew Cotter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Cotter
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Monomial Ideals

This file defines the basic structure of monomial ideals, in particular we related the
structure of monomials to that of their exponent vector.

# Main Definitions

# Main Results

# TODO

Maybe some of what's here could be more elegantly stated if we used LowerSet/UpperSets
instead.

Finite intersection of monomial ideals is a monomial ideal (already showed the intersection
of two is a monomial ideal).
-/

public section
noncomputable section

variable {σ R : Type*} [CommRing R] [Nontrivial R]

open MvPolynomial
namespace Monomial

/-- Coercion from Monomial to MvPolynomial in the obvious sense. -/
instance : Coe (σ →₀ ℕ) (MvPolynomial σ R) where
  coe x := monomial x 1

/-- Coercion preserves equality. -/
@[simp]
lemma coe_eq (a b : σ →₀ ℕ) :
    (a : MvPolynomial σ R) = b ↔ (a : σ →₀ ℕ) = b := by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, monomial_left_inj]

/-- Coercion preserves one. -/
@[simp]
lemma coe_one {R : Type*} [CommRing R] :
    (1 : MvPolynomial σ R) = (0 : σ →₀ ℕ) := by rfl

/-- Coercion is multiplcative. -/
lemma coe_add {R : Type*} [CommRing R] (a b : σ →₀ ℕ) :
   (a + b : σ →₀ ℕ) = (a : MvPolynomial σ R) * b := by
  rw [MvPolynomial.monomial_mul, one_mul]

/-- `a ≤ b` as maps to `ℕ` if and only if the `a ∣ b` as polynomials -/
lemma coe_dvd (a b : σ →₀ ℕ) :
    a ≤ b ↔ (a : MvPolynomial σ R) ∣ b := by
  rw [monomial_one_dvd_monomial_one]

/-- Support of coerced exponent vector is itself. -/
lemma coe_support (a : σ →₀ ℕ) :
    (a : MvPolynomial σ R).support = {a} := by
  rw [@support_monomial _ _ _ _ _ (Classical.propDecidable (1 = 0))]
  simp only [one_ne_zero, ↓reduceIte]

/-- Shorthand for existing mathlib monomial ideal. -/
abbrev MonomialIdeal (σ R : Type*) [CommRing R] [Nontrivial R]
  (s : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun exp ↦ monomial exp (1 : R)) '' s)

/-- Monomial ideal of the bottom of the lattice of subsets (empty set) is the bottom
  of the lattice of ideals, i.e. `(0)`. -/
@[simp]
lemma monomial_ideal_of_bot : MonomialIdeal σ R ⊥ = ⊥ := by
  simp only [Set.bot_eq_empty, Submodule.span_eq_bot, Set.image_empty, Set.mem_empty_iff_false,
    IsEmpty.forall_iff, implies_true]

@[simp]
lemma monomial_ideal_of_empty : MonomialIdeal σ R ∅ = ⊥ := by
  simp only [Submodule.span_eq_bot, Set.image_empty, Set.mem_empty_iff_false,
    IsEmpty.forall_iff, implies_true]

/-- Auxiliary lemma about ideal spans. States if you have a set `t` compose of multiples
  of elements of `s`, then the ideal `(t)` is contained in `(s)`. -/
lemma Ideal.span_le_span {R : Type*} [CommRing R] (s t : Set R) :
    (∀ x ∈ t, ∃ y ∈ s, y ∣ x) → Ideal.span t ≤ Ideal.span s := by
  rw [Ideal.span_le]
  intro hx a ha_mem_t
  rw [@SetLike.mem_coe]
  rcases (hx a ha_mem_t) with ⟨r, hrs, hr_dvd_a⟩
  apply Ideal.mem_of_dvd
  · exact hr_dvd_a
  · exact Submodule.mem_span_of_mem hrs

lemma mem_span_of_mem (s : Set (σ →₀ ℕ)) :
    ∀ x ∈ s, (x : MvPolynomial σ R) ∈ MonomialIdeal σ R s := by
  exact fun x hx ↦ Ideal.subset_span (Set.mem_image_of_mem _ hx)

lemma monomial_mem_monomial_ideal {r : R} (s : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ s) :
    (monomial m) r ∈ MonomialIdeal σ R s := by
  rw [MvPolynomial.monomial_eq]
  apply Ideal.mul_mem_left
  rw [← one_mul (m.prod fun n e ↦ X n ^ e), ← C_1, ← MvPolynomial.monomial_eq]
  exact mem_span_of_mem _ _ hm

/-- A monomial is in a monomial ideal if it is divisible by one of the elements. -/
theorem mem_monomial_ideal_iff (s : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) :
  (m : MvPolynomial σ R) ∈ MonomialIdeal σ R s ↔ ∃ n ∈ s, n ≤ m := by
  rw [mem_ideal_span_monomial_image]
  constructor <;> intro h
  · rw [@MvPolynomial.support_monomial _ _ _ _ _ (Classical.propDecidable (1 = 0))] at h
    simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton, forall_eq] at h
    exact h
  · intro xi hx
    have : xi = m := by
      rw [@MvPolynomial.support_monomial _ _ _ _ _ (Classical.propDecidable (1 = 0))] at hx
      simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hx
      exact hx
    rwa [this]

/-- For sets of monomial `s` and `t`, the ideal corresponding to `s` is contained in `t`
  if and only if each element of `s` divides an element of `t`. -/
theorem monomial_ideal_le_monomial_ideal (s t : Set (σ →₀ ℕ)) :
  (∀ m ∈ t, ∃ n ∈ s, n ≤ m) ↔ MonomialIdeal σ R t ≤ MonomialIdeal σ R s := by
  constructor <;> intro h
  · apply Ideal.span_le_span
    intro p hp
    rcases hp with ⟨a, b⟩
    rcases h a b.1 with ⟨c, d⟩
    use monomial c (1 : R)
    constructor
    · simp only [Set.mem_image, ne_eq, one_ne_zero, not_false_eq_true, monomial_left_inj,
      exists_eq_right]
      exact d.1
    · rw [← b.2, ← coe_dvd]
      exact d.2
  · intro m hm
    have : (m : MvPolynomial σ R) ∈ MonomialIdeal σ R s := by
      apply h
      rw [mem_monomial_ideal_iff]
      use m
    rcases (mem_monomial_ideal_iff s m).mp this with ⟨n, hn⟩
    use n

/-- Monomial ideals are equal if and only if their generators contain eachother. -/
theorem monomial_ideal_eq_monomial_ideal (s t : Set (σ →₀ ℕ)) :
    (∀ m ∈ t, ∃ n ∈ s, n ≤ m) ∧ (∀ n ∈ s, ∃ m ∈ t, m ≤ n) ↔
    MonomialIdeal σ R t = MonomialIdeal σ R s := by
  rw [le_antisymm_iff, ← monomial_ideal_le_monomial_ideal,
  ← monomial_ideal_le_monomial_ideal]

/-- Supremum of two monomial ideals is the monomial ideal of the union. -/
theorem sup_monomial_ideal (s t : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R s ⊔ MonomialIdeal σ R t = MonomialIdeal σ R (s ∪ t) := by
  rw [← Ideal.span_union, ← Set.image_union]

/-- Supremum of any number of monomial ideals is a monomial ideal of the union. -/
theorem iSup_monomial_ideal {ι : Type*} (p : ι → Set (σ →₀ ℕ)) :
    ⨆ i, MonomialIdeal σ R (p i) = MonomialIdeal σ R (⋃ i, p i) := by
  rw [← Ideal.span_iUnion, ← Set.image_iUnion]

/-- Support of a polynomial is in an ideal `I` implies the polynomial is in the `I`. -/
theorem aux {R : Type*} [CommRing R]
    {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (h : ∀ xi ∈ p.support, (xi : MvPolynomial σ R) ∈ I) : p ∈ I := by
  rw [← support_sum_monomial_coeff p]
  apply Ideal.sum_mem _ fun i hi ↦ ?_
  have : (monomial i) (coeff i p) = C (coeff i p) * (monomial i) (1 : R) := by
    rw [@C_mul_monomial, mul_one]
  rw [this]
  apply Ideal.mul_mem_left
  exact h i hi

/-- An ideal `I` is monomial if and only if it includes the support of all polynomials in `I`. -/
theorem monomial_ideal_iff_support_mem (I : Ideal (MvPolynomial σ R)) :
    (∃ (s : Set (σ →₀ ℕ)), I = MonomialIdeal σ R s) ↔
    ∀ p : I, ∀ xi ∈ p.1.support, (xi : MvPolynomial σ R) ∈ I := by
  constructor
  · intro ⟨s, hIs⟩
    rw [hIs]
    intro p xi hxi
    rw [mem_monomial_ideal_iff]
    have : p.1 ∈ MonomialIdeal σ R s := by
      simp only [SetLike.coe_mem]
    rw [mem_ideal_span_monomial_image] at this
    rcases this xi hxi with ⟨a, ha⟩
    use a
  · intro ha
    use {x | ∃ p : I, x ∈ p.1.support}
    ext a
    constructor <;> intro h
    · rw [mem_ideal_span_monomial_image]
      intro xi hxi
      use xi
      simp only [Std.le_refl, and_true]
      rw [@Set.mem_setOf_eq]
      use ⟨a, h⟩
    · suffices ∀ xi ∈ a.support, (xi : MvPolynomial σ R) ∈ I from aux this
      intro xi hxi
      rw [mem_ideal_span_monomial_image] at h
      rcases h xi hxi with ⟨d, hd⟩
      rcases hd.1 with ⟨e, he⟩
      have hd_dvd_xi : (d : MvPolynomial σ R) ∣ xi := by rw [← coe_dvd]; exact hd.2
      exact Ideal.mem_of_dvd I hd_dvd_xi (ha e d he)

/-- Infimum of two monomial ideals is a monomial ideal generated by the `lcm` of elements. -/
theorem inf_monomial_ideal (s t : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R s ⊓ MonomialIdeal σ R t =
    MonomialIdeal σ R {m | ∃ xs ∈ s, ∃ xt ∈ t, m = max xs xt} := by
  rw [le_antisymm_iff]
  constructor
  · intro x ⟨hxt, hxs⟩
    simp only [SetLike.mem_coe] at *
    rw [mem_ideal_span_monomial_image] at *
    intro xi hxi
    rcases hxt xi hxi with ⟨a, ha⟩
    rcases hxs xi hxi with ⟨b, hb⟩
    use a ⊔ b
    simp only [Set.mem_setOf_eq, sup_le_iff, ha.2, hb.2, and_true]
    exact ⟨a, ha.1, ⟨b, hb.1, rfl⟩⟩
  · rw [le_inf_iff]
    constructor <;> rw [← monomial_ideal_le_monomial_ideal]
    · intro m hm
      rcases hm with ⟨n, hns, l, hl⟩
      use n
      rw [hl.2]
      exact ⟨hns, le_sup_left⟩
    · intro m hm
      rcases hm with ⟨n, hns, l, hl⟩
      use l
      rw [hl.2]
      exact ⟨hl.1, le_sup_right⟩

/-- Product of two monomial ideals is generated by the product of generators. -/
theorem mul_monomial_ideal (s t : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R s * MonomialIdeal σ R t =
    MonomialIdeal σ R {z | ∃ x ∈ s, ∃ y ∈ t, x + y = z} := by
  rw [Ideal.span_mul_span']
  congr
  ext x
  rw [Set.mem_mul]
  simp only [Set.mem_image, exists_exists_and_eq_and, monomial_mul, mul_one, Set.mem_setOf_eq,
    exists_exists_and_exists_and_eq_and]

end Monomial
