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

# YOUR CODE SUCKS

Coercion is redundant, remove it. You have to type `(m : MvPolynomial σ R)` anyway.
-/

public section
noncomputable section

variable {σ R : Type*} [CommRing R] [Nontrivial R]

open MvPolynomial
namespace Monomial

/-- Shorthand for existing mathlib monomial ideal. -/
abbrev MonomialIdeal (σ R : Type*) [CommRing R] [Nontrivial R]
  (s : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun exp ↦ monomial exp (1 : R)) '' s)

/-- Monomial ideal of the bottom of the lattice of subsets (empty set) is the bottom
  of the lattice of ideals, i.e. `(0)`. -/
@[simp]
lemma monomial_ideal_of_bot : MonomialIdeal σ R ⊥ = ⊥ := by simp

@[simp]
lemma monomial_ideal_of_empty : MonomialIdeal σ R ∅ = ⊥ := by simp

/-- Auxiliary lemma about ideal spans. States if you have a set `t` compose of multiples
  of elements of `s`, then the ideal `(t)` is contained in `(s)`. -/
lemma Ideal.span_le_span {R : Type*} [CommRing R] (s t : Set R) (hx : ∀ x ∈ t, ∃ y ∈ s, y ∣ x) :
    Ideal.span t ≤ Ideal.span s := by
  rw [Ideal.span_le]
  intro a hat
  rcases (hx a hat) with ⟨r, hrs, hra⟩
  exact Ideal.mem_of_dvd _ hra (Submodule.mem_span_of_mem hrs)

lemma mem_span_of_mem (s : Set (σ →₀ ℕ)) :
    ∀ x ∈ s, monomial x 1 ∈ MonomialIdeal σ R s :=
  fun _ hx ↦ Ideal.subset_span (Set.mem_image_of_mem _ hx)

lemma monomial_mem_monomial_ideal {r : R} (s : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ s) :
    (monomial m) r ∈ MonomialIdeal σ R s := by
  rw [MvPolynomial.monomial_eq]
  apply Ideal.mul_mem_left
  rw [← one_mul (m.prod fun n e ↦ X n ^ e), ← C_1, ← MvPolynomial.monomial_eq]
  exact mem_span_of_mem _ _ hm

open Classical in
/-- A monomial is in a monomial ideal if it is divisible by one of the elements. -/
theorem mem_monomial_ideal_iff {s : Set (σ →₀ ℕ)} {m : σ →₀ ℕ} :
  monomial m 1 ∈ MonomialIdeal σ R s ↔ ∃ n ∈ s, n ≤ m := by
  rw [mem_ideal_span_monomial_image]
  constructor <;> intro h
  · simp [MvPolynomial.support_monomial] at h
    assumption
  · intro xi hx
    rwa [show xi = m by simp [MvPolynomial.support_monomial] at hx; assumption]

/-- For sets of monomial `s` and `t`, the ideal corresponding to `s` is contained in `t`
  if and only if each element of `s` divides an element of `t`. -/
theorem monomial_ideal_le_monomial_ideal {s t : Set (σ →₀ ℕ)} :
  (∀ m ∈ t, ∃ n ∈ s, n ≤ m) ↔ MonomialIdeal σ R t ≤ MonomialIdeal σ R s := by
  constructor <;> intro h
  · apply Ideal.span_le_span
    intro p ⟨a, hat, hap⟩
    obtain ⟨c, hcs, hca⟩ := h a hat
    use monomial c (1 : R)
    constructor
    · simpa
    · rwa [← hap, monomial_one_dvd_monomial_one]
  · intro m hm
    obtain ⟨n, hn⟩ := mem_monomial_ideal_iff.mp
      (h (mem_monomial_ideal_iff.mpr ⟨m, hm, le_refl _⟩))
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
theorem support_mem_mem {R : Type*} [CommRing R]
    {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (h : ∀ xi ∈ p.support, monomial xi 1 ∈ I) : p ∈ I := by
  rw [← support_sum_monomial_coeff p]
  apply Ideal.sum_mem _ fun i hi ↦ ?_
  rw [show (monomial i) (coeff i p) = C (coeff i p) * (monomial i) (1 : R) by
    rw [@C_mul_monomial, mul_one]]
  exact Ideal.mul_mem_left _ _ (h i hi)

/-- An ideal `I` is monomial if and only if it includes the support of all polynomials in `I`. -/
theorem monomial_ideal_iff_support_mem (I : Ideal (MvPolynomial σ R)) :
    (∃ (s : Set (σ →₀ ℕ)), I = MonomialIdeal σ R s) ↔
    ∀ p ∈ I, ∀ xi ∈ p.support, monomial xi 1 ∈ I := by
  constructor
  · intro ⟨s, hIs⟩ p hp xi hxi
    rw [hIs] at hp ⊢
    exact mem_monomial_ideal_iff.mpr <| mem_ideal_span_monomial_image.mp hp _ hxi
  · intro ha
    use {x | ∃ p ∈ I, x ∈ p.support}
    ext a
    constructor <;> intro ha1
    · rw [mem_ideal_span_monomial_image]
      intro xi hxi
      use xi
      simp only [le_refl, and_true, Set.mem_setOf_eq]
      use a
    · suffices ∀ xi ∈ a.support, monomial xi 1 ∈ I from support_mem_mem this
      intro xi hxi
      apply mem_ideal_span_monomial_image.mp ha1 at hxi
      obtain ⟨yi, ⟨b, hbI, hyib⟩, hyi⟩ := hxi
      apply Ideal.mem_of_dvd
      · change monomial yi 1 ∣ monomial xi 1
        rwa [monomial_one_dvd_monomial_one]
      · exact ha _ hbI _ hyib

/-- Infimum of two monomial ideals is a monomial ideal generated by the `max` (lcm) of elements. -/
theorem inf_monomial_ideal (s t : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R s ⊓ MonomialIdeal σ R t =
    MonomialIdeal σ R {m | ∃ xs ∈ s, ∃ xt ∈ t, m = max xs xt} := by
  rw [le_antisymm_iff]
  constructor
  · intro x ⟨hxt, hxs⟩
    simp only [SetLike.mem_coe, mem_ideal_span_monomial_image] at *
    intro xi hxi
    obtain ⟨a, ha⟩ := hxt xi hxi
    obtain ⟨b, hb⟩ := hxs xi hxi
    use a ⊔ b
    simp only [Set.mem_setOf_eq, sup_le_iff, ha.2, hb.2, and_true]
    exact ⟨a, ha.1, ⟨b, hb.1, rfl⟩⟩
  · rw [le_inf_iff]
    constructor <;> rw [← monomial_ideal_le_monomial_ideal]
    · intro m ⟨n, hns, l, hl⟩
      use n
      rw [hl.2]
      exact ⟨hns, le_sup_left⟩
    · intro m ⟨n, hns, l, hl⟩
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
  simp [Set.mem_mul]

end Monomial
