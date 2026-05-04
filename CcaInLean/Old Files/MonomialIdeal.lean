import Mathlib

noncomputable section

variable {σ R : Type*} [CommRing R] [Nontrivial R]

/- Abbreviation for the monomials, aka the standard basis for MvPolynomial -/
/- Addition is automatically defined since Mathlib knows this type to be a
  ""module"" over `ℕ`, but we would like to show this to be multiplication.
  It probably doesn't matter though. -/
abbrev Monomial (σ : Type*) := σ →₀ ℕ

/- Coercion from Monomial to MvPolynomial in the obvious sense -/
instance : Coe (Monomial σ) (MvPolynomial σ R) where
  coe x := MvPolynomial.monomial x 1

/- The monomial corresponding to `1` in MvPolynomial -/
abbrev Monomial.one (σ : Type*) : Monomial σ := {
    support := ⊥
    toFun := fun _ ↦ 0
    mem_support_toFun := by
      simp only [Finset.bot_eq_empty, Finset.notMem_empty, ne_eq, not_true_eq_false, implies_true]
  }

/- Coercion preserves equality. -/
@[simp]
lemma Monomial.coe_eq (a b : Monomial σ) :
    a = b ↔ (a : Monomial σ) = (b : Monomial σ) := by rfl

/- Coercion preserves one -/
@[simp]
lemma Monomial.coe_one {R : Type*} [CommRing R] :
    (Monomial.one σ : MvPolynomial σ R) = (1 : MvPolynomial σ R) := by
  congr

/- Coercion is multiplcative -/
lemma Monomial.coe_add {R : Type*} [CommRing R] (a b : Monomial σ) :
   (a + b : Monomial σ) = (a : MvPolynomial σ R) * b := by
  rw [@MvPolynomial.monomial_mul, one_mul]

/- Probably not necessary to have this leema -/
lemma Monomial.le_iff (a b : Monomial σ) :
    a ≤ b ↔ (a : MvPolynomial σ R) ∣ b := by
  rw [MvPolynomial.monomial_one_dvd_monomial_one]

/- Wrapper for basis set of monomials -/
structure MonomialIdeal (σ R : Type*) [CommRing R] [Nontrivial R] where
  basis : Set (Monomial σ)

/- Ideal of a monomial ideal -/
def MonomialIdeal.ideal (I : MonomialIdeal σ R) : Ideal (MvPolynomial σ R) :=
  Ideal.span {m : MvPolynomial σ R | ∃ (i : I.basis), m = i}

/- Monomials in an ideal -/
def idealMonomials (I : Ideal (MvPolynomial σ R)) :=
  {i : I | ∃ m : σ →₀ ℕ, i = (m : MvPolynomial σ R)}

/- Monomials in an ideal -/
def idealMonomials2 (I : Ideal (MvPolynomial σ R)) :=
  {m : σ →₀ ℕ | (m : MvPolynomial σ R) ∈ I}

#check MvPolynomial.mem_ideal_span_monomial_image

lemma supp_in_ideal (I : MonomialIdeal σ R) :
    ∀ (p : MvPolynomial σ R), 
    p ∈ I.ideal → (p.support : Set (σ →₀ ℕ)) ⊆ (idealMonomials2 I.ideal) := by
  intro p hpI m hmp


lemma monomials_in_ideal_lin_ind (I : Ideal (MvPolynomial σ R)) :
    LinearIndependent R (fun (x : MonomialIdeal.idealMonomials I) ↦ x.1) := by
  sorry

lemma monomial_ideal_gen_ (I : MonomialIdeal σ R) :
    Submodule.span R (MonomialIdeal.idealMonomials I.ideal) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  sorry

def monomial_basis_mideal (I : MonomialIdeal σ R) :
   Module.Basis (σ →₀ ℕ) R I.ideal := sorry