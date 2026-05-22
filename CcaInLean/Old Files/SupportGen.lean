/-

def SupportGen (p : MvPolynomial σ R) (s : Set (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
    {m ∈ s | ∃ mi ∈ p.support, m ≤ mi}

theorem support_gen_finite (p : MvPolynomial σ R) (s : Set (σ →₀ ℕ)) : Finite (SupportGen p s) := by
    have : SupportGen p s ≤ ⨆ mi ∈ p.support, {m : σ →₀ ℕ | m ≤ mi} := by
      rintro m ⟨hm, n, hmn⟩
      rw [Set.iSup_eq_iUnion, Set.mem_iUnion]
      simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_setOf_eq]
      use n
    apply Set.Finite.subset _ this
    exact Set.Finite.biUnion (Finset.finite_toSet p.support) (fun _ _ ↦ Set.finite_Iic _)

theorem support_gen_le (p : MvPolynomial σ R) (s : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R (SupportGen p s) ≤ MonomialIdeal σ R s := by
  rw [← monomial_ideal_le_monomial_ideal]
  rintro m ⟨_, _⟩
  use m

theorem mem_monomial_ideal_iff_mem_support_gen (p : MvPolynomial σ R) (s : Set (σ →₀ ℕ)) :
    p ∈ MonomialIdeal σ R s ↔ p ∈ MonomialIdeal σ R (SupportGen p s) := by
  constructor
  · rw [mem_ideal_span_monomial_image, mem_ideal_span_monomial_image]
    intro hp xi hxi
    rcases hp xi hxi with ⟨m, hm⟩
    use m
    constructor
    · unfold SupportGen
      rw [Set.mem_setOf_eq]
      tauto
    · exact hm.2
  · exact fun hp ↦ support_gen_le _ _ hp
example [IsReduced R] (p : MvPolynomial σ R) (k : ℕ) (m : σ →₀ ℕ) (hm : m ∈ p.support)
    (hm1 : ∀ x ∈ p.support, ∀ n : ℕ, x ≤ n • m → x = m) :
    k • m ∈ (p ^ k).support := by
  rw [mem_support_iff]
  rw [← thingy p k m hm1]
  rw [ne_eq, pow_eq_zero_iff']
  intro ⟨h1, h2⟩
  rw [mem_support_iff] at hm
  contradiction

/-
noncomputable
instance : LinearOrder σ := by
  classical
  exact linearOrderOfSTO WellOrderingRel

noncomputable
instance : LinearOrder (σ →₀ ℕ) := Finsupp.DegLex.instLinearOrderDegLexNat
-/
-- ≼

-/
