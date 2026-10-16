import Mathlib
import CcaInLean.Macaulay.Expansion
import CcaInLean.Macaulay.LexSegment

open LocallyFiniteOrder

variable {n : ℕ} {m : Fin (n + 1) →₀ ℕ} {𝒜 ℬ : Finset (Fin n →₀ ℕ)} {s : Fin n →₀ ℕ} {i : Fin n}

/-- Monomials which are given by one variable times the monomials in a set. -/
noncomputable
def shade (𝒜 : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  𝒜.biUnion fun m ↦
    Finset.image (fun i ↦ m + Finsupp.single i 1) (Finset.univ)

/-- Shadow of an inidividual element. -/
noncomputable
def iShadow1 (v : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
    {f ∈ finsetIcc 0 v | ∃ i : Fin n, f + Finsupp.single i 1 = v}

/-- Shadow of a family, notably this is a computable definition. -/
noncomputable
def shadow (𝒜 : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) := 𝒜.biUnion iShadow1

lemma mem_iShadow1 {v : Fin n →₀ ℕ} :
    v ∈ iShadow1 s ↔ ∃ i : Fin n, (v + Finsupp.single i 1) = s := by
  simp [iShadow1, finset_mem_Icc]
  intro x rfl
  simp

/-- Member of the shadow if and only if -/
lemma mem_shadow {v : Fin n →₀ ℕ} :
    v ∈ shadow 𝒜 ↔ ∃ i : Fin n, (v + Finsupp.single i 1) ∈ 𝒜 := by
  simp [shadow, iShadow1]
  apply Iff.intro
  · exact fun ⟨i, hi⟩ ↦ ⟨i, hi.1⟩
  exact fun ⟨i, hi⟩ ↦ ⟨i, hi, by  simp [finset_mem_Icc]⟩

@[simp]
lemma mem_shade {x : Fin n →₀ ℕ} :
    x ∈ shade 𝒜 ↔ ∃ y ∈ 𝒜, ∃ i, y + Finsupp.single i 1 = x := by simp [shade]

lemma add_single_mem_shade {x : Fin n →₀ ℕ} (hx : x ∈ 𝒜) :
    x + Finsupp.single i 1 ∈ shade 𝒜 := by
  rw [mem_shade]
  exact ⟨x, hx, i, rfl⟩

lemma sub_single_mem_shadow {x : Fin n →₀ ℕ} (hx : x ∈ 𝒜) (hi : i ∈ x.support) :
    x - Finsupp.single i 1 ∈ shadow 𝒜 := by
  rw [mem_shadow]
  use i
  have : Finsupp.single i 1 ≤ x := by
    rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff]
    exact hi
  rw [tsub_add_cancel_iff_le.mpr this]
  exact hx

lemma le_ge_lex {a b : Fin n} (hab : a ≤ b) :
    toLex (Finsupp.single b 1 : Fin n →₀ ℕ) ≤ toLex (Finsupp.single a 1) := by
  cases lt_or_eq_of_le hab with
  | inl hlt => exact le_of_lt <| Finsupp.single_lt_gt_lex hlt
  | inr heq => exact heq ▸ le_refl _

theorem subset_shadow_shade {𝒜 : Finset (Fin (n + 1) →₀ ℕ)} : 𝒜 ⊆ shadow (shade 𝒜) := by
  intro x hx
  rw [mem_shadow]
  exact ⟨0, add_single_mem_shade hx⟩

lemma ne_zero_shade_shadow {𝒜 : Finset (Fin (n + 1) →₀ ℕ)} {x : Fin (n + 1) →₀ ℕ}
    (hx : x ≠ 0) (h𝒜 : x ∈ 𝒜) :
    x ∈ shade (shadow 𝒜) := by
  rw [mem_shade]
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hx
  use x - (Finsupp.single a 1)
  constructor
  · exact sub_single_mem_shadow h𝒜 ha
  · use a
    have : Finsupp.single a 1 ≤ x := by
      rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff]
      exact ha
    rw [tsub_add_cancel_iff_le.mpr this]

theorem subset_shade_shadow {𝒜 : Finset (Fin (n + 1) →₀ ℕ)} (h𝒜 : 0 ∉ 𝒜) : 𝒜 ⊆ shade (shadow 𝒜) :=
  fun _ hx ↦ ne_zero_shade_shadow (fun h ↦ h𝒜 <| h ▸ hx) hx

#print axioms subset_shade_shadow

open Classical in
noncomputable def LevelSet (𝒜 : Set (Fin n →₀ ℕ)) (k : ℕ) : Finset (Fin n →₀ ℕ) :=
  {x ∈ Finset.finsuppAntidiag Finset.univ k | x ∈ 𝒜}

example {𝒜 : Set (Fin n →₀ ℕ)} :
    ∀ x ∈ 𝒜, ∀ y, y ≤ x → y ∈ 𝒜 ↔ ∀ k, LevelSet 𝒜 k ⊆ shadow (LevelSet 𝒜 (k + 1)) := by
  sorry


/-- Shade of the right segment is the right segment times the least variablle. -/
theorem shade_rightSeg {m : Fin (n + 1) →₀ ℕ} :
    shade (cRightSeg m) = cRightSeg (m + Finsupp.single (Fin.last n) 1) := by
  ext x
  simp only [mem_shade, mem_crightSeg, Finsupp.coe_add, Pi.add_apply, toLex_add]
  constructor <;> intro h
  · obtain ⟨a, ha, ⟨b, hb⟩⟩ := h
    constructor
    · simp [← hb, Finset.sum_add_distrib, ha.1]
    · cases ha.2 with
      | inl heq =>
        simp at heq
        rw [heq, ← hb, toLex_add, add_le_add_iff_left]
        apply le_ge_lex (Fin.le_last _)
      | inr hlt =>
        apply le_of_lt
        rw [← hb, toLex_add]
        apply add_lt_add_of_lt_of_le hlt
        have := Fin.le_last b
        rw [le_iff_lt_or_eq] at ⊢ this
        cases this with
        | inl hl => left; exact Finsupp.single_lt_gt_lex hl
        | inr hr => right; rw [hr]
  · cases lt_or_eq_of_le h.2 with
    | inr heq =>
      rw [← toLex_add, toLex_inj] at heq
      use x - fun₀ | Fin.last n => 1
      constructor
      · simp [← heq]
      · use Fin.last n
        rw [tsub_add_cancel_iff_le, ← heq]
        exact CanonicallyOrderedAdd.le_add_self _ _
    | inl hlt =>
      rw [← toLex_add, Finsupp.Lex.lt_def] at hlt
      obtain ⟨a, ha₁, ha₂⟩ := hlt
      have hxzero : x ≠ 0 := by
        intro hx0
        rw [hx0] at h
        grind =>
          instantiate only [= Finsupp.zero_apply]
          lia
      have hxs : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hxzero
      use x - Finsupp.single (Finset.max' _ hxs) 1
      constructor
      · simp only [Finsupp.tsub_apply]
        rw [Finset.sum_tsub_distrib, h.1, Finset.sum_add_distrib]
        simp only [Finsupp.univ_sum_single_apply, add_tsub_cancel_right, toLex_sub, true_and]
        · have : a ≤ (Finset.max' _ hxs) := by
            have : x a ≠ 0 := by
              intro ha0
              rw [ha0] at ha₂
              apply Nat.not_lt_zero _ ha₂
            apply Finset.le_max'
            rwa [Finsupp.mem_support_iff]
          cases lt_or_eq_of_le this with
          | inl hl =>
            apply le_of_lt
            rw [← toLex_sub, Finsupp.Lex.lt_def]
            use a
            constructor
            · intro j hj
              have hjx : j ≠ x.support.max' hxs := by
                intro hjx
                rw [hjx] at hj
                exact (lt_self_iff_false _).mp (lt_trans hj hl)
              have hjn : j ≠ Fin.last n := by
                intro hjn
                rw [hjn, lt_iff_not_ge] at hj
                exact hj <| Fin.le_last a
              simp [hjx]
              rw [← ha₁ _ hj]
              simp [hjn]
            · have : a < Fin.last n := lt_of_lt_of_le hl (Fin.le_last _)
              simp [ne_of_lt hl, ne_of_lt this] at ⊢ ha₂
              exact ha₂
          | inr hr =>
            rw [← toLex_sub]
            by_cases hxa : x a = m a + 1
            · have : x = m + Finsupp.single a 1 := by
                ext i
                obtain hlt | heq | hgt := lt_trichotomy a i
                · have : x i = 0 := by
                    contrapose! hlt
                    exact hr ▸ Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hlt)
                  rw [this]
                  have hsum := h.1
                  rw [Finset.sum_add_distrib, Finsupp.univ_sum_single_apply] at hsum
                  suffices m i = 0 by simp [ne_of_lt hlt, this]
                  have : ∑ i, m i = ∑ i ∈ Finset.Icc 0 a, m i := by
                    calc
                      _ = ∑ i, x i - 1 := by
                        rw [hsum, Nat.add_sub_cancel_right]
                      _ = ∑ i ∈ Finset.Icc 0 a, x i - 1 := by
                        congr 1
                        have : Function.support x ⊆ Finset.Icc 0 a := by
                          intro i hi
                          rw [Finsupp.fun_support_eq, SetLike.mem_coe] at hi
                          rw [SetLike.mem_coe, Finset.mem_Icc, hr]
                          exact ⟨Fin.zero_le _, Finset.le_max' _ _ hi⟩
                        rw [← finsum_eq_sum_of_support_subset _ this]
                        exact Eq.symm (finsum_eq_sum_of_fintype _)
                      _ = ∑ i ∈ Finset.Icc 0 a, m i:= by
                        rw [Finset.Icc_eq_cons_Ico, Finset.sum_cons, Finset.sum_cons, hxa]
                        · have : ∑ x_1 ∈ Finset.Ico 0 a, x x_1 = ∑ i ∈ Finset.Ico 0 a, m i := by
                            apply Finset.sum_congr rfl
                            intro j hj
                            rw [Finset.mem_Ico] at hj
                            rw [show m j = (m + fun₀ | Fin.last n => 1) j by
                              simp [ne_of_lt <| lt_of_lt_of_le hj.2 (Fin.le_last _)]]
                            exact (ha₁ j hj.2).symm
                          rw [this]
                          simp
                        exact Fin.zero_le _
                  contrapose! this
                  apply ne_of_gt
                  suffices ∑ i ∈ Finset.Icc 0 a, m i < ∑ i ∈ Finset.Icc 0 a, m i + m i by
                    apply lt_of_lt_of_le this
                    rw [add_comm, ← Finset.sum_cons]
                    apply Finset.sum_le_univ_sum_of_nonneg (fun x ↦ Nat.zero_le _)
                    exact fun hicc ↦ not_le_of_gt hlt (Finset.mem_Icc.mp hicc).2
                  lia
                · simp [← heq, hxa]
                · simp [ne_of_lt hgt]
                  have h := ha₁ _ hgt
                  have : i < Fin.last n := lt_of_lt_of_le hgt (Fin.le_last _)
                  simp [ne_of_lt this] at h
                  exact h.symm
              rw [← hr, this, add_tsub_cancel_right]
            · apply le_of_lt
              rw [Finsupp.Lex.lt_def]
              use a
              constructor
              · intro j hj
                simp [← hr, ne_of_lt hj, ← ha₁ _ hj]
                have : j < Fin.last n := lt_of_lt_of_le hj (Fin.le_last _)
                simp [ne_of_lt this]
              · simp [← hr]
                by_cases hl : a = Fin.last n
                · simp [hl] at ha₂
                  lia
                have : a < Fin.last n := by
                  apply lt_of_le_of_ne (Fin.le_last _) hl
                simp [ne_of_lt this] at ha₂
                lia
        · intro y _
          by_cases h : y = x.support.max' hxs <;> simp [h]
          rw [← Nat.lt_iff_add_one_le, ← Nat.ne_zero_iff_zero_lt, ← Finsupp.mem_support_iff]
          exact Finset.max'_mem _ hxs
      · use (Finset.max' _ hxs)
        rw [tsub_add_cancel_iff_le]
        intro i
        by_cases h : i = x.support.max' hxs <;> simp [h]
        rw [← Nat.lt_iff_add_one_le, ← Nat.ne_zero_iff_zero_lt, ← Finsupp.mem_support_iff]
        exact Finset.max'_mem _ hxs
