import Mathlib
open LocallyFiniteOrder

variable {n : ℕ} {m : Fin (n + 1) →₀ ℕ} {𝒜 : Finset (Fin n →₀ ℕ)}

def cLeftSeg (m : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
  {x ∈ Finset.finsuppAntidiag Finset.univ (∑ i, m i) | toColex x ≤ toColex m}

@[simp]
lemma mem_cLeftSeg {m x : Fin n →₀ ℕ} : x ∈ cLeftSeg m
    ↔ ∑ i, x i = ∑ i, m i ∧ toColex x ≤ toColex m := by simp [cLeftSeg]

/-- Shadow of an inidividual element. -/
noncomputable
def iShadow (v : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
    {f ∈ finsetIcc 0 v | ∃ i : Fin n, f + Finsupp.single i 1 = v}

/-- Shadow of a family, notably this is a computable definition. -/
noncomputable
def Shadow (𝒜 : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) := 𝒜.biUnion iShadow

/-- Member of the Shadow if and only if -/
@[simp]
lemma mem_Shadow {v : Fin n →₀ ℕ} :
    v ∈ Shadow 𝒜 ↔ ∃ i : Fin n, (v + Finsupp.single i 1) ∈ 𝒜 := by
  simp [Shadow, iShadow]
  refine Iff.intro (fun ⟨i, hi⟩ ↦ ⟨i, hi.1⟩) ?_
  exact fun ⟨i, hi⟩ ↦ ⟨i, hi, by  simp [finset_mem_Icc]⟩

lemma sub_single_mem_Shadow {x : Fin n →₀ ℕ} (hx : x ∈ 𝒜) (hi : i ∈ x.support) :
    x - Finsupp.single i 1 ∈ Shadow 𝒜 := by
  rw [mem_Shadow]
  use i
  have : Finsupp.single i 1 ≤ x := by
    rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff]
    exact hi
  rw [tsub_add_cancel_iff_le.mpr this]
  exact hx

noncomputable
def Shadow_sup {m : Fin n →₀ ℕ} (hm : m ≠ 0) : Fin n →₀ ℕ :=
    have : Finset.Nonempty m.support := Finsupp.support_nonempty_iff.mpr hm
    m - (Finsupp.single (Finset.min' _ this) 1)

lemma Shadow_sup_size {m : Fin n →₀ ℕ} (hm : m ≠ 0) :
    ∑ i, (Shadow_sup hm) i = ∑ i, m i - 1 := by
  simp only [Shadow_sup, Finsupp.tsub_apply]
  rw [Finset.sum_tsub_distrib, Finsupp.univ_sum_single_apply]
  intro a ha
  by_cases h : a = m.support.min' (Finsupp.support_nonempty_iff.mpr hm) <;> simp [h]
  · rw [Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff]
    exact Finset.min'_mem _ (Finsupp.support_nonempty_iff.mpr hm)

lemma zero_sum : m = 0 ↔ ∑ i, m i = 0 := by aesop

lemma nonzero_sum : m ≠ 0 ↔ ∑ i, m i ≠ 0 := by contrapose!; exact zero_sum

lemma Finsupp.Colex.lt_def {s t : Fin n →₀ ℕ} : toColex s < toColex t ↔
  ∃ i : Fin n, (∀ j : Fin n, j > i → s j = t j) ∧ (s i) < (t i) := by rfl

lemma Finsupp.Colex_lt_iff {s t : Fin n →₀ ℕ} : toColex s < toColex t ↔
    ∃ i : Fin n, (∀ j : Fin n, j > i → s j ≤ t j) ∧ (s i) < (t i) := by
  rw [Finsupp.Colex.lt_def]
  constructor <;> intro ⟨k, hk⟩
  · exact ⟨k, fun a ha ↦ le_of_eq (hk.1 _ ha), hk.2⟩
  · have hn : Finset.Nonempty {i : Fin n | s i < t i} := ⟨k, by simp [hk.2]⟩
    use Finset.max' _ hn
    have : k ≤ (Finset.max' _ hn) := by simp [Finset.le_max', hk.2]
    constructor
    · intro j hj
      apply le_antisymm
      · exact hk.1 _ (lt_of_le_of_lt this hj)
      · by_contra!
        have h1 := (Finset.max'_lt_iff _ hn).mp hj
        exact (lt_self_iff_false j).mp (h1 j <| (Finset.mem_filter_univ j).mpr this)
    · have h := Finset.max'_mem _ hn -- Bad code
      simp at h
      exact h

lemma toColex_le_iff_lt_or_eq {a b : Colex (Fin n →₀ ℕ)} :
    a ≤ b ↔ a < b ∨ a = b := Std.le_iff_lt_or_eq

lemma Colex_single_lt_single {i j : Fin n} (hij : i < j) :
    toColex (fun₀ | i => 1) < toColex (fun₀ | j => 1) := by
  use j
  simp [ne_of_lt hij]
  exact fun k hjk ↦ by simp [ne_of_lt hjk, ne_of_lt (lt_trans hij hjk)]

lemma Colex_single_le_single {i j : Fin n} (hij : i ≤ j) :
    toColex (fun₀ | i => 1) ≤ toColex (fun₀ | j => 1) := by
  rw [le_iff_lt_or_eq] at hij
  cases hij with
  | inl hlt => exact le_of_lt (Colex_single_lt_single hlt)
  | inr heq => simp [heq]

lemma colex_sub_lt_iff {a b c : Fin n →₀ ℕ} (hca : c ≤ a) :
    toColex (a - c) < toColex b ↔ toColex a < toColex (b + c) := by
  rw [← @add_lt_add_iff_right _ _ _ _ _ (toColex c) (toColex (a - c)) (toColex b)]
  have : toColex (a - c) + toColex c = toColex a := by
    rw [← toColex_add, toColex_inj]
    exact tsub_add_cancel_of_le hca
  rw [this, toColex_add]

lemma colex_sub_le_iff {a b c : Fin n →₀ ℕ} (hca : c ≤ a) : -- THis is probably a little idiotic
    toColex (a - c) ≤ toColex b ↔ toColex a ≤ toColex (b + c) := by
  have : toColex (a - c) = toColex b ↔ toColex a = toColex (b + c) := by
    nth_rw 2 [← tsub_add_cancel_of_le hca]
    rw [toColex_add, toColex_add, add_right_cancel_iff]
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, colex_sub_lt_iff hca, this]

lemma colex_le_sub_iff {a b c : Fin n →₀ ℕ} (hca : c ≤ a) :
    toColex b ≤ toColex (a - c) ↔ toColex (b + c) ≤ toColex a := by
  contrapose!
  rw [colex_sub_lt_iff hca]

lemma Finsupp.sum_support {a : Fin n →₀ ℕ} : ∑ i ∈ a.support, a i = ∑ i, a i :=
    Finset.sum_subset (Finset.subset_univ a.support) (by norm_num)

lemma Finsupp.support_erase_sum (a : Fin n →₀ ℕ) (j : Fin n) :
    ∑ i ∈ a.support, a i = ∑ i ∈ (Finset.erase a.support j), a i + a j := by
  by_cases h : j ∈ a.support
  · exact Eq.symm (Finset.sum_erase_add a.support _ h)
  · simp_all only [mem_support_iff, ne_eq, Decidable.not_not, not_true_eq_false, not_false_eq_true,
    Finset.erase_eq_of_notMem, add_zero]

lemma Finsupp.eq_if_le_eq_sum {a b : Fin n →₀ ℕ} (hab : ∑ i, a i = ∑ i, b i)
    (hle : a ≤ b) : a = b := by
  contrapose! hab
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hab
  apply ne_of_lt
  refine Finset.sum_lt_sum
    (fun i a ↦ hle i) ⟨i, Finset.mem_univ i, Nat.lt_of_le_of_ne (hle i) hi⟩

theorem Shadow_leftSeg_eq_leftSeg (hm : m ≠ 0) :
        Shadow (cLeftSeg m) = cLeftSeg (Shadow_sup hm) := by
    ext x
    rw [mem_Shadow, mem_cLeftSeg]
    let j := (Finset.min' _ <| Finsupp.support_nonempty_iff.mpr hm)
    have hj : j = (Finset.min' _ <| Finsupp.support_nonempty_iff.mpr hm) := rfl
    have hjm : ∀ i < j, m i = 0 := by
      intro i hi
      rw [Finset.lt_min'_iff] at hi
      suffices ¬(i ∈ m.support) by simp_all
      contrapose! hi; exact ⟨i, hi, le_refl _⟩
    have hjs₁ : Shadow_sup hm = m - fun₀ | j => 1 := Finsupp.ext (congrFun rfl)
    have hjs₂ : ∀ i ≠ j, (Shadow_sup hm) i = m i := fun i hi ↦ by simp [hjs₁, hi]
    have hs₁ : Shadow_sup hm ≤ m := hjs₁ ▸ tsub_le_self
    have hs₂ : (fun₀ | j => 1) ≤ m := by
      rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
      exact Finsupp.mem_support_iff.mp <|
        Finset.min'_mem m.support (Finsupp.support_nonempty_iff.mpr hm)
    have hs₃ : Shadow_sup hm + (fun₀ | j => 1) = m := by
      rw [hjs₁, tsub_add_cancel_iff_le.mpr hs₂]
    constructor <;> intro h
    · obtain ⟨i, hi⟩ := h
      constructor
      · simp [Shadow_sup_size hm, ← (mem_cLeftSeg.mp hi).1, Finset.sum_add_distrib]
      · apply mem_cLeftSeg.mp at hi
        by_cases! hij : i < j
        · cases lt_or_eq_of_le hi.2 with
          | inl hlt =>
            obtain ⟨r, hr₁, hr₂⟩ := hlt
            simp at hr₁ hr₂
            have : r ≥ j := by
              by_contra!
              exact (ne_of_lt <| Nat.zero_lt_of_lt hr₂) (hjm _ this).symm
            have hr₃ : ∀ a > r, x a = m a := fun a ha ↦ by
              simp [← hr₁ _ ha, ne_of_lt <| lt_trans hij (lt_of_le_of_lt this ha)]
            cases lt_or_eq_of_le this with
            | inl hlt =>
              refine le_of_lt ⟨r, ?_⟩
              simp only [ofColex_toColex]
              constructor
              · intro a hra
                rw [hjs₂ _ (ne_of_gt <| lt_trans hlt hra), ← hr₃ _ hra]
              · simp [ne_of_gt (lt_trans hij hlt)] at hr₂
                rwa [hjs₂ _ (ne_of_gt hlt)]
            | inr heq =>
              have : x r + 1 ≤ m r := by
                rw [Nat.add_one_le_iff]
                simp [ne_of_lt (heq ▸ hij)] at hr₂
                exact hr₂
              cases lt_or_eq_of_le this with
              | inl hxr =>
                refine le_of_lt ⟨r, ?_⟩
                simp only [ofColex_toColex]
                constructor
                · intro a har
                  rw [hjs₂ _ <| ne_of_gt (heq ▸ har), hr₃ _ har]
                · simp [hjs₁, heq]
                  exact Nat.lt_sub_of_add_lt hxr
              | inr hxr =>
                apply le_of_eq
                apply toColex_inj.mpr
                symm
                apply Finsupp.eq_if_le_eq_sum
                · simp [Shadow_sup_size hm, ← hi.1, Finset.sum_add_distrib]
                · intro k
                  rcases lt_trichotomy k j with hkj | hmeqn | hjk
                  · simp [hjs₂ _ (ne_of_lt hkj), hjm _ hkj]
                  · simp [hjs₁, heq, hmeqn, hxr]
                  · apply le_of_eq
                    simp [hjs₂ _ (ne_of_gt hjk)]
                    rw [← hr₁]
                    simp [ne_of_lt <| Fin.lt_trans hij hjk]
                    exact heq ▸ hjk
          | inr heq =>
            have : m i = 0 := hjm _ hij
            have : m i = x i + 1 := by simp [← toColex_inj.mp heq]
            linarith
        · rw [hjs₁, colex_le_sub_iff hs₂]
          refine le_trans (by simp [Colex_single_le_single hij]) hi.2
    · use j
      apply mem_cLeftSeg.mpr
      constructor
      · simp [Finset.sum_add_distrib, h.1, Shadow_sup_size hm]
        apply Nat.sub_add_cancel
        rw [Nat.one_le_iff_ne_zero]
        exact nonzero_sum.mp hm
      · rw [← hs₃]
        simp [h.2]
