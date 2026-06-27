import Mathlib

open LocallyFiniteOrder

variable {n : ℕ} {i : Fin n} {s : Fin n → ℕ}

/-- Shadow of an inidividual element. -/
def iShadow (v : Fin n → ℕ) : Finset (Fin n → ℕ) :=
    {f ∈ finsetIcc 0 v | ∃ i : Fin n, f + Pi.single i 1 = v}

/-- SHadow of a family, notably this is a computable definition. -/
def Shadow (𝒜 : Finset (Fin n → ℕ)) : Finset (Fin n → ℕ) := 𝒜.biUnion iShadow

lemma mem_iShadow_iff {v : Fin n → ℕ} :
    v ∈ iShadow s ↔ ∃ i : Fin n, (v + Pi.single i 1) = s := by
  unfold iShadow
  simp only [Finset.mem_filter, and_iff_right_iff_imp, forall_exists_index, finset_mem_Icc]
  intro x rfl
  simp

lemma mem_shadow_iff {v : Fin n → ℕ} {s : Finset (Fin n → ℕ)} :
    v ∈ Shadow s ↔ ∃ i : Fin n, (v + Pi.single i 1) ∈ s := by
  unfold Shadow iShadow
  simp only [Finset.mem_biUnion, Finset.mem_filter, ↓existsAndEq, and_true]
  apply Iff.intro
  · exact fun ⟨i, hi⟩ ↦ ⟨i, hi.1⟩
  refine fun ⟨i, hi⟩ ↦ ⟨i, hi, ?_⟩
  simp [finset_mem_Icc]

lemma lt_def {s t : Fin n → ℕ} : toLex s < toLex t ↔
  ∃ i : Fin n, (∀ j : Fin n, j < i → s j = t j) ∧ (s i) < (t i) := by rfl

lemma toLex.lt_of_le_cond {s t : Fin n → ℕ} : toLex s < toLex t ↔
    ∃ i : Fin n, (∀ j : Fin n, j < i → s j ≤ t j) ∧ (s i) < (t i) := by sorry

-- Something horrible is going on with the lt here
lemma test {s t : Fin n → ℕ} : toLex s ≤ toLex t ↔ toLex s < toLex t ∨ toLex s = toLex t :=
  le_iff_lt_or_eq

lemma toLex.lt_of_le {s t : Fin n → ℕ} : toLex s < toLex t → toLex s ≤ toLex t := by
  rw [test]
  intro h
  left
  exact h

lemma lt_gt_lex {a b : Fin n} (hab : a < b) :
    toLex (Pi.single b 1 : Fin n → ℕ) < toLex (Pi.single a 1) := by
  rw [lt_def]
  use a
  constructor
  · intro j hj
    simp [ne_of_lt hj, ne_of_lt (lt_trans hj hab)]
  · simp [ne_of_lt hab]

def remSmallest (s : Fin n → ℕ) : (Fin n → ℕ) :=
  match Fin.findRev? (fun i ↦ s i ≠ 0) with
  | some i => s - Pi.single i 1
  | none => 0

@[simp]
theorem remSmallest_zero : remSmallest (0 : Fin n → ℕ) = 0 := by
  unfold remSmallest
  aesop

lemma sub_single_le_remSmallest (j : Fin n) (hi : s j ≠ 0) :
    toLex (s - Pi.single j 1) ≤ toLex (remSmallest s) := by
  unfold remSmallest
  cases hf : Fin.findRev? (fun i ↦ s i ≠ 0) with
  | some i =>
    simp only [test]
    have hji : j ≤ i := by
      contrapose! hi
      have : _ := Fin.get_findRev?_maximal (Option.isSome_of_mem hf) j (
        by rwa [Option.get_of_eq_some (Option.isSome_of_mem hf) hf])
      simp at this
      assumption
    by_cases! h : i = j
    · exact Or.inr <| h ▸ rfl
    · left
      rw [lt_def]
      use j
      constructor
      · intro k hkj
        simp [Pi.single_eq_of_ne (ne_of_lt hkj) 1,
          Pi.single_eq_of_ne (ne_of_lt (lt_of_lt_of_le hkj hji))]
      · simp [h, Nat.zero_lt_of_ne_zero hi]
  | none =>
    have : s = 0 := by
      simp at hf
      exact funext_iff.mpr hf
    simp [this]

lemma shadow_le_remSmallest {t : Fin n → ℕ} (ht : t ∈ iShadow s) :
    toLex t ≤ toLex (remSmallest s) := by
  obtain ⟨x, rfl⟩ := mem_iShadow_iff.mp ht
  calc
    _ = toLex (t + Pi.single x 1 - Pi.single x 1) := by simp
    _ ≤ _ := by
      apply sub_single_le_remSmallest
      simp

theorem exists_single_remSmallest (hs : s ≠ 0) :
    ∃ i : Fin n, ((remSmallest s) = s - Pi.single i 1 ∧ ∀ j > i, s j = 0) ∧ s i ≠ 0 := by
  cases hf : Fin.findRev? (fun i ↦ s i ≠ 0) with
  | some i =>
    use i
    constructor
    · constructor
      · unfold remSmallest
        grind only
      · simp only [ne_eq, decide_not, Fin.findSomeRev?_eq_some_iff, Option.guard_eq_some_iff,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Option.guard_eq_none_iff,
        Bool.not_false, decide_eq_true_eq, ↓existsAndEq, true_and] at hf
        tauto
    · simp_all only [ne_eq, decide_not, Fin.findSomeRev?_eq_some_iff, Option.guard_eq_some_iff,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Option.guard_eq_none_iff,
      Bool.not_false, decide_eq_true_eq, ↓existsAndEq, true_and, not_false_eq_true]
  | none =>
    contrapose! hs
    simp_all only [ne_eq, decide_not, Fin.findSomeRev?_eq_none_iff, Option.guard_eq_none_iff,
      Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, gt_iff_lt, implies_true, and_true]
    ext x : 1
    simp_all only [Pi.zero_apply]

theorem remSmallest_mono {a b : Fin n → ℕ} (hab : toLex a ≤ toLex b) (habs : ∑ i, a i = ∑ i, b i) :
    toLex (remSmallest a) ≤ toLex (remSmallest b) := by
  cases test.mp hab with
  | inr heq => rw [toLex_inj.mp heq]
  | inl hlt =>
    obtain ⟨x, hx⟩ := lt_def.mp hlt
    by_cases! ha : a = 0
    · rw [ha, remSmallest_zero]
      exact StrictMono.minimal_preimage_bot (fun _ _ a ↦ a) rfl _
    · obtain ⟨y, ⟨hay, hy⟩, ha0⟩ := exists_single_remSmallest ha
      have : b ≠ 0 := Ne.symm (Ne.intro fun a ↦ (by lia : b x ≠ 0) (congrFun (id (Eq.symm a)) x))
      obtain ⟨z, ⟨haz, hz⟩, hb0⟩ := exists_single_remSmallest this
      rw [hay, haz]
      by_cases hbx : b x = a x + 1
      · by_cases! h : ∀ i > x, b i = 0
        · sorry
        · apply toLex.lt_of_le
          rw [toLex.lt_of_le_cond]
          use x
          obtain ⟨w, hw⟩ := h
          have hyw : w ≤ z := sorry
          constructor
          · intro j hj
            sorry
          · sorry
      · have hax : a x + 1 < b x := by lia
        apply toLex.lt_of_le
        rw [toLex.lt_of_le_cond]
        use x
        by_cases! h : ∀ i > x, b i = 0
        · have hx0 : b x ≠ 0 := by lia
          have : z = x := by
            apply le_antisymm
            by_contra!
            apply hb0 <| h _ this
            by_contra!
            apply hx0 <| hz _ this
          constructor
          · intro k hk
            rw [this]
            simp [ne_of_lt hk, hx.1 _ hk]
          · calc
              _ < b x - 1:= by
                rw [Pi.sub_apply]
                refine Nat.sub_lt_of_lt ?_
                exact Nat.lt_sub_of_add_lt hax
              _ ≤ b x - (Pi.single z 1 : Fin n → ℕ) x := by
                apply Nat.sub_le_sub_left
                grind only [= Pi.single_apply]
              _ = _ := Eq.symm (Pi.sub_apply b (Pi.single z 1) x)
        · sorry
      /-
      by_cases! h : ∀ j > x, a j = 0
      · by_cases hbx : b x = 1
        · sorry
        · sorry
      · obtain ⟨w, hw⟩ := h
        rw [test]
        left
        rw [lt_def]
        use x
        have : x < y := by
          calc
            _ < w := hw.1
            _ ≤ y := by by_contra!; exact hw.2 <| hy _ <| this
        have hbw : b w ≠ 0 := sorry
        have : x < z := by
          calc
            _ < w := hw.1
            _ ≤ z := by by_contra!; exact hbw <| hz _ this
        constructor
        · intro j hj
          have hjy : j < y := sorry
          have hjz : j < z := sorry
          simp [ne_of_lt hjz, ne_of_lt hjy]
          exact hx.1 _ hj
        · sorry
          -/


    /-
    by_cases hax : a x = 0
    · by_cases hbx : b x = 1
      · sorry
      · have : b x > 1 := by lia
        calc
          _ ≤ toLex (b - Pi.single x 1) := by
            apply test.mpr
            left
            rw [lt_def]
            use x
            sorry
          _ ≤ toLex (remSmallest b) := sorry
    · apply test.mpr
      apply Or.inl
      rw [lt_def]
      use x
      sorry
    -/
    /-
    by_cases! h : ∀ j > x, a j = 0
    · sorry
    · obtain ⟨k, hk⟩ := h
      calc
        _ ≤ toLex (b - Pi.single k 1) := by
          rw [test]
          left
          rw [lt_def]
          use x
          constructor
          · intro y hy
            simp [ne_of_lt (lt_trans hy hk.1)]
            sorry
          · sorry
        _ ≤ _ := by
          apply sub_single_le_remSmallest
          sorry
    -/


/-
/-- Shadow of an initial segment is initial. -/
example (𝒜 : Finset (Fin n → ℕ)) (h𝒜 : IsInitSeg c 𝒜) (h𝒜f : IsFixed c (r + 1) 𝒜) :
    IsInitSeg c (Shadow 𝒜) := by
  intro s t hs ⟨htc, hts, hSum⟩
  rw [mem_shadow_iff] at ⊢ hs
  rcases hs with ⟨i, hsi⟩
  obtain hts | heq := test.mp hts
  · rcases lt_def.mp hts with ⟨f, hf, htsa⟩
    rcases le_or_gt i f with hfi | hif
    · have : toLex (t + Pi.single i 1) ≤ toLex (s + Pi.single i 1) := by
        rw [toLex_add, toLex_add]
        exact add_le_add_left (le_of_lt hts) _
      use i
      apply h𝒜 _ _ hsi
      constructor
      · intro x
        by_cases hxi : x = i
        · rw [hxi, Pi.add_apply, Pi.single_eq_same]
          · obtain hfi | hfi := lt_or_eq_of_le hfi
            · rw [hf i hfi, show s i + 1 = (s + Pi.single i 1 : Fin n → ℕ) i by simp]
              exact (h𝒜f _ hsi).1 i
            · rw [hfi]
              calc
                _ ≤ s f := Order.add_one_le_iff.mpr htsa
                _ ≤ (s + Pi.single i 1 : Fin n → ℕ) f := by
                  rw [Pi.add_apply]
                  exact Nat.le_add_right _ _
                _  ≤ c f := (h𝒜f _ hsi).1 f
        · simp [hxi, htc x]
      · constructor
        · exact this
        · simp [Pi.add_apply, Finset.sum_add_distrib, hSum]
    · by_cases h : ∀ r > f, t r = c r
      · use f
        apply h𝒜 _ _ hsi
        constructor
        · intro x
          obtain hxf | heq | hfx := lt_trichotomy x f
          · simp [ne_of_lt hxf]
            rw [hf _ hxf]
            apply le_trans
            show _ ≤ (s + Pi.single i 1 : Fin n → ℕ) x
            rw [Pi.add_apply]
            exact Nat.le_add_right _ _
            exact (h𝒜f _ hsi).1 _
          · simp only [heq, Pi.add_apply, Pi.single_eq_same]
            calc
              _ ≤ s f := Order.add_one_le_iff.mpr htsa
              _ ≤ (s + (Pi.single i 1 : Fin n → ℕ)) f := by
                  rw [Pi.add_apply]
                  exact Nat.le_add_right _ _
              _ ≤ c f := (h𝒜f _ hsi).1 f
          · simp only [Pi.add_apply, ne_eq, ne_of_lt hfx, not_false_eq_true, Pi.single_eq_of_ne',
            add_zero]
            rw [h _ hfx]
        · constructor
          · by_cases h : t f + 1 < s f
            · rw [test]
              left
              rw [lt_def]
              use f
              constructor
              intro j hj
              simp [ne_of_lt hj, ne_of_lt (lt_trans hj hif), hf _ hj]
              simpa [ne_of_lt hif]
            · sorry
          · simp [Pi.add_apply, Finset.sum_add_distrib, hSum]
      simp only [not_forall, gt_iff_lt] at h
      rcases h with ⟨r, hir, htcr⟩
      use r
      apply h𝒜 _ _ hsi
      constructor
      · intro x
        by_cases h : x = r
        · simp [h, lt_of_le_of_ne (htc r) (htcr)]
        · simp only [Pi.add_apply, ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
          exact htc x
      · constructor
        · rw [test]
          left
          rw [lt_def]
          use f
          constructor
          · intro j hj
            simp only [Pi.add_apply, ne_eq, ne_of_lt (lt_trans hj hir), not_false_eq_true,
              Pi.single_eq_of_ne, add_zero, ne_of_lt (lt_trans hj hif)]
            exact hf _ hj
          · rw [Pi.add_apply, Pi.add_apply]
            apply add_lt_add_of_lt_of_le htsa
            simp [ne_of_lt hir, ne_of_lt hif]
        · simp [Pi.add_apply, Finset.sum_add_distrib, hSum]
  · exact ⟨i, toLex_inj.mp heq ▸ hsi⟩

-/
/-
example (𝒜 : Finset (Fin n → ℕ)) (h𝒜 : IsInitSeg c (r + 1) 𝒜) :
    IsInitSeg c r (Shadow 𝒜) := by
  constructor
  · intro s hs
    rcases mem_shadow_iff.mp hs with ⟨f, hj⟩
    constructor
    · exact le_trans (hj ▸ le_self_add) (h𝒜.1 f hf).1
    · rw [← @Nat.add_right_cancel_iff _ _ 1, ← (h𝒜.1 f hf).2, hj]
      simp [Pi.add_apply, Finset.sum_add_distrib]
  · intro s t hs ⟨htc, hts, hSum
    rw [mem_shadow_iff] at ⊢ hs
    rcases hs with ⟨i, hwi⟩
    obtain htc | heq := test.mp hts
    · rcases lt_def.mp htc with ⟨f, hf, htsa⟩
      rcases le_or_gt i f with (hfi | hif)
      · have : toLex (t + Pi.single i 1) ≤ toLex (s + Pi.single i 1) := by
          rw [toLex_add, toLex_add]
          apply add_le_add_left (le_of_lt htc)
        use t + Pi.single i 1
        constructor
        · apply h𝒜.2 (s + Pi.single i 1) _
          · exact hi ▸ hw𝒜
          constructor
          · intro x
            by_cases hxi : x = i
            · rw [hxi, Pi.add_apply, Pi.single_eq_same]
              · obtain hfi | hfi := lt_or_eq_of_le hfi
                · rw [hf i hfi]
                  sorry
                · rw [hfi, Nat.add_one_le_iff]
                  apply lt_of_lt_of_le (htsa)
                  sorry
            · simp only [Pi.add_apply, ne_eq, hxi, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
              sorry
          · constructor
            · exact this
            · sorry
        · use i
      · by_cases h : ∀ r > i, t r = c r
        · sorry
        rw [not_forall] at h
        simp only [gt
        rw [not_forall] at h
        simp only [gt_iff_lt, Classical.not_imp] at h
        rcases h with ⟨r, hir, htcr⟩
        use t + Pi.single r 1
        constructor
        · apply h𝒜.2  w _ hw𝒜
          constructor
          · have : t r < c r := sorry
            intro x
            by_cases hrx : r = x
            · simp only [hrx, Pi.add_apply, Pi.single_eq_same, Order.add_one_le_iff]
              rwa [← hrx]
            · simp [hrx]
              sorry
          · constructor
            · sorry
            · sorry
        · use r
    exact ⟨w, hw𝒜, i, toLex_inj.mp heq ▸ hi⟩
-/
