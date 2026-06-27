import Mathlib
import CcaInLean.Combo.Cascade

variable {n : ℕ} {m : Fin (n + 1) →₀ ℕ}

lemma lt_def {s t : Fin n →₀ ℕ} : toLex s < toLex t ↔
  ∃ i : Fin n, (∀ j : Fin n, j < i → s j = t j) ∧ (s i) < (t i) := by rfl

/-- Helper lemma for lex lt implies the first entries are le. -/
lemma lt_imp_zero {s t : Fin (n + 1) →₀ ℕ} (hst : toLex s < toLex t) :
    s 0 ≤ t 0 := by
  rw [lt_def] at hst
  obtain ⟨a, ha₁, ha₂⟩ := hst
  by_cases h : a = 0
  · rw [← h]
    exact le_of_lt ha₂
  · exact le_of_eq (ha₁ 0 (Fin.pos_iff_ne_zero.mpr h))

/-- All monomials strictly greater than `m`. -/
def RightSeg (m : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
  {x ∈ Finset.finsuppAntidiag Finset.univ (∑ i, m i) | toLex m < toLex x}

/-- All monomials strictly greater than `m`. -/
def cRightSeg (m : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
  {x ∈ Finset.finsuppAntidiag Finset.univ (∑ i, m i) | toLex m ≤ toLex x}

@[simp]
lemma mem_rightSeg {m x : Fin n →₀ ℕ} : x ∈ RightSeg m
    ↔ ∑ i, x i = ∑ i, m i ∧ toLex m < toLex x := by simp [RightSeg]

@[simp]
lemma mem_crightSeg {m x : Fin n →₀ ℕ} : x ∈ cRightSeg m
    ↔ ∑ i, x i = ∑ i, m i ∧ toLex m ≤ toLex x := by simp [cRightSeg]

@[simp]
lemma not_mem_rightSeg_open {m : Fin n →₀ ℕ} : m ∉ RightSeg m := by
  intro hm
  rw [mem_rightSeg, lt_self_iff_false] at hm
  exact hm.2

lemma crightseg_eq {m : Fin n →₀ ℕ} :
    cRightSeg m = {m} ∪ RightSeg m := by
  ext x
  simp only [mem_crightSeg, le_iff_lt_or_eq, EmbeddingLike.apply_eq_iff_eq, Finset.singleton_union,
    Finset.mem_insert, mem_rightSeg]
  grind only [#63c0, #0658, #2fc3, #0f55]

theorem exists_cRightSeg {k a : ℕ} (hk : k ≤ Nat.multichoose n a)
    (hk0 : k ≠ 0) :
    ∃ m : Fin n →₀ ℕ,
    Finset.card (cRightSeg m) = k ∧ ∑ i, m i = a := by
  rw [← Finset.card_fin n, ← Finset.card_finsuppAntidiag_nat_eq_multichoose] at hk
  unfold cRightSeg
  let s : Finset (Lex (Fin n →₀ ℕ)) := Finset.univ.finsuppAntidiag a
  have : s.card = Nat.multichoose n a := by
    unfold s
    rw [← Finset.card_fin n, ← Finset.card_finsuppAntidiag_nat_eq_multichoose]
    congr 4 <;> simp only [Finset.card_univ, Fintype.card_fin]
  let f := Finset.orderIsoOfFin s this
  have hklt : s.card - k < n.multichoose a := sorry
  let m : (Fin n) →₀ ℕ := (f ⟨s.card - k, hklt⟩).1
  refine ⟨m, ?_, ?_⟩
  · sorry
  · sorry

theorem cRightSeg_mono {x y : Fin n →₀ ℕ} (hxy : toLex x ≤ toLex y) (hsum : ∑ i, x i = ∑ i, y i) :
    cRightSeg y ≤ cRightSeg x := by
  intro i hi
  rw [mem_crightSeg] at hi ⊢
  exact ⟨hsum ▸ hi.1, le_trans hxy hi.2⟩

theorem cRightSeg_total {x y : Fin n →₀ ℕ} (hsum : ∑ i, x i = ∑ i, y i) :
    cRightSeg x ≤ cRightSeg y ∨ cRightSeg y ≤ cRightSeg x := by
  obtain h₁ | h₂ := le_or_gt (toLex x) (toLex y)
  sorry
  sorry

lemma crightseg_card {m : Fin n →₀ ℕ} :
    Finset.card (cRightSeg m) = 1 + Finset.card (RightSeg m) := by
  rw [crightseg_eq, Finset.card_union, Finset.card_singleton,
      Finset.singleton_inter_of_notMem, Finset.card_empty, Nat.sub_zero]
  exact not_mem_rightSeg_open

/-- Members of the right segment which share their first value with `m`. -/
def M0 (m : Fin (n + 1) →₀ ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  {x ∈ Finset.finsuppAntidiag Finset.univ (∑ i, m i) | toLex m < toLex x ∧ x 0 = m 0}

@[simp]
lemma mem_M0 {m x : Fin (n + 1) →₀ ℕ} : x ∈ M0 m
    ↔ ∑ i, x i = ∑ i, m i ∧ toLex m < toLex x ∧ x 0 = m 0 := by
  unfold M0
  simp

/-- Members of the right segment which have first vlaue greater than `m`. -/
def M1 (m : Fin (n + 1) →₀ ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  {x ∈ Finset.finsuppAntidiag Finset.univ (∑ i, m i) | toLex m < toLex x ∧ m 0 < x 0}

@[simp]
lemma mem_M1 {m x : Fin (n + 1) →₀ ℕ} : x ∈ M1 m
    ↔ ∑ i, x i = ∑ i, m i ∧ toLex m < toLex x ∧ m 0 < x 0 := by
  unfold M1
  simp

/-- The sets `M0` and `M1` are disjoint. -/
theorem m_inter : (M0 m) ∩ (M1 m) = ∅ := by
  ext i
  simp [M0, M1]
  exact fun _ _ h _ _ ↦ Nat.le_of_eq h

/-- The sets `M0` and `M1` partition the right segment. -/
theorem m_union : (M0 m) ∪ (M1 m) = RightSeg m := by
  ext i
  simp [M0, M1, RightSeg]
  apply Iff.intro <;> intro ha
  · exact Or.elim ha (fun h ↦ ⟨h.1, h.2.1⟩) (fun h ↦ ⟨h.1, h.2.1⟩)
  · have := le_iff_lt_or_eq.mp (lt_imp_zero ha.2)
    tauto

/-- Cardinality of the right segment is `#M0 + #M1`. -/
theorem card_rightSeg_eq_m : Finset.card (RightSeg m) =
    Finset.card (M0 m) + Finset.card (M1 m) := by
  rw [← m_union, Finset.card_union, m_inter, Finset.card_empty, Nat.sub_zero]

/-- Cardinality of `M1` is given by the number of variables multichoose the remaining
  variables after removing all the ones in the first entry and one more. -/
theorem card_m1 (hm : m 0 + 1 ≤ ∑ i, m i) :
    Finset.card (M1 m) = Nat.multichoose (n + 1) (∑ i, m i - m 0 - 1) := by
  calc
    _ = Finset.card (Finset.finsuppAntidiag (Finset.univ : Finset (Fin (n + 1))) (∑ i, m i - m 0 - 1)) := by
      have (m x : Fin (n + 1) →₀ ℕ) (hmx : m 0 < x 0) : toLex m < toLex x := by
        rw [lt_def]
        use 0
        simp [hmx]
      let f : (Fin (n + 1) →₀ ℕ) → (Fin (n + 1) →₀ ℕ) := fun x ↦ x + Finsupp.single 0 (m 0 + 1)
      have : Finset.image f (Finset.univ.finsuppAntidiag (∑ i, m i - m 0 - 1)) = M1 m := by
        ext i
        simp only [Finset.mem_image, Finset.mem_finsuppAntidiag,
          Finset.subset_univ, and_true, M1, Finset.mem_filter, f]
        constructor <;> intro h
        · obtain ⟨c, hc₁, hc₂⟩ := h
          rw [and_iff_right_of_imp (this m i), ← hc₂]
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
          rw [Finset.sum_add_distrib, Finsupp.univ_sum_single_apply,
            ← Fintype.sum_congr _ _ (congrFun rfl), hc₁, Nat.sub_sub, Nat.sub_add_cancel]
          · exact ⟨rfl, by lia⟩
          · exact hm
        use i - Finsupp.single 0 (m 0 + 1)
        simp only [Finsupp.coe_tsub, Pi.sub_apply]
        rw [Finset.sum_tsub_distrib, ← Fintype.sum_congr _ _ (congrFun rfl), h.1]
        constructor
        · rw [Finsupp.univ_sum_single_apply, Nat.sub_add_eq]
        · apply tsub_add_cancel_of_le
          intro x
          by_cases hx : x = 0 <;> simp [hx, h.2]
        intro x _
        by_cases hx : x = 0 <;> simp [hx, h.2]
      rw [← this, Finset.card_image_iff]
      intro x hx y hy hfxy
      unfold f at hfxy
      exact add_right_cancel hfxy
    _ = _ := by
      rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin]

lemma Finsupp.sum_cons₁ {s : ℕ} {m : Fin n →₀ ℕ} :
    ∑ i, (Finsupp.cons s m) i = s + ∑ i, m i := by
  simp [Fin.sum_univ_succ]

/-- Cardinality of `M0` is the cardinality of the right segment with the first variable
  removed. -/
theorem card_m0 {m : Fin n →₀ ℕ} {s : ℕ} :
    Finset.card (M0 (m.cons s)) = Finset.card (RightSeg m) := by
  have : Finset.image (fun x ↦ (x.cons s)) (RightSeg m) = M0 (m.cons s) := by
    ext i
    constructor <;> intro h
    · obtain ⟨a, ha₁, ha₂⟩ := Finset.mem_image.mp h
      rw [mem_rightSeg] at ha₁
      simp [ha₁, ← ha₂]
      rw [Finsupp.sum_cons₁]
      constructor
      · rw [ha₁.1, Finsupp.sum_cons₁]
      · rw [lt_def] at ⊢ ha₁
        obtain ⟨j, hj₁, hj₂⟩ := ha₁.2
        use j.succ
        simp [hj₂]
        intro k hk
        induction k using Fin.cases with
        | zero => simp
        | succ c => simp [hj₁ _ <| Fin.succ_lt_succ_iff.mp hk]
    · simp at h ⊢
      use i.tail
      rw [← h.2.2, Finsupp.cons_tail]
      obtain ⟨a, ha₁, ha₂⟩ := lt_def.mp h.2.1
      induction a using Fin.cases with
      | zero =>
        by_contra!
        simp [h.2.2] at ha₂
      | succ c =>
        simp at ha₂ ⊢
        constructor
        · suffices i 0 + ∑ j, i.tail j = i 0 + ∑ i, m i from Nat.add_left_cancel this
          calc
            _ = ∑ j, Finsupp.cons (i 0) i.tail j := by rw [Finsupp.sum_cons₁]
            _ = ∑ j, Finsupp.cons s m j := by rw [Finsupp.cons_tail, ← h.1]
            _ = _ := by rw [Finsupp.sum_cons₁, h.2.2]
        · rw [lt_def]
          use c
          constructor
          · intro j hj
            have := ha₁ j.succ (by simp [hj])
            rw [Finsupp.cons_succ] at this
            rw [this, Finsupp.tail_apply]
          · rwa [Finsupp.tail_apply]
  rw [← this, Finset.card_image_iff]
  exact fun _ _ _ _ hfxy ↦ (Finsupp.cons_injective2 hfxy).2

/-- API for dealing with the cardinality of the right segment. -/
theorem card_rightSeg {m : Fin (n + 1) →₀ ℕ} (hm : m 0 + 1 ≤ ∑ i, m i) :
    Finset.card (RightSeg m) =
    Finset.card (RightSeg m.tail) + Nat.multichoose (n + 1) (∑ i, m i - m 0 - 1) := by
  rw [card_rightSeg_eq_m, card_m1]
  · nth_rw 1 [← Finsupp.cons_tail m, card_m0]
  · exact hm

theorem card_rightSeg2 {m : Fin (n + 1) →₀ ℕ} (hm : m 0 + 1 ≤ ∑ i, m i) :
    Finset.card (RightSeg m) =
    Finset.card (RightSeg m.tail) + Nat.choose (n + (∑ i, m i - m 0 - 1)) n := by
  rw [card_rightSeg hm, Nat.multichoose_eq, ← Nat.choose_symm]
  · simp
  · rw [Nat.succ_add_sub_one, le_add_iff_nonneg_left]
    exact Nat.zero_le _

theorem card_cRightSeg_cons {m : Fin (n + 1) →₀ ℕ} (hm : m 0 + 1 ≤ ∑ i, m i) :
    Finset.card (cRightSeg m) =
    Finset.card (cRightSeg m.tail) + Nat.choose ((n + ∑ i, m i - m 0) - 1) n := by
  rw [crightseg_card, crightseg_card, card_rightSeg2 hm, add_assoc]
  lia

theorem cRightSeg_bot (hm : m 0 = ∑ i, m i) :
    cRightSeg m = {m} := by
  ext x
  rw [mem_crightSeg, Finset.mem_singleton]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun h ↦ by simp [h]⟩
  have m_zero : m = Finsupp.single 0 (m 0) := sorry
  obtain hlt | heq := lt_or_eq_of_le h₂
  · obtain ⟨j, hj₁, hj₂⟩ := lt_def.mp hlt
    sorry
  · exact toLex_inj.mp heq.symm

theorem card_cRightSeg_succ {m : Fin (n + 1) →₀ ℕ} (hm : m 0 = ∑ i, m i) (hn : n ≠ 0) :
    Finset.card (cRightSeg m) =
    Finset.card (cRightSeg m.tail) + Nat.choose ((n + ∑ i, m i - m 0) - 1) n := by
  have h : Finset.card (cRightSeg m) = 1 := by
    rw [cRightSeg_bot hm, Finset.card_singleton]
  have htail : Finset.card (cRightSeg m.tail) = 1 := by
    have : m.tail = 0 := by sorry
    sorry
  rw [h, htail, hm, Nat.add_sub_cancel_right, Nat.left_eq_add, Nat.choose_eq_zero_of_lt]
  exact Nat.sub_one_lt hn

theorem card_cRightSeg {m : Fin (n + 1) →₀ ℕ} (hn : n ≠ 0) :
    Finset.card (cRightSeg m) =
    Finset.card (cRightSeg m.tail) + Nat.choose ((n + ∑ i, m i - m 0) - 1) n := by
  have : m 0 ≤ ∑ i, m i :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
  obtain hlt | heq := lt_or_eq_of_le this
  · rw [Nat.lt_iff_add_one_le] at hlt
    exact card_cRightSeg_cons hlt
  · exact card_cRightSeg_succ heq hn

theorem card_cRightSeg_le {m : Fin (n + 1) →₀ ℕ} :
    Finset.card (cRightSeg m) < Nat.choose (n + ∑ i, m i - m 0) n := by
  have : (n + ∑ i, m i - m 0).choose n = (n + 1).multichoose (∑ i, m i - m 0) := by
    rw [← Nat.choose_symm, Nat.multichoose_eq]
    sorry
    sorry
  sorry



/-- Monomials which are given by one variable times the monomials in a set. -/
noncomputable
def shade (s : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  s.biUnion fun m ↦
    Finset.image (fun i ↦ m + Finsupp.single i 1) (Finset.univ)

@[simp]
lemma mem_shade {s : Finset (Fin n →₀ ℕ)} {x : Fin n →₀ ℕ} :
    x ∈ shade s ↔ ∃ y ∈ s, ∃ i, y + Finsupp.single i 1 = x := by simp [shade]

lemma test {s t : Fin n → ℕ} : toLex s ≤ toLex t ↔ toLex s < toLex t ∨ toLex s = toLex t :=
  le_iff_lt_or_eq

lemma lt_gt_lex {a b : Fin n} (hab : a < b) :
    toLex (Finsupp.single b 1 : Fin n →₀ ℕ) < toLex (Finsupp.single a 1) := by
  rw [lt_def]
  use a
  constructor
  · intro j hj
    simp [ne_of_lt hj, ne_of_lt (lt_trans hj hab)]
  · simp [ne_of_lt hab]

lemma le_ge_lex {a b : Fin n} (hab : a ≤ b) :
    toLex (Finsupp.single b 1 : Fin n →₀ ℕ) ≤ toLex (Finsupp.single a 1) := by
  cases lt_or_eq_of_le hab with
  | inl hlt => exact le_of_lt <| lt_gt_lex hlt
  | inr heq => exact heq ▸ le_refl _

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
        | inl hl => left; exact lt_gt_lex hl
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
      rw [← toLex_add, lt_def] at hlt
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
            rw [← toLex_sub, lt_def]
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
              rw [lt_def]
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

theorem card_shade {m : Fin (n + 1) →₀ ℕ} :
    Finset.card (shade (cRightSeg m)) = Macaulay n (Finset.card (cRightSeg m)) := sorry
