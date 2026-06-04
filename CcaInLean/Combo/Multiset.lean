/-
import Mathlib.Data.Finsupp.Lex
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Pi.Interval
import Mathlib.Order.SupClosed
-/
import Mathlib

/-- `c` is the maximum value of each variable, and `m` is the maximum in the lex.
  So that makes this the set of multisets which are less than `c` in every entry
  (while having the same multicardinality as `m`), and less than `m` lexicograpically. -/
noncomputable
def initfSeg {n : ℕ} (c m : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  {f ∈ LocallyFiniteOrder.finsetIcc 0 c | ∑ i, f i = ∑ i, m i ∧ toLex f ≤ toLex m}

variable {n : ℕ} (r : ℕ) (c m : Fin n → ℕ)

@[simp]
lemma mem_initSeg (t : Fin n → ℕ) :
    t ∈ initfSeg c m ↔ t ≤ c ∧ ∑ i, t i = ∑ i, m i ∧ toLex t ≤ toLex m := by
  simp [initfSeg, LocallyFiniteOrder.finset_mem_Icc]

@[simp]
lemma mem_initSeg_self (hm : m ≤ c) : m ∈ initfSeg c m := by simpa

def IsFixed (r : ℕ) (𝒜 : Finset (Fin n → ℕ)) : Prop :=
   (∀ s ∈ 𝒜, s ≤ c ∧ ∑ i, s i = r)

def IsInitSeg (𝒜 : Finset (Fin n → ℕ)) : Prop :=
  ∀ s t : Fin n → ℕ, s ∈ 𝒜 → t ≤ c ∧ toLex t ≤ toLex s ∧ ∑ i, t i = ∑ i, s i → t ∈ 𝒜

@[simp]
lemma isInitSeg_empty : IsInitSeg c (∅ : Finset (Fin n → ℕ)) := by simp [IsInitSeg]

lemma IsInitSeg.total (𝒜₁ 𝒜₂ : Finset (Fin n → ℕ)) (h𝒜₁ : IsInitSeg m 𝒜₁)
    (h𝒜₁f : IsFixed m r 𝒜₁) (h𝒜₂ : IsInitSeg m 𝒜₂) (h𝒜₂f : IsFixed m r 𝒜₂) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ := by
  simp_rw [← Finset.sdiff_eq_empty_iff_subset]
  by_contra! h
  obtain ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [Finset.mem_sdiff] at hs ht
  have : ∑ i, s i = ∑ i, t i := by
    rw [(h𝒜₁f s hs.1).2, (h𝒜₂f t ht.1).2]
  obtain hst | hst := le_total (toLex s) (toLex t)
  · exact hs.2 <| h𝒜₂ t s ht.1 ⟨(h𝒜₁f s hs.1).1, hst, this⟩
  · exact ht.2 <| h𝒜₁ s t hs.1 ⟨(h𝒜₂f t ht.1).1, hst, this.symm⟩

lemma isInitSeg_initfSeg : IsInitSeg c (initfSeg c m) := by
  unfold IsInitSeg
  intro s t hs ha
  rw [mem_initSeg] at ⊢ hs
  exact ⟨ha.1, ha.2.2 ▸ hs.2.1, le_trans ha.2.1 hs.2.2⟩

lemma isFixed_initfSeg : IsFixed c (∑ i, m i) (initfSeg c m) := by
  intro s hs
  rw [mem_initSeg] at hs
  exact ⟨hs.1, hs.2.1⟩

lemma IsInitSeg.exists_initSeg (𝒜 : Finset (Fin n → ℕ)) (h𝒜 : IsInitSeg c 𝒜) (h𝒜f : IsFixed c r 𝒜)
  (h𝒜₀ : 𝒜.Nonempty) : ∃ a : Fin n → ℕ, ∑ i, a i = r ∧ 𝒜 = initfSeg c a := by
  obtain hs := Finset.sup'_mem (ofLex ⁻¹' SetLike.coe 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toLex
    (fun a ha ↦ by simpa using ha)
  refine ⟨_, (h𝒜f _ hs).2, ?_⟩
  ext t
  rw [mem_initSeg]
  constructor <;> intro h
  · exact ⟨(h𝒜f t h).1, (h𝒜f t h).2 ▸ ((h𝒜f _ hs).2).symm, Finset.le_sup' _ h⟩
  · simp [h𝒜 _ _ hs, h]

def iShadow (v : Fin n → ℕ) : Finset (Fin n → ℕ) :=
    {f ∈ LocallyFiniteOrder.finsetIcc 0 v | ∃ i : Fin n, f + Pi.single i 1 = v}

def Shadow (𝒜 : Finset (Fin n → ℕ)) : Finset (Fin n → ℕ) := 𝒜.biUnion iShadow

lemma toLex.zero_eq_bot : (0 : Lex (Fin n → ℕ)) = ⊥ := ofLex_inj.mp rfl

theorem toLex.le_self_add {a b : Fin n → ℕ} : toLex a ≤ toLex (a + b) := by
  nth_rw 1 [toLex_add, ← add_zero (toLex a)]
  apply add_le_add_right _
  exact toLex.zero_eq_bot ▸ OrderBot.bot_le _

theorem toLex.le_add_self {a b : Fin n → ℕ} : toLex a ≤ toLex (b + a) := by
  rw [add_comm]
  exact le_self_add

lemma shadow_le_self {v : Fin n → ℕ} : ∀ i ∈ iShadow v, toLex i ≤ toLex v := by
  simp only [iShadow, Finset.mem_filter]
  exact fun i ⟨_, _, hx⟩ ↦ hx.symm ▸ toLex.le_self_add

lemma mem_shadow_iff {v : Fin n → ℕ} {s : Finset (Fin n → ℕ)} :
    v ∈ Shadow s ↔ ∃ i : Fin n, (v + Pi.single i 1) ∈ s := by
  unfold Shadow iShadow
  simp only [Finset.mem_biUnion, Finset.mem_filter, ↓existsAndEq, and_true]
  apply Iff.intro
  · exact fun ⟨i, hi⟩ ↦ ⟨i, hi.1⟩
  refine fun ⟨i, hi⟩ ↦ ⟨i, hi, ?_⟩
  simp [@LocallyFiniteOrder.finset_mem_Icc]

lemma lt_def {s t : Fin n → ℕ} : toLex s < toLex t ↔
  ∃ i : Fin n, (∀ j : Fin n, j < i → s j = t j) ∧ (s i) < (t i) := by rfl

-- Something horrible is going on with the lt here
lemma test {s t : Fin n → ℕ} : toLex s ≤ toLex t ↔ toLex s < toLex t ∨ toLex s = toLex t :=
  le_iff_lt_or_eq

theorem fixed_shadow_fixed (𝒜 : Finset (Fin n → ℕ)) (h𝒜f : IsFixed c (r + 1) 𝒜) :
    IsFixed c r (Shadow 𝒜) := by
  intro s hs
  rcases mem_shadow_iff.mp hs with ⟨a, ha⟩
  constructor
  · exact le_trans le_self_add (h𝒜f _ ha).1
  · rw [← @Nat.add_right_cancel_iff _ _ 1, show ∑ i, s i + 1 =
      ∑ i, (s + (Pi.single a 1 : Fin n → ℕ)) i by simp [Pi.add_apply, Finset.sum_add_distrib]]
    exact (h𝒜f _ ha).2

example (𝒜 : Finset (Fin n → ℕ)) (h𝒜 : IsInitSeg c 𝒜) (h𝒜f : IsFixed c (r + 1) 𝒜) :
    IsInitSeg c (Shadow 𝒜) := by
  intro s t hs ⟨htc, hts, hSum⟩
  rw [mem_shadow_iff] at ⊢ hs
  rcases hs with ⟨i, hsi⟩
  obtain htc | heq := test.mp hts
  · rcases lt_def.mp htc with ⟨f, hf, htsa⟩
    rcases le_or_gt i f with hfi | hif
    · have : toLex (t + Pi.single i 1) ≤ toLex (s + Pi.single i 1) := by
        rw [toLex_add, toLex_add]
        exact add_le_add_left (le_of_lt htc) _
      use i
      apply h𝒜 _ _ hsi
      constructor
      · sorry
      · constructor
        · sorry
        · sorry
    · sorry
  · exact ⟨i, toLex_inj.mp heq ▸ hsi⟩


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
  · intro s t hs ⟨htc, hts, hSum⟩
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


def iCompact (r j : ℕ) (i : Fin n) (𝒜 : Finset (Fin n → ℕ)) : Prop :=
    ∀ s t : Fin n → ℕ, s ∈ 𝒜 → t ≤ c ∧ toLex t ≤ toLex s ∧ ∑ i, t i = r ∧ t i = j → t ∈ 𝒜

#check CanonicallyOrderedAdd
