import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Finsupp.Lex
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Push

/-!
# Shadow

This file contains definitions and lemmas about shadows of families of monomials.

## Main definitions

* The shadow of a set of monomials, i.e. the set of monomials given by dividing
  each monomial in the family by any variable. `Shadow`

## Main results

* The shadow of a colex initial segment is the colex initial segment
  `Shadow_leftSeg_eq_leftSeg`

* Removing a single monomial from a colex initial segment removes at most one
    element from the shadow. `shadow_erase_subset_insert`

-/

open LocallyFiniteOrder

variable {n : ℕ} {m : Fin (n + 1) →₀ ℕ} {𝒜 ℬ : Finset (Fin n →₀ ℕ)}

def cLeftSeg (m : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
  {x ∈ Finset.finsuppAntidiag Finset.univ (∑ i, m i) | toColex x ≤ toColex m}

@[simp]
lemma mem_cLeftSeg {m x : Fin n →₀ ℕ} : x ∈ cLeftSeg m
    ↔ ∑ i, x i = ∑ i, m i ∧ toColex x ≤ toColex m := by simp [cLeftSeg]

/-- Shadow of a single monomial. -/
noncomputable
def iShadow (v : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
    {f ∈ finsetIcc 0 v | ∃ i : Fin n, f + Finsupp.single i 1 = v}

/-- Lower shadow of a family of monomials. -/
noncomputable
def Shadow (𝒜 : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) := 𝒜.biUnion iShadow

/-- Member of the Shadow if and only if -/
@[simp]
lemma mem_Shadow {v : Fin n →₀ ℕ} :
    v ∈ Shadow 𝒜 ↔ ∃ i : Fin n, (v + Finsupp.single i 1) ∈ 𝒜 := by
  simp [Shadow, iShadow]
  refine Iff.intro (fun ⟨i, hi⟩ ↦ ⟨i, hi.1⟩) ?_
  exact fun ⟨i, hi⟩ ↦ ⟨i, hi, by  simp [finset_mem_Icc]⟩

/-- Shadow is monotone. -/
lemma shadow_mono (h𝒜 : 𝒜 ⊆ ℬ) : Shadow 𝒜 ⊆ Shadow ℬ :=
  fun _ hx ↦ mem_Shadow.mpr ((mem_Shadow.mp hx).imp fun _ hi ↦ h𝒜 hi)

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
    toColex (Finsupp.single i 1) < toColex (Finsupp.single j 1) :=
  Finsupp.Colex.single_lt_iff.mpr hij

lemma Colex_single_le_single {i j : Fin n} (hij : i ≤ j) :
    toColex (Finsupp.single i 1) ≤ toColex (Finsupp.single j 1) :=
  Finsupp.Colex.single_le_iff.mpr hij

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


namespace Macaulay

/-- Every monomial in the family has total degree k. -/
def DegHomogenous (A : Finset (Fin n →₀ ℕ)) (k : ℕ) : Prop :=
  ∀ a ∈ A, (∑ i, a i) = k

theorem degHomogenous_iff_subset {k : ℕ} :
    DegHomogenous 𝒜 k ↔ 𝒜 ⊆ Finset.univ.finsuppAntidiag k := by
  simp [DegHomogenous, Finset.subset_iff]

theorem DegHomogenous.mono {k : ℕ} (h : DegHomogenous ℬ k) (hsub : 𝒜 ⊆ ℬ) :
    DegHomogenous 𝒜 k := fun a ha ↦ h a (hsub ha)

end Macaulay

@[simp] lemma Finsupp.sum_add_single_one (a : Fin n →₀ ℕ) (i : Fin n) :
    (∑ j, (a + Finsupp.single i 1 : Fin n →₀ ℕ) j) = (∑ j, a j) + 1 := by
  simp [Finset.sum_add_distrib]

theorem Macaulay.DegHomogenous.shadow {k : ℕ} (h : Macaulay.DegHomogenous 𝒜 k) :
    Macaulay.DegHomogenous (Shadow 𝒜) (k - 1) := by
  intro a ha
  obtain ⟨i, hi⟩ := mem_Shadow.mp ha
  simpa only [Finsupp.sum_add_single_one, Nat.add_sub_cancel] using congrArg (fun t : ℕ ↦ t - 1) (h _ hi)

@[simp] theorem shadow_fin_zero (A : Finset (Fin 0 →₀ ℕ)) : Shadow A = ∅ := by
  ext a
  simp

lemma colex_add_single_le (a : Fin n →₀ ℕ) {i j : Fin n} (h : i ≤ j) :
    toColex (a + Finsupp.single i 1) ≤ toColex (a + Finsupp.single j 1) := by
  simpa only [toColex_add] using add_le_add (le_refl (toColex a)) (Colex_single_le_single h)

/-- A family is initial among monomials of the same degree. -/
def ColexInitial (A : Finset (Fin n →₀ ℕ)) : Prop :=
  ∀ {u v}, u ∈ A → (∑ i, v i) = (∑ i, u i) → toColex v ≤ toColex u → v ∈ A

lemma cLeftSeg_colexInitial (a : Fin n →₀ ℕ) : ColexInitial (cLeftSeg a) :=
  fun hu hd hle ↦ mem_cLeftSeg.mpr
    ⟨hd.trans (mem_cLeftSeg.mp hu).1, hle.trans (mem_cLeftSeg.mp hu).2⟩

/-- To test shadow membership in an initial family, try the first variable. -/
theorem ColexInitial.mem_shadow_iff {C : Finset (Fin (n + 1) →₀ ℕ)} (hC : ColexInitial C)
    {q : Fin (n + 1) →₀ ℕ} : q ∈ Shadow C ↔ q + Finsupp.single 0 1 ∈ C := by
  refine ⟨?_, fun h ↦ mem_Shadow.mpr ⟨0, h⟩⟩
  intro h
  obtain ⟨i, hi⟩ := mem_Shadow.mp h
  exact hC hi (by simp only [Finsupp.sum_add_single_one]) (colex_add_single_le q (Fin.zero_le i))

/-- Only the first-variable divisor can disappear when a monomial is erased. -/
theorem shadow_erase_subset_insert {C : Finset (Fin (n + 1) →₀ ℕ)} (hC : ColexInitial C)
    (u : Fin (n + 1) →₀ ℕ) :
    Shadow C ⊆ insert (u - Finsupp.single 0 1) (Shadow (C.erase u)) := by
  intro q hq
  by_cases h : q + Finsupp.single 0 1 = u
  · simp [← h]
  · exact Finset.mem_insert_of_mem (mem_Shadow.mpr
      ⟨0, Finset.mem_erase.mpr ⟨h, hC.mem_shadow_iff.mp hq⟩⟩)

theorem shadow_erase_card_le {C : Finset (Fin (n + 1) →₀ ℕ)} (hC : ColexInitial C)
    (u : Fin (n + 1) →₀ ℕ) : (Shadow C).card ≤ (Shadow (C.erase u)).card + 1 :=
  (Finset.card_le_card (shadow_erase_subset_insert hC u)).trans (Finset.card_insert_le _ _)

/-- The largest divisor of the endpoint is obtained by deleting its first factor. -/
theorem Shadow_leftSeg_eq_leftSeg (hm : m ≠ 0) :
    Shadow (cLeftSeg m) = cLeftSeg (Shadow_sup hm) := by
  let j := m.support.min' (Finsupp.support_nonempty_iff.mpr hm)
  have hj : Shadow_sup hm + Finsupp.single j 1 = m :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (Finset.min'_mem _ _))))
  have hz (i : Fin (n + 1)) (hi : i < j) : Shadow_sup hm i = 0 := by
    have : i ∉ m.support := fun h ↦ hi.not_ge (Finset.min'_le _ _ h)
    simp [Shadow_sup, Finsupp.notMem_support_iff.mp this]
  have htail (i : Fin (n + 1)) (hi : j < i) : m i = Shadow_sup hm i := by
    simpa [Finsupp.single_apply, hi.ne, hi.ne.symm] using
      (congrArg (fun u : Fin (n + 1) →₀ ℕ ↦ u i) hj).symm
  ext q
  constructor
  · intro h
    obtain ⟨hd, hle⟩ := mem_cLeftSeg.mp ((ColexInitial.mem_shadow_iff (cLeftSeg_colexInitial m)).mp h)
    have hdeg : (∑ i, q i) = ∑ i, Shadow_sup hm i := by
      rw [Shadow_sup_size]
      simpa only [Finsupp.sum_add_single_one, Nat.add_sub_cancel] using congrArg (fun t : ℕ ↦ t - 1) hd
    refine mem_cLeftSeg.mpr ⟨hdeg, le_of_not_gt ?_⟩
    rintro ⟨i, heq, hlt⟩
    have hji : j < i := by
      by_contra! hij
      apply (ne_of_lt hlt)
      apply congrArg (fun u : Fin (n + 1) →₀ ℕ ↦ u i)
      refine Finsupp.eq_if_le_eq_sum hdeg.symm fun a ↦ ?_
      rcases lt_trichotomy a i with ha | rfl | ha
      · simp [hz a (ha.trans_le hij)]
      · exact hlt.le
      · rw [heq a ha]
    have hq (i : Fin (n + 1)) (hi : j < i) : (q + Finsupp.single 0 1 : Fin (n + 1) →₀ ℕ) i = q i := by
      simp [((Fin.zero_le j).trans_lt hi).ne]
    exact hle.not_gt (Finsupp.Colex.lt_def.mpr
      ⟨i, fun a ha ↦ by rw [htail a (hji.trans ha), hq a (hji.trans ha)]; exact heq a ha,
        by rw [htail i hji, hq i hji]; exact hlt⟩)
  · intro h
    obtain ⟨hd, hle⟩ := mem_cLeftSeg.mp h
    exact mem_Shadow.mpr ⟨j, mem_cLeftSeg.mpr ⟨by rw [← hj]; simp only [Finsupp.sum_add_single_one, hd],
      by rw [← hj, toColex_add, toColex_add]; exact add_le_add hle le_rfl⟩⟩
