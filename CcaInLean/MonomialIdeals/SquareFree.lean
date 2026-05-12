import CcaInLean.MonomialIdeals.Monomial
import CcaInLean.MonomialIdeals.MinimalGenerators

import Mathlib

variable {σ R : Type*} [CommRing R] [Nontrivial R] [DecidableEq σ]

open MvPolynomial
namespace Monomial

noncomputable
def SqFreeMono [DecidableEq σ] : Finset σ → (σ →₀ ℕ) :=
  fun s ↦
    {
      support := s
      toFun := Set.indicator s (fun x ↦ 1)
      mem_support_toFun := by simp only [ne_eq, Set.indicator_apply_eq_zero, SetLike.mem_coe,
        one_ne_zero, imp_false, Decidable.not_not, implies_true]
    }

noncomputable
def SquareFreeIdeal (σ R : Type*) (S : Set (Finset σ))
    [CommRing R] [Nontrivial R] [DecidableEq σ] : Ideal (MvPolynomial σ R) :=
  MonomialIdeal σ R (SqFreeMono '' S)

theorem sq_free_mono_le_iff (a b : Finset σ) :
    SqFreeMono a ≤ SqFreeMono b ↔ a ⊆ b := by
  unfold SqFreeMono
  constructor <;> intro h x
  · intro hxa
    unfold Set.indicator LE.le Finsupp.instLE  at h
    dsimp at h
    have : (if x ∈ a then 1 else 0) ≤ if x ∈ ↑b then 1 else 0 := by
      simp only [SetLike.mem_coe] at h; apply h
    simp only [hxa, ↓reduceIte] at this
    by_cases hb : x ∈ b
    · exact hb
    · simp only [hb, ↓reduceIte, nonpos_iff_eq_zero, one_ne_zero] at this
  · simp only [Finsupp.coe_mk]
    by_cases hxa : x ∈ a
    · simp [SetLike.mem_coe, hxa, h hxa]
    · simp [SetLike.mem_coe, hxa]

theorem sq_free_mono_mem_iff (S : Set (Finset σ)) (sf : Finset σ) :
    (∃ s ∈ S, s ⊆ sf) ↔ (SqFreeMono sf : MvPolynomial σ R) ∈ SquareFreeIdeal σ R S := by
  unfold SquareFreeIdeal
  rw [mem_monomial_ideal_iff]
  constructor <;> rintro ⟨a, ha⟩
  · use SqFreeMono a
    constructor
    · rw [Set.mem_image]
      exact ⟨a, ha.1, rfl⟩
    · rw [sq_free_mono_le_iff]
      exact ha.2
  · rcases ha.1 with ⟨b, hb⟩
    use b
    constructor
    · exact hb.1
    · intro x hx
      rw [← hb.2, sq_free_mono_le_iff] at ha
      exact ha.2 hx

noncomputable
def MonoRoot (m : σ →₀ ℕ) : σ →₀ ℕ :=
  {
    support := m.support
    toFun := fun x ↦ if m x = 0 then 0 else 1
    mem_support_toFun := by simp only [Finsupp.mem_support_iff, ne_eq, ite_eq_left_iff, one_ne_zero,
      imp_false, Decidable.not_not, implies_true]
  }

lemma mono_le_mono_root_le {σ : Type*} (m n : σ →₀ ℕ) :
    m ≤ n → MonoRoot m ≤ n := by
  intro hmn i
  by_cases h : m i = 0
  · unfold MonoRoot
    simp only [Finsupp.coe_mk, h, ↓reduceIte, zero_le]
  · unfold MonoRoot
    simp only [Finsupp.coe_mk, h, ↓reduceIte]
    calc
      1 ≤ m i := Nat.one_le_iff_ne_zero.mpr h
      _ ≤ n i := hmn i

lemma mono_root_le {σ : Type*} (m : σ →₀ ℕ) :
    MonoRoot m ≤ m := mono_le_mono_root_le _ _ (le_refl _)

theorem monomial_ideal_le_monomial_ideal_mono_root {σ : Type*} (s : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R s ≤ MonomialIdeal σ R (MonoRoot '' s) := by
  rw [← monomial_ideal_le_monomial_ideal]
  intro m hm
  simp only [Set.mem_image, exists_exists_and_eq_and]
  use m
  exact ⟨hm, mono_le_mono_root_le _ _ (le_refl m)⟩

theorem mono_root_le_iff (m n : σ →₀ ℕ) :
    (∃ k : ℕ, n ≤ k • m) ↔ MonoRoot n ≤ m := by
  constructor <;> intro h
  · intro i
    rcases h with ⟨c, hc⟩
    unfold MonoRoot
    rw [Finsupp.coe_mk]
    by_cases hni : n i = 0
    · rw [if_pos hni]
      omega
    · rw [if_neg hni]
      have : 1 ≤ c * m i := by
        calc
          1 ≤ n i := by simpa only [Nat.one_le_iff_ne_zero]
          _ ≤ c * m i := hc i
      rw [Nat.one_le_iff_ne_zero] at this ⊢
      intro hmi
      apply this
      rw [hmi, mul_zero]
  · use n.support.sup n
    intro i
    by_cases hni : n i = 0
    · rw [hni]
      exact Nat.zero_le _
    · rw [@Finsupp.nsmul_apply, smul_eq_mul]
      have a1 : MonoRoot n i = 1 := by
        unfold MonoRoot
        simpa only [Finsupp.coe_mk, ite_eq_right_iff, zero_ne_one, imp_false]
      have : 1 ≤ m i := by rw [← a1]; apply h
      calc
        _ ≤ n.support.sup n := by
          apply Finset.le_sup
          rwa [Finsupp.mem_support_iff, ne_eq]
        _ ≤ n.support.sup n * m i := Nat.le_mul_of_pos_right (n.support.sup ⇑n) (this)

theorem mem_radical_monomial_iff (s : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) :
    (m : MvPolynomial σ R) ∈ Ideal.radical (MonomialIdeal σ R s) ↔
    ∃ x ∈ s, MonoRoot x ≤ m := by
  rw [Ideal.mem_radical_iff]
  constructor <;> rintro ⟨n, hn⟩
  · rw [monomial_pow, one_pow, mem_monomial_ideal_iff] at hn
    rcases hn with ⟨l, hl⟩
    use l
    rw [← mono_root_le_iff]
    exact ⟨hl.1, n, hl.2⟩
  · rw [← mono_root_le_iff] at hn
    rcases hn.2 with ⟨k, hk⟩
    use k
    rw [monomial_pow, one_pow, mem_monomial_ideal_iff]
    exact ⟨n, hn.1, hk⟩

theorem mono_root_mono_root (m : σ →₀ ℕ) :
    MonoRoot (MonoRoot m) = MonoRoot m := by
  unfold MonoRoot
  simp only [Finsupp.coe_mk, ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not]

variable [DecidableEq σ]

theorem mono_root_sqfreemono (s : Finset σ) :
    MonoRoot (SqFreeMono s) = SqFreeMono s := by
  unfold MonoRoot SqFreeMono Set.indicator
  simp only [SetLike.mem_coe, Finsupp.coe_mk, ite_eq_right_iff, one_ne_zero, imp_false,
    Finsupp.mk.injEq, true_and]
  ext x
  grind only

theorem monomial_ideal_homogeneous [DecidableEq R] (s : Set (σ →₀ ℕ)) :
    Ideal.IsHomogeneous (AddMonoidAlgebra.grade R) (MonomialIdeal σ R s) := by
  rw [Ideal.IsHomogeneous.iff_exists]
  use {x | ∃ m ∈ s,
    x = ⟨monomial m (1 : R), by
      use m
      intro n hn
      rw [MvPolynomial.finsupp_support_eq_support, MvPolynomial.support_monomial] at hn
      simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hn
      rwa [id]⟩}
  unfold MonomialIdeal
  congr
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Subtype.mk.injEq, exists_and_left,
    exists_prop, exists_eq_right_right]
  constructor <;> intro h
  · constructor
    · tauto
    · rcases h with ⟨a, ha⟩
      use a
      simp only [Submodule.mem_mk, id_eq, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      intro n hn
      rw [MvPolynomial.finsupp_support_eq_support, ← ha.2, MvPolynomial.support_monomial] at hn
      simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hn
      exact hn
  · tauto

open Classical in
theorem homogeneous_implies_monomial_ideal {k : Type*} [Field k] (I : Ideal (MvPolynomial σ k)) :
    Ideal.IsHomogeneous (AddMonoidAlgebra.grade k) I →
    ∃ (s : Set (σ →₀ ℕ)), I = MonomialIdeal σ k s := by
  intro hHomI
  rcases (Ideal.IsHomogeneous.iff_exists _ _).mp hHomI with ⟨A, hA⟩
  unfold SetLike.homogeneousSubmonoid at A
  unfold SetLike.IsHomogeneousElem at A
  have : ∀ a ∈ A, ∃ (i : σ →₀ ℕ), ∃ (r : k),
    a.1 ≠ 0 → r ≠ 0 ∧ a = monomial i r := by
    intro a ha
    rcases a.2 with ⟨b, hb⟩
    simp only [Submodule.mem_mk, id_eq, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hb
    use b, (a.1 b)
    intro haneqzero
    have : a.1 = (monomial b) (a.1 b) := by
      ext x
      simp only [coeff_monomial]
      by_cases h : b = x
      · simp only [h, ↓reduceIte]
        rfl
      · simp only [h, ↓reduceIte, Finsupp.mem_support_iff] at hb ⊢
        apply byContradiction (fun b ↦ by apply h; rwa [hb x])
    exact ⟨fun hab ↦ by apply haneqzero; rw [this, hab, MvPolynomial.monomial_eq_zero], this⟩
  let B := {m : σ →₀ ℕ | ∃ a ∈ A, ∃ r : k, r ≠ 0 ∧ a = monomial m r}
  use B
  rw [hA]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    rcases hx with ⟨a, ha⟩
    rw [← ha.2]
    rcases this a ha.1 with ⟨c, r, hc⟩
    by_cases h : a.1 = 0
    · rw [h, SetLike.mem_coe]
      apply Ideal.zero_mem
    rw [(hc h).2, SetLike.mem_coe]
    apply monomial_mem_monomial_ideal _
    · exact ⟨a, ha.1, r, hc h⟩
    · exact le_refl c
  · rw [Ideal.span_le]
    intro m hm
    rcases hm with ⟨a, ha⟩
    rw [← ha.2]
    simp only [SetLike.mem_coe]
    rcases ha.1 with ⟨c, hcA, d, hd⟩
    apply Ideal.span_mono
    · change {c.1} ⊆ Subtype.val '' A
      simpa only [Set.singleton_subset_iff, Set.mem_image, SetLike.coe_eq_coe, exists_eq_right,
        ne_eq, Subtype.forall, Submodule.mem_mk, Finsupp.mem_support_iff, id_eq,
        AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
        Submonoid.mem_mk, Subsemigroup.mem_mk, forall_exists_index]
    · rw [← Ideal.submodule_span_eq, Submodule.mem_span_singleton]
      use C d⁻¹
      rw [hd.2, monomial_eq, smul_eq_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀]
      · rw [← monomial_eq]
      · exact hd.1

theorem MvPolynomial.pow_support (p : MvPolynomial σ R) (n : ℕ) :
    (p ^ n).support ≤
    {x : σ →₀ ℕ | ∃ f : Fin n → (σ →₀ ℕ), (∀ i, f i ∈ p.support) ∧ ∑ i, f i = x} := by
  induction n with
  | zero =>
    rw [pow_zero, support_one]
    intro xi hxi
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hxi
    simp only [IsEmpty.forall_iff, Finset.univ_eq_empty, Finset.sum_empty,
      true_and, exists_const, Set.setOf_eq_eq_singleton', hxi, Set.mem_singleton_iff]
  | succ k hk =>
    intro xi hxi
    rw [Set.mem_setOf_eq]
    rw [pow_succ] at hxi
    apply support_mul at hxi
    rw [Finset.mem_add] at hxi
    rcases hxi with ⟨a, ha, b, hb, hab⟩
    rcases hk ha with ⟨f, hf⟩
    use Fin.snoc f b
    constructor
    · intro i
      cases i using Fin.lastCases
      · rwa [Fin.snoc_last]
      · rw [Fin.snoc_castSucc]
        exact hf.1 _
    · rw [@Fin.sum_snoc, hf.2, hab]

def SupportGen (p : MvPolynomial σ R) (s : Set (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
    {m ∈ s | ∃ mi ∈ p.support, m ≤ mi}

example (p : MvPolynomial σ R) (s : Set (σ →₀ ℕ)) : Finite (SupportGen p s) := by
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

lemma test (p : MvPolynomial σ R) (s : Set (σ →₀ ℕ)) :
    ∃ n : ℕ, (MonomialIdeal σ R (SupportGen p (MonoRoot '' s))) ^ n ≤
      MonomialIdeal σ R s := by
    let T : Set ℕ := ⨆ m ∈ p.support, ⨆ i ∈ m.support, {m i}
    have : Finite T := by
      unfold T
      apply Set.Finite.biUnion
      exact Finset.finite_toSet p.support
      intro m hm
      apply Set.Finite.biUnion
      exact Finset.finite_toSet m.support
      intro i hi
      exact Set.finite_singleton (m i)
    let Tfin : Finset ℕ := Set.toFinset T
    let q := Finset.max' Tfin sorry
    sorry

theorem monomial_ideal_le_mono_root (s : Set (σ →₀ ℕ)) :
    MonomialIdeal σ R s ≤ MonomialIdeal σ R (MonoRoot '' s) := by
  rw [← monomial_ideal_le_monomial_ideal]
  exact fun m ms ↦ ⟨MonoRoot m, Set.mem_image_of_mem MonoRoot ms, mono_root_le m⟩

theorem monomial_ideal_radical_eq (s : Set (σ →₀ ℕ)) :
    Ideal.radical (MonomialIdeal σ R s) =
    Ideal.radical (MonomialIdeal σ R (MonoRoot '' s)) := by
  apply le_antisymm
  · apply Ideal.radical_mono
    exact monomial_ideal_le_monomial_ideal_mono_root s
  · intro p hp
    rw [Ideal.mem_radical_iff] at hp
    rcases hp with ⟨k, hk⟩
    rw [mem_monomial_ideal_iff_mem_support_gen] at hk
    rcases test p s with ⟨n, hn⟩
    have : p ^ (k * n) ∈ MonomialIdeal σ R (SupportGen p (MonoRoot '' s)) ^ n := by
      rw [pow_mul]
      apply Ideal.pow_mem_pow
      sorry
    rw [Ideal.mem_radical_iff]
    use k * n
    apply hn
    exact this

/-
theorem pow_support_contains1 [IsReduced R] (p : MvPolynomial σ R) (n : ℕ) :
    ∀ x ∈ p.support, n • x ∈ (p ^ n).support := by
  intro xi hxi
  have : coeff (n • xi) (p ^ n) = (coeff xi p) ^ n := by
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, zero_smul, coeff_one]
      simp only [↓reduceIte]
    | succ k hk =>
      sorry
  rw [mem_support_iff, this, ne_eq, pow_eq_zero_iff']
  simp only [ne_eq, not_and, Decidable.not_not]
  intro hxi1
  rw [mem_support_iff] at hxi
  contradiction

theorem pow_support_contains [IsReduced R] (p : MvPolynomial σ R) (n : ℕ) :
    ∀ x ∈ p.support, ∃ y ∈ (p ^ n).support, y = n • x := by
  sorry

example [IsReduced R] (s : Set (σ →₀ ℕ)) :
    Ideal.radical (MonomialIdeal σ R s) = MonomialIdeal σ R (MonoRoot '' s) := by
  apply le_antisymm
  · intro p hp
    rcases Ideal.mem_radical_iff.mp hp with ⟨k, hk⟩
    rw [mem_ideal_span_monomial_image]
    intro xi hxi
    rcases pow_support_contains p k xi hxi with ⟨a, hap, hak⟩
    rw [mem_ideal_span_monomial_image] at hk
    rcases hk a hap with ⟨b, hb⟩
    use MonoRoot b
    constructor
    · rw [Set.mem_image]
      exact ⟨b, hb.1, rfl⟩
    · rw [← mono_root_le_iff]
      use k
      rw [← hak]
      exact hb.2
  · rw [monomial_ideal_radical_eq]
    exact Ideal.radical_le_radical_iff.mp (Ideal.radical_mono (le_refl _))
-/
