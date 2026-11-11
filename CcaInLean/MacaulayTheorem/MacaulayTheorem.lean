import CcaInLean.MacaulayTheorem.iCompression
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FinCases

/-!
# Macaulay's lower-shadow theorem

A counterexample is minimal first in the number of variables, then in cardinality.
The smaller-variable hypothesis controls coordinate compression. Selecting a
colex-minimal counterexample of the same size makes every coordinate compressed.
-/

namespace Macaulay

open Finset

/-- The two minimality conditions serve different parts of the proof. -/
structure MC (m k : ℕ) where
  𝒜 : Finset (Fin m →₀ ℕ)
  degHomo : DegHomogenous 𝒜 k
  varMin : ∀ {n d} {B : Finset (Fin n →₀ ℕ)}, n < m → DegHomogenous B d → MacaulayProp d B
  cardMin : ∀ {B : Finset (Fin m →₀ ℕ)}, DegHomogenous B k → B.card < 𝒜.card → MacaulayProp k B
  counter : ¬ MacaulayProp k 𝒜

/-- Any failure yields a counterexample satisfying both minimality conditions. -/
private theorem exists_MC
    (h : ∃ m k, ∃ A : Finset (Fin m →₀ ℕ), DegHomogenous A k ∧ ¬ MacaulayProp k A) :
    ∃ m k, Nonempty (MC m k) := by
  classical
  obtain ⟨k, A, hA, hbad⟩ := Nat.find_spec h
  have hcard : ∃ s, ∃ B : Finset (Fin (Nat.find h) →₀ ℕ),
      DegHomogenous B k ∧ B.card = s ∧ ¬ MacaulayProp k B :=
    ⟨A.card, A, hA, rfl, hbad⟩
  obtain ⟨B, hB, hsize, hbad⟩ := Nat.find_spec hcard
  refine ⟨Nat.find h, k, ⟨⟨B, hB, ?_, ?_, hbad⟩⟩⟩
  · intro n d C hn hC
    by_contra hfail
    exact (not_le_of_gt hn) (Nat.find_min' h ⟨d, C, hC, hfail⟩)
  · intro C hC hlt
    by_contra hfail
    exact (not_le_of_gt (hsize ▸ hlt)) (Nat.find_min' hcard ⟨C, hC, rfl, hfail⟩)

/-- Deleting a member cannot delete anything from a minimal counterexample's shadow. -/
theorem MC.erase_shadow_eq {m k : ℕ} (c : MC m k) {u : Fin m →₀ ℕ}
    (hu : u ∈ c.𝒜) : Shadow (c.𝒜.erase u) = Shadow c.𝒜 := by
  apply Finset.eq_of_subset_of_card_le (shadow_mono (Finset.erase_subset _ _))
  exact Nat.le_of_lt_succ <| (Nat.lt_of_not_ge c.counter).trans_le
    ((card_shadow_ACompression_erase c.degHomo hu).trans (Nat.add_le_add_right
      (c.cardMin (DegHomogenous.mono c.degHomo (Finset.erase_subset _ _))
        (Finset.card_erase_lt_of_mem hu)) 1))


theorem MC.otherExtension {m k : ℕ} (c : MC m k) {q : Fin m →₀ ℕ} {i : Fin m}
    (h : q + Finsupp.single i 1 ∈ c.𝒜) :
    ∃ j, j ≠ i ∧ q + Finsupp.single j 1 ∈ c.𝒜 := by
  obtain ⟨j, hj⟩ := mem_Shadow.mp
    ((c.erase_shadow_eq h).symm ▸ mem_Shadow.mpr ⟨i, h⟩)
  refine ⟨j, ?_, (Finset.mem_erase.mp hj).2⟩
  rintro rfl
  exact (Finset.mem_erase.mp hj).1 rfl

/-- Here varMin supplies the theorem in one fewer variable, for every degree. -/
theorem MC.iCompression_shadow_le {n k : ℕ} (c : MC (n + 1) k) (i : Fin (n + 1)) :
    (Shadow (iCompression c.𝒜 i k)).card ≤ (Shadow c.𝒜).card :=
  Macaulay.iCompression_shadow_le (fun h ↦ c.varMin (by omega) h) i c.degHomo

theorem MC.iCompression_counter {n k : ℕ} (c : MC (n + 1) k) (i : Fin (n + 1)) :
    ¬ MacaulayProp k (iCompression c.𝒜 i k) := by
  intro h
  apply c.counter
  unfold MacaulayProp ACompression at h ⊢
  rw [← card_iCompression i k (degHomogenous_iff_subset.mp c.degHomo)] at h
  exact h.trans (c.iCompression_shadow_le i)

theorem MC.firstTwoExchange {n k : ℕ} (c : MC (n + 2) k)
    (hs : ∀ q i j, i ≤ j → q + Finsupp.single j 1 ∈ c.𝒜 → q + Finsupp.single i 1 ∈ c.𝒜)
    (q : Fin (n + 2) →₀ ℕ) :
    q + Finsupp.single 0 1 ∈ c.𝒜 ↔ q + Finsupp.single 1 1 ∈ c.𝒜 := by
  constructor
  · intro h
    obtain ⟨j, hj, h⟩ := c.otherExtension h
    exact hs q 1 j (Fin.one_le_of_ne_zero hj) h
  · exact hs q 0 1 (by simp)

theorem MC.firstTwoBlockExchange {n k : ℕ} (c : MC (n + 2) k)
    (hs : ∀ q, q + Finsupp.single 0 1 ∈ c.𝒜 ↔ q + Finsupp.single 1 1 ∈ c.𝒜)
    (q : Fin (n + 2) →₀ ℕ) (r : ℕ) :
    q + Finsupp.single 0 r ∈ c.𝒜 ↔ q + Finsupp.single 1 r ∈ c.𝒜 := by
  induction r generalizing q with
  | zero => simp
  | succ r ih =>
    calc
      _ ↔ (q + Finsupp.single 0 1) + Finsupp.single 0 r ∈ c.𝒜 := by
        simp [Finsupp.single_add, add_comm, add_left_comm]
      _ ↔ (q + Finsupp.single 0 1) + Finsupp.single 1 r ∈ c.𝒜 := ih _
      _ ↔ (q + Finsupp.single 1 r) + Finsupp.single 1 1 ∈ c.𝒜 := by
        simpa only [add_right_comm q (Finsupp.single 0 1) (Finsupp.single 1 r)] using
          hs (q + Finsupp.single 1 r)
      _ ↔ _ := by simp [Finsupp.single_add, add_assoc]


theorem MC.mem_mergeFirstTwo {n k : ℕ} (c : MC (n + 2) k)
    (hs : ∀ q, q + Finsupp.single 0 1 ∈ c.𝒜 ↔ q + Finsupp.single 1 1 ∈ c.𝒜)
    (u : Fin (n + 2) →₀ ℕ) : u ∈ c.𝒜 ↔ mergeFirstTwo u ∈ c.𝒜 := by
  simpa only [Finsupp.erase_add_single] using c.firstTwoBlockExchange hs (u.erase 0) (u 0)

lemma exists_third_coordinate {n : ℕ} (i j : Fin (n + 3)) :
    ∃ p : Fin (n + 3), p ≠ i ∧ p ≠ j := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i, j} : Finset (Fin (n + 3))).card < (Finset.univ : Finset (Fin (n + 3))).card from
      lt_of_le_of_lt Finset.card_le_two (by simp))
  exact ⟨p, by simpa using hp⟩

theorem MC.shifted_of_iCompressed {n k : ℕ} (c : MC (n + 3) k)
    (hc : ∀ i, iCompression c.𝒜 i k = c.𝒜) :
    ∀ q i j, i ≤ j → q + Finsupp.single j 1 ∈ c.𝒜 → q + Finsupp.single i 1 ∈ c.𝒜 := by
  intro q i j hij hj
  obtain ⟨p, hpi, hpj⟩ := exists_third_coordinate i j
  exact iCompression_lower_of_fixed (hc p)
    (by simpa only [Finsupp.sum_add_single_one] using c.degHomo _ hj)
    (by simp [hpi, hpj]) (colex_add_single_le q hij) hj

theorem MC.colexInitial_of_iCompressed {n k : ℕ} (c : MC (n + 3) k)
    (hc : ∀ i, iCompression c.𝒜 i k = c.𝒜) : ColexInitial c.𝒜 := by
  intro u v hu hd hle
  have hm := c.mem_mergeFirstTwo (c.firstTwoExchange (c.shifted_of_iCompressed hc))
  apply (hm v).mpr
  exact iCompression_lower_of_fixed (hc 0)
    (by rw [mergeFirstTwo_sum, hd]; exact c.degHomo _ hu) (by simp)
    (mergeFirstTwo_colex_mono hd hle) ((hm u).mp hu)

/-- Among equal-size counterexamples choose a colex minimum. Compression can
only decrease colex, so this representative is fixed by every compression. -/
theorem MC.exists_iCompressed {n k : ℕ} (c : MC (n + 1) k) :
    ∃ b : MC (n + 1) k, ∀ i, iCompression b.𝒜 i k = b.𝒜 := by
  classical
  let bad := (Finset.univ.finsuppAntidiag k : Finset (Fin (n + 1) →₀ ℕ)).powerset.filter
    (fun B ↦ B.card = c.𝒜.card ∧ ¬ MacaulayProp k B)
  have hc : c.𝒜 ∈ bad := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (degHomogenous_iff_subset.mp c.degHomo), rfl, c.counter⟩
  obtain ⟨B, hB, hmin⟩ := bad.exists_min_image
    (fun B ↦ toColex (B.image toColex)) ⟨c.𝒜, hc⟩
  obtain ⟨hd, hcard, hbad⟩ : DegHomogenous B k ∧ B.card = c.𝒜.card ∧ ¬ MacaulayProp k B := by
    simpa only [bad, Finset.mem_filter, Finset.mem_powerset, ← degHomogenous_iff_subset] using hB
  let b : MC (n + 1) k :=
    ⟨B, hd, c.varMin, fun h hlt ↦ c.cardMin h (hcard ▸ hlt), hbad⟩
  refine ⟨b, fun i ↦ ?_⟩
  have hi : iCompression B i k ∈ bad := by
    simp only [bad, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨iCompression_subset i k,
      (card_iCompression i k (degHomogenous_iff_subset.mp hd)).symm.trans hcard,
      b.iCompression_counter i⟩
  simpa only [image_colex] using toColex_inj.mp
    (le_antisymm (iCompression_colex_le i (degHomogenous_iff_subset.mp hd)) (hmin _ hi))

/-- A minimal counterexample deforms to a compressed one, which is initial. -/
theorem MC.false {m k : ℕ} (c : MC m k) : False := by
  cases m with
  | zero => exact c.counter (by simp [MacaulayProp])
  | succ n =>
    obtain ⟨b, hb⟩ := c.exists_iCompressed
    apply b.counter
    have hinit : ColexInitial b.𝒜 := by
      cases n with
      | zero =>
        intro u v hu hd _
        have : v = u := Finsupp.ext fun i ↦ by fin_cases i; simpa using hd
        simpa [this] using hu
      | succ n =>
        cases n with
        | zero =>
          have hs (q : Fin 2 →₀ ℕ) :
              q + Finsupp.single 0 1 ∈ b.𝒜 ↔ q + Finsupp.single 1 1 ∈ b.𝒜 := by
            constructor <;> intro h <;> obtain ⟨j, hj, hq⟩ := b.otherExtension h <;>
              fin_cases j <;> simp_all
          intro u v hu hd _
          apply (b.mem_mergeFirstTwo hs v).mpr
          rw [mergeFirstTwo_eq_of_tail hd (fun j ↦ Fin.elim0 j)]
          exact (b.mem_mergeFirstTwo hs u).mp hu
        | succ n => exact b.colexInitial_of_iCompressed hb
    unfold MacaulayProp
    rw [← colexInitial_eq_compression b.degHomo hinit]

/-- Colex initial segments minimize the lower shadow in every degree. -/
theorem macaulay_shadow {m k : ℕ} {A : Finset (Fin m →₀ ℕ)}
    (hA : DegHomogenous A k) : MacaulayProp k A := by
  by_contra hbad
  obtain ⟨m, k, ⟨c⟩⟩ := exists_MC ⟨m, k, A, hA, hbad⟩
  exact c.false

#print axioms macaulay_shadow

end Macaulay
