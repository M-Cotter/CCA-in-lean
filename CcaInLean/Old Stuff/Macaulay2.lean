import CcaInLean.MacaulayAnderson.Shadow
import CcaInLean.MacaulayAnderson.Compression
import CcaInLean.MacaulayAnderson.iCompression

open Finset

namespace Macaulay

variable {n k : ℕ} (𝒜 : Finset (Fin n →₀ ℕ)) (u : Fin n →₀ ℕ)

def MacaulayProp (k : ℕ) : Prop :=
  (Shadow (ACompression 𝒜 k)).card ≤ (Shadow 𝒜).card

def DegHomogenous (k : ℕ) : Prop :=
  ∀ a ∈ 𝒜, ∑ i, a i = k

structure MC where
  m : ℕ
  k : ℕ
  𝒜 : Finset (Fin m →₀ ℕ)
  degHomo : DegHomogenous 𝒜 k
  cardMin : ∀ ℬ ≤ 𝒜, MacaulayProp ℬ k
  counter : ¬MacaulayProp 𝒜 k

variable (C : MC)

lemma minimal_counter_erase_shadow :
    ∀ u ∈ C.𝒜, Shadow (C.𝒜.erase u) = Shadow C.𝒜 := by
  intro u hu
  have hm : MacaulayProp (C.𝒜.erase u) C.k := C.cardMin _ (Finset.erase_subset u C.𝒜)
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  exact @_root_.shadow_mono _ _ _ u (Finset.erase_subset u C.𝒜)
  have := C.counter
  unfold MacaulayProp at this hm
  have : #(Shadow (ACompression (C.𝒜) C.k)) ≤
    #(Shadow (ACompression (C.𝒜.erase u) C.k)) + 1 := by
    sorry
  omega

example (a : (Fin C.m →₀ ℕ)) (i : Fin C.m) (hai : a + Finsupp.single i 1 ∈ C.𝒜) :
    ∃ j ≠ i, a + Finsupp.single j 1 ∈ C.𝒜 := by
  have ha : a ∈ Shadow C.𝒜 := mem_Shadow.mpr ⟨i, hai⟩
  rw [← minimal_counter_erase_shadow _ _ hai] at ha
  obtain ⟨j, hj⟩ := mem_Shadow.mp ha
  have hj' := Finset.mem_erase.mp hj
  refine ⟨j, ?_, hj'.2⟩
  intro hji
  subst j
  exact hj'.1 rfl

end Macaulay
