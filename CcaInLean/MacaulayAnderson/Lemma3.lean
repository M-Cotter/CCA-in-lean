import Mathlib
import CcaInLean.MacaulayAnderson.Lemma1
import CcaInLean.MacaulayAnderson.Lemma2

namespace Finset
open LocallyFiniteOrder

variable {k n : ℕ} {a v : Fin n →₀ ℕ} (i : Fin n) {j : Fin n} {𝒜 : Finset (Fin n →₀ ℕ)}

noncomputable
def iOneShadow (v : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
    {f ∈ finsetIcc 0 v | f + Finsupp.single i 1 = v}

noncomputable
def OneShadow (𝒜 : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
    𝒜.biUnion fun v ↦ (iOneShadow i v)

@[simp]
lemma mem_iOneShadow :
    a ∈ iOneShadow i v ↔ a + Finsupp.single i 1 = v := by
  simp [iOneShadow]
  intro rfl
  exact Finset.mem_Icc.mpr (by norm_num)

@[simp]
lemma mem_OneShadow :
    a ∈ OneShadow i 𝒜 ↔ a + Finsupp.single i 1 ∈ 𝒜 := by
  simp [OneShadow]

lemma shadow_eq₀ :
    Shadow 𝒜 = Finset.univ.biUnion (fun i ↦ OneShadow i 𝒜) := by
  ext x
  simp

noncomputable
def iNotShadow (v : Fin n →₀ ℕ) : Finset (Fin n →₀ ℕ) :=
    {f ∈ finsetIcc 0 v | ∃ j ≠ i, f + Finsupp.single j 1 = v}

noncomputable
def NotShadow (𝒜 : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
    𝒜.biUnion fun v ↦ iNotShadow i v

@[simp]
lemma mem_iNotShadow :
    a ∈ iNotShadow i v ↔ ∃ j ≠ i, a + Finsupp.single j 1 = v := by
  simp [iNotShadow]
  intro x _ rfl
  apply Finset.mem_Icc.mpr
  simp

@[simp]
lemma mem_NotShadow :
    a ∈ NotShadow i 𝒜 ↔ ∃ j ≠ i, a + Finsupp.single j 1 ∈ 𝒜 := by
  simp [NotShadow, and_comm]

lemma iPart_Shadow_eq :
    iPart (Shadow 𝒜) i k =
    OneShadow i (iPart 𝒜 i (k + 1)) ∪ NotShadow i (iPart 𝒜 i k) := by
  ext x
  simp
  constructor
  · intro ⟨⟨j, hj₀⟩, hj₁⟩
    by_cases! hij : i = j
    · left
      rw [hij, ← hj₁, hij]
      exact ⟨hj₀, rfl⟩
    · right
      refine ⟨j, hij.symm, hj₀, ?_⟩
      simp [hij, hj₁]
  · rintro (h | ⟨j, hj, hj₀⟩)
    exact ⟨⟨i, h.1⟩, h.2⟩
    refine ⟨⟨j, ?_⟩, ?_⟩
    exact hj₀.1
    simp [hj] at hj₀
    exact hj₀.2
