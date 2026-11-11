import CcaInLean.MacaulayAnderson.Compression

namespace Macaulay

open Finset

variable {n : ℕ} (i : Fin n) (k l m : ℕ) {S : Finset (Fin n →₀ ℕ)}

/-- Part of a Finset `S` of vectors whose `i`th entry is `k`. -/
def iPart (S : Finset (Fin n →₀ ℕ)) (i : Fin n) (k : ℕ) := {v ∈ S | v i = k}

@[simp]
lemma mem_iPart {i : Fin n} {k : ℕ} {v : Fin n →₀ ℕ} :
    v ∈ iPart S i k ↔ v ∈ S ∧ v i = k := by simp [iPart]

/-- Given an index `i` all the `i`-parts make the whole `S`. -/
lemma union_iPart_eq_self {i : Fin n} :
    (S.image (fun v ↦ v i)).biUnion (fun k ↦ iPart S i k) = S := by
  ext v
  simp
  exact fun h ↦ ⟨v, h, rfl⟩

lemma iPart_disjoint₀ {i : Fin n} (v : Fin n →₀ ℕ)
    (hvi : v ∈ iPart S i k) (hvj : v ∈ iPart S i l) : k = l := by
  simp at hvi hvj
  rw [← hvi.2, hvj.2]

lemma iPart_disjoint {i : Fin n} :
    (S.image (fun v ↦ v i) : Set ℕ).PairwiseDisjoint (fun k ↦ iPart S i k) := by
  intro k hk j hj hjk
  apply disjoint_left.mpr
  intro a ha
  contrapose! hjk
  apply iPart_disjoint₀ _ _ a ha hjk

/-- The set of elements on an antidiagonal whose `i`th entry is `k`. -/
def iUniv : Finset (Fin n →₀ ℕ) := {x ∈ (Finset.univ.finsuppAntidiag m) | x i = k}

@[simp]
lemma mem_iUniv (x : Fin n →₀ ℕ) :
    x ∈ iUniv i k m ↔ x ∈ (Finset.univ.finsuppAntidiag m) ∧ x i = k := by
  simp [iUniv]

lemma iPart_le_iUniv (hS : S ⊆ Finset.univ.finsuppAntidiag m)
    : iPart S i k ≤ iUniv i k m := by
  intro x
  simp
  exact fun hxS hxi ↦ ⟨mem_finsuppAntidiag.mp (hS hxS) |>.1, hxi⟩

/-- Compression of a set by its `i`th entry along an antidiagonal. -/
def iCompression (S : Finset (Fin n →₀ ℕ)) (i : Fin n) (m : ℕ)
      : Finset (Fin n →₀ ℕ) :=
    (S.image (fun v ↦ v i)).biUnion (fun k ↦
      Compression (iUniv i k m) (iPart S i k).card
    )

lemma iCompression_disjoint : ((image (fun v ↦ v i) S) : Set ℕ).PairwiseDisjoint
    fun k ↦ Compression (iUniv i k m) #(iPart S i k) := by
  intro k hk j hj hjk
  apply disjoint_left.mpr
  intro a ha
  contrapose! hjk
  simp at ha hjk
  apply mem_compression at ha
  apply mem_compression at hjk
  simp at ha hjk
  rw [← ha.2, ← hjk.2]

lemma card_iCompression (hS : S ⊆ (Finset.univ.finsuppAntidiag m)) :
    S.card = (iCompression S i m).card := by
  rw [iCompression, Finset.card_biUnion]
  nth_rw 1 [← @union_iPart_eq_self _ S, Finset.card_biUnion]
  apply sum_congr
  · gcongr
  · intro x hx
    rw [card_compression]
    exact Finset.card_mono (iPart_le_iUniv i x m hS)
  · exact iPart_disjoint
  · exact iCompression_disjoint _ _

lemma iUniv_subset :
    iUniv i k m ⊆ Finset.univ.finsuppAntidiag m := by
  simp [iUniv]

lemma iCompression_subset :
    iCompression S i m ⊆ (Finset.univ.finsuppAntidiag m) := by
  unfold iCompression
  apply Finset.biUnion_subset.mpr
  intro x hx
  apply subset_trans
  apply compression_subset
  exact iUniv_subset _ _ _

lemma mem_iCompression {a : Fin n →₀ ℕ} (ha : a ∈ iCompression S i m)
    (hak : a i = k) : a ∈ iUniv i k m := by
  simp [iCompression] at ⊢ ha
  obtain ⟨x, hx₁, hx₂⟩ := ha
  apply mem_compression at hx₂
  simp at hx₂
  exact ⟨hx₂.1, by gcongr⟩

lemma iCompression_iLower
    {a b : Fin n →₀ ℕ} {i : Fin n} {k m : ℕ} (habi : a i = b i)
    (hab : toColex a ≤ toColex b) (haU : a ∈ iUniv i k m)
    (hbC : b ∈ iCompression S i m)
    : a ∈ iCompression S i m := by
  simp [iCompression] at ⊢ hbC
  obtain ⟨x, hx₁, hx₂⟩ := hbC
  refine ⟨x, hx₁, lower_set_compression hab ?_ (mem_compression hx₂) hx₂⟩
  convert haU
  apply mem_compression at hx₂
  rw [← (mem_iUniv _ _ _ _ |>.mp hx₂).2, ← habi, (mem_iUniv _ _ _ _ |>.mp haU).2]

theorem iCompression_colex_le {n m : ℕ} {S : Finset (Fin n →₀ ℕ)}
    (i : Fin n) (hS : S ⊆ Finset.univ.finsuppAntidiag m) :
    toColex ((iCompression S i m).image toColex) ≤ toColex (S.image toColex) := by
  nth_rw 2 [← @union_iPart_eq_self _ S i]
  rw [iCompression, Finset.biUnion_image, Finset.biUnion_image]
  apply toColex_biUnion_le_toColex_biUnion _ _ _
  · intro j hj k hk hjk
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro a haj hak
    simp only [mem_image_colex, mem_iPart] at haj hak
    exact hjk (haj.2.symm.trans hak.2)
  · intro j hj
    apply compression_contraction (iPart_le_iUniv i j m hS)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨v, mem_iPart.mpr ⟨hv, rfl⟩⟩

end Macaulay
