import CcaInLean.MacaulayAnderson.Shadow

/-!
# Compression

This file contains lemmas about the compressino of a family of monomials, which
is the colex initial segment of the same cardinality as that family. We also
prove facts about the `i`-compression, which is obtained by compressing the

-/

namespace Macaulay

variable {X : Type*} {L : List X} {n : ℕ} {S 𝒜 : Finset (Fin n →₀ ℕ)}
  {C : Finset <| Colex <| Fin n →₀ ℕ} {k : ℕ}

open Finset

/-- Compression will take a Finset of `n`-vectors and a natural `k` and return the first
  `k` elements of that set. -/
def Compression (S : Finset (Fin n →₀ ℕ)) (k : ℕ) : Finset (Fin n →₀ ℕ) :=
  List.toFinset <| S.image toColex |>.sort.take k

/-- Auxiliary lemma that take has no duplicates if your original list does. -/
lemma List.take_nodup (hL : L.Nodup) : (L.take k).Nodup := by grind

/-- Cardinality of the compression equals `k` when `k` is less that `#S`. -/
lemma card_compression (hk : k ≤ S.card) : (Compression S k).card = k := by
  rw [Compression, List.card_toFinset,
      List.dedup_eq_self.mpr, List.length_take, inf_of_le_left]
  · apply le_trans hk
    rw [← card_image_of_injective S (fun _ _ a ↦ a)]
    apply le_of_eq
    have : (S.image toColex |>.sort).length = (S.image toColex).card := length_sort fun a b ↦ a ≤ b
    tauto
  · exact List.take_nodup <| (S.image toColex).sort_nodup _

/-- If a vector `i` is a member of `S` then it also a member of `S` sorted (as a list). -/
lemma mem_toColex_sort {i : Fin n →₀ ℕ} (hi : i ∈ S) : i ∈ (S.image toColex |>.sort) :=
  (mem_sort fun a b ↦ a ≤ b).mpr <| (Function.Injective.mem_finset_image fun _ _ a ↦ a).mpr hi

/-- A vector `i` is in the first `k` elements iff its index is less than `k`. -/
lemma mem_colex_take {i : Fin n →₀ ℕ} (hi : i ∈ S) :
    i ∈ (List.take k (S.image toColex |>.sort) : List (Fin n →₀ ℕ))
    ↔ (S.image toColex |>.sort).idxOf i < k := by
  have : i ∈ (List.take k (S.image toColex |>.sort) : List (Fin n →₀ ℕ)) ↔
      i ∈ List.take k (S.image toColex |>.sort) := by trivial
  rw [this, ← (List.mem_take_iff_idxOf_lt _)]
  · rfl
  · exact mem_toColex_sort hi

/-- This is annoying, but it is necessary later. Just says the coercion works. -/
lemma image_colex : image toColex S = S := by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨a, ha⟩ ↦ ha.2 ▸ ha.1, fun h ↦ ⟨x, h, rfl⟩⟩

/-- Definition of compression. -/
lemma mem_compression_iff {i : Fin n →₀ ℕ} (hi : i ∈ S) :
    i ∈ Compression S k ↔ (S.image toColex |>.sort).idxOf i < k := by
  simp [Compression, mem_colex_take hi]

lemma mem_compression {i : Fin n →₀ ℕ} (hi : i ∈ Compression S k) : i ∈ S := by
  simp [Compression] at hi
  apply List.mem_of_mem_take at hi
  have h₁ : i ∈ (image (toColex) S) ↔ i ∈ (image (toColex) S).sort :=
    Iff.symm (mem_sort fun a b ↦ a ≤ b)
  have h₂ : i ∈ S ↔ i ∈ (image (toColex) S) :=
    (Function.Injective.mem_finset_image fun ⦃a₁ a₂⦄ a ↦ a).symm
  rw [h₂, h₁]
  trivial

/-- Compression with respect to a set is a subset of that set. -/
lemma compression_subset : Compression S k ≤ S :=
   fun _ hi ↦ mem_compression hi

variable {i j : Fin n →₀ ℕ}

-- The next four lemmas are just some crap about idxOf being monotone for our sorted list.
-- There has to be a better way
lemma sort_idxOf_strict_mono (hi : i ∈ S) (hj : j ∈ S) :
    (S.image toColex |>.sort).idxOf i < (S.image toColex |>.sort).idxOf j →
    toColex i < toColex j := by
  intro hij
  let L := (S.image toColex |>.sort)
  have hilt := List.idxOf_lt_length_iff.mpr <| mem_toColex_sort hi
  have hjlt := List.idxOf_lt_length_iff.mpr <| mem_toColex_sort hj
  rw [← show L.get ⟨List.idxOf i L, hilt⟩ = i from List.idxOf_get hilt,
      ← show L.get ⟨List.idxOf j L, hjlt⟩ = j from List.idxOf_get hjlt]
  exact (sortedLT_sort _) <| Fin.mk_lt_mk.mpr hij

lemma sort_idxOf_mono (hi : i ∈ S) (hj : j ∈ S) :
    (S.image toColex |>.sort).idxOf i ≤ (S.image toColex |>.sort).idxOf j →
    toColex i ≤ toColex j := by
  intro hij
  cases lt_or_eq_of_le hij with
  | inl hlt => exact le_of_lt <| sort_idxOf_strict_mono hi hj hlt
  | inr heq => exact le_of_eq <| (List.idxOf_inj <| mem_toColex_sort hi).mp heq

lemma idxOf_sort_mono (hi : i ∈ S) (hj : j ∈ S) :
    toColex i ≤ toColex j →
    (S.image toColex |>.sort).idxOf i ≤ (S.image toColex |>.sort).idxOf j
    := by
  contrapose!
  exact sort_idxOf_strict_mono hj hi

lemma idxOf_sort_stirct_mono (hi : i ∈ S) (hj : j ∈ S) :
    toColex i < toColex j →
    (S.image toColex |>.sort).idxOf i < (S.image toColex |>.sort).idxOf j
    := by
  contrapose!
  exact sort_idxOf_mono hj hi

/-- Compression is a lower Finset. -/
lemma lower_set_compression (hij : toColex i ≤ toColex j) (hi : i ∈ S) (hj : j ∈ S) :
    j ∈ Compression S k → i ∈ Compression S k := by
  simp only [Compression, List.mem_toFinset]
  intro hjC
  rw [mem_colex_take hi]
  rw [mem_colex_take hj] at hjC
  exact lt_of_le_of_lt (idxOf_sort_mono hi hj hij) hjC

lemma compression_mono {j k : ℕ} (hjk : j ≤ k) :
    Compression S j ≤ Compression S k := by
  intro a ha
  have : a ∈ S := mem_compression ha
  rw [mem_compression_iff] at ha ⊢
  · omega
  · exact this
  · exact this

-- Shit code
lemma compression_self_card : Compression S S.card = S := by
  unfold Compression
  have hS : #S = ((image (toColex) S).sort).length := by
    rw [length_sort]
    apply (Finset.card_image_iff.mpr _).symm
    exact Function.Injective.injOn fun _ _ a ↦ a
  calc
    _ = (((image (toColex) S).sort).take _).toFinset := by rw [hS]; rfl
    _ = _  := by rw [List.take_length, sort_toFinset, image_colex]

/-- Cardinality of the compression is equal to the minimum of the cardinality of the
  university set and the number taken. -/
lemma card_compression_min :
    (Compression S k).card = min S.card k := by
  cases le_or_gt k S.card with
  | inl hle =>
    rw [inf_of_le_right hle, card_compression hle]
  | inr hgt =>
    rw [inf_of_le_left (le_of_lt hgt)]
    apply le_antisymm <| card_le_card compression_subset
    nth_rw 1 [← @compression_self_card _ S]
    exact Finset.card_le_card <| compression_mono <| le_of_lt hgt

/-- Compression is nonempty when `k` is positive. -/
lemma compression_nonempty (hk : 0 < k) (hS : S.Nonempty) :
    (Compression S k).Nonempty := by
  rw [← Finset.card_ne_zero, Nat.ne_zero_iff_zero_lt, card_compression_min]
  simp [hk, hS]

def CompressionSup (hk : 0 < k) (hS : S.Nonempty) : Fin n →₀ ℕ :=
  ofColex <| Finset.max' ((Compression S k).image toColex) <|
    Finset.image_nonempty.mpr (compression_nonempty hk hS)

lemma compression_le_sup {v : Fin n →₀ ℕ} (hk : 0 < k) (hS : S.Nonempty)
    (hv : v ∈ Compression S k) :
    toColex v ≤ toColex (CompressionSup hk hS) := by
  simp [CompressionSup]
  exact Finset.le_max' _ _ <| Finset.mem_image.mpr ⟨v, hv, rfl⟩

lemma compression_sup_mem (hk : 0 < k) (hS : S.Nonempty) :
    (CompressionSup hk hS) ∈ Compression S k := by
  have : (toColex <| CompressionSup hk hS) ∈
      (Compression S k).image toColex := by
    simp only [CompressionSup, toColex_ofColex, Finset.max'_mem]
  simp_all only [mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]

lemma mem_compression_iff_sup {v : Fin n →₀ ℕ} (hk : 0 < k) (hS : S.Nonempty)
    (hv : v ∈ S) :
    v ∈ Compression S k ↔ toColex v ≤ toColex (CompressionSup hk hS) := by
  constructor <;> intro h
  · exact compression_le_sup _ _ h
  · apply lower_set_compression h hv
      (mem_compression <| compression_sup_mem hk hS)
    exact compression_sup_mem hk hS

@[simp]
lemma mem_image_colex {a : Colex (Fin n →₀ ℕ)}
    : a ∈ image (⇑toColex) S ↔
      ofColex a ∈ S := by
    rw [mem_image]
    refine ⟨fun ⟨c, hc₁, hc₂⟩ ↦ ?_, fun h ↦ ⟨_, h, toColex_ofColex _ ▸ rfl⟩⟩
    rwa [← hc₂, ofColex_toColex]

def ACompression (𝒜 : Finset (Fin n →₀ ℕ)) (k : ℕ) : Finset (Fin n →₀ ℕ) :=
  Compression (Finset.univ.finsuppAntidiag k) 𝒜.card

lemma card_ACompression (h𝒜 : 𝒜 ≤ Finset.univ.finsuppAntidiag k) :
    #(ACompression 𝒜 k) = 𝒜.card := by
  simp [ACompression, card_compression (card_mono h𝒜)]

-- Lemmas

lemma compression_contraction {S T : Finset (Fin n →₀ ℕ)} (hST : S ≤ T)
    (hS : S.Nonempty) :
    toColex ((Compression T S.card).image toColex) ≤ toColex (S.image toColex) := by
  apply Finset.Colex.toColex_le_toColex.mpr
  intro a haC haS
  let b := (S.image toColex).max' (Finset.image_nonempty.mpr hS)
  have heq : Compression T #S ≠ S := by
    apply Membership.mem.ne_of_notMem'
    use mem_image_colex.mp haC
    contrapose! haS
    rwa [mem_image_colex]
  have hb : b ∉ image (⇑toColex) (Compression T #S) := by
    contrapose! heq
    obtain ⟨c, hc⟩ := mem_image.mp heq
    symm
    apply (Finset.subset_iff_eq_of_card_le _).mp
    · intro x hx
      apply lower_set_compression
      · rw [hc.2]
        apply Finset.le_max'
        apply Finset.mem_image.mpr
        use x
      · exact hST hx
      · exact mem_compression hc.1
      · exact hc.1
    · rw [card_compression]
      exact Finset.card_le_card hST
  have hab : a < b := by
    contrapose! hb
    rw [mem_image_colex] at ⊢ haC
    apply lower_set_compression
    · simpa
    · apply hST
      unfold b
      rw [← mem_image_colex]
      · apply Finset.max'_mem
    · exact mem_compression haC
    · exact haC
  exact ⟨b, Finset.max'_mem _ _, hb, le_of_lt hab⟩

variable {ι α : Type*} [LinearOrder α] [DecidableEq α] (I : Finset ι) (A B : ι → Finset α)

/-- biUnions are monotone over the toColex ordering. -/
theorem toColex_biUnion_le_toColex_biUnion
    (hB : (I : Set ι).PairwiseDisjoint B)
    (hAB : ∀ i ∈ I, toColex (A i) ≤ toColex (B i)) :
    toColex (I.biUnion A) ≤ toColex (I.biUnion B) := by
  rw [Finset.Colex.toColex_le_toColex]
  intro a haA haB
  obtain ⟨i, hi, hai⟩ := mem_biUnion.mp haA
  let M := I.biUnion fun j ↦ A j \ B j
  have haM : a ∈ M := mem_biUnion.mpr ⟨i, hi, by grind⟩
  obtain ⟨j, hj, hmj⟩ := mem_biUnion.mp (max'_mem M ⟨a, haM⟩)
  obtain ⟨hmA, hmB⟩ := mem_sdiff.mp hmj
  obtain ⟨b, hbB, hbA, hmb⟩ :=
    (Finset.Colex.toColex_le_toColex.mp (hAB j hj)) hmA hmB
  have hmb₁ := lt_of_le_of_ne hmb (fun h => hbA (h ▸ hmA))
  have hbI : b ∉ I.biUnion A := by
    intro hbA
    obtain ⟨k, hk, hkA⟩ := mem_biUnion.mp hbA
    apply not_lt_of_ge (Finset.le_max' M b _) hmb₁
    refine Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_sdiff.mpr ⟨hkA, ?_⟩⟩
    exact fun hb ↦ (by grind : k ≠ j) (hB.elim_finset hk hj b hb hbB)
  exact ⟨b, Finset.mem_biUnion.mpr ⟨j, hj, hbB⟩, hbI, by simp_all⟩

theorem compression_colexInitial {n : ℕ} (d k : ℕ) :
    ColexInitial (Compression (Finset.univ.finsuppAntidiag d :
      Finset (Fin n →₀ ℕ)) k) := by
  intro u v hu hdeg hle
  have huU := mem_compression hu
  have hvU : v ∈ (Finset.univ.finsuppAntidiag d : Finset (Fin n →₀ ℕ)) := by
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨hdeg.trans (Finset.mem_finsuppAntidiag.mp huU).1, Finset.subset_univ _⟩
  exact lower_set_compression hle hvU huU hu
