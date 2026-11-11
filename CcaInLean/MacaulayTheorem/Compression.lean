import CcaInLean.MacaulayTheorem.Shadow
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.GCongr
/-!
# Colex compression

Compression, its cardinality and order properties, and the ACompression benchmark.
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

/-- Sorting and taking a prefix gives the expected cardinality. -/
lemma card_compression_min : (Compression S k).card = min S.card k := by
  rw [Compression, List.toFinset_card_of_nodup (α := Fin n →₀ ℕ)
    (List.take_nodup (k := k) ((S.image toColex).sort_nodup (fun a b ↦ a ≤ b))),
    List.length_take]
  exact (congrArg (min k) (Finset.length_sort (s := S.image toColex) (fun a b ↦ a ≤ b))).trans
    (by rw [Finset.card_image_of_injective S (f := toColex) toColex.injective, min_comm])

lemma card_compression (hk : k ≤ S.card) : (Compression S k).card = k := by
  rw [card_compression_min, min_eq_right hk]

/-- If a vector `i` is a member of `S` then it also a member of `S` sorted (as a list). -/
lemma mem_toColex_sort {i : Fin n →₀ ℕ} (hi : i ∈ S) : i ∈ (S.image toColex |>.sort) :=
  (mem_sort fun a b ↦ a ≤ b).mpr <| (Function.Injective.mem_finset_image fun _ _ a ↦ a).mpr hi

/-- A vector `i` is in the first `k` elements iff its index is less than `k`. -/
lemma mem_colex_take {i : Fin n →₀ ℕ} (hi : i ∈ S) :
    i ∈ (List.take k (S.image toColex |>.sort) : List (Fin n →₀ ℕ))
    ↔ (S.image toColex |>.sort).idxOf i < k :=
  List.mem_take_iff_idxOf_lt (mem_toColex_sort hi)

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
  unfold Compression at hi
  exact (Function.Injective.mem_finset_image (fun _ _ h ↦ h)).mp
    ((Finset.mem_sort (fun a b : Colex (Fin n →₀ ℕ) ↦ a ≤ b)).mp
      (List.mem_of_mem_take (List.mem_toFinset.mp hi)))

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

lemma compression_self_card : Compression S S.card = S :=
  Finset.eq_of_subset_of_card_le compression_subset (by rw [card_compression le_rfl])

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


lemma compression_contraction {S T : Finset (Fin n →₀ ℕ)} (hST : S ⊆ T) :
    toColex ((Compression T S.card).image toColex) ≤ toColex (S.image toColex) := by
  apply Finset.Colex.toColex_le_toColex.mpr
  intro a haC haS
  simp only [mem_image_colex] at haC haS
  obtain ⟨b, hb, hbC⟩ : ∃ b ∈ S, b ∉ Compression T S.card := by
    by_contra! h
    apply haS
    rwa [Finset.eq_of_subset_of_card_le h (by rw [card_compression (card_mono hST)])]
  refine ⟨toColex b, by simpa, by simpa, ?_⟩
  by_contra! h
  exact hbC (lower_set_compression (by simpa using h.le) (hST hb)
    (mem_compression haC) haC)

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
    exact fun hb ↦ (Finset.disjoint_left.mp (hB hk hj (by grind))) hb hbB
  exact ⟨b, Finset.mem_biUnion.mpr ⟨j, hj, hbB⟩, hbI, (Finset.le_max' M a haM).trans hmb⟩

theorem compression_colexInitial {n : ℕ} (d k : ℕ) :
    ColexInitial (Compression (Finset.univ.finsuppAntidiag d :
      Finset (Fin n →₀ ℕ)) k) := by
  intro u v hu hdeg hle
  have huU := mem_compression hu
  have hvU : v ∈ (Finset.univ.finsuppAntidiag d : Finset (Fin n →₀ ℕ)) := by
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨hdeg.trans (Finset.mem_finsuppAntidiag.mp huU).1, Finset.subset_univ _⟩
  exact lower_set_compression hle hvU huU hu

/-- The shadow-minimizing assertion, using the user's global compression. -/
def MacaulayProp (k : ℕ) (A : Finset (Fin n →₀ ℕ)) : Prop :=
  (Shadow (ACompression A k)).card ≤ (Shadow A).card

theorem ACompression_homogeneous (A : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    DegHomogenous (ACompression A k) k :=
  degHomogenous_iff_subset.mpr fun _ ha ↦ mem_compression ha

theorem ACompression_colexInitial (A : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    ColexInitial (ACompression A k) := compression_colexInitial k A.card

/-- Taking a shadow preserves the initial-segment property. -/
theorem ColexInitial.shadow (hA : ColexInitial 𝒜) : ColexInitial (Shadow 𝒜) := by
  intro u v hu hd hle
  obtain ⟨i, hi⟩ := mem_Shadow.mp hu
  exact mem_Shadow.mpr ⟨i, hA hi (by sorry)
    (by rw [toColex_add, toColex_add]; exact add_le_add hle le_rfl)⟩

theorem ColexInitial.comparable {A B : Finset (Fin n →₀ ℕ)} {d : ℕ}
    (hA : ColexInitial A) (hB : ColexInitial B)
    (hdA : DegHomogenous A d) (hdB : DegHomogenous B d) : A ⊆ B ∨ B ⊆ A := by
  by_contra! h
  obtain ⟨a, ha, haB⟩ := Finset.not_subset.mp h.1
  obtain ⟨b, hb, hbA⟩ := Finset.not_subset.mp h.2
  exact (le_total (toColex a) (toColex b)).elim
    (fun h ↦ haB (hB hb ((hdA a ha).trans (hdB b hb).symm) h))
    (fun h ↦ hbA (hA ha ((hdB b hb).trans (hdA a ha).symm) h))

theorem colexInitial_eq_compression {d : ℕ} (hd : DegHomogenous S d)
    (hS : ColexInitial S) : S = ACompression S d := by
  obtain h | h := ColexInitial.comparable hS (ACompression_colexInitial S d)
    hd (ACompression_homogeneous S d)
  · exact Finset.eq_of_subset_of_card_le h
      (card_ACompression (degHomogenous_iff_subset.mp hd)).le
  · exact (Finset.eq_of_subset_of_card_le h
      (card_ACompression (degHomogenous_iff_subset.mp hd)).ge).symm

/-- Erasing one monomial changes the benchmark shadow by at most one. -/
theorem card_shadow_ACompression_erase {d : ℕ} (hS : DegHomogenous S d)
    {u : Fin n →₀ ℕ} (hu : u ∈ S) :
    (Shadow (ACompression S d)).card ≤ (Shadow (ACompression (S.erase u) d)).card + 1 := by
  cases n with
  | zero => simp
  | succ n =>
    let C := ACompression S d
    let P := ACompression (S.erase u) d
    have hPC : P ⊆ C := compression_mono Finset.card_erase_le
    have hC : C.card = S.card := card_ACompression (degHomogenous_iff_subset.mp hS)
    have hP : P.card = S.card - 1 := by
      rw [card_ACompression (degHomogenous_iff_subset.mp (DegHomogenous.mono hS (Finset.erase_subset _ _))),
        Finset.card_erase_of_mem hu]
    obtain ⟨v, hv, hvP⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show P.card < C.card by rw [hP, hC]; exact Nat.sub_lt (Finset.card_pos.mpr ⟨u, hu⟩) (by decide))
    have hP' : P = C.erase v := Finset.eq_of_subset_of_card_le
      (fun a ha ↦ Finset.mem_erase.mpr ⟨by rintro rfl; exact hvP ha, hPC ha⟩)
      (by rw [Finset.card_erase_of_mem hv, hC, hP])
    change (Shadow C).card ≤ (Shadow P).card + 1
    rw [hP']
    exact shadow_erase_card_le (ACompression_colexInitial S d) v

end Macaulay
