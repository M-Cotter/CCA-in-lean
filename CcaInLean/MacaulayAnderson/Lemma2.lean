import Mathlib
import CcaInLean.MacaulayAnderson.Lemma1

variable {X : Type*} {L : List X} {n : ℕ} {S : Finset (Fin n →₀ ℕ)}
  {C : Finset <| Colex <| Fin n →₀ ℕ} {k : ℕ}

open Finset

/-- Compression will take a Finset of `n`-vectors and a natural `k` and return the first
  `k` elements of that set. -/
def Compression (S : Finset <| Fin n →₀ ℕ) (k : ℕ) : Finset (Fin n →₀ ℕ) :=
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

lemma image_colex : image toColex S = S := by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨a, ha⟩ ↦ ha.2 ▸ ha.1, fun h ↦ ⟨x, h, rfl⟩⟩

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

variable (i : Fin n) (k l m : ℕ)

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

@[simp]
lemma mem_image_colex {a : Colex (Fin n →₀ ℕ)}
    : a ∈ image (⇑toColex) S ↔
      ofColex a ∈ S := by
    rw [mem_image]
    refine ⟨fun ⟨c, hc₁, hc₂⟩ ↦ ?_, fun h ↦ ⟨_, h, toColex_ofColex _ ▸ rfl⟩⟩
    rwa [← hc₂, ofColex_toColex]

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
        unfold b
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

-- Chatgpt writes even worse code than me
theorem toColex_biUnion_le_toColex_biUnion
    {ι α : Type*} [LinearOrder α] [DecidableEq α]
    (I : Finset ι)
    (A B : ι → Finset α)
    (hB : (I : Set ι).PairwiseDisjoint B)
    (hAB : ∀ i ∈ I, toColex (A i) ≤ toColex (B i)) :
    toColex (I.biUnion A) ≤ toColex (I.biUnion B) := by
  rw [Finset.Colex.toColex_le_toColex]
  intro a haU hnaV
  rcases Finset.mem_biUnion.mp haU with ⟨i, hi, hai⟩
  have hnaBi : a ∉ B i := by
    intro haiB
    exact hnaV (Finset.mem_biUnion.mpr ⟨i, hi, haiB⟩)
  rcases
      (Finset.Colex.toColex_le_toColex.mp (hAB i hi)) hai hnaBi with
    ⟨b, hbiB, hnbiA, hab⟩
  by_cases hbU : b ∈ I.biUnion A
  · let M : Finset α :=
      (I.biUnion (fun k => B k \ A k)) ∩ I.biUnion A
    have hbM : b ∈ M := by
      refine Finset.mem_inter.mpr ⟨?_, hbU⟩
      refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
      exact Finset.mem_sdiff.mpr ⟨hbiB, hnbiA⟩
    have hM : M.Nonempty := ⟨b, hbM⟩
    let m : α := M.max' hM
    have hbm : b ≤ m := le_max' M b hbM
    rcases Finset.mem_inter.mp (max'_mem M hM) with ⟨hmD, hmU⟩
    rcases Finset.mem_biUnion.mp hmD with ⟨k, hk, hmkD⟩
    have hmkB : m ∈ B k := (Finset.mem_sdiff.mp hmkD).1
    have hmkA : m ∉ A k := (Finset.mem_sdiff.mp hmkD).2
    rcases Finset.mem_biUnion.mp hmU with ⟨j, hj, hmjA⟩
    have hkj : k ≠ j := fun h ↦ hmkA <| h ▸ hmjA
    have hmjB : m ∉ B j := by
      intro hmjB
      exact hkj (hB.elim_finset hk hj m hmkB hmjB)
    rcases
        (Finset.Colex.toColex_le_toColex.mp (hAB j hj)) hmjA hmjB with
      ⟨c, hcjB, hncjA, hmc⟩
    have hncU : c ∉ I.biUnion A := by
      intro hcU
      have hcM : c ∈ M := by
        refine Finset.mem_inter.mpr ⟨?_, hcU⟩
        refine Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩
        exact Finset.mem_sdiff.mpr ⟨hcjB, hncjA⟩
      have hcm : c ≤ m := le_max' M c hcM
      exact (not_lt_of_ge hcm) (lt_of_le_of_ne hmc fun h ↦ hmjB <| h ▸ hcjB)
    refine ⟨c, ?_, hncU, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨j, hj, hcjB⟩
    · exact hab.trans (hbm.trans hmc)
  · exact ⟨b, Finset.mem_biUnion.mpr ⟨i, hi, hbiB⟩, hbU, hab⟩

lemma iCompression_contraction (hSn : S.Nonempty)
    (hS : S ≤ (Finset.univ.finsuppAntidiag m)) :
    toColex (S.image toColex) ≤
    toColex ((iCompression S i m).image toColex) := by
  nth_rw 1 [← @union_iPart_eq_self _ S i]
  unfold iCompression
  rw [Finset.biUnion_image, Finset.biUnion_image]
  apply toColex_biUnion_le_toColex_biUnion _ _ _
  · have : (S.image (fun v ↦ v i) : Set ℕ) =
      (S : Set (Fin n →₀ ℕ)).image (fun v ↦ v i) := coe_image
    rw [coe_image]
    sorry
  · intro j hj
    sorry

def ACompression₀ (S : Finset (Fin n →₀ ℕ)) (m : ℕ)
    : Fin n → Finset (Fin n →₀ ℕ)
  | ⟨0, h⟩ => iCompression S ⟨0, h⟩ m
  | ⟨k + 1, h⟩ => iCompression (
    ACompression₀ S m ⟨k, lt_trans (Nat.lt_add_one _) h⟩
  ) ⟨k + 1, h⟩ m

def ACompression (S : Finset (Fin (n + 1) →₀ ℕ)) (m : ℕ) :
    Finset (Fin (n + 1) →₀ ℕ) :=
    ACompression₀ S m (Fin.last n)

theorem ACompression₀_eq
    (S : Finset (Fin n →₀ ℕ)) (m : ℕ)
    (k : ℕ) (h : k + 1 < n) :
    ACompression₀ S m ⟨k + 1, h⟩ = iCompression (
      ACompression₀ S m ⟨k, lt_trans (Nat.lt_add_one _) h⟩
    ) ⟨k + 1, h⟩ m := by
  conv_lhs =>
  unfold ACompression₀

lemma ACompression₀_zero {S : Finset (Fin (n + 1) →₀ ℕ)} :
    ACompression₀ S m 0 = iCompression S 0 m := by
  unfold ACompression₀
  trivial

lemma ACompression₀_succ {S : Finset (Fin (n + 1) →₀ ℕ)} (i : Fin n) :
    ACompression₀ S m i.succ =
    iCompression (
      ACompression₀ S m i.castSucc
    ) i.succ m := by
  conv_lhs => unfold ACompression₀
  simp [Fin.succ]
  congr

lemma ACompression₀_subset :
    ACompression₀ S m i ⊆ Finset.univ.finsuppAntidiag m := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.inductionOn with
    | zero => exact ACompression₀_zero _ ▸ iCompression_subset _ _
    | succ i hi =>
      rw [ACompression₀_succ]
      apply iCompression_subset

variable {S : Finset <| Fin (n + 1) →₀ ℕ}

lemma ACompression_subset :
    ACompression S m ⊆ Finset.univ.finsuppAntidiag m := ACompression₀_subset _ _

-- FUck this shit

theorem ACompression_fixed_point : ∃ k,
    toColex (((fun X ↦ ACompression X m)^[k + 1] S).image toColex) ≤
    toColex (((fun X ↦ ACompression X m)^[k] S).image toColex) := by
  by_contra!
  let jth_pow := fun j ↦
    toColex (((fun X ↦ ACompression X m)^[j] S).image toColex)
  have : StrictMono jth_pow := by
    apply strictMono_nat_of_lt_succ
    intro k
    apply this
  have mem_jth_pow (j : ℕ) (hj : j > 0) :
      (ofColex <| jth_pow j).image ofColex ⊆ univ.finsuppAntidiag m := by
    intro b hb
    apply ACompression_subset
    obtain ⟨c, hc₁, hc₂⟩ := mem_image.mp hb
    simp [jth_pow] at hc₁
    obtain ⟨d, hd₁, hd₂⟩:= hc₁
    rw [← hc₂, ← hd₂, ofColex_toColex]
    show d ∈ (fun X ↦ ACompression X m) (((fun X ↦ ACompression X m)^[j - 1]) S)
    have : (fun X ↦ ACompression X m) ((fun X ↦ ACompression X m)^[j - 1] S) =
        ((fun X ↦ ACompression X m) ∘ (fun X ↦ ACompression X m)^[j - 1]) S:= by
      norm_num
    rw [this, ← Function.iterate_succ']
    have : (j - 1).succ = j := Nat.sub_one_add_one_eq_of_pos hj
    rw [this]
    exact hd₁
  have jth_pow_card : ∀ j, ((Finset.Icc 1 j).image jth_pow).card = j := by
    intro j
    rw [Finset.card_image_of_injective]
    simp only [Nat.card_Icc, add_tsub_cancel_right]
    exact StrictMono.injective this
  let A := (Finset.univ.finsuppAntidiag m : Finset (Fin (n + 1) →₀ ℕ)).image toColex
  have jth_pow_subset : ∀ j > 0, ((Finset.Icc 1 j).image jth_pow).card ≤
      (A.powerset.image toColex).card := fun j hj ↦ by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨c, hc₁, hc₂⟩ := mem_image.mp ha
    refine mem_image.mpr ⟨ofColex a, ?_⟩
    simp only [A, mem_powerset, toColex_ofColex, and_true]
    refine subset_image_iff.mpr ⟨a.image ofColex, ?_, ?_⟩
    · have : c > 0 := by
        rw [Finset.mem_Icc] at hc₁
        lia
      apply subset_trans _ (mem_jth_pow c this)
      apply image_subset_image
      show ofColex a ⊆ ofColex (jth_pow c)
      rw [hc₂]
    · ext x
      simp [image_image]
      rfl
  let M := (image (⇑toColex) A.powerset).card
  have h₁ := jth_pow_card ((image (⇑toColex) A.powerset).card + 1)
  have : M + 1 > 0 := Nat.add_one_pos _
  have h₂ := jth_pow_subset _ this
  rw [h₁] at h₂
  omega
