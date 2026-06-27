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

/-- Condition for membership in an initial segment. -/
@[simp]
lemma mem_initSeg (t : Fin n → ℕ) :
    t ∈ initfSeg c m ↔ t ≤ c ∧ ∑ i, t i = ∑ i, m i ∧ toLex t ≤ toLex m := by
  simp [initfSeg, LocallyFiniteOrder.finset_mem_Icc]

/-- m is in its own initial segment. -/
@[simp]
lemma mem_initSeg_self (hm : m ≤ c) : m ∈ initfSeg c m := by simpa

/-- A fixed set of `n → ℕ`, by this I mean one which is always less than or equal to `c` and
  which always has multicardinality `r`. -/
def IsFixed (r : ℕ) (𝒜 : Finset (Fin n → ℕ)) : Prop :=
   (∀ s ∈ 𝒜, s ≤ c ∧ ∑ i, s i = r)

/-- Alternative characterization of initial segments. -/
def IsInitSeg (𝒜 : Finset (Fin n → ℕ)) : Prop :=
  ∀ s t : Fin n → ℕ, s ∈ 𝒜 → t ≤ c ∧ toLex t ≤ toLex s ∧ ∑ i, t i = ∑ i, s i → t ∈ 𝒜

/-- Empty set is an initial segment. -/
@[simp]
lemma isInitSeg_empty : IsInitSeg c (∅ : Finset (Fin n → ℕ)) := by simp [IsInitSeg]

/-- Initial segments are totally ordered. -/
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

/-- Initial segments are initial by the alternative characterization. -/
lemma isInitSeg_initfSeg : IsInitSeg c (initfSeg c m) := by
  unfold IsInitSeg
  intro s t hs ha
  rw [mem_initSeg] at ⊢ hs
  exact ⟨ha.1, ha.2.2 ▸ hs.2.1, le_trans ha.2.1 hs.2.2⟩

/-- Initial segments are fixed. -/
lemma isFixed_initfSeg : IsFixed c (∑ i, m i) (initfSeg c m) := by
  intro s hs
  rw [mem_initSeg] at hs
  exact ⟨hs.1, hs.2.1⟩

/-- Every initial segment (Prop) has a supremum which makes it initial. -/
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

/-- Shadow of an inidividual element. -/
def iShadow (v : Fin n → ℕ) : Finset (Fin n → ℕ) :=
    {f ∈ LocallyFiniteOrder.finsetIcc 0 v | ∃ i : Fin n, f + Pi.single i 1 = v}

/-- Shadow of a family, notably this is a computable definition. -/
def Shadow (𝒜 : Finset (Fin n → ℕ)) : Finset (Fin n → ℕ) := 𝒜.biUnion iShadow

/-- Zero is the bottom of the lexicographical order. -/
lemma toLex.zero_eq_bot : (0 : Lex (Fin n → ℕ)) = ⊥ := ofLex_inj.mp rfl

-- The fact I have to have this lemma might point to an issue with Mathlib? I'm quite confused
theorem toLex.le_self_add {a b : Fin n → ℕ} : toLex a ≤ toLex (a + b) :=
  le_add_of_nonneg_right <| toLex.zero_eq_bot ▸ OrderBot.bot_le _

theorem toLex.le_add_self {a b : Fin n → ℕ} : toLex a ≤ toLex (b + a) :=
  add_comm a _ ▸ le_self_add

/-- Shadows are always lexicographically before an element. -/
lemma shadow_le_self {v : Fin n → ℕ} : ∀ i ∈ iShadow v, toLex i ≤ toLex v := by
  simp only [iShadow, Finset.mem_filter]
  exact fun i ⟨_, _, hx⟩ ↦ hx.symm ▸ toLex.le_self_add

/-- Membership in a shadow iff there exists a unit vector which add to a member. -/
lemma mem_shadow_iff {v : Fin n → ℕ} {s : Finset (Fin n → ℕ)} :
    v ∈ Shadow s ↔ ∃ i : Fin n, (v + Pi.single i 1) ∈ s := by
  unfold Shadow iShadow
  simp only [Finset.mem_biUnion, Finset.mem_filter, ↓existsAndEq, and_true]
  apply Iff.intro
  · exact fun ⟨i, hi⟩ ↦ ⟨i, hi.1⟩
  refine fun ⟨i, hi⟩ ↦ ⟨i, hi, ?_⟩
  simp [@LocallyFiniteOrder.finset_mem_Icc]

-- This doesn't appear to be in Mathlib, which is also confusing
lemma lt_def {s t : Fin n → ℕ} : toLex s < toLex t ↔
  ∃ i : Fin n, (∀ j : Fin n, j < i → s j = t j) ∧ (s i) < (t i) := by rfl

-- Something horrible is going on with the lt here
lemma test {s t : Fin n → ℕ} : toLex s ≤ toLex t ↔ toLex s < toLex t ∨ toLex s = toLex t :=
  le_iff_lt_or_eq

/-- Shadows of fixed sets with multicardinality `r + 1` are fixed with multicardinality `r`. -/
theorem fixed_shadow_fixed (𝒜 : Finset (Fin n → ℕ)) (h𝒜f : IsFixed c (r + 1) 𝒜) :
    IsFixed c r (Shadow 𝒜) := by
  intro s hs
  rcases mem_shadow_iff.mp hs with ⟨a, ha⟩
  constructor
  · exact le_trans le_self_add (h𝒜f _ ha).1
  · rw [← @Nat.add_right_cancel_iff _ _ 1, show ∑ i, s i + 1 =
      ∑ i, (s + (Pi.single a 1 : Fin n → ℕ)) i by simp [Pi.add_apply, Finset.sum_add_distrib]]
    exact (h𝒜f _ ha).2

lemma lt_gt_lex {a b : Fin n} (hab : a < b) :
    toLex (Pi.single b 1 : Fin n → ℕ) < toLex (Pi.single a 1) := by
  rw [lt_def]
  use a
  constructor
  · intro j hj
    simp [ne_of_lt hj, ne_of_lt (lt_trans hj hab)]
  · simp [ne_of_lt hab]


/-- A family `𝒜` is iCompact if the subset of multisets which have `j` elements in their `i`th entry
    is lower. -/
def iCompressed (r j : ℕ) (i : Fin n) (𝒜 : Finset (Fin n → ℕ)) : Prop :=
    ∀ s t : Fin n → ℕ, s ∈ 𝒜 → t ≤ c ∧ toLex t ≤ toLex s ∧ ∑ i, t i = r ∧ t i = j → t ∈ 𝒜

variable {α : Type*} [LinearOrder α] [Fintype α]

def InitSegment (n : ℕ) : Finset α :=
  ((Finset.univ.sort (· ≤ ·)).take n).toFinset

/-- Compression returns the first `# A` elements of `F`. -/
def Compression (A F : Finset α) : Finset α :=
  ((F.sort (· ≤ ·)).take (Finset.card A)).toFinset

def InitSeg (n : ℕ) (A : Finset α) :=
  ((A.sort (· ≤ ·)).take n).toFinset

/-- Let `A` and `F` be finite sets of monomials, then compress will return the first `# A` elements of `F` in
   the lexicogrpahical ordering. This is intended to be used when `F` is the set of all monomials of some fixed
    degree `k` and `A ⊆ F`. -/
noncomputable
def Compress (A F : Finset (Fin n → ℕ)) : Finset (Fin n → ℕ) :=
  Finset.image ofLex (((Finset.image toLex F).sort (· ≤ ·)).take (Finset.card A)).toFinset

/-- Compress is a subset of `F`, this is almost definitional since `F` is our 'universe'. -/
theorem compress_subset {A F : Finset (Fin n → ℕ)} : Compress A F ⊆ F := by
  intro a ha
  unfold Compress at ha
  simp only [Finset.mem_image, List.mem_toFinset, Lex.exists, ofLex_toLex, exists_eq_right] at ha
  apply List.take_subset A.card _ at ha
  simp_all only [Finset.mem_sort, Finset.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]

/-- Take has no duplicates if the list has no duplicates. -/
theorem List.nodup_take {α : Type} {n : ℕ} {L : List α} (h : List.Nodup L) :
    List.Nodup (List.take n L) := by
  grind only [= List.nodup_iff_count, = List.nodup_iff_pairwise_ne, ← List.Pairwise.take]

/-- Cardinality of the compression is the constant. -/
theorem compress_card {A F : Finset (Fin n → ℕ)} (hA : A ⊆ F) :
    Finset.card A = Finset.card (Compress A F) := by
  unfold Compress
  rw [Finset.card_image_of_injective _ (Equiv.injective ofLex), List.card_toFinset,
  List.dedup_eq_self.mpr]
  · simp only [List.length_take, Finset.length_sort,
    Finset.card_image_of_injective _ (Equiv.injective toLex), left_eq_inf]
    exact Finset.card_le_card hA
  apply List.nodup_take
  simp only [Finset.sort_nodup]

/-- Compress is the initial segment lexicographically-/
theorem mem_compress {f a : Fin n → ℕ} {A F : Finset (Fin n → ℕ)} (hf : f ∈ F)
    (ha : a ∈ Compress A F) (hfa : toLex f ≤ toLex a) :
    f ∈ Compress A F := by
  unfold Compress at ⊢ ha
  simp only [Finset.mem_image, List.mem_toFinset, Lex.exists, ofLex_toLex, exists_eq_right] at ⊢ ha
  rw [List.mem_take_iff_idxOf_lt] at ⊢ ha
  · have : List.idxOf (toLex f) ((Finset.image (⇑toLex) F).sort fun x1 x2 ↦ x1 ≤ x2) ≤
      List.idxOf (toLex a) ((Finset.image (⇑toLex) F).sort fun x1 x2 ↦ x1 ≤ x2) := by
      sorry
    · exact lt_of_le_of_lt this ha
  · simp [Finset.mem_sort, hf]
  · exact List.take_subset A.card _ ha

theorem compress_total {A B F : Finset (Fin n → ℕ)} :
    Compress A F ⊆ Compress B F ∨ Compress B F ⊆ Compress A F := by
  simp_rw [← Finset.sdiff_eq_empty_iff_subset]
  by_contra! h
  obtain ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [Finset.mem_sdiff] at hs ht
  obtain hst | hst := le_total (toLex s) (toLex t)
  · exact hs.2 <| mem_compress (compress_subset hs.1) ht.1 hst
  · exact ht.2 <| mem_compress (compress_subset ht.1) hs.1 hst

theorem compress_contraction {A F : Finset (Fin n → ℕ)} (hA : A ⊆ F) :
    toColex (Finset.image toLex (Compress A F)) ≤ toColex (Finset.image toLex A) := by
  by_contra
  rw [not_le, Finset.Colex.lt_iff_exists_forall_lt] at this
  obtain ⟨a, ha₁, ha₂, hb⟩ := this
  simp only [ofColex_toColex, Finset.mem_image, not_exists, not_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, EmbeddingLike.apply_eq_iff_eq, Finset.forall_mem_not_eq'] at *
  obtain ⟨c, hc⟩ := ha₁
  have : ∃ x ∈ A, x ∉ Compress A F := by
    apply Finset.not_subset.mp
    intro hAF
    rw [Finset.eq_of_subset_of_card_le hAF (le_of_eq (compress_card hA).symm)] at ha₂
    exact ha₂ c hc.1 hc.2
  obtain ⟨d, hd⟩ := this
  apply hd.2
  apply mem_compress (hA hd.1)
  · exact hc.2.symm ▸ (ofLex_toLex c ▸ hc.1)
  · exact toLex_ofLex _ ▸ (le_of_lt <| hb d hd.1 hd.2)

/-- Compress of one entry with a target. -/
noncomputable
def itCompress (i : Fin n) (t : ℕ) (A F : Finset (Fin n → ℕ)) : Finset (Fin n → ℕ) :=
  {a ∈ A | a i ≠ t} ∪
  Compress {a ∈ A | a i = t} {f ∈ F | f i = t}

/-- Compress with target keeps cardinality. -/
theorem itCompress_card {i : Fin n} {t : ℕ} {A F : Finset (Fin n → ℕ)} (hA : A ⊆ F) :
    Finset.card (itCompress i t A F) = Finset.card A := by
  unfold itCompress
  rw [Finset.card_union, ← compress_card]
  · have : ({a ∈ A | a i ≠ t} ∩ Compress ({a ∈ A | a i = t}) ({f ∈ F | f i = t})) = ∅ := by
      by_contra!
      obtain ⟨a, ha⟩ := this
      rw [Finset.mem_inter, Finset.mem_filter] at ha
      exact ha.1.2 (Finset.mem_filter.mp <| compress_subset ha.2).2
    · rw [this, Finset.card_empty, Nat.sub_zero, ← Finset.card_union_add_card_inter,
        show {a ∈ A | ¬a i = t} ∪ {a ∈ A | a i = t} = A by grind,
        show {a ∈ A | ¬a i = t} ∩ {a ∈ A | a i = t} = ∅ by grind, Finset.card_empty, add_zero]
  · exact Finset.filter_subset_filter (fun a ↦ a i = t) hA

/-- itCompress is an initial segment lexicographically. -/
theorem mem_itCompress {f a : Fin n → ℕ} {i : Fin n} {t : ℕ}
    {A F : Finset (Fin n → ℕ)} (hf : f ∈ F)
    (ha : a ∈ itCompress i t A F) (hfa : toLex f ≤ toLex a) (hai : a i = t)
    (hfi : f i = t) : f ∈ itCompress i t A F := by
  unfold itCompress
  apply Finset.mem_union_right
  apply mem_compress
  · rw [Finset.mem_filter]
    exact ⟨hf, hfi⟩
  · unfold Compress
    apply (Finset.mem_union.mp ha).resolve_left
    simp [hai]
  · exact hfa

variable {i : Fin n} {A F : Finset (Fin n → ℕ)}

/-- iCompress from the book, in terms of compressing one entry by each target. In other words, it takes an
  index `i` and two finset `A` and `F` and returns the first `# {a ∈ A | a i = t}` entries of `F` such
  that `f i = t`. -/
noncomputable
def iCompress (i : Fin n) (A F : Finset (Fin n → ℕ)) : Finset (Fin n → ℕ):=
    (Finset.image (fun a ↦ a i) A).biUnion
    (fun t ↦ Compress {a ∈ A | a i = t} {f ∈ F | f i = t})

theorem iCompress_subset : iCompress i F A ⊆ A :=
  Finset.biUnion_subset.mpr <| fun _ _ ↦ subset_trans compress_subset (Finset.filter_subset _ _)

/-- iCompress cardinality is constant. -/
theorem card_iCompress (hA : A ⊆ F) :
    Finset.card (iCompress i A F) = Finset.card A := by
  unfold iCompress
  rw [Finset.card_biUnion]
  · have : ∀ t, {a ∈ A | a i = t} ⊆ {f ∈ F | f i = t} := fun t ↦
      Finset.filter_subset_filter _ hA
    have hsum :
      ∑ u ∈ Finset.image (fun a ↦ a i) A,
          (Compress ({a ∈ A | a i = u}) ({f ∈ F | f i = u})).card
      = ∑ u ∈ Finset.image (fun a ↦ a i) A, ({a ∈ A | a i = u}).card := by
      refine Finset.sum_congr rfl ?_
      intro u _
      exact (compress_card (this u)).symm
    rw [hsum, ← Finset.card_biUnion]
    · congr
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, exists_eq_right_right',
        and_iff_right_iff_imp]
      intro x
      use a
    · exact Set.pairwiseDisjoint_filter (fun x ↦ x i) _ A
  · intro x hx y hy hxy I hI₁ hI₂
    simp at hI₁ hI₂
    have hIx : I ⊆ {f ∈ F | f i = x} := subset_trans hI₁ compress_subset
    have hIy : I ⊆ {f ∈ F | f i = y} := subset_trans hI₂ compress_subset
    intro i hi
    contrapose! hxy
    grind only [= Finset.subset_iff, = Finset.mem_filter, #be4d, #8d14]

/-- iCompress is an initial segment lexicographically. -/
theorem mem_iCompress {f a : Fin n → ℕ} {i : Fin n} {A F : Finset (Fin n → ℕ)}
    (hf : f ∈ F) (ha : a ∈ iCompress i A F) (haf : f i = a i) (hafl : toLex f ≤ toLex a)
    : f ∈ iCompress i A F := by
  unfold iCompress
  simp only [Finset.mem_biUnion, Finset.mem_image, exists_exists_and_eq_and]
  obtain ⟨w, hw₁, hw₂⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨o, ho⟩ := Finset.mem_image.mp hw₁
  use o
  refine ⟨ho.1, mem_compress ?_ (ho.2 ▸ hw₂) hafl⟩
  apply compress_subset at hw₂
  rw [Finset.mem_filter] at hw₂
  simp [ho.2, ← hw₂.2, hf, haf]


/-
theorem compress_contraction {A F : Finset (Fin n → ℕ)} (hA : A ⊆ F) :
    toColex (Finset.image toLex (Compress A F)) ≤ toColex (Finset.image toLex A) := by
  by_contra
  rw [not_le, Finset.Colex.lt_iff_exists_forall_lt] at this
  obtain ⟨a, ha₁, ha₂, hb⟩ := this
  simp only [ofColex_toColex, Finset.mem_image, not_exists, not_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, EmbeddingLike.apply_eq_iff_eq, Finset.forall_mem_not_eq'] at *
  obtain ⟨c, hc⟩ := ha₁
  have : ∃ x ∈ A, x ∉ Compress A F := by
    apply Finset.not_subset.mp
    intro hAF
    rw [Finset.eq_of_subset_of_card_le hAF (le_of_eq (compress_card hA).symm)] at ha₂
    exact ha₂ c hc.1 hc.2
  obtain ⟨d, hd⟩ := this
  apply hd.2
  apply mem_compress (hA hd.1)
  · exact hc.2.symm ▸ (ofLex_toLex c ▸ hc.1)
  · exact toLex_ofLex _ ▸ (le_of_lt <| hb d hd.1 hd.2)
-/

theorem Colex.disj_union_le {α : Type*} [LinearOrder α]
    {A B C D : Finset α} (hAC : toColex A ≤ toColex C)
    (hAB : toColex B ≤ toColex D) (hdAC : Disjoint A B) (hdCD : Disjoint C D) :
    toColex (A ∪ B) ≤ toColex (C ∪ D) := by
  rw [Finset.Colex.toColex_le_toColex_iff_max'_mem] at ⊢ hAC hAB
  intro hABCD
  let q := (symmDiff (A ∪ B) (C ∪ D)).max' (Finset.symmDiff_nonempty.mpr hABCD)
  have : q ∈ symmDiff (A ∪ B) (C ∪ D) :=
    Finset.max'_mem _ _
  have : q ∈ (C ∪ D) := by
    rw [symmDiff, Finset.sup_eq_union, Finset.mem_union] at this
    cases this with
    | inr h => exact Finset.sdiff_subset h
    | inl h =>
      have : q ∈ A ∨ q ∈ B := by rw [← Finset.mem_union]; exact Finset.sdiff_subset h
      have : A ≠ C ∨ B ≠ D := by grind only
      cases this with
      | inl hAC' =>
        have := hAC hAC'
        sorry
      | inr hBD' => sorry
  exact this

open Classical in
theorem Colex.disj_biUnion_le {α σ : Type*} (s : Finset σ) [LinearOrder α]
    {f g : σ → Finset α} (hf : ∀ i j, Disjoint (f i) (f j)) (hg : ∀ i j, Disjoint (g i) (g j))
    (hfg : ∀ i, toColex (f i) ≤ toColex (g i)) :
    toColex (s.biUnion f) ≤ toColex (s.biUnion g) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.biUnion_empty, Finset.Colex.toColex_empty, Std.le_refl]
  | insert x s hx ih =>
    simp only [Finset.biUnion_insert]
    apply Colex.disj_union_le (hfg _) ih
    · exact (Finset.disjoint_biUnion_right _ _ _).mpr <| fun i _ ↦ hf _ _
    · exact (Finset.disjoint_biUnion_right _ _ _).mpr <| fun i _ ↦ hg _ _

theorem iCompress_contraction {i : Fin n} {A F : Finset (Fin n → ℕ)} (hA : A ⊆ F) :
    toColex ((iCompress i A F).image toLex) ≤ toColex (A.image toLex) := by
  sorry

variable {m : ℕ} {A F : Finset (Fin (n + 1) → ℕ)}

noncomputable
def LexPow (m : ℕ) (A F : Finset (Fin (n + 1) → ℕ)) : Finset (Fin (n + 1) → ℕ) :=
  match m with
  | 0 => A
  | m + 1 => iCompress (Fin.ofNat _ m) (LexPow m A F) F

@[simp]
lemma lexpow_zero : LexPow 0 A F = A := rfl

@[simp]
lemma lexpow_succ : LexPow (m + 1) A F = iCompress (Fin.ofNat _ m) (LexPow m A F) F := rfl

lemma lexpow_subset (hA : A ⊆ F) : LexPow m A F ⊆ F := by
  induction m with
  | zero => rwa [lexpow_zero]
  | succ k hk => exact lexpow_succ ▸ iCompress_subset

theorem card_lexpow (hA : A ⊆ F) :
    Finset.card (LexPow m A F) = Finset.card A := by
  induction m with
  | zero => rw [lexpow_zero]
  | succ k hk =>
    rwa [lexpow_succ, card_iCompress]
    exact lexpow_subset hA
/-
theorem mem_lexpow (hA : A ⊆ F) : -/
