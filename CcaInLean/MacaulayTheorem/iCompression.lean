import CcaInLean.MacaulayTheorem.Compression
import Mathlib.Tactic.Convert

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
    exact compression_contraction (iPart_le_iUniv i j m hS)

theorem iCompression_homogeneous (S : Finset (Fin n →₀ ℕ)) (p : Fin n) (d : ℕ) :
    DegHomogenous (iCompression S p d) d :=
  degHomogenous_iff_subset.mpr (iCompression_subset p d)

theorem iCompression_lower_of_fixed {A : Finset (Fin n →₀ ℕ)} {p : Fin n} {d : ℕ}
    (hfix : iCompression A p d = A) {u v : Fin n →₀ ℕ}
    (hu : (∑ i, u i) = d) (hp : u p = v p) (hle : toColex u ≤ toColex v) (hv : v ∈ A) :
    u ∈ A := by
  rw [← hfix] at hv ⊢
  exact iCompression_iLower (k := u p) hp hle (by simp [mem_iUniv, hu]) hv

/-- Delete the `p`th exponent, retaining the order of the other variables. -/
noncomputable def eraseIndex {n : ℕ} (p : Fin (n + 1))
    (u : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => u (p.succAbove j))

/-- Insert a fixed exponent at position `p`. -/
noncomputable def insertIndex {n : ℕ} (p : Fin (n + 1)) (k : ℕ)
    (u : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.insertNth p k u)

@[simp] lemma eraseIndex_apply {n : ℕ} (p : Fin (n + 1))
    (u : Fin (n + 1) →₀ ℕ) (j : Fin n) :
    eraseIndex p u j = u (p.succAbove j) := rfl

@[simp] lemma insertIndex_pivot {n : ℕ} (p : Fin (n + 1)) (k : ℕ)
    (u : Fin n →₀ ℕ) : insertIndex p k u p = k := by
  simp [insertIndex]

@[simp] lemma insertIndex_above {n : ℕ} (p : Fin (n + 1)) (k : ℕ)
    (u : Fin n →₀ ℕ) (j : Fin n) : insertIndex p k u (p.succAbove j) = u j := by
  simp [insertIndex]

@[simp] lemma eraseIndex_insertIndex {n : ℕ} (p : Fin (n + 1)) (k : ℕ)
    (u : Fin n →₀ ℕ) : eraseIndex p (insertIndex p k u) = u := by
  ext j
  simp

@[simp] lemma insertIndex_eraseIndex {n : ℕ} (p : Fin (n + 1))
    (u : Fin (n + 1) →₀ ℕ) : insertIndex p (u p) (eraseIndex p u) = u := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove p j with h | ⟨t, rfl⟩
  · subst j
    simp
  · simp

lemma insertIndex_sum {n : ℕ} (p : Fin (n + 1)) (k : ℕ) (u : Fin n →₀ ℕ) :
    (∑ j, insertIndex p k u j) = k + ∑ j, u j := by
  rw [Fin.sum_univ_succAbove _ p]
  simp

/-- Deleting a common coordinate preserves and reflects strict colex order. -/
theorem eraseIndex_colex_lt_iff {n : ℕ} (p : Fin (n + 1))
    {u v : Fin (n + 1) →₀ ℕ} (hp : u p = v p) :
    toColex (eraseIndex p u) < toColex (eraseIndex p v) ↔ toColex u < toColex v := by
  rw [Finsupp.Colex.lt_def, Finsupp.Colex.lt_def]
  constructor
  · rintro ⟨t, htail, hlt⟩
    refine ⟨p.succAbove t, ?_, ?_⟩
    · intro j hj
      rcases Fin.eq_self_or_eq_succAbove p j with heq | ⟨s, rfl⟩
      · subst j
        exact hp
      · exact htail s ((Fin.strictMono_succAbove p).lt_iff_lt.mp hj)
    · simpa using hlt
  · rintro ⟨j, htail, hlt⟩
    have hj : j ≠ p := by
      intro heq
      subst j
      exact (ne_of_lt hlt) hp
    obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hj
    refine ⟨t, ?_, ?_⟩
    · intro s hs
      exact htail (p.succAbove s) ((Fin.strictMono_succAbove p) hs)
    · simpa using hlt


/-- Inserting equal coordinates preserves colex order. -/
theorem insertIndex_colex_le {n : ℕ} (p : Fin (n + 1)) (k : ℕ) (u v : Fin n →₀ ℕ) :
    toColex (insertIndex p k u) ≤ toColex (insertIndex p k v) ↔ toColex u ≤ toColex v := by
  rw [← not_lt, ← not_lt, ← eraseIndex_colex_lt_iff p (by simp)]
  simp

/-- A coordinate section, viewed in one fewer variable. -/
noncomputable def stripSection {n : ℕ} (S : Finset (Fin (n + 1) →₀ ℕ))
    (p : Fin (n + 1)) (k : ℕ) : Finset (Fin n →₀ ℕ) :=
  (iPart S p k).image (eraseIndex p)

@[simp] theorem mem_stripSection {n : ℕ} {S : Finset (Fin (n + 1) →₀ ℕ)}
    {p : Fin (n + 1)} {k : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ stripSection S p k ↔ insertIndex p k u ∈ S := by
  simp only [stripSection, Finset.mem_image, mem_iPart]
  constructor
  · rintro ⟨v, ⟨hv, hp⟩, rfl⟩
    simpa only [← hp, insertIndex_eraseIndex] using hv
  · exact fun h ↦ ⟨insertIndex p k u, ⟨h, by simp⟩, by simp⟩

lemma eraseIndex_injective_on_slice {n : ℕ} (p : Fin (n + 1))
    {u v : Fin (n + 1) →₀ ℕ} (hp : u p = v p)
    (h : eraseIndex p u = eraseIndex p v) : u = v := by
  simpa only [insertIndex_eraseIndex] using congrArg₂ (insertIndex p) hp h

lemma stripSection_card {n : ℕ} (S : Finset (Fin (n + 1) →₀ ℕ)) (p : Fin (n + 1)) (k : ℕ) :
    (stripSection S p k).card = (iPart S p k).card :=
  Finset.card_image_iff.mpr fun _ hu _ hv h ↦
    eraseIndex_injective_on_slice p ((mem_iPart.mp hu).2.trans (mem_iPart.mp hv).2.symm) h

theorem iPart_iCompression_eq {n d k : ℕ} {S : Finset (Fin n →₀ ℕ)} (p : Fin n) :
    iPart (iCompression S p d) p k = Compression (iUniv p k d) (iPart S p k).card := by
  ext u
  constructor
  · intro hu
    obtain ⟨hu, hup⟩ := mem_iPart.mp hu
    obtain ⟨j, hj, huj⟩ := Finset.mem_biUnion.mp hu
    have := (mem_iUniv p j d u).mp (mem_compression huj)
    grind
  · intro hu
    have hup := (mem_iUniv p k d u).mp (mem_compression hu)
    have hk : k ∈ S.image (fun v ↦ v p) := by
      by_contra h
      have : iPart S p k = ∅ := by ext v; simp; grind
      simp [this, Compression] at hu
    exact mem_iPart.mpr ⟨Finset.mem_biUnion.mpr ⟨k, hk, hu⟩, hup.2⟩

lemma iPart_iCompression_card {n d k : ℕ} {S : Finset (Fin n →₀ ℕ)} (p : Fin n)
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) :
    (iPart (iCompression S p d) p k).card = (iPart S p k).card := by
  rw [iPart_iCompression_eq, card_compression (Finset.card_mono (iPart_le_iUniv p k d hS))]

theorem stripSection_homogeneous {n d k : ℕ} {S : Finset (Fin (n + 1) →₀ ℕ)}
    (p : Fin (n + 1)) (hS : DegHomogenous S d) :
    DegHomogenous (stripSection S p k) (d - k) := by
  intro u hu
  have := hS _ (mem_stripSection.mp hu)
  rw [insertIndex_sum] at this
  omega

theorem stripSection_iCompression_initial {n d k : ℕ}
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1)) :
    ColexInitial (stripSection (iCompression S p d) p k) := by
  intro u v hu hd hle
  rw [mem_stripSection] at hu ⊢
  refine iCompression_iLower (k := k) (by simp) ((insertIndex_colex_le p k v u).mpr hle) ?_ hu
  refine (mem_iUniv p k d _).mpr ⟨Finset.mem_finsuppAntidiag.mpr
    ⟨?_, Finset.subset_univ _⟩, by simp⟩
  simpa only [insertIndex_sum, hd] using (iCompression_homogeneous S p d) _ hu

/-- Each compressed slice is exactly ACompression in one fewer variable. -/
theorem stripSection_iCompression_eq {n d k : ℕ}
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1)) (hS : DegHomogenous S d) :
    stripSection (iCompression S p d) p k = ACompression (stripSection S p k) (d - k) := by
  simpa only [ACompression, stripSection_card,
    iPart_iCompression_card p (degHomogenous_iff_subset.mp hS)] using
    colexInitial_eq_compression (stripSection_homogeneous p (iCompression_homogeneous S p d))
      (stripSection_iCompression_initial p)

lemma insertIndex_add_above {n : ℕ} (p : Fin (n + 1)) (k : ℕ)
    (w : Fin n →₀ ℕ) (t : Fin n) :
    insertIndex p k (w + Finsupp.single t 1) =
      insertIndex p k w + Finsupp.single (p.succAbove t) 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove p j with heq | ⟨s, rfl⟩
  · subst j
    simp
  · simp [Finsupp.single_apply, Fin.succAbove_inj]

lemma insertIndex_add_pivot {n : ℕ} (p : Fin (n + 1)) (k : ℕ)
    (w : Fin n →₀ ℕ) :
    insertIndex p (k + 1) w = insertIndex p k w + Finsupp.single p 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove p j with heq | ⟨s, rfl⟩
  · subst j
    simp
  · simp


/-- A shadow slice consists of the shadow of this slice and the next slice. -/
theorem stripSection_shadow_eq {n : ℕ} (S : Finset (Fin (n + 1) →₀ ℕ))
    (p : Fin (n + 1)) (k : ℕ) :
    stripSection (Shadow S) p k = Shadow (stripSection S p k) ∪ stripSection S p (k + 1) := by
  ext u
  simp only [mem_stripSection, mem_Shadow, Finset.mem_union, Fin.exists_iff_succAbove p,
    insertIndex_add_above, insertIndex_add_pivot]
  exact or_comm

lemma card_eq_sum_iPart {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (p : Fin n)
    (I : Finset ℕ) (hI : S.image (fun v ↦ v p) ⊆ I) :
    S.card = ∑ k ∈ I, (iPart S p k).card :=
  Finset.card_eq_sum_card_fiberwise fun v hv ↦ hI (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- The smaller-variable theorem is used only here, on the current slice. -/
theorem iCompression_shadow_section_le {n d : ℕ}
    (ih : ∀ {k} {A : Finset (Fin n →₀ ℕ)}, DegHomogenous A k → MacaulayProp k A)
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1)) (hS : DegHomogenous S d) (k : ℕ) :
    (iPart (Shadow (iCompression S p d)) p k).card ≤ (iPart (Shadow S) p k).card := by
  rw [← stripSection_card, ← stripSection_card, stripSection_shadow_eq, stripSection_shadow_eq,
    stripSection_iCompression_eq p hS, stripSection_iCompression_eq p hS]
  let A := stripSection S p k
  let B := stripSection S p (k + 1)
  obtain h | h := ColexInitial.comparable (ColexInitial.shadow (ACompression_colexInitial A (d - k)))
    (ACompression_colexInitial B (d - (k + 1)))
    (by simpa only [Nat.sub_sub] using (DegHomogenous.shadow (ACompression_homogeneous A (d - k))))
    (ACompression_homogeneous B (d - (k + 1)))
  · rw [Finset.union_eq_right.mpr h,
      card_ACompression (degHomogenous_iff_subset.mp (stripSection_homogeneous p hS))]
    exact Finset.card_mono Finset.subset_union_right
  · rw [Finset.union_eq_left.mpr h]
    exact (ih (stripSection_homogeneous p hS)).trans (Finset.card_mono Finset.subset_union_left)

/-- Summing the slice bounds proves the coordinate-compression inequality. -/
theorem iCompression_shadow_le {n d : ℕ}
    (ih : ∀ {k} {A : Finset (Fin n →₀ ℕ)}, DegHomogenous A k → MacaulayProp k A)
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1)) (hS : DegHomogenous S d) :
    (Shadow (iCompression S p d)).card ≤ (Shadow S).card := by
  let T := iCompression S p d
  let I := (Shadow S).image (fun q ↦ q p) ∪ (Shadow T).image (fun q ↦ q p)
  calc
    (Shadow T).card = ∑ k ∈ I, (iPart (Shadow T) p k).card :=
      card_eq_sum_iPart _ p I Finset.subset_union_right
    _ ≤ ∑ k ∈ I, (iPart (Shadow S) p k).card :=
      Finset.sum_le_sum fun k _ ↦ iCompression_shadow_section_le ih p hS k
    _ = (Shadow S).card := (card_eq_sum_iPart _ p I Finset.subset_union_left).symm


/-- Merge the first two exponents. -/
noncomputable def mergeFirstTwo {n : ℕ} (u : Fin (n + 2) →₀ ℕ) : Fin (n + 2) →₀ ℕ :=
  u.erase 0 + Finsupp.single 1 (u 0)

@[simp] lemma mergeFirstTwo_zero {n : ℕ} (u : Fin (n + 2) →₀ ℕ) :
    mergeFirstTwo u 0 = 0 := by simp [mergeFirstTwo]

@[simp] lemma mergeFirstTwo_one {n : ℕ} (u : Fin (n + 2) →₀ ℕ) :
    mergeFirstTwo u 1 = u 0 + u 1 := by simp [mergeFirstTwo, add_comm]

lemma mergeFirstTwo_above {n : ℕ} (u : Fin (n + 2) →₀ ℕ) {i : Fin (n + 2)}
    (hi : 1 < i) : mergeFirstTwo u i = u i := by
  simp [mergeFirstTwo, hi.ne.symm, ((Fin.zero_le 1).trans_lt hi).ne.symm]

lemma mergeFirstTwo_sum {n : ℕ} (u : Fin (n + 2) →₀ ℕ) :
    (∑ i, mergeFirstTwo u i) = ∑ i, u i := by
  simpa [mergeFirstTwo, Finset.sum_add_distrib] using
    congrArg (fun v : Fin (n + 2) →₀ ℕ ↦ ∑ i, v i) (Finsupp.erase_add_single 0 u)

/-- The merged vector depends only on the tail and the total degree. -/
lemma mergeFirstTwo_eq_of_tail {n : ℕ} {u v : Fin (n + 2) →₀ ℕ}
    (hd : (∑ i, u i) = ∑ i, v i)
    (ht : ∀ j : Fin n, u j.succ.succ = v j.succ.succ) : mergeFirstTwo u = mergeFirstTwo v := by
  have hs : (∑ j : Fin n, u j.succ.succ) = ∑ j : Fin n, v j.succ.succ :=
    Finset.sum_congr rfl (fun j _ ↦ ht j)
  have hp : u 0 + u 1 = v 0 + v 1 := by
    simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one] at hd
    omega
  ext i
  refine Fin.cases (by simp) (fun j ↦ Fin.cases (by simpa using hp)
    (fun j ↦ by simpa only [mergeFirstTwo_above u (Fin.one_lt_succ_succ j),
      mergeFirstTwo_above v (Fin.one_lt_succ_succ j)] using ht j) j) i

/-- Colex is decided in the unchanged tail, or the merged vectors are equal. -/
theorem mergeFirstTwo_colex_mono {n : ℕ} {u v : Fin (n + 2) →₀ ℕ}
    (hd : (∑ i, u i) = ∑ i, v i) (hle : toColex u ≤ toColex v) :
    toColex (mergeFirstTwo u) ≤ toColex (mergeFirstTwo v) := by
  rcases hle.lt_or_eq with h | h
  · obtain ⟨i, ht, hi⟩ := Finsupp.Colex.lt_def.mp h
    by_cases h1i : 1 < i
    · refine le_of_lt (Finsupp.Colex.lt_def.mpr ⟨i, fun j hj ↦ ?_, ?_⟩)
      · simpa only [mergeFirstTwo_above u (h1i.trans hj), mergeFirstTwo_above v (h1i.trans hj)]
          using ht j hj
      · simpa only [mergeFirstTwo_above u h1i, mergeFirstTwo_above v h1i] using hi
    · exact (congrArg toColex (mergeFirstTwo_eq_of_tail hd
        (fun j ↦ ht _ (lt_of_le_of_lt (le_of_not_gt h1i) (Fin.one_lt_succ_succ j))))).le
  · exact (congrArg (fun u ↦ toColex (mergeFirstTwo u)) (toColex_inj.mp h)).le

end Macaulay
