import CcaInLean.MacaulayAnderson.Compression
import CcaInLean.MacaulayAnderson.Shadow
import CcaInLean.MacaulayAnderson.iCompression

/-!
# Macaulay's lower-shadow theorem

The main theorem is `MacaulayMinimal.macaulay_shadow`. The proof uses
coordinate compression and a smallest-cardinality counterexample.

It imports the existing `Lemma1` and `Lemma2` definitions. The original
`iCompression_contraction` in `Lemma2` has its inequality backwards; this
file proves the correct direction independently and never uses that lemma.
Consequently the proof also works with the original, unfinished `Lemma2`.
-/

open Finset

namespace Macaulay

/-- A family is homogeneous of degree `k`. -/
def DegHomogenous {m : ℕ} (𝒜 : Finset (Fin m →₀ ℕ)) (k : ℕ) : Prop :=
  ∀ a ∈ 𝒜, (∑ i, a i) = k

/-- The colex family of the same size has no larger shadow. -/
def MacaulayProp {m : ℕ} (k : ℕ) (𝒜 : Finset (Fin m →₀ ℕ)) : Prop :=
  (Shadow (Compression (Finset.univ.finsuppAntidiag k : Finset (Fin m →₀ ℕ)) 𝒜.card)).card
    ≤ (Shadow 𝒜).card

/-- A smallest-cardinality counterexample in a fixed degree and dimension. -/
structure MC (m k : ℕ) where
  𝒜 : Finset (Fin m →₀ ℕ)
  degHomo : DegHomogenous 𝒜 k
  cardMin : ∀ ℬ : Finset (Fin m →₀ ℕ), ℬ ⊆ 𝒜 →
    ℬ.card < 𝒜.card → MacaulayProp k ℬ
  counter : ¬ MacaulayProp k 𝒜

/-- Homogeneity packages the ambient-degree hypothesis used by compression. -/
theorem MC.subset_degreeLayer {m k : ℕ} (c : MC m k) :
    c.𝒜 ⊆ Finset.univ.finsuppAntidiag k := by
  intro a ha
  apply Finset.mem_finsuppAntidiag.mpr
  exact ⟨c.degHomo a ha, Finset.subset_univ _⟩

/-- A family is initial among monomials of the same degree. -/
def ColexInitial {n : ℕ} (S : Finset (Fin n →₀ ℕ)) : Prop :=
  ∀ {u v}, u ∈ S → (∑ i, v i) = (∑ i, u i) → toColex v ≤ toColex u → v ∈ S

/-- Erasing a monomial from an initial family can remove at most one divisor
from its lower shadow. -/
theorem shadow_erase_subset_insert {n : ℕ}
    {C : Finset (Fin (n + 1) →₀ ℕ)} (hC : ColexInitial C) {u : Fin (n + 1) →₀ ℕ}
    (hu : u ∈ C) :
    Shadow C ⊆ insert (u - Finsupp.single 0 1) (Shadow (C.erase u)) := by
  intro q hq
  by_cases hq' : q ∈ Shadow (C.erase u)
  · exact Finset.mem_insert_of_mem hq'
  · obtain ⟨i, hi⟩ := mem_Shadow.mp hq
    have hqi : q + Finsupp.single i 1 = u := by
      by_contra hne
      apply hq'
      exact mem_Shadow.mpr ⟨i, Finset.mem_erase.mpr ⟨hne, hi⟩⟩
    by_cases hi0 : i = 0
    · subst i
      apply Finset.mem_insert.mpr
      left
      rw [← hqi]
      simp
    · have h0i : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
      have hlt : toColex (q + Finsupp.single (0 : Fin (n + 1)) 1) < toColex u := by
        rw [← hqi, toColex_add, toColex_add]
        exact add_lt_add_right (Colex_single_lt_single h0i) (toColex q)
      have hdeg :
          (∑ j : Fin (n + 1), (q + Finsupp.single (0 : Fin (n + 1)) 1 :
            Fin (n + 1) →₀ ℕ) j) = ∑ j, u j := by
        rw [← hqi]
        simp [Finset.sum_add_distrib]
      have hx := hC hu hdeg (le_of_lt hlt)
      have hne : q + Finsupp.single (0 : Fin (n + 1)) 1 ≠ u := by
        intro heq
        rw [heq] at hlt
        exact (lt_irrefl _) hlt
      exact (hq' (mem_Shadow.mpr ⟨0, Finset.mem_erase.mpr ⟨hne, hx⟩⟩)).elim

theorem shadow_erase_card_le {n : ℕ}
    {C : Finset (Fin (n + 1) →₀ ℕ)} (hC : ColexInitial C) {u : Fin (n + 1) →₀ ℕ}
    (hu : u ∈ C) : (Shadow C).card ≤ (Shadow (C.erase u)).card + 1 := by
  exact (Finset.card_le_card (shadow_erase_subset_insert hC hu)).trans
    (Finset.card_insert_le _ _)

/-- The colex benchmark's lower-shadow cardinality grows by at most one. -/
theorem compression_shadow_step {m d k : ℕ}
    (hpos : 0 < k)
    (hk : k ≤ (Finset.univ.finsuppAntidiag d : Finset (Fin m →₀ ℕ)).card) :
    (Shadow (Compression (Finset.univ.finsuppAntidiag d :
      Finset (Fin m →₀ ℕ)) k)).card ≤
    (Shadow (Compression (Finset.univ.finsuppAntidiag d :
      Finset (Fin m →₀ ℕ)) (k - 1))).card + 1 := by
  let U : Finset (Fin m →₀ ℕ) := Finset.univ.finsuppAntidiag d
  let C := Compression U k
  let P := Compression U (k - 1)
  have hPC : P ⊆ C := compression_mono (by omega)
  have hkU : k ≤ U.card := hk
  have hPcard : P.card = k - 1 := card_compression ((Nat.sub_le k 1).trans hkU)
  have hCcard : C.card = k := card_compression hkU
  have hlt : P.card < C.card := by omega
  obtain ⟨u, hu, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hPsub : P ⊆ C.erase u := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, hPC hx⟩
    intro heq
    subst x
    exact hnot hx
  have hP : P = C.erase u := by
    apply Finset.eq_of_subset_of_card_le hPsub
    rw [Finset.card_erase_of_mem hu]
    omega
  have hinit : ColexInitial C := compression_colexInitial d k
  have h := shadow_erase_card_le hinit hu -- this gives an error
  rw [← hP] at h
  exact h

-- This code is very ugly, I am sur it can be greatly erduced in length
/-- Minimality forces every monomial to have no private divisor. -/
theorem MC.erase_shadow_eq {m k : ℕ} (c : MC m k) {u : Fin m →₀ ℕ}
    (hu : u ∈ c.𝒜) : Shadow (c.𝒜.erase u) = Shadow c.𝒜 := by
  have hpos : 0 < c.𝒜.card := by
    by_contra h
    have hempty : c.𝒜 = ∅ := Finset.card_eq_zero.mp (by omega)
    apply c.counter
    rw [hempty]
    simp [MacaulayProp, Compression, Shadow]
  have hsmall : (Shadow (Compression (Finset.univ.finsuppAntidiag k :
      Finset (Fin m →₀ ℕ)) (c.𝒜.card - 1))).card ≤
      (Shadow (c.𝒜.erase u)).card := by
    simpa [MacaulayProp, Finset.card_erase_of_mem hu] using
      c.cardMin (c.𝒜.erase u) (Finset.erase_subset u c.𝒜)
        (Finset.card_erase_lt_of_mem hu)
  have hstep := compression_shadow_step hpos
    (Finset.card_le_card c.subset_degreeLayer)
  have hbad : (Shadow c.𝒜).card <
      (Shadow (Compression (Finset.univ.finsuppAntidiag k :
        Finset (Fin m →₀ ℕ)) c.𝒜.card)).card :=
    Nat.lt_of_not_ge (by simpa [MacaulayProp] using c.counter)
  have hshadow : Shadow (c.𝒜.erase u) ⊆ Shadow c.𝒜 := by
    intro q hq
    obtain ⟨i, hi⟩ := mem_Shadow.mp hq
    exact mem_Shadow.mpr ⟨i, Finset.erase_subset u c.𝒜 hi⟩
  apply Finset.eq_of_subset_of_card_le hshadow
  have huCard : (c.𝒜.erase u).card = c.𝒜.card - 1 :=
    Finset.card_erase_of_mem hu
  omega

/-- Every divisor belongs to a second, distinct monomial in an `MC`. -/
theorem MC.otherExtension {m k : ℕ} (c : MC m k) {q : Fin m →₀ ℕ} {i : Fin m}
    (hqi : q + Finsupp.single i 1 ∈ c.𝒜) :
    ∃ j : Fin m, j ≠ i ∧ q + Finsupp.single j 1 ∈ c.𝒜 := by
  have hq : q ∈ Shadow c.𝒜 := mem_Shadow.mpr ⟨i, hqi⟩
  rw [← c.erase_shadow_eq hqi] at hq
  obtain ⟨j, hj⟩ := mem_Shadow.mp hq
  have hj' := Finset.mem_erase.mp hj
  refine ⟨j, ?_, hj'.2⟩
  intro hji
  subst j
  exact hj'.1 rfl

/-- In an `MC`, shifting and minimality permit exchanging the first two
variables one factor at a time. -/
theorem MC.firstTwoExchange {n k : ℕ} (c : MC (n + 2) k)
    (hshift : ∀ q i j, i ≤ j → q + Finsupp.single j 1 ∈ c.𝒜 →
      q + Finsupp.single i 1 ∈ c.𝒜) (q : Fin (n + 2) →₀ ℕ) :
    q + Finsupp.single (0 : Fin (n + 2)) 1 ∈ c.𝒜 ↔
      q + Finsupp.single (1 : Fin (n + 2)) 1 ∈ c.𝒜 := by
  constructor
  · intro hq
    obtain ⟨j, hj0, hj⟩ := c.otherExtension hq
    have hjpos : (0 : Fin (n + 2)) < j := Fin.pos_iff_ne_zero.mpr hj0
    have hj1 : (1 : Fin (n + 2)) ≤ j := by
      change 1 ≤ j.val
      change 0 < j.val at hjpos
      omega
    exact hshift q 1 j hj1 hj
  · intro hq
    exact hshift q 0 1 (by simp) hq

/-- The first two variables can be exchanged in blocks, not just one factor
at a time. -/
theorem MC.firstTwoBlockExchange {n d : ℕ} (c : MC (n + 2) d)
    (hshift : ∀ q i j, i ≤ j → q + Finsupp.single j 1 ∈ c.𝒜 →
      q + Finsupp.single i 1 ∈ c.𝒜) (q : Fin (n + 2) →₀ ℕ) (r : ℕ) :
    q + Finsupp.single (0 : Fin (n + 2)) r ∈ c.𝒜 ↔
      q + Finsupp.single (1 : Fin (n + 2)) r ∈ c.𝒜 := by
  induction r generalizing q with
  | zero => simp
  | succ r ih =>
    calc
      q + Finsupp.single (0 : Fin (n + 2)) (r + 1) ∈ c.𝒜 ↔
          (q + Finsupp.single 0 r) + Finsupp.single 0 1 ∈ c.𝒜 := by
            simp [Finsupp.single_add, add_assoc]
      _ ↔ (q + Finsupp.single 0 r) + Finsupp.single 1 1 ∈ c.𝒜 :=
          c.firstTwoExchange hshift _
      _ ↔ (q + Finsupp.single 1 1) + Finsupp.single 0 r ∈ c.𝒜 := by
            simp [add_assoc, add_comm, add_left_comm]
      _ ↔ (q + Finsupp.single 1 1) + Finsupp.single 1 r ∈ c.𝒜 := ih _
      _ ↔ q + Finsupp.single (1 : Fin (n + 2)) (r + 1) ∈ c.𝒜 := by
            simp [Finsupp.single_add, add_comm, add_left_comm]

/-- Move all of the exponent of the first variable to the second. -/
noncomputable def mergeFirstTwo {n : ℕ} (u : Fin (n + 2) →₀ ℕ) : Fin (n + 2) →₀ ℕ :=
  u.erase 0 + Finsupp.single 1 (u 0)

@[simp] lemma mergeFirstTwo_zero {n : ℕ} (u : Fin (n + 2) →₀ ℕ) :
    mergeFirstTwo u 0 = 0 := by
  simp [mergeFirstTwo]

@[simp] lemma mergeFirstTwo_one {n : ℕ} (u : Fin (n + 2) →₀ ℕ) :
    mergeFirstTwo u 1 = u 0 + u 1 := by
  simp [mergeFirstTwo, add_comm]

lemma mergeFirstTwo_other {n : ℕ} (u : Fin (n + 2) →₀ ℕ) (i : Fin (n + 2))
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) : mergeFirstTwo u i = u i := by
  simp [mergeFirstTwo, hi0, hi1]

lemma mergeFirstTwo_sum {n : ℕ} (u : Fin (n + 2) →₀ ℕ) :
    (∑ i, mergeFirstTwo u i) = ∑ i, u i := by
  have h := congrArg (fun v : Fin (n + 2) →₀ ℕ => ∑ i, v i)
    (Finsupp.erase_add_single 0 u)
  simpa [mergeFirstTwo, Finset.sum_add_distrib] using h

theorem MC.mem_mergeFirstTwo {n d : ℕ} (c : MC (n + 2) d)
    (hshift : ∀ q i j, i ≤ j → q + Finsupp.single j 1 ∈ c.𝒜 →
      q + Finsupp.single i 1 ∈ c.𝒜) (u : Fin (n + 2) →₀ ℕ) :
    u ∈ c.𝒜 ↔ mergeFirstTwo u ∈ c.𝒜 := by
  have h := c.firstTwoBlockExchange hshift (u.erase 0) (u 0)
  rw [Finsupp.erase_add_single] at h
  exact h

/-- Three variables leave a coordinate distinct from any specified pair. -/
lemma exists_third_coordinate {n : ℕ} (i j : Fin (n + 3)) :
    ∃ p : Fin (n + 3), p ≠ i ∧ p ≠ j := by
  have htwo : ({i, j} : Finset (Fin (n + 3))).card ≤ 2 := Finset.card_le_two
  have hcard : ({i, j} : Finset (Fin (n + 3))).card <
      (Finset.univ : Finset (Fin (n + 3))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨p, hp.1, hp.2⟩



/-- Coordinate-compression makes an `MC` closed under shifting. -/
theorem MC.shifted_of_iCompressed {n d : ℕ} (c : MC (n + 3) d)
    (hcomp : ∀ i, iCompression c.𝒜 i d = c.𝒜) :
    ∀ (q : Fin (n + 3) →₀ ℕ) (i j : Fin (n + 3)), i ≤ j →
      q + Finsupp.single j 1 ∈ c.𝒜 → q + Finsupp.single i 1 ∈ c.𝒜 := by
  intro q i j hij hj
  have hS := c.subset_degreeLayer
  obtain ⟨p, hpi, hpj⟩ := exists_third_coordinate i j
  have hsame : (q + Finsupp.single i 1 : Fin (n + 3) →₀ ℕ) p =
      (q + Finsupp.single j 1 : Fin (n + 3) →₀ ℕ) p := by
    simp [hpi, hpj]
  have hle : toColex (q + Finsupp.single i 1) ≤ toColex (q + Finsupp.single j 1) := by
    rw [toColex_add, toColex_add]
    simpa [add_comm] using add_le_add_right (Colex_single_le_single hij) (toColex q)
  have hlevel : q + Finsupp.single i 1 ∈
      (Finset.univ.finsuppAntidiag d : Finset (Fin (n + 3) →₀ ℕ)) := by
    have hjd := (Finset.mem_finsuppAntidiag.mp (hS hj)).1
    apply Finset.mem_finsuppAntidiag.mpr
    refine ⟨?_, Finset.subset_univ _⟩
    simpa [Finset.sum_add_distrib] using hjd
  have hU : q + Finsupp.single i 1 ∈ iUniv p ((q + Finsupp.single i 1 : Fin (n + 3) →₀ ℕ) p) d := by
    simp [mem_iUniv, hlevel]
  have hJ : q + Finsupp.single j 1 ∈ iCompression c.𝒜 p d := by
    rw [hcomp p]
    exact hj
  have h := iCompression_iLower hsame hle hU hJ
  rw [hcomp p] at h
  exact h

/-- Merging the first two coordinates weakly preserves colex on a degree layer. -/
theorem mergeFirstTwo_colex_mono {n : ℕ} {u v : Fin (n + 2) →₀ ℕ}
    (hdeg : (∑ i, u i) = ∑ i, v i) (hle : toColex u ≤ toColex v) :
    toColex (mergeFirstTwo u) ≤ toColex (mergeFirstTwo v) := by
  by_cases htail : ∀ i : Fin (n + 2), 1 < i → u i = v i
  · have htailSum : (∑ j : Fin n, u j.succ.succ) = ∑ j : Fin n, v j.succ.succ := by
      apply Finset.sum_congr rfl
      intro j _
      apply htail
      change 1 < j.val + 1 + 1
      omega
    have hpair : u 0 + u 1 = v 0 + v 1 := by
      have h := hdeg
      simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one] at h
      rw [htailSum] at h
      omega
    have heq : mergeFirstTwo u = mergeFirstTwo v := by
      ext i
      by_cases hi0 : i = 0
      · subst i
        simp
      by_cases hi1 : i = 1
      · subst i
        simp [hpair]
      have hi0v := Fin.val_ne_of_ne hi0
      have hi1v := Fin.val_ne_of_ne hi1
      simp only [Fin.val_zero] at hi0v
      simp only [Fin.val_one] at hi1v
      have h1i : (1 : Fin (n + 2)) < i := by
        change 1 < i.val
        omega
      rw [mergeFirstTwo_other u i hi0 hi1, mergeFirstTwo_other v i hi0 hi1]
      exact htail i h1i
    rw [heq]
  · push Not at htail
    obtain ⟨k, hk, hneq⟩ := htail
    have huv : u ≠ v := by
      intro heq
      subst v
      exact hneq rfl
    have hne : toColex u ≠ toColex v := fun h => huv (toColex_inj.mp h)
    have hlt : toColex u < toColex v := lt_of_le_of_ne hle hne
    obtain ⟨j, hjtail, hjlt⟩ := Finsupp.Colex.lt_def.mp hlt
    have h1j : (1 : Fin (n + 2)) < j := by
      by_contra hn
      have hj1 : j ≤ 1 := le_of_not_gt hn
      exact hneq (hjtail k (lt_of_le_of_lt hj1 hk))
    have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (by simp) h1j)
    have hj1 : j ≠ 1 := ne_of_gt h1j
    apply le_of_lt
    apply Finsupp.Colex.lt_def.mpr
    refine ⟨j, ?_, ?_⟩
    · intro t ht
      have h1t : (1 : Fin (n + 2)) < t := lt_trans h1j ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_le_of_lt (by simp) h1t)
      have ht1 : t ≠ 1 := ne_of_gt h1t
      rw [mergeFirstTwo_other u t ht0 ht1, mergeFirstTwo_other v t ht0 ht1]
      exact hjtail t ht
    · rw [mergeFirstTwo_other u j hj0 hj1, mergeFirstTwo_other v j hj0 hj1]
      exact hjlt

/-- A coordinate-compressed `MC` is colex-initial. -/
theorem MC.colexInitial_of_iCompressed {n d : ℕ} (c : MC (n + 3) d)
    (hcomp : ∀ i, iCompression c.𝒜 i d = c.𝒜) : ColexInitial c.𝒜 := by
  have hS := c.subset_degreeLayer
  have hshift := c.shifted_of_iCompressed hcomp
  intro v u hu hdeg hle
  have hmulevel : mergeFirstTwo u ∈
      (Finset.univ.finsuppAntidiag d : Finset (Fin (n + 3) →₀ ℕ)) := by
    apply Finset.mem_finsuppAntidiag.mpr
    refine ⟨?_, Finset.subset_univ _⟩
    rw [mergeFirstTwo_sum, hdeg]
    exact (Finset.mem_finsuppAntidiag.mp (hS hu)).1
  have hU : mergeFirstTwo u ∈ iUniv 0 0 d := by
    simp [mem_iUniv, hmulevel]
  have hu' : mergeFirstTwo v ∈ c.𝒜 := (c.mem_mergeFirstTwo hshift v).mp hu
  have hcompu : mergeFirstTwo v ∈ iCompression c.𝒜 0 d := by
    rw [hcomp 0]
    exact hu'
  have hsame : mergeFirstTwo u 0 = mergeFirstTwo v 0 := by simp
  have hmerged : toColex (mergeFirstTwo u) ≤ toColex (mergeFirstTwo v) :=
    mergeFirstTwo_colex_mono hdeg hle
  have h := iCompression_iLower hsame hmerged hU hcompu
  rw [hcomp 0] at h
  exact (c.mem_mergeFirstTwo hshift u).mpr h

/-- A colex-initial subset of a degree layer is its cardinality's compression. -/
theorem colexInitial_eq_compression {n d : ℕ} {S : Finset (Fin n →₀ ℕ)}
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) (hinit : ColexInitial S) :
    S = Compression (Finset.univ.finsuppAntidiag d) S.card := by
  let U : Finset (Fin n →₀ ℕ) := Finset.univ.finsuppAntidiag d
  let C := Compression U S.card
  have hcard : C.card = S.card := card_compression (Finset.card_le_card hS)
  have hsub : S ⊆ C := by
    intro x hx
    by_contra hnot
    have hnotsub : ¬ C ⊆ S := by
      intro hCS
      have heq : C = S := Finset.eq_of_subset_of_card_le hCS (by omega)
      rw [heq] at hnot
      exact hnot hx
    have hex : ∃ y ∈ C, y ∉ S := by
      by_contra h
      push Not at h
      exact hnotsub h
    obtain ⟨y, hy, hynot⟩ := hex
    have hyx : toColex y < toColex x := by
      by_contra h
      have hxy : toColex x ≤ toColex y := le_of_not_gt h
      exact hnot (lower_set_compression hxy (hS hx) (mem_compression hy) hy)
    have hyU : y ∈ U := mem_compression hy
    have hxU : x ∈ U := hS hx
    have hdeg : (∑ i, y i) = ∑ i, x i :=
      (Finset.mem_finsuppAntidiag.mp hyU).1.trans
        (Finset.mem_finsuppAntidiag.mp hxU).1.symm
    exact hynot (hinit hx hdeg (le_of_lt hyx))
  change S = C
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- The minimal-counterexample argument reduces Macaulay's inequality to
showing that each coordinate compression does not increase the shadow. -/
theorem macaulay_of_iCompression_shadow_le {n d m : ℕ}
    (hcompress : ∀ T : Finset (Fin (n + 3) →₀ ℕ),
      T ⊆ Finset.univ.finsuppAntidiag d → ∀ i,
      (Shadow (iCompression T i d)).card ≤ (Shadow T).card)
    (hsmall : ∀ T : Finset (Fin (n + 3) →₀ ℕ),
      T ⊆ Finset.univ.finsuppAntidiag d → T.card < m →
      MacaulayProp d T)
    (S : Finset (Fin (n + 3) →₀ ℕ))
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) (hcard : S.card = m) :
    MacaulayProp d S := by
  classical
  let U : Finset (Fin (n + 3) →₀ ℕ) := Finset.univ.finsuppAntidiag d
  let C := Compression U m
  by_contra hwrong
  have hbadS : (Shadow S).card < (Shadow C).card :=
    Nat.lt_of_not_ge (by simpa [MacaulayProp, C, U, hcard] using hwrong)
  let bad : Finset (Finset (Fin (n + 3) →₀ ℕ)) :=
    U.powerset.filter fun T => T.card = m ∧ (Shadow T).card < (Shadow C).card
  have hSbad : S ∈ bad := by
    simp only [bad, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hS, hcard, hbadS⟩
  let ranks := bad.image (fun T => toColex (T.image toColex))
  have hranks : ranks.Nonempty := ⟨toColex (S.image toColex),
    Finset.mem_image.mpr ⟨S, hSbad, rfl⟩⟩
  obtain ⟨B, hB, hBmin⟩ := Finset.mem_image.mp (Finset.min'_mem ranks hranks)
  have hBprops : B ⊆ U ∧ B.card = m ∧ (Shadow B).card < (Shadow C).card := by
    simpa [bad] using hB
  obtain ⟨hBU, hBm, hBbad⟩ := hBprops
  have hcompB : ∀ i, iCompression B i d = B := by
    intro i
    let T := iCompression B i d
    have hTU : T ⊆ U := iCompression_subset i d
    have hTm : T.card = m := by
      change (iCompression B i d).card = m
      rw [← card_iCompression i d hBU]
      exact hBm
    have hTbad : (Shadow T).card < (Shadow C).card :=
      lt_of_le_of_lt (hcompress B hBU i) hBbad
    have hT : T ∈ bad := by simp [bad, hTU, hTm, hTbad]
    have hmin : toColex (B.image toColex) ≤ toColex (T.image toColex) := by
      rw [hBmin]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
    have hless : toColex (T.image toColex) ≤ toColex (B.image toColex) :=
      iCompression_colex_le i hBU
    have heq := toColex_inj.mp (le_antisymm hless hmin)
    simpa only [image_colex] using heq
  let c : MC (n + 3) d := {
    𝒜 := B
    degHomo := by
      intro a ha
      exact (Finset.mem_finsuppAntidiag.mp (hBU ha)).1
    cardMin := by
      intro T hTB hlt
      exact hsmall T (hTB.trans hBU) (by omega)
    counter := by
      intro hle
      exact (not_le_of_gt hBbad) (sorry)
  }
  have hinit : ColexInitial B := by
    change ColexInitial c.𝒜
    exact c.colexInitial_of_iCompressed hcompB
  have hBeq : B = C := by
    simpa [C, U, hBm] using colexInitial_eq_compression hBU hinit
  rw [← hBeq] at hBbad
  omega

/-- For at least three variables, the shadow inequality follows once one
proves that each coordinate compression does not enlarge the shadow. -/
theorem macaulay_of_shadow_compression {n d : ℕ}
    (hcompress : ∀ T : Finset (Fin (n + 3) →₀ ℕ),
      T ⊆ Finset.univ.finsuppAntidiag d → ∀ i,
      (Shadow (iCompression T i d)).card ≤ (Shadow T).card)
    (S : Finset (Fin (n + 3) →₀ ℕ))
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) : MacaulayProp d S := by
  have hall : ∀ m, ∀ T : Finset (Fin (n + 3) →₀ ℕ),
      T ⊆ Finset.univ.finsuppAntidiag d → T.card = m →
      MacaulayProp d T := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hT hTm
      apply macaulay_of_iCompression_shadow_le hcompress ?_ T hT hTm
      intro V hV hVlt
      exact ih V.card hVlt V hV rfl
  exact hall S.card S hS rfl

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

/-- The `k`th coordinate section, viewed as monomials in one fewer variable. -/
noncomputable def stripSection {n : ℕ} (S : Finset (Fin (n + 1) →₀ ℕ))
    (p : Fin (n + 1)) (k : ℕ) : Finset (Fin n →₀ ℕ) :=
  (iPart S p k).image (eraseIndex p)

lemma eraseIndex_injective_on_slice {n : ℕ} (p : Fin (n + 1))
    {u v : Fin (n + 1) →₀ ℕ} (hp : u p = v p)
    (h : eraseIndex p u = eraseIndex p v) : u = v := by
  calc
    u = insertIndex p (u p) (eraseIndex p u) := (insertIndex_eraseIndex p u).symm
    _ = insertIndex p (v p) (eraseIndex p v) := by rw [hp, h]
    _ = v := insertIndex_eraseIndex p v

lemma stripSection_card {n : ℕ} (S : Finset (Fin (n + 1) →₀ ℕ))
    (p : Fin (n + 1)) (k : ℕ) : (stripSection S p k).card = (iPart S p k).card := by
  unfold stripSection
  apply Finset.card_image_iff.mpr
  intro u hu v hv h
  exact eraseIndex_injective_on_slice p ((mem_iPart.mp hu).2.trans (mem_iPart.mp hv).2.symm) h

/-- Coordinate compression acts independently on each individual section. -/
theorem iPart_iCompression_eq {n d k : ℕ} {S : Finset (Fin n →₀ ℕ)} (p : Fin n) :
    iPart (iCompression S p d) p k = Compression (iUniv p k d) (iPart S p k).card := by
  ext u
  constructor
  · intro hu
    obtain ⟨hu, hup⟩ := mem_iPart.mp hu
    obtain ⟨j, hj, huj⟩ := Finset.mem_biUnion.mp hu
    have hju := (mem_iUniv p j d u).mp (mem_compression huj)
    have hjk : j = k := hju.2.symm.trans hup
    subst j
    exact huj
  · intro hu
    have hup := (mem_iUniv p k d u).mp (mem_compression hu)
    have hk : k ∈ S.image (fun v => v p) := by
      by_contra hn
      have hzero : iPart S p k = ∅ := by
        ext v
        constructor
        · intro hv
          obtain ⟨hv, hp⟩ := mem_iPart.mp hv
          exact (hn (Finset.mem_image.mpr ⟨v, hv, hp⟩)).elim
        · intro hv
          simp at hv
      simp [hzero, Compression] at hu
    apply mem_iPart.mpr
    refine ⟨?_, hup.2⟩
    exact Finset.mem_biUnion.mpr ⟨k, hk, hu⟩

lemma iPart_iCompression_card {n d k : ℕ} {S : Finset (Fin n →₀ ℕ)} (p : Fin n)
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) :
    (iPart (iCompression S p d) p k).card = (iPart S p k).card := by
  rw [iPart_iCompression_eq, card_compression]
  exact Finset.card_le_card (iPart_le_iUniv p k d hS)

/-- A section of a degree-`d` family has degree `d-k` after deletion. -/
theorem stripSection_subset_level {n d k : ℕ} {S : Finset (Fin (n + 1) →₀ ℕ)}
    (p : Fin (n + 1)) (hS : S ⊆ Finset.univ.finsuppAntidiag d) :
    stripSection S p k ⊆ Finset.univ.finsuppAntidiag (d - k) := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hu, hup⟩ := mem_iPart.mp hu
  have hdeg := (Finset.mem_finsuppAntidiag.mp (hS hu)).1
  rw [Fin.sum_univ_succAbove _ p] at hdeg
  have hsum : k + (∑ j, eraseIndex p u j) = d := by simpa [hup] using hdeg
  apply Finset.mem_finsuppAntidiag.mpr
  refine ⟨?_, Finset.subset_univ _⟩
  change (∑ j, eraseIndex p u j) = d - k
  omega

/-- Each section of an i-compressed family is colex-initial after deletion. -/
theorem stripSection_iCompression_initial {n d k : ℕ}
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1)) :
    ColexInitial (stripSection (iCompression S p d) p k) := by
  intro u v hu hdeg hle
  obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hu', hup⟩ := mem_iPart.mp hu'
  have hlevel := iCompression_subset p d hu'
  have hdeg' := (Finset.mem_finsuppAntidiag.mp hlevel).1
  rw [Fin.sum_univ_succAbove _ p] at hdeg'
  have hsum : k + (∑ j, eraseIndex p u' j) = d := by simpa [hup] using hdeg'
  have hvU : insertIndex p k v ∈ iUniv p k d := by
    rw [mem_iUniv]
    constructor
    · apply Finset.mem_finsuppAntidiag.mpr
      refine ⟨?_, Finset.subset_univ _⟩
      rw [insertIndex_sum, hdeg]
      exact hsum
    · simp
  have hp : insertIndex p k v p = u' p := by simp [hup]
  have hle' : toColex (insertIndex p k v) ≤ toColex u' := by
    by_contra h
    have hlt : toColex u' < toColex (insertIndex p k v) := lt_of_not_ge h
    have hlt' := (eraseIndex_colex_lt_iff p hp.symm).mpr hlt
    simp only [eraseIndex_insertIndex] at hlt'
    exact (not_lt_of_ge hle) hlt'
  have hv' := iCompression_iLower hp hle' hvU hu'
  apply Finset.mem_image.mpr
  refine ⟨insertIndex p k v, mem_iPart.mpr ⟨hv', by simp⟩, ?_⟩
  simp

/-- Deleting the fixed coordinate identifies each compressed section with an
ordinary colex segment in one fewer variable. -/
theorem stripSection_iCompression_eq {n d k : ℕ}
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1))
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) :
    stripSection (iCompression S p d) p k =
      Compression (Finset.univ.finsuppAntidiag (d - k) : Finset (Fin n →₀ ℕ))
        (stripSection S p k).card := by
  have hc : (stripSection (iCompression S p d) p k).card = (stripSection S p k).card := by
    rw [stripSection_card, iPart_iCompression_card p hS, stripSection_card]
  have hinit : ColexInitial (stripSection (iCompression S p d) p k) :=
    stripSection_iCompression_initial p
  have hlevel := stripSection_subset_level (k := k) p (iCompression_subset (S := S) p d)
  rw [← hc]
  exact colexInitial_eq_compression hlevel hinit

@[simp] lemma eraseIndex_add_pivot {n : ℕ} (p : Fin (n + 1))
    (q : Fin (n + 1) →₀ ℕ) :
    eraseIndex p (q + Finsupp.single p 1) = eraseIndex p q := by
  ext t
  simp [eraseIndex]

@[simp] lemma eraseIndex_add_above {n : ℕ} (p : Fin (n + 1))
    (q : Fin (n + 1) →₀ ℕ) (t : Fin n) :
    eraseIndex p (q + Finsupp.single (p.succAbove t) 1) =
      eraseIndex p q + Finsupp.single t 1 := by
  ext s
  simp [eraseIndex, Finsupp.single_apply, Fin.succAbove_inj]

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

/-- The shadow in a fixed coordinate is the union of the lower shadow of the
corresponding section and the next section. -/
theorem stripSection_shadow_eq {n : ℕ} (S : Finset (Fin (n + 1) →₀ ℕ))
    (p : Fin (n + 1)) (k : ℕ) :
    stripSection (Shadow S) p k = Shadow (stripSection S p k) ∪ stripSection S p (k + 1) := by
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, hqw⟩ := Finset.mem_image.mp hw
    obtain ⟨hq, hqp⟩ := mem_iPart.mp hq
    obtain ⟨j, hj⟩ := mem_Shadow.mp hq
    by_cases hjp : j = p
    · subst j
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨q + Finsupp.single p 1, mem_iPart.mpr ⟨hj, ?_⟩, ?_⟩
      · simp [hqp]
      · simpa using hqw
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hjp
      apply Finset.mem_union_left
      apply mem_Shadow.mpr
      refine ⟨t, Finset.mem_image.mpr ⟨q + Finsupp.single (p.succAbove t) 1, ?_, ?_⟩⟩
      · apply mem_iPart.mpr
        simp [hj, hqp]
      · simp [hqw]
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨t, ht⟩ := mem_Shadow.mp hw
      obtain ⟨u, hu, huq⟩ := Finset.mem_image.mp ht
      obtain ⟨hu, hup⟩ := mem_iPart.mp hu
      let q := insertIndex p k w
      have hqu : q + Finsupp.single (p.succAbove t) 1 = u := by
        rw [← insertIndex_add_above, ← huq, ← hup, insertIndex_eraseIndex]
      have hq : q ∈ Shadow S := mem_Shadow.mpr ⟨p.succAbove t, hqu ▸ hu⟩
      exact Finset.mem_image.mpr ⟨q, mem_iPart.mpr ⟨hq, by simp [q]⟩, by simp [q]⟩
    · obtain ⟨u, hu, huq⟩ := Finset.mem_image.mp hw
      obtain ⟨hu, hup⟩ := mem_iPart.mp hu
      let q := insertIndex p k w
      have hqu : q + Finsupp.single p 1 = u := by
        rw [← insertIndex_add_pivot, ← huq, ← hup, insertIndex_eraseIndex]
      have hq : q ∈ Shadow S := mem_Shadow.mpr ⟨p, hqu ▸ hu⟩
      exact Finset.mem_image.mpr ⟨q, mem_iPart.mpr ⟨hq, by simp [q]⟩, by simp [q]⟩

/-- Taking a lower shadow preserves the initial-segment property. -/
theorem ColexInitial.shadow {n : ℕ} {S : Finset (Fin n →₀ ℕ)}
    (hS : ColexInitial S) : ColexInitial (Shadow S) := by
  intro u v hu hdeg hle
  obtain ⟨i, hi⟩ := mem_Shadow.mp hu
  apply mem_Shadow.mpr
  refine ⟨i, hS hi ?_ ?_⟩
  · simp [Finset.sum_add_distrib, hdeg]
  · rw [toColex_add, toColex_add]
    grind

/-- Two initial families in the same degree are comparable by inclusion. -/
theorem ColexInitial.comparable {n : ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : ColexInitial A) (hB : ColexInitial B)
    (hdeg : ∀ x ∈ A, ∀ y ∈ B, (∑ i, x i) = ∑ i, y i) : A ⊆ B ∨ B ⊆ A := by
  by_cases h : A ⊆ B
  · exact Or.inl h
  · right
    have hex : ∃ x ∈ A, x ∉ B := by
      by_contra hn
      apply h
      intro x hx
      by_contra hxb
      exact hn ⟨x, hx, hxb⟩
    obtain ⟨x, hx, hxnot⟩ := hex
    intro y hy
    have hyx : toColex y ≤ toColex x := by
      by_contra hn
      have hxy : toColex x < toColex y := lt_of_not_ge hn
      exact hxnot (hB hy (hdeg x hx y hy) (le_of_lt hxy))
    exact hA hx (hdeg x hx y hy).symm hyx

lemma card_union_eq_max_of_nested {α : Type*} [DecidableEq α] {A B : Finset α}
    (h : A ⊆ B ∨ B ⊆ A) : (A ∪ B).card = max A.card B.card := by
  rcases h with h | h
  · rw [Finset.union_eq_right.mpr h, max_eq_right (Finset.card_le_card h)]
  · rw [Finset.union_eq_left.mpr h, max_eq_left (Finset.card_le_card h)]

/-- Count a family by its sections, using any finite set of coordinate values
that contains all values occurring in the family. -/
lemma card_eq_sum_iPart {n : ℕ} (X : Finset (Fin n →₀ ℕ)) (p : Fin n)
    (I : Finset ℕ) (hI : X.image (fun v => v p) ⊆ I) :
    X.card = ∑ k ∈ I, (iPart X p k).card := by
  have hunion : I.biUnion (fun k => iPart X p k) = X := by
    ext v
    simp only [Finset.mem_biUnion, mem_iPart]
    constructor
    · rintro ⟨k, hk, hv, _⟩
      exact hv
    · intro hv
      exact ⟨v p, hI (Finset.mem_image.mpr ⟨v, hv, rfl⟩), hv, rfl⟩
  have hdisj : (I : Set ℕ).PairwiseDisjoint (fun k => iPart X p k) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    exact hab ((mem_iPart.mp hva).2.symm.trans (mem_iPart.mp hvb).2)
  calc
    X.card = (I.biUnion (fun k => iPart X p k)).card := congrArg Finset.card hunion.symm
    _ = ∑ k ∈ I, (iPart X p k).card := Finset.card_biUnion hdisj

/-- Macaulay's shadow inequality in a specified number of variables. -/
def MacaulayInVars (n : ℕ) : Prop :=
  ∀ (d : ℕ) (S : Finset (Fin n →₀ ℕ)), S ⊆ Finset.univ.finsuppAntidiag d →
    MacaulayProp d S

/-- The inequality in one smaller dimension controls each shadow section after
coordinate compression. -/
theorem iCompression_shadow_section_le {n d : ℕ} (ih : MacaulayInVars n)
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1))
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) (k : ℕ) :
    (iPart (Shadow (iCompression S p d)) p k).card ≤
      (iPart (Shadow S) p k).card := by
  let X := stripSection (iCompression S p d) p k
  let Y := stripSection (iCompression S p d) p (k + 1)
  let A := stripSection S p k
  let B := stripSection S p (k + 1)
  have hXlevel : X ⊆ Finset.univ.finsuppAntidiag (d - k) :=
    stripSection_subset_level p (iCompression_subset (S := S) p d)
  have hYlevel : Y ⊆ Finset.univ.finsuppAntidiag (d - (k + 1)) :=
    stripSection_subset_level p (iCompression_subset (S := S) p d)
  have hXinit : ColexInitial X := stripSection_iCompression_initial p
  have hYinit : ColexInitial Y := stripSection_iCompression_initial p
  have hXs : (Shadow X).card ≤ (Shadow A).card := by
    change (Shadow (stripSection (iCompression S p d) p k)).card ≤ (Shadow A).card
    rw [stripSection_iCompression_eq p hS]
    -- Apply the induction hypothesis in the `n` remaining variables.
    exact ih (d - k) A (stripSection_subset_level p hS)
  have hYcard : Y.card = B.card := by
    dsimp [Y, B]
    rw [stripSection_card, iPart_iCompression_card p hS, stripSection_card]
  have hdeg : ∀ x ∈ Shadow X, ∀ y ∈ Y, (∑ i, x i) = ∑ i, y i := by
    intro x hx y hy
    obtain ⟨j, hj⟩ := mem_Shadow.mp hx
    have hxdeg := (Finset.mem_finsuppAntidiag.mp (hXlevel hj)).1
    have hydeg := (Finset.mem_finsuppAntidiag.mp (hYlevel hy)).1
    have hxdeg' : (∑ i : Fin n, x i) + 1 = d - k := by
      simpa [Finset.sum_add_distrib] using hxdeg
    have hydeg' : (∑ i : Fin n, y i) = d - (k + 1) := hydeg
    omega
  have hShadowInit : ColexInitial (Shadow X) := ColexInitial.shadow hXinit
  have hnested : Shadow X ⊆ Y ∨ Y ⊆ Shadow X :=
    ColexInitial.comparable hShadowInit hYinit hdeg
  have hbound : ((Shadow X) ∪ Y).card ≤ ((Shadow A) ∪ B).card := by
    rw [card_union_eq_max_of_nested hnested]
    apply max_le
    · exact le_trans hXs (Finset.card_le_card Finset.subset_union_left)
    · rw [hYcard]
      exact Finset.card_le_card Finset.subset_union_right
  calc
    (iPart (Shadow (iCompression S p d)) p k).card =
        (stripSection (Shadow (iCompression S p d)) p k).card := (stripSection_card _ p k).symm
    _ = ((Shadow X) ∪ Y).card := by rw [stripSection_shadow_eq]
    _ ≤ ((Shadow A) ∪ B).card := hbound
    _ = (stripSection (Shadow S) p k).card := by rw [stripSection_shadow_eq]
    _ = (iPart (Shadow S) p k).card := stripSection_card _ p k

/-- The `n`-variable induction hypothesis makes each compression in `n+1`
variables shadow-nonincreasing: split by the chosen exponent and apply the
induction hypothesis to each remaining-variable slice. -/
theorem iCompression_shadow_le_of_macaulay {n d : ℕ} (ih : MacaulayInVars n)
    {S : Finset (Fin (n + 1) →₀ ℕ)} (p : Fin (n + 1))
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) :
    (Shadow (iCompression S p d)).card ≤ (Shadow S).card := by
  let T := iCompression S p d
  let I := (Shadow S).image (fun q => q p) ∪ (Shadow T).image (fun q => q p)
  have hI₁ : (Shadow S).image (fun q => q p) ⊆ I := Finset.subset_union_left
  have hI₂ : (Shadow T).image (fun q => q p) ⊆ I := Finset.subset_union_right
  calc
    (Shadow T).card = ∑ k ∈ I, (iPart (Shadow T) p k).card := card_eq_sum_iPart _ p I hI₂
    _ ≤ ∑ k ∈ I, (iPart (Shadow S) p k).card := by
      apply Finset.sum_le_sum
      intro k hk
      exact iCompression_shadow_section_le ih p hS k
    _ = (Shadow S).card := (card_eq_sum_iPart _ p I hI₁).symm

lemma shadow_fin_zero (S : Finset (Fin 0 →₀ ℕ)) : Shadow S = ∅ := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, _⟩ := mem_Shadow.mp hq
    exact Fin.elim0 i
  · intro hq
    simp at hq

theorem macaulayInVars_zero : MacaulayInVars 0 := by
  intro d S hS
  simp [shadow_fin_zero]

lemma colexInitial_fin_one (S : Finset (Fin 1 →₀ ℕ)) : ColexInitial S := by
  intro u v hu hdeg hle
  have hvu : v = u := by
    apply Finsupp.ext
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simpa using hdeg
  simpa [hvu] using hu

theorem macaulayInVars_one : MacaulayInVars 1 := by
  intro d S hS
  have heq := colexInitial_eq_compression hS (colexInitial_fin_one S)
  rw [← heq]

/-- In two variables, an `MC` must already be closed under shifting. -/
theorem MC.shifted_fin_two {k : ℕ} (c : MC 2 k) :
    ∀ (q : Fin 2 →₀ ℕ) (i j : Fin 2), i ≤ j →
      q + Finsupp.single j 1 ∈ c.𝒜 → q + Finsupp.single i 1 ∈ c.𝒜 := by
  intro q i j hij hq
  fin_cases i <;> fin_cases j
  · exact hq
  · obtain ⟨r, hr, hqr⟩ := c.otherExtension hq
    have hr0 : r = 0 := by fin_cases r <;> simp_all
    simpa [hr0] using hqr
  · norm_num at hij
  · exact hq

/-- In two variables, an `MC` is colex-initial. -/
theorem MC.colexInitial_fin_two {k : ℕ} (c : MC 2 k) : ColexInitial c.𝒜 := by
  have hshift := c.shifted_fin_two
  intro u v hu hdeg hle
  have hmerge : mergeFirstTwo v = mergeFirstTwo u := by
    ext i
    fin_cases i
    · simp
    · have h := hdeg
      simp only [Fin.sum_univ_two] at h
      simpa using h
  have hu' := (c.mem_mergeFirstTwo hshift u).mp hu
  apply (c.mem_mergeFirstTwo hshift v).mpr
  rw [hmerge]
  exact hu'

theorem macaulayInVars_two : MacaulayInVars 2 := by
  intro d
  have hall : ∀ m, ∀ S : Finset (Fin 2 →₀ ℕ),
      S ⊆ Finset.univ.finsuppAntidiag d → S.card = m → MacaulayProp d S := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro S hS hSm
      by_contra hbad
      have hbad' : (Shadow S).card <
          (Shadow (Compression (Finset.univ.finsuppAntidiag d :
            Finset (Fin 2 →₀ ℕ)) S.card)).card :=
        Nat.lt_of_not_ge (by simpa [MacaulayProp] using hbad)
      let c : MC 2 d := {
        𝒜 := S
        degHomo := by
          intro a ha
          exact (Finset.mem_finsuppAntidiag.mp (hS ha)).1
        cardMin := by
          intro T hTS hlt
          exact ih T.card (by omega) T (hTS.trans hS) rfl
        counter := hbad
      }
      have heq := colexInitial_eq_compression hS c.colexInitial_fin_two
      have hcontra : (Shadow S).card < (Shadow S).card := by
        simpa only [← heq] using hbad'
      exact (Nat.lt_irrefl _) hcontra
  intro S hS
  exact hall S.card S hS rfl

/-- Macaulay's lower-shadow theorem in every finite number of variables. -/
theorem macaulayInVars_all : ∀ n, MacaulayInVars n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact macaulayInVars_zero
    | succ n =>
      cases n with
      | zero => exact macaulayInVars_one
      | succ n =>
        cases n with
        | zero => exact macaulayInVars_two
        | succ n =>
          intro d S hS
          have ihLower : MacaulayInVars (n + 2) := ih (n + 2) (by omega)
          have hcompress : ∀ T : Finset (Fin (n + 3) →₀ ℕ),
              T ⊆ Finset.univ.finsuppAntidiag d → ∀ p,
              (Shadow (iCompression T p d)).card ≤ (Shadow T).card := by
            intro T hT p
            exact iCompression_shadow_le_of_macaulay ihLower p hT
          exact macaulay_of_shadow_compression hcompress S hS

/-- Macaulay's theorem: among all families of fixed-degree monomials of a
specified cardinality, the colex initial segment has a smallest lower shadow. -/
theorem macaulay_shadow {n d : ℕ} (S : Finset (Fin n →₀ ℕ))
    (hS : S ⊆ Finset.univ.finsuppAntidiag d) :
    MacaulayProp d S :=
  macaulayInVars_all n d S hS

/-- An arbitrary colex-initial family with the same cardinality has minimal
shadow, stated without requiring the family to be written as `Compression`. -/
theorem macaulay_shadow_of_initial {n d : ℕ}
    {A C : Finset (Fin n →₀ ℕ)}
    (hA : A ⊆ Finset.univ.finsuppAntidiag d)
    (hC : C ⊆ Finset.univ.finsuppAntidiag d)
    (hCinit : ColexInitial C) (hcard : C.card = A.card) :
    (Shadow C).card ≤ (Shadow A).card := by
  have heq := colexInitial_eq_compression hC hCinit
  rw [hcard] at heq
  rw [heq]
  exact macaulay_shadow A hA

/-- Macaulay's theorem using the `cLeftSeg` definition in `Lemma1`. -/
theorem macaulay_shadow_cLeftSeg {n d : ℕ} (A : Finset (Fin n →₀ ℕ))
    (m : Fin n →₀ ℕ) (hA : A ⊆ Finset.univ.finsuppAntidiag d)
    (hm : (∑ i, m i) = d) (hcard : (cLeftSeg m).card = A.card) :
    (Shadow (cLeftSeg m)).card ≤ (Shadow A).card := by
  have hC : cLeftSeg m ⊆ Finset.univ.finsuppAntidiag d := by
    intro u hu
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨(mem_cLeftSeg.mp hu).1.trans hm, Finset.subset_univ _⟩
  have hCinit : ColexInitial (cLeftSeg m) := by
    intro u v hu hdeg hle
    exact mem_cLeftSeg.mpr ⟨hdeg.trans (mem_cLeftSeg.mp hu).1,
      hle.trans (mem_cLeftSeg.mp hu).2⟩
  exact macaulay_shadow_of_initial hA hC hCinit hcard

#print axioms macaulay_shadow
#print axioms macaulay_shadow_cLeftSeg

end Macaulay
